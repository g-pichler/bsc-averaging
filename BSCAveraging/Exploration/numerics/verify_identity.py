"""Verify the route-2 linchpin  F = J(U;V)*[rho(U;V) - rho(U;X) - rho(Y;V)]  at fixed
points, and independently verify that G(c,d) really is rho(Y;V)."""
import numpy as np
from scipy.optimize import fsolve
import fixed_point_value as V
at = np.arctanh
def Psi(y):
    y = np.clip(np.abs(y), 0., 1 - 1e-16)
    return .5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))
def fz(z): return (1 + z) * np.log1p(z)
def G(p, q): return (Psi(p) / p + Psi(q) / q) / (at(p) + at(q))

rng = np.random.default_rng(9091)
errs, errs2, rows = [], [], []
for _ in range(80000):
    if len(rows) >= 150: break
    m = 10 ** rng.uniform(-6, -0.3); k = rng.uniform(.01, 1 - m - .01); de = rng.uniform(.1, .995)
    sol, info, ier, msg = fsolve(V.eqs, [rng.uniform(.1,.95), rng.uniform(.1,.95)],
                                 args=(m, k, de), full_output=True)
    if ier != 1: continue
    c, d = sol
    if not (1e-6 < c < 1-1e-12 and 1e-6 < d < 1-1e-12): continue
    if max(abs(np.array(V.eqs(sol, m, k, de)))) > 1e-11: continue
    p = V.pieces(m, k, c, d, de); mu, nu = p[12], p[13]
    if not (np.isfinite(mu) and 0 <= mu < 1 and 0 <= nu < 1): continue
    a, b = k/(1+m), k/(1-m)
    if a >= 1 or b >= 1: continue
    # --- U;V from the 4-atom kernel (S = bias of U given X, T = bias of V given Y) ---
    S = np.array([a,-b]); P = np.array([b,a])/(a+b)
    T = np.array([c,-d]); Q = np.array([d,c])/(c+d)
    W = P[:,None]*Q[None,:]; Z = de*np.outer(S,T)
    I_uv = float((W*fz(Z)).sum()); L_uv = float(-(W*np.log1p(Z)).sum()); J_uv = I_uv + L_uv
    # --- F from the value formula ---
    F = float(V.Phi(m, k, c, d, mu, nu, de))
    lhs = F
    rhs = J_uv*(I_uv/J_uv - G(a,b) - G(c,d))
    errs.append(abs(lhs-rhs))
    # --- independent check that G(c,d) = rho(Y;V): build the Y-V joint directly ---
    # Y marginal bias de*m; V has biases-of-Y  T in {c,-d} w/ weights Q  =>  mean 0
    Iyv = float(Q @ Psi(T)); Jyv = float(Q @ (T*at(T)))
    errs2.append(abs(Iyv/Jyv - G(c,d)))
    rows.append((F, J_uv*(I_uv/J_uv-G(a,b)-G(c,d))))
errs = np.array(errs); errs2 = np.array(errs2)
print(f"fixed points checked                       : {len(errs)}")
print(f"max |F - J(U;V)*(rho_UV - rho_UX - rho_YV)|: {errs.max():.3e}")
print(f"  (typical |F| magnitude                   : {np.abs([r[0] for r in rows]).mean():.3e})")
print(f"max |rho(Y;V) - G(c,d)| (indep. rebuild)   : {errs2.max():.3e}")
