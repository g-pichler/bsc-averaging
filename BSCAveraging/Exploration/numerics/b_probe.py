"""(B): G(a,b)+G(c,d) >= 1/2 at fixed points.  What forces it?  (NOTES sec.6)"""
import numpy as np
from scipy.optimize import fsolve
import fixed_point_value as V
at = np.arctanh

def Psi(y):
    y = np.clip(np.abs(y), 0., 1 - 1e-16)
    return .5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))
def fz(z): return (1 + z) * np.log1p(z)
def G(p, q): return (Psi(p) / p + Psi(q) / q) / (at(p) + at(q))

rng = np.random.default_rng(7717)
rows = []
tries = 0
while len(rows) < 400 and tries < 200000:
    tries += 1
    m = 10 ** rng.uniform(-7, -0.15); k = rng.uniform(.005, 1 - m - .005)
    de = rng.uniform(.05, .999)
    sol, info, ier, msg = fsolve(V.eqs, [np.tanh(rng.uniform(.2, 6.)), np.tanh(rng.uniform(.2, 6.))],
                                 args=(m, k, de), full_output=True)
    if ier != 1: continue
    c, d = sol
    if not (1e-6 < c < 1 - 1e-12 and 1e-6 < d < 1 - 1e-12): continue
    if max(abs(np.array(V.eqs(sol, m, k, de)))) > 1e-11: continue
    p = V.pieces(m, k, c, d, de); mu, nu = p[12], p[13]
    if not (np.isfinite(mu) and 0 <= mu < 1 and 0 <= nu < 1): continue
    a, b = k / (1 + m), k / (1 - m)
    if a >= 1 or b >= 1: continue
    T = np.array([c, -d]); Q = np.array([d, c]) / (c + d)
    A = lambda y: -.5 * np.log(1 - y ** 2)
    gam = mu * A(a) + float(Q @ np.log1p(de * a * T))
    if gam <= 1e-6 or mu <= 1e-3 or nu <= 1e-3: continue
    S = np.array([a, -b]); P = np.array([b, a]) / (a + b)
    W = P[:, None] * Q[None, :]; Z = de * np.outer(S, T)
    I = float((W * fz(Z)).sum()); L = float(-(W * np.log1p(Z)).sum())
    r = I / (I + L)
    rows.append((r, G(a, b), G(c, d), G(de*a, de*b), m, de, a, b, c, d, mu, nu))
R = np.array(rows)
r, gu, gv, gy = R[:,0], R[:,1], R[:,2], R[:,3]
print(f"non-degenerate asymmetric fixed points: {len(R)}")
print(f"  min [G(a,b)+G(c,d)]        = {(gu+gv).min():.6f}   (>= 0.5 = claim (B))")
print(f"  min G(a,b)                 = {gu.min():.6f}    max G(a,b) = {gu.max():.6f}")
print(f"  min G(c,d)                 = {gv.min():.6f}    max G(c,d) = {gv.max():.6f}")
print(f"  max rho(U;V)               = {r.max():.6f}")
print("  --- candidate stronger statements ---")
print(f"  rho(U;V) <= G(a,b) always? {'YES' if (r<=gu+1e-12).all() else 'NO'}   max[r-G(a,b)] = {(r-gu).max():+.4f}")
print(f"  rho(U;V) <= G(c,d) always? {'YES' if (r<=gv+1e-12).all() else 'NO'}   max[r-G(c,d)] = {(r-gv).max():+.4f}")
print(f"  rho(U;V) <= 2G(a,b)?       {'YES' if (r<=2*gu+1e-12).all() else 'NO'}  max[r-2G(a,b)] = {(r-2*gu).max():+.4f}")
print(f"  rho(U;V) <= 2G(c,d)?       {'YES' if (r<=2*gv+1e-12).all() else 'NO'}  max[r-2G(c,d)] = {(r-2*gv).max():+.4f}")
print(f"  rho(U;V) <= G(da,db)?      {'YES' if (r<=gy+1e-12).all() else 'NO'}   max[r-G(da,db)] = {(r-gy).max():+.4f}")
j = int(np.argmin(gu+gv))
print("  argmin sum: sum=%.5f G_u=%.4f G_v=%.4f rho=%.4f m=%.2e de=%.4f a=%.4f b=%.4f c=%.4f d=%.4f mu=%.3f nu=%.3f" % tuple(R[j][[1,1,2,0,4,5,6,7,8,9,10,11]]*0 + np.r_[gu[j]+gv[j], R[j][[1,2,0,4,5,6,7,8,9,10,11]]]))
