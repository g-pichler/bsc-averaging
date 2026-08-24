"""Direct minimization of G(a,b)+G(c,d) over the fixed-point set  -- does (B) survive
as k -> 1?  Also minimizes the REAL target  G_u+G_v-rho(U;V), and tracks mu."""
import numpy as np
from scipy.optimize import fsolve, minimize
import fixed_point_value as V
at = np.arctanh
def Psi(y):
    y = np.clip(np.abs(y), 0., 1 - 1e-16)
    return .5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))
def fz(z): return (1 + z) * np.log1p(z)
def G(p, q): return (Psi(p) / p + Psi(q) / q) / (at(p) + at(q))

def solve_at(m, k, de, seed=(0.9, 0.9)):
    sol, info, ier, msg = fsolve(V.eqs, list(seed), args=(m, k, de), full_output=True)
    if ier != 1: return None
    c, d = sol
    if not (1e-9 < c < 1 - 1e-13 and 1e-9 < d < 1 - 1e-13): return None
    if max(abs(np.array(V.eqs(sol, m, k, de)))) > 1e-10: return None
    a, b = k / (1 + m), k / (1 - m)
    if a >= 1 or b >= 1: return None
    p = V.pieces(m, k, c, d, de); mu, nu = p[12], p[13]
    if not (np.isfinite(mu) and np.isfinite(nu)): return None
    T = np.array([c, -d]); Q = np.array([d, c]) / (c + d)
    S = np.array([a, -b]); P = np.array([b, a]) / (a + b)
    W = P[:, None] * Q[None, :]; Z = de * np.outer(S, T)
    I = float((W * fz(Z)).sum()); L = float(-(W * np.log1p(Z)).sum())
    A = lambda y: -.5 * np.log(1 - y ** 2)
    gam = mu * A(a) + float(Q @ np.log1p(de * a * T))
    return dict(a=a,b=b,c=c,d=d,mu=mu,nu=nu,gam=gam,rho=I/(I+L),Gu=G(a,b),Gv=G(c,d))

def obj(x, mode, nondeg):
    m = 10 ** x[0]; k = 1/(1+np.exp(-x[1])); de = 1/(1+np.exp(-x[2]))
    if not (1e-9 < m < .8 and 0 < k < 1 - m and 0 < de < 1): return 5.
    r = solve_at(m, k, de)
    if r is None: return 5.
    if nondeg and (r['gam'] <= 1e-6 or r['mu'] <= 1e-3 or r['nu'] <= 1e-3): return 5.
    return (r['Gu']+r['Gv']) if mode=='B' else (r['Gu']+r['Gv']-r['rho'])

rng = np.random.default_rng(31337)
for mode, label in (('B','G_u+G_v            (claim (B), target >= 0.5)'),
                    ('T','G_u+G_v-rho(U;V)   (real target, >= 0)')):
    for nondeg in (True, False):
        best, barg = 5., None
        for _ in range(12):
            x0 = [rng.uniform(-7,-.2), rng.uniform(-1,5), rng.uniform(0,5)]
            res = minimize(obj, x0, args=(mode,nondeg), method='Nelder-Mead',
                           options=dict(maxiter=400, xatol=1e-10, fatol=1e-13))
            if res.fun < best: best, barg = res.fun, res.x
        m = 10**barg[0]; k = 1/(1+np.exp(-barg[1])); de = 1/(1+np.exp(-barg[2]))
        r = solve_at(m,k,de)
        tag = "non-degenerate" if nondeg else "ALL fixed points"
        print(f"min {label}  [{tag}] = {best:.6f}")
        if r: print(f"    at m={m:.3e} k={k:.6f} delta={de:.6f} a={r['a']:.5f} b={r['b']:.5f} "
                    f"c={r['c']:.5f} d={r['d']:.5f} mu={r['mu']:.4f} nu={r['nu']:.4f} rho={r['rho']:.4f}")
