"""Verify the bias/kernel reduction of NOTES.md section 2, numerically.

With pi_u = P(U=u), rho_v = P(V=v), s_u = 1-2P(X=1|U=u), t_v = 1-2P(Y=1|V=v)
and delta = 1-2p:

    P(u,v) = pi_u rho_v (1 + delta s_u t_v)
    I(U;V) = sum pi_u rho_v f(delta s_u t_v),  f(z) = (1+z) log2(1+z)
    I(U;X) = sum pi_u phi(s_u),                phi(s) = 1 - H((1+s)/2)
    E S = E T = 0                              (equivalent to X, Y ~ Bern(1/2))

All four hold to machine precision for random channel pairs.
"""
import numpy as np
from convex_hull_lp import triple, h

rng = np.random.default_rng(7)
phi = lambda s: 1 - h((1 + s) / 2)
f = lambda z: (1 + z) * np.log2(1 + z)

for _ in range(6):
    p = rng.random() * 0.5
    s0, s1, t0, t1 = rng.random(4)
    d = 1 - 2 * p
    pxy = np.array([[(1 - p) / 2, p / 2], [p / 2, (1 - p) / 2]])
    cL = np.array([[1 - s0, s0], [1 - s1, s1]])
    cR = np.array([[1 - t0, t0], [1 - t1, t1]])
    Puv = cL.T @ pxy @ cR
    pi, rho = Puv.sum(1), Puv.sum(0)
    S = 1 - 2 * np.array([0.5 * cL[1, u] / pi[u] for u in (0, 1)])
    T = 1 - 2 * np.array([0.5 * cR[1, v] / rho[v] for v in (0, 1)])
    K = np.array([[pi[u] * rho[v] * (1 + d * S[u] * T[v]) for v in (0, 1)] for u in (0, 1)])
    IUV, IUX, IYV = triple(p, s0, s1, t0, t1)
    IUV_k = sum(pi[u] * rho[v] * f(d * S[u] * T[v]) for u in (0, 1) for v in (0, 1))
    print(f"p={p:.4f}  kernel={np.abs(Puv - K).max():.1e}  ES={pi @ S:+.1e} ET={rho @ T:+.1e}"
          f"  I(U;X)={abs(IUX - pi @ phi(S)):.1e}  I(U;V)={abs(IUV - IUV_k):.1e}")
