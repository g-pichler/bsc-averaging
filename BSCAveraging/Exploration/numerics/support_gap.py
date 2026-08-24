"""Fast support-function test for MO 285151 (all in bits).

RESULT (see scan-results.txt): over 726 combinations of p in [0, 0.45] and
(mu, nu) in [0.05, 0.95]^2, the largest observed value of
sup_general - sup_bsc is 3.5e-6 bits, and in every case the maximizing pair of
general channels returned by the optimizer is itself a BSC pair.  No gap.
Strong numerical evidence that conv(A) = conv(B) for every p.

Note the contrast with the *pointwise* problem (Dikshtein-Ordentlich-Shamai,
Entropy 24(9):1321, 2022): at p = 0, C_u = C_v = 0.4 bits, general channels
reach 0.19539 (a near-Z/S pair) versus 0.18950 for BSCs — the MO 213084
counterexample.  The concave envelope of the BSC region at that point is 0.4,
so the counterexample is absorbed with a wide margin.  The Z/S advantage lives
strictly inside the non-concave part of the rate region, which the convex hull
of the question erases.


Channels: cL(U=1|X=x) = s_x,  cR(V=1|Y=y) = t_y,  (X,Y) ~ DSBS(p).

Closed forms (X, Y ~ Bern(1/2)):
    I(U;X) = h((s0+s1)/2) - (h(s0)+h(s1))/2
    I(Y;V) = h((t0+t1)/2) - (h(t0)+h(t1))/2
    P(U=1) = (s0+s1)/2,  P(V=1) = (t0+t1)/2
    P(U=1,V=1) = (1-p)/2 (s0 t0 + s1 t1) + p/2 (s0 t1 + s1 t0)
    I(U;V) = h(pU) + h(pV) - H(qUV)

BSC pairs are s1 = 1-s0, t1 = 1-t0.
"""
import numpy as np
from scipy.optimize import minimize


def xlog(a):
    a = np.asarray(a, dtype=float)
    return np.where(a > 0, a * np.log2(np.where(a > 0, a, 1.0)), 0.0)


def h(a):
    return -xlog(a) - xlog(1.0 - a)


def lag(s0, s1, t0, t1, p, mu, nu):
    pU = (s0 + s1) / 2.0
    pV = (t0 + t1) / 2.0
    IUX = h(pU) - (h(s0) + h(s1)) / 2.0
    IYV = h(pV) - (h(t0) + h(t1)) / 2.0
    q11 = (1 - p) / 2.0 * (s0 * t0 + s1 * t1) + p / 2.0 * (s0 * t1 + s1 * t0)
    q10 = pU - q11
    q01 = pV - q11
    q00 = 1.0 - pU - pV + q11
    HUV = -(xlog(q00) + xlog(q01) + xlog(q10) + xlog(q11))
    IUV = h(pU) + h(pV) - HUV
    return IUV - mu * IUX - nu * IYV


def sup_general(p, mu, nu, n=41, n_refine=12):
    g = np.linspace(0.0, 1.0, n)
    S0, S1, T0, T1 = np.meshgrid(g, g, g, g, indexing="ij")
    L = lag(S0, S1, T0, T1, p, mu, nu)
    flat = L.ravel()
    idx = np.argpartition(flat, -n_refine)[-n_refine:]
    best, arg = -np.inf, None
    for i in idx:
        z0 = np.array([S0.ravel()[i], S1.ravel()[i], T0.ravel()[i], T1.ravel()[i]])
        r = minimize(lambda z: -lag(z[0], z[1], z[2], z[3], p, mu, nu), z0,
                     bounds=[(0, 1)] * 4, method="L-BFGS-B")
        if -r.fun > best:
            best, arg = float(-r.fun), r.x
    return best, arg


def sup_bsc(p, mu, nu, n=801):
    g = np.linspace(0.0, 1.0, n)
    A, B = np.meshgrid(g, g, indexing="ij")
    L = lag(A, 1 - A, B, 1 - B, p, mu, nu)
    i = int(np.argmax(L))
    a0, b0 = A.ravel()[i], B.ravel()[i]
    r = minimize(lambda w: -lag(w[0], 1 - w[0], w[1], 1 - w[1], p, mu, nu),
                 np.array([a0, b0]), bounds=[(0, 1)] * 2, method="L-BFGS-B")
    best = max(float(L.ravel()[i]), float(-r.fun))
    arg = r.x if -r.fun >= L.ravel()[i] else np.array([a0, b0])
    return best, arg


if __name__ == "__main__":
    rows = []
    ps = [0.0, 0.02, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45]
    ls = [0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 0.95]
    for p in ps:
        for mu in ls:
            for nu in ls:
                if nu < mu:
                    continue
                sg, zg = sup_general(p, mu, nu)
                sb, zb = sup_bsc(p, mu, nu)
                rows.append((sg - sb, p, mu, nu, sg, sb, zg, zb))
    rows.sort(reverse=True, key=lambda r: r[0])
    print("largest gaps (sup_general - sup_bsc), bits:")
    for g_, p, mu, nu, sg, sb, zg, zb in rows[:20]:
        print(f"  gap={g_:+.3e}  p={p:.2f} mu={mu:.2f} nu={nu:.2f}  "
              f"gen={sg:.6f} bsc={sb:.6f}  z*={np.round(zg, 4)}  ab*={np.round(zb, 4)}")
