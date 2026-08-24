"""Is (L1) far from sharp AT fixed points?  (NOTES.md sec.6, route 2)

(L1) gives rho(U;V) <= c0 = 2 - 1/log 2 = 0.5573 for ALL two-point pairs, sharp
at a Z-channel corner.  (L2) -- rho(U;X)+rho(Y;V) >= c0 -- failed by 0.017.
But the (L2) counterexample had rho(U;V) = 0.3189, far below c0, suggesting the
sharp constant is not attained anywhere near the fixed-point set.

If   max rho(U;V)  <  min [rho(U;X)+rho(Y;V)]   over fixed points,
the decoupling works after all, with a fixed-point-restricted (L1).
"""
import numpy as np
from scipy.optimize import fsolve
import fixed_point_value as V

at = np.arctanh


def Psi(y):
    y = np.clip(np.abs(y), 0., 1 - 1e-16)
    return .5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


def fz(z):
    return (1 + z) * np.log1p(z)


def G(p, q):
    return (Psi(p) / p + Psi(q) / q) / (at(p) + at(q))


if __name__ == "__main__":
    rng = np.random.default_rng(20260808)
    rhoUV, sums, rows = [], [], []
    tries = 0
    while len(rhoUV) < 200 and tries < 60000:
        tries += 1
        m = 10 ** rng.uniform(-7, -0.15)
        k = rng.uniform(.005, 1 - m - .005)
        de = rng.uniform(.05, .999)
        sol, info, ier, msg = fsolve(
            V.eqs, [np.tanh(rng.uniform(.2, 6.)), np.tanh(rng.uniform(.2, 6.))],
            args=(m, k, de), full_output=True)
        if ier != 1:
            continue
        c, d = sol
        if not (1e-6 < c < 1 - 1e-12 and 1e-6 < d < 1 - 1e-12):
            continue
        if max(abs(np.array(V.eqs(sol, m, k, de)))) > 1e-11:
            continue
        p = V.pieces(m, k, c, d, de)
        mu, nu = p[12], p[13]
        if not (np.isfinite(mu) and 0 <= mu < 1 and 0 <= nu < 1):
            continue
        a, b = k / (1 + m), k / (1 - m)
        if a >= 1 or b >= 1:
            continue
        T = np.array([c, -d]); Q = np.array([d, c]) / (c + d)
        A = lambda y: -.5 * np.log(1 - y ** 2)
        gam = mu * A(a) + float(Q @ np.log1p(de * a * T))
        if gam <= 1e-6 or mu <= 1e-3 or nu <= 1e-3:
            continue
        S = np.array([a, -b]); P = np.array([b, a]) / (a + b)
        W = P[:, None] * Q[None, :]; Z = de * np.outer(S, T)
        I = float((W * fz(Z)).sum()); L = float(-(W * np.log1p(Z)).sum())
        r = I / (I + L)
        s = G(a, b) + G(c, d)
        rhoUV.append(r); sums.append(s)
        rows.append((r, s, m, de, a, b, c, d))
    rhoUV = np.array(rhoUV); sums = np.array(sums)
    print(f"non-degenerate asymmetric fixed points : {len(rhoUV)}")
    print(f"  max rho(U;V)                          : {rhoUV.max():.6f}   "
          f"(global sharp bound c0 = 0.557305)")
    print(f"  min [rho(U;X) + rho(Y;V)]             : {sums.min():.6f}")
    print(f"  max rho(U;V) < min sum ?              : "
          f"{'YES — decoupling works at fixed points' if rhoUV.max() < sums.min() else 'NO'}")
    print(f"  max [rho(U;V) - rho(U;X) - rho(Y;V)]  : {(rhoUV - sums).max():.6f}  (<= 0 = target)")
    i = int(np.argmax(rhoUV))
    print("  argmax rho(U;V): rho=%.4f sum=%.4f m=%.2e delta=%.4f a=%.4f b=%.4f c=%.4f d=%.4f" % rows[i])
    j = int(np.argmin(sums))
    print("  argmin sum     : rho=%.4f sum=%.4f m=%.2e delta=%.4f a=%.4f b=%.4f c=%.4f d=%.4f" % rows[j])
