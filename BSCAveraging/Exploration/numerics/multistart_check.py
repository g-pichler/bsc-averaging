"""Cheap insurance for route 2 (NOTES.md sec.6).

Earlier scans solved (E2),(E4) for (c,d) from a SINGLE random start per
(m,k,delta).  (L2) died from exactly that kind of under-sampling, so before
betting on route 2 we re-measure  sup gamma/(nu*I(Y;V))  with MANY starts per
triple, count how many distinct roots exist, and verify that the extremal ones
are genuine best responses on both sides (the equations are only stationarity).

If the supremum stays near ~0.4 the margin is real; if it creeps towards 1,
route 2 is the rho-formulation again and should be dropped early.
"""
import numpy as np
from scipy.optimize import fsolve
import fixed_point_value as V

NSTART = 16
CO, NG = 8.0, 900
pos = np.tanh(np.linspace(1e-4, CO, NG))
A2, B2 = pos[:, None], pos[None, :]


def Psi(y):
    y = np.clip(np.abs(y), 0., 1 - 1e-16)
    return .5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


def fz(z):
    return (1 + z) * np.log1p(z)


def best_U(c, d, mu, de):
    T = np.array([c, -d]); Q = np.array([d, c]) / (c + d)
    Gp = (fz(de * np.outer(pos, T)) * Q[None, :]).sum(axis=1) - mu * Psi(pos)
    Gn = (fz(-de * np.outer(pos, T)) * Q[None, :]).sum(axis=1) - mu * Psi(pos)
    return float(((B2 * Gp[:, None] + A2 * Gn[None, :]) / (A2 + B2)).max())


def best_V(m, k, nu, de):
    grid = np.concatenate([-pos[::-1], pos])
    ze = Psi(m + k * de * grid) - nu * Psi(grid)
    neg = ze[:NG][::-1]; po = ze[NG:]
    return float(((B2 * po[:, None] + A2 * neg[None, :]) / (A2 + B2)).max())


if __name__ == "__main__":
    rng = np.random.default_rng(112358)
    nroots, best, arg, ntrip = [], -np.inf, None, 0
    top = []
    for _ in range(6000):
        m = 10 ** rng.uniform(-7, -0.15)
        k = rng.uniform(.005, 1 - m - .005)
        de = rng.uniform(.05, .999)
        roots = []
        for _s in range(NSTART):
            s0 = [np.tanh(rng.uniform(.2, 6.)), np.tanh(rng.uniform(.2, 6.))]
            sol, info, ier, msg = fsolve(V.eqs, s0, args=(m, k, de), full_output=True)
            if ier != 1:
                continue
            c, d = sol
            if not (1e-6 < c < 1 - 1e-12 and 1e-6 < d < 1 - 1e-12):
                continue
            if max(abs(np.array(V.eqs(sol, m, k, de)))) > 1e-11:
                continue
            p = V.pieces(m, k, c, d, de); mu, nu = p[12], p[13]
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
            if any(abs(c - rc) < 1e-6 and abs(d - rd) < 1e-6 for rc, rd in roots):
                continue
            roots.append((c, d))
            r = gam / (nu * float(Q @ Psi(T)))
            top.append((r, m, k, de, c, d, mu, nu))
            if r > best:
                best, arg = r, (m, k, de, c, d, mu, nu)
        if roots:
            ntrip += 1
            nroots.append(len(roots))
    nroots = np.array(nroots)
    print(f"(m,k,delta) triples with >=1 non-degenerate root : {ntrip}")
    print(f"  distinct roots per triple: mean {nroots.mean():.2f}  max {nroots.max()}  "
          f"frac >1 : {(nroots > 1).mean():.3f}")
    print(f"  total non-degenerate fixed points found        : {len(top)}")
    print(f"  sup gamma/(nu I(Y;V))                          : {best:.6f}   (target <= 1)")
    print(f"    at m=%.3e k=%.5f delta=%.5f c=%.5f d=%.5f mu=%.4f nu=%.4f" % arg)
    top.sort(reverse=True)
    print("  top-8 ratios, with both-sides best-response check:")
    for r, m, k, de, c, d, mu, nu in top[:8]:
        a, b = k / (1 + m), k / (1 - m)
        S = np.array([a, -b]); P = np.array([b, a]) / (a + b)
        T = np.array([c, -d]); Q = np.array([d, c]) / (c + d)
        W = P[:, None] * Q[None, :]
        cu = float((W * fz(de * np.outer(S, T))).sum()) - mu * float(P @ Psi(S))
        # V-side objective is E[zeta(T)] = Ef - nu*E Psi(T) + Psi(m)
        cv = (float((W * fz(de * np.outer(S, T))).sum())
              - nu * float(Q @ Psi(T)) + Psi(m))
        gu = best_U(c, d, mu, de) - cu
        gv = best_V(m, k, nu, de) - cv
        ok = "genuine" if max(gu, gv) < 1e-7 else f"NOT (gapU={gu:.1e} gapV={gv:.1e})"
        print(f"    ratio={r:.4f}  m={m:.2e}  delta={de:.4f}   {ok}")
