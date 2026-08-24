"""Stratifying the asymmetric fixed points by the asymmetry `m` (NOTES.md sec.6).

Route 2 needs `gamma <= nu*I(Y;V)` at asymmetric fixed points; lemma (L3) is
supposed to cover the near-symmetric stratum `m < m0` via a quantitative form of
sec.5d.  Since `Lambda*Lambda' <= 0.0013` (local_rigidity.py), the contraction
factor `1 - Lambda*Lambda' >= 0.9987` is essentially free, and `m0` is governed
entirely by the second-order constant `C` in `m0 = (1-Lambda*Lambda')/C`.

This scan reports, stratified by `m`, the largest `F` and the largest
`gamma/(nu*I(Y;V))` over non-degenerate asymmetric fixed points — i.e. how much
room (L3) actually has to cover, and how much the direct bound has outside.
"""
import numpy as np
from scipy.optimize import fsolve
import fixed_point_value as V


def Psi(y):
    y = np.clip(np.abs(y), 0., 1 - 1e-16)
    return .5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


if __name__ == "__main__":
    rng = np.random.default_rng(8080)
    rows = []
    tries = 0
    while len(rows) < 250 and tries < 60000:
        tries += 1
        m = 10 ** rng.uniform(-7, -0.15)
        k = rng.uniform(.005, 1 - m - .005)
        de = rng.uniform(.05, .999)
        sol, info, ier, msg = fsolve(
            V.eqs, [np.tanh(rng.uniform(.5, 5.)), np.tanh(rng.uniform(.5, 5.))],
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
        IYV = float(Q @ Psi(T))
        rows.append((m, V.Phi(m, k, c, d, mu, nu, de), gam / (nu * IYV)))
    rows = np.array(rows)
    print(f"non-degenerate asymmetric fixed points: {len(rows)}")
    print(f"{'stratum':>14} {'count':>7} {'max F':>13} {'max gamma/(nu I)':>18}")
    for m0 in [1e-5, 1e-4, 1e-3, 1e-2, 1e-1]:
        sel = rows[rows[:, 0] < m0]
        if len(sel):
            print(f"{'m < %.0e' % m0:>14} {len(sel):7d} {sel[:, 1].max():13.3e} {sel[:, 2].max():18.4f}")
    for m0 in [1e-5, 1e-4, 1e-3, 1e-2, 1e-1]:
        sel = rows[rows[:, 0] >= m0]
        if len(sel):
            print(f"{'m >= %.0e' % m0:>14} {len(sel):7d} {sel[:, 1].max():13.3e} {sel[:, 2].max():18.4f}")
