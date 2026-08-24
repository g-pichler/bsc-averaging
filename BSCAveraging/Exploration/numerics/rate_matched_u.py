"""U-side RATE matching (NOTES.md sec.6, route 1).

sec.5j's (SH') matched the PENALTY, mu*Psi(k') = mu*A + (1-mu)*Psi(m).  That is
the wrong invariant: the rate is I(U;X) = A - Psi(m), not A.  Matching the rate,
Psi(k'') = A - Psi(m), and using

    F_opt(m,k)   = -mu*A - (1-mu)*Psi(m) + conc(zeta_{m,k})(0),
    F_opt(0,k'') = -mu*Psi(k'') + max_y [Psi(delta*k''*y) - nu*Psi(y)],
    Psi(k'') = A - Psi(m),

the comparison F_opt(m,k) <= F_opt(0,k'') collapses to the mu-FREE claim

    (RM-U)  conc(zeta_{m,k})(0) - Psi(m) <= max_y [Psi(delta*k''*y) - nu*Psi(y)],

i.e. among binary U with a given I(U;X), the BSC maximizes
sup_V [ I(U;V) - nu*I(Y;V) ].
"""
import numpy as np
import shift_bound as S

Psi = S.Psi
_pos = S._pos


def psi_inv(r):
    lo, hi = 0.0, 1.0
    for _ in range(120):
        mid = 0.5 * (lo + hi)
        if Psi(mid) < r:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


rng = np.random.default_rng(97531)
worst, at = -np.inf, None
N = 8000
for _ in range(N):
    delta = rng.uniform(0.02, 0.999)
    nu = rng.uniform(0.0, 0.999)
    m = rng.uniform(0.0, 1.0)
    k = rng.uniform(0.0, 1.0 - m)
    A = 0.5 * (Psi(m + k) + Psi(m - k))
    rate = max(A - Psi(m), 0.0)
    kpp = psi_inv(rate)
    lhs = S.conc_zeta(m, k, nu, delta) - Psi(m)
    rhs = float(np.max(Psi(delta * kpp * _pos) - nu * Psi(_pos)))
    if lhs - rhs > worst:
        worst, at = lhs - rhs, (delta, nu, m, k, kpp, lhs, rhs)
print(f"samples: {N}")
print(f"max [LHS - RHS] = {worst:.3e}    (<= 0 = (RM-U), which closes route 1)")
print(f"at (delta,nu,m,k,k'',lhs,rhs) = {at}")
