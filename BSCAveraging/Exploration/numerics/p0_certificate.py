"""Dual certificates for the one-sided problem at p = 0 (Entropy 24(9):1321).

Setting (NOTES.md §7).  At p = 0 the DSIB objective in bias coordinates is
I(U;V) = E_pi[phi_T(S)] with phi_T(s) = sum_v rho_v f(s t_v), f(z)=(1+z)log(1+z),
and the U-side is constrained only by E[S] = 0 and E[Psi(S)] <= Cu -- both
linear in the law of S.  So maximizing over the U-side is a linear program over
measures, whose dual is the envelope condition

    D(s) = l0 + l1 s + l2 Psi(s) - phi_T(s) >= 0  on [-1,1],  = 0 on supp(S).

This script checks, for the configurations the two conjectures predict:

  Conj 1 (max I(U;V)):  S = (a, -1) Z-channel, T = (+1, -d) S-channel
                        -> contacts at s = a (tangency) and s = -1 (endpoint)
  Conj 2 (min I(U;V), i.e. max I(X;U,V)):  S = (+1, -a), T = (+1, -d), both Z
                        -> contacts at s = +1 (endpoint) and s = -a (tangency)

that (i) the certificate holds with the right sign, and (ii) D'' changes sign
exactly once -- the fact a proof would use, since

    D''(s) * (1-s^2) * (1 + s t_false) * (1 + s t_true)   is a QUADRATIC in s,

so "D >= 0" reduces to root counting plus the two contact conditions.

Result: certificate valid at every (Cu,Cv) tested, one sign change of D''
everywhere.  This proves each side is a *global* best response to the other
(over all laws, any cardinality) once D >= 0 is established.  It does NOT give
joint optimality: the BSC pair is also a fixed point, and no affine certificate
can separate them (at p = 0 the best affine bound is the trivial min(Cu,Cv)).
"""

import numpy as np
from scipy.optimize import brentq

np.seterr(all="ignore")
L2 = np.log(2)


def Psi(s):
    s = np.abs(np.asarray(s, dtype=float))
    return 0.5 * ((1 + s) * np.log1p(s)
                  + np.where(s < 1, (1 - s) * np.log1p(-np.minimum(s, 1 - 1e-300)), 0.0))


def artanh(s):
    return np.arctanh(np.clip(s, -1 + 1e-15, 1 - 1e-15))


def f(z):
    z = np.asarray(z, dtype=float)
    return np.where(z <= -1 + 1e-15, 0.0, (1 + z) * np.log1p(np.maximum(z, -1 + 1e-15)))


def fp(z):
    return np.log1p(np.maximum(np.asarray(z, dtype=float), -1 + 1e-15)) + 1


def opt_extreme(C):
    """Interior atom x of the rate-C two-atom law whose other atom sits at +-1."""
    return brentq(lambda x: (Psi(x) + x * L2) / (x + 1) - C, 1e-12, 1 - 1e-12)


def check(Cu, Cv, mode, n=400001):
    a, d = opt_extreme(Cu), opt_extreme(Cv)
    tp, tm = 1.0, -d                       # T atoms, weights below
    qp, qm = d / (1 + d), 1 / (1 + d)
    phi = lambda s: qp * f(s * tp) + qm * f(s * tm)
    php = lambda s: qp * tp * fp(s * tp) + qm * tm * fp(s * tm)
    x0, x1 = (a, -1.0) if mode == "max" else (-a, 1.0)   # x0 tangency, x1 endpoint
    M = np.array([[1, x0, Psi(x0)], [0, 1, artanh(x0)], [1, x1, Psi(x1)]])
    l0, l1, l2 = np.linalg.solve(M, np.array([phi(x0), php(x0), phi(x1)]))
    g = np.linspace(-1, 1, n)
    D = l0 + l1 * g + l2 * Psi(g) - phi(g)
    sgn = 1 if mode == "max" else -1
    ok = bool((sgn * D >= -1e-12).all())
    Dpp = (l2 / (1 - np.clip(g, -1 + 1e-12, 1 - 1e-12) ** 2)
           - (qp * tp ** 2 / (1 + g * tp) + qm * tm ** 2 / (1 + g * tm)))
    changes = int(np.sum(np.diff(np.sign(Dpp[1:-1])) != 0))
    worst = (sgn * D).min()
    print(f"  {mode} Cu={Cu / L2:.2f} Cv={Cv / L2:.2f} b | a={a:.5f} d={d:.5f} "
          f"l1={l1:+.5f} l2={l2:+.5f} | {'OK  ' if ok else 'FAIL'} "
          f"min(sgn*D)={worst:+.2e} | sign changes of D'': {changes}")
    return ok and changes == 1


CASES = [(0.1, 0.1), (0.2, 0.2), (0.4, 0.4), (0.4, 0.6),
         (0.1, 0.9), (0.7, 0.7), (0.9, 0.9), (0.05, 0.5)]

if __name__ == "__main__":
    print("CONJ 1 (max I(U;V)): need D >= 0, contacts at s = a and s = -1")
    ok1 = all(check(u * L2, v * L2, "max") for u, v in CASES)
    print("CONJ 2 (min I(U;V)): need D <= 0, contacts at s = -a and s = +1")
    ok2 = all(check(u * L2, v * L2, "min") for u, v in CASES)
    print(f"\nall certificates valid: {ok1 and ok2}")
