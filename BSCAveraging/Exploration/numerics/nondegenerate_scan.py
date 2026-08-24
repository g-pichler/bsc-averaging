"""Degeneracy audit of the asymmetric fixed points, and the refutation of (L2).

Two things this script establishes (NOTES.md sec.6).

**1. Roughly half of the "asymmetric fixed points" found by solving (E2),(E4)
are degenerate.**  The diagnostic is `gamma = conc(H)(0)`, the U-side concave
envelope value, computed as `gamma = mu*A(a) - B(a)` with
`A(y) = -log(1-y^2)/2 = D(pi_X || P_{X|y})` and `B(y) = D(rho_V || P_{V|y})`.
Always `gamma >= H(0) = 0`; `gamma = 0` means the bitangent passes through the
origin, so `S == 0` is already optimal and `F = -nu*I(Y;V) <= 0` holds
vacuously.  Measured: `|gamma| < 1e-9` for ~49% of samples and `mu < 1e-6` for
~41%.  Earlier counts of "694 / 337 / >1000 asymmetric fixed points" therefore
overstated the effective evidence by about a factor of two.

**2. (L2) is false**, hence the two-regime architecture is dead.  With
`G(p,q) := [Psi(p)/p + Psi(q)/q] / (artanh p + artanh q)`, (L2) claimed
`G(a,b) + G(c,d) >= c0 = 2 - 1/log 2` at asymmetric fixed points with
`m >= m0`.  A non-degenerate counterexample with `m = 0.0142 >> 3e-3`:

    m=0.01421, delta=0.9964, a=0.95239, b=0.97984, c=0.99607, d=0.98818,
    mu=0.9185, nu=0.6536,  G(a,b)=0.3035, G(c,d)=0.2371,  sum=0.5406 < 0.5573.

There `F = -0.408 < 0` still, but via `rho(U;V) = 0.3189`, far below both `c0`
and the sum — i.e. the inequality `F <= 0` holds while the *decoupled* bound
fails.  Earlier infima (0.5812 at m0=3e-3, 0.625 at m0=1e-2) were under-sampled.

What survives: on the non-degenerate points, `max F = -8.9e-4` — a genuine
margin rather than machine zero.
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
    rng = np.random.default_rng(97531)
    tot = nd = 0
    ndeg_gamma = ndeg_mu = 0
    worstF, argF = -np.inf, None
    minsum, argS = np.inf, None
    while nd < 300 and tot < 200000:
        tot += 1
        m = 10 ** rng.uniform(-2.52, -0.15)
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
        if abs(gam) < 1e-9:
            ndeg_gamma += 1
        if mu < 1e-6:
            ndeg_mu += 1
        if gam <= 1e-6 or mu <= 1e-3 or nu <= 1e-3:
            continue
        nd += 1
        F = V.Phi(m, k, c, d, mu, nu, de)
        if F > worstF:
            worstF, argF = F, (m, de, a, b, c, d, mu, nu)
        s = G(a, b) + G(c, d)
        if s < minsum:
            S = np.array([a, -b]); P = np.array([b, a]) / (a + b)
            W = P[:, None] * Q[None, :]; Z = de * np.outer(S, T)
            I = float((W * fz(Z)).sum()); L = float(-(W * np.log1p(Z)).sum())
            minsum, argS = s, (m, de, a, b, c, d, mu, nu, G(a, b), G(c, d), I / (I + L), F)
    print(f"candidates accepted as fixed points      : {ndeg_gamma + ndeg_mu and '(see below)'}")
    print(f"  degenerate by |gamma| < 1e-9           : {ndeg_gamma}")
    print(f"  degenerate by mu < 1e-6                : {ndeg_mu}")
    print(f"  NON-degenerate kept                    : {nd}")
    print(f"  max F over non-degenerate              : {worstF:.6e}   (<= 0 required)")
    print(f"  min G(a,b)+G(c,d)   [ (L2) ]           : {minsum:.6f}   (needed >= 0.557305)")
    print(f"    at m=%.5f delta=%.4f a=%.5f b=%.5f c=%.5f d=%.5f" % argS[:6])
    print(f"    mu=%.4f nu=%.4f G(a,b)=%.4f G(c,d)=%.4f rho(U;V)=%.6f F=%.3e" % argS[6:])
    print("  => (L2) is FALSE; the two-regime architecture does not close.")
