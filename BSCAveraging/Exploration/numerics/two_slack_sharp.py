"""Sharpness of the two-slack inequality  Omega <= Sigma_S + Sigma_T  (NOTES.md sec.5g).

Same decomposition as two_slack.py, but with the rate matching Psi(t) = E Psi(|T|)
solved by bisection rather than grid interpolation (the grid version leaves a
~1e-7 error, which is enough to make Sigma_T look slightly negative even though
Mrs. Gerber's Lemma forces Sigma_T >= 0).

Reported: the ratio  rho = Omega / (Sigma_S + Sigma_T).  Near a symmetric
configuration Omega ~ C*e*e', Sigma_S ~ C_S e^2, Sigma_T ~ C_T e'^2, so
sup rho = C / (2 sqrt(C_S C_T)) -- the same AM-GM constant that sec.5d bounds.
If sup rho stays well below 1 there is a real margin to exploit; if it tends to
1 the inequality is tight and any proof has to be sharp.

Sampled both at random and on deliberate near-symmetric perturbations
a = s(1+e), b = s(1-e), c = t(1+e'), d = t(1-e') with e, e' of both signs and
many magnitudes, in artanh coordinates for s, t.

REFUTED: (RM) is FALSE.  rm_counterexample.py exhibits
    delta=0.994712945387, mu=0.768497935293, T in {0.804518249404, -0.999983353638},
    Phi(T) = 0.014037097 > Phi(+-t) = 0.012046858  with Psi(t) = E Psi(|T|).
This script's random-S sampling never hits the optimal S, so its "no violation"
verdict is NOT evidence for (RM); the equivalence quantifies over ALL S.  What
remains valid here: the identity itself (max error 2.8e-16) and Sigma_T >= 0
(Mrs. Gerber's Lemma).
"""
import numpy as np

CO = 8.0
NGRID = 6000


def Psi(y):
    y = np.clip(np.abs(y), 0.0, 1 - 1e-16)
    return 0.5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


def fz(z):
    return (1 + z) * np.log1p(z)


def f_o(z):
    return 0.5 * ((1 + z) * np.log1p(z) - (1 - z) * np.log1p(-z))


_pos = np.tanh(np.linspace(0.0, CO, NGRID))
_PSI = Psi(_pos)


def psi_inv(r):
    """Psi(t) = r by bisection; Psi is strictly increasing on [0,1]."""
    lo, hi = 0.0, 1.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if Psi(mid) < r:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def law(a, b):
    return np.array([a, -b]), np.array([b, a]) / (a + b)


def pieces(a, b, c, d, mu, delta):
    S, P = law(a, b)
    T, Q = law(c, d)
    aS, aT = np.abs(S), np.abs(T)
    t = psi_inv(float(Q @ Psi(T)))
    A = Psi(delta * _pos * t) - mu * _PSI
    maxA = float(A.max())
    SigS = maxA - float(P @ (Psi(delta * aS * t) - mu * Psi(aS)))
    SigT = float(P @ Psi(delta * aS * t)) \
        - float((P[:, None] * Q[None, :] * Psi(delta * np.outer(aS, aT))).sum())
    Om = float((P[:, None] * Q[None, :] * f_o(delta * np.outer(S, T))).sum())
    return SigS, SigT, Om


def scan(gen, n, label):
    minS = minT = np.inf
    worst_abs, worst_rho, at = -np.inf, -np.inf, None
    for _ in range(n):
        a, b, c, d, mu, delta = gen()
        SigS, SigT, Om = pieces(a, b, c, d, mu, delta)
        minS, minT = min(minS, SigS), min(minT, SigT)
        worst_abs = max(worst_abs, Om - (SigS + SigT))
        tot = SigS + SigT
        if tot > 1e-13 and Om > 0:
            rho = Om / tot
            if rho > worst_rho:
                worst_rho, at = rho, (delta, mu, a, b, c, d, Om, SigS, SigT)
    print(f"[{label}]  n={n}")
    print(f"    min Sigma_S = {minS:.3e}   min Sigma_T = {minT:.3e}   (MGL: >= 0)")
    print(f"    max (Omega - Sigma_S - Sigma_T) = {worst_abs:.3e}   (<= 0 required)")
    print(f"    max rho = Omega/(Sigma_S+Sigma_T) = {worst_rho:.6f}   (< 1 required)")
    print(f"    at {at}")


if __name__ == "__main__":
    rng = np.random.default_rng(1234567)

    def rand():
        return (*np.tanh(rng.uniform(0.002, CO, size=4)),
                rng.uniform(0.0, 1.0), rng.uniform(0.02, 0.999))

    def near_sym():
        s, t = np.tanh(rng.uniform(0.05, CO, size=2))
        e = rng.choice([1.0, -1.0]) * 10 ** rng.uniform(-6, -0.5)
        ep = rng.choice([1.0, -1.0]) * 10 ** rng.uniform(-6, -0.5)
        a, b = min(s * (1 + e), 1.0), min(s * (1 - e), 1.0)
        c, d = min(t * (1 + ep), 1.0), min(t * (1 - ep), 1.0)
        return a, b, c, d, rng.uniform(0.0, 1.0), rng.uniform(0.02, 0.999)

    scan(rand, 4000, "random")
    scan(near_sym, 8000, "near-symmetric")
