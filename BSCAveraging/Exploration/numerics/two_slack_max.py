"""Global maximization of  rho = Omega / (Sigma_S + Sigma_T)   (NOTES.md sec.5g).

(RM) -- and hence the conjecture -- is equivalent to rho <= 1 everywhere.
two_slack_sharp.py found rho up to 0.904 by random sampling, and, notably, the
worst case was NOT near-symmetric: the binding regime is strongly asymmetric.
That leaves only a ~10% margin, so it is worth maximizing rho properly.

All six parameters are optimized: a, b, c, d in artanh coordinates (the optima
sit at atoms ~0.999, which uniform grids miss), mu and delta through a logistic
map.  max_s A_t(s) is a grid maximum polished by golden section, and the rate
matching Psi(t) = E Psi(|T|) is done by bisection.

REFUTED: (RM) is FALSE.  rm_counterexample.py exhibits
    delta=0.994712945387, mu=0.768497935293, T in {0.804518249404, -0.999983353638},
    Phi(T) = 0.014037097 > Phi(+-t) = 0.012046858  with Psi(t) = E Psi(|T|).
This script's random-S sampling never hits the optimal S, so its "no violation"
verdict is NOT evidence for (RM); the equivalence quantifies over ALL S.  What
remains valid here: the identity itself (max error 2.8e-16) and Sigma_T >= 0
(Mrs. Gerber's Lemma).
"""
import numpy as np
from scipy.optimize import minimize

CO = 9.0
NGRID = 4000


def Psi(y):
    y = np.clip(np.abs(y), 0.0, 1 - 1e-16)
    return 0.5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


def f_o(z):
    return 0.5 * ((1 + z) * np.log1p(z) - (1 - z) * np.log1p(-z))


_u = np.linspace(0.0, CO, NGRID)
_pos = np.tanh(_u)
_PSI = Psi(_pos)


def psi_inv(r):
    lo, hi = 0.0, 1.0
    for _ in range(120):
        mid = 0.5 * (lo + hi)
        if Psi(mid) < r:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def A(s, t, mu, delta):
    return Psi(delta * s * t) - mu * Psi(s)


def maxA(t, mu, delta):
    """max over s in [0,1] of A, grid + golden-section polish in artanh coords."""
    vals = A(_pos, t, mu, delta)
    k = int(np.argmax(vals))
    lo = _u[max(k - 1, 0)]
    hi = _u[min(k + 1, NGRID - 1)]
    gr = (np.sqrt(5.0) - 1.0) / 2.0
    x1, x2 = hi - gr * (hi - lo), lo + gr * (hi - lo)
    f1, f2 = A(np.tanh(x1), t, mu, delta), A(np.tanh(x2), t, mu, delta)
    for _ in range(120):
        if f1 < f2:
            lo, x1, f1 = x1, x2, f2
            x2 = lo + gr * (hi - lo)
            f2 = A(np.tanh(x2), t, mu, delta)
        else:
            hi, x2, f2 = x2, x1, f1
            x1 = hi - gr * (hi - lo)
            f1 = A(np.tanh(x1), t, mu, delta)
    return max(float(max(f1, f2)), float(vals[k]))


def law(a, b):
    return np.array([a, -b]), np.array([b, a]) / (a + b)


def rho(a, b, c, d, mu, delta):
    S, P = law(a, b)
    T, Q = law(c, d)
    aS, aT = np.abs(S), np.abs(T)
    t = psi_inv(float(Q @ Psi(T)))
    M = maxA(t, mu, delta)
    SigS = M - float(P @ (Psi(delta * aS * t) - mu * Psi(aS)))
    SigT = float(P @ Psi(delta * aS * t)) \
        - float((P[:, None] * Q[None, :] * Psi(delta * np.outer(aS, aT))).sum())
    Om = float((P[:, None] * Q[None, :] * f_o(delta * np.outer(S, T))).sum())
    tot = SigS + SigT
    if tot <= 1e-15 or Om <= 0:
        return -np.inf, SigS, SigT, Om
    return Om / tot, SigS, SigT, Om


def unpack(z):
    a, b, c, d = np.tanh(np.clip(z[:4], 1e-6, CO))
    mu = 1.0 / (1.0 + np.exp(-z[4]))
    delta = 1.0 / (1.0 + np.exp(-z[5]))
    return a, b, c, d, mu, delta


def neg(z):
    r = rho(*unpack(z))[0]
    return -r if np.isfinite(r) else 1e6


if __name__ == "__main__":
    rng = np.random.default_rng(2718281)
    best, barg = -np.inf, None

    # seed with the worst point found by random sampling, plus random restarts
    seeds = [np.array([np.arctanh(0.9999997303180714), np.arctanh(0.9049180539447196),
                       np.arctanh(0.6973339088750206), np.arctanh(0.9996346401518833),
                       np.log(0.5202 / (1 - 0.5202)), np.log(0.9906 / (1 - 0.9906))])]
    for _ in range(400):
        seeds.append(np.concatenate([rng.uniform(0.05, CO, 4), rng.uniform(-4, 4, 2)]))

    for z0 in seeds:
        r = minimize(neg, z0, method="Nelder-Mead",
                     options={"maxiter": 4000, "xatol": 1e-10, "fatol": 1e-14})
        if -r.fun > best:
            best, barg = -r.fun, r.x

    a, b, c, d, mu, delta = unpack(barg)
    r, SigS, SigT, Om = rho(a, b, c, d, mu, delta)
    print(f"max rho = {best:.9f}     (<= 1 required; = 1 would make (RM) tight)")
    print(f"  delta = {delta:.9f}   mu = {mu:.9f}")
    print(f"  a = {a:.9f}  b = {b:.9f}   c = {c:.9f}  d = {d:.9f}")
    print(f"  Omega = {Om:.6e}   Sigma_S = {SigS:.6e}   Sigma_T = {SigT:.6e}")
