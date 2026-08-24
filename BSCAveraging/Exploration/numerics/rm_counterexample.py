"""High-precision check of the candidate counterexample to (RM)  (NOTES.md sec.5g).

(RM) claimed:  Phi(T) <= Phi(+-t)  when Psi(t) = E Psi(|T|), where

    Phi(T) = max over mean-zero S of [ E f(delta*S*T) - mu*E Psi(|S|) ].

rate_matched.py reported a violation.  This script re-checks that point with a
much finer grid plus Nelder-Mead polish on both sides, and then searches locally
for the largest violation.  Grid maxima only ever UNDER-estimate a max, so a
violation survives refinement only if it is real.
"""
import numpy as np
from scipy.optimize import minimize

CO = 10.0
NG = 12000


def Psi(y):
    y = np.clip(np.abs(y), 0.0, 1 - 1e-16)
    return 0.5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


def fz(z):
    return (1 + z) * np.log1p(z)


_u = np.linspace(1e-4, CO, NG)          # must stay > 0: a + b = 0 would divide by zero
_pos = np.tanh(_u)
_PSI = Psi(_pos)


def psi_inv(r):
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


def Gfun(y, T, Q, mu, delta):
    y = np.asarray(y)
    return (fz(delta * np.outer(y, T)) * Q[None, :]).sum(axis=1) - mu * Psi(np.abs(y))


def Phi(T, Q, mu, delta):
    """max over mean-zero S of E f - mu E Psi, exact in two atoms; grid + polish."""
    Gp = Gfun(_pos, T, Q, mu, delta)
    Gn = Gfun(-_pos, T, Q, mu, delta)
    A, B = _pos[:, None], _pos[None, :]
    V = (B * Gp[:, None] + A * Gn[None, :]) / (A + B)
    k = int(np.argmax(V))
    i, j = divmod(k, NG)
    best = float(V.flat[k])

    def negv(z):
        a, b = np.tanh(np.clip(z, 1e-9, CO))
        ga = float(Gfun(np.array([a]), T, Q, mu, delta)[0])
        gb = float(Gfun(np.array([-b]), T, Q, mu, delta)[0])
        return -(b * ga + a * gb) / (a + b)

    r = minimize(negv, np.array([_u[i], _u[j]]), method="Nelder-Mead",
                 options={"xatol": 1e-12, "fatol": 1e-15, "maxiter": 20000})
    return max(best, -float(r.fun))


def Phi_sym(t, mu, delta):
    vals = Psi(delta * t * _pos) - mu * _PSI
    k = int(np.argmax(vals))
    best = float(vals[k])

    def negv(z):
        y = np.tanh(np.clip(z[0], 1e-9, CO))
        return -(Psi(delta * t * y) - mu * Psi(y))

    r = minimize(negv, np.array([_u[k]]), method="Nelder-Mead",
                 options={"xatol": 1e-12, "fatol": 1e-15, "maxiter": 20000})
    return max(best, -float(r.fun))


def gap(c, d, mu, delta):
    T, Q = law(c, d)
    t = psi_inv(float(Q @ Psi(T)))
    return Phi(T, Q, mu, delta) - Phi_sym(t, mu, delta), t


if __name__ == "__main__":
    c, d = 0.8045182494037625, 0.9999833536383655
    mu, delta = 0.7684979352929654, 0.99471294538742
    g, t = gap(c, d, mu, delta)
    print("reported point, refined:")
    print(f"  delta={delta:.12f} mu={mu:.12f} c={c:.12f} d={d:.12f} t={t:.12f}")
    print(f"  Phi(T) - Phi(+-t) = {g:.9e}    (> 0 refutes (RM))")

    def negg(z):
        cc, dd = np.tanh(np.clip(z[:2], 1e-6, CO))
        m = 1.0 / (1.0 + np.exp(-z[2]))
        de = 1.0 / (1.0 + np.exp(-z[3]))
        return -gap(cc, dd, m, de)[0]

    z0 = np.array([np.arctanh(c), np.arctanh(d),
                   np.log(mu / (1 - mu)), np.log(delta / (1 - delta))])
    r = minimize(negg, z0, method="Nelder-Mead",
                 options={"xatol": 1e-10, "fatol": 1e-14, "maxiter": 6000})
    cc, dd = np.tanh(np.clip(r.x[:2], 1e-6, CO))
    m = 1.0 / (1.0 + np.exp(-r.x[2]))
    de = 1.0 / (1.0 + np.exp(-r.x[3]))
    g2, t2 = gap(cc, dd, m, de)
    print("locally maximized violation:")
    print(f"  delta={de:.12f} mu={m:.12f} c={cc:.12f} d={dd:.12f} t={t2:.12f}")
    print(f"  Phi(T) - Phi(+-t) = {g2:.9e}")
