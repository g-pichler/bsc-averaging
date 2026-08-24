"""Direct maximization of rho(U;V) over the fixed-point set (NOTES.md sec.6).

Route 2's decoupling works if  max rho(U;V) < min[rho(U;X)+rho(Y;V)]  over
fixed points.  Sampling gave 0.4999 vs 0.5484.  The max sits suspiciously close
to 1/2 -- and rho <= 1/2 is exactly I(U;V) <= L(U;V), which on the symmetric
slice is the already-proved trapezoid bound Psi_le_half_mul.  This maximizes
rho(U;V) directly to see whether 1/2 is ever exceeded.
"""
import numpy as np
from scipy.optimize import fsolve, minimize
import fixed_point_value as V


def Psi(y):
    y = np.clip(np.abs(y), 0., 1 - 1e-16)
    return .5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


def fz(z):
    return (1 + z) * np.log1p(z)


def neg_rho(z3):
    m = 1 / (1 + np.exp(-z3[0])); k = 1 / (1 + np.exp(-z3[1])); de = 1 / (1 + np.exp(-z3[2]))
    if m + k >= 1:
        return 1e3
    for st in [(0.5, 0.5), (0.9, 0.3), (0.3, 0.9), (0.99, 0.99), (0.1, 0.1)]:
        sol, info, ier, msg = fsolve(V.eqs, list(st), args=(m, k, de), full_output=True)
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
        S = np.array([a, -b]); P = np.array([b, a]) / (a + b)
        W = P[:, None] * Q[None, :]; Z = de * np.outer(S, T)
        I = float((W * fz(Z)).sum()); L = float(-(W * np.log1p(Z)).sum())
        return -(I / (I + L))
    return 1e3


if __name__ == "__main__":
    rng = np.random.default_rng(999)
    best, arg = -1e9, None
    for _ in range(14):
        z0 = np.array([rng.uniform(-9, 0), rng.uniform(-4, 4), rng.uniform(-3, 5)])
        r = minimize(neg_rho, z0, method="Nelder-Mead",
                     options={"maxiter": 150, "xatol": 1e-9, "fatol": 1e-12})
        if -r.fun > best and -r.fun < 1:
            best, arg = -r.fun, r.x
    m = 1 / (1 + np.exp(-arg[0])); k = 1 / (1 + np.exp(-arg[1])); de = 1 / (1 + np.exp(-arg[2]))
    print(f"max rho(U;V) over fixed points (direct maximization) = {best:.9f}")
    print(f"  vs 1/2 -> {'EXCEEDS 1/2' if best > 0.5 else 'stays <= 1/2'}")
    print(f"  at m={m:.6e} k={k:.6f} delta={de:.6f}")
