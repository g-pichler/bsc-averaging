"""Supremum of rho(U;V) = I/(I+L) over two-point pairs (NOTES.md sec.6).

The two-regime split of sec.6 needs  sup rho(U;V) < inf[rho(U;X)+rho(Y;V)]
restricted to asymmetric fixed points with m >= m0.  Random sampling gave
sup rho(U;V) ~ 0.5486; this maximizes it properly.
"""
import numpy as np
from scipy.optimize import minimize

CO = 12.0


def fz(z):
    return (1 + z) * np.log1p(z)


def rho(z):
    a, b, c, d = np.tanh(np.clip(z[:4], 1e-9, CO))
    de = 1 / (1 + np.exp(-z[4]))
    S = np.array([a, -b]); P = np.array([b, a]) / (a + b)
    T = np.array([c, -d]); Q = np.array([d, c]) / (c + d)
    W = P[:, None] * Q[None, :]
    Z = de * np.outer(S, T)
    I = float((W * fz(Z)).sum())
    J = float((W * Z * np.log1p(Z)).sum())
    return 0.0 if J <= 1e-16 else I / J


if __name__ == "__main__":
    rng = np.random.default_rng(13131)
    best, arg = -np.inf, None
    for _ in range(250):
        z0 = np.concatenate([rng.uniform(0.05, CO, 4), rng.uniform(-3, 3, 1)])
        r = minimize(lambda z: -rho(z), z0, method="Nelder-Mead",
                     options={"maxiter": 4000, "xatol": 1e-11, "fatol": 1e-14})
        if -r.fun > best:
            best, arg = -r.fun, r.x
    a, b, c, d = np.tanh(np.clip(arg[:4], 1e-9, CO))
    de = 1 / (1 + np.exp(-arg[4]))
    print(f"sup rho(U;V) over two-point pairs = {best:.6f}")
    print(f"  at a={a:.6f} b={b:.6f} c={c:.6f} d={d:.6f} delta={de:.6f}")
    print("  two-regime split needs < 0.5812  ->",
          "HOLDS" if best < 0.5812 else "BREAKS")
