"""Verification of every step of the local-rigidity theorem (NOTES.md sec.5d).

    L(y) = artanh y,  Psi(y) = int_0^y L,  g = (1-y^2)L/y,
    R = Psi/(y L),    Q = (1-y^2)L^2/Psi,   so   g = Q * R.

Theorem: if x = delta*s*t with delta in (0,1] and R(s) + R(t) < R(x), then
Lambda*Lambda' = (1-g(x))^2 / (x^2 * kappa_s * kappa_t) < x^2 < 1, where
kappa_y = g(x)/g(y) - 1.

Proof steps checked here:
  (1) 0 <= 1 - g(y) <= y^2,  g strictly decreasing
  (4) Q strictly decreasing, via  2*Psi*(1 - y*L) < (1-y^2)*L^2,
      which uses Psi <= y*L/2 (convexity of artanh) and y < artanh y
  (5) g(s) + g(t) < g(x) on the feasible region
  (6) the resulting bound Lambda*Lambda' < x^2
"""
import numpy as np

at, th = np.arctanh, np.tanh
Psi = lambda y: 0.5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))
g = lambda y: (1 - y ** 2) * at(y) / y
R = lambda y: Psi(y) / (y * at(y))
Q = lambda y: (1 - y ** 2) * at(y) ** 2 / Psi(y)

if __name__ == "__main__":
    y = th(np.linspace(1e-5, 7, 300000))
    L = at(y)
    print("step 1:  g strictly decreasing        ", bool(np.all(np.diff(g(y)) < 0)))
    print("         0 <= 1 - g(y) <= y^2         ",
          bool(np.all((1 - g(y) >= 0) & (1 - g(y) <= y ** 2 + 1e-15))))
    print("step 4:  Psi <= y*L/2                 ", bool(np.all(Psi(y) <= y * L / 2 + 1e-15)))
    print("         y < artanh y                 ", bool(np.all(y < L)))
    print("         2Psi(1-yL) < (1-y^2)L^2      ",
          bool(np.all(2 * Psi(y) * (1 - y * L) < (1 - y ** 2) * L ** 2)))
    print("         => Q strictly decreasing     ", bool(np.all(np.diff(Q(y)) < 0)))
    print("identity g = Q*R, max error           ", float(np.max(np.abs(g(y) - Q(y) * R(y)))))

    worst_bound, worst_sub, arg = 0.0, 0.0, None
    for us in np.linspace(0.05, 7, 150):
        s = th(us)
        for ut in np.linspace(0.05, 7, 150):
            t = th(ut)
            rs = R(s) + R(t)
            for d in np.linspace(0.02, 1.0, 50):
                x = d * s * t
                if not 0 < x < 1 or rs >= R(x):
                    continue
                G = g(x)
                worst_sub = max(worst_sub, (g(s) + g(t)) / G)          # step 5: must be < 1
                LL = (1 - G) ** 2 / (x ** 2 * (G / g(s) - 1) * (G / g(t) - 1))
                if LL / x ** 2 > worst_bound:
                    worst_bound, arg = LL / x ** 2, (s, t, d)
    print(f"step 5:  max (g(s)+g(t))/g(x) on feasible set = {worst_sub:.6f}  (< 1 required)")
    print(f"step 6:  max (Lambda*Lambda')/x^2             = {worst_bound:.6f}  (<= 1 proved)")
