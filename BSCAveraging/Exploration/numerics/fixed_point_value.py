"""Value at a general alternating-maximization fixed point (NOTES.md sec.6).

With L = artanh, v0,v1 = m +- k, b1 = m+k*delta*c, b2 = m-k*delta*d,
wc,wd = d/(c+d), c/(c+d), kappa = cd/(c+d), A = (Psi(v0)+Psi(v1))/2,
Delta = L(b1)-L(b2), D = L(v0)-L(v1):

    R_B = (wc*Psi(b1) + wd*Psi(b2)) / Delta
    R_U = 2*(b1-m)*wc*A / (k*D)
    R_V = ((m-b2)*Psi(c) + (b1-m)*Psi(d)) / ((L(c)+L(d))*(c+d))

    F = Delta*(R_B - R_U - R_V) - (1-mu)*Psi(m).

At symmetry (m=0, c=d=t, k=s) this is Delta=2L(x), R_B,R_U,R_V = x*R(.)/2, so
F = x*L(x)*(R(x)-R(s)-R(t)), i.e. sec.5d.  The extra term -(1-mu)*Psi(m) <= 0 is
a pure asymmetry cost.

The fixed-point system: (E1) fixes mu, (E3) fixes nu, and (E2),(E4) are then two
parameter-free equations in (m,k,c,d).  Here we fix (m,k,delta) and solve (E2),(E4)
for (c,d), then (i) check the value formula against a direct evaluation of Phi,
and (ii) report whether the resulting mu, nu land in [0,1) -- they must, or the
fixed point is not one of ours.
"""
import numpy as np
from scipy.optimize import fsolve

at = np.arctanh


def Psi(y):
    y = np.clip(np.abs(y), 0.0, 1 - 1e-16)
    return 0.5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


def pieces(m, k, c, d, de):
    v0, v1 = m + k, m - k
    b1, b2 = m + k * de * c, m - k * de * d
    wc, wd = d / (c + d), c / (c + d)
    kap = c * d / (c + d)
    A = 0.5 * (Psi(v0) + Psi(v1))
    LX = 0.5 * (at(v0) + at(v1))
    LV = wc * at(b1) + wd * at(b2)
    D = at(v0) - at(v1)
    Dl = at(b1) - at(b2)
    mu = (LV - at(m)) / (LX - at(m)) if abs(LX - at(m)) > 1e-13 else np.nan
    nu = k * de * Dl / (at(c) + at(d))
    return v0, v1, b1, b2, wc, wd, kap, A, LX, LV, D, Dl, mu, nu


def eqs(cd, m, k, de):
    c, d = cd
    if not (1e-6 < c < 1 - 1e-9 and 1e-6 < d < 1 - 1e-9):
        return [1e3, 1e3]
    v0, v1, b1, b2, wc, wd, kap, A, LX, LV, D, Dl, mu, nu = pieces(m, k, c, d, de)
    e2 = mu * 0.5 * D - de * kap * Dl
    e4 = (Psi(b1) - Psi(b2) - nu * (Psi(c) - Psi(d))
          - (c + d) * (k * de * at(b1) - nu * at(c)))
    return [e2, e4]


def Phi(m, k, c, d, mu, nu, de):
    A = 0.5 * (Psi(m + k) + Psi(m - k))
    b1, b2 = m + k * de * c, m - k * de * d
    wc, wd = d / (c + d), c / (c + d)
    return -mu * A - (1 - mu) * Psi(m) + wc * (Psi(b1) - nu * Psi(c)) + wd * (Psi(b2) - nu * Psi(d))


if __name__ == "__main__":
    rng = np.random.default_rng(31415)
    print(f"{'m':>6} {'k':>6} {'delta':>6} {'c':>7} {'d':>7} {'mu':>8} {'nu':>8} "
          f"{'|F-formula|':>12} {'F':>9}")
    found = 0
    for _ in range(4000):
        if found >= 12:
            break
        m = rng.uniform(0.02, 0.5)
        k = rng.uniform(0.02, 1 - m - 0.02)
        de = rng.uniform(0.3, 0.98)
        c0, d0 = rng.uniform(0.1, 0.9, 2)
        sol, info, ier, msg = fsolve(eqs, [c0, d0], args=(m, k, de), full_output=True)
        if ier != 1:
            continue
        c, d = sol
        if not (1e-4 < c < 1 - 1e-6 and 1e-4 < d < 1 - 1e-6):
            continue
        if max(abs(np.array(eqs(sol, m, k, de)))) > 1e-9:
            continue
        v0, v1, b1, b2, wc, wd, kap, A, LX, LV, D, Dl, mu, nu = pieces(m, k, c, d, de)
        if not np.isfinite(mu) or abs(Dl) < 1e-12:
            continue
        RB = (wc * Psi(b1) + wd * Psi(b2)) / Dl
        RU = 2 * (b1 - m) * wc * A / (k * D)
        RV = ((m - b2) * Psi(c) + (b1 - m) * Psi(d)) / ((at(c) + at(d)) * (c + d))
        Ff = Dl * (RB - RU - RV) - (1 - mu) * Psi(m)
        Fd = Phi(m, k, c, d, mu, nu, de)
        found += 1
        print(f"{m:6.3f} {k:6.3f} {de:6.3f} {c:7.4f} {d:7.4f} {mu:8.4f} {nu:8.4f} "
              f"{abs(Ff - Fd):12.2e} {Fd:9.5f}")
    print(f"\nsolutions found: {found}")
