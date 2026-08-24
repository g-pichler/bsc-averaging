"""Penalty-matched symmetrization on the U side (NOTES.md sec.5j).

Coordinates of sec.5h: m = (v0+v1)/2, k = (v0-v1)/2, A = (Psi(m+k)+Psi(m-k))/2,

    F_opt(m,k) = -mu*A - (1-mu)*Psi(m) + conc(zeta_{m,k})(0),
    zeta_{m,k}(y) = Psi(m + k*delta*y) - nu*Psi(y),
    F_opt(0,k)  = -mu*Psi(k) + max_y [Psi(delta*k*y) - nu*Psi(y)].

Choose the symmetric competitor k' so the PENALTIES match exactly:

    mu*Psi(k') = mu*A + (1-mu)*Psi(m)   i.e.   Psi(k') = A + ((1-mu)/mu)*Psi(m),

capped at k' = 1.  Then  F_opt(m,k) <= F_opt(0,k')  is equivalent to

    (SH')   conc(zeta_{m,k})(0) <= max_y [Psi(delta*k'*y) - nu*Psi(y)].

This is the U-side analogue of the V-side rate matching that sec.5g REFUTED.
The two are not the same statement: here the asymmetry enters as a shift m inside
Psi, and the penalty budget includes the extra (1-mu)*Psi(m) term.

Tests
  (a) F_opt(m,k) <= max over k' of F_opt(0,k')     -- the conjecture itself
  (b) F_opt(m,k) <= F_opt(0, k'_matched)           -- (SH'), unknown
"""
import numpy as np

CO = 8.0
NG = 700


def Psi(y):
    y = np.clip(np.abs(y), 0.0, 1 - 1e-16)
    return 0.5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


_pos = np.tanh(np.linspace(1e-4, CO, NG))
_grid = np.concatenate([-_pos[::-1], _pos])
_A2, _B2 = _pos[:, None], _pos[None, :]
_PSIPOS = Psi(_pos)


def psi_inv(r):
    lo, hi = 0.0, 1.0
    for _ in range(120):
        mid = 0.5 * (lo + hi)
        if Psi(mid) < r:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def conc_at_zero(vals):
    neg = vals[:NG][::-1]
    pos = vals[NG:]
    V = (_B2 * pos[:, None] + _A2 * neg[None, :]) / (_A2 + _B2)
    return float(V.max())


def F_opt(m, k, mu, nu, delta):
    A = 0.5 * (Psi(m + k) + Psi(m - k))
    return -mu * A - (1 - mu) * Psi(m) + conc_at_zero(Psi(m + k * delta * _grid)
                                                     - nu * Psi(_grid))


def F_sym(kp, mu, nu, delta):
    return -mu * Psi(kp) + float(np.max(Psi(delta * kp * _pos) - nu * _PSIPOS))


def J_sym(mu, nu, delta):
    M = Psi(delta * np.outer(_pos, _pos)) - nu * _PSIPOS[None, :] - mu * _PSIPOS[:, None]
    return float(M.max())


if __name__ == "__main__":
    rng = np.random.default_rng(5150)
    worst_a, at_a = -np.inf, None
    worst_b, at_b = -np.inf, None
    n = 0
    for _ in range(6000):
        delta = rng.uniform(0.02, 0.999)
        mu = rng.uniform(0.02, 0.999)
        nu = rng.uniform(0.0, 0.999)
        m = rng.uniform(0.0, 1.0)
        k = rng.uniform(0.0, 1.0 - m)
        n += 1
        F = F_opt(m, k, mu, nu, delta)
        js = J_sym(mu, nu, delta)
        if F - js > worst_a:
            worst_a, at_a = F - js, (delta, mu, nu, m, k, F, js)
        A = 0.5 * (Psi(m + k) + Psi(m - k))
        target = A + (1 - mu) / mu * Psi(m)
        kp = 1.0 if target >= Psi(1.0) else psi_inv(target)
        fb = F - F_sym(kp, mu, nu, delta)
        if fb > worst_b:
            worst_b, at_b = fb, (delta, mu, nu, m, k, kp, F, F_sym(kp, mu, nu, delta))
    print(f"samples: {n}")
    print(f"(a) max [F_opt(m,k) - J_sym]              = {worst_a:.3e}   (<= 0 = conjecture)")
    print(f"    at (delta,mu,nu,m,k,F,J_sym) = {at_a}")
    print(f"(b) max [F_opt(m,k) - F_opt(0,k'match)]   = {worst_b:.3e}   (<= 0 = (SH'))")
    print(f"    at (delta,mu,nu,m,k,k',F,Fsym) = {at_b}")
