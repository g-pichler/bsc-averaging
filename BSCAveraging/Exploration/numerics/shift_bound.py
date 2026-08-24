"""The shift bound (SH) of NOTES.md sec.5j.

In the conditional-MI coordinates of sec.5h, with m = (v0+v1)/2, k = (v0-v1)/2,

    F_opt(m,k) = -mu*A - (1-mu)*Psi(m) + conc(zeta_{m,k})(0),
    A = (Psi(m+k) + Psi(m-k))/2,   zeta_{m,k}(y) = Psi(m + k*delta*y) - nu*Psi(y),

and symmetry is m = 0.  Psi is supermodular in the sense
Psi(m+k) + Psi(m-k) >= 2 Psi(m) + 2 Psi(k)  (its mixed second derivative is
L'(m+k) - L'(m-k) > 0 and it vanishes on both axes), so A >= Psi(m) + Psi(k) and

    F_opt(m,k) <= conc(zeta_{m,k})(0) - Psi(m) - mu*Psi(k),
    F_opt(0,k)  = conc(zeta_{0,k})(0) - mu*Psi(k).

Hence the conjecture follows from

    (SH)   Gain(m,k) := conc(zeta_{m,k})(0) - conc(zeta_{0,k})(0)  <=  Psi(m).

Both sides vanish at m = 0.  Note the *raw* analogue E[Psi(m+U)] <= Psi(m) + E[Psi(U)]
is FALSE (superadditivity of Psi points the wrong way), so (SH) genuinely needs
the envelope and the nu penalty.

Tests
  1  the supermodularity  Psi(m+k) + Psi(m-k) >= 2 Psi(m) + 2 Psi(k)
  2  (SH) itself, and how tight it gets
"""
import numpy as np

CO = 8.0
NG = 900


def Psi(y):
    y = np.clip(np.abs(y), 0.0, 1 - 1e-16)
    return 0.5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


_pos = np.tanh(np.linspace(1e-4, CO, NG))
_grid = np.concatenate([-_pos[::-1], _pos])
_A2, _B2 = _pos[:, None], _pos[None, :]


def conc_at_zero(vals):
    """Concave envelope at 0, exact in two atoms: max over y-<0<y+ of the chord."""
    neg = vals[:NG][::-1]      # values at -_pos
    pos = vals[NG:]            # values at +_pos
    V = (_B2 * pos[:, None] + _A2 * neg[None, :]) / (_A2 + _B2)
    return float(V.max())


def conc_zeta(m, k, nu, delta):
    return conc_at_zero(Psi(m + k * delta * _grid) - nu * Psi(_grid))


def gain(m, k, nu, delta):
    return conc_zeta(m, k, nu, delta) - conc_zeta(0.0, k, nu, delta)


if __name__ == "__main__":
    rng = np.random.default_rng(864213)

    # 1. supermodularity of Psi
    worst1 = np.inf
    for _ in range(200000):
        m, k = rng.uniform(0, 1, 2)
        if m + k > 1:
            m, k = 1 - m, 1 - k
        worst1 = min(worst1, Psi(m + k) + Psi(m - k) - 2 * Psi(m) - 2 * Psi(k))
    print(f"[1] min [Psi(m+k)+Psi(m-k) - 2Psi(m) - 2Psi(k)] = {worst1:.3e}   (>= 0 required)")

    # 2. the shift bound
    worst, at = -np.inf, None
    worst_ratio, atr = -np.inf, None
    for _ in range(20000):
        delta = rng.uniform(0.02, 0.999)
        nu = rng.uniform(0.0, 1.0)
        m = rng.uniform(0.0, 1.0)
        k = rng.uniform(0.0, 1.0 - m)
        g = gain(m, k, nu, delta)
        viol = g - Psi(m)
        if viol > worst:
            worst, at = viol, (delta, nu, m, k, g, Psi(m))
        if Psi(m) > 1e-12:
            r = g / Psi(m)
            if r > worst_ratio:
                worst_ratio, atr = r, (delta, nu, m, k, g, Psi(m))
    print(f"[2] max [Gain(m,k) - Psi(m)] = {worst:.3e}   (<= 0 = (SH))")
    print(f"    at (delta,nu,m,k,Gain,Psi(m)) = {at}")
    print(f"    max Gain/Psi(m) = {worst_ratio:.6f}   (<= 1 required)")
    print(f"    at {atr}")
