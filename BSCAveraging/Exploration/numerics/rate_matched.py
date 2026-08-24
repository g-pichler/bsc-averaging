"""Does rate-matched symmetrization of ONE side ever lose?  (NOTES.md sec.5g)

Corollary 3 of sec.5e says the conjecture is equivalent to

    Omega <= max g - E[g(|S|,|T|)]   for every independent mean-zero pair,

which is just  F(S,T) <= max_{s,t} g(s,t) = J_sym.  Write

    Phi(T) := max over mean-zero S of [ E f(delta*S*T) - mu*E Psi(|S|) ],

so that  F(S,T) = Phi(T) - nu*E Psi(|T|)  once S is optimized.  Replacing T by
the SYMMETRIC law +-t with the same rate,  Psi(t) = E Psi(|T|),  leaves the nu
term untouched.  So the conjecture would follow from the one-sided claim

    (RM)   Phi(T) <= Phi(+-t)      whenever  Psi(t) = E Psi(|T|),

because once T is symmetric the optimal S is symmetric (classical), so
F <= max_{s,t} g(s,t) = J_sym.  Note (RM) does not mention nu.

(RM) is NOT the false pointwise claim I(U;V) <= log2 - h(a*p*b): here the S side
is optimized out, and it is exactly that optimization which can absorb the
Z-channel gain.

This script tests (RM) on two-point T = {c,-d} (the extreme points).

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
NGRID = 1500


def Psi(y):
    y = np.clip(np.abs(y), 0.0, 1 - 1e-16)
    return 0.5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


def fz(z):
    return (1 + z) * np.log1p(z)


_pos = np.tanh(np.linspace(0.0005, CO, NGRID))
_A = _pos[:, None]
_B = _pos[None, :]
_AB = _A + _B
_PSI = Psi(_pos)


def law(a, b):
    return np.array([a, -b]), np.array([b, a]) / (a + b)


def Phi(atoms, weights, mu, delta):
    """max over mean-zero S of E f(delta*S*T) - mu*E Psi(|S|), exact in two atoms."""
    Gp = (fz(delta * np.outer(_pos, atoms)) * weights[None, :]).sum(axis=1) - mu * _PSI
    Gn = (fz(-delta * np.outer(_pos, atoms)) * weights[None, :]).sum(axis=1) - mu * _PSI
    V = (_B * Gp[:, None] + _A * Gn[None, :]) / _AB
    return float(V.max())


def Phi_sym(t, mu, delta):
    """Same, for the symmetric law +-t: G is even, so the value is max_y G(y)."""
    return float(np.max(Psi(delta * t * _pos) - mu * _PSI))


def psi_inv(r):
    """t in [0,1] with Psi(t) = r, by interpolation on the Psi grid."""
    return float(np.interp(r, _PSI, _pos))


if __name__ == "__main__":
    rng = np.random.default_rng(4242)
    worst, at = -np.inf, None
    worst_rel, n = -np.inf, 0
    for _ in range(20000):
        delta = rng.uniform(0.02, 0.999)
        mu = rng.uniform(0.0, 1.0)
        c, d = np.tanh(rng.uniform(0.002, CO, size=2))
        T, Q = law(c, d)
        r = float(Q @ Psi(T))                       # E Psi(|T|)
        t = psi_inv(r)
        lhs, rhs = Phi(T, Q, mu, delta), Phi_sym(t, mu, delta)
        n += 1
        viol = lhs - rhs
        if viol > worst:
            worst, at = viol, (delta, mu, c, d, t, lhs, rhs)
        scale = max(abs(rhs), 1e-12)
        worst_rel = max(worst_rel, viol / scale)

    print(f"trials: {n}")
    print(f"max (Phi(T) - Phi(+-t))          = {worst:.6e}   (<= 0 required)")
    print(f"max relative violation           = {worst_rel:.6e}")
    print(f"at (delta,mu,c,d,t,lhs,rhs) = {at}")
