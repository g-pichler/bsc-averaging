"""Global version of the local-rigidity theorem (NOTES.md sec.5d -> sec.5f).

Sec.5d proves that the *linearized* skew map at a symmetric fixed point of
positive value contracts: Lambda*Lambda' < x^2 < 1.  The global question is
whether the exact best-response map contracts everywhere, so that the
alternating maximization has no asymmetric fixed point at all.

Exact best response.  For T in {c,-d} with weights w_c = d/(c+d), w_d = c/(c+d)
and kappa = cd/(c+d), the objective on the S side splits as

    G(y) = E_T f(delta*y*T) - mu*Psi(y) = G_e(y) + O(y),
    G_e(y) = E_{|T|}[Psi(delta*y*|T|)] - mu*Psi(y)          (even),
    O(y)   = kappa * y * [ w(d*y) - w(c*y) ]                 (odd),

where w(u) = W(u)/u, W(u) = delta*u - f_o(delta*u), using w_c*c = w_d*d = kappa
and that w is even.  So the whole tilt away from symmetry is O, and O == 0 iff
c == d.  The best response is the pair of contact points {a,-b} of the concave
envelope of G at 0, obtained here as the exact two-atom maximum
    max over (a,b) of [b*G(a) + a*G(-b)]/(a+b).

Measured here, on the composed map T -> S -> T':
  one-step ratio    |skew S| / |skew T|          (may exceed 1; sec.5d only
                                                  bounds the product)
  two-step ratio    |skew T'| / |skew T|         (the contraction claim)
in two coordinates: the atom gap  sigma = b - a  and the third moment
m3(S) = a*b*(a-b).  Only configurations of positive value are counted -- the
value constraint is indispensable in sec.5d and without it sup Lambda*Lambda' = 4.
"""
import numpy as np

CO = 8.0
NGRID = 1200


def Psi(y):
    y = np.clip(np.abs(y), 0.0, 1 - 1e-16)
    return 0.5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


def fz(z):
    return (1 + z) * np.log1p(z)


_pos = np.tanh(np.linspace(0.004, CO, NGRID))
_A = _pos[:, None]
_B = _pos[None, :]
_AB = _A + _B


def law(a, b):
    return np.array([a, -b]), np.array([b, a]) / (a + b)


def best_response(atoms, weights, coef, delta):
    """Returns (value, b, a): the best mean-zero response is {a, -b}."""
    Gp = (fz(delta * np.outer(_pos, atoms)) * weights[None, :]).sum(axis=1) - coef * Psi(_pos)
    Gn = (fz(-delta * np.outer(_pos, atoms)) * weights[None, :]).sum(axis=1) - coef * Psi(_pos)
    V = (_B * Gp[:, None] + _A * Gn[None, :]) / _AB
    k = int(np.argmax(V))
    i, j = divmod(k, len(_pos))
    return float(V.flat[k]), float(_pos[j]), float(_pos[i])


def F_gen(a, b, c, d, mu, nu, delta):
    S, P = law(a, b)
    T, Q = law(c, d)
    K = float((P[:, None] * Q[None, :] * fz(delta * np.outer(S, T))).sum())
    return K - mu * float(P @ Psi(S)) - nu * float(Q @ Psi(T))


def m3(p, q):
    """Third moment of the mean-zero two-point law {p, -q}."""
    return p * q * (p - q)


if __name__ == "__main__":
    rng = np.random.default_rng(31337)

    worst1_s = worst2_s = worst1_m = worst2_m = 0.0
    at1 = at2 = None
    n, flips = 0, 0
    for _ in range(4000):
        delta = rng.uniform(0.1, 0.999)
        mu = rng.uniform(0.01, 0.9)
        nu = rng.uniform(0.01, 0.9)
        c, d = np.tanh(rng.uniform(0.05, CO, size=2))
        if abs(d - c) < 1e-6:
            continue
        v1, b, a = best_response(*law(c, d), mu, delta)
        v2, d2, c2 = best_response(*law(a, b), nu, delta)
        if F_gen(a, b, c2, d2, mu, nu, delta) <= 1e-9:
            continue                       # value constraint J > 0
        sT, sS, sT2 = d - c, b - a, d2 - c2
        if abs(sT) < 1e-9:
            continue
        n += 1
        if sS * sT > 0:
            flips += 1                     # would contradict the sign-flip theorem
        r1s, r2s = abs(sS) / abs(sT), abs(sT2) / abs(sT)
        if r1s > worst1_s:
            worst1_s = r1s
        if r2s > worst2_s:
            worst2_s, at2 = r2s, (delta, mu, nu, c, d, a, b, c2, d2)
        mT, mS, mT2 = m3(c, d), m3(a, b), m3(c2, d2)
        if abs(mT) > 1e-14:
            r1m, r2m = abs(mS) / abs(mT), abs(mT2) / abs(mT)
            worst1_m = max(worst1_m, r1m)
            if r2m > worst2_m:
                worst2_m, at1 = r2m, (delta, mu, nu, c, d, a, b, c2, d2)

    print(f"positive-value trials with skewed T: {n}")
    print(f"sign-flip violations (sign sS == sign sT):        {flips}")
    print(f"atom gap    max one-step |sS|/|sT|  = {worst1_s:.6f}")
    print(f"atom gap    max two-step |sT'|/|sT| = {worst2_s:.6f}   (< 1 = contraction)")
    print(f"            at {at2}")
    print(f"third mom.  max one-step |mS|/|mT|  = {worst1_m:.6f}")
    print(f"third mom.  max two-step |mT'|/|mT| = {worst2_m:.6f}   (< 1 = contraction)")
    print(f"            at {at1}")
