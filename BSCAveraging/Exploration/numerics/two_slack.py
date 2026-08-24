"""The two-slack identity of NOTES.md sec.5g.

Let S, T be independent mean-zero on [-1,1], delta in (0,1], mu >= 0, and let t
be the RATE-MATCHED symmetric partner of T,  Psi(t) = E Psi(|T|).  Put

    A_t(s) := Psi(delta*s*t) - mu*Psi(s).

Then, exactly,

    max_s A_t(s)  -  [ E f(delta*S*T) - mu*E Psi(S) ]  =  Sigma_S + Sigma_T - Omega,

    Sigma_S := max_s A_t(s) - E[ A_t(|S|) ]                        >= 0,
    Sigma_T := E_{|S|}[ Psi(delta*|S|*t) - E_{|T|} Psi(delta*|S|*|T|) ] >= 0,
    Omega   := E[ f_o(delta*S*T) ].

Sigma_S >= 0 is "max >= average".  Sigma_T >= 0 is Mrs. Gerber's Lemma applied
at parameter delta*|S| : the map  r |-> Psi(delta*|S|*Psi^{-1}(r))  is concave,
and E Psi(|T|) = Psi(t) by construction, so Jensen gives it.

Since max_s A_t(s) = Phi(+-t) is the S-optimum against the symmetric partner,

    (RM)  Phi(T) <= Phi(+-t)    <=>    Omega <= Sigma_S + Sigma_T   for all S,

and (RM) implies the conjecture (see rate_matched.py).  Sigma_S is a Jensen gap
in the |S| law, Sigma_T an MGL gap in the |T| law, and Omega is bilinear in the
two skews -- so the inequality has the AM-GM shape of sec.5d, but with all three
constants explicit and no dynamics.

Tests
  1  the identity, to machine precision
  2  Sigma_S >= 0, Sigma_T >= 0   (the latter is MGL)
  3  Omega <= Sigma_S + Sigma_T   (equivalent to (RM))

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
NGRID = 4000


def Psi(y):
    y = np.clip(np.abs(y), 0.0, 1 - 1e-16)
    return 0.5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


def fz(z):
    return (1 + z) * np.log1p(z)


def f_o(z):
    return 0.5 * ((1 + z) * np.log1p(z) - (1 - z) * np.log1p(-z))


_pos = np.tanh(np.linspace(0.0, CO, NGRID))
_PSI = Psi(_pos)


def law(a, b):
    return np.array([a, -b]), np.array([b, a]) / (a + b)


def psi_inv(r):
    return float(np.interp(r, _PSI, _pos))


def pieces(a, b, c, d, mu, delta):
    S, P = law(a, b)
    T, Q = law(c, d)
    aS, aT = np.abs(S), np.abs(T)
    t = psi_inv(float(Q @ Psi(T)))

    A = Psi(delta * _pos * t) - mu * _PSI
    maxA = float(A.max())

    lhs = maxA - (float((P[:, None] * Q[None, :] * fz(delta * np.outer(S, T))).sum())
                  - mu * float(P @ Psi(S)))
    SigS = maxA - float(P @ (Psi(delta * aS * t) - mu * Psi(aS)))
    SigT = float(P @ Psi(delta * aS * t)) \
        - float((P[:, None] * Q[None, :] * Psi(delta * np.outer(aS, aT))).sum())
    Om = float((P[:, None] * Q[None, :] * f_o(delta * np.outer(S, T))).sum())
    return lhs, SigS, SigT, Om, t


if __name__ == "__main__":
    rng = np.random.default_rng(90210)
    e_id = 0.0
    minS = minT = np.inf
    worst, at = -np.inf, None
    N = 20000
    for _ in range(N):
        delta = rng.uniform(0.02, 0.999)
        mu = rng.uniform(0.0, 1.0)
        a, b, c, d = np.tanh(rng.uniform(0.002, CO, size=4))
        lhs, SigS, SigT, Om, t = pieces(a, b, c, d, mu, delta)
        e_id = max(e_id, abs(lhs - (SigS + SigT - Om)))
        minS, minT = min(minS, SigS), min(minT, SigT)
        viol = Om - (SigS + SigT)
        if viol > worst:
            worst, at = viol, (delta, mu, a, b, c, d, t, Om, SigS, SigT)

    print(f"trials: {N}")
    print(f"[1] max |identity error|                 {e_id:.3e}")
    print(f"[2] min Sigma_S                          {minS:.3e}   (>= 0 required)")
    print(f"    min Sigma_T  (Mrs. Gerber)           {minT:.3e}   (>= 0 required)")
    print(f"[3] max (Omega - Sigma_S - Sigma_T)      {worst:.3e}   (<= 0 = (RM))")
    print(f"    at (delta,mu,a,b,c,d,t,Om,SigS,SigT) = {at}")
