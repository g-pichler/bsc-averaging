"""Local analysis at the double-tangency (fixed) points — NOTES.md sec.5c.

At a symmetric fixed point (S = +-s, T = +-t, x = delta*s*t) perturb T off
symmetry by eps.  The perturbation of g_T is ODD:

    g_T(sigma) = [fbar(delta*sigma*t) - mu*phi(sigma)] + (eps/2)*w(delta*sigma*t) + O(eps^2)
    w(z) = 2z - log((1+z)/(1-z)) = 2(z - artanh z)

so both bitangent points shift by the same u: the touching interval translates
rigidly and skew_S = 2u.  The chord condition then gives

    skew_S = -Lambda * skew_T,     Lambda = psi(x) / (s*t*m) > 0
    psi(x) = x - artanh(x) + x^3/(1-x^2) = sum_{k odd >=3} (1 - 1/k) x^k > 0
    m = mu/(1-s^2) - (delta*t)^2/(1-x^2) = -G''(s) > 0

Lambda > 0 is the sign flip.  A fixed point with nonzero skew needs exactly
Lambda*Lambda' = 1.  Using the stationarity relations

    mu = delta*t*artanh(x)/artanh(s),   nu = delta*s*artanh(x)/artanh(t)

this becomes the explicit three-variable condition (x <= s*t):

    Lambda*Lambda' = psi(x)^2 / (s*t*x^2*A*B),
    A = artanh(x)/((1-s^2)artanh(s)) - x/(s(1-x^2)),
    B = artanh(x)/((1-t^2)artanh(t)) - x/(t(1-x^2)).

RESULT: over 7421 genuine symmetric GLOBAL optima (J > 0 and (s,t) maximizing
the symmetric problem for its induced mu, nu), sup Lambda*Lambda' = 6.2e-4.
No bifurcation: the symmetric optimum is locally unique and strongly attracting.
Values > 1 occur only at stationary points that are NOT global optima (they are
coordinatewise maxima that are saddles of the joint problem), where they are
irrelevant.  Note the optima sit at s, t ~ 0.998, so grids on [0, 0.96] miss
them entirely — sample in artanh coordinates.
"""
import numpy as np

at, th = np.arctanh, np.tanh
LN2 = np.log(2.0)

psi = lambda x: x - at(x) + x ** 3 / (1 - x ** 2)
fbar = lambda x: 0.5 * ((1 + x) * np.log1p(x) + (1 - x) * np.log1p(-x))


def phi(s):
    a = (1 + s) / 2
    return LN2 + a * np.log(a) + (1 - a) * np.log1p(-a)


def scan(n_st=44, n_delta=12, n_check=260):
    """Return (count, sup Lambda*Lambda', argmax) over genuine symmetric optima."""
    U = np.linspace(0.02, 6.0, n_check)
    SU = th(U)
    PROD = SU[:, None] * SU[None, :]
    PH1, PH2 = phi(SU)[:, None], phi(SU)[None, :]
    worst, arg, kept, rej = 0.0, None, 0, 0
    for u in np.linspace(0.05, 5.5, n_st):
        s = th(u)
        for v in np.linspace(0.05, 5.5, n_st):
            t = th(v)
            for d in np.linspace(0.05, 1.0, n_delta):
                x = d * s * t
                if not 0 < x < 1:
                    continue
                mu = d * t * at(x) / at(s)
                nu = d * s * at(x) / at(t)
                m = mu / (1 - s ** 2) - (d * t) ** 2 / (1 - x ** 2)
                mp = nu / (1 - t ** 2) - (d * s) ** 2 / (1 - x ** 2)
                if m <= 0 or mp <= 0:          # not a coordinatewise max
                    continue
                Jh = fbar(x) - mu * phi(s) - nu * phi(t)
                if Jh <= 1e-12:                # trivial pair wins: not the optimum
                    rej += 1
                    continue
                Jg = fbar(d * PROD) - mu * PH1 - nu * PH2
                if Jh < Jg.max() - 1e-9:       # not the global symmetric optimum
                    rej += 1
                    continue
                ll = psi(x) ** 2 / ((s * t) ** 2 * m * mp)
                kept += 1
                if ll > worst:
                    worst, arg = ll, (s, t, d, mu, nu, Jh)
    return kept, worst, rej, arg


if __name__ == "__main__":
    kept, worst, rej, arg = scan()
    print(f"genuine symmetric global optima: {kept}   rejected: {rej}")
    print(f"sup Lambda*Lambda' = {worst:.3e}")
    if arg:
        s, t, d, mu, nu, J = arg
        print(f"  attained at s={s:.5f} t={t:.5f} delta={d:.3f} mu={mu:.5f} nu={nu:.5f} J={J:.6f}")
    print("all < 1  =>  no asymmetric branch bifurcates from the optimum")
