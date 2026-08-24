"""Checks of the sign/magnitude split of NOTES.md sec.5e.

    f(z) = (1+z)log(1+z) = Psi(z) + f_o(z),  Psi even, f_o odd,
    F(S,T) = E[g(|S|,|T|)] + Omega,   Omega = E[f_o(delta*S*T)],
    g(r,q) = Psi(delta*r*q) - mu*Psi(r) - nu*Psi(q).

    Wtil(u) := delta*u - f_o(delta*u) = sum_{k odd >= 3} (delta*u)^k / (k(k-1)) >= 0,
    and because E S = E T = 0 and S is independent of T,

        Omega = - E[ sign(S) sign(T) Wtil(|S| |T|) ] ,   |Omega| <= Wtil(1).

    For two-point S in {a,-b}, T in {c,-d} this becomes, with w(u) = Wtil(u)/u,
    lam = ab/(a+b), kap = cd/(c+d),

        Omega = -lam*kap*[ w(ac) - w(ad) - w(bc) + w(bd) ] ,

    a mixed second difference of the strictly supermodular kernel w(rq), so

        Omega > 0  <=>  (a-b)(c-d) < 0     (the skews point opposite ways).
"""
import numpy as np

rng = np.random.default_rng(7)


def Psi(y):
    y = np.clip(np.abs(y), 0.0, 1 - 1e-16)
    return 0.5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


def fz(z):
    return (1 + z) * np.log1p(z)


def f_o(z):
    return 0.5 * ((1 + z) * np.log1p(z) - (1 - z) * np.log1p(-z))


def law(a, b):
    return np.array([a, -b]), np.array([b, a]) / (a + b)


N = 20000
A, B, C, D = np.tanh(rng.uniform(0.01, 8.0, size=(4, N)))
MU, NU, DE = rng.uniform(0, 1, N), rng.uniform(0, 1, N), rng.uniform(0.01, 1, N)

e_split = e_sig = e_prod = 0.0
bad_sign = 0
max_abs_om, max_bound = 0.0, 0.0
for i in range(N):
    a, b, c, d, mu, nu, de = A[i], B[i], C[i], D[i], MU[i], NU[i], DE[i]
    S, P = law(a, b)
    T, Q = law(c, d)
    W = P[:, None] * Q[None, :]
    F = float((W * fz(de * np.outer(S, T))).sum()) - mu * float(P @ Psi(S)) - nu * float(Q @ Psi(T))
    Eg = float((W * (Psi(de * np.abs(np.outer(S, T))) - mu * Psi(S)[:, None]
                     - nu * Psi(T)[None, :])).sum())
    Om = float((W * f_o(de * np.outer(S, T))).sum())
    e_split = max(e_split, abs(F - (Eg + Om)))

    # Omega = -E[sign*sign*Wtil]
    Wt = lambda u: de * u - f_o(de * u)
    sg = np.outer(np.sign(S), np.sign(T))
    Om2 = -float((W * sg * Wt(np.abs(np.outer(S, T)))).sum())
    e_sig = max(e_sig, abs(Om - Om2))

    # two-point product formula
    w = lambda u: Wt(u) / u
    lam, kap = a * b / (a + b), c * d / (c + d)
    Om3 = -lam * kap * (w(a * c) - w(a * d) - w(b * c) + w(b * d))
    e_prod = max(e_prod, abs(Om - Om3))

    if Om * ((a - b) * (c - d)) > 1e-14:
        bad_sign += 1
    max_abs_om = max(max_abs_om, abs(Om))
    max_bound = max(max_bound, abs(Om) - Wt(1.0))

print(f"max |F - (Eg + Omega)|                       {e_split:.3e}")
print(f"max |Omega + E[sign*sign*Wtil(|S||T|)]|      {e_sig:.3e}")
print(f"max |Omega - two-point product formula|      {e_prod:.3e}")
print(f"sign violations  Omega*(a-b)(c-d) > 0        {bad_sign}/{N}")
print(f"max |Omega|                                  {max_abs_om:.6f}")
print(f"max (|Omega| - Wtil(1))                      {max_bound:.3e}   (<= 0 required)")
