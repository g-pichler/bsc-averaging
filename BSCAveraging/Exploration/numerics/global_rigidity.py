"""Global version of the local-rigidity theorem (NOTES.md sec.5d, sec.5e).

Local rigidity says: no asymmetric branch bifurcates *from* a symmetric fixed
point.  The global question is whether an asymmetric maximizer exists anywhere.

Exact two-point parametrization (WLOG, since F is bilinear in the pair of laws
and the extreme points of the mean-zero measures on [-1,1] are two-point):

    S in {a, -b},  P(S=a) = b/(a+b),    T in {c, -d},  P(T=c) = d/(c+d),
    F = E f(delta*S*T) - mu*E Psi(S) - nu*E Psi(T),
    f(z) = (1+z)log(1+z),   Psi(y) = [(1+y)log(1+y) + (1-y)log(1-y)]/2.

Method.  For a *fixed* T the best response is the concave envelope at 0 of
G_T(y) = E f(delta*y*T) - mu*Psi(y), attained by two atoms {a,-b}, so its value
is  max over (a,b) of [b*G_T(a) + a*G_T(-b)]/(a+b) -- a plain vectorized grid
maximum.  Using no gradient optimizer avoids stalling on the zero-gradient
plateau that the artanh parametrization creates at |atom| -> 1 (the trap that
made the first version of this script report nonsense).  Alternating best
responses are monotone in F, hence convergent.

Sec.5e decomposition, which the tests below check:  with R = |S|, Q = |T|,

    F = E[g(R,Q)] + Omega,   g(r,q) = Psi(delta*r*q) - mu*Psi(r) - nu*Psi(q),
    Omega = E[f_o(delta*S*T)],   f_o(z) = [(1+z)log(1+z) - (1-z)log(1-z)]/2,

because Psi is even.  The first term sees only the magnitudes, the second only
the signs.  Since g's argument set (all probability measures on [0,1], no
mean-zero constraint) has point masses as extreme points,

    J_sym = max_{s,t in [0,1]} g(s,t),

so the conjecture J = J_sym is *equivalent* to

    Omega  <=  max g - E[g(R,Q)]        (odd gain <= Jensen slack)

for every independent mean-zero pair.  Test 5 checks that directly.

Tests
  1  global gap        max F  -  max_{s,t} g(s,t)
  2  asymmetry of the global maximizer, where J > 0
  3  sign flip         best response to a skewed T is skewed the other way
  4  contraction       alternating best responses drive both skews to zero
  5  sec.5e form       Omega <= max g - E[g(R,Q)], and its slack
"""
import numpy as np

CO = 8.0            # artanh-coordinate cap: tanh(8) = 1 - 2.3e-7
NGRID = 420


def Psi(y):
    y = np.clip(np.abs(y), 0.0, 1 - 1e-16)
    return 0.5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


def fz(z):
    return (1 + z) * np.log1p(z)


def f_o(z):
    return 0.5 * ((1 + z) * np.log1p(z) - (1 - z) * np.log1p(-z))


_pos = np.tanh(np.linspace(0.005, CO, NGRID))
_A = _pos[:, None]
_B = _pos[None, :]
_AB = _A + _B


def best_response(atoms, weights, coef, delta):
    """Best mean-zero response to a law given by (atoms, weights).

    Maximizes  E_S[ E_T f(delta*S*T) ] - coef * E Psi(S)  over mean-zero S.
    Two atoms are optimal (they are the extreme points of the mean-zero
    measures), and for S in {a,-b} the value is  [b*G(a) + a*G(-b)]/(a+b)
    with G(y) = E_T f(delta*y*T) - coef*Psi(y).  So a plain vectorized maximum
    over the (a,b) grid is exact up to the grid -- no optimizer, hence no
    stalling on the zero-gradient plateau that the artanh parametrization
    creates at |atom| -> 1.

    Returns (value, b, a), i.e. the response is {a, -b}.
    """
    Gp = (fz(delta * np.outer(_pos, atoms)) * weights[None, :]).sum(axis=1) \
        - coef * Psi(_pos)
    Gn = (fz(-delta * np.outer(_pos, atoms)) * weights[None, :]).sum(axis=1) \
        - coef * Psi(_pos)
    V = (_B * Gp[:, None] + _A * Gn[None, :]) / _AB
    k = int(np.argmax(V))
    i, j = divmod(k, len(_pos))
    return float(V.flat[k]), float(_pos[j]), float(_pos[i])


def law(a, b):
    return np.array([a, -b]), np.array([b, a]) / (a + b)


def F_gen(a, b, c, d, mu, nu, delta):
    S, P = law(a, b)
    T, Q = law(c, d)
    K = float((P[:, None] * Q[None, :] * fz(delta * np.outer(S, T))).sum())
    return K - mu * float(P @ Psi(S)) - nu * float(Q @ Psi(T))


def g(r, q, mu, nu, delta):
    return Psi(delta * r * q) - mu * Psi(r) - nu * Psi(q)


def J_sym(mu, nu, delta):
    """max over s,t in [0,1] of g(s,t) -- equals the symmetric optimum."""
    P = _pos
    M = g(P[:, None], P[None, :], mu, nu, delta)
    k = int(np.argmax(M))
    return float(M.flat[k]), float(P[k // len(P)]), float(P[k % len(P)])


def alternate(mu, nu, delta, start, iters=20):
    a, b, c, d = start
    hist = []
    for _ in range(iters):
        T, Q = law(c, d)
        _, b, a = best_response(T, Q, mu, delta)
        S, P = law(a, b)
        _, d, c = best_response(S, P, nu, delta)
        hist.append((b - a, d - c, F_gen(a, b, c, d, mu, nu, delta)))
    return np.array(hist), (a, b, c, d)


def decomposition(a, b, c, d, mu, nu, delta):
    """F = E[g(|S|,|T|)] + Omega.  Returns (Eg, Omega)."""
    S, P = law(a, b)
    T, Q = law(c, d)
    W = P[:, None] * Q[None, :]
    Eg = float((W * g(np.abs(S)[:, None], np.abs(T)[None, :], mu, nu, delta)).sum())
    Om = float((W * f_o(delta * np.outer(S, T))).sum())
    return Eg, Om


if __name__ == "__main__":
    rng = np.random.default_rng(20260807)
    deltas = [0.15, 0.35, 0.55, 0.75, 0.9, 0.99]
    grid = [0.05, 0.2, 0.4, 0.6, 0.8, 0.95]

    worst_gap, gap_at = -np.inf, None
    worst_asym, asym_at = 0.0, None
    worst_5e, w5e_at = -np.inf, None
    n_pos = 0
    for delta in deltas:
        for mu in grid:
            for nu in grid:
                js, ss, ts = J_sym(mu, nu, delta)
                best, barg = -np.inf, None
                for _ in range(6):
                    st = np.tanh(rng.uniform(0.02, CO, size=4))
                    hist, fin = alternate(mu, nu, delta, st, iters=20)
                    if hist[-1, 2] > best:
                        best, barg = float(hist[-1, 2]), fin
                if best - js > worst_gap:
                    worst_gap, gap_at = best - js, (delta, mu, nu, best, js)
                if best > 1e-9:
                    n_pos += 1
                    a, b, c, d = barg
                    asym = abs(a - b) + abs(c - d)
                    if asym > worst_asym:
                        worst_asym, asym_at = asym, (delta, mu, nu, a, b, c, d)
                # test 5 on random (not necessarily optimal) pairs
                for _ in range(30):
                    a, b, c, d = np.tanh(rng.uniform(0.02, CO, size=4))
                    Eg, Om = decomposition(a, b, c, d, mu, nu, delta)
                    viol = Om - (js - Eg)
                    if viol > worst_5e:
                        worst_5e, w5e_at = viol, (delta, mu, nu, a, b, c, d, Om, js - Eg)

    print(f"[1] max (J - J_sym) over {len(deltas)*len(grid)**2} directions "
          f"= {worst_gap:.3e}")
    print(f"    at (delta,mu,nu)=({gap_at[0]},{gap_at[1]},{gap_at[2]}) "
          f"J={gap_at[3]:.9f}  J_sym={gap_at[4]:.9f}")
    print(f"[2] {n_pos} directions with J > 0; max asymmetry |a-b|+|c-d| "
          f"of the maximizer = {worst_asym:.3e}")
    print(f"    at {asym_at}")
    print(f"[5] max (Omega - (max g - E g)) over random pairs = {worst_5e:.3e}"
          "   (<= 0 required, = conjecture)")
    print(f"    at {w5e_at}")

    print("[3] sign flip: skew of the best response vs skew of the target")
    bad = 0
    for _ in range(400):
        delta = rng.uniform(0.05, 0.999)
        mu = rng.uniform(0.02, 0.98)
        c, d = np.tanh(rng.uniform(0.02, CO, size=2))
        T, Q = law(c, d)
        val, b, a = best_response(T, Q, mu, delta)
        if val <= 1e-9 or abs(d - c) < 1e-9:
            continue
        if (b - a) * (d - c) > 1e-9:
            bad += 1
    print(f"    violations (same-sign skews at a positive-value best response): {bad}/400")

    print("[4] alternating best responses, |skew| trajectory (positive value only):")
    shown = 0
    while shown < 8:
        delta = rng.uniform(0.2, 0.99)
        mu, nu = rng.uniform(0.02, 0.6, size=2)
        st = np.tanh(rng.uniform(0.02, CO, size=4))
        hist, fin = alternate(mu, nu, delta, st, iters=20)
        if hist[-1, 2] <= 1e-9:
            continue
        sk = np.abs(hist[:, 0]) + np.abs(hist[:, 1])
        print(f"    delta={delta:.3f} mu={mu:.3f} nu={nu:.3f}  "
              f"skew {sk[0]:.3e} -> {sk[-1]:.3e}   F {hist[0,2]:.6f} -> {hist[-1,2]:.6f}")
        shown += 1
