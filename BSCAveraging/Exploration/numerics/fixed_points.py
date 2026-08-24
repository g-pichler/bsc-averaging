"""Enumerate fixed points of the alternating maximization for MO 285151.

Bias coordinates (NOTES.md sec.2), nats:
    S has atoms (-a, b), weights (b, a)/(a+b);  T has atoms (-c, d), weights (d, c)/(c+d).
    J = E f(d*S*T) - mu E phi(S) - nu E phi(T),  f(z)=(1+z)ln(1+z), phi(s)=ln2-h2((1+s)/2).

One side's update = concave envelope at 0 of g(s) = E_T f(delta s T) - mu phi(s),
i.e. the best chord through 0.  A fixed point of iterating both updates is what
"symmetric fixed point?" refers to.
"""
import numpy as np

LN2 = np.log(2.0)


def xlogx(a):
    a = np.asarray(a, dtype=float)
    return np.where(a > 0, a * np.log(np.where(a > 0, a, 1.0)), 0.0)


def h2(x):
    return -xlogx(x) - xlogx(1 - x)


def phi(s):
    return LN2 - h2((1 + s) / 2)


def f(z):
    return np.where(1 + z > 0, (1 + z) * np.log(np.where(1 + z > 0, 1 + z, 1.0)), 0.0)


def g_of(s, delta, mu, c, d):
    """E_T f(delta*s*T) - mu*phi(s) for T with atoms (-c,d), weights (d,c)/(c+d)."""
    w = c + d
    if w <= 0:
        return -mu * phi(s)
    r0, r1 = d / w, c / w
    return r0 * f(-delta * s * c) + r1 * f(delta * s * d) - mu * phi(s)


def best_chord(gfun, n=801):
    """max over s- in [-1,0], s+ in [0,1] of the chord through 0; returns (val, a, b)."""
    sm = np.linspace(-1.0, 0.0, n)
    sp = np.linspace(0.0, 1.0, n)
    gm, gp = gfun(sm), gfun(sp)
    SM, SP = np.meshgrid(sm, sp, indexing="ij")
    GM, GP = np.meshgrid(gm, gp, indexing="ij")
    den = SP - SM
    with np.errstate(divide="ignore", invalid="ignore"):
        val = np.where(den > 0, (SP * GM - SM * GP) / np.where(den > 0, den, 1.0), 0.0)
    i = np.unravel_index(np.argmax(val), val.shape)
    return float(val[i]), float(-sm[i[0]]), float(sp[i[1]])


def alt_max(delta, mu, nu, init, iters=60, n=401):
    a, b, c, d = init
    for _ in range(iters):
        _, a, b = best_chord(lambda s: g_of(s, delta, mu, c, d), n)
        _, c, d = best_chord(lambda t: g_of(t, delta, nu, a, b), n)
    return a, b, c, d


def J(delta, mu, nu, a, b, c, d):
    wS, wT = a + b, c + d
    if wS <= 0 or wT <= 0:
        return 0.0
    pi = np.array([b, a]) / wS
    rho = np.array([d, c]) / wT
    s = np.array([-a, b])
    t = np.array([-c, d])
    out = sum(pi[u] * rho[v] * f(delta * s[u] * t[v]) for u in (0, 1) for v in (0, 1))
    return float(out - mu * (pi @ phi(s)) - nu * (rho @ phi(t)))


def J_sym(delta, mu, nu, n=601):
    s = np.linspace(0, 1, n)
    S, T = np.meshgrid(s, s, indexing="ij")
    fbar = (f(delta * S * T) + f(-delta * S * T)) / 2
    return float(np.max(fbar - mu * phi(S) - nu * phi(T)))


def asym(a, b, c, d, tol=5e-3):
    return abs(a - b) > tol or abs(c - d) > tol


if __name__ == "__main__":
    rng = np.random.default_rng(3)
    print(f"{'p':>5} {'mu':>5} {'nu':>5} | {'#fp':>4} {'#asym':>6} | "
          f"{'best asym J':>12} {'J_sym':>10} {'asymJ - J_sym':>14}")
    for p in [0.0, 0.05, 0.1, 0.2, 0.3]:
        delta = 1 - 2 * p
        for (mu, nu) in [(0.2, 0.2), (0.1, 0.5), (0.05, 0.3), (0.4, 0.4), (0.3, 0.1)]:
            fps, best_a, n_asym = [], -9e9, 0
            for _ in range(14):
                init = rng.random(4)
                fp = alt_max(delta, mu, nu, init, iters=25, n=301)
                v = J(delta, mu, nu, *fp)
                fps.append((np.round(fp, 3), round(v, 6)))
                if asym(*fp):
                    n_asym += 1
                    best_a = max(best_a, v)
            js = J_sym(delta, mu, nu)
            uniq = len({tuple(x[0]) for x in fps})
            ba = f"{best_a:12.6f}" if n_asym else f"{'—':>12}"
            gap = f"{best_a - js:+14.3e}" if n_asym else f"{'—':>14}"
            print(f"{p:5.2f} {mu:5.2f} {nu:5.2f} | {uniq:4d} {n_asym:6d} | {ba} {js:10.6f} {gap}")
