"""Direct region-level test of MO 285151 (see NOTES.md section 5): is every sampled point of A in conv(B)?

For a sampled pair of arbitrary binary channels we get (r0,r1,r2) =
(I(U;V), I(U;X), I(Y;V)) in A.  Membership in conv(B) is an LP over a grid of
BSC points (a,b) in [0,1/2]^2 (which covers B up to relabelling):

    exists lam >= 0, sum lam = 1,  sum lam*P0 >= r0,  sum lam*P1 <= r1,
                                   sum lam*P2 <= r2.

Infeasible for some sample  ==>  counterexample to the conjecture.
"""
import numpy as np
from scipy.optimize import linprog

rng = np.random.default_rng(12345)


def xlog(a):
    a = np.asarray(a, dtype=float)
    return np.where(a > 0, a * np.log2(np.where(a > 0, a, 1.0)), 0.0)


def h(a):
    return -xlog(a) - xlog(1.0 - a)


def triple(p, s0, s1, t0, t1):
    """(I(U;V), I(U;X), I(Y;V)) in bits for cL(1|x)=s_x, cR(1|y)=t_y."""
    pU = (s0 + s1) / 2.0
    pV = (t0 + t1) / 2.0
    IUX = h(pU) - (h(s0) + h(s1)) / 2.0
    IYV = h(pV) - (h(t0) + h(t1)) / 2.0
    q11 = (1 - p) / 2.0 * (s0 * t0 + s1 * t1) + p / 2.0 * (s0 * t1 + s1 * t0)
    HUV = -(xlog(1 - pU - pV + q11) + xlog(pV - q11) + xlog(pU - q11) + xlog(q11))
    IUV = h(pU) + h(pV) - HUV
    return float(IUV), float(IUX), float(IYV)


def bsc_grid(p, n=121):
    g = np.linspace(0.0, 0.5, n)
    A, B = np.meshgrid(g, g, indexing="ij")
    A, B = A.ravel(), B.ravel()
    ap = A * (1 - p) + (1 - A) * p
    apb = ap * (1 - B) + (1 - ap) * B
    P0 = 1 - h(apb)
    P1 = 1 - h(A)
    P2 = 1 - h(B)
    return np.vstack([P0, P1, P2])


def in_convB(pt, G, tol=0.0):
    """LP feasibility: is pt = (r0,r1,r2) dominated by a convex combo of columns of G?"""
    r0, r1, r2 = pt
    N = G.shape[1]
    A_ub = np.vstack([-G[0], G[1], G[2]])
    b_ub = np.array([-r0 + tol, r1 + tol, r2 + tol])
    A_eq = np.ones((1, N))
    b_eq = np.array([1.0])
    res = linprog(np.zeros(N), A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=[(0, None)] * N, method="highs")
    return res.status == 0, res


def max_violation(p, n=41, maxiter=40, seed=1):
    """Globally maximize  R0 - (concave envelope of B at (R1,R2))  over channel pairs.

    A positive value would be a counterexample.  Observed: <= 1.1e-14 for every
    p tested, i.e. nothing beyond floating point.
    """
    from scipy.optimize import differential_evolution
    G = bsc_grid(p, n)
    N = G.shape[1]

    def env(r1, r2):
        res = linprog(-G[0], A_ub=np.vstack([G[1], G[2]]), b_ub=np.array([r1, r2]),
                      A_eq=np.ones((1, N)), b_eq=np.array([1.0]),
                      bounds=[(0, None)] * N, method="highs")
        return -res.fun if res.status == 0 else -1e9

    def neg_viol(z):
        r0, r1, r2 = triple(p, *z)
        return -(r0 - env(r1, r2))

    r = differential_evolution(neg_viol, [(0, 1)] * 4, maxiter=maxiter, popsize=12,
                               tol=1e-10, seed=seed, polish=True)
    return -r.fun, r.x


if __name__ == "__main__":
    for p in [0.0, 0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.4]:
        G = bsc_grid(p)
        worst = None
        n_fail = 0
        samples = []
        # random channels + deliberately Z/S-like ones
        for _ in range(400):
            samples.append(rng.random(4))
        for z in (0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.8):
            samples.append(np.array([0.0, z, 1 - z, 1.0]))   # Z paired with S
            samples.append(np.array([0.0, z, 0.0, z]))       # two Z channels
            samples.append(np.array([z, 1.0, 0.0, 1 - z]))
        for s in samples:
            pt = triple(p, *s)
            ok, res = in_convB(pt, G, tol=1e-9)
            if not ok:
                n_fail += 1
                if worst is None:
                    worst = (pt, s)
        print(f"p={p:.2f}: {len(samples)} sampled points of A, {n_fail} outside conv(B)"
              + (f"   first failure pt={np.round(worst[0],6)} z={np.round(worst[1],4)}" if worst else ""))
