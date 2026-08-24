"""Is F_opt(m,k) non-increasing in m at fixed k?  (NOTES.md sec.6, route 1)

F_opt is even in m, and sec.5d gives negative curvature at m = 0.  If it were
monotone decreasing in m on [0, 1-k] for every k, the conjecture would follow
at once, since symmetry is m = 0.
"""
import numpy as np
import shift_bound as S

rng = np.random.default_rng(20260807)
worst, at = -np.inf, None
bad = 0
N = 1500
for _ in range(N):
    delta = rng.uniform(0.02, 0.999)
    mu = rng.uniform(0.0, 0.999)
    nu = rng.uniform(0.0, 0.999)
    k = rng.uniform(0.0, 0.999)
    ms = np.linspace(0.0, 1.0 - k, 40)
    vals = []
    for m in ms:
        A = 0.5 * (S.Psi(m + k) + S.Psi(m - k))
        vals.append(-mu * A - (1 - mu) * S.Psi(m) + S.conc_zeta(m, k, nu, delta))
    d = np.diff(np.array(vals))
    if d.max() > 1e-10:
        bad += 1
        if d.max() > worst:
            worst, at = d.max(), (delta, mu, nu, k, float(ms[int(np.argmax(d))]))
print(f"samples: {N}")
print(f"non-monotone (some increase in m): {bad}/{N}")
print(f"max increase along m = {worst:.3e}   (<= 0 would close the conjecture)")
print(f"at (delta,mu,nu,k,m) = {at}")
