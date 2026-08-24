"""Asymmetric fixed points in the dangerous regime (NOTES.md sec.6).

Positive value needs contact points near +-1 (sec.6 item 4), i.e. k -> 1 with m
small.  Section 5d already rules out asymmetric fixed points in a neighbourhood
of the symmetric positive-value branch (the linearized skew map contracts), so
this scan probes the region just outside: tiny m, k close to 1.
"""
import numpy as np
from scipy.optimize import fsolve
import fixed_point_value as V

rng = np.random.default_rng(31337)
best, at, n, near = -np.inf, None, 0, 0
for _ in range(25000):
    m = 10 ** rng.uniform(-7, -1.0)
    k = 1 - m - 10 ** rng.uniform(-6, -0.3)
    if k <= 0:
        continue
    de = rng.uniform(0.3, 0.999)
    sol, info, ier, msg = fsolve(V.eqs, [np.tanh(rng.uniform(1., 5.)), np.tanh(rng.uniform(1., 5.))],
                                 args=(m, k, de), full_output=True)
    if ier != 1:
        continue
    c, d = sol
    if not (1e-6 < c < 1 - 1e-12 and 1e-6 < d < 1 - 1e-12):
        continue
    if max(abs(np.array(V.eqs(sol, m, k, de)))) > 1e-11:
        continue
    p = V.pieces(m, k, c, d, de)
    mu, nu = p[12], p[13]
    if not (np.isfinite(mu) and 0 <= mu < 1 and 0 <= nu < 1):
        continue
    a, b = k / (1 + m), k / (1 - m)
    if a >= 1 or b >= 1 or abs(a - b) < 1e-12:
        continue
    F = V.Phi(m, k, c, d, mu, nu, de)
    n += 1
    if max(a, b, c, d) > 0.99:
        near += 1
    if F > best:
        best, at = F, (m, k, de, a, b, c, d, mu, nu)
print('asymmetric fixed points in the dangerous regime :', n)
print('   of which with some contact point > 0.99      :', near)
print('max F over them                                 :', f'{best:.6e}')
print('at (m,k,delta,a,b,c,d,mu,nu) =', at)
