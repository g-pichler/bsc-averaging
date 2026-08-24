"""DECISIVE: at mu,nu,delta of the F>0 point, maximise Phi over ALL (m,k,c,d).
sup F = 0 is the conjecture (attained at trivial/BSC configs).  sup F > 0 would refute it."""
import numpy as np
from scipy.optimize import minimize
import fixed_point_value as V
MU,NU,DE=0.045822,0.070104,0.393872462719
def negPhi(x):
    m=np.tanh(x[0]); k=1/(1+np.exp(-x[1]))
    c=1/(1+np.exp(-x[2])); d=1/(1+np.exp(-x[3]))
    if abs(m)+k>=1-1e-13 or k<=1e-13: return 9.
    if min(c,d)<1e-13 or max(c,d)>1-1e-13: return 9.
    v=V.Phi(m,k,c,d,MU,NU,DE)
    return -v if np.isfinite(v) else 9.
rng=np.random.default_rng(77)
best=9.;bx=None
for _ in range(4000):
    x0=[rng.uniform(-6,6),rng.uniform(-2,8),rng.uniform(-6,6),rng.uniform(-6,6)]
    r=minimize(negPhi,x0,method='Nelder-Mead',options=dict(maxiter=2000,xatol=1e-12,fatol=1e-15))
    if r.fun<best: best,bx=r.fun,r.x
m=np.tanh(bx[0]); k=1/(1+np.exp(-bx[1])); c=1/(1+np.exp(-bx[2])); d=1/(1+np.exp(-bx[3]))
print("mu=%.6f nu=%.6f delta=%.12f"%(MU,NU,DE))
print("global max Phi over (m,k,c,d) = %+.8e"%(-best))
print("   at m=%.6e k=%.10f c=%.8f d=%.8f"%(m,k,c,d))
print("   Phi at the reported point   = %+.8e"%V.Phi(1.1475e-12,0.997836072818,9.790567e-01,9.790567e-01,MU,NU,DE))
print("   sup F <= 0 is the conjecture; sup F > 0 would REFUTE it.")
