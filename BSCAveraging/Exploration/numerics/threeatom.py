"""Does a THIRD atom ever beat the best 2-atom configuration?
F = E[f(delta*S*T)] - mu*E[Psi(S)] - nu*E[Psi(T)],  S,T mean-zero on [-1,1].
Compare best 2-atom vs best 3-atom (per side)."""
import numpy as np
from scipy.optimize import minimize
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-15); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def fF(z): return (1+z)*np.log1p(z)

def val(S,pS,T,pT,de,mu,nu):
    Z=de*np.outer(S,T); W=np.outer(pS,pT)
    return float((W*fF(Z)).sum()) - mu*float(pS@Psi(S)) - nu*float(pT@Psi(T))

def mk(x,n):
    """n atoms in (-1,1) with weights, projected to mean zero."""
    a=np.tanh(x[:n]); w=np.exp(x[n:2*n]); w/=w.sum()
    m=w@a
    a=a-m                      # shift to mean zero
    s=np.max(np.abs(a))
    if s>=1-1e-9: a=a*(1-1e-9)/s
    return a,w

def best(de,mu,nu,nS,nT,tries,rng):
    def neg(x):
        S,pS=mk(x[:2*nS],nS); T,pT=mk(x[2*nS:],nT)
        v=val(S,pS,T,pT,de,mu,nu)
        return -v if np.isfinite(v) else 9.
    b=-9.
    for _ in range(tries):
        x0=rng.normal(0,1.5,2*nS+2*nT)
        r=minimize(neg,x0,method='Nelder-Mead',options=dict(maxiter=3000,xatol=1e-10,fatol=1e-13))
        b=max(b,-r.fun)
    return b

rng=np.random.default_rng(20260811)
print(' delta     mu      nu    best(2,2)   best(3,3)   gain(3-2)')
worst=-9
for _ in range(14):
    de=rng.uniform(.1,.99); mu=rng.uniform(0,1); nu=rng.uniform(0,1)
    b22=best(de,mu,nu,2,2,26,rng)
    b33=best(de,mu,nu,3,3,26,rng)
    g=b33-b22
    worst=max(worst,g)
    print(' %.4f  %.4f  %.4f   %+.6e  %+.6e  %+.3e'%(de,mu,nu,b22,b33,g))
print()
print('max gain from a 3rd atom = %.3e  (<=0 up to optimiser noise => 2 atoms suffice)'%worst)
