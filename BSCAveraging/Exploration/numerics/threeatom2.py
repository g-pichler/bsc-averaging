"""Two atoms suffice?  Targeted at (delta,mu,nu) with NONTRIVIAL optimum (J_sym>0)."""
import numpy as np
from scipy.optimize import minimize
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-15); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def fF(z): return (1+z)*np.log1p(z)
def val(S,pS,T,pT,de,mu,nu):
    Z=de*np.outer(S,T); W=np.outer(pS,pT)
    return float((W*fF(Z)).sum()) - mu*float(pS@Psi(S)) - nu*float(pT@Psi(T))
def mk(x,n):
    a=np.tanh(x[:n]); w=np.exp(np.clip(x[n:2*n],-30,30)); w=w/w.sum()
    a=a-w@a
    s=np.max(np.abs(a))
    if s>=1-1e-9: a=a*(1-1e-9)/max(s,1e-300)
    return a,w
def best(de,mu,nu,nS,nT,tries,rng):
    def neg(x):
        S,pS=mk(x[:2*nS],nS); T,pT=mk(x[2*nS:],nT)
        v=val(S,pS,T,pT,de,mu,nu)
        return -v if np.isfinite(v) else 9.
    b=-9.
    for _ in range(tries):
        r=minimize(neg,rng.normal(0,1.5,2*nS+2*nT),method='Nelder-Mead',
                   options=dict(maxiter=4000,xatol=1e-11,fatol=1e-14))
        b=max(b,-r.fun)
    return b
rng=np.random.default_rng(4242)
print(' delta    mu      nu      best(2,2)      best(3,3)      gain33     best(3,2)      gain32')
worst=-9; ninf=0
for de,mu,nu in [(.95,.05,.05),(.9,.1,.1),(.99,.02,.03),(.85,.15,.05),(.98,.05,.2),
                 (.9,.3,.05),(.95,.2,.2),(.99,.1,.4),(.8,.05,.1),(.97,.35,.12)]:
    b22=best(de,mu,nu,2,2,30,rng)
    if b22<=1e-12:
        print(' %.3f  %.4f  %.4f   trivial optimum (J_sym=0) - uninformative'%(de,mu,nu)); continue
    ninf+=1
    b33=best(de,mu,nu,3,3,30,rng); b32=best(de,mu,nu,3,2,30,rng)
    worst=max(worst,b33-b22,b32-b22)
    print(' %.3f  %.4f  %.4f   %+.7e  %+.7e  %+.2e  %+.7e  %+.2e'%(de,mu,nu,b22,b33,b33-b22,b32,b32-b22))
print()
print('informative configurations: %d'%ninf)
print('max gain from extra atoms = %.3e   (<=0 up to noise => 2 atoms suffice)'%worst)
