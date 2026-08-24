"""Sample (delta,mu,nu), SOLVE for the global maximiser (s,t) of g, then test the
discriminant  E(z)^2 <= z^2 A_s A_t.  Globality holds by construction."""
import numpy as np
from scipy.optimize import minimize
at=np.arctanh
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-15); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def E(z): return z/(1-z*z)-at(z)
def As(s,z): return s*at(z)/((1-s*s)*at(s)) - z/(1-z*z)
def g(de,mu,nu,p,q): return Psi(de*p*q)-mu*Psi(p)-nu*Psi(q)
rng=np.random.default_rng(20260809)
worst=-9; wr=None; n=0; trivial=0
for _ in range(60000):
    if n>=3000: break
    de=rng.uniform(.02,1-1e-9)
    if rng.integers(0,2): mu,nu=rng.uniform(0,1,2)
    else: mu,nu=10**rng.uniform(-6,0,2)
    best=0.; bx=None                       # g(0,0)=0 always available
    for x0 in ((0.,0.),(3.,3.),(-3.,3.),(3.,-3.),(6.,6.),(5.,-5.),(-5.,5.),(8.,8.)):
        r=minimize(lambda x:-g(de,mu,nu,1/(1+np.exp(-x[0])),1/(1+np.exp(-x[1]))),x0,
                   method='Nelder-Mead',options=dict(maxiter=900,xatol=1e-13,fatol=1e-16))
        if -r.fun>best: best,bx=-r.fun,r.x
    if bx is None: trivial+=1; continue     # sup attained at the trivial pair
    s,t=1/(1+np.exp(-bx[0])),1/(1+np.exp(-bx[1]))
    if min(s,t)<1e-9 or max(s,t)>1-1e-11: trivial+=1; continue
    z=de*s*t
    a_s=As(s,z); a_t=As(t,z)
    if a_s<=0 or a_t<=0: trivial+=1; continue
    n+=1
    r=E(z)**2/(z*z*a_s*a_t)
    if r>worst: worst,wr=r,(s,t,de,z,mu,nu,a_s,a_t)
print('interior global maximisers tested:',n,'   (trivial/boundary sup:',trivial,')')
print('max  E(z)^2 / (z^2 A_s A_t) = %.8e    (<= 1 REQUIRED)'%worst)
if wr: print('   at s=%.6f t=%.6f de=%.6f z=%.6f mu=%.5f nu=%.5f A_s=%.4e A_t=%.4e'%wr)
