"""Discriminant  E(z)^2 <= z^2 A_s A_t  at critical points that are the GLOBAL max of g."""
import numpy as np
from scipy.optimize import minimize
at=np.arctanh
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-15); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def E(z): return z/(1-z*z)-at(z)
def As(s,z): return s*at(z)/((1-s*s)*at(s)) - z/(1-z*z)
def g(de,mu,nu,p,q): return Psi(de*p*q)-mu*Psi(p)-nu*Psi(q)
rng=np.random.default_rng(99)
worst=-9; wr=None; n=0; notglobal=0
for _ in range(200000):
    if n>=1500: break
    s,t,de=rng.uniform(1e-4,1-1e-9,3)
    z=de*s*t
    if not(0<z<1-1e-12): continue
    a_s=As(s,z); a_t=As(t,z)
    if a_s<=0 or a_t<=0: continue
    mu=de*t*at(z)/at(s); nu=de*s*at(z)/at(t)
    if not(0<=mu<1 and 0<=nu<1): continue
    gst=g(de,mu,nu,s,t)
    if gst<0: notglobal+=1; continue          # g(0,0)=0 beats it
    ok=True
    for x0 in ((0.,0.),(3.,3.),(-3.,3.),(3.,-3.),(6.,6.),(-6.,-6.)):
        r=minimize(lambda x:-g(de,mu,nu,1/(1+np.exp(-x[0])),1/(1+np.exp(-x[1]))),x0,
                   method='Nelder-Mead',options=dict(maxiter=300,xatol=1e-11,fatol=1e-14))
        if -r.fun>gst+1e-12: ok=False; break
    if not ok: notglobal+=1; continue
    n+=1
    r=E(z)**2/(z*z*a_s*a_t)
    if r>worst: worst,wr=r,(s,t,de,z,mu,nu,a_s,a_t)
print('critical points that ARE the global max of g:',n,'  rejected (not global):',notglobal)
print('max  E(z)^2 / (z^2 A_s A_t) = %.8f   (<= 1 REQUIRED)'%worst)
if wr: print('   at s=%.6f t=%.6f de=%.6f z=%.6f mu=%.5f nu=%.5f A_s=%.4e A_t=%.4e'%wr)
