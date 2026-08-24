"""(S):  Omega <= J_sym - E[g(|S|,|T|)]  at OPPOSITE skews.  Equivalently F <= J_sym.
Reports the ratio Omega/deficit -- where it approaches 1 the bound is tight."""
import numpy as np
from scipy.optimize import minimize
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-15); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def Fo(z):
    return (1+z)*np.log1p(z)-Psi(z)
def g(de,mu,nu,p,q): return Psi(de*p*q)-mu*Psi(p)-nu*Psi(q)
def Jsym(de,mu,nu):
    best=-9.
    for x0 in ((0.,0.),(2.,2.),(-2.,2.),(4.,4.),(-4.,-4.),(1.,-1.)):
        r=minimize(lambda x:-g(de,mu,nu,1/(1+np.exp(-x[0])),1/(1+np.exp(-x[1]))),
                   x0,method='Nelder-Mead',options=dict(maxiter=800,xatol=1e-12,fatol=1e-15))
        best=max(best,-r.fun)
    return max(best,0.)   # g(0,0)=0 is always available
rng=np.random.default_rng(424242)
worst=-9.;wr=None;n=0;viol=0
for _ in range(300000):
    a,b,c,d=rng.uniform(1e-4,1-1e-9,4); de=rng.uniform(.02,1-1e-9)
    if (a-b)*(c-d)>=0: continue          # opposite skews only
    mu=rng.uniform(0,1); nu=rng.uniform(0,1)
    N=(a+b)*(c+d)
    gs=(b*d*g(de,mu,nu,a,c)+b*c*g(de,mu,nu,a,d)+a*d*g(de,mu,nu,b,c)+a*c*g(de,mu,nu,b,d))/N
    Om=(b*d*Fo(de*a*c)-b*c*Fo(de*a*d)-a*d*Fo(de*b*c)+a*c*Fo(de*b*d))/N
    if Om<=0: continue
    J=Jsym(de,mu,nu); defc=J-gs
    n+=1
    if defc<=0: viol+=1; continue
    r=Om/defc
    if r>worst: worst,wr=r,(a,b,c,d,de,mu,nu,Om,defc,J,gs)
print(f"opposite-skew configs with Omega>0: {n}   (deficit<=0 cases: {viol})")
print(f"  max  Omega/deficit = {worst:.6f}    (<1 required; ->1 means tight)")
if wr: print("   at a=%.5f b=%.5f c=%.5f d=%.5f de=%.5f mu=%.4f nu=%.4f\n   Omega=%.4e deficit=%.4e Jsym=%.4e gSum=%.4e"%wr)
def obj(x):
    v=[1/(1+np.exp(-t)) for t in x]; a,b,c,d,de,mu,nu=v
    if (a-b)*(c-d)>=0: return 9.
    N=(a+b)*(c+d)
    gs=(b*d*g(de,mu,nu,a,c)+b*c*g(de,mu,nu,a,d)+a*d*g(de,mu,nu,b,c)+a*c*g(de,mu,nu,b,d))/N
    Om=(b*d*Fo(de*a*c)-b*c*Fo(de*a*d)-a*d*Fo(de*b*c)+a*c*Fo(de*b*d))/N
    if Om<=0: return 9.
    J=Jsym(de,mu,nu); defc=J-gs
    if defc<=0: return -9.
    return -Om/defc
best=9.;barg=None
for _ in range(40):
    r=minimize(obj,rng.uniform(-4,4,7),method='Nelder-Mead',options=dict(maxiter=1500,xatol=1e-11,fatol=1e-14))
    if r.fun<best: best,barg=r.fun,r.x
print(f"  targeted max Omega/deficit = {-best:.6f}")
v=[1/(1+np.exp(-t)) for t in barg]
print("   at a=%.6f b=%.6f c=%.6f d=%.6f de=%.6f mu=%.4f nu=%.4f"%tuple(v))
