"""(S'):  Omega <= Psi(delta*s*t) - E[Psi(delta|S||T|)]   with  Psi(s)=E[Psi(|S|)],
Psi(t)=E[Psi(|T|)].  No mu, no nu, no maximisation.  Opposite skews."""
import numpy as np
from scipy.optimize import brentq, minimize
at=np.arctanh
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-15); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def Fo(z): return (1+z)*np.log1p(z)-Psi(z)
L2=np.log(2.)
def Psinv(v):
    if v<=0: return 0.
    if v>=L2*(1-1e-14): return 1-1e-14
    return brentq(lambda y: Psi(y)-v, 0., 1-1e-14, xtol=1e-15, rtol=1e-15)
def ratio(a,b,c,d,de):
    N=(a+b)*(c+d)
    Om=(b*d*Fo(de*a*c)-b*c*Fo(de*a*d)-a*d*Fo(de*b*c)+a*c*Fo(de*b*d))/N
    if Om<=0: return None
    pa,pb=b/(a+b),a/(a+b); qc,qd=d/(c+d),c/(c+d)
    s=Psinv(pa*Psi(a)+pb*Psi(b)); t=Psinv(qc*Psi(c)+qd*Psi(d))
    EP=(pa*qc*Psi(de*a*c)+pa*qd*Psi(de*a*d)+pb*qc*Psi(de*b*c)+pb*qd*Psi(de*b*d))
    gap=Psi(de*s*t)-EP
    return Om,gap,s,t
rng=np.random.default_rng(31337)
worst=-9;wr=None;n=0;bad=0
for _ in range(400000):
    a,b,c,d=rng.uniform(1e-5,1-1e-9,4); de=rng.uniform(.01,1-1e-9)
    if (a-b)*(c-d)>=0: continue
    r=ratio(a,b,c,d,de)
    if r is None: continue
    Om,gap,s,t=r; n+=1
    if gap<-1e-15: bad+=1
    if gap<=0: continue
    q=Om/gap
    if q>worst: worst,wr=q,(a,b,c,d,de,Om,gap,s,t)
print(f"opposite-skew pairs with Omega>0: {n}   (MGL gap < 0 cases: {bad})")
print(f"  max Omega / MGLgap = {worst:.6f}    (<= 1 required = (S'))")
if wr: print("   at a=%.6f b=%.6f c=%.6f d=%.6f de=%.6f\n   Omega=%.4e gap=%.4e s=%.6f t=%.6f"%wr)
def obj(x):
    v=[1/(1+np.exp(-u)) for u in x]; a,b,c,d,de=v
    if (a-b)*(c-d)>=0: return 9.
    if min(v)<1e-12 or max(v)>1-1e-12: return 9.
    r=ratio(a,b,c,d,de)
    if r is None: return 9.
    Om,gap,s,t=r
    if gap<=0: return -9.
    return -Om/gap
best=9.;barg=None
for _ in range(60):
    r=minimize(obj,rng.uniform(-4,4,5),method='Nelder-Mead',options=dict(maxiter=2500,xatol=1e-12,fatol=1e-15))
    if r.fun<best: best,barg=r.fun,r.x
print(f"  targeted max Omega/MGLgap = {-best:.6f}")
print("   at a=%.8f b=%.8f c=%.8f d=%.8f de=%.8f"%tuple(1/(1+np.exp(-u)) for u in barg))
