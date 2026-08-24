"""Do  mu<1 and nu<1  ALONE imply  rho(U;V) <= rho(U;X)+rho(Y;V)?
mu>=1 or nu>=1 are already proved cases, so we may assume both < 1.  If this works
we never need the stationarity equation E4 -- only the two multiplier bounds."""
import numpy as np
from scipy.optimize import minimize
at=np.arctanh
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-16); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def fz(z): return (1+z)*np.log1p(z)
def G(p,q): return (Psi(p)/p+Psi(q)/q)/(at(p)+at(q))

def data(a,b,c,d,de):
    m=(b-a)/(a+b); k=2*a*b/(a+b)
    if not (abs(m)+k<1-1e-12): return None
    b1,b2=m+k*de*c, m-k*de*d
    if not (-1+1e-13<b1<1-1e-13 and -1+1e-13<b2<1-1e-13): return None
    Dl=at(b1)-at(b2); D=at(m+k)-at(m-k); kap=c*d/(c+d)
    mu=2*de*kap*Dl/D; nu=k*de*Dl/(at(c)+at(d))
    S=np.array([a,-b]);P=np.array([b,a])/(a+b);T=np.array([c,-d]);Q=np.array([d,c])/(c+d)
    W=P[:,None]*Q[None,:];Z=de*np.outer(S,T)
    I=float((W*fz(Z)).sum());L=float(-(W*np.log1p(Z)).sum())
    if I+L<=0: return None
    return mu,nu,I/(I+L)-G(a,b)-G(c,d)

EPS=1e-9
def obj(x):
    v=[1/(1+np.exp(-xi)) for xi in x]
    a,b,c,d,de=v
    if min(v)<EPS or max(v)>1-EPS: return 9.
    r=data(a,b,c,d,de)
    if r is None: return 9.
    mu,nu,gap=r
    if not (np.isfinite(mu) and np.isfinite(nu)): return 9.
    if mu>=1 or nu>=1 or mu<0 or nu<0: return 9.       # only the unproved regime
    return -gap

rng=np.random.default_rng(1234)
worst=-9; wr=None; n=0
for _ in range(600000):
    a,b,c,d=rng.uniform(1e-4,1-1e-9,4); de=rng.uniform(.01,1-1e-9)
    r=data(a,b,c,d,de)
    if r is None: continue
    mu,nu,gap=r
    if not(np.isfinite(mu) and np.isfinite(nu)) or mu>=1 or nu>=1 or mu<0 or nu<0: continue
    n+=1
    if gap>worst: worst,wr=gap,(a,b,c,d,de,mu,nu)
print(f"sweep: {n} configs with 0<=mu<1, 0<=nu<1")
print(f"  max [rho_UV - rho_UX - rho_YV] = {worst:+.6e}   (<= 0 = claim)")
if wr: print("    a=%.6f b=%.6f c=%.6f d=%.6f delta=%.6f  mu=%.4f nu=%.4f"%wr)
best=9.;barg=None
for _ in range(80):
    r=minimize(obj,rng.uniform(-4,4,5),method='Nelder-Mead',
               options=dict(maxiter=4000,xatol=1e-12,fatol=1e-15))
    if r.fun<best: best,barg=r.fun,r.x
v=[1/(1+np.exp(-xi)) for xi in barg]
rr=data(*v)
print(f"targeted: max gap = {-best:+.6e}")
if rr: print("    a=%.8f b=%.8f c=%.8f d=%.8f delta=%.8f  mu=%.5f nu=%.5f"%(*v,rr[0],rr[1]))
