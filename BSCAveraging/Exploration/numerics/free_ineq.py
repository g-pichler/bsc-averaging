"""Is  rho_delta(S,T) <= G(a,b) + G(c,d)  TRUE FOR ALL two-point mean-zero pairs and
all delta -- with no fixed-point constraint?  If so the whole fixed-point analysis is
unnecessary.  Symmetric case (a=b, c=d) is sec.5d, already proved."""
import numpy as np
from scipy.optimize import minimize
at = np.arctanh
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-16); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def fz(z): return (1+z)*np.log1p(z)
def G(p,q): return (Psi(p)/p+Psi(q)/q)/(at(p)+at(q))

def gap(a,b,c,d,de):
    """rho(U;V) - G(a,b) - G(c,d);  > 0 would refute."""
    S=np.array([a,-b]); P=np.array([b,a])/(a+b)
    T=np.array([c,-d]); Q=np.array([d,c])/(c+d)
    W=P[:,None]*Q[None,:]; Z=de*np.outer(S,T)
    I=float((W*fz(Z)).sum()); L=float(-(W*np.log1p(Z)).sum())
    if I+L<=0: return -9.
    return I/(I+L)-G(a,b)-G(c,d)

EPS=1e-9
def unpack(x): return tuple(1/(1+np.exp(-xi)) for xi in x)

def obj(x, opp):
    a,b,c,d,de=unpack(x)
    if min(a,b,c,d,de)<EPS or max(a,b,c,d,de)>1-EPS: return 9.
    if opp and (a-b)*(c-d)>0: return 9.
    return -gap(a,b,c,d,de)

rng=np.random.default_rng(20260808)
# --- random sweep ---
for opp,lab in ((False,'unconstrained'),(True,'opposite skews only')):
    worst=-9; wr=None
    for _ in range(400000):
        a,b,c,d=rng.uniform(1e-4,1-1e-9,4); de=rng.uniform(.01,1-1e-9)
        if opp and (a-b)*(c-d)>0: continue
        g=gap(a,b,c,d,de)
        if g>worst: worst,wr=g,(a,b,c,d,de)
    print(f"sweep [{lab}]: max gap = {worst:+.6e}")
    print(f"    at a=%.6f b=%.6f c=%.6f d=%.6f delta=%.6f"%wr)
    # --- targeted maximization ---
    best=9.; barg=None
    for _ in range(60):
        x0=rng.uniform(-4,4,5)
        r=minimize(obj,x0,args=(opp,),method='Nelder-Mead',
                   options=dict(maxiter=4000,xatol=1e-12,fatol=1e-15))
        if r.fun<best: best,barg=r.fun,r.x
    print(f"targeted [{lab}]: max gap = {-best:+.6e}")
    print("    at a=%.8f b=%.8f c=%.8f d=%.8f delta=%.8f"%unpack(barg))
