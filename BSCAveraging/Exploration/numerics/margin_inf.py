"""Is the ratio-form margin  G(a,b)+G(c,d)-rho(U;V)  uniformly bounded below on the
fixed-point manifold?  Seeded minimisation from the known-low configurations."""
import numpy as np
from scipy.optimize import fsolve, minimize
import fixed_point_value as V
at=np.arctanh
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-15); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def G(p,q): return (Psi(p)/p+Psi(q)/q)/(at(p)+at(q))
def fz(z): return (1+z)*np.log1p(z)

def margin(m,k,de,seed=(.5,.5),nondeg=True):
    sol,info,ier,msg=fsolve(V.eqs,list(seed),args=(m,k,de),full_output=True)
    if ier!=1: return None
    c,d=sol
    if not(1e-12<c<1-1e-13 and 1e-12<d<1-1e-13): return None
    if max(abs(np.array(V.eqs(sol,m,k,de))))>1e-10: return None
    p=V.pieces(m,k,c,d,de); mu,nu=p[12],p[13]
    if not(np.isfinite(mu) and np.isfinite(nu) and 0<=mu<1 and 0<=nu<1): return None
    a,b=k/(1+m),k/(1-m)
    if a>=1 or b>=1: return None
    S=np.array([a,-b]);P=np.array([b,a])/(a+b);T=np.array([c,-d]);Q=np.array([d,c])/(c+d)
    W=P[:,None]*Q[None,:];Z=de*np.outer(S,T)
    I=float((W*fz(Z)).sum());L=float(-(W*np.log1p(Z)).sum())
    if I+L<=0: return None
    return dict(marg=G(a,b)+G(c,d)-I/(I+L),a=a,b=b,c=c,d=d,mu=mu,nu=nu,rho=I/(I+L),
                Ga=G(a,b),Gc=G(c,d))

def obj(x,seed):
    m=10**x[0]; k=1/(1+np.exp(-x[1])); de=1/(1+np.exp(-x[2]))
    if not(1e-12<m<.95 and 0<k<1-m and 0<de<1): return 9.
    r=margin(m,k,de,seed)
    return 9. if r is None else r['marg']

seeds=[(.5,.5),(.95,.9),(.99,.95),(.2,.8),(.9,.2),(.05,.05)]
starts=[(-4.85,np.log(0.999977/(1-0.999977)),np.log(0.999958/(1-0.999958))),
        (-1.45,np.log(0.847348/(1-0.847348)),np.log(0.973861/(1-0.973861)))]
rng=np.random.default_rng(2718)
for _ in range(30): starts.append((rng.uniform(-7,-.2),rng.uniform(-1,7),rng.uniform(0,7)))
best=9.;barg=None;bseed=None
for sd in seeds:
    for x0 in starts:
        r=minimize(obj,list(x0),args=(sd,),method='Nelder-Mead',
                   options=dict(maxiter=600,xatol=1e-11,fatol=1e-14))
        if r.fun<best: best,barg,bseed=r.fun,r.x,sd
m=10**barg[0]; k=1/(1+np.exp(-barg[1])); de=1/(1+np.exp(-barg[2]))
r=margin(m,k,de,bseed)
print("targeted MIN of ratio-form margin over fixed points = %.6f"%best)
if r: print("   at m=%.4e k=%.6f delta=%.6f  a=%.5f b=%.5f c=%.5f d=%.5f"%(m,k,de,r['a'],r['b'],r['c'],r['d']))
if r: print("   Ga=%.5f Gc=%.5f rho=%.5f mu=%.5f nu=%.5f"%(r['Ga'],r['Gc'],r['rho'],r['mu'],r['nu']))
