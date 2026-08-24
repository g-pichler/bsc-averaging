"""Test the scale-free margin bounds.  Sampler DELIBERATELY driven into k->1, delta->1,
nu->1 -- the regions the previous samplers structurally could not reach."""
import numpy as np
from scipy.optimize import fsolve, minimize
import fixed_point_value as V
at=np.arctanh
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-15); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def G(p,q): return (Psi(p)/p+Psi(q)/q)/(at(p)+at(q))
def fz(z): return (1+z)*np.log1p(z)

def evaluate(m,k,de,seed):
    sol,info,ier,msg=fsolve(V.eqs,list(seed),args=(m,k,de),full_output=True)
    if ier!=1: return None
    c,d=sol
    if not(1e-13<c<1-1e-14 and 1e-13<d<1-1e-14): return None
    if max(abs(np.array(V.eqs(sol,m,k,de))))>1e-9: return None
    p=V.pieces(m,k,c,d,de); mu,nu=p[12],p[13]
    if not(np.isfinite(mu) and np.isfinite(nu) and 0<=mu<1 and 0<=nu<1): return None
    a,b=k/(1+m),k/(1-m)
    if a>=1 or b>=1: return None
    S=np.array([a,-b]);P=np.array([b,a])/(a+b);T=np.array([c,-d]);Q=np.array([d,c])/(c+d)
    W=P[:,None]*Q[None,:];Z=de*np.outer(S,T)
    I=float((W*fz(Z)).sum());L=float(-(W*np.log1p(Z)).sum())
    if I+L<=0: return None
    Ga,Gc=G(a,b),G(c,d); mg=Ga+Gc-I/(I+L)
    if min(Ga,Gc)<=0: return None
    return dict(mg=mg,Ga=Ga,Gc=Gc,rho=I/(I+L),mu=mu,nu=nu,a=a,b=b,c=c,d=d)

SEEDS=[(.95,.9),(.5,.5),(.99,.95),(.2,.8),(.9,.2),(.05,.05),(.999,.99)]
rng=np.random.default_rng(20260808)
rows=[]
for _ in range(400000):
    if len(rows)>=4000: break
    style=rng.integers(0,3)
    if style==0:   k=1-10.0**rng.uniform(-14,-0.3)          # k -> 1
    elif style==1: k=rng.uniform(.01,.999)
    else:          k=1-10.0**rng.uniform(-6,-0.05)
    m=10.0**rng.uniform(-13,-0.3)
    if m>=1-k: m=(1-k)*rng.uniform(.01,.9)
    de=1-10.0**rng.uniform(-14,-0.02) if rng.integers(0,2) else rng.uniform(.05,.9999)
    r=evaluate(m,k,de,SEEDS[rng.integers(0,len(SEEDS))])
    if r is None: continue
    rows.append((r['mg'],r['Ga'],r['Gc'],r['nu'],r['mu'],m,k,de,r['a'],r['c'],r['d']))
R=np.array(rows); mg,Ga,Gc,nu,mu = R[:,0],R[:,1],R[:,2],R[:,3],R[:,4]
print(f"fixed points sampled: {len(R)}   (max k={R[:,6].max():.12f}, max nu={nu.max():.6f})")
print(f"  min margin (absolute)        = {mg.min():.6e}   <- infimum is 0, so this just tracks reach")
for nm,den in (("G(a,b)",Ga),("G(c,d)",Gc),("min(Ga,Gc)",np.minimum(Ga,Gc)),("Ga+Gc",Ga+Gc)):
    r=mg/den
    print(f"  min margin / {nm:<11s} = {r.min():.6f}   (at nu={nu[int(np.argmin(r))]:.6f})")
print(f"  any margin <= 0 ?            {(mg<=0).sum()} of {len(R)}")

def obj(x,seed,which):
    m=10**x[0]; k=1-10**x[1]; de=1-10**x[2]
    if not(1e-14<m<.9 and 0<k<1-m and 0<de<1): return 9.
    r=evaluate(m,k,de,seed)
    if r is None: return 9.
    den={'Ga':r['Ga'],'Gc':r['Gc'],'min':min(r['Ga'],r['Gc']),'sum':r['Ga']+r['Gc']}[which]
    return r['mg']/den if den>0 else 9.
print("--- targeted minimisation ---")
for which in ('Ga','min','sum'):
    best=9.;barg=None;bs=None
    for sd in SEEDS:
        for _ in range(6):
            x0=[rng.uniform(-13,-.5),rng.uniform(-13,-.5),rng.uniform(-13,-.05)]
            res=minimize(obj,x0,args=(sd,which),method='Nelder-Mead',
                         options=dict(maxiter=500,xatol=1e-12,fatol=1e-15))
            if res.fun<best: best,barg,bs=res.fun,res.x,sd
    m=10**barg[0]; k=1-10**barg[1]; de=1-10**barg[2]; r=evaluate(m,k,de,bs)
    print(f"  min margin/{which:<4s} = {best:.6f}" + (f"   at m={m:.2e} k={k:.10f} de={de:.10f} nu={r['nu']:.6f}" if r else ""))
