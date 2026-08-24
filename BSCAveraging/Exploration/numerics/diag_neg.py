import numpy as np
from scipy.optimize import fsolve, minimize
import fixed_point_value as V
at=np.arctanh
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-15); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def G(p,q): return (Psi(p)/p+Psi(q)/q)/(at(p)+at(q))
def fz(z): return (1+z)*np.log1p(z)
SEEDS=[(.95,.9),(.5,.5),(.99,.95),(.2,.8),(.9,.2),(.05,.05),(.999,.99)]
rng=np.random.default_rng(20260808); found=[]
for _ in range(400000):
    if len(found)>=3: break
    st=rng.integers(0,3)
    if st==0:   k=1-10.0**rng.uniform(-14,-0.3)
    elif st==1: k=rng.uniform(.01,.999)
    else:       k=1-10.0**rng.uniform(-6,-0.05)
    m=10.0**rng.uniform(-13,-0.3)
    if m>=1-k: m=(1-k)*rng.uniform(.01,.9)
    de=1-10.0**rng.uniform(-14,-0.02) if rng.integers(0,2) else rng.uniform(.05,.9999)
    sd=SEEDS[rng.integers(0,len(SEEDS))]
    sol,info,ier,msg=fsolve(V.eqs,list(sd),args=(m,k,de),full_output=True)
    if ier!=1: continue
    c,d=sol
    if not(1e-13<c<1-1e-14 and 1e-13<d<1-1e-14): continue
    res=max(abs(np.array(V.eqs(sol,m,k,de))))
    if res>1e-9: continue
    p=V.pieces(m,k,c,d,de); mu,nu=p[12],p[13]
    if not(np.isfinite(mu) and 0<=mu<1 and 0<=nu<1): continue
    a,b=k/(1+m),k/(1-m)
    if a>=1 or b>=1: continue
    S=np.array([a,-b]);P=np.array([b,a])/(a+b);T=np.array([c,-d]);Q=np.array([d,c])/(c+d)
    W=P[:,None]*Q[None,:];Z=de*np.outer(S,T)
    I=float((W*fz(Z)).sum());L=float(-(W*np.log1p(Z)).sum())
    mg=G(a,b)+G(c,d)-I/(I+L)
    if mg<=0: found.append((mg,m,k,de,c,d,a,b,mu,nu,res,I,L,G(a,b),G(c,d)))
print('negative-margin candidates found:',len(found))
for f in found:
    mg,m,k,de,c,d,a,b,mu,nu,res,I,L,Ga,Gc=f
    J=I+L; F=float(V.Phi(m,k,c,d,mu,nu,de))
    print('--- margin=%.6e ---'%mg)
    print('  m=%.4e k=%.12f delta=%.12f  c=%.6e d=%.6e'%(m,k,de,c,d))
    print('  a=%.10f b=%.10f  mu=%.6e nu=%.6e  residual=%.2e'%(a,b,mu,nu,res))
    print('  I=%.6e  L=%.6e  J=%.6e   rho=%.6f Ga=%.6f Gc=%.6f'%(I,L,J,I/J,Ga,Gc))
    print('  F (Phi)       = %+.6e   <-- must be <= 0'%F)
    print('  J*(rho-Ga-Gc) = %+.6e   <-- route-identity cross-check'%(J*(I/J-Ga-Gc)))
    print('  (a-b)(c-d)    = %+.3e   <-- must be <= 0 at a maximiser'%((a-b)*(c-d)))
    def neg(x):
        cc,dd=1/(1+np.exp(-x[0])),1/(1+np.exp(-x[1]))
        if min(cc,dd)<1e-12 or max(cc,dd)>1-1e-12: return 9.
        v=V.Phi(m,k,cc,dd,mu,nu,de); return -v if np.isfinite(v) else 9.
    best=9.
    for _ in range(25):
        r=minimize(neg,rng.uniform(-6,6,2),method='Nelder-Mead',options=dict(maxiter=1200))
        best=min(best,r.fun)
    print('  Phi(sol)=%.6e  Phi(best response)=%.6e  gap=%.3e'%(F,-best,-best-F))
