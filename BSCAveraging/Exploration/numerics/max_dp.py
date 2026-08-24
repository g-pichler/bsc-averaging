"""Is  rho(U;V) <= max(rho(U;X), rho(Y;V))  at fixed points?
If yes the conjecture follows: the other term is >= 0, so sum >= max >= rho."""
import numpy as np
from scipy.optimize import fsolve, minimize
import fixed_point_value as V
at = np.arctanh
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-16); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def fz(z): return (1+z)*np.log1p(z)
def G(p,q): return (Psi(p)/p+Psi(q)/q)/(at(p)+at(q))

def solve_at(m,k,de,seed=(.9,.9)):
    sol,info,ier,msg=fsolve(V.eqs,list(seed),args=(m,k,de),full_output=True)
    if ier!=1: return None
    c,d=sol
    if not (1e-9<c<1-1e-13 and 1e-9<d<1-1e-13): return None
    if max(abs(np.array(V.eqs(sol,m,k,de))))>1e-10: return None
    a,b=k/(1+m),k/(1-m)
    if a>=1 or b>=1: return None
    p=V.pieces(m,k,c,d,de); mu,nu=p[12],p[13]
    if not (np.isfinite(mu) and np.isfinite(nu) and 0<=mu<1 and 0<=nu<1): return None
    S=np.array([a,-b]);P=np.array([b,a])/(a+b);T=np.array([c,-d]);Q=np.array([d,c])/(c+d)
    W=P[:,None]*Q[None,:];Z=de*np.outer(S,T)
    I=float((W*fz(Z)).sum());L=float(-(W*np.log1p(Z)).sum())
    return dict(a=a,b=b,c=c,d=d,mu=mu,nu=nu,rho=I/(I+L),Gu=G(a,b),Gv=G(c,d))

# --- (1) random sweep ---
rng=np.random.default_rng(4242); worst=-9; wrow=None; n=0
for _ in range(300000):
    m=10**rng.uniform(-7,-0.2); k=rng.uniform(.005,1-m-.005); de=rng.uniform(.05,.9999)
    r=solve_at(m,k,de,(rng.uniform(.05,.99),rng.uniform(.05,.99)))
    if r is None: continue
    n+=1
    g=r['rho']-max(r['Gu'],r['Gv'])
    if g>worst: worst,wrow=g,(m,k,de,r)
    if n>=3000: break
print(f"random sweep: {n} fixed points")
print(f"  max [rho(U;V) - max(rho_UX,rho_YV)] = {worst:+.6e}   (<= 0 = claim)")
if wrow: print("    at m=%.3e k=%.6f de=%.6f  Gu=%.5f Gv=%.5f rho=%.5f mu=%.4f nu=%.4f"
               %(wrow[0],wrow[1],wrow[2],wrow[3]['Gu'],wrow[3]['Gv'],wrow[3]['rho'],wrow[3]['mu'],wrow[3]['nu']))

# --- (2) targeted maximization of the violation ---
def obj(x):
    m=10**x[0]; k=1/(1+np.exp(-x[1])); de=1/(1+np.exp(-x[2]))
    if not (1e-9<m<.8 and 0<k<1-m and 0<de<1): return 5.
    r=solve_at(m,k,de)
    if r is None: return 5.
    return -(r['rho']-max(r['Gu'],r['Gv']))
best=5.; barg=None
for _ in range(14):
    x0=[rng.uniform(-7,-.2),rng.uniform(-1,6),rng.uniform(0,6)]
    res=minimize(obj,x0,method='Nelder-Mead',options=dict(maxiter=400,xatol=1e-10,fatol=1e-13))
    if res.fun<best: best,barg=res.fun,res.x
m=10**barg[0]; k=1/(1+np.exp(-barg[1])); de=1/(1+np.exp(-barg[2])); r=solve_at(m,k,de)
print(f"targeted max [rho - max(rho_UX,rho_YV)] = {-best:+.6e}")
if r: print("    at m=%.3e k=%.6f de=%.6f  Gu=%.5f Gv=%.5f rho=%.5f mu=%.4f nu=%.4f"
            %(m,k,de,r['Gu'],r['Gv'],r['rho'],r['mu'],r['nu']))
