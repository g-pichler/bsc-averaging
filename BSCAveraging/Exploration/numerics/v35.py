"""Venue 3 (m-expansion) + venue 5 (linearity in nu) diagnostics."""
import numpy as np
from scipy.optimize import fsolve
import fixed_point_value as V
at=np.arctanh
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-15); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def A(y): return -.5*np.log(1-y*y)
def G(p,q): return (Psi(p)/p+Psi(q)/q)/(at(p)+at(q))
def fz(z): return (1+z)*np.log1p(z)

rows=[]
rng=np.random.default_rng(1001)
for _ in range(200000):
    if len(rows)>=600: break
    m=10**rng.uniform(-7,-0.4); k=rng.uniform(.05,1-m-.05); de=rng.uniform(.15,.995)
    sol,info,ier,msg=fsolve(V.eqs,[rng.uniform(.15,.95),rng.uniform(.15,.95)],args=(m,k,de),full_output=True)
    if ier!=1: continue
    c,d=sol
    if not(1e-6<c<1-1e-9 and 1e-6<d<1-1e-9): continue
    if max(abs(np.array(V.eqs(sol,m,k,de))))>1e-11: continue
    p=V.pieces(m,k,c,d,de); mu,nu=p[12],p[13]
    if not(np.isfinite(mu) and 0<=mu<1 and 0<=nu<1): continue
    a,b=k/(1+m),k/(1-m)
    if a>=1 or b>=1: continue
    b1,b2=m+k*de*c, m-k*de*d
    S=np.array([a,-b]);P=np.array([b,a])/(a+b);T=np.array([c,-d]);Q=np.array([d,c])/(c+d)
    W=P[:,None]*Q[None,:];Z=de*np.outer(S,T)
    I=float((W*fz(Z)).sum()); Lau=float(-(W*np.log1p(Z)).sum())
    rho=I/(I+Lau); marg=G(a,b)+G(c,d)-rho
    IUX=.5*(Psi(m+k)+Psi(m-k))-Psi(m)
    gain=nu*A(c)-A(b1)+A(m)+m*(at(b1)-at(m))
    nustar=(mu*IUX+A(b1)-A(m)-m*(at(b1)-at(m)))/A(c)
    rows.append((m,k,de,c,d,mu,nu,nustar,marg,abs(c-d),rho))
R=np.array(rows)
m_,k_,de_,c_,d_,mu_,nu_,ns_,marg_,cd_,rho_=R.T
print(f"non-degenerate fixed points: {len(R)}")
print("--- venue 3: behaviour as m -> 0 ---")
for lo,hi in [(1e-7,1e-5),(1e-5,1e-3),(1e-3,1e-2),(1e-2,1e-1),(1e-1,1.)]:
    s=(m_>=lo)&(m_<hi)
    if s.sum()<3: continue
    print(f"  m in [{lo:.0e},{hi:.0e}): n={s.sum():4d}  min margin={marg_[s].min():.4f}  "
          f"max|c-d|={cd_[s].max():.4f}  median |c-d|/m={np.median(cd_[s]/m_[s]):.3e}  max mu={mu_[s].max():.4f}")
print(f"  OVERALL min ratio-form margin = {marg_.min():.6f}")
print(f"  corr(|c-d|, m): |c-d|/m  min={np.min(cd_/m_):.3e} max={np.max(cd_/m_):.3e}  (bounded => c-d = O(m))")
print("--- venue 5: nu vs threshold nu* ---")
print(f"  (M) holds (nu <= nu*) for {(nu_<=ns_).sum()}/{len(R)}")
print(f"  min [nu* - nu]            = {(ns_-nu_).min():.6e}")
print(f"  min [nu*/nu]              = {(ns_/nu_).min():.6f}")
print(f"  max nu                    = {nu_.max():.6f}   max nu* = {ns_.max():.6f}")
i=int(np.argmin(ns_-nu_))
print("  tightest: m=%.2e k=%.4f de=%.4f c=%.4f d=%.4f mu=%.4f nu=%.4f nu*=%.4f marg=%.4f"%(
    m_[i],k_[i],de_[i],c_[i],d_[i],mu_[i],nu_[i],ns_[i],marg_[i]))
