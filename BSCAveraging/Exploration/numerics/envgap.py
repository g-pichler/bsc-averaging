"""Sharpest form of (S):   Omega  <=  min_{mu,nu>=0} [ max_{p,q} g - gSum ].
Inner max over (p,q) on a fine grid; outer min over (mu,nu) is CONVEX."""
import numpy as np
from scipy.optimize import minimize
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-15); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def Fo(z): return (1+z)*np.log1p(z)-Psi(z)
G=np.concatenate([np.linspace(0,0.97,140), 1-np.logspace(-1.5,-8,110)])
PG,QG=np.meshgrid(G,G,indexing='ij')
PsiP=Psi(PG); PsiQ=Psi(QG)

def sharp(a,b,c,d,de):
    N=(a+b)*(c+d)
    Om=(b*d*Fo(de*a*c)-b*c*Fo(de*a*d)-a*d*Fo(de*b*c)+a*c*Fo(de*b*d))/N
    if Om<=0: return None
    pa,pb=b/(a+b),a/(a+b); qc,qd=d/(c+d),c/(c+d)
    U0=pa*Psi(a)+pb*Psi(b); V0=qc*Psi(c)+qd*Psi(d)
    EP=pa*qc*Psi(de*a*c)+pa*qd*Psi(de*a*d)+pb*qc*Psi(de*b*c)+pb*qd*Psi(de*b*d)
    base=Psi(de*PG*QG)
    def h(x):
        mu,nu=np.exp(x[0]),np.exp(x[1])
        m=(base-mu*PsiP-nu*PsiQ).max()
        return m+mu*U0+nu*V0-EP
    best=np.inf; bx=None
    for x0 in ([-1.,-1.],[0.,0.],[-3.,-3.],[-6.,-6.]):
        r=minimize(h,x0,method='Nelder-Mead',options=dict(maxiter=180,xatol=1e-9,fatol=1e-13))
        if r.fun<best: best,bx=r.fun,r.x
    return Om,best,np.exp(bx[0]),np.exp(bx[1]),U0,V0

print("=== the (S') counterexample ===")
r=sharp(0.983388,0.773061,0.775054,0.993080,0.999594)
Om,mn,mu,nu,U0,V0=r
print("  Omega                              = %.6e"%Om)
print("  min_{mu,nu}[max g - gSum]          = %.6e   at mu=%.4f nu=%.4f"%(mn,mu,nu))
print("  (S) holds here?                      %s   ratio Omega/min = %.6f"%('YES' if Om<=mn else 'NO', Om/mn))
print()
print("=== sweep over opposite-skew configurations ===")
rng=np.random.default_rng(20260810)
worst=-9; wr=None; n=0
for _ in range(120):
    a,b,c,d=rng.uniform(1e-3,1-1e-6,4); de=rng.uniform(.05,1-1e-9)
    if (a-b)*(c-d)>=0: continue
    r=sharp(a,b,c,d,de)
    if r is None: continue
    Om,mn,mu,nu,U0,V0=r
    if mn<=0: continue
    n+=1
    q=Om/mn
    if q>worst: worst,wr=q,(a,b,c,d,de,Om,mn,mu,nu)
print("  configurations tested: %d"%n)
print("  max Omega / min_{mu,nu}[max g - gSum] = %.6f    (<= 1 = (S) holds)"%worst)
if wr: print("   at a=%.5f b=%.5f c=%.5f d=%.5f de=%.5f\n   Omega=%.4e min=%.4e mu=%.4f nu=%.4f"%wr)
