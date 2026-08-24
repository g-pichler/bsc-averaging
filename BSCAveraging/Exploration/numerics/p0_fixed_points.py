import numpy as np
from scipy.optimize import brentq, fsolve
np.seterr(all='ignore')
L2=np.log(2)
def Psi(s):
    s=abs(s); return 0.5*((1+s)*np.log1p(s)+((1-s)*np.log1p(-s) if s<1 else 0.0))
def at(x): return np.arctanh(min(max(x,-1+1e-15),1-1e-15))
def rate(x,y): return (y*Psi(x)+x*Psi(y))/(x+y)
# S=(a,-b), T=(c,-d).  residual of the bitangency equation on the S side
def resid_S(a,b,c,d):
    rp,rm=d/(c+d),c/(c+d); kT=c*d/(c+d)
    A1,A2,A3,A4=1+a*c,1-a*d,1-b*c,1+b*d
    if min(A1,A2,A3,A4)<=0: return np.nan
    Lam=np.log(A1)+np.log(A4)-np.log(A2)-np.log(A3)
    l2=kT*Lam/(at(a)+at(b))
    phi_a =rp*A1*np.log(A1)+rm*A2*np.log(A2)
    phi_mb=rp*A3*np.log(A3)+rm*A4*np.log(A4)
    dphi_a=kT*(np.log(A1)-np.log(A2))
    return phi_a-phi_mb-l2*(Psi(a)-Psi(b))-(a+b)*(dphi_a-l2*at(a))
def resid_T(a,b,c,d): return resid_S(c,d,a,b)
def bfor(x,C):
    f=lambda y: rate(x,y)-C
    if f(1e-12)*f(1.0)>0: return None
    return brentq(f,1e-12,1.0,xtol=1e-14)
def system(v,Cu,Cv):
    a,c=np.clip(v,1e-9,1-1e-9)
    b,d=bfor(a,Cu),bfor(c,Cv)
    if b is None or d is None: return [1e3,1e3]
    return [resid_S(a,b,c,d),resid_T(a,b,c,d)]
for (Cub,Cvb) in [(0.4,0.4),(0.4,0.6),(0.2,0.7)]:
    Cu,Cv=Cub*L2,Cvb*L2
    sols=[]
    for a0 in np.linspace(0.05,0.95,19):
        for c0 in np.linspace(0.05,0.95,19):
            s,info,ier,msg=fsolve(system,[a0,c0],args=(Cu,Cv),full_output=True,xtol=1e-13)
            if ier!=1: continue
            a,c=s; 
            if not(1e-6<a<1-1e-6 and 1e-6<c<1-1e-6): continue
            if max(abs(np.array(system(s,Cu,Cv))))>1e-9: continue
            b,d=bfor(a,Cu),bfor(c,Cv)
            if not any(abs(a-x[0])<1e-5 and abs(c-x[2])<1e-5 for x in sols):
                sols.append((a,b,c,d))
    print(f"\n(Cu,Cv)=({Cub},{Cvb}) bits: interior fixed points found: {len(sols)}")
    for a,b,c,d in sorted(sols):
        sym = "SYMMETRIC (a=b,c=d)" if abs(a-b)<1e-6 and abs(c-d)<1e-6 else "asymmetric"
        print(f"   a={a:.6f} b={b:.6f} | c={c:.6f} d={d:.6f}   {sym}")
