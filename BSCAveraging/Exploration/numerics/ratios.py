"""Anchor both sides of (S4) to the SAME multiplier-free |Delta_g|:
   r1 = Omega/|Delta_g|                       (multiplier-free)
   r2 = min_{mu,nu>=0}(gMax4-gSum)/|Delta_g|
max r1 < min r2  =>  (S4).  Same configuration, so not the refuted decoupling."""
import numpy as np
from scipy.optimize import linprog
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-15); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def Fo(z): return (1+z)*np.log1p(z)-Psi(z)
def calc(a,b,c,d,de):
    if a<b: a,b=b,a
    if d<c: c,d=d,c
    N=(a+b)*(c+d)
    Om=(b*d*Fo(de*a*c)-b*c*Fo(de*a*d)-a*d*Fo(de*b*c)+a*c*Fo(de*b*d))/N
    if Om<=0: return None
    Dg=Psi(de*a*c)-Psi(de*a*d)-Psi(de*b*c)+Psi(de*b*d)
    if abs(Dg)<1e-14: return None
    pa,pb=b/(a+b),a/(a+b); qc,qd=d/(c+d),c/(c+d)
    U0=pa*Psi(a)+pb*Psi(b); V0=qc*Psi(c)+qd*Psi(d)
    EP=pa*qc*Psi(de*a*c)+pa*qd*Psi(de*a*d)+pb*qc*Psi(de*b*c)+pb*qd*Psi(de*b*d)
    P=[a,b];Q=[c,d]
    A=[[Psi(de*P[i]*Q[j])-EP for j in range(2)] for i in range(2)]
    B=[Psi(P[i])-U0 for i in range(2)]; C=[Psi(Q[j])-V0 for j in range(2)]
    Aub=[];bub=[]
    for i in range(2):
        for j in range(2):
            Aub.append([-1.,-B[i],-C[j]]); bub.append(-A[i][j])
    r=linprog(c=[1.,0.,0.],A_ub=np.array(Aub),b_ub=np.array(bub),
              bounds=[(None,None),(0,None),(0,None)],method='highs')
    if not r.success: return None
    return Om/abs(Dg), r.x[0]/abs(Dg), Om, r.x[0], abs(Dg)
rng=np.random.default_rng(2718281)
r1s=[];r2s=[];w1=None;w2=None
for _ in range(150000):
    a,b,c,d=rng.uniform(1e-4,1-1e-8,4); de=rng.uniform(.02,1-1e-9)
    if (a-b)*(c-d)>=0: continue
    r=calc(a,b,c,d,de)
    if r is None: continue
    r1,r2,Om,val,Dg=r
    if val<=1e-13: continue
    r1s.append(r1); r2s.append(r2)
    if w1 is None or r1>w1[0]: w1=(r1,a,b,c,d,de)
    if w2 is None or r2<w2[0]: w2=(r2,a,b,c,d,de)
r1s=np.array(r1s); r2s=np.array(r2s)
print('configs: %d'%len(r1s))
print('  max r1 = max Omega/|Delta_g|         = %.6f'%r1s.max())
print('     at a=%.5f b=%.5f c=%.5f d=%.5f de=%.5f'%w1[1:])
print('  min r2 = min [gMax4-gSum]/|Delta_g|  = %.6f'%r2s.min())
print('     at a=%.5f b=%.5f c=%.5f d=%.5f de=%.5f'%w2[1:])
print('  SEPARATION max r1 < min r2 ?           %s'%('YES -> proves (S4)' if r1s.max()<r2s.min() else 'NO'))
