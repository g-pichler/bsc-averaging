"""Does the FOUR-CORNER bound alone give (S)?   max g >= max over the 4 corners,
and gSum is their weighted average, so  min_{mu,nu>=0} max_ij [g_ij - gSum]  is an LP."""
import numpy as np
from scipy.optimize import linprog
def Psi(y):
    y=np.clip(np.abs(y),0.,1-1e-15); return .5*((1+y)*np.log1p(y)+(1-y)*np.log1p(-y))
def Fo(z): return (1+z)*np.log1p(z)-Psi(z)
def four(a,b,c,d,de):
    N=(a+b)*(c+d)
    Om=(b*d*Fo(de*a*c)-b*c*Fo(de*a*d)-a*d*Fo(de*b*c)+a*c*Fo(de*b*d))/N
    if Om<=0: return None
    pa,pb=b/(a+b),a/(a+b); qc,qd=d/(c+d),c/(c+d)
    U0=pa*Psi(a)+pb*Psi(b); V0=qc*Psi(c)+qd*Psi(d)
    EP=pa*qc*Psi(de*a*c)+pa*qd*Psi(de*a*d)+pb*qc*Psi(de*b*c)+pb*qd*Psi(de*b*d)
    P=[a,b]; Q=[c,d]
    A=[[Psi(de*P[i]*Q[j])-EP for j in range(2)] for i in range(2)]
    B=[Psi(P[i])-U0 for i in range(2)]; C=[Psi(Q[j])-V0 for j in range(2)]
    Aub=[];bub=[]
    for i in range(2):
        for j in range(2):
            Aub.append([-1., -B[i], -C[j]]); bub.append(-A[i][j])
    r=linprog(c=[1.,0.,0.],A_ub=np.array(Aub),b_ub=np.array(bub),
              bounds=[(None,None),(0,None),(0,None)],method='highs')
    if not r.success: return None
    return Om, r.x[0], r.x[1], r.x[2]
print('=== (S-prime) counterexample ===')
r=four(0.983388,0.773061,0.775054,0.993080,0.999594)
if r:
    Om,val,mu,nu=r
    print('  Omega=%.6e  min max4-gSum=%.6e  ratio=%.6f  at mu=%.4f nu=%.4f'%(Om,val,Om/val if val>0 else np.inf,mu,nu))
rng=np.random.default_rng(31415); worst=-9;wr=None;n=0;nonpos=0
for _ in range(200000):
    a,b,c,d=rng.uniform(1e-4,1-1e-8,4); de=rng.uniform(.02,1-1e-9)
    if (a-b)*(c-d)>=0: continue
    r=four(a,b,c,d,de)
    if r is None: continue
    Om,val,mu,nu=r
    if val<=0: nonpos+=1; continue
    n+=1
    q=Om/val
    if q>worst: worst,wr=q,(a,b,c,d,de,Om,val,mu,nu)
print('four-corner LP, opposite skews: %d configs  (val<=0: %d)'%(n,nonpos))
print('  max Omega / min_{mu,nu}(max4-gSum) = %.6f   (<=1 => (S) from 4 corners ALONE)'%worst)
if wr: print('   at a=%.5f b=%.5f c=%.5f d=%.5f de=%.5f\n   Om=%.4e val=%.4e mu=%.4f nu=%.4f'%wr)
