import random, mpmath as mp
mp.mp.dps=25
# Q as a function, evaluated OUTSIDE the box A_i<=1  (i.e. theta_i<0)
def Qval(A,c,d,v):
    u=d+v; t=u*v
    a=[Ai*u+c for Ai in A]; b=[Ai*v+c+d for Ai in A]; w=[Ai*t+(1-t) for Ai in A]
    P=[a[i]*b[i] for i in range(3)]
    tot=0
    for (i,j,k) in [(0,1,2),(1,2,0),(2,0,1)]:
        S=A[j]*w[k]+A[k]*w[j]
        tot+=A[i]*w[i]*S*(a[i]**2*b[j]*b[k]-b[i]**2*a[j]*a[k])*P[j]*P[k]
    return tot
print("Q on the true domain (A_i in [0,1], c+d+v=1):")
random.seed(0); mn=mp.inf
for _ in range(3000):
    A=[mp.mpf(random.uniform(0,1)) for _ in range(3)]
    x=[random.random() for _ in range(3)]; s=sum(x); c,d,v=[mp.mpf(y/s) for y in x]
    mn=min(mn,Qval(A,c,d,v))
print(f"   min over 3000 samples: {mp.nstr(mn,6)}   (nonneg: {mn>=-1e-20})")
print()
print("Q with A_i > 1 allowed (theta_i < 0 — outside the box, but inside the monomial cone's domain):")
mn2=mp.inf; arg=None
for _ in range(20000):
    A=[mp.mpf(random.uniform(0,6)) for _ in range(3)]
    x=[random.random() for _ in range(3)]; s=sum(x); c,d,v=[mp.mpf(y/s) for y in x]
    q=Qval(A,c,d,v)
    if q<mn2: mn2,arg=q,(list(map(float,A)),float(c),float(d),float(v))
print(f"   min: {mp.nstr(mn2,6)}   at A={[round(z,3) for z in arg[0]]}, (c,d,v)=({arg[1]:.3f},{arg[2]:.3f},{arg[3]:.3f})")
print(f"   => Q is NEGATIVE for A_i>1: {mn2<0}")
print()
print("consequence: any certificate Q = sum (A_i-A_j)^2 M_ij with M_ij nonneg-COEFFICIENT")
print("would force Q >= 0 on the whole orthant A>=0, which is false. So the LP had to be")
print("infeasible: the certificate must use the upper bounds A_i <= 1 (Handelman/Bernstein).")
