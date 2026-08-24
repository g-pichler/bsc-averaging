import sympy as sp, numpy as np
r1,r2,r3,k=sp.symbols('r1 r2 r3 kappa', positive=True)
r=[r1,r2,r3]; v=1-k; s=[(1-x)/k for x in r]
c=[r[i]**2-r[(i+1)%3]*r[(i+2)%3] for i in range(3)]
C=sum(c); D=0
for i in range(3):
    j,kk=(i+1)%3,(i+2)%3
    D+= -(s[i]/r[i])*(r[j]+r[kk])*c[i] + (r[j]+r[kk])*(2*r[i]*s[i]-s[j]*r[kk]-r[j]*s[kk])
D+= -v*sum(r[j]*s[j]*(C-c[j]) for j in range(3))
P=sp.expand(sp.simplify(sp.together(D)*k*r1*r2*r3)); Pk=sp.Poly(P,k)
X=Pk.coeff_monomial(k); Y=Pk.coeff_monomial(1)
fX=sp.lambdify((r1,r2,r3),X); fY=sp.lambdify((r1,r2,r3),Y)
rng=np.random.default_rng(1); N=400000
badY=0; wY=0.0; badP=0
for _ in range(N):
    rr=rng.uniform(0,1,3); kk=rng.uniform(0,1)
    y=fY(*rr); x=fX(*rr)
    if y<-1e-14: badY+=1; wY=min(wY,y)
    if kk*x+y<-1e-14: badP+=1
print(f"{N} samples on r in (0,1)^3, kappa in (0,1)")
print(f"  Y >= 0        : violations {badY}   most negative {wY:.3e}")
print(f"  kappa*X + Y>=0: violations {badP}")
# is Y >= 0 also outside the cube (would tell whether the box constraints are needed)?
bad2=0; w2=0.0
for _ in range(100000):
    rr=rng.uniform(0,3,3); y=fY(*rr)
    if y<-1e-12: bad2+=1; w2=min(w2,y)
print(f"  Y >= 0 on (0,3)^3 : violations {bad2}   most negative {w2:.3e}")
sp.pprint(sp.factor(Y))
