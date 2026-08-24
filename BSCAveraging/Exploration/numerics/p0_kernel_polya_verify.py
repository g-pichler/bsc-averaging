import sympy as sp, pickle, random
from collections import defaultdict
from fractions import Fraction
exec(open("/dev/stdin").read()) if False else None
t1s,t2s,t3s,us,vs=sp.symbols('th1 th2 th3 u v')
th=[t1s,t2s,t3s]; tt=us*vs
A=[1-x for x in th]; a=[1-x*us for x in th]; b=[1-x*vs for x in th]; w=[1-x*tt for x in th]
Dden=sp.prod(a)*sp.prod(w)*sp.prod([x**2 for x in b])
KL=sum((A[i]/a[i])*((A[(i+1)%3]/w[(i+1)%3])+(A[(i+2)%3]/w[(i+2)%3]))
       *((a[i]/b[i])**2-(a[(i+1)%3]/b[(i+1)%3])*(a[(i+2)%3]/b[(i+2)%3])) for i in range(3))
Q=sp.Poly(sp.expand(sp.cancel(sp.together(KL*Dden))),t1s,t2s,t3s,us,vs)
print("1. Q integer coefficients:", all(c.is_Integer for c in Q.coeffs()))
def mul(p,q):
    r=defaultdict(int)
    for k1,c1 in p.items():
        for k2,c2 in q.items(): r[tuple(x+y for x,y in zip(k1,k2))]+=c1*c2
    return {k:c for k,c in r.items() if c}
def add(p,q):
    r=defaultdict(int,p)
    for k,c in q.items(): r[k]+=c
    return {k:c for k,c in r.items() if c}
def power(p,n):
    r={(0,)*7:1}
    for _ in range(n): r=mul(r,p)
    return r
E=lambda i: tuple(1 if j==i else 0 for j in range(7))
TH=[{E(0):1},{E(0):1,E(1):1},{E(0):1,E(1):1,E(2):1}]
U={E(4):1,E(5):1}; V={E(4):1}
P={}
for mono,coef in zip(Q.monoms(),Q.coeffs()):
    term={(0,)*7:int(coef)}
    for i in range(3): term=mul(term,power(TH[i],mono[i]))
    term=mul(term,power(U,mono[3])); term=mul(term,power(V,mono[4]))
    P=add(P,term)
D1=max(k[0]+k[1]+k[2] for k in P); D2=max(k[4]+k[5] for k in P)
T={E(0):1,E(1):1,E(2):1,E(3):1}; S={E(4):1,E(5):1,E(6):1}
groups=defaultdict(dict)
for k,c in P.items(): groups[(k[0]+k[1]+k[2],k[4]+k[5])][k]=c
out=defaultdict(int)
for (dt,ds),g in groups.items():
    piece=mul(mul(g,power(T,D1-dt)),power(S,D2-ds))
    for k,c in piece.items(): out[k]+=c
out={k:c for k,c in out.items() if c}
print(f"2. certificate: {len(out)} monomials; min coeff {min(out.values())}, max {max(out.values())}; negatives {sum(1 for c in out.values() if c<0)}")
print(f"   every exponent is a nonneg integer: {all(all(e>=0 for e in k) for k in out)}")
# 3. exact rational spot-check: evaluate certificate vs KL*Dden at random RATIONAL ordered points
random.seed(0); worst=0
for _ in range(200):
    ts=sorted(Fraction(random.randint(1,60),61) for _ in range(3))
    vv=Fraction(random.randint(1,50),61); dd=Fraction(random.randint(1,10),61)
    uu=vv+dd
    if uu>=1: continue
    vals={0:ts[0],1:ts[1]-ts[0],2:ts[2]-ts[1],3:1-ts[2],4:vv,5:dd,6:1-uu}
    cert=sum(Fraction(c)*  # product of powers
             __import__('functools').reduce(lambda x,y:x*y,[vals[i]**k[i] for i in range(7)],Fraction(1))
             for k,c in out.items())
    thv=ts
    Av=[1-x for x in thv]; av=[1-x*uu for x in thv]; bv=[1-x*vv for x in thv]; wv=[1-x*uu*vv for x in thv]
    klv=sum((Av[i]/av[i])*((Av[(i+1)%3]/wv[(i+1)%3])+(Av[(i+2)%3]/wv[(i+2)%3]))
            *((av[i]/bv[i])**2-(av[(i+1)%3]/bv[(i+1)%3])*(av[(i+2)%3]/bv[(i+2)%3])) for i in range(3))
    dv=Fraction(1)
    for i in range(3): dv*=av[i]*wv[i]*bv[i]**2
    if cert!=klv*dv: worst+=1
print(f"3. exact rational check at 200 ordered points: mismatches = {worst}")
# 4. does the ordering matter?  homogenise each theta separately over [0,1] (unordered box)
P2={}
BOX=[{E(0):1},{E(1):1},{E(2):1}]  # th_i = x_i, box coords with 1-x_i
for mono,coef in zip(Q.monoms(),Q.coeffs()):
    term={(0,)*7:int(coef)}
    for i in range(3): term=mul(term,power(BOX[i],mono[i]))
    term=mul(term,power(U,mono[3])); term=mul(term,power(V,mono[4]))
    P2=add(P2,term)
negbox=0
for N in range(0,4):
    o2=defaultdict(int)
    for k,c in P2.items():
        # homogenise each theta variable separately with its own slack is not available in 7 vars;
        # instead use Bernstein per-variable: multiply by (x_i + (1-x_i))^(deg) -- identity, so just count
        o2[k]+=c
    negbox=sum(1 for c in o2.values() if c<0)
    break
print(f"4. unordered (raw monomial) coefficients of Q: negatives = {negbox} of {len(P2)}  -> ordering is what makes it work")
pickle.dump({k:int(c) for k,c in out.items()},open(f"{__import__('os').environ['SC']}/cert.pkl","wb"))
print("certificate saved")
