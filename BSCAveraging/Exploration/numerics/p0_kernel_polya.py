import sympy as sp, itertools, sys
from collections import defaultdict
from math import comb
t1s,t2s,t3s,us,vs=sp.symbols('th1 th2 th3 u v')
th=[t1s,t2s,t3s]; tt=us*vs
A=[1-x for x in th]; a=[1-x*us for x in th]; b=[1-x*vs for x in th]; w=[1-x*tt for x in th]
Dden=sp.prod(a)*sp.prod(w)*sp.prod([x**2 for x in b])
KL=sum((A[i]/a[i])*((A[(i+1)%3]/w[(i+1)%3])+(A[(i+2)%3]/w[(i+2)%3]))
       *((a[i]/b[i])**2-(a[(i+1)%3]/b[(i+1)%3])*(a[(i+2)%3]/b[(i+2)%3])) for i in range(3))
Q=sp.Poly(sp.expand(sp.cancel(sp.together(KL*Dden))),t1s,t2s,t3s,us,vs)
# --- substitute ordered coords, keep exponents as dict over (t1,t2,t3,t4,v,d,c) ---
def mul(p,q):
    r=defaultdict(int)
    for k1,c1 in p.items():
        for k2,c2 in q.items():
            r[tuple(x+y for x,y in zip(k1,k2))]+=c1*c2
    return {k:c for k,c in r.items() if c}
def add(p,q):
    r=defaultdict(int,p)
    for k,c in q.items(): r[k]+=c
    return {k:c for k,c in r.items() if c}
def power(p,n):
    r={(0,)*7:1}
    for _ in range(n): r=mul(r,p)
    return r
E=lambda i: tuple(1 if j==i else 0 for j in range(7))   # t1,t2,t3,t4,v,d,c
TH1={E(0):1}; TH2={E(0):1,E(1):1}; TH3={E(0):1,E(1):1,E(2):1}
U={E(4):1,E(5):1}; V={E(4):1}
TH=[TH1,TH2,TH3]
P={}
for mono,coef in zip(Q.monoms(),Q.coeffs()):
    term={(0,)*7:int(coef)}
    for i in range(3): term=mul(term,power(TH[i],mono[i]))
    term=mul(term,power(U,mono[3])); term=mul(term,power(V,mono[4]))
    P=add(P,term)
print("after substitution:", len(P), "monomials")
D1=max(k[0]+k[1]+k[2] for k in P); D2=max(k[4]+k[5] for k in P)
print("theta-block degree D1 =",D1,"  uv-block degree D2 =",D2)
T={E(0):1,E(1):1,E(2):1,E(3):1}; S={E(4):1,E(5):1,E(6):1}
Tpow={0:{(0,)*7:1}}; Spow={0:{(0,)*7:1}}
for N1,N2 in [(0,0),(1,1),(2,2),(3,3),(4,4),(6,6)]:
    d1,d2=D1+N1,D2+N2
    groups=defaultdict(dict)
    for k,c in P.items(): groups[(k[0]+k[1]+k[2],k[4]+k[5])][k]=c
    out=defaultdict(int)
    for (dt,ds),g in groups.items():
        n1,n2=d1-dt,d2-ds
        if n1 not in Tpow: Tpow[n1]=power(T,n1)
        if n2 not in Spow: Spow[n2]=power(S,n2)
        piece=mul(mul(g,Tpow[n1]),Spow[n2])
        for k,c in piece.items(): out[k]+=c
    neg=[(k,c) for k,c in out.items() if c<0]
    print(f"  elevation ({N1},{N2}) -> bidegree ({d1},{d2}): {len(out)} monomials, {len(neg)} negative", flush=True)
    if not neg:
        print("  *** ALL COEFFICIENTS NONNEGATIVE — POLYA CERTIFICATE FOR THE KERNEL LEMMA ***")
        break
    print("     most negative:", min(c for _,c in neg), " example exps(t1,t2,t3,t4,v,d,c):", min(neg,key=lambda x:x[1])[0])
