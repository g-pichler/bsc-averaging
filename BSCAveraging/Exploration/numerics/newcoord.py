from collections import defaultdict
import itertools
NV=5   # z1,z2,z3,a,b
def C(c): return {(0,)*NV: c} if c else {}
def var(i):
    m=[0]*NV; m[i]=1; return {tuple(m):1}
def add(*ps):
    r=defaultdict(int)
    for p in ps:
        for k,v in p.items(): r[k]+=v
    return {k:v for k,v in r.items() if v}
def mul(p,q):
    r=defaultdict(int)
    for a,x in p.items():
        for b,y in q.items(): r[tuple(i+j for i,j in zip(a,b))]+=x*y
    return {k:v for k,v in r.items() if v}
def sub(p,q): return add(p,{k:-v for k,v in q.items()})
z1,z2,z3,a,b=[var(i) for i in range(5)]
# ordered y's and A <= B
y=[z1, add(z1,z2), add(z1,z2,z3)]
A=a; B=add(a,b); Cc=sub(add(A,B),mul(A,B))          # C = A+B-AB
F=[add(C(1),mul(t,A)) for t in y]
G=[add(C(1),mul(t,Cc)) for t in y]
H=[add(C(1),mul(t,B)) for t in y]
tot={}
for i in range(3):
    j,k=(i+1)%3,(i+2)%3
    inner=sub(mul(mul(F[i],F[i]),mul(H[j],H[k])), mul(mul(F[j],F[k]),mul(H[i],H[i])))
    tot=add(tot, mul(mul(mul(F[j],F[k]),mul(G[i],add(G[j],G[k]))), mul(mul(H[j],H[k]),inner)))
neg={k:v for k,v in tot.items() if v<0}
print("monomials:", len(tot), "  negative coefficients:", len(neg))
print("total degree: min %d max %d" % (min(sum(m) for m in tot), max(sum(m) for m in tot)))
print("coeff range: %d .. %d" % (min(tot.values()), max(tot.values())))
if neg:
    print("most negative:", min(neg.values()), " example exponent (z1,z2,z3,a,b):", min(neg,key=neg.get))

# group by z-exponent; each group is a polynomial in (a,b)
groups=defaultdict(dict)
for m,cf in tot.items():
    groups[m[:3]][m[3:]] = cf
print("\nz-monomial groups:", len(groups))
# which groups go negative somewhere on the simplex a,b>=0, a+b<=1 ?
import itertools
N=40; badgroups=[]
for zk,poly in groups.items():
    worst=1e9
    for i in range(N+1):
        for j in range(N+1-i):
            A=i/N; B=j/N
            val=sum(cf*(A**e[0])*(B**e[1]) for e,cf in poly.items())
            if val<worst: worst=val
    if worst < -1e-12: badgroups.append((zk,worst))
print("groups negative somewhere on the simplex:", len(badgroups))
if badgroups:
    badgroups.sort(key=lambda t:t[1])
    print("worst three:", [(z,round(w,4)) for z,w in badgroups[:3]])
