from collections import defaultdict
from math import comb
STATS={'prod':0,'sortelems':0,'sortcmp':0}
import math
NV=5
def C0(c): return {(0,)*NV:c} if c else {}
def var(i):
    m=[0]*NV; m[i]=1; return {tuple(m):1}
def add(*ps):
    r=defaultdict(int); n=0
    for p in ps:
        n+=len(p)
        for k,v in p.items(): r[k]+=v
    STATS['sortelems']+=n; STATS['sortcmp']+=n*max(1,math.ceil(math.log2(max(n,2))))
    return {k:v for k,v in r.items() if v}
def mul(p,q):
    r=defaultdict(int); STATS['prod']+=len(p)*len(q)
    for a,x in p.items():
        for b,y in q.items(): r[tuple(i+j for i,j in zip(a,b))]+=x*y
    n=len(p)*len(q); STATS['sortelems']+=n; STATS['sortcmp']+=n*max(1,math.ceil(math.log2(max(n,2))))
    return {k:v for k,v in r.items() if v}
def sub(p,q): return add(p,{k:-v for k,v in q.items()})
z1,z2,z3,a,b=[var(i) for i in range(5)]
y=[z1,add(z1,z2),add(z1,z2,z3)]
A=a; B=add(a,b); Cc=sub(add(A,B),mul(A,B))
F=[add(C0(1),mul(t,A)) for t in y]; G=[add(C0(1),mul(t,Cc)) for t in y]; H=[add(C0(1),mul(t,B)) for t in y]
tot={}
for i in range(3):
    j,k=(i+1)%3,(i+2)%3
    inner=sub(mul(mul(F[i],F[i]),mul(H[j],H[k])), mul(mul(F[j],F[k]),mul(H[i],H[i])))
    tot=add(tot, mul(mul(mul(F[j],F[k]),mul(G[i],add(G[j],G[k]))), mul(mul(H[j],H[k]),inner)))
groups=defaultdict(dict)
for m,cf in tot.items(): groups[m[:3]][m[3:]]=cf
def to_sw(poly):
    out=defaultdict(int)
    for (i,j),c in poly.items():
        for t in range(i+1): out[(i+j,j+t)] += c*comb(i,t)*(-1)**t
    return {k:v for k,v in out.items() if v}
allint=True; allpos=True; nb=0; mx=0
for zk,poly in groups.items():
    ia=min(e[0] for e in poly); ib=min(e[1] for e in poly)
    q={(e[0]-ia,e[1]-ib):c for e,c in poly.items()}
    sw=to_sw(q); m0=min(p for p,_ in sw); sw={(p-m0,qq):c for (p,qq),c in sw.items()}
    ds=max(p for p,_ in sw); dw=max(q2 for _,q2 in sw)
    for I in range(ds+1):
        for J in range(dw+1):
            bIJ=sum(c*comb(ds-p,I-p)*comb(dw-q2,J-q2) for (p,q2),c in sw.items() if p<=I and q2<=J)
            nb+=1; mx=max(mx,abs(bIJ))
            if bIJ!=int(bIJ): allint=False
            if bIJ<0: allpos=False
print("expansion: %d monomials, %.3e products, %.3e sort comparisons" % (len(tot),STATS['prod'],STATS['sortcmp']))
print("certificate: %d scaled Bernstein coefficients, all integers: %s, all >= 0: %s, max |b| = %d"
      % (nb, allint, allpos, mx))
