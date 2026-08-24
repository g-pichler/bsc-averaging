import os
_HERE = os.path.dirname(os.path.abspath(__file__))
from collections import defaultdict
from math import comb
import random
_src=open(os.path.join(_HERE, 'newcoord.py')).read().split("neg={k:v")[0]
exec(_src)
# 1. does the cleared 5-var polynomial equal the cleared original kernel?
def kern(th,u,v):
    t=u*v
    f=lambda x:(1-x)/(1-x*u); g=lambda x:(1-x)/(1-x*t); r=lambda x:(1-x*u)/(1-x*v)
    return sum(f(th[i])*(g(th[(i+1)%3])+g(th[(i+2)%3]))*(r(th[i])**2-r(th[(i+1)%3])*r(th[(i+2)%3])) for i in range(3))
def evalpoly(p, vals): return sum(c*prod for (m,c) in p.items() for prod in [eval_m(m,vals)])
def eval_m(m,vals):
    r=1.0
    for e,x in zip(m,vals): r*= x**e
    return r
rng=random.Random(3); worst=0
for _ in range(2000):
    z=[rng.uniform(0,3) for _ in range(3)]
    aa=rng.uniform(1e-3,1); bb=rng.uniform(0,1-aa)
    y=[z[0],z[0]+z[1],z[0]+z[1]+z[2]]
    th=[t/(1+t) for t in y]; u=1-aa; v=1-aa-bb
    if not (0<v<=u<1): continue
    A,B,Cc=aa,aa+bb,aa+(aa+bb)-aa*(aa+bb)
    D=1.0
    for t in y: D*= (1+t*A)*(1+t*Cc)*(1+t*B)**2
    lhs=evalpoly(tot,[z[0],z[1],z[2],aa,bb]); rhs=kern(th,u,v)*D
    worst=max(worst, abs(lhs-rhs)/max(1,abs(rhs)))
print("cleared identity max rel error over 2000 points: %.2e" % worst)

# 2. reconstruct the kernel from the certificate and compare
groups=defaultdict(dict)
for m,cf in tot.items(): groups[m[:3]][m[3:]]=cf
def to_sw(poly):
    out=defaultdict(int)
    for (i,j),c in poly.items():
        for t in range(i+1): out[(i+j, j+t)] += c*comb(i,t)*(-1)**t
    return {k:v for k,v in out.items() if v}
cert={}
for zk,poly in groups.items():
    ia=min(e[0] for e in poly); ib=min(e[1] for e in poly)
    q={(e[0]-ia,e[1]-ib):c for e,c in poly.items()}
    sw=to_sw(q); m0=min(p for p,_ in sw); sw={(p-m0,qq):c for (p,qq),c in sw.items()}
    ds=max(p for p,_ in sw); dw=max(q2 for _,q2 in sw)
    beta={}
    for I in range(ds+1):
        for J in range(dw+1):
            beta[(I,J)]=sum(c*comb(I,p)*comb(J,q2)/(comb(ds,p)*comb(dw,q2))
                            for (p,q2),c in sw.items() if p<=I and q2<=J)
    cert[zk]=(ia,ib,m0,ds,dw,beta)
print("all Bernstein coefficients >= 0:", all(b>=-1e-12 for _,_,_,_,_,B in cert.values() for b in B.values()))
worst=0
for _ in range(2000):
    z=[rng.uniform(0,3) for _ in range(3)]
    aa=rng.uniform(1e-3,1); bb=rng.uniform(0,1-aa)
    s=aa+bb; w=(bb/s if s>0 else 0)
    val=0
    for zk,(ia,ib,m0,ds,dw,beta) in cert.items():
        bern=sum(b*comb(ds,I)*(s**I)*((1-s)**(ds-I))*comb(dw,J)*(w**J)*((1-w)**(dw-J))
                 for (I,J),b in beta.items())
        val += (z[0]**zk[0])*(z[1]**zk[1])*(z[2]**zk[2]) * (aa**ia)*(bb**ib) * (s**m0) * bern
    direct=evalpoly(tot,[z[0],z[1],z[2],aa,bb])
    worst=max(worst, abs(val-direct)/max(1,abs(direct)))
print("certificate reconstructs the polynomial, max rel error: %.2e" % worst)
