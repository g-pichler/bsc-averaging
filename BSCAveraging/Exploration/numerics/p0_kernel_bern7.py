from collections import defaultdict
NV=7   # z1,z2,z3,s,sp,w,wp
def C0(c): return {(0,)*NV:c} if c else {}
def var(i):
    m=[0]*NV; m[i]=1; return {tuple(m):1}
def add(*ps):
    r=defaultdict(int)
    for p in ps:
        for k,v in p.items(): r[k]+=v
    return {k:v for k,v in r.items() if v}
def mul(*ps):
    r=ps[0]
    for q in ps[1:]:
        t=defaultdict(int)
        for a,x in r.items():
            for b,y in q.items(): t[tuple(i+j for i,j in zip(a,b))]+=x*y
        r={k:v for k,v in t.items() if v}
    return r
def sub(p,q): return add(p,{k:-v for k,v in q.items()})
z1,z2,z3,s,sp,w,wp=[var(i) for i in range(7)]
S1=add(s,sp); W1=add(w,wp)                      # the two "ones"
y=[z1, add(z1,z2), add(z1,z2,z3)]
A=mul(s,wp); B=s                                 # A = s(1-w), B = s
Ch=sub(add(mul(S1,A), mul(S1,W1,B)), mul(A,B))   # C homogenised to bidegree (2,1)
F=[add(mul(S1,W1), mul(t,A)) for t in y]         # (1,1)
H=[add(S1, mul(t,B)) for t in y]                 # (1,0)
G=[add(mul(S1,S1,W1), mul(t,Ch)) for t in y]     # (2,1)
tot={}
for i in range(3):
    j,k=(i+1)%3,(i+2)%3
    inner=sub(mul(F[i],F[i],H[j],H[k]), mul(F[j],F[k],H[i],H[i]))
    tot=add(tot, mul(F[j],F[k],G[i],add(G[j],G[k]),H[j],H[k],inner))
neg=[(m,c) for m,c in tot.items() if c<0]
print("monomials:", len(tot), "  negative:", len(neg))
if neg:
    neg.sort(key=lambda t:t[1]); print("most negative:", neg[0])
else:
    print("coeff range: %d .. %d" % (min(tot.values()), max(tot.values())))
