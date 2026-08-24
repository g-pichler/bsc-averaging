import numpy as np, itertools, sympy as sp, cvxpy as cp
from collections import defaultdict
A1,A2,A3=sp.symbols('A1 A2 A3'); A=[A1,A2,A3]
def buildQ(uu,vv):
    u=sp.Rational(uu); v=sp.Rational(vv); t=u*v; c=1-u; d=u-v
    a=[Ai*u+c for Ai in A]; b=[Ai*v+c+d for Ai in A]; w=[sp.expand(Ai*t+(1-t)) for Ai in A]
    P=[sp.expand(a[i]*b[i]) for i in range(3)]
    Q=0
    for (i,j,k) in [(0,1,2),(1,2,0),(2,0,1)]:
        S=sp.expand(A[j]*w[k]+A[k]*w[j])
        Q+=sp.expand(A[i]*w[i]*S*(sp.expand(a[i]**2*b[j]*b[k])-sp.expand(b[i]**2*a[j]*a[k]))*P[j]*P[k])
    return sp.Poly(sp.expand(Q),A)
def monos(deg): return [m for m in itertools.product(range(deg+1),repeat=3) if sum(m)<=deg]
def polymul(p,q):
    r=defaultdict(float)
    for m1,c1 in p.items():
        for m2,c2 in q.items(): r[tuple(m1[i]+m2[i] for i in range(3))]+=c1*c2
    return dict(r)
D1={(1,0,0):1.0,(0,1,0):-1.0}      # A1-A2
D2={(0,1,0):1.0,(0,0,1):-1.0}      # A2-A3
def run(uu,vv,h=3,solver=cp.SCS,extra_mult=True):
    Qp=buildQ(uu,vv); tg={m:float(c) for m,c in zip(Qp.monoms(),Qp.coeffs())}
    sc=max(abs(x) for x in tg.values()); tg={k:v/sc for k,v in tg.items()}
    expr=defaultdict(lambda:0); mats=[]
    def block(gpoly,hh):
        """PSD Gram over basis {delta_p * m}, times multiplier gpoly."""
        basis=[]
        for D in (D1,D2):
            for m in monos(hh): basis.append(polymul(D,{m:1.0}))
        n=len(basis); G=cp.Variable((n,n),PSD=True); mats.append(G)
        for i in range(n):
            for j in range(n):
                pr=polymul(polymul(basis[i],basis[j]),gpoly)
                for mm,cc in pr.items(): expr[mm]=expr[mm]+cc*G[i,j]
    block({(0,0,0):1.0},h)
    if extra_mult:
        for k in range(3):
            ek=[0,0,0]; ek[k]=1
            block({tuple(ek):1.0},h-1)                      # A_k
            block({(0,0,0):1.0,tuple(ek):-1.0},h-1)         # 1-A_k
    cons=[expr[k]==tg.get(k,0.0) for k in set(expr)|set(tg)]
    prob=cp.Problem(cp.Minimize(sum(cp.trace(G) for G in mats)),cons)
    try:
        prob.solve(solver=solver,eps=1e-7,max_iters=40000,verbose=False) if solver==cp.SCS else prob.solve(solver=solver)
    except Exception as e: return 'err'
    return prob.status
print("ansatz  Q = [delta-module SOS] + sum_k A_k*[...] + sum_k (1-A_k)*[...]   (WITH cross terms)")
for (uu,vv) in [('9/10','3/10'),('1/2','1/4')]:
    r1=run(uu,vv,3,cp.SCS); r2=run(uu,vv,4,cp.SCS)
    print(f"   u={uu:>7} v={vv:>7}:  h=3 -> {r1:22}  h=4 -> {r2}")
