import numpy as np, itertools, sympy as sp, cvxpy as cp
from collections import defaultdict
A1,A2,A3=sp.symbols('A1 A2 A3'); A=[A1,A2,A3]
def monos(deg): return [m for m in itertools.product(range(deg+1),repeat=3) if sum(m)<=deg]
def solve_for(target_poly,half=3,box=True,solver=cp.SCS):
    Qp=sp.Poly(sp.expand(target_poly),A); tg={m:float(c) for m,c in zip(Qp.monoms(),Qp.coeffs())}
    sc=max(abs(x) for x in tg.values()); tg={k:v/sc for k,v in tg.items()}
    B=monos(half); Bl=monos(half-1)
    expr=defaultdict(lambda:0); mats=[]
    def add(basis,G,extra,sign=1):
        for i,m1 in enumerate(basis):
            for j,m2 in enumerate(basis):
                for em,ec in extra.items():
                    key=tuple(m1[k]+m2[k]+em[k] for k in range(3))
                    expr[key]=expr[key]+sign*ec*G[i,j]
    for (i,j) in [(0,1),(0,2),(1,2)]:
        base=defaultdict(float)
        for (di,dj,co) in [(2,0,1.0),(1,1,-2.0),(0,2,1.0)]:
            e=[0,0,0]; e[i]+=di+1; e[j]+=dj+1; base[tuple(e)]+=co
        G=cp.Variable((len(B),len(B)),PSD=True); mats.append(G); add(B,G,dict(base))
        if box:
            for k in range(3):
                e1={tuple(a1[m]+(1 if m==k else 0) for m in range(3)):c1 for a1,c1 in base.items()}
                G1=cp.Variable((len(Bl),len(Bl)),PSD=True); mats.append(G1); add(Bl,G1,e1)
                G2=cp.Variable((len(Bl),len(Bl)),PSD=True); mats.append(G2)
                add(Bl,G2,dict(base)); add(Bl,G2,e1,sign=-1)
    cons=[expr[k]==tg.get(k,0.0) for k in set(expr)|set(tg)]
    prob=cp.Problem(cp.Minimize(sum(cp.trace(G) for G in mats)),cons)
    try: prob.solve(solver=solver,eps=1e-9,max_iters=100000,verbose=False) if solver==cp.SCS else prob.solve(solver=solver)
    except Exception as e: return 'err:'+str(e)[:30]
    return prob.status
# self-test 1: exactly the ansatz with M=1
T1=sum(A[i]*A[j]*(A[i]-A[j])**2 for (i,j) in [(0,1),(0,2),(1,2)])
print("  self-test 1  (M_ij = 1):                    ", solve_for(T1))
# self-test 2: M_ij = (1 + A_k^2), still in the cone
T2=sum(A[i]*A[j]*(A[i]-A[j])**2*(1+A[3-i-j]**2) for (i,j) in [(0,1),(0,2),(1,2)])
print("  self-test 2  (M_ij = 1 + A_k^2):            ", solve_for(T2))
# self-test 3: degree-10 element of the cone
T3=sum(A[i]*A[j]*(A[i]-A[j])**2*(1+A[0]**2+A[1]**2+A[2]**2)**3 for (i,j) in [(0,1),(0,2),(1,2)])
print("  self-test 3  (M_ij = (1+|A|^2)^3, degree 10):", solve_for(T3))
