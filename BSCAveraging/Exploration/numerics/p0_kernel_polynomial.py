import os
_HERE = os.path.dirname(os.path.abspath(__file__))
import sympy as sp
A1,A2,A3,c,d,v = sp.symbols('A1 A2 A3 c d v', nonnegative=True)
u = d+v; t = u*v
A=[A1,A2,A3]
a=[Ai*u+c for Ai in A]          # 1-theta_i u
b=[Ai*v+c+d for Ai in A]        # 1-theta_i v
w=[Ai*t+(1-t) for Ai in A]      # 1-theta_i t   (1-t expanded below)
one_minus_t = sp.expand(1-t)
w=[sp.expand(Ai*t+one_minus_t) for Ai in A]
P=[sp.expand(a[i]*b[i]) for i in range(3)]
def D1(i,j,k): return sp.expand(b[i]**2*a[j]*a[k])
def D2(i,j,k): return sp.expand(a[i]**2*b[j]*b[k])
idx=[(0,1,2),(1,2,0),(2,0,1)]
Q=0
for (i,j,k) in idx:
    S_jk = sp.expand(A[j]*w[k] + A[k]*w[j])      # (1-th_j)w_k + (1-th_k)w_j
    Q += sp.expand(A[i]*w[i]*S_jk*(D2(i,j,k)-D1(i,j,k))*P[j]*P[k])
Q=sp.expand(Q)
print("Q built.  total degree:", sp.Poly(Q,[A1,A2,A3,c,d,v]).total_degree())
print("number of monomials:", len(Q.as_ordered_terms()))
# sanity: Q vanishes when A1=A2=A3
print("Q at A1=A2=A3:", sp.simplify(Q.subs({A2:A1,A3:A1})))
# numeric sanity vs the direct kernel
import random, mpmath as mp
def Kdirect(th,u_,v_):
    import itertools
    t_=u_*v_
    Ath=lambda th,z: z*(1-th)/(1-th*z)**2
    Bth=lambda th,z: (1-z)/(1-th*z)
    Cth=lambda th,z: (1-th)*(z-t_)/((1-th*z)*(1-th*t_))
    K=lambda t1,t2,t3: Ath(t1,v_)*Bth(t2,u_)*Cth(t3,u_)-Ath(t1,u_)*Bth(t2,v_)*Cth(t3,v_)
    return sum(K(*p) for p in itertools.permutations(th))/6
random.seed(0)
for _ in range(3):
    th=[random.uniform(0.05,0.95) for _ in range(3)]
    uu=random.uniform(0.3,0.95); vv=random.uniform(0.05,uu)
    sub={A1:1-th[0],A2:1-th[1],A3:1-th[2],c:1-uu,d:uu-vv,v:vv}
    qval=float(Q.subs(sub))
    ksym=Kdirect(th,uu,vv)
    # K_sym = uv(1-u)(1-v) Q / (6 * Pi^2 * w1w2w3)
    Pi=1; W=1
    for i in range(3):
        Pi*= (1-th[i]*uu)*(1-th[i]*vv); W*= (1-th[i]*uu*vv)
    pred=uu*vv*(1-uu)*(1-vv)*qval/(6*Pi**2*W)
    print(f"   check: K_sym={ksym:.6e}   from Q={pred:.6e}   ratio={pred/ksym if ksym else 0:.6f}")
import pickle
pickle.dump(sp.srepr(Q), open(os.path.join(_HERE, 'Q.pkl'), 'wb'))
