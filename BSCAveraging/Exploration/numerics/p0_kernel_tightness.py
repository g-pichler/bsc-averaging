import numpy as np
from scipy.optimize import minimize
def ratio(z):
    th=np.clip(z[:3],1e-9,1-1e-9); u=np.clip(z[3],1e-9,1-1e-9); v=np.clip(z[4],1e-9,u)
    t=u*v; c=1-u; d=u-v
    A=1-th; a=1-th*u; b=1-th*v; w=1-th*t; r=a/b
    lam=np.array([A[i]/a[i]*sum(A[j]/w[j] for j in range(3) if j!=i) for i in range(3)])
    pos=neg=0.0
    for (i,l,m) in [(0,1,2),(0,2,1),(1,2,0)]:
        C=(A[i]-A[l])**2*d*(r[i]+r[l])/(a[i]*a[l]*b[i]*b[l])
        N=A[i]*A[l]*u*(1-v)/(w[i]*w[l]); P=A[m]*c/w[m]
        D=lam[m]*(A[i]-A[l])**2*d**2/(b[i]**2*b[l]**2)
        E=C*(P-N)+D
        if E>0: pos+=E
        else: neg+=-E
    return -(neg/pos) if pos>0 else 0.0
best=0; arg=None; rng=np.random.default_rng(0)
for _ in range(600):
    z0=np.concatenate([rng.uniform(0,1,3),[rng.uniform(0.1,1),rng.uniform(0,1)]])
    r=minimize(ratio,z0,bounds=[(1e-9,1-1e-9)]*3+[(1e-9,1-1e-9),(1e-9,1-1e-9)],method='L-BFGS-B')
    if -r.fun>best: best,arg=-r.fun,r.x
th=np.clip(arg[:3],0,1); u=arg[3]; v=min(arg[4],u)
print(f"worst  (negative)/(positive)  = {best:.6f}")
print(f"   at theta = {np.round(th,6)},  u = {u:.6f}, v = {v:.6f}")
print(f"   theta spread = {th.max()-th.min():.3e},  u-v = {u-v:.3e},  min theta = {th.min():.3e}")
print()
print("behaviour along the suspected degenerate directions:")
for eps in [1e-1,1e-2,1e-3,1e-4]:
    z=np.array([0.5,0.5+eps,0.5+2*eps,0.8,0.3]); print(f"   theta coalescing (eps={eps:.0e}): ratio {-ratio(z):.6f}")
for eps in [1e-1,1e-2,1e-3,1e-4]:
    z=np.array([0.3,0.6,0.9,0.5+eps,0.5]); print(f"   u->v      (u-v={eps:.0e}): ratio {-ratio(z):.6f}")
