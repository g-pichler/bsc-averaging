import numpy as np, mpmath as mp
mp.mp.dps=40
# --- 1. verify the corner leading coefficient ---
def KL(th,u,v):
    t=u*v; A=1-th; a=1-th*u; b=1-th*v; w=1-th*t; f=A/a; g=A/w; r=a/b
    return sum(f[i]*(g[(i+1)%3]+g[(i+2)%3])*(r[i]**2-r[(i+1)%3]*r[(i+2)%3]) for i in range(3))
p,q,kap,sig,v=mp.mpf('1.4'),mp.mpf('0.6'),mp.mpf('0.8'),mp.mpf('0.35'),mp.mpf('0.5')
print("corner expansion  KL/eps  vs predicted L:")
for e in ['1e-2','1e-3','1e-4','1e-5','1e-6']:
    e=mp.mpf(e); th=np.array([1-e*p,sig,1-e*q],dtype=object); u=1-kap*e
    val=KL(th,u,v)/e
    g2=(1-sig)/(1-sig*u*v); r2=(1-sig*u)/(1-sig*v)
    L=g2*r2/(1-v)*kap*(p-q)**2/((p+kap)*(q+kap))
    print(f"   eps={float(e):8.0e}   KL/eps = {mp.nstr(val,10)}   L = {mp.nstr(L,10)}   ratio {mp.nstr(val/L,8)}")
# --- 2. is the N-part absorbed by the D-part? ---
rng=np.random.default_rng(7); N=300000
bad_pair=0; bad_sum=0; worst_pair=0.0; worst_sum=0.0
for _ in range(N):
    th=rng.uniform(0,1,3); u=rng.uniform(0,1); vv=rng.uniform(0,u); t=u*vv
    A=1-th; a=1-th*u; b=1-th*vv; w=1-th*t; r=a/b; c=1-u; d=u-vv
    lam=np.array([A[i]/a[i]*sum(A[j]/w[j] for j in range(3) if j!=i) for i in range(3)])
    SD=SCN=0.0
    for (i,l,m) in [(0,1,2),(0,2,1),(1,2,0)]:
        C=(A[i]-A[l])**2*d*(r[i]+r[l])/(a[i]*a[l]*b[i]*b[l])
        Nn=A[i]*A[l]*u*(1-vv)/(w[i]*w[l])
        D=lam[m]*(A[i]-A[l])**2*d**2/(b[i]**2*b[l]**2)
        SD+=D; SCN+=C*Nn
        if D<C*Nn-1e-15:
            bad_pair+=1; worst_pair=max(worst_pair,(C*Nn)/D if D>0 else np.inf)
    if SD<SCN-1e-15:
        bad_sum+=1; worst_sum=max(worst_sum,SCN/SD if SD>0 else np.inf)
print(f"\n{N} samples")
print(f"  pairwise   D_il >= C_il*N_il : violations {bad_pair:7d}   worst CN/D {worst_pair:.4f}")
print(f"  summed     sum D >= sum C*N  : violations {bad_sum:7d}   worst CN/D {worst_sum:.4f}")
