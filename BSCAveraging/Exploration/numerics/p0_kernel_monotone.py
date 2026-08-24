import numpy as np
def KL(th,u,v):
    t=u*v; A=1-th; a=1-th*u; b=1-th*v; w=1-th*t; f=A/a; g=A/w; r=a/b
    return sum(f[i]*(g[(i+1)%3]+g[(i+2)%3])*(r[i]**2-r[(i+1)%3]*r[(i+2)%3]) for i in range(3))
rng=np.random.default_rng(21); N=200000; h=1e-6
badv=badu=0; wv=wu=0.0
for _ in range(N):
    th=rng.uniform(0,1,3); u=rng.uniform(0.05,0.95); v=rng.uniform(0.02,u-0.02) if u>0.05 else 0.01
    dv=(KL(th,u,v+h)-KL(th,u,v-h))/(2*h)
    du=(KL(th,u+h,v)-KL(th,u-h,v))/(2*h)
    if dv> 1e-9: badv+=1; wv=max(wv,dv)
    if du< -1e-9: badu+=1; wu=max(wu,-du)
print(f"{N} samples")
print(f"  dKL/dv <= 0 : violations {badv:7d}  worst +{wv:.3e}")
print(f"  dKL/du >= 0 : violations {badu:7d}  worst -{wu:.3e}")
# also: monotone in the spread of theta? scale spread about the mean
badS=0; wS=0.0
for _ in range(N//2):
    th=rng.uniform(0,1,3); u=rng.uniform(0.05,0.95); v=rng.uniform(0.02,max(u-0.02,0.03))
    m=th.mean()
    f=lambda s: KL(np.clip(m+s*(th-m),1e-9,1-1e-9),u,v)
    ds=(f(1+h)-f(1-h))/(2*h)
    if ds<-1e-9: badS+=1; wS=max(wS,-ds)
print(f"  KL increasing in theta-spread : violations {badS:7d}  worst -{wS:.3e}")
