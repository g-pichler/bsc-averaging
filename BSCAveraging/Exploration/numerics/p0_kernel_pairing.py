import numpy as np
rng=np.random.default_rng(5)
nb=nneg={0:0,1:0,2:0,3:0}
nb={'T pairwise':0,'T>=0 count':{0:0,1:0,2:0,3:0}}
worst=0.0; N=200000
for _ in range(N):
    th=rng.uniform(0,1,3); u=rng.uniform(0,1); v=rng.uniform(0,u); t=u*v
    A=1-th; a=1-th*u; b=1-th*v; w=1-th*t
    f=A/a; g=A/w; r=a/b
    c=np.array([r[i]**2-r[(i+1)%3]*r[(i+2)%3] for i in range(3)])
    T=[g[l]*f[i]*c[i]+g[i]*f[l]*c[l] for (i,l) in [(0,1),(0,2),(1,2)]]
    k=sum(1 for x in T if x<0); nb['T>=0 count'][k]+=1
    if k: nb['T pairwise']+=1
    tot=sum(T)
    if tot<0: worst=min(worst,tot)
print(f"{N} samples: direct pairing T_il = g_l f_i c_i + g_i f_l c_l")
print(f"  samples with >=1 negative T : {nb['T pairwise']}   distribution of #negative: {nb['T>=0 count']}")
print(f"  most negative total (should be 0) : {worst}")
