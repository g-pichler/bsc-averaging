import numpy as np
rng=np.random.default_rng(11)
def quantities(th,u,v):
    t=u*v; A=1-th; a=1-th*u; b=1-th*v; w=1-th*t
    f=A/a; g=A/w; r=a/b
    S=lambda phi: sum(phi[i]*(r[i]**2-r[(i+1)%3]*r[(i+2)%3]) for i in range(3))
    return f,g,r,S(f),S(f*g),S(np.ones(3))
bad={'S_f>=0':0,'S_fg>=0':0,'S_1>=0':0,'gmax*S_f>=S_fg':0,'(gmax+gmid)*S_f>=S_fg':0,'G*S_f>=S_fg (=KL)':0}
worst={k:0.0 for k in bad}
N=300000
for _ in range(N):
    th=rng.uniform(0,1,3); u=rng.uniform(0,1); v=rng.uniform(0,u)
    f,g,r,Sf,Sfg,S1=quantities(th,u,v)
    gs=np.sort(g)[::-1]; G=g.sum()
    tests={'S_f>=0':(Sf,0.0),'S_fg>=0':(Sfg,0.0),'S_1>=0':(S1,0.0),
           'gmax*S_f>=S_fg':(gs[0]*Sf,Sfg),'(gmax+gmid)*S_f>=S_fg':((gs[0]+gs[1])*Sf,Sfg),
           'G*S_f>=S_fg (=KL)':(G*Sf,Sfg)}
    for k,(lhs,rhs) in tests.items():
        if lhs<rhs-1e-14:
            bad[k]+=1
            if lhs!=0 and rhs>0: worst[k]=max(worst[k],rhs/lhs if lhs>0 else np.inf)
print(f"{N} samples")
for k in bad: print(f"  {k:26s}  violations {bad[k]:7d}   worst rhs/lhs {worst[k]:.4f}")
