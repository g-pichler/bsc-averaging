import random
def K(F,G,R):
    return (F[0]*(G[1]+G[2])*(R[0]**2-R[1]*R[2])
          + F[1]*(G[0]+G[2])*(R[1]**2-R[0]*R[2])
          + F[2]*(G[0]+G[1])*(R[2]**2-R[0]*R[1]))
rng=random.Random(7)
def dec(rng):           # decreasing positive triple, normalised first = 1
    a=rng.uniform(0,1); b=rng.uniform(0,a); return [1.0,a,b]
tests={ "monotone only":lambda F,G,R: True,
        "+ g/f decreasing":lambda F,G,R: G[0]/F[0]>=G[1]/F[1]>=G[2]/F[2],
        "+ fg decreasing":lambda F,G,R: F[0]*G[0]>=F[1]*G[1]>=F[2]*G[2],
        "+ both":lambda F,G,R: G[0]/F[0]>=G[1]/F[1]>=G[2]/F[2] and F[0]*G[0]>=F[1]*G[1]>=F[2]*G[2]}
for name,cond in tests.items():
    bad=0; n=0; worst=(1e9,None)
    for _ in range(400000):
        F,G,R=dec(rng),dec(rng),dec(rng)
        if not cond(F,G,R): continue
        n+=1; k=K(F,G,R)
        if k<worst[0]: worst=(k,(F,G,R))
        if k<-1e-12: bad+=1
    print("%-20s samples=%-7d violations=%-7d min=%.4f" % (name,n,bad,worst[0]))
    if bad: print("      witness F,G,R =", [[round(x,3) for x in t] for t in worst[1]])
