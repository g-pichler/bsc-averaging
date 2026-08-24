import mpmath as mp
mp.mp.dps=30
def N_of(c,u,v):     # c: dict k->weight ; N = A(v)B(u)C(u) - A(u)B(v)C(v), t=uv
    t=u*v
    G=lambda z: sum(w*z**k for k,w in c.items())
    A=lambda z: sum(w*k*z**k for k,w in c.items())
    B=lambda z: 1-G(z); C=lambda z: G(z)-G(t)
    return A(v)*B(u)*C(u)-A(u)*B(v)*C(v)
print("two-atom laws  c = {i:p, j:1-p}:  is N >= 0 for u>=v ?")
bad=[]
for (i,j) in [(1,2),(1,5),(1,8),(2,3),(2,7),(3,9)]:
    for p in [0.1,0.3,0.5,0.7,0.9]:
        for (u,v) in [(0.9,0.3),(0.7,0.2),(0.95,0.6),(0.5,0.1)]:
            u,v=mp.mpf(u),mp.mpf(v)
            val=N_of({i:mp.mpf(p),j:1-mp.mpf(p)},u,v)
            if val<-1e-25: bad.append((i,j,p,float(u),float(v),float(val)))
print(f"   violations among two-atom laws: {len(bad)}")
if bad:
    for b in bad[:6]: print("     ",b)
print()
print("the actual law c_k = 2/(4k^2-1), truncated:")
c={k:mp.mpf(2)/(4*k*k-1) for k in range(1,4000)}
tot=sum(c.values()); print(f"   mass captured: {mp.nstr(tot,8)}")
worst=mp.inf
for (u,v) in [(0.9,0.3),(0.7,0.2),(0.95,0.6),(0.5,0.1),(0.99,0.02),(0.6,0.55)]:
    u,v=mp.mpf(u),mp.mpf(v); val=N_of(c,u,v)
    worst=min(worst,val)
    print(f"   u={float(u):4.2f} v={float(v):4.2f}: N = {mp.nstr(val,6)}   {'OK' if val>0 else 'NEG'}")
