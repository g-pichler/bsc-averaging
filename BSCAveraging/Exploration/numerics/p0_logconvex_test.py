import mpmath as mp
mp.mp.dps=30
def N_of(G,A,u,v):
    t=u*v; B=lambda z: 1-G(z); C=lambda z: G(z)-G(t)
    return A(v)*B(u)*C(u)-A(u)*B(v)*C(v)
print("(a) single geometric  c_k=(1-th)th^{k-1}:  G(z)=(1-th)z/(1-th z)")
bad=0
for th in ['0.05','0.3','0.6','0.9','0.99']:
    th=mp.mpf(th)
    G=lambda z: (1-th)*z/(1-th*z)
    A=lambda z: z*mp.diff(G,z)
    vals=[]
    for (u,v) in [(0.9,0.3),(0.7,0.2),(0.95,0.6),(0.5,0.1),(0.99,0.02)]:
        u,v=mp.mpf(u),mp.mpf(v); n=N_of(G,A,u,v); vals.append(float(n))
        if n<-1e-25: bad+=1
    print(f"   theta={float(th):5.2f}: N = {['%.3e'%x for x in vals]}")
print(f"   negatives: {bad}   -> geometric laws satisfy it: {bad==0}")
print()
print("(b) log-convex two-atom-ish mixtures of geometrics (should hold), vs non-log-convex (may fail)")
def mixG(ws):    # ws: list of (weight, theta)
    G=lambda z: sum(w*(1-th)*z/(1-th*z) for w,th in ws)
    A=lambda z: z*mp.diff(G,z)
    return G,A
tests={'mix .5/.5 th=0.1,0.9':[(0.5,0.1),(0.5,0.9)],
       'mix .8/.2 th=0.05,0.95':[(0.8,0.05),(0.2,0.95)],
       'mix .3/.7 th=0.4,0.6':[(0.3,0.4),(0.7,0.6)]}
for name,ws in tests.items():
    G,A=mixG([(mp.mpf(w),mp.mpf(t)) for w,t in ws])
    vals=[float(N_of(G,A,mp.mpf(u),mp.mpf(v))) for (u,v) in [(0.9,0.3),(0.7,0.2),(0.5,0.1),(0.99,0.02)]]
    print(f"   {name}: {['%.3e'%x for x in vals]}  all>0: {all(x>0 for x in vals)}")
print()
print("(c) non-log-convex control  c={1:0.1, 2:0.9}  (known violation)")
G=lambda z: mp.mpf('0.1')*z+mp.mpf('0.9')*z**2
A=lambda z: z*mp.diff(G,z)
print("   N at (0.9,0.3):", mp.nstr(N_of(G,A,mp.mpf('0.9'),mp.mpf('0.3')),6))
