import mpmath as mp
mp.mp.dps=30
G=lambda z: 1-(1-z)*mp.atanh(mp.sqrt(z))/mp.sqrt(z)
def xi(z,t):
    m=G(t); return z*mp.diff(G,z)/((G(z)-m)*(1-G(z)))
def Xi(z,t): return z*mp.diff(lambda y: mp.log(xi(y,t)), z)
print("single-crossing of  s(u) = Xi(u) + Xi(t/u)  on (sqrt t, 1):  '-' then '+', once")
allok=True
for t in ['0.01','0.05','0.2','0.5','0.8','0.95']:
    t=mp.mpf(t); rt=mp.sqrt(t)
    us=[rt+(1-rt)*mp.mpf(k)/60 for k in range(1,60)]
    sg=[]
    for u in us:
        v=t/u
        if v<=t or u>=1: continue
        sg.append(1 if Xi(u,t)+Xi(v,t)>0 else -1)
    changes=sum(1 for i in range(len(sg)-1) if sg[i]!=sg[i+1])
    pat=''.join('+' if x>0 else '-' for x in sg)
    ok = changes==1 and pat[0]=='-' and pat[-1]=='+'
    allok &= ok
    print(f"   t={float(t):5.2f}: sign changes = {changes}   pattern {pat[:20]}...{pat[-6:]}   OK: {ok}")
print(f"\n   single crossing in every case: {allok}")
