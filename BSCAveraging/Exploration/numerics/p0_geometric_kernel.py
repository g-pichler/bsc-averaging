import itertools, mpmath as mp
mp.mp.dps=30
def Ath(th,z): return z*(1-th)/(1-th*z)**2
def Bth(th,z): return (1-z)/(1-th*z)
def Cth(th,z,t): return (1-th)*(z-t)/((1-th*z)*(1-th*t))
def K(t1,t2,t3,u,v):
    t=u*v
    return Ath(t1,v)*Bth(t2,u)*Cth(t3,u,t) - Ath(t1,u)*Bth(t2,v)*Cth(t3,v,t)
def Ksym(t1,t2,t3,u,v):
    return sum(K(*p,u,v) for p in itertools.permutations((t1,t2,t3)))/6
print("is K_sym(th1,th2,th3) >= 0  for u >= v ?   (=0 when th1=th2=th3)")
mn=mp.inf; bad=0; tested=0
ths=[0.02,0.15,0.35,0.55,0.75,0.9,0.98]
for (u,v) in [(0.9,0.3),(0.7,0.2),(0.95,0.6),(0.5,0.1),(0.99,0.02),(0.6,0.55),(0.8,0.79)]:
    u,v=mp.mpf(u),mp.mpf(v)
    for t1 in ths:
        for t2 in ths:
            for t3 in ths:
                s=Ksym(mp.mpf(t1),mp.mpf(t2),mp.mpf(t3),u,v); tested+=1
                if s<mn: mn=s; arg=(t1,t2,t3,float(u),float(v))
                if s<-1e-25: bad+=1
print(f"   tested {tested};  negatives: {bad};  min = {mp.nstr(mn,6)}  at {arg}")
print()
print("sanity: K_sym(th,th,th) = 0 ?")
for th in [0.1,0.5,0.9]:
    print(f"   th={th}: {mp.nstr(Ksym(mp.mpf(th),mp.mpf(th),mp.mpf(th),mp.mpf('0.9'),mp.mpf('0.3')),6)}")
