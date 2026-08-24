import mpmath as mp, itertools, random
mp.mp.dps=30
def test(u,v,ths):
    t=u*v
    g=lambda th:(1-th)/(1-th*t)
    r=lambda th:(1-th*u)/(1-th*v)
    S=sum(g(th) for th in ths)
    W=lambda th:(1-th)*(1-th*v)*(S-g(th))/(1-th*u)**2
    ws=[W(th) for th in ths]; rs=[r(th) for th in ths]
    rho=rs[0]*rs[1]*rs[2]
    # similarly ordered?  W_i larger exactly when r_i larger
    order_ok=all((ws[i]-ws[j])*(rs[i]-rs[j])>=-1e-30 for i in range(3) for j in range(3))
    lhs=sum(ws[i]*(rs[i]**3-rho) for i in range(3))
    cheb=(sum(ws)/3)*(sum(x**3 for x in rs)-3*rho)
    return order_ok, lhs, cheb
print("Chebyshev route:  are W_i and r_i similarly ordered?  and does Sum W_i(r_i^3-rho) >= 0 ?")
random.seed(1); bad_order=0; bad_pos=0; n=0
for _ in range(4000):
    u=mp.mpf(random.uniform(0.05,0.999)); v=mp.mpf(random.uniform(0.01,float(u)))
    ths=[mp.mpf(random.uniform(0.001,0.999)) for _ in range(3)]
    ok,lhs,cheb=test(u,v,ths); n+=1
    if not ok: bad_order+=1
    if lhs<-1e-28: bad_pos+=1
print(f"   {n} random cases:  ordering violations {bad_order};  positivity violations {bad_pos}")
print()
print("systematic grid check of the ordering (W decreasing in theta for fixed S):")
bad=0; tot=0
for u in [0.99,0.9,0.7,0.4,0.15]:
  for v in [0.9,0.6,0.3,0.05]:
    if v>=u: continue
    u_,v_=mp.mpf(u),mp.mpf(v); t=u_*v_
    g=lambda th:(1-th)/(1-th*t)
    for Sv in [0.2,0.5,1.0,1.6,2.2,2.9]:
        Sv=mp.mpf(Sv)
        W=lambda th:(1-th)*(1-th*v_)*(Sv-g(th))/(1-th*u_)**2
        prev=None
        for k in range(1,200):
            th=mp.mpf(k)/200
            if Sv-g(th)<0: continue
            val=W(th); tot+=1
            if prev is not None and val>prev+1e-25: bad+=1
            prev=val
print(f"   monotone-decreasing violations: {bad} of {tot} steps")
