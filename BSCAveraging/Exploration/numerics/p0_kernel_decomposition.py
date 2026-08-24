import mpmath as mp, random
mp.mp.dps=30
def parts(u,v,th):
    t=u*v
    f=lambda x:(1-x)/(1-x*u); g=lambda x:(1-x)/(1-x*t); r=lambda x:(1-x*u)/(1-x*v)
    F=[f(x) for x in th]; G=[g(x) for x in th]; R=[r(x) for x in th]
    lam=[F[i]*(sum(G)-G[i]) for i in range(3)]
    tot=sum(lam[i]*(R[i]**2-R[(i+1)%3]*R[(i+2)%3]) for i in range(3))
    pairs=[(0,1,2),(0,2,1),(1,2,0)]
    part1=sum((lam[i]-lam[l])*(R[i]**2-R[l]**2) for i,l,m in pairs)/2
    part2=sum(lam[m]*(R[i]-R[l])**2 for i,l,m in pairs)/2
    pw=[ (R[i]-R[l])*((lam[i]-lam[l])*(R[i]+R[l])+lam[m]*(R[i]-R[l])) for i,l,m in pairs]
    return tot,part1,part2,pw
random.seed(3); n=0; neg_tot=0; neg_p1=0; neg_pw=0
for _ in range(4000):
    u=mp.mpf(random.uniform(0.05,0.999)); v=mp.mpf(random.uniform(0.01,float(u)))
    th=[mp.mpf(random.uniform(0.001,0.999)) for _ in range(3)]
    tot,p1,p2,pw=parts(u,v,th); n+=1
    if tot<-1e-28: neg_tot+=1
    if p1<-1e-28: neg_p1+=1
    if any(x<-1e-28 for x in pw): neg_pw+=1
print(f"{n} random cases:")
print(f"   total < 0 : {neg_tot}        (the claim)")
print(f"   part1 < 0 : {neg_p1}        (Chebyshev part — often negative, as expected)")
print(f"   some pairwise term < 0 : {neg_pw}   (pairwise decomposition insufficient)")
print()
print("worst case theta_m -> 1 (third weight vanishes):  f_i g_l (r_i^2 - r_l r_m) + f_l g_i (r_l^2 - r_i r_m) >= 0 ?")
bad=0; tot_c=0; mn=mp.inf
for _ in range(3000):
    u=mp.mpf(random.uniform(0.05,0.999)); v=mp.mpf(random.uniform(0.01,float(u)))
    th=[mp.mpf(random.uniform(0.001,0.999)),mp.mpf(random.uniform(0.001,0.999)),mp.mpf(1)]
    tot,_,_,_=parts(u,v,th); tot_c+=1
    if tot<mn: mn=tot
    if tot<-1e-28: bad+=1
print(f"   {tot_c} cases: violations {bad};  min value {mp.nstr(mn,6)}")
