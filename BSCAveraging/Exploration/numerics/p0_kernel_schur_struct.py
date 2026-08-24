import mpmath as mp, random
mp.mp.dps=30
def parts(u,v,th):
    t=u*v; c=1-u; d=u-v
    A=[1-x for x in th]
    a=[1-x*u for x in th]; b=[1-x*v for x in th]; w=[1-x*t for x in th]
    r=[a[i]/b[i] for i in range(3)]
    f=[A[i]/a[i] for i in range(3)]; g=[A[i]/w[i] for i in range(3)]
    lam=[f[i]*(sum(g)-g[i]) for i in range(3)]
    P=[A[i]*c/w[i] for i in range(3)]
    out=[]
    for (i,l,m) in [(0,1,2),(0,2,1),(1,2,0)]:
        C=(A[i]-A[l])**2*d*(r[i]+r[l])/(a[i]*a[l]*b[i]*b[l])
        N=A[i]*A[l]*u*(1-v)/(w[i]*w[l])
        D=lam[m]*(A[i]-A[l])**2*d**2/(b[i]**2*b[l]**2)
        out.append((C*(P[m]-N)+D, C*P[m], C*N, D))
    tot=sum(o[0] for o in out)/2
    return tot,out
random.seed(7)
neg_count={0:0,1:0,2:0,3:0}; worst_ratio=0; bad=0; n=0
for _ in range(20000):
    u=mp.mpf(random.uniform(0.02,0.999)); v=mp.mpf(random.uniform(0.01,float(u)))
    th=[mp.mpf(random.uniform(0.001,0.999)) for _ in range(3)]
    tot,out=parts(u,v,th); n+=1
    if tot<-1e-25: bad+=1
    k=sum(1 for o in out if o[0]<0); neg_count[k]+=1
    negs=-sum(o[0] for o in out if o[0]<0); poss=sum(o[0] for o in out if o[0]>0)
    if poss>0 and negs>0: worst_ratio=max(worst_ratio,float(negs/poss))
print(f"{n} samples;  total < 0 : {bad}")
print(f"  how many of the three pair-terms E_il are negative at once: {neg_count}")
print(f"  worst  (sum of negative E)/(sum of positive E) = {worst_ratio:.4f}   (<1 means absorption always works)")
print()
print("is the negativity always confined to ONE pair, and is  C_il*N_il  dominated by")
print("the OTHER pairs' positive parts  C_im*P_l + C_lm*P_i  alone?")
bad2=0; worst2=0
for _ in range(20000):
    u=mp.mpf(random.uniform(0.02,0.999)); v=mp.mpf(random.uniform(0.01,float(u)))
    th=[mp.mpf(random.uniform(0.001,0.999)) for _ in range(3)]
    tot,out=parts(u,v,th)
    for idx,(E,CP,CN,D) in enumerate(out):
        if E<0:
            others=sum(out[j][1] for j in range(3) if j!=idx)+sum(out[j][3] for j in range(3) if j!=idx)
            if -E>others: bad2+=1
            worst2=max(worst2,float(-E/others) if others>0 else 9e9)
print(f"  violations of  |E_neg| <= (other pairs' C*P + D): {bad2};  worst ratio {worst2:.4f}")
