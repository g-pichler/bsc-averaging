import mpmath as mp
mp.mp.dps=50
def Es(p,q,kap,v,eps):
    th=[1-eps*p, mp.mpf(0), 1-eps*q]; u=1-kap*eps
    t=u*v; c=1-u; d=u-v
    A=[1-x for x in th]; a=[1-x*u for x in th]; b=[1-x*v for x in th]; w=[1-x*t for x in th]
    r=[a[i]/b[i] for i in range(3)]
    lam=[A[i]/a[i]*sum(A[j]/w[j] for j in range(3) if j!=i) for i in range(3)]
    E=[]
    for (i,l,m) in [(0,1,2),(1,2,0),(0,2,1)]:
        C=(A[i]-A[l])**2*d*(r[i]+r[l])/(a[i]*a[l]*b[i]*b[l])
        N=A[i]*A[l]*u*(1-v)/(w[i]*w[l]); P=A[m]*c/w[m]
        D=lam[m]*(A[i]-A[l])**2*d**2/(b[i]**2*b[l]**2)
        E.append(C*(P-N)+D)
    return E    # [E12, E23, E13]
p,q,kap,v=mp.mpf('1.4'),mp.mpf(1),mp.mpf('0.7'),mp.mpf('0.53')
pred=p/(p+kap)-q/(q+kap)
print(f"predicted limits:  E12 -> {mp.nstr(-pred,8)},  E23 -> {mp.nstr(pred,8)},  E13 -> 0")
print(f"{'eps':>10} {'E12':>14} {'E23':>14} {'E13':>12} {'E12+E23':>13} {'total':>13} {'ratio':>9}")
for e in ['1e-1','1e-2','1e-3','1e-4','1e-5','1e-6']:
    e=mp.mpf(e); E=Es(p,q,kap,v,e); tot=sum(E)
    neg=-sum(x for x in E if x<0); pos=sum(x for x in E if x>0)
    print(f"{float(e):10.0e} {mp.nstr(E[0],6):>14} {mp.nstr(E[1],6):>14} {mp.nstr(E[2],6):>12} "
          f"{mp.nstr(E[0]+E[1],6):>13} {mp.nstr(tot,6):>13} {float(neg/pos):9.6f}")
print("\n=> leading orders cancel exactly; the total is O(eps) positive, ratio -> 1.")
