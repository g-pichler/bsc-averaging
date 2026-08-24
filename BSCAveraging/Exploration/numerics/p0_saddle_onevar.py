import mpmath as mp
mp.mp.dps=50
g=lambda y: (1-y**2)*mp.atanh(y)/y
def LL(al,be):
    x=al*be; G=g(x)
    return (1-G)**2/(x**2*(G/g(al)-1)*(G/g(be)-1))
def kprod(al,be):
    x=al*be; G=g(x); return (G/g(al)-1)*(G/g(be)-1)
print("1) is kappa_a*kappa_b MAXIMISED on the diagonal for fixed product x=al*be?")
for x in ['0.02','0.2','0.6','0.9']:
    x=mp.mpf(x); dg=kprod(mp.sqrt(x),mp.sqrt(x)); worst=0; arg=None
    r=mp.sqrt(x)
    for k in range(1,60):
        al=r+(1-r)*mp.mpf(k)/60
        if al>=1: break
        be=x/al
        d=kprod(al,be)-dg
        if d>worst: worst,arg=d,(al,be)
    print(f"   x={float(x):4.2f}: diag kprod={mp.nstr(dg,10)}  max excess off-diagonal={mp.nstr(worst,6)}"
          + (f"  at al={float(arg[0]):.3f}" if arg else "  (diagonal is the max)"))
print()
print("2) one-variable form:  1/log Z - 1/(Z-1) > tanh(th)/(2 th),  Z=cosh 2th")
def lhs(th):
    Z=mp.cosh(2*th); return 1/mp.log(Z)-1/(Z-1)
def rhs(th): return mp.tanh(th)/(2*th)
bad=0
for e in ['0.001','0.01','0.05','0.1','0.3','0.6','1.0','2.0','4.0','8.0']:
    th=mp.mpf(e); d=lhs(th)-rhs(th)
    print(f"   th={float(th):7.3f}   LHS-RHS = {mp.nstr(d,8)}")
    if d<=0: bad+=1
print(f"   violations: {bad}")
print()
print("3) equivalence check: (iii_sym) in y  vs  one-variable form in th=artanh y")
for y in ['0.05','0.2','0.5','0.8','0.95']:
    y=mp.mpf(y); th=mp.atanh(y)
    s1=g(y)*(1+y**2-g(y**2))-y**2*g(y**2)
    s2=lhs(th)-rhs(th)
    print(f"   y={float(y):4.2f}: (iii_sym) slack={mp.nstr(s1,8)}   one-var slack={mp.nstr(s2,8)}   "
          f"same sign: {(s1>0)==(s2>0)}")
