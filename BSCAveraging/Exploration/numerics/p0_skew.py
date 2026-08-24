import mpmath as mp
mp.mp.dps=30
def Psi(x): return mp.mpf('0.5')*((1+x)*mp.log(1+x)+(1-x)*mp.log(1-x))
def fF(z): return (1+z)*mp.log(1+z) if 1+z>0 else mp.mpf(0)
# U-side atoms (+a,-b), masses (b/(a+b), a/(a+b)); same for V with (c,d). delta = 1 (p=0)
def rate(a,b): return (b*Psi(a)+a*Psi(b))/(a+b)
def value(a,b,c,d):
    pu=[b/(a+b), a/(a+b)]; su=[a,-b]
    pv=[d/(c+d), c/(c+d)]; sv=[c,-d]
    return sum(pu[i]*pv[j]*fF(su[i]*sv[j]) for i in range(2) for j in range(2))
al=mp.mpf('0.5'); be=mp.mpf('0.5')
print("perturb U by +eps/-eps, V by -eps/+eps (opposite skews), delta=1")
print(f"{'eps':>10} {'value gain':>16} {'rate change U':>16} {'gain/eps^2':>14} {'drate/eps^2':>14}")
v0=value(al,al,be,be)
for e in ['1e-1','1e-2','1e-3','1e-4']:
    e=mp.mpf(e)
    v=value(al+e,al-e,be-e,be+e)
    dr=rate(al+e,al-e)-rate(al,al)
    print(f"{float(e):10.0e} {mp.nstr(v-v0,8):>16} {mp.nstr(dr,8):>16} {mp.nstr((v-v0)/e**2,8):>14} {mp.nstr(dr/e**2,8):>14}")
print("\n=> both gain and rate-cost are Theta(eps^2): the skew route needs the same")
print("   second-order comparison as the Hessian criterion, no shortcut.")
