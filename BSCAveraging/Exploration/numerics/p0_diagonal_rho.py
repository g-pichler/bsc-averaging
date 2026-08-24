import mpmath as mp
mp.mp.dps=40
G=lambda z: 1-(1-z)*mp.atanh(mp.sqrt(z))/mp.sqrt(z)
def Theta(z,t):   # B(z)(G(z)-G(t))/A(z)
    m=G(t); A=z*mp.diff(G,z); B=1-G(z)
    return B*(G(z)-m)/A
def rho(w,t):
    rt=mp.sqrt(t); u=rt*mp.e**w; v=rt*mp.e**(-w)
    if u>=1: return mp.nan
    return mp.log(Theta(u,t))-mp.log(Theta(v,t))
print("rho(w) = log Theta(u) - log Theta(t/u),  u = sqrt(t) e^w    [need rho <= 0]")
print("  endpoints: rho(0)=0 exactly; rho(W)=0 exactly (log cancellation, W=log(1/sqrt t))")
for t in ['0.05','0.3','0.8']:
    t=mp.mpf(t); W=mp.log(1/mp.sqrt(t))
    vals=[(float(w),rho(mp.mpf(w)*W,t)) for w in ['0.001','0.1','0.3','0.5','0.7','0.9','0.999']]
    print(f"\n  t={float(t):4.2f}  (W={float(W):.4f})")
    for frac,r in vals:
        print(f"     w/W={frac:5.3f}: rho={mp.nstr(r,6):>12}  {'OK' if r<=1e-25 else 'VIOLATION'}")
    # sign pattern of rho'
    d=[mp.diff(lambda x: rho(x,t), mp.mpf(f)*W) for f in ['0.05','0.3','0.6','0.9','0.99']]
    print("     sign of rho' at w/W=0.05,0.3,0.6,0.9,0.99:", [('-' if x<0 else '+') for x in d])
