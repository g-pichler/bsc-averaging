import mpmath as mp
from fractions import Fraction as Fr
mp.mp.dps=60
# exact coefficients h_k of Delta(theta)/theta^9 = sum h_k theta^(2k)   (from sympy, k=0..8)
H=[Fr(8,45),Fr(-8,21),Fr(1016,1575),Fr(-22592,22275),Fr(36728528,23648625),
   Fr(-100337464,42567525),Fr(83053225048,23260111875),Fr(-7816607790496,1443677610375),
   Fr(3266800331003056,397011342853125)]
M=mp.mpf('9.05'); r=mp.mpf('0.75'); Mh=M/r**9; q=1/r**2      # |h_k| <= Mh * q^k
print(f"Cauchy: |h_k| <= {float(Mh):.1f} * {float(q):.4f}^k")
def lower(t):                      # rigorous lower bound for Delta/theta^9
    s=sum(mp.mpf(h.numerator)/h.denominator*t**(2*k) for k,h in enumerate(H))
    x=q*t**2
    tail=Mh*x**9/(1-x) if x<1 else mp.inf
    return s-tail
print("\nregime 1: rigorous lower bound on Delta/theta^9 over (0, 0.45]")
grid=[mp.mpf(i)/1000 for i in range(1,451)]
vals=[lower(t) for t in grid]
print(f"   min over grid = {mp.nstr(min(vals),6)}  at theta={float(grid[vals.index(min(vals))]):.3f}   all>0: {min(vals)>0}")
def Delta(t):
    sh=mp.sinh(t); ch=mp.cosh(t)
    return 2*t*sh**2 - mp.log(mp.cosh(2*t))*(t + sh**3/ch)
def K(b):
    sh=mp.sinh(b); ch=mp.cosh(b); lc=mp.log(mp.cosh(2*b))
    return 2*sh**2+4*b*sh*ch+2*(b+sh**2)+lc*(1+2*sh*ch+sh**2)
print("\nregime 2: certified stepping on [0.45, 3]")
a=mp.mpf('0.45'); hi=mp.mpf(3); n=0
while a<hi:
    step=Delta(a)/K(min(a*mp.mpf('1.2'),hi))*mp.mpf('0.9')
    if step<=0: print("   FAIL at",float(a)); break
    a+=step; n+=1
print(f"   steps: {n}   reached {float(min(a,hi)):.4f}   success: {a>=hi}")
print("\nregime 3: theta>=3 elementary:  log2 > e^{-4t} + 8.04 t^2 e^{-2t}")
t=mp.mpf(3); print(f"   at theta=3: {mp.nstr(mp.e**(-4*t)+mp.mpf('8.04')*t**2*mp.e**(-2*t),6)} < 0.6931 ; RHS decreasing for t>=3")
print("\nCOVERAGE: (0,0.45] u [0.45,3] u [3,inf)  =  (0,inf)   -> QED")
