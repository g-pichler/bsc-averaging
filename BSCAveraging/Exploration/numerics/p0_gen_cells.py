import mpmath as mp
from fractions import Fraction as Fr
mp.mp.dps=40
D = 10**7            # rational denominator for cell endpoints
DW = 10**7           # denominator for log witnesses
PAD = Fr(3, 10**6)   # widening pad on witnesses

def q(x):            # mpf -> Fraction on the D grid
    return Fr(int(mp.floor(x*D)), D)

def logwit(a, b):
    """witnesses bracketing the *enclosure* of log(cosh 2θ) over [a,b]"""
    A, B = mp.mpf(a.numerator)/a.denominator, mp.mpf(b.numerator)/b.denominator
    Zlo = (mp.exp(2*A) + mp.exp(-2*B))/2      # how coshI computes its lower bound
    Zhi = (mp.exp(2*B) + mp.exp(-2*A))/2
    lo = mp.log(Zlo); hi = mp.log(Zhi)
    lp = Fr(int(mp.floor(lo*DW)), DW) - PAD
    lq = Fr(int(mp.ceil(hi*DW)), DW) + PAD
    return lp, lq

def cells(lo, hi, width_fn):
    out=[]; a=Fr(lo)
    B=Fr(hi)
    while a < B:
        w = width_fn(float(a))
        b = min(a + w, B)
        lp, lq = logwit(a, b)
        mid = (a+b)/2
        cp, cq = logwit(mid, mid)
        out.append((a,b,lp,lq,cp,cq))
        a = b
    return out

def width(t):
    if t < 0.6:  return Fr(1,1000)
    if t < 1.0:  return Fr(2,1000)
    if t < 2.0:  return Fr(5,1000)
    return Fr(1,100)

cs = cells(Fr(45,100), Fr(3), width)
print(f"{len(cs)} cells")
def r(f): return f"{f.numerator}/{f.denominator}"
lines = [f"⟨{r(a)}, {r(b)}, {r(lp)}, {r(lq)}, {r(cp)}, {r(cq)}⟩" for (a,b,lp,lq,cp,cq) in cs]
open('/tmp/gen/cells.txt','w').write(",\n  ".join(lines))
print("first:", lines[0]); print("last: ", lines[-1])
