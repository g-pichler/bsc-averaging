"""Generate the cells of the regime-2 sweep (CoreSweep.lean).

The widths are *adaptive*: at each step the generator takes the widest cell on
the 1/1000 grid that still passes `cellOkC`, so cells grow from 2/1000 near
0.45, where `F` is smallest and `|F'|` largest, to 149/1000 near 3.  That needs
the Lean test itself, so `Interval.lean` / `CoreDeriv.lean` are ported below
verbatim onto `fractions.Fraction`; the port is validated by re-checking every
generated cell before the file is written.

Emits the `cellsC..` blocks of `CoreSweep.lean` on stdout.
"""
import math, sys
from fractions import Fraction as Fr
import mpmath as mp
mp.mp.dps = 40

K, N, M = 4, 10, 10**9   # squarings, series terms, rounding grid
DW = 10**7               # denominator of the log witnesses
PAD = Fr(3, 10**6)       # widening pad on the witnesses
GRID = 1000              # cell endpoints live on 1/GRID
LO, HI = Fr(45, 100), Fr(3)

# ---------------------------------------------------------------- Interval.lean

def fl(x): return x.numerator // x.denominator
def ce(x): return -((-x.numerator) // x.denominator)

class Iv:
    __slots__ = ('lo', 'hi')
    def __init__(self, lo, hi): self.lo, self.hi = Fr(lo), Fr(hi)

def const(q):   return Iv(q, q)
def add(I, J):  return Iv(I.lo + J.lo, I.hi + J.hi)
def neg(I):     return Iv(-I.hi, -I.lo)
def sub(I, J):  return add(I, neg(J))
def mul(I, J):
    p = (I.lo * J.lo, I.lo * J.hi, I.hi * J.lo, I.hi * J.hi)
    return Iv(min(p), max(p))
def outward(m, I): return Iv(Fr(fl(I.lo * m), m), Fr(ce(I.hi * m), m))
def sq(I):      return mul(I, I)
def sqIter(m, k, I):
    for _ in range(k): I = outward(m, sq(I))
    return I
def inv(J):     return Iv(Fr(1) / J.hi, Fr(1) / J.lo)
def div(I, J):  return mul(I, inv(J))
def scale(c, I): return mul(const(c), I)

def expSum(q, n):
    s, f = Fr(0), 1
    for i in range(n):
        if i > 0: f *= i
        s += q ** i / f
    return s

def expIv1(q, n):
    s = expSum(q, n)
    e = abs(q) ** n * Fr(n + 1, math.factorial(n) * n)
    return Iv(s - e, s + e)

def expIv(q, k, n, m): return sqIter(m, k, outward(m, expIv1(q / Fr(2 ** k), n)))
def expI(I, k, n, m):  return Iv(expIv(I.lo, k, n, m).lo, expIv(I.hi, k, n, m).hi)
def coshI(I, k, n, m):
    return outward(m, scale(Fr(1, 2), add(expI(I, k, n, m), expI(neg(I), k, n, m))))
def sinhI(I, k, n, m):
    return outward(m, scale(Fr(1, 2), sub(expI(I, k, n, m), expI(neg(I), k, n, m))))
def tanhI(I, k, n, m): return outward(m, div(sinhI(I, k, n, m), coshI(I, k, n, m)))
def absBound(I): return max(abs(I.lo), abs(I.hi))

# ---------------------------------------------------------------- CoreDeriv.lean

def FI2(Ith, lp, lq, k, n, m):
    Z = coshI(scale(2, Ith), k, n, m)
    Zm1 = outward(m, sub(Z, const(1)))
    L = Iv(lp, lq)
    return outward(m, sub(outward(m, div(sub(Zm1, L), outward(m, mul(L, Zm1)))),
                          outward(m, div(tanhI(Ith, k, n, m), scale(2, Ith)))))

def FpI(Ith, lp, lq, k, n, m):
    I2 = scale(2, Ith); Z = coshI(I2, k, n, m); S2 = sinhI(I2, k, n, m)
    L = Iv(lp, lq); C = coshI(Ith, k, n, m); S = sinhI(Ith, k, n, m)
    t1 = outward(m, div(neg(outward(m, div(scale(2, S2), Z))), outward(m, mul(L, L))))
    t2 = outward(m, div(neg(scale(2, S2)),
        outward(m, mul(outward(m, sub(Z, const(1))), outward(m, sub(Z, const(1)))))))
    den = outward(m, mul(C, I2))
    num = outward(m, sub(outward(m, mul(C, den)),
        outward(m, mul(S, outward(m, add(outward(m, mul(S, I2)), scale(2, C)))))))
    t3 = outward(m, div(num, outward(m, mul(den, den))))
    return outward(m, sub(outward(m, sub(t1, t2)), t3))

def _le1(q, k): return abs(q / Fr(2 ** k)) <= 1

def fpOk(I, lp, lq, k, n, m):
    I2 = scale(2, I); Z = coshI(I2, k, n, m); Zm1 = outward(m, sub(Z, const(1)))
    den = outward(m, mul(coshI(I, k, n, m), I2))
    return (_le1(lp, k) and _le1(lq, k)
            and expIv(lp, k, n, m).hi <= Z.lo and Z.hi <= expIv(lq, k, n, m).lo
            and Z.lo > 0 and outward(m, mul(Iv(lp, lq), Iv(lp, lq))).lo > 0
            and outward(m, mul(Zm1, Zm1)).lo > 0 and outward(m, mul(den, den)).lo > 0
            and coshI(I, k, n, m).lo > 0
            and _le1(I2.lo, k) and _le1(I2.hi, k)
            and _le1(neg(I2).lo, k) and _le1(neg(I2).hi, k)
            and _le1(I.lo, k) and _le1(I.hi, k)
            and _le1(neg(I).lo, k) and _le1(neg(I).hi, k))

def fOk(I, p, q, k, n, m):
    I2 = scale(2, I); Z = coshI(I2, k, n, m); Zm1 = outward(m, sub(Z, const(1)))
    return (I.lo > 0 and _le1(p, k) and _le1(q, k) and p > 0
            and expIv(p, k, n, m).hi <= Z.lo and Z.hi <= expIv(q, k, n, m).lo
            and Zm1.lo > 0 and outward(m, mul(Iv(p, q), Zm1)).lo > 0
            and I2.lo > 0 and coshI(I, k, n, m).lo > 0
            and _le1(I2.lo, k) and _le1(I2.hi, k)
            and _le1(neg(I2).lo, k) and _le1(neg(I2).hi, k)
            and _le1(I.lo, k) and _le1(I.hi, k)
            and _le1(neg(I).lo, k) and _le1(neg(I).hi, k))

def cellOkC(cell, k=K, n=N, m=M):
    lo, hi, lp, lq, cp, cq = cell
    if not (lo > 0 and lo <= hi): return False
    if not fpOk(Iv(lo, hi), lp, lq, k, n, m): return False
    mid = (lo + hi) / 2
    if not fOk(Iv(mid, mid), cp, cq, k, n, m): return False
    return absBound(FpI(Iv(lo, hi), lp, lq, k, n, m)) * (hi - lo) \
        < FI2(Iv(mid, mid), cp, cq, k, n, m).lo

# ---------------------------------------------------------------- generation

def logwit(a, b):
    """witnesses bracketing the *enclosure* of log(cosh 2θ) over [a,b]"""
    A = mp.mpf(a.numerator) / a.denominator
    B = mp.mpf(b.numerator) / b.denominator
    Zlo = (mp.exp(2 * A) + mp.exp(-2 * B)) / 2      # how coshI forms its lower bound
    Zhi = (mp.exp(2 * B) + mp.exp(-2 * A)) / 2
    lp = Fr(int(mp.floor(mp.log(Zlo) * DW)), DW) - PAD
    lq = Fr(int(mp.ceil(mp.log(Zhi) * DW)), DW) + PAD
    return lp, lq

def mkcell(a, b):
    lp, lq = logwit(a, b)
    mid = (a + b) / 2
    cp, cq = logwit(mid, mid)
    return (a, b, lp, lq, cp, cq)

def generate():
    out, a = [], LO
    while a < HI:
        lim = min(400, int((HI - a) * GRID))
        if not cellOkC(mkcell(a, a + Fr(1, GRID))):
            sys.exit(f"minimal width fails at {float(a)}")
        lo, hi = 1, lim                     # widest passing width, by bisection
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if cellOkC(mkcell(a, a + Fr(mid, GRID))): lo = mid
            else: hi = mid - 1
        b = a + Fr(lo, GRID)
        out.append(mkcell(a, b))
        a = b
    return out

def r(f): return f"{f.numerator}/{f.denominator}"

if __name__ == "__main__":
    cs = generate()
    assert cs[0][0] == LO and cs[-1][1] == HI
    assert all(cs[i][1] == cs[i + 1][0] for i in range(len(cs) - 1))
    assert all(cellOkC(c) for c in cs)
    ws = [float(c[1] - c[0]) for c in cs]
    print(f"-- {len(cs)} cells, widths {min(ws)}..{max(ws)}", file=sys.stderr)
    for i in range(0, len(cs), 10):
        body = ",\n   ".join("⟨" + ", ".join(r(x) for x in c) + "⟩" for c in cs[i:i + 10])
        print(f"\ndef cellsC{i // 10:02d} : List CellC :=\n  [{body}]")
