# NOTES.md §7l.  Replace the saddle step (C) by a global comparison?
#   (1) BSC pair vs (Z_a, S_d) / (Z_a, Z_d) at *equal rates* -- the inequality
#       that would make (C) unnecessary;
#   (2) it does not split into one-sided steps: against a fixed BSC the corner
#       is worse;
#   (3) the centre-linear path from the BSC pair to the corner pair at fixed
#       rates: V(l) is monotone and convex, V'(0) = 0, gain = odd part vs even loss.
import math
L2 = math.log(2)
def f(z):  return 0.0 if z <= -1 else (1 + z) * math.log(1 + z)
def fe(z): return 0.5 * (f(z) + f(-z))
def fo(z): return 0.5 * (f(z) - f(-z))
def RZ(a): return (fe(a) + a * L2) / (1 + a)            # rate of Z_a (= of S_a)
def bis(g, lo, hi, target):
    for _ in range(100):
        m = (lo + hi) / 2
        if g(m) < target: lo = m
        else: hi = m
    return (lo + hi) / 2
def law(p, h):                                          # mean-zero two-atom law, atoms p±h
    s1, s2 = p + h, p - h
    return [(s1, -s2 / (s1 - s2)), (s2, s1 / (s1 - s2))]
def rate(l): return sum(w * fe(x) for x, w in l)
def val(l1, l2): return sum(p * q * f(x * y) for x, p in l1 for y, q in l2)
def Z(a): return [(-1, a / (1 + a)), (a, 1 / (1 + a))]
def S(d): return [(1, d / (1 + d)), (-d, 1 / (1 + d))]
def BSC(s): return [(s, .5), (-s, .5)]
def side(p, r):                                         # two-atom law at centre p with rate r
    return law(p, bis(lambda h: rate(law(p, h)), abs(p) + 1e-15, 1 - abs(p), r))

# (1) the global comparison at equal rates
worst_max = (1e9, None); worst_min = (1e9, None); worst_rel = (1e9, None)
for i in range(1, 200):
    for j in range(1, 200):
        s, t = i / 200, j / 200
        a, d = bis(RZ, 0, 1, fe(s)), bis(RZ, 0, 1, fe(t))
        vb, vzs, vzz = val(BSC(s), BSC(t)), val(Z(a), S(d)), val(Z(a), Z(d))
        worst_max = min(worst_max, (vzs - vb, (s, t)))
        worst_min = min(worst_min, (vb - vzz, (s, t)))
        worst_rel = min(worst_rel, (vzs / vb - 1, (s, t)))
print("(1) min V_ZS-V_BSC:", worst_max, " min V_BSC-V_ZZ:", worst_min)
print("    min relative slack V_ZS/V_BSC-1:", worst_rel)
for e in [1e-1, 1e-2, 1e-3, 1e-4]:
    s = t = 1 - e; a = d = bis(RZ, 0, 1, fe(s))
    print("    s=t=1-%g: relative slack %.3e" % (e, val(Z(a), S(d)) / val(BSC(s), BSC(t)) - 1))

# (2) one-sided step fails: fix V = BSC_t, compare U = Z_a with U = BSC_s at equal rate
print("(2) V(Z_a,BSC_t)/V(BSC_s,BSC_t) at equal rate, s,t in {.05,.3,.6,.9}:")
for s in [0.05, 0.3, 0.6, 0.9]:
    a = bis(RZ, 0, 1, fe(s))
    print("    s=%.2f: " % s + "  ".join("%.4f" % (val(Z(a), BSC(t)) / val(BSC(s), BSC(t))) for t in [0.05, 0.3, 0.6, 0.9]))

# (3) the centre-linear path at fixed rates
def V(s, t, l):
    rU, rV = fe(s), fe(t); a, d = bis(RZ, 0, 1, rU), bis(RZ, 0, 1, rV)
    return val(side(l * (a - 1) / 2, rU), side(l * (1 - d) / 2, rV))
bad_m = bad_c = n = 0
for i in range(1, 20):
    for j in range(1, 20):
        s, t = i / 20, j / 20; vs = [V(s, t, k / 20) for k in range(21)]; n += 1
        if not all(vs[k + 1] >= vs[k] - 1e-14 for k in range(20)): bad_m += 1
        if not all(vs[k - 1] - 2 * vs[k] + vs[k + 1] >= -1e-14 for k in range(1, 20)): bad_c += 1
print("(3) path, %d (s,t) points x 21 steps: non-monotone %d, non-convex %d" % (n, bad_m, bad_c))
for (s, t) in [(0.1, 0.1), (0.5, 0.5), (0.9, 0.9), (0.05, 0.95)]:
    v0 = V(s, t, 0)
    print("    s=%.2f t=%.2f  V(l)/V(0): " % (s, t) + " ".join("%.4f" % (V(s, t, k / 10) / v0) for k in range(11)))
print("    even/odd split, s=t=0.5:  l  even/V0  odd/V0")
for k in range(0, 11, 2):
    l = k / 10; rU = rV = fe(0.5); a = bis(RZ, 0, 1, rU)
    l1, l2 = side(l * (a - 1) / 2, rU), side(l * (1 - a) / 2, rV); v0 = V(0.5, 0.5, 0)
    print("      %.1f  %.4f  %+.4f" % (l, sum(p * q * fe(x * y) for x, p in l1 for y, q in l2) / v0,
                                        sum(p * q * fo(x * y) for x, p in l1 for y, q in l2) / v0))

# (3b) the same without rate control: interpolate the atoms linearly, weights from mean zero
def lin(x0, x1, l): return (1 - l) * x0 + l * x1
def Vlin(s, t, l):
    a, d = bis(RZ, 0, 1, fe(s)), bis(RZ, 0, 1, fe(t))
    return val(law_atoms(lin(s, a, l), lin(-s, -1, l)), law_atoms(lin(t, 1, l), lin(-t, -d, l)))
def law_atoms(s1, s2): return [(s1, -s2 / (s1 - s2)), (s2, s1 / (s1 - s2))]
bad_m = n = 0
for i in range(1, 40):
    for j in range(1, 40):
        s, t = i / 40, j / 40; vs = [Vlin(s, t, k / 40) for k in range(41)]; n += 1
        if not all(vs[k + 1] >= vs[k] - 1e-14 for k in range(40)): bad_m += 1
print("(3b) linear-atom path, no rate control, %d points: non-monotone %d" % (n, bad_m))
for (s, t) in [(0.1, 0.1), (0.9, 0.9)]:
    v0 = Vlin(s, t, 0)
    print("     s=%.2f t=%.2f  V(l)/V(0): " % (s, t) + " ".join("%.3f" % (Vlin(s, t, k / 10) / v0) for k in range(11)))

# (3c) is convexity along the rate-constant path provable?  where V'' is smallest,
#      the cone margin at l = 0, and the endpoint singularity
def d2(s, t, l, h=2e-3): return (V(s, t, l - h) - 2 * V(s, t, l) + V(s, t, l + h)) / h ** 2
def d1(s, t, l, h=1e-4): return (V(s, t, l + h) - V(s, t, l - h)) / (2 * h)
print("(3c) V''(l)/V(0), l = .05 .. .95 (every third):")
for (s, t) in [(0.1, 0.1), (0.5, 0.5), (0.9, 0.9)]:
    v0 = V(s, t, 0); prof = [d2(s, t, k / 20) / v0 for k in range(1, 20)]
    print("     s=%.2f t=%.2f min=%.1e at l=%.2f | " % (s, t, min(prof), (prof.index(min(prof)) + 1) / 20) + " ".join("%.1e" % x for x in prof[::3]))
def G(y): return (1 - y * y) * math.atanh(y) / y
print("     l=0 cone: path direction q1/|p1| vs the roots (r-,r+) of the Hessian form, and margin")
for (s, t) in [(0.05, 0.05), (0.1, 0.1), (0.5, 0.5), (0.9, 0.9), (0.2, 0.8)]:
    a, d = bis(RZ, 0, 1, fe(s)), bis(RZ, 0, 1, fe(t)); p1, q1 = (a - 1) / 2, (1 - d) / 2; x = s * t
    Fpp = -t * t * (G(x) / G(s) - 1) / (1 - x * x); Fqq = -s * s * (G(x) / G(t) - 1) / (1 - x * x); Fpq = -(1 - G(x)) / (1 - x * x)
    Q = Fpp * p1 * p1 + 2 * Fpq * p1 * q1 + Fqq * q1 * q1; disc = Fpq * Fpq - Fpp * Fqq
    rm, rp = (-Fpq - math.sqrt(disc)) / (-Fqq), (-Fpq + math.sqrt(disc)) / (-Fqq)
    print("       s=%.2f t=%.2f  q1/|p1|=%.3f  cone=(%.3f,%.3f)  margin=%+.4f" % (s, t, q1 / abs(p1), rm, rp, Q / (abs(Fpp) * p1 * p1 + abs(Fqq) * q1 * q1)))
print("     endpoint V'(l)/V(0), s=t=0.1: " + "  ".join("1-%g: %.2f" % (e, d1(0.1, 0.1, 1 - e, h=e / 4) / V(0.1, 0.1, 0)) for e in [1e-2, 1e-3, 1e-4, 1e-5]))

# (3d) the global comparison directly: where it is thin, and the edge expansion
def VZS(a, d): return (a * f(d) + d * f(a) + f(-a * d)) / ((1 + a) * (1 + d))
A = lambda s: bis(RZ, 0, 1, fe(s))
def dVda(a, d, h=1e-6): return (VZS(a + h, d) - VZS(a - h, d)) / (2 * h)
print("(3d) relative slack along st = x: min over s, and the diagonal value")
for x in [0.1, 0.5, 0.9]:
    best = min((VZS(A(s), A(x / s)) / fe(x) - 1, s) for s in [x + (1 - x) * k / 400 for k in range(1, 400)] if 0 < x / s <= 1)
    print("     x=%.1f  min %.2e at s=%.3f   diagonal %.2e" % (x, best[0], best[1], VZS(A(x ** .5), A(x ** .5)) / fe(x) - 1))
print("     corner s=t=1-sigma: (1-a)/sigma, rel.slack/sigma, rel.slack/sigma*ln(1/sigma)")
for e in [1e-1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6]:
    s = 1 - e; a = A(s); r = VZS(a, a) / fe(s * s) - 1
    print("       sigma=%-6g  %.4f  %.3f  %.3f" % (e, (1 - a) / e, r / e, r / e * math.log(1 / e)))
print("     edge s=1-sigma, t fixed: observed rel.slack/sigma vs first-order prediction")
print("       [t artanh t - (alpha/sigma) dV_ZS/da(1,d)] / f_e(t)   (regular in (sigma,alpha); only alpha(sigma) is singular)")
for t in [0.2, 0.5, 0.8]:
    d = A(t); row = []
    for e in [1e-1, 1e-2, 1e-3, 1e-4]:
        a = A(1 - e); obs = (VZS(a, d) / fe((1 - e) * t) - 1) / e
        pred = (t * math.atanh(t) - ((1 - a) / e) * dVda(1 - 1e-7, d)) / fe(t)
        row.append("%.3f/%.3f" % (obs, pred))
    print("       t=%.1f: " % t + "  ".join(row))
print("     limit coefficient c(t) = [t artanh t - 2 dV/da(1,d(t))]/f_e(t): " +
      "  ".join("t=%.2f %.3f" % (t, (t * math.atanh(t) - 2 * dVda(1 - 1e-7, A(t))) / fe(t)) for t in [0.05, 0.5, 0.95, 0.99]))
print("     min side edge: (V_BSC - V_ZZ)/V_BSC/sigma at t=0.5: " + "  ".join("%g: %.1f" % (e, (1 - val(Z(A(1 - e)), Z(A(0.5))) / fe((1 - e) * 0.5)) / e) for e in [1e-1, 1e-3, 1e-5]) + "   (grows like ln(1/sigma))")
print("     crude explicit bound a >= f_e(s)/ln2: min rel. slack " + "%.3f" % min(VZS(fe(s) / L2, fe(t) / L2) / fe(s * t) - 1 for s in [i / 100 for i in range(1, 100)] for t in [j / 100 for j in range(1, 100)]) + "  (fails near the edge)")
