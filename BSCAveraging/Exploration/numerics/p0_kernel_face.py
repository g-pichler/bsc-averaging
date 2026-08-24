import sympy as sp
r1,r2,r3,k=sp.symbols('r1 r2 r3 kappa', positive=True)
r=[r1,r2,r3]; v=1-k; s=[(1-xx)/k for xx in r]
c=[r[i]**2-r[(i+1)%3]*r[(i+2)%3] for i in range(3)]
C=sum(c); D=0
for i in range(3):
    j,kk=(i+1)%3,(i+2)%3
    D+= -(s[i]/r[i])*(r[j]+r[kk])*c[i] + (r[j]+r[kk])*(2*r[i]*s[i]-s[j]*r[kk]-r[j]*s[kk])
D+= -v*sum(r[j]*s[j]*(C-c[j]) for j in range(3))
P=sp.expand(sp.simplify(sp.together(D)*k*r1*r2*r3)); Pk=sp.Poly(P,k)
X=sp.expand(Pk.coeff_monomial(k)); Y=sp.expand(Pk.coeff_monomial(1))
w,q,p,m=sp.symbols('w q p m', nonnegative=True)
sub={r3:w, r2:w+q, r1:w+q+p}
for name,poly in [('Y',Y),('X',X)]:
    E=sp.expand(poly.subs(sub,simultaneous=True))
    print(f"\n=== {name} in simplex coords (w,q,p), with m = 1-w-q-p ===")
    for N in range(0,7):
        # homogenise using w+q+p+m = 1, then elevate by N
        Eh=sp.expand(E*(w+q+p+m)**N)
        # substitute nothing: we need the homogeneous form. Homogenise term by term.
        Ep=sp.Poly(Eh,w,q,p,m)
        d=Ep.total_degree()
        hom=sum(co*mo[0]**0*w**mo[0]*q**mo[1]*p**mo[2]*m**mo[3]*(w+q+p+m)**(d-sum(mo))
                for mo,co in zip(Ep.monoms(),Ep.coeffs()))
        H=sp.Poly(sp.expand(hom),w,q,p,m)
        neg=[(mo,co) for mo,co in zip(H.monoms(),H.coeffs()) if co<0]
        print(f"   elevation N={N}: degree {H.total_degree()}, negative coefficients: {len(neg)}")
        if not neg:
            print(f"   *** ALL COEFFICIENTS NONNEGATIVE at N={N} — Polya certificate found for {name} ***")
            break
