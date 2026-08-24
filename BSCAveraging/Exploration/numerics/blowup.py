import os
_HERE = os.path.dirname(os.path.abspath(__file__))
from collections import defaultdict
from math import comb
_src=open(os.path.join(_HERE, 'newcoord.py')).read().split("neg={k:v")[0]
exec(_src)
groups=defaultdict(dict)
for m,cf in tot.items(): groups[m[:3]][m[3:]]=cf

def to_sw(poly):
    """a=s(1-w), b=sw  ->  dict {(deg_s, deg_w): coeff} in basis s^p w^q"""
    out=defaultdict(int)
    for (i,j),c in poly.items():
        for t in range(i+1):                    # (1-w)^i
            out[(i+j, j+t)] += c*comb(i,t)*(-1)**t
    return {k:v for k,v in out.items() if v}
def bernstein_ok(poly, K=30):
    """certify >=0 on [0,1]^2 : expand in s^p w^q, elevate with (s+(1-s)) etc."""
    ds=max(p for p,_ in poly); dw=max(q for _,q in poly)
    for k in range(K+1):
        # Bernstein coefficients of degree (ds+k, dw+k)
        Ds, Dw = ds+k, dw+k
        ok=True; nterms=(Ds+1)*(Dw+1)
        for I in range(Ds+1):
            for J in range(Dw+1):
                v=0
                for (p,q),c in poly.items():
                    if p<=I and q<=J and (Ds-p)>=(I-p) and (Dw-q)>=(J-q):
                        v += c*comb(I,p)*comb(Ds-I,0)*0  # placeholder
                # proper Bernstein coefficient formula
                v=0
                for (p,q),c in poly.items():
                    if p<=I and q<=J:
                        v += c*comb(I,p)*comb(J,q)/ (comb(Ds,p)*comb(Dw,q)) if comb(Ds,p)*comb(Dw,q) else 0
                if v < -1e-15: ok=False; break
            if not ok: break
        if ok: return k, nterms
    return None, None
cert=0; fail=0; maxk=0; terms=0
for zk,poly in groups.items():
    ia=min(e[0] for e in poly); ib=min(e[1] for e in poly)
    q={(e[0]-ia,e[1]-ib):c for e,c in poly.items()}
    sw=to_sw(q)
    m0=min(p for p,_ in sw)
    sw={(p-m0,qq):c for (p,qq),c in sw.items()}     # factor s^m0
    k,n=bernstein_ok(sw)
    if k is None: fail+=1
    else: cert+=1; maxk=max(maxk,k); terms+=n
print("groups certified in the (s,w) box:", cert, "/", len(groups), " failures:", fail)
print("max Bernstein elevation:", maxk, "  total certificate coefficients:", terms)
