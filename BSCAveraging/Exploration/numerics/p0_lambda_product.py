import numpy as np
np.seterr(all='ignore')
at=np.arctanh
g=lambda y: (1-y**2)*at(y)/y
def LL(al,be):                      # Lambda*Lambda' at delta=1, x=al*be
    x=al*be; G=g(x)
    ka=G/g(al)-1; kb=G/g(be)-1
    return (1-G)**2/(x**2*ka*kb)
print("Lambda*Lambda' at p=0  (>1 ⟹ symmetric point is a saddle)")
print("  al\\be " + " ".join(f"{b:6.2f}" for b in [0.05,0.2,0.4,0.6,0.8,0.95,0.99]))
for a in [0.05,0.2,0.4,0.6,0.8,0.95,0.99]:
    print(f"{a:6.2f} "+" ".join(f"{LL(a,b):6.3f}" for b in [0.05,0.2,0.4,0.6,0.8,0.95,0.99]))
print()
vals=[LL(a,b) for a in np.linspace(0.01,0.995,120) for b in np.linspace(0.01,0.995,120)]
vals=np.array(vals); print(f"grid min = {vals.min():.6f}   max = {vals.max():.4f}   any <=1: {(vals<=1).any()}")
print()
print("small-rate limit (al=be=eps):")
for e in [0.3,0.1,0.03,0.01,0.003,0.001]:
    print(f"   eps={e:6.3f}   LL={LL(e,e):.8f}")
print()
print("cross-check vs measured Hessian slope product (Cu=Cv=0.4 b ⟹ al=be=0.70779): "
      f"{LL(0.70779,0.70779):.4f}  (Hessian gave 1.1954)")
