import numpy as np
from scipy.integrate import quad
np.seterr(all='ignore')
L=lambda x: np.logaddexp(x,-x)-np.log(2)
M=lambda w,g: L(w+g)-L(w-g)
Mpp=lambda w,g: 1/np.cosh(w+g)**2-1/np.cosh(w-g)**2
sech2=lambda x: 1/np.cosh(x)**2
def check(u,v,m,n):
    X=u+v; p,q=X-m,X+m
    lam=(M(q,n)-M(p,n))/(2*m); c2=lam*q-M(q,n)
    R=quad(lambda w:(M(w,n)-lam*w+c2)*sech2(w-v),p,q,limit=200)[0]
    bK=(L(q-v)-L(p-v))/(2*m); aK=L(p-v)-bK*p
    K=lambda w: L(w-v)-(aK+bK*w)
    if X>=m:  # window inside the concave half
        return R, R, None, None
    I1=quad(lambda t: Mpp(t,n)*(K(t)-K(-t)),0,m-X,limit=200)[0]
    I2=quad(lambda t: Mpp(t,n)*K(t),m-X,m+X,limit=200)[0] if X>0 else 0.0
    return R, I1+I2, I1, I2
print("step check over v>0, 0<=X<m :   R>0 ?   split R = I1 + I2 with I1,I2 >= 0 ?")
badR=badI1=badI2=badsplit=0; n_t=0
for m in [0.3,0.9,1.8]:
  for n in [0.2,0.7,1.9]:
    for v in np.linspace(0.02,1.6,14):
      for X in np.linspace(0.0,min(1.6,0.999*m),14):
        u=X-v; R,S,I1,I2=check(u,v,m,n); n_t+=1
        if R<=0: badR+=1
        if abs(R-S)>1e-9: badsplit+=1
        if I1 is not None and I1<-1e-12: badI1+=1
        if I2 is not None and I2<-1e-12: badI2+=1
print(f"   tested {n_t}:  R<=0 : {badR}   split mismatch: {badsplit}   I1<0 : {badI1}   I2<0 : {badI2}")
print()
print("(♦) via convexity of log cosh:  2g·tanh(Y−2g) ≤ L(Y) − L(Y−2g)")
worst=1e9
for Y in np.linspace(0.01,8,60):
  for g in np.linspace(1e-4,Y/2*0.999,60):
    worst=min(worst,(L(Y)-L(Y-2*g))-2*g*np.tanh(Y-2*g))
print(f"   min slack over the grid: {worst:.3e}   (0 only in the limit g→0)")
print()
print("full fixed-point consequence: R_S=0 & v>0 ⟹ X<0 ;  R_T=0 & u>0 ⟹ X<0")
from scipy.optimize import brentq
for (m,n) in [(0.9,0.8),(1.6,0.3)]:
    for v in [0.3,1.0]:
        uS=brentq(lambda u: check(u,v,m,n)[0],-4,4,xtol=1e-13)
        print(f"   m={m} n={n} v={v}: R_S=0 at u={uS:+.6f}, X={uS+v:+.6f} (<0: {uS+v<0})")
