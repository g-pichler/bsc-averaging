import numpy as np
from scipy.optimize import brentq
np.seterr(all='ignore')
L2=np.log(2); at=np.arctanh
Psi=lambda s: 0.5*((1+s)*np.log1p(s)+(1-s)*np.log1p(-s))
g=lambda y: (1-y**2)*at(y)/y
def LL(p,al,be):
    x=(1-2*p)*al*be; G=g(x)
    return (1-G)**2/(x**2*(G/g(al)-1)*(G/g(be)-1))
def theta_pred(Cub,Cvb):
    al=brentq(lambda x: Psi(x)-Cub*L2,1e-12,1-1e-12)
    be=brentq(lambda x: Psi(x)-Cvb*L2,1e-12,1-1e-12)
    if LL(0.0,al,be)<=1: return 0.0
    return brentq(lambda p: LL(p,al,be)-1,1e-9,0.4,xtol=1e-14)
meas={(0.05,0.05):9.1,(0.05,0.4):13.1,(0.2,0.2):12.5,(0.4,0.4):15.2,(0.4,0.6):14.5,
      (0.6,0.6):13.3,(0.8,0.8):7.1,(0.95,0.95):1.4,(0.1,0.9):11.1,(0.2,0.7):13.0}
print(" (Cu,Cv)b    theta predicted x1000   theta measured x1000 (bisection scan)")
for k,v in meas.items():
    print(f" {k}      {1000*theta_pred(*k):8.2f}                {v:6.1f}")
