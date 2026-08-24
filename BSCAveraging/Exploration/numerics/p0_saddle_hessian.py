import numpy as np
from scipy.optimize import brentq
np.seterr(all='ignore')
L2=np.log(2)
def Psi(s):
    s=abs(s); return 0.5*((1+s)*np.log1p(s)+((1-s)*np.log1p(-s) if s<1 else 0.0))
def rate(x,y): return (y*Psi(x)+x*Psi(y))/(x+y)
def f(z): return 0.0 if z<=-1+1e-15 else (1+z)*np.log1p(z)
def IUV(d,a,b,c,e):
    pa,pb=b/(a+b),a/(a+b); qc,qe=e/(c+e),c/(c+e); tot=0
    for ps,s in ((pa,a),(pb,-b)):
        for q,t in ((qc,c),(qe,-e)): tot+=ps*q*f(d*s*t)
    return tot
def partner(x,C):                      # b with rate(x,b)=C
    g=lambda y: rate(x,y)-C
    if g(1e-12)*g(1.0)>0: return None
    return brentq(g,1e-12,1.0,xtol=1e-15)
def hessian(p,Cu,Cv,h=2e-3):
    d=1-2*p
    al=brentq(lambda x: Psi(x)-Cu,1e-12,1-1e-12)   # symmetric fixed point
    be=brentq(lambda x: Psi(x)-Cv,1e-12,1-1e-12)
    F=lambda x,y: IUV(d,x,partner(x,Cu),y,partner(y,Cv))
    Fxx=(F(al+h,be)-2*F(al,be)+F(al-h,be))/h**2
    Fyy=(F(al,be+h)-2*F(al,be)+F(al,be-h))/h**2
    Fxy=(F(al+h,be+h)-F(al+h,be-h)-F(al-h,be+h)+F(al-h,be-h))/(4*h*h)
    det=Fxx*Fyy-Fxy**2
    return Fxx,Fyy,Fxy,det,Fxy**2/(Fxx*Fyy)
print(" p      (Cu,Cv)b     Fxx      Fyy      Fxy      det      slope-product   verdict")
for (cu,cv) in [(0.4,0.4),(0.4,0.6),(0.2,0.7),(0.8,0.8)]:
    for p in [0.0,0.005,0.01,0.02,0.05,0.2]:
        Fxx,Fyy,Fxy,det,prod=hessian(p,cu*L2,cv*L2)
        verdict="SADDLE" if det<0 else ("local max" if Fxx<0 else "?")
        print(f"{p:5.3f}  ({cu},{cv})  {Fxx:+8.4f} {Fyy:+8.4f} {Fxy:+8.4f} {det:+9.5f}   {prod:8.4f}   {verdict}")
    print()
