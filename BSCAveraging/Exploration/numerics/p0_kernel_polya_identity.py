import pickle, random, os
from fractions import Fraction as F
cert=pickle.load(open(f"{os.environ['SC']}/cert.pkl","rb"))
def kerQ(th1,th2,th3,u,v):
    A=[1-th1,1-th2,1-th3]; a=[1-th1*u,1-th2*u,1-th3*u]
    b=[1-th1*v,1-th2*v,1-th3*v]; w=[1-th1*u*v,1-th2*u*v,1-th3*u*v]
    s=0
    for i in range(3):
        j,k=(i+1)%3,(i+2)%3
        s+=A[i]*(a[j]*a[k])*(A[j]*(w[i]*w[k])+A[k]*(w[i]*w[j]))*(a[i]**2*(b[j]**2*b[k]**2)-a[j]*a[k]*(b[i]**2*(b[j]*b[k])))
    return s
random.seed(11); bad=0
for trial in range(60):
    t1=F(random.randint(-30,30),7); t2=F(random.randint(-30,30),7); t3=F(random.randint(-30,30),7)
    s1=F(random.randint(-30,30),7); s2=F(random.randint(-30,30),7)
    vals=[t1,t2,t3,1-t1-t2-t3,s1,s2,1-s1-s2]
    rhs=F(0)
    for k,c in cert.items():
        term=F(c)
        for i in range(7):
            if k[i]: term*=vals[i]**k[i]
        rhs+=term
    lhs=kerQ(t1,t1+t2,t1+t2+t3,s1+s2,s1)
    if lhs!=rhs: bad+=1
print(f"exact identity at 60 UNCONSTRAINED rational points: mismatches = {bad}")
print("=> the Lean `ring` goal is a true polynomial identity" if bad==0 else "IDENTITY WRONG")
