from fractions import Fraction as Fr
N=12
c=[Fr(0)]+[Fr(2,4*k*k-1) for k in range(1,N+2)]
def Z(): return [[Fr(0)]*(N+1) for _ in range(N+1)]
def mul(A,B):
    C=Z()
    for i in range(N+1):
        for j in range(N+1):
            a=A[i][j]
            if a==0: continue
            for k in range(N+1-i):
                for l in range(N+1-j):
                    b=B[k][l]
                    if b: C[i+k][j+l]+=a*b
    return C
def add(A,B,s=1):
    C=Z()
    for i in range(N+1):
        for j in range(N+1): C[i][j]=A[i][j]+s*B[i][j]
    return C
one=Z(); one[0][0]=Fr(1)
Gu=Z(); Gv=Z(); Guv=Z(); uGpu=Z(); vGpv=Z()
for k in range(1,N+1):
    Gu[k][0]=c[k]; Gv[0][k]=c[k]; Guv[k][k]=c[k]
    uGpu[k][0]=c[k]*k; vGpv[0][k]=c[k]*k        # z G'(z) = sum k c_k z^k
R=add(mul(vGpv,mul(add(one,Gu,-1),add(Gu,Guv,-1))),
      mul(uGpu,mul(add(one,Gv,-1),add(Gv,Guv,-1))),-1)
# divide by (u - v):  R = (u-v) S  with S symmetric
Ssym=Z()
for d in range(N,-1,-1):      # do polynomial division in u
    pass
# direct division: treat R as poly in u with coefficients polys in v
import copy
Rw=copy.deepcopy(R); Sq=Z()
for i in range(N,0,-1):
    for j in range(N+1):
        a=Rw[i][j]
        if a==0: continue
        Sq[i-1][j]+=a            # quotient term a*u^{i-1} v^j
        Rw[i][j]-=a              # subtract a*u^i v^j
        if j+1<=N: Rw[i-1][j+1]+=a   # ... minus a*u^{i-1} v^{j+1}
rem=sum(1 for i in range(N+1) for j in range(N+1) if Rw[i][j]!=0)
neg=[(i,j,Sq[i][j]) for i in range(N+1) for j in range(N+1) if Sq[i][j]<0]
pos=sum(1 for i in range(N+1) for j in range(N+1) if Sq[i][j]>0)
print(f"R = (u-v)*S  : remainder terms {rem}  (0 expected up to truncation edge)")
print(f"S coefficients: {pos} positive, {len(neg)} negative")
if neg: print("  negatives:", neg[:10])
print("\nlow-order block of S (rows u^i, cols v^j, i,j<=5):")
for i in range(6):
    print("  "+" ".join(f"{float(Sq[i][j]):+9.5f}" for j in range(6)))
