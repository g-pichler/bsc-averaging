import numpy as np, time, pickle, os
from collections import defaultdict
from math import comb
from scipy.sparse import coo_matrix
from scipy.optimize import linprog
SC=os.path.dirname(os.path.abspath(__file__))
target=pickle.load(open(SC+'/Qh.pkl','rb'))
def elevate(tgt,k):          # multiply by (c+d+v)^k
    out=defaultdict(float)
    for m,cf in tgt.items():
        for i in range(k+1):
            for j in range(k+1-i):
                l=k-i-j
                out[(m[0],m[1],m[2],m[3]+i,m[4]+j,m[5]+l)]+=cf*comb(k,i)*comb(k-i,j)
    return dict(out)
def run(D,k):
    tt=time.time(); tgt=elevate(target,k); sdeg=12+k
    smons=[(i,j,sdeg-i-j) for i in range(sdeg+1) for j in range(sdeg+1-i)]
    bern=[[(p, comb(D-kk,p-kk)*(-1)**(p-kk)) for p in range(kk,D+1)] for kk in range(D+1)]
    keys=[(k1,k2,k3,si) for k1 in range(D+1) for k2 in range(k1,D+1) for k3 in range(D+1)
          for si in range(len(smons))]
    rows=[];cols=[];vals=[]
    for n,(k1,k2,k3,si) in enumerate(keys):
        sm=smons[si]; loc=defaultdict(float)
        combos=[(k1,k2,k3)] if k1==k2 else [(k1,k2,k3),(k2,k1,k3)]
        for (K1,K2,K3) in combos:
            for (i,j,kk) in [(0,1,2),(0,2,1),(1,2,0)]:
                KK=[0,0,0]; KK[i]=K1; KK[j]=K2; KK[kk]=K3
                for (p1,c1) in bern[KK[0]]:
                    for (p2,c2) in bern[KK[1]]:
                        for (p3,c3) in bern[KK[2]]:
                            base=c1*c2*c3
                            for (di,dj,cc) in [(2,0,1),(1,1,-2),(0,2,1)]:
                                e=[p1,p2,p3]; e[i]+=di; e[j]+=dj
                                loc[(e[0],e[1],e[2],sm[0],sm[1],sm[2])]+=base*cc
        for mon,co in loc.items():
            if co: rows.append(mon); cols.append(n); vals.append(co)
    allm=sorted(set(rows)|set(tgt)); mi={m:r for r,m in enumerate(allm)}
    Am=coo_matrix((vals,([mi[m] for m in rows],cols)),shape=(len(allm),len(keys))).tocsr()
    bv=np.zeros(len(allm))
    for m,cf in tgt.items(): bv[mi[m]]=cf
    res=linprog(np.zeros(len(keys)),A_eq=Am,b_eq=bv,bounds=[(0,None)]*len(keys),method='highs')
    ok=res.status==0
    print(f"   D={D} k={k}: {Am.shape[0]}x{Am.shape[1]} nnz={Am.nnz}  "
          f"{'FEASIBLE' if ok else 'infeasible'}  [{time.time()-tt:.0f}s]")
    if ok:
        x=res.x; print(f"      nonzeros {(x>1e-11).sum()}/{len(x)}, max {x.max():.4g}")
        np.save(SC+f'/cert_D{D}_k{k}.npy',x)
    return ok
for (D,k) in [(4,1),(4,2),(5,2),(4,4),(5,4),(4,6)]:
    if run(D,k): break
