import random
def kern(th, u, v):
    t = u*v
    f = lambda x: (1-x)/(1-x*u)
    g = lambda x: (1-x)/(1-x*t)
    r = lambda x: (1-x*u)/(1-x*v)
    a,b,c = th
    return (f(a)*(g(b)+g(c))*(r(a)**2 - r(b)*r(c))
          + f(b)*(g(a)+g(c))*(r(b)**2 - r(a)*r(c))
          + f(c)*(g(a)+g(b))*(r(c)**2 - r(a)*r(b)))
rng = random.Random(0)
h = 1e-6
sgn_u = {'+':0,'-':0,'0':0}; sgn_v = dict(sgn_u); neg=0; worst=(1e9,None)
for _ in range(200000):
    th = tuple(sorted(rng.uniform(1e-3, 1-1e-3) for _ in range(3)))
    v = rng.uniform(1e-3, 1-1e-3); u = rng.uniform(v, 1-1e-9)
    k = kern(th,u,v)
    if k < worst[0]: worst = (k,(th,u,v))
    if k < -1e-12: neg += 1
    if u+h < 1:
        du = (kern(th,u+h,v) - kern(th,u-h,v))/(2*h)
        sgn_u['+' if du > 1e-9 else '-' if du < -1e-9 else '0'] += 1
    dv = (kern(th,u,min(v+h,u)) - kern(th,u,v-h))/(2*h)
    sgn_v['+' if dv > 1e-9 else '-' if dv < -1e-9 else '0'] += 1
print("kernel negatives:", neg, " min value: %.3e" % worst[0])
print("d/du signs:", sgn_u)
print("d/dv signs:", sgn_v)
