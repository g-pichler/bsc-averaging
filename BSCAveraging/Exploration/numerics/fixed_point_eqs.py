"""The alternating-maximization fixed-point system in (m,k,c,d) (NOTES.md sec.6).

A global maximizer is a fixed point, so we may add the stationarity equations to
route 1.  With L = artanh, v0,v1 = m +- k the biases of U given X (weights 1/2),
b1 = m + k*delta*c, b2 = m - k*delta*d those given V (weights w_c, w_d),
kappa = cd/(c+d):

  (E1)  mu*(L(v0)+L(v1))/2 + (1-mu)*L(m) = w_c*L(b1) + w_d*L(b2)      [U-side, d/dm]
  (E2)  mu*(L(v0)-L(v1))/2 = delta*kappa*(L(b1) - L(b2))              [U-side, d/dk]
  (E3)  k*delta*(L(b1)-L(b2)) = nu*(L(c)+L(d))                        [V-side, slopes]
  (E4)  Psi(b1)-Psi(b2) - nu*(Psi(c)-Psi(d))
            = (c+d)*(k*delta*L(b1) - nu*L(c))                         [V-side, chord]

(E1) and (E3) are linear in mu and nu, so both eliminate:
  mu = (L_V - L(m)) / (L_X - L(m)),  L_X = (L(v0)+L(v1))/2, L_V = w_c L(b1)+w_d L(b2)
  nu = k*delta*(L(b1)-L(b2)) / (L(c)+L(d)).

Checked here against fixed points produced by alternating maximization in the
bias coordinates of global_rigidity.py, converting via
  m = (b-a)/(a+b),  k = 2ab/(a+b)   for S = {a, -b}.
"""
import numpy as np
import global_rigidity as G

at = np.arctanh


def Psi(y):
    y = np.clip(np.abs(y), 0.0, 1 - 1e-16)
    return 0.5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


def residuals(m, k, c, d, mu, nu, delta):
    v0, v1 = m + k, m - k
    b1, b2 = m + k * delta * c, m - k * delta * d
    wc, wd = d / (c + d), c / (c + d)
    kap = c * d / (c + d)
    LX = 0.5 * (at(v0) + at(v1))
    LV = wc * at(b1) + wd * at(b2)
    e1 = mu * LX + (1 - mu) * at(m) - LV
    e2 = mu * 0.5 * (at(v0) - at(v1)) - delta * kap * (at(b1) - at(b2))
    e3 = k * delta * (at(b1) - at(b2)) - nu * (at(c) + at(d))
    e4 = (Psi(b1) - Psi(b2) - nu * (Psi(c) - Psi(d))
          - (c + d) * (k * delta * at(b1) - nu * at(c)))
    mu_rec = (LV - at(m)) / (LX - at(m)) if abs(LX - at(m)) > 1e-12 else np.nan
    nu_rec = k * delta * (at(b1) - at(b2)) / (at(c) + at(d))
    return e1, e2, e3, e4, mu_rec, nu_rec


if __name__ == "__main__":
    rng = np.random.default_rng(13579)
    rows, tried = [], 0
    while len(rows) < 12 and tried < 400:
        tried += 1
        delta = rng.uniform(0.3, 0.99)
        mu, nu = rng.uniform(0.05, 0.7, 2)
        st = np.tanh(rng.uniform(0.05, 8.0, size=4))
        hist, fin = G.alternate(mu, nu, delta, st, iters=60)
        if hist[-1, 2] <= 1e-6:
            continue
        a, b, c, d = fin
        m, k = (b - a) / (a + b), 2 * a * b / (a + b)
        e1, e2, e3, e4, mur, nur = residuals(m, k, c, d, mu, nu, delta)
        rows.append((delta, mu, nu, m, k, max(abs(e1), abs(e2), abs(e3), abs(e4)),
                     abs(mur - mu), abs(nur - nu), hist[-1, 2]))
    print(f"{'delta':>6} {'mu':>6} {'nu':>6} {'m':>10} {'k':>8} "
          f"{'max|E|':>9} {'|mu_rec-mu|':>11} {'|nu_rec-nu|':>11} {'F':>9}")
    for r in rows:
        print(f"{r[0]:6.3f} {r[1]:6.3f} {r[2]:6.3f} {r[3]:10.2e} {r[4]:8.4f} "
              f"{r[5]:9.2e} {r[6]:11.2e} {r[7]:11.2e} {r[8]:9.5f}")
