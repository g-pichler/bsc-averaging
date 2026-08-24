"""Check of the conditional-MI reformulation (NOTES.md sec.5h).

Because U -- X -- (Y,V) is Markov, I(U;X,V) = I(U;X), hence
I(U;V) = I(U;X) - I(U;X|V) and

    F = (1-mu) I(U;X) - I(U;X|V) - nu I(Y;V).

Given V = v the input X has bias delta*t_v and the channel P(u|x) is unchanged,
so I(U;X|V) = E_T[C(delta*T)] where C(beta) := I(Bern((1+beta)/2), W) is the
channel's MI-vs-input-bias curve.  For a binary channel whose conditional biases
are v0 (given x=0) and v1 (given x=1),

    C(beta) = A + B*beta - Psi(m + k*beta),
    A = (Psi(v0)+Psi(v1))/2,  B = (Psi(v0)-Psi(v1))/2,
    m = (v0+v1)/2,            k = (v0-v1)/2.

B multiplies E[T] = 0, so it drops out, leaving

    F_opt(v0,v1) = -mu*A - (1-mu)*Psi(m) + conc(zeta)(0),
    zeta(y) = Psi(m + k*delta*y) - nu*Psi(y),

with conc(.)(0) the concave envelope at 0 (= sup over mean-zero T of E zeta(T)).
Symmetry is m = 0, i.e. v1 = -v0.

The old bias parametrization has S = bias of X given U, which by Bayes is
    S = {k/(1+m) w.p. (1+m)/2,  -k/(1-m) w.p. (1-m)/2}.

Tests
  1  C(beta) against a direct mutual-information computation
  2  F_opt(v0,v1) against  max over mean-zero T of the old  E f(delta S T) - mu E Psi(S) - nu E Psi(T)
  3  mu >= 1 (or nu >= 1) forces F <= 0
"""
import numpy as np

CO = 8.0
NG = 700


def Psi(y):
    y = np.clip(np.abs(y), 0.0, 1 - 1e-16)
    return 0.5 * ((1 + y) * np.log1p(y) + (1 - y) * np.log1p(-y))


def fz(z):
    return (1 + z) * np.log1p(z)


_pos = np.tanh(np.linspace(1e-4, CO, NG))
_grid = np.concatenate([-_pos[::-1], _pos])
_A2, _B2 = _pos[:, None], _pos[None, :]


def mi_direct(v0, v1, beta):
    """I(U;X) for X ~ bias beta and channel with conditional biases v0, v1."""
    px = np.array([(1 + beta) / 2, (1 - beta) / 2])
    W = np.array([[(1 + v0) / 2, (1 - v0) / 2], [(1 + v1) / 2, (1 - v1) / 2]])
    J = px[:, None] * W
    pu = J.sum(axis=0)
    out = 0.0
    for i in range(2):
        for j in range(2):
            if J[i, j] > 0:
                out += J[i, j] * np.log(J[i, j] / (px[i] * pu[j]))
    return out


def C(v0, v1, beta):
    A = (Psi(v0) + Psi(v1)) / 2
    B = (Psi(v0) - Psi(v1)) / 2
    m, k = (v0 + v1) / 2, (v0 - v1) / 2
    return A + B * beta - Psi(m + k * beta)


def conc_at_zero(vals):
    """Concave envelope at 0 of the samples (_grid, vals), via the exact
    two-atom maximum  max over y- < 0 < y+ of the chord value at 0."""
    n = NG
    neg = vals[:n][::-1]          # value at -_pos
    pos = vals[n:]                # value at +_pos
    V = (_B2 * pos[:, None] + _A2 * neg[None, :]) / (_A2 + _B2)
    return float(V.max())


def F_new(v0, v1, mu, nu, delta):
    m, k = (v0 + v1) / 2, (v0 - v1) / 2
    A = (Psi(v0) + Psi(v1)) / 2
    zeta = Psi(m + k * delta * _grid) - nu * Psi(_grid)
    return -mu * A - (1 - mu) * Psi(m) + conc_at_zero(zeta)


def F_old(v0, v1, mu, nu, delta):
    """Same quantity in the bias parametrization: S from Bayes, T optimized."""
    m, k = (v0 + v1) / 2, (v0 - v1) / 2
    if abs(1 - m) < 1e-14 or abs(1 + m) < 1e-14:
        return np.nan
    S = np.array([k / (1 + m), -k / (1 - m)])
    P = np.array([(1 + m) / 2, (1 - m) / 2])
    G = (fz(delta * np.outer(_grid, S)) * P[None, :]).sum(axis=1) - nu * Psi(_grid)
    return conc_at_zero(G) - mu * float(P @ Psi(S))


if __name__ == "__main__":
    rng = np.random.default_rng(20260807)

    e1 = 0.0
    for _ in range(600):
        v0, v1 = rng.uniform(-1, 1, 2)
        beta = rng.uniform(-1, 1)
        e1 = max(e1, abs(C(v0, v1, beta) - mi_direct(v0, v1, beta)))
    print(f"[1] max |C(beta) - direct MI|            {e1:.3e}")

    e2, at = 0.0, None
    for _ in range(400):
        v0, v1 = rng.uniform(-0.999, 0.999, 2)
        mu, nu = rng.uniform(0, 1, 2)
        delta = rng.uniform(0.02, 0.999)
        a, b = F_new(v0, v1, mu, nu, delta), F_old(v0, v1, mu, nu, delta)
        if np.isfinite(b) and abs(a - b) > e2:
            e2, at = abs(a - b), (v0, v1, mu, nu, delta, a, b)
    print(f"[2] max |F_new - F_old|                  {e2:.3e}")
    print(f"    at {at}")

    worst = -np.inf
    for _ in range(600):
        v0, v1 = rng.uniform(-0.999, 0.999, 2)
        mu = rng.uniform(1.0, 3.0)
        nu = rng.uniform(0, 3)
        delta = rng.uniform(0.02, 0.999)
        worst = max(worst, F_new(v0, v1, mu, nu, delta))
    print(f"[3] max F over mu >= 1                   {worst:.3e}   (<= 0 required)")
