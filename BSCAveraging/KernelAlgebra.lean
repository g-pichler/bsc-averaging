import Mathlib.Analysis.Complex.ExponentialBounds
import BSCAveraging.PZero
/-! # The Z/S branch value at `p = 0`

`NOTES.md` §7f reduces Conjecture 1 at `p = 0` to the *kernel lemma*, an explicit
rational inequality in five variables.  What that reduction needs from this file
is one definition: `zsValue`, the value of the Z/S branch as a function of the
two Z-parameters.  Its companion `zsRate` is in `Definitions.lean`, beside
`dsbs`.

The section headings below track `Exploration/KernelAlgebra.lean`, so that the
two read in parallel.  That file, which no part of the proof imports, is where
the analysis of the reduction lives: the boundary case of (iii) (`artanh_edge`),
the Schur-type decomposition (`schur_decomposition`), its equal-weight case
(`cube_sum_ge_three_mul`), the difference identities carrying an explicit factor
`(θ_l − θ_i)` (`rFun_sub`, `fFun'_sub`, `fg_cross`), and the vanishing of the
kernel on the face `u = 1`.

The kernel lemma is not open: it is proved by the Pólya certificate of
`KernelCertFast.lean` (`kerQ_nonneg_reflect`), checked in the kernel by
Kronecker substitution (`KernelKron.lean`) — no axiom beyond the standard three.

See `NOTES.md` §7f. -/

open Real Set

namespace BSCAveraging

/-! ## The boundary case of (iii) -/



/-! ## The Schur-type decomposition -/



/-! ## The difference identities

Every difference appearing in the kernel lemma carries an explicit factor
`(θ_l − θ_i)`; this is why the kernel is divisible by `(θ_i − θ_l)²`. -/

section Differences

variable {θ₁ θ₂ u v : ℝ}




end Differences


/-! ## Why the mixture route, and why no general argument can work -/

section GeometricDegeneracy

variable {θ u v : ℝ}


end GeometricDegeneracy



/-! ## The other route: the branch comparison at `p = 0`

Conjecture 1 can also be closed by comparing the two branches directly:
`V_Z(C_u,C_v) > V_B(C_u,C_v)`, where `V_B = f_e(αβ)` is the BSC value and

```
V_Z(a,d) = (d/(1+d))·log(1+a) + ((1−ad)/((1+a)(1+d)))·log(1−ad) + (a/(1+a))·log(1+d)
```

is the Z/S value, the rates being `f_e(α) = C_u` and `(f_e(a) + a·log 2)/(1+a) = C_u`.
Unlike (iii) this comparison has a **uniform** relative margin (≈ 4 % at small
rates, measured), but it is irreducibly two-sided: against a fixed BSC the
S-channel *loses* to the BSC, by Mrs. Gerber's Lemma (`mgl_jensen`), so no
one-side-at-a-time chain reaches it.

Its small-rate limit is the constant below: `α ≈ √(2C)` gives `V_B ≈ 2C_uC_v`
while `a ≈ C/log 2` gives `V_Z ≈ C_uC_v/log²2`, so the ratio tends to
`1/(2log²2) = 1.0407… > 1`. -/

/-- The Z/S branch value at `p = 0`, as a function of the two Z-parameters. -/
noncomputable def zsValue (a d : ℝ) : ℝ :=
  d / (1 + d) * log (1 + a) + (1 - a * d) / ((1 + a) * (1 + d)) * log (1 - a * d)
    + a / (1 + a) * log (1 + d)



/-! ## Comonotone Schur: the two halves of the kernel lemma that *are* theorems

Write `S φ = Σ_i φ(θ_i)·(r_i² − r_j r_k)` and `G = g θ₁ + g θ₂ + g θ₃`.  Since
the kernel weight is `λ_i = f(θ_i)·(G − g(θ_i))`,

```
Σ_i λ_i (r_i² − r_j r_k)  =  G · S f  −  S (f·g) .
```

Both halves are nonnegative, and for a *structural* reason: `f`, `g`, hence
`f·g`, and `r` are all **decreasing** in `θ`, and a Schur sum whose weights are
comonotone with `r` is nonnegative (`kernel_nonneg_of_comonotone`, from
`schur_decomposition`: the Chebyshev bracket is then termwise nonnegative).

So the kernel lemma is exactly the *ratio* bound `S (f·g) ≤ G · S f` between two
quantities already known to be nonnegative.  Equivalently, by

```
λ_i − λ_l = g_m·(f_i − f_l)  +  f_i f_l·(φ_l − φ_i),     φ = g/f = (1−θu)/(1−θuv)
```

(`lambda_sub`), the only obstruction to comonotonicity of `λ` itself — and hence
the only negative contribution anywhere — is the second term, `φ` being
decreasing.  Numerically all three summands of `G` are needed: `S (f·g) ≤ g_max·S f`
fails on 97% of samples and `(g_max+g_mid)·S f` still fails on 31%. -/

section Comonotone

variable {θ₁ θ₂ θ₃ u v : ℝ}






end Comonotone

/-! ### The two halves, for the actual `f`, `g`, `r` -/

section Halves

variable {θ₁ θ₂ θ₃ u v : ℝ}




end Halves


/-! ### The degenerate face `u = 1`

At `u = 1` one has `a_i = 1−θ_i = A_i`, hence `f ≡ 1`, `w_i = b_i`, `g_i = r_i`,
and the kernel **vanishes identically**: the whole
face `u = 1` is a zero of the kernel lemma.  That is why every global
certificate attempt saw a vanishing margin, and why the corner analysis of §7f′
found an exact leading-order cancellation — the corner merely sits on this face.

So on the face the first non-trivial datum is the derivative in `c = 1 − u`.
Writing `s_i = θ_i/b_i`, the face relation is `r_i + (1−v)·s_i = 1` — the two
coordinates are affinely dependent — so `s_i = (1−r_i)/κ` with `κ = 1−v`, and a
CAS computation (`numerics/p0_kernel_face.py`) gives

```
κ·r₁r₂r₃ · ∂(kernel)/∂c  at  c = 0   =   κ · faceX(r)  +  faceY(r) ,   r_i ∈ (0,1).
```

Both coefficients are nonnegative on the cube — `faceX` outright, `faceY` after
ordering — so the kernel enters the region `u < 1` with a nonnegative slope
across the whole face.  `faceY` is negative off the cube (e.g. on `(0,3)³`), so
the box constraints are essential; the certificate is the Pólya one in the
ordered simplex coordinates `w = r₃`, `q = r₂−r₃`, `p = r₁−r₂`, `m = 1−r₁`,
where `faceY` has **53 monomials, all with positive integer coefficients** and
no degree elevation is needed.

The differentiation itself is done by CAS, not in Lean; what is formalised here
is the algebra it produces — the face identity and the two positivity
statements. -/

section Face







end Face

/-! ## The remaining open inequality -/


end BSCAveraging
