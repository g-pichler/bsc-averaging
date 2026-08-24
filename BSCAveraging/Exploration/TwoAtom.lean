import BSCAveraging.TwoAtom
import BSCAveraging.Exploration.LogCosh

/-! # `TwoAtom` — exploration companion

The declarations of `BSCAveraging.TwoAtom` that are **not** used by any of the
three theorems of `BSCAveraging.Basic`.  Section headers are copied from the
main file so the two read in parallel. -/

/-! # Two-atom laws in `θ` coordinates, and the saddle criterion

`NOTES.md` §7e.  At `p = 0` the value is **bilinear** in the two side-laws:
with `μ` supported on the biases `s_u` with weights `π_u`,

```
I(U;V) = Σ_{u,v} π_u ρ_v · f(s_u t_v) ,     f(z) = (1+z)log(1+z),
```

linear in `(π,s)` and in `(ρ,t)` separately.  Both feasible sets are convex
(mass one, mean zero, `∫f_e ≤ C` are all linear in the law).  Consequently

```
V(μ*+d_U, ν*+d_V) − V(μ*,ν*) = A_U + A_V + Q(d_U,d_V)
```

is an *exact identity*, not a Taylor expansion: `A_U`, `A_V` are one-sided and
`Q` is the bilinear cross term.  That is what makes the second-order test for
`(C)` a computation on one-sided objects only.

For a two-atom mean-zero law with atoms `tanh α, −tanh β` the weights are forced,
`π₁ = sinh β cosh α / sinh(α+β)`, `π₂ = sinh α cosh β / sinh(α+β)`, and both the
rate and the value collapse to closed forms in `θ` coordinates (`Rtwo`, `Vtwo`
below; both verified against the direct definitions).

The saddle criterion of §7e — the Hessian slope product `F_uv²/(F_uu F_vv)`
exceeding `1` at the symmetric point — is **exactly the reciprocal** of the
(iii) ratio, so `saddle_iii` discharges it: `saddleRatio_gt_one`. -/

namespace BSCAveraging.Core

open Real BSCAveraging.LC

/-- The rate of the two-atom mean-zero law with atoms `tanh α, −tanh β`,
in `θ` coordinates: `Σ_u π_u f_e(s_u)`. -/
noncomputable def Rtwo (α β : ℝ) : ℝ :=
  (Real.sinh β * Real.cosh α * (α * Real.tanh α - LC α)
    + Real.sinh α * Real.cosh β * (β * Real.tanh β - LC β)) / Real.sinh (α + β)

/-- The value `I(U;V)` of the two-atom pair, in `θ` coordinates. -/
noncomputable def Vtwo (α β γ δ : ℝ) : ℝ :=
  (Real.sinh β * Real.sinh δ * Real.cosh (α + γ) * (LC (α + γ) - LC α - LC γ)
    + Real.sinh β * Real.sinh γ * Real.cosh (α - δ) * (LC (α - δ) - LC α - LC δ)
    + Real.sinh α * Real.sinh δ * Real.cosh (β - γ) * (LC (β - γ) - LC β - LC γ)
    + Real.sinh α * Real.sinh γ * Real.cosh (β + δ) * (LC (β + δ) - LC β - LC δ))
    / (Real.sinh (α + β) * Real.sinh (γ + δ))

/-! ### The saddle criterion

`F_uv²/(F_uu F_vv) > 1` at the symmetric point is, in the `g`-language,

```
(1 − g(x))²·g(α)g(β)  >  x²·(g(x)−g(α))(g(x)−g(β)) ,      x = αβ,
```

which is `saddle_iii`.  Both sides are positive because `g` is strictly
decreasing and `x < α, β`. -/

/-- The denominator of the criterion is strictly positive. -/
lemma criterion_den_pos {α β : ℝ} (ha0 : 0 < α) (ha1 : α < 1) (hb0 : 0 < β) (hb1 : β < 1) :
    0 < (α * β) ^ 2 * ((gFun (α * β) - gFun α) * (gFun (α * β) - gFun β)) := by
  have hx0 : 0 < α * β := mul_pos ha0 hb0
  have hx1 : α * β < 1 := by nlinarith
  have hxa : α * β < α := by nlinarith
  have hxb : α * β < β := by nlinarith
  have h1 : 0 < gFun (α * β) - gFun α := by
    have := gFun_strictAntiOn (Set.mem_Ioo.mpr ⟨hx0, hx1⟩) (Set.mem_Ioo.mpr ⟨ha0, ha1⟩) hxa
    linarith
  have h2 : 0 < gFun (α * β) - gFun β := by
    have := gFun_strictAntiOn (Set.mem_Ioo.mpr ⟨hx0, hx1⟩) (Set.mem_Ioo.mpr ⟨hb0, hb1⟩) hxb
    linarith
  positivity

/-- **The saddle criterion**, in the exact form the Hessian computation
consumes: the slope product exceeds `1`.  This is `saddle_iii` divided by the
(positive) denominator. -/
theorem saddleRatio_gt_one {α β : ℝ} (ha0 : 0 < α) (ha1 : α < 1) (hb0 : 0 < β)
    (hb1 : β < 1) :
    1 < (1 - gFun (α * β)) ^ 2 * (gFun α * gFun β)
      / ((α * β) ^ 2 * ((gFun (α * β) - gFun α) * (gFun (α * β) - gFun β))) := by
  have hden := criterion_den_pos ha0 ha1 hb0 hb1
  rw [lt_div_iff₀ hden, one_mul]
  have h := saddle_iii ha0 ha1 hb0 hb1
  linarith

/-! ### The constrained Hessian at the symmetric point

`NOTES.md` §7e′.  Bilinearity of the value makes the three second derivatives
along the rate-constant curves *one-sided* objects:

```
F_pp = ⟨φ_{ν₀}, μ″⟩ ,   F_qq = ⟨φ_{μ₀}, ν″⟩ ,   F_pq = (μ′⊗ν′)[f(xy)] .
```

At the symmetric point `μ₀ = ½(δ_s+δ_{−s})`, `ν₀ = ½(δ_t+δ_{−t})`, the field is
`φ_{ν₀}(x) = f_e(xt)`.  Bitangency (`λ₁ = 0` by symmetry) makes
`H(x) = f_e(xt) − λ₀ − λ₂f_e(x)` vanish to second order at `±s`, and since `μ″`
annihilates `1`, `id` and `f_e` only the `H″` term survives:

```
F_pp = Σ_i w_i (x_i′)² H″(x_i) = H″(s) = t²/(1−x²) − λ₂/(1−s²),
λ₂ = t·artanh x / artanh s ,   x = st .
```

For the mixed term, the tangent direction is `w₁′ = −1/(2s)`, `w₂′ = 1/(2s)`,
`x₁′ = x₂′ = 1` (both atoms translate — the skew of §7f⁷; the rate is
automatically stationary along it).  Pairing against `f` gives
`A(y) = ⟨f(·y), μ′⟩ = y − artanh(sy)/s`, whence
`F_pq = A′(t) − A(t)/t = artanh x/x − 1/(1−x²)`.

Rewritten through `g`, all three collapse, and the slope product is exactly the
reciprocal of the (iii) ratio. -/


end BSCAveraging.Core
