import BSCAveraging.SaddleIII
import BSCAveraging.LogCosh

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



/-! ### The saddle criterion

`F_uv²/(F_uu F_vv) > 1` at the symmetric point is, in the `g`-language,

```
(1 − g(x))²·g(α)g(β)  >  x²·(g(x)−g(α))(g(x)−g(β)) ,      x = αβ,
```

which is `saddle_iii`.  Both sides are positive because `g` is strictly
decreasing and `x < α, β`. -/



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

/-- Mixed second derivative of the value along the two rate-constant curves. -/
noncomputable def Fpq (s t : ℝ) : ℝ :=
  Real.artanh (s * t) / (s * t) - 1 / (1 - (s * t) ^ 2)

/-- Pure second derivative in the `U`-side parameter. -/
noncomputable def Fpp (s t : ℝ) : ℝ :=
  t ^ 2 / (1 - (s * t) ^ 2) - t * Real.artanh (s * t) / (Real.artanh s * (1 - s ^ 2))

/-- Pure second derivative in the `V`-side parameter. -/
noncomputable def Fqq (s t : ℝ) : ℝ :=
  s ^ 2 / (1 - (s * t) ^ 2) - s * Real.artanh (s * t) / (Real.artanh t * (1 - t ^ 2))

lemma artanh_eq_gFun {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    Real.artanh y = y * gFun y / (1 - y ^ 2) := by
  have h1 : (1:ℝ) - y ^ 2 ≠ 0 := by nlinarith
  rw [gFun]; field_simp

lemma Fpq_eq {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    Fpq s t = -(1 - gFun (s * t)) / (1 - (s * t) ^ 2) := by
  have hx0 : 0 < s * t := mul_pos hs0 ht0
  have hx1 : s * t < 1 := by nlinarith
  have hd : (1:ℝ) - (s * t) ^ 2 ≠ 0 := by nlinarith
  rw [Fpq, artanh_eq_gFun hx0 hx1]
  field_simp
  ring

lemma Fpp_eq {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    Fpp s t = -(t ^ 2 * (gFun (s * t) / gFun s - 1)) / (1 - (s * t) ^ 2) := by
  have hx0 : 0 < s * t := mul_pos hs0 ht0
  have hx1 : s * t < 1 := by nlinarith
  have hd : (1:ℝ) - (s * t) ^ 2 ≠ 0 := by nlinarith
  have hs2 : (1:ℝ) - s ^ 2 ≠ 0 := by nlinarith
  have hgs : gFun s ≠ 0 := ne_of_gt (gFun_pos hs0 hs1)
  rw [Fpp, artanh_eq_gFun hx0 hx1, artanh_eq_gFun hs0 hs1]
  field_simp
  ring

lemma Fqq_eq {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    Fqq s t = -(s ^ 2 * (gFun (s * t) / gFun t - 1)) / (1 - (s * t) ^ 2) := by
  have hx0 : 0 < s * t := mul_pos hs0 ht0
  have hx1 : s * t < 1 := by nlinarith
  have hd : (1:ℝ) - (s * t) ^ 2 ≠ 0 := by nlinarith
  have ht2 : (1:ℝ) - t ^ 2 ≠ 0 := by nlinarith
  have hgt : gFun t ≠ 0 := ne_of_gt (gFun_pos ht0 ht1)
  rw [Fqq, artanh_eq_gFun hx0 hx1, artanh_eq_gFun ht0 ht1]
  field_simp
  ring

/-- Both pure second derivatives are strictly negative: each side is
individually optimal. -/
lemma Fpp_neg {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    Fpp s t < 0 := by
  have hx0 : 0 < s * t := mul_pos hs0 ht0
  have hx1 : s * t < 1 := by nlinarith
  have hxs : s * t < s := by nlinarith
  have hgs : 0 < gFun s := gFun_pos hs0 hs1
  have hgt : gFun s < gFun (s * t) :=
    gFun_strictAntiOn (Set.mem_Ioo.mpr ⟨hx0, hx1⟩) (Set.mem_Ioo.mpr ⟨hs0, hs1⟩) hxs
  have hd : (0:ℝ) < 1 - (s * t) ^ 2 := by nlinarith
  rw [Fpp_eq hs0 hs1 ht0 ht1]
  have hr : 1 < gFun (s * t) / gFun s := (one_lt_div hgs).mpr hgt
  apply div_neg_of_neg_of_pos _ hd
  have := mul_pos (pow_pos ht0 2) (sub_pos.mpr hr)
  linarith

lemma Fqq_neg {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    Fqq s t < 0 := by
  have hx0 : 0 < s * t := mul_pos hs0 ht0
  have hx1 : s * t < 1 := by nlinarith
  have hxt : s * t < t := by nlinarith
  have hgt0 : 0 < gFun t := gFun_pos ht0 ht1
  have hgt : gFun t < gFun (s * t) :=
    gFun_strictAntiOn (Set.mem_Ioo.mpr ⟨hx0, hx1⟩) (Set.mem_Ioo.mpr ⟨ht0, ht1⟩) hxt
  have hd : (0:ℝ) < 1 - (s * t) ^ 2 := by nlinarith
  rw [Fqq_eq hs0 hs1 ht0 ht1]
  have hr : 1 < gFun (s * t) / gFun t := (one_lt_div hgt0).mpr hgt
  apply div_neg_of_neg_of_pos _ hd
  have := mul_pos (pow_pos hs0 2) (sub_pos.mpr hr)
  linarith

/-- **The Hessian identification and the saddle property.**  At the symmetric
point the constrained Hessian is *indefinite*: `F_pq² > F_pp·F_qq`, with both
diagonal entries negative.  This is exactly `saddle_iii`. -/
theorem hessian_indefinite {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t)
    (ht1 : t < 1) : Fpp s t * Fqq s t < Fpq s t ^ 2 := by
  have hx0 : 0 < s * t := mul_pos hs0 ht0
  have hx1 : s * t < 1 := by nlinarith
  have hd : (0:ℝ) < 1 - (s * t) ^ 2 := by nlinarith
  have hgs : 0 < gFun s := gFun_pos hs0 hs1
  have hgt : 0 < gFun t := gFun_pos ht0 ht1
  rw [Fpp_eq hs0 hs1 ht0 ht1, Fqq_eq hs0 hs1 ht0 ht1, Fpq_eq hs0 hs1 ht0 ht1]
  rw [div_mul_div_comm, div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
  have h := saddle_iii hs0 hs1 ht0 ht1
  have hkey : (s * t) ^ 2 * ((gFun (s * t) / gFun s - 1) * (gFun (s * t) / gFun t - 1))
      < (1 - gFun (s * t)) ^ 2 := by
    rw [div_sub_one (ne_of_gt hgs), div_sub_one (ne_of_gt hgt), div_mul_div_comm,
      ← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith [h]
  have hpos : (0:ℝ) < (1 - (s * t) ^ 2) ^ 2 := by positivity
  nlinarith [mul_lt_mul_of_pos_right hkey hpos]

/-- The saddle direction, made explicit: the quadratic form is positive on
`(1, θ)` with `θ = −F_pq/F_qq`. -/
theorem saddle_direction {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t)
    (ht1 : t < 1) :
    0 < Fpp s t + 2 * (-(Fpq s t) / Fqq s t) * Fpq s t
      + (-(Fpq s t) / Fqq s t) ^ 2 * Fqq s t := by
  have hq := Fqq_neg hs0 hs1 ht0 ht1
  have hind := hessian_indefinite hs0 hs1 ht0 ht1
  have hqne : Fqq s t ≠ 0 := ne_of_lt hq
  have hval : Fpp s t + 2 * (-(Fpq s t) / Fqq s t) * Fpq s t
      + (-(Fpq s t) / Fqq s t) ^ 2 * Fqq s t
      = (Fpp s t * Fqq s t - Fpq s t ^ 2) / Fqq s t := by
    field_simp
    ring
  rw [hval]
  exact div_pos_of_neg_of_neg (by linarith) hq

end BSCAveraging.Core
