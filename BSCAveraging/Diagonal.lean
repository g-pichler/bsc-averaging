import BSCAveraging.CorePos
import Mathlib.Analysis.SpecialFunctions.Artanh

/-! # The diagonal case of the saddle inequality (iii)

`NOTES.md` §7f.  With `g y = (1−y²)·artanh y / y` the saddle inequality (iii) is

```
(1 − g(x))² > x²·(g(x)/g(α) − 1)(g(x)/g(β) − 1),      x = αβ,  α,β ∈ (0,1).
```

On the diagonal `α = β = y` it factors, after multiplying by the positive
`g(y)²`, as `diag · (positive)` with

```
diag  =  (1 − g(y²))·g(y) − y²·(g(y²) − g(y)) .
```

Writing `y = tanh θ` and `Z = cosh 2θ`, `S = sinh 2θ`, `L = log Z` one has the
*exact* identities

```
g(tanh θ) = 2θ/S,     g(tanh²θ) = 2ZL/S²,     tanh²θ = (Z−1)²/S²,
diag · S⁴ = 2 Z S · N(θ),     N(θ) = 2θ(Z−1)·L·F(θ)
```

with `F` the one-variable core of `CoreDeriv.lean`.  So the diagonal case is a
pure algebraic consequence of `core_pos`. -/

namespace BSCAveraging.Core

open Real

/-- `g y = (1 − y²)·artanh y / y`, the profile appearing in (iii). -/
noncomputable def gFun (y : ℝ) : ℝ := (1 - y ^ 2) * Real.artanh y / y

lemma sinh_two_pos {θ : ℝ} (hθ : 0 < θ) : 0 < Real.sinh (2 * θ) :=
  Real.sinh_pos_iff.mpr (by linarith)

lemma cosh_two_gt_one {θ : ℝ} (hθ : 0 < θ) : 1 < Real.cosh (2 * θ) := by
  have h := Real.cosh_sq (2 * θ)
  nlinarith [sinh_two_pos hθ, Real.cosh_pos (2 * θ)]

lemma sinh_two_sq {θ : ℝ} : Real.sinh (2 * θ) ^ 2 = Real.cosh (2 * θ) ^ 2 - 1 := by
  have := Real.cosh_sq_sub_sinh_sq (2 * θ); linarith

/-- `g(tanh θ) = 2θ / sinh 2θ`. -/
lemma gFun_tanh {θ : ℝ} (hθ : 0 < θ) :
    gFun (Real.tanh θ) = 2 * θ / Real.sinh (2 * θ) := by
  have hs : 0 < Real.sinh θ := Real.sinh_pos_iff.mpr hθ
  have hc : 0 < Real.cosh θ := Real.cosh_pos θ
  have ht : 0 < Real.tanh θ := by
    rw [Real.tanh_eq_sinh_div_cosh]; positivity
  have h1 : 1 - Real.tanh θ ^ 2 = 1 / Real.cosh θ ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq θ]
  rw [gFun, Real.artanh_tanh, h1, Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul]
  field_simp

/-- `artanh (tanh²θ) = ½ log (cosh 2θ)`. -/
lemma artanh_tanh_sq (θ : ℝ) :
    Real.artanh (Real.tanh θ ^ 2) = Real.log (Real.cosh (2 * θ)) / 2 := by
  have hc : 0 < Real.cosh θ := Real.cosh_pos θ
  have htlt : Real.tanh θ ^ 2 < 1 := by
    have := Real.abs_tanh_lt_one θ
    nlinarith [abs_nonneg (Real.tanh θ), sq_abs (Real.tanh θ)]
  have hnn : (0:ℝ) ≤ Real.tanh θ ^ 2 := sq_nonneg _
  have hmem : Real.tanh θ ^ 2 ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, le_of_lt htlt⟩
  have h2 : Real.cosh (2 * θ) = Real.cosh θ ^ 2 + Real.sinh θ ^ 2 := by
    exact Real.cosh_two_mul θ
  have hne : 1 - Real.tanh θ ^ 2 ≠ 0 := by intro h; linarith
  have hratio : (1 + Real.tanh θ ^ 2) / (1 - Real.tanh θ ^ 2) = Real.cosh (2 * θ) := by
    rw [h2, div_eq_iff hne, Real.tanh_eq_sinh_div_cosh]
    have hpy := Real.cosh_sq_sub_sinh_sq θ
    field_simp
    linear_combination (-1 : ℝ) * hpy
  rw [Real.artanh_eq_half_log hmem, hratio]
  ring

/-- `g(tanh²θ) = 2·Z·log Z / S²` with `Z = cosh 2θ`, `S = sinh 2θ`. -/
lemma gFun_tanh_sq {θ : ℝ} (hθ : 0 < θ) :
    gFun (Real.tanh θ ^ 2)
      = 2 * Real.cosh (2 * θ) * Real.log (Real.cosh (2 * θ)) / Real.sinh (2 * θ) ^ 2 := by
  have hs : 0 < Real.sinh θ := Real.sinh_pos_iff.mpr hθ
  have hc : 0 < Real.cosh θ := Real.cosh_pos θ
  have hZ : Real.cosh (2 * θ) = Real.cosh θ ^ 2 + Real.sinh θ ^ 2 := by
    exact Real.cosh_two_mul θ
  have hS : Real.sinh (2 * θ) = 2 * Real.sinh θ * Real.cosh θ := Real.sinh_two_mul θ
  have ht : Real.tanh θ = Real.sinh θ / Real.cosh θ := Real.tanh_eq_sinh_div_cosh θ
  rw [gFun, artanh_tanh_sq, ht, hS, hZ]
  have hpyth := Real.cosh_sq_sub_sinh_sq θ
  field_simp
  linear_combination (Real.log (Real.cosh θ ^ 2 + Real.sinh θ ^ 2)
    * (Real.cosh θ ^ 2 + Real.sinh θ ^ 2)) * hpyth

/-- `tanh²θ = (Z−1)²/S²`. -/
lemma tanh_sq_eq {θ : ℝ} (hθ : 0 < θ) :
    Real.tanh θ ^ 2 = (Real.cosh (2 * θ) - 1) ^ 2 / Real.sinh (2 * θ) ^ 2 := by
  have hs : 0 < Real.sinh θ := Real.sinh_pos_iff.mpr hθ
  have hc : 0 < Real.cosh θ := Real.cosh_pos θ
  have hZ : Real.cosh (2 * θ) - 1 = 2 * Real.sinh θ ^ 2 := by
    rw [Real.cosh_two_mul]; linarith [Real.cosh_sq_sub_sinh_sq θ]
  rw [hZ, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- The cleared form of the core: `N(θ) = 2θ(Z−1)·log Z·F(θ)`. -/
noncomputable def Ncore (θ : ℝ) : ℝ :=
  2 * θ * (Real.cosh (2 * θ) - 1) - 2 * θ * Real.log (Real.cosh (2 * θ))
    - Real.tanh θ * Real.log (Real.cosh (2 * θ)) * (Real.cosh (2 * θ) - 1)

lemma Ncore_pos {θ : ℝ} (hθ : 0 < θ) : 0 < Ncore θ := by
  have hZ1 : 1 < Real.cosh (2 * θ) := cosh_two_gt_one hθ
  have hL : 0 < Real.log (Real.cosh (2 * θ)) := Real.log_pos hZ1
  have hF := core_pos hθ
  rw [F_eq hθ] at hF
  have hid : Ncore θ
      = 2 * θ * (Real.cosh (2 * θ) - 1) * Real.log (Real.cosh (2 * θ))
        * (1 / Real.log (Real.cosh (2 * θ)) - 1 / (Real.cosh (2 * θ) - 1)
            - Real.tanh θ / (2 * θ)) := by
    have h1 : Real.log (Real.cosh (2 * θ)) ≠ 0 := ne_of_gt hL
    have h2 : Real.cosh (2 * θ) - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
    have h3 : (2 : ℝ) * θ ≠ 0 := by positivity
    rw [Ncore]
    field_simp
  rw [hid]
  have : (0:ℝ) < 2 * θ * (Real.cosh (2 * θ) - 1) * Real.log (Real.cosh (2 * θ)) := by
    have : (0:ℝ) < Real.cosh (2 * θ) - 1 := by linarith
    positivity
  exact mul_pos this hF

/-- **The diagonal case of (iii)**: for `y = tanh θ`, `θ > 0`,

```
(1 − g(y²))·g(y) − y²·(g(y²) − g(y))  >  0 .
```
-/
theorem diag_pos {θ : ℝ} (hθ : 0 < θ) :
    0 < (1 - gFun (Real.tanh θ ^ 2)) * gFun (Real.tanh θ)
        - Real.tanh θ ^ 2 * (gFun (Real.tanh θ ^ 2) - gFun (Real.tanh θ)) := by
  set Z := Real.cosh (2 * θ) with hZdef
  set S := Real.sinh (2 * θ) with hSdef
  set L := Real.log Z with hLdef
  have hSpos : 0 < S := sinh_two_pos hθ
  have hZ1 : 1 < Z := cosh_two_gt_one hθ
  have hS2 : S ^ 2 = Z ^ 2 - 1 := sinh_two_sq
  rw [gFun_tanh hθ, gFun_tanh_sq hθ, tanh_sq_eq hθ]
  -- the cleared identity: `diag · S⁴ = 2 Z S · N(θ)`
  have hkey : ((1 - 2 * Z * L / S ^ 2) * (2 * θ / S)
        - (Z - 1) ^ 2 / S ^ 2 * (2 * Z * L / S ^ 2 - 2 * θ / S)) * S ^ 4
      = 2 * Z * S * (2 * θ * (Z - 1) - 2 * θ * L - ((Z - 1) / S) * L * (Z - 1)) := by
    field_simp
    linear_combination (S * θ) * hS2
  have hN : 0 < 2 * θ * (Z - 1) - 2 * θ * L - ((Z - 1) / S) * L * (Z - 1) := by
    have hNc := Ncore_pos hθ
    rw [Ncore] at hNc
    have htanh : Real.tanh θ = (Z - 1) / S := by
      have hs : 0 < Real.sinh θ := Real.sinh_pos_iff.mpr hθ
      have hc : 0 < Real.cosh θ := Real.cosh_pos θ
      have h1 : Z - 1 = 2 * Real.sinh θ ^ 2 := by
        rw [hZdef, Real.cosh_two_mul]; linarith [Real.cosh_sq_sub_sinh_sq θ]
      rw [h1, hSdef, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
      field_simp
    rw [htanh] at hNc
    convert hNc using 2 <;> ring
  have hS4 : (0:ℝ) < S ^ 4 := by positivity
  nlinarith [hkey, mul_pos (mul_pos (by positivity : (0:ℝ) < 2 * Z) hSpos) hN, hS4]

end BSCAveraging.Core
