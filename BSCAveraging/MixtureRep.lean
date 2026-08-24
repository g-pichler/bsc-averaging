import BSCAveraging.Diagonal
import BSCAveraging.Rigidity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The geometric-mixture representation

`NOTES.md` §7f, step (ii)–(iii).  With `Ĝ(y²) = 1 − g(y)` the coefficients of
`Ĝ` are `c_k = 2/((2k−1)(2k+1)) = ∫₀¹ (1−θ)θ^{k−1}·dθ/(2√θ)`, so `Ĝ` is the
mixture of the geometric family over `θ = s²`, `s` uniform on `[0,1]`.  Written
out, for `α ∈ (0,1)`:

```
1 − g(α)  =  ∫₀¹ (1−s²)α²/(1−s²α²) ds                        (Ĝ)
    g(α)  =  ∫₀¹ (1−α²)/(1−s²α²) ds                          (B)
    A(α)  =  ∫₀¹ α²(1−s²)/(1−s²α²)² ds  =  ((1+α²)artanh α − α)/(2α)
```

`A(α²) = α²Ĝ′(α²) = −α·g′(α)/2` is the third linear functional entering the
kernel.  Every one of the three is an elementary antiderivative in `s`; nothing
here needs differentiation under the integral sign. -/

namespace BSCAveraging.Core

open Real MeasureTheory

variable {α : ℝ}

lemma sq_mul_sq_lt_one {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha0 : 0 < α) (ha1 : α < 1) :
    s ^ 2 * α ^ 2 < 1 := by
  have h1 : s ^ 2 ≤ 1 := by nlinarith
  have h2 : α ^ 2 < 1 := by nlinarith
  nlinarith [sq_nonneg s]

lemma one_sub_sq_ne {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha0 : 0 < α) (ha1 : α < 1) :
    (1 : ℝ) - s ^ 2 * α ^ 2 ≠ 0 := by
  have := sq_mul_sq_lt_one hs0 hs1 ha0 ha1; linarith

lemma hd_congr {f : ℝ → ℝ} {d d' x : ℝ} (h : HasDerivAt f d x) (he : d = d') :
    HasDerivAt f d' x := he ▸ h

/-- Derivative of `s ↦ artanh (s·α)`. -/
lemma hasDerivAt_artanh_mul {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha0 : 0 < α) (ha1 : α < 1) :
    HasDerivAt (fun r : ℝ => Real.artanh (r * α)) (α / (1 - s ^ 2 * α ^ 2)) s := by
  have hlt : s * α < 1 := by nlinarith
  have hgt : -1 < s * α := by nlinarith
  have hne : (1:ℝ) - s ^ 2 * α ^ 2 ≠ 0 := one_sub_sq_ne hs0 hs1 ha0 ha1
  have h := (hasDerivAt_artanh hgt hlt).comp s ((hasDerivAt_id s).mul_const α)
  rw [Function.comp_def] at h
  simp only [id_eq, one_mul] at h
  have he : (1:ℝ) / (1 - (s * α) ^ 2) * α = α / (1 - s ^ 2 * α ^ 2) := by
    rw [mul_pow]; field_simp
  rwa [he] at h

/-! ### `B`: the mixture form of `g` -/

/-- `g α = ∫₀¹ (1−α²)/(1−s²α²) ds`. -/
theorem gFun_eq_integral (ha0 : 0 < α) (ha1 : α < 1) :
    gFun α = ∫ s in (0:ℝ)..1, (1 - α ^ 2) / (1 - s ^ 2 * α ^ 2) := by
  have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => (1 - α ^ 2) * Real.artanh (r * α) / α)
        ((1 - α ^ 2) / (1 - s ^ 2 * α ^ 2)) s := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have h := (hasDerivAt_artanh_mul hs.1 hs.2 ha0 ha1).const_mul (1 - α ^ 2)
    have h2 := h.div_const α
    have he : (1 - α ^ 2) * (α / (1 - s ^ 2 * α ^ 2)) / α = (1 - α ^ 2) / (1 - s ^ 2 * α ^ 2) := by
      field_simp
    rwa [he] at h2
  have hcont : ContinuousOn (fun s : ℝ => (1 - α ^ 2) / (1 - s ^ 2 * α ^ 2)) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro s hs; exact one_sub_sq_ne hs.1 hs.2 ha0 ha1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp [gFun, mul_comm]

/-! ### `Ĝ`: the mixture form of `1 − g` -/

/-- `1 − g α = ∫₀¹ (1−s²)α²/(1−s²α²) ds`. -/
theorem one_sub_gFun_eq_integral (ha0 : 0 < α) (ha1 : α < 1) :
    1 - gFun α = ∫ s in (0:ℝ)..1, (1 - s ^ 2) * α ^ 2 / (1 - s ^ 2 * α ^ 2) := by
  have hpt : ∀ s : ℝ, (1 : ℝ) - s ^ 2 * α ^ 2 ≠ 0 →
      (1 - s ^ 2) * α ^ 2 / (1 - s ^ 2 * α ^ 2) = 1 - (1 - α ^ 2) / (1 - s ^ 2 * α ^ 2) := by
    intro s hne; field_simp; ring
  have hcong : (∫ s in (0:ℝ)..1, (1 - s ^ 2) * α ^ 2 / (1 - s ^ 2 * α ^ 2))
      = ∫ s in (0:ℝ)..1, (1 - (1 - α ^ 2) / (1 - s ^ 2 * α ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    exact hpt s (one_sub_sq_ne hs.1 hs.2 ha0 ha1)
  have hint : IntervalIntegrable (fun s : ℝ => (1 - α ^ 2) / (1 - s ^ 2 * α ^ 2))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro s hs; exact one_sub_sq_ne hs.1 hs.2 ha0 ha1
  rw [hcong, intervalIntegral.integral_sub intervalIntegrable_const hint, ← gFun_eq_integral ha0 ha1]
  simp

/-! ### `A`: the third functional -/

/-- `A α = ((1+α²)·artanh α − α)/(2α)`, the value of `α²Ĝ′(α²)`. -/
noncomputable def Aval (α : ℝ) : ℝ := ((1 + α ^ 2) * Real.artanh α - α) / (2 * α)

/-- `A α = ∫₀¹ α²(1−s²)/(1−s²α²)² ds`. -/
theorem Aval_eq_integral (ha0 : 0 < α) (ha1 : α < 1) :
    Aval α = ∫ s in (0:ℝ)..1, α ^ 2 * (1 - s ^ 2) / (1 - s ^ 2 * α ^ 2) ^ 2 := by
  have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => (1 + α ^ 2) * Real.artanh (r * α) / (2 * α)
          - r * (1 - α ^ 2) / (2 * (1 - r ^ 2 * α ^ 2)))
        (α ^ 2 * (1 - s ^ 2) / (1 - s ^ 2 * α ^ 2) ^ 2) s := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have hne := one_sub_sq_ne hs.1 hs.2 ha0 ha1
    have h1 := ((hasDerivAt_artanh_mul hs.1 hs.2 ha0 ha1).const_mul (1 + α ^ 2)).div_const (2 * α)
    have hden : HasDerivAt (fun r : ℝ => 2 * (1 - r ^ 2 * α ^ 2)) (-(4 * s * α ^ 2)) s :=
      hd_congr ((((hasDerivAt_pow 2 s).mul_const (α ^ 2)).const_sub 1).const_mul (2:ℝ))
        (by norm_num; ring)
    have hnum : HasDerivAt (fun r : ℝ => r * (1 - α ^ 2)) (1 - α ^ 2) s :=
      hd_congr ((hasDerivAt_id s).mul_const (1 - α ^ 2)) (by simp)
    have hd0 : 2 * (1 - s ^ 2 * α ^ 2) ≠ 0 := by
      intro h; exact hne (by linarith)
    refine hd_congr (h1.sub (hnum.div hden hd0)) ?_
    field_simp
    ring
  have hcont : ContinuousOn (fun s : ℝ => α ^ 2 * (1 - s ^ 2) / (1 - s ^ 2 * α ^ 2) ^ 2)
      (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro s hs; exact pow_ne_zero 2 (one_sub_sq_ne hs.1 hs.2 ha0 ha1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have h1 : (1 : ℝ) - 1 ^ 2 * α ^ 2 = 1 - α ^ 2 := by ring
  have hne : (1 : ℝ) - α ^ 2 ≠ 0 := by nlinarith
  rw [Aval]
  simp only [h1, one_mul, zero_mul, Real.artanh_zero, zero_div, sub_zero, mul_zero]
  field_simp

end BSCAveraging.Core
