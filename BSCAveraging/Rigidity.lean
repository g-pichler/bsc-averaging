import BSCAveraging.Definitions
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # The analytic core of the local-rigidity theorem

`NOTES.md` §5d proves that at every symmetric fixed point of positive value the
linearized skew map contracts, so no asymmetric branch bifurcates.  The whole
proof rests on two elementary facts about

```
L(y) = artanh y ,   f_e(y) = ∫₀^y L = ½[(1+y)·log(1+y) + (1−y)·log(1−y)] ,
g(y) = (1−y²)·L(y)/y ,   R(y) = f_e(y)/(y·L(y)) ,   Q(y) = (1−y²)·L(y)²/f_e(y) ,
```

namely `y < L(y)` and `f_e(y) ≤ y·L(y)/2` (the latter is the trapezoid bound, from
convexity of `artanh`).  This file establishes them, together with the small
amount of `artanh` calculus they need — Mathlib defines `Real.artanh` but
provides no derivative API for it.

See `BSCAveraging.Basic`. -/

open Real Set

namespace BSCAveraging

/-! ## A monotonicity helper -/

/-- If `f` vanishes at `0` and has positive derivative on `(0,1)`, it is positive
on `(0,1)`. -/
lemma pos_of_hasDerivAt_pos (f f' : ℝ → ℝ) (h0 : f 0 = 0)
    (hd : ∀ z ∈ Ioo (0:ℝ) 1, HasDerivAt f (f' z) z)
    (hd0 : ContinuousWithinAt f (Ico 0 1) 0)
    (hpos : ∀ z ∈ Ioo (0:ℝ) 1, 0 < f' z) {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : 0 < f y := by
  have hcont : ContinuousOn f (Ico 0 1) := by
    intro z hz
    rcases eq_or_lt_of_le hz.1 with h | h
    · rw [← h]; exact hd0
    · exact ((hd z ⟨h, hz.2⟩).continuousAt).continuousWithinAt
  have hmono : StrictMonoOn f (Ico 0 1) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := f') (convex_Ico 0 1) hcont ?_ ?_
    · rw [interior_Ico]
      exact fun z hz => (hd z hz).hasDerivWithinAt
    · rw [interior_Ico]; exact hpos
  have := hmono (left_mem_Ico.mpr one_pos) ⟨le_of_lt hy0, hy1⟩ hy0
  rwa [h0] at this

/-! ## `artanh` calculus -/

lemma artanh_eq_log_sub {z : ℝ} (h0 : -1 < z) (h1 : z < 1) :
    artanh z = (log (1 + z) - log (1 - z)) / 2 := by
  rw [artanh_eq_half_log ⟨le_of_lt h0, le_of_lt h1⟩,
    Real.log_div (by linarith) (by linarith)]
  ring

/-- The derivative of `artanh`, which Mathlib does not provide. -/
lemma hasDerivAt_artanh {z : ℝ} (h0 : -1 < z) (h1 : z < 1) :
    HasDerivAt artanh (1 / (1 - z ^ 2)) z := by
  have hp : (1 : ℝ) + z ≠ 0 := by linarith
  have hm : (1 : ℝ) - z ≠ 0 := by linarith
  have d1 : HasDerivAt (fun u : ℝ => log (1 + u)) (1 / (1 + z)) z := by
    have h : HasDerivAt (fun u : ℝ => 1 + u) 1 z := by simpa using (hasDerivAt_id z).const_add 1
    simpa using h.log hp
  have d2 : HasDerivAt (fun u : ℝ => log (1 - u)) (-1 / (1 - z)) z := by
    have h : HasDerivAt (fun u : ℝ => 1 - u) (-1) z := by simpa using (hasDerivAt_id z).const_sub 1
    simpa using h.log hm
  have d : HasDerivAt (fun u : ℝ => (log (1 + u) - log (1 - u)) / 2)
      ((1 / (1 + z) - -1 / (1 - z)) / 2) z := (d1.sub d2).div_const 2
  have hev : (fun u : ℝ => (log (1 + u) - log (1 - u)) / 2) =ᶠ[nhds z] artanh := by
    filter_upwards [Ioo_mem_nhds h0 h1] with u hu
    exact (artanh_eq_log_sub hu.1 hu.2).symm
  have hval : (1 / (1 + z) - -1 / (1 - z)) / 2 = 1 / (1 - z ^ 2) := by
    have hfac : (1 : ℝ) - z ^ 2 = (1 + z) * (1 - z) := by ring
    rw [hfac]
    field_simp
    ring
  rw [← hval]
  exact d.congr_of_eventuallyEq hev.symm

/-- **`y < artanh y`** on `(0,1)`. -/
theorem self_lt_artanh {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : y < artanh y := by
  have key : 0 < artanh y - y := by
    refine pos_of_hasDerivAt_pos (fun z => artanh z - z) (fun z => 1 / (1 - z ^ 2) - 1)
      (by simp) ?_ ?_ ?_ hy0 hy1
    · intro z hz
      exact (hasDerivAt_artanh (by linarith [hz.1]) hz.2).sub (hasDerivAt_id z)
    · exact (((hasDerivAt_artanh (by norm_num) (by norm_num)).sub
        (hasDerivAt_id (0:ℝ))).continuousAt).continuousWithinAt
    · intro z hz
      have h1 : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
      have : 1 < 1 / (1 - z ^ 2) := by
        rw [lt_div_iff₀ h1]; nlinarith [hz.1]
      linarith
  linarith

lemma hasDerivAt_one_sub_sq (z : ℝ) : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-(2 * z)) z := by
  simpa using ((hasDerivAt_pow 2 z).const_sub 1)

/-- `artanh y · (1 - y²) < y` on `(0,1)` — the multiplied-out form of
`artanh y < y/(1-y²)`, which is the derivative bound behind the trapezoid
estimate.  Its own derivative is `2y·artanh y > 0`. -/
theorem artanh_mul_lt {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : artanh y * (1 - y ^ 2) < y := by
  have key : 0 < y - artanh y * (1 - y ^ 2) := by
    refine pos_of_hasDerivAt_pos (fun z => z - artanh z * (1 - z ^ 2))
      (fun z => 2 * z * artanh z) (by simp) ?_ ?_ ?_ hy0 hy1
    · intro z hz
      have hne : (1 : ℝ) - z ^ 2 ≠ 0 := by nlinarith [hz.1, hz.2]
      have hm := (hasDerivAt_artanh (by linarith [hz.1]) hz.2).mul (hasDerivAt_one_sub_sq z)
      have heq : 1 / (1 - z ^ 2) * (1 - z ^ 2) + artanh z * -(2 * z) = 1 - 2 * z * artanh z := by
        field_simp
        ring
      rw [heq] at hm
      have h := (hasDerivAt_id' (x := z)).sub hm
      have heq2 : (1 : ℝ) - (1 - 2 * z * artanh z) = 2 * z * artanh z := by ring
      rwa [heq2] at h
    · have hm := (hasDerivAt_artanh (by norm_num) (by norm_num)).mul (hasDerivAt_one_sub_sq (0:ℝ))
      exact (((hasDerivAt_id' (x := (0:ℝ))).sub hm).continuousAt).continuousWithinAt
    · intro z hz
      have hpos : 0 < artanh z := Real.artanh_pos ⟨by linarith [hz.1], hz.2⟩
      have := hz.1
      positivity
  linarith

/-- The quotient form, for use below. -/
theorem artanh_lt_div {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : artanh y < y / (1 - y ^ 2) := by
  have h1 : 0 < 1 - y ^ 2 := by nlinarith
  rw [lt_div_iff₀ h1]
  exact artanh_mul_lt hy0 hy1

/-! ## `f_e` and the trapezoid bound -/

@[simp] lemma fe_zero : fe 0 = 0 := by simp [fe]

end BSCAveraging
