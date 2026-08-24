import BSCAveraging.Assembly
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! # Exploration: results not used by the final proof

Everything here is proved and `sorry`-free, but none of it is needed by
`averagedBSCConjecture_all`.  It is the record of the routes explored on the way:
Mrs. Gerber's Lemma, the sharp ratio bound (L1), the even/odd split (A), the skew
mechanism, and the many auxiliary results of `FixedPoint`.  Kept for reference and
because several are of independent interest; see `NOTES.md`.

Not imported by `BSCAveraging.Basic`. -/

open Real Set Pointwise

/-! Legacy exploration namespace: this file predates several files of the main
development and re-derives some of the same names, so it lives one level down. -/
namespace BSCAveraging.Legacy


/-! ### From `Definitions.lean` -/

lemma bconv_comm (a b : ℝ) : a ⊛ b = b ⊛ a := by unfold bconv; ring

lemma bconv_assoc (a b c : ℝ) : (a ⊛ b) ⊛ c = a ⊛ (b ⊛ c) := by unfold bconv; ring

@[simp] lemma bconv_zero_left (b : ℝ) : (0 : ℝ) ⊛ b = b := by unfold bconv; ring

lemma h2_symm (a : ℝ) : h2 (1 - a) = h2 a := by simp [h2, add_comm]

/-! ## The joint laws induced by the Markov chain `U — X — Y — V` -/


/-! ### From `Regions.lean` -/

lemma regionA_mono {p : ℝ} {R S : ℝ × ℝ × ℝ} (hR : R ∈ regionA p)
    (h0 : S.1 ≤ R.1) (h1 : R.2.1 ≤ S.2.1) (h2 : R.2.2 ≤ S.2.2) : S ∈ regionA p := by
  obtain ⟨cL, cR, hA, hB, hC⟩ := hR
  exact ⟨cL, cR, hA.trans h1, hB.trans h2, h0.trans hC⟩


/-! ### From `Nonneg.lean` -/

lemma mul_log_le_mul_log {q r : ℝ} (hq : 0 ≤ q) (h : q ≤ r) : q * log q ≤ q * log r := by
  rcases eq_or_lt_of_le hq with h0 | h0
  · rw [← h0]; simp
  · exact mul_le_mul_of_nonneg_left (Real.log_le_log h0 h) (le_of_lt h0)

/-! ## Consequences -/

/-- Conditioning reduces entropy: `H(V) ≤ H(U, V)`. -/
lemma entropy1_marg₂_le_entropy2 {q : Bool → Bool → ℝ} (hq : ∀ u v, 0 ≤ q u v) :
    entropy1 (marg₂ q) ≤ entropy2 q := by
  have t1 := mul_log_le_mul_log (hq false false) (le_marg₂ hq false false)
  have t2 := mul_log_le_mul_log (hq false true) (le_marg₂ hq false true)
  have t3 := mul_log_le_mul_log (hq true false) (le_marg₂ hq true false)
  have t4 := mul_log_le_mul_log (hq true true) (le_marg₂ hq true true)
  simp only [entropy1, entropy2, negMulLog, marg₂] at *
  linarith

/-- `I(U;V) ≤ H(U)`. -/
lemma mutualInfo_le_entropy1_marg₁ {q : Bool → Bool → ℝ} (hq : ∀ u v, 0 ≤ q u v) :
    mutualInfo q ≤ entropy1 (marg₁ q) := by
  have := entropy1_marg₂_le_entropy2 hq
  simp only [mutualInfo]
  linarith

lemma entropy1_le_log_two {m : Bool → ℝ} (h0 : 0 ≤ m false) (h1 : 0 ≤ m true)
    (hs : m false + m true = 1) : entropy1 m ≤ log 2 := by
  have he : entropy1 m = h2 (m false) := by
    simp only [entropy1, h2, show (1 : ℝ) - m false = m true by linarith]
  rw [he]
  exact h2_le_log_two h0 (by linarith)

/-- Mutual information of a joint law on `Bool × Bool` is at most `log 2`. -/
theorem mutualInfo_le_log_two {q : Bool → Bool → ℝ} (hq : ∀ u v, 0 ≤ q u v)
    (hsum : q false false + q false true + q true false + q true true = 1) :
    mutualInfo q ≤ log 2 := by
  refine le_trans (mutualInfo_le_entropy1_marg₁ hq) (entropy1_le_log_two ?_ ?_ ?_)
  · simp only [marg₁]; linarith [hq false false, hq false true]
  · simp only [marg₁]; linarith [hq true false, hq true true]
  · simp only [marg₁]; linarith


/-! ### From `Zero.lean` -/

theorem regionA_fst_le_log_two {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R : ℝ × ℝ × ℝ}
    (hR : R ∈ regionA p) : R.1 ≤ log 2 := by
  obtain ⟨cL, cR, _, _, hC⟩ := hR
  exact hC.trans ((mutualInfo_jointUV_le_jointUX hp0 hp1 cL cR).trans
    (mutualInfo_le_log_two (jointUX_nonneg cL) (jointUX_sum cL)))

lemma convex_outerBound (p : ℝ) : Convex ℝ (outerBound p) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  obtain ⟨k1, k2, k3, k4, k5⟩ := hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    nlinarith

/-- The outer bound survives the convex hull. -/
theorem convexHull_regionA_subset_outerBound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    convexHull ℝ (regionA p) ⊆ outerBound p :=
  convexHull_min (regionA_subset_outerBound hp0 hp1) (convex_outerBound p)

/-! ## The mirror symmetry on the region

Mirroring `cL` (relabelling `X`) keeps both rates and sends `I(U;V)` to its
value at `1 - p`.  Time-sharing a pair with its mirror image therefore realizes
the *even part* `½[I_p(U;V) + I_{1-p}(U;V)]` inside `conv 𝒜` at unchanged rates.
BSC pairs are exactly the pairs whose two values already agree
(`mutualInfo_jointUV_bsc_flip`), so for them symmetrization is free — this is
the mechanism behind the symmetrization analysis of `NOTES.md` §4. -/

/-- Each point of `𝒜` witnessed by `(cL, cR)` has a mirror partner in `𝒜` with
the same rates and `R₀` evaluated at `1 - p`. -/
theorem regionA_mirror {p r₁ r₂ : ℝ} (cL cR : Chan)
    (h1 : mutualInfo (jointUX cL) ≤ r₁) (h2 : mutualInfo (jointYV cR) ≤ r₂) :
    (mutualInfo (jointUV (1 - p) cL cR), r₁, r₂) ∈ regionA p :=
  ⟨mirror cL, cR, by rwa [mutualInfo_jointUX_mirror], h2,
    by rw [mutualInfo_jointUV_mirror]⟩

/-- The even part is achieved in `conv 𝒜`, at the same rates. -/
theorem even_part_mem_convexHull_regionA {p r₁ r₂ : ℝ} (cL cR : Chan)
    (h1 : mutualInfo (jointUX cL) ≤ r₁) (h2 : mutualInfo (jointYV cR) ≤ r₂) :
    ((mutualInfo (jointUV p cL cR) + mutualInfo (jointUV (1 - p) cL cR)) / 2, r₁, r₂)
      ∈ convexHull ℝ (regionA p) := by
  have hP : (mutualInfo (jointUV p cL cR), r₁, r₂) ∈ regionA p := ⟨cL, cR, h1, h2, le_rfl⟩
  have hQ : (mutualInfo (jointUV (1 - p) cL cR), r₁, r₂) ∈ regionA p := regionA_mirror cL cR h1 h2
  refine segment_subset_convexHull hP hQ ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> ring

/-- A BSC pair has no odd part: its `I(U;V)` is the same at `p` and at `1 - p`. -/
theorem mutualInfo_jointUV_bsc_flip {a b p : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mutualInfo (jointUV (1 - p) (bsc a ha0 ha1) (bsc b hb0 hb1))
      = mutualInfo (jointUV p (bsc a ha0 ha1) (bsc b hb0 hb1)) := by
  rw [mutualInfo_jointUV_bsc ha0 ha1 hb0 hb1 (by linarith) (by linarith),
    mutualInfo_jointUV_bsc ha0 ha1 hb0 hb1 hp0 hp1]
  have hflip : (a ⊛ (1 - p)) ⊛ b = 1 - (a ⊛ p) ⊛ b := by unfold bconv; ring
  rw [hflip, h2_symm]

/-! ## The two extreme points of `ℬ` at `p = 0` -/

/-- At `p = 0` the outer bound is exactly the answer: the three sets
`conv 𝒜`, `conv ℬ` and the data-processing bound all coincide. -/
theorem convexHull_regionA_zero_eq_outerBound :
    convexHull ℝ (regionA 0) = outerBound 0 := by
  refine Set.Subset.antisymm (convexHull_regionA_subset_outerBound le_rfl (by norm_num)) ?_
  refine le_trans outerBound_zero_subset_convexHull ?_
  exact convexHull_regionB_subset le_rfl (by norm_num)

theorem convexHull_regionB_zero_eq_outerBound :
    convexHull ℝ (regionB 0) = outerBound 0 := by
  rw [← averagedBSCConjecture_zero]
  exact convexHull_regionA_zero_eq_outerBound


/-! ### From `Rigidity.lean` -/

lemma hasDerivAt_fe {z : ℝ} (h0 : -1 < z) (h1 : z < 1) : HasDerivAt fe (artanh z) z := by
  have hp : (1 : ℝ) + z ≠ 0 := by linarith
  have hm : (1 : ℝ) - z ≠ 0 := by linarith
  have d1 : HasDerivAt (fun u : ℝ => (1 + u) * log (1 + u)) (log (1 + z) + 1) z := by
    have ha : HasDerivAt (fun u : ℝ => 1 + u) 1 z := by simpa using (hasDerivAt_id z).const_add 1
    have h := ha.mul (ha.log hp)
    have heq : 1 * log (1 + z) + (1 + z) * (1 / (1 + z)) = log (1 + z) + 1 := by
      field_simp
    rwa [heq] at h
  have d2 : HasDerivAt (fun u : ℝ => (1 - u) * log (1 - u)) (-log (1 - z) - 1) z := by
    have ha : HasDerivAt (fun u : ℝ => 1 - u) (-1) z := by simpa using (hasDerivAt_id z).const_sub 1
    have h := ha.mul (ha.log hm)
    have heq : -1 * log (1 - z) + (1 - z) * (-1 / (1 - z)) = -log (1 - z) - 1 := by
      field_simp
      ring
    rwa [heq] at h
  have h := (d1.add d2).div_const 2
  have heq : (log (1 + z) + 1 + (-log (1 - z) - 1)) / 2 = artanh z := by
    rw [artanh_eq_log_sub h0 h1]; ring
  rwa [heq] at h

/-- **The trapezoid bound** `f_e(y) ≤ y·artanh(y)/2`, from convexity of `artanh`. -/
theorem fe_le_half_mul {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : fe y < y * artanh y / 2 := by
  have key : 0 < y * artanh y / 2 - fe y := by
    refine pos_of_hasDerivAt_pos (fun z => z * artanh z / 2 - fe z)
      (fun z => (1 * artanh z + z * (1 / (1 - z ^ 2))) / 2 - artanh z) (by simp) ?_ ?_ ?_ hy0 hy1
    · intro z hz
      exact (((hasDerivAt_id z).mul (hasDerivAt_artanh (by linarith [hz.1]) hz.2)).div_const
        2).sub (hasDerivAt_fe (by linarith [hz.1]) hz.2)
    · exact ((((hasDerivAt_id (0:ℝ)).mul (hasDerivAt_artanh (by norm_num) (by norm_num))).div_const
        2).sub (hasDerivAt_fe (by norm_num) (by norm_num))).continuousAt.continuousWithinAt
    · intro z hz
      have h1 : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
      have hlt := artanh_lt_div hz.1 hz.2
      have : z * (1 / (1 - z ^ 2)) = z / (1 - z ^ 2) := by ring
      rw [this]
      linarith
  linarith

lemma fe_pos {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : 0 < fe y := by
  refine pos_of_hasDerivAt_pos fe artanh fe_zero
    (fun z hz => hasDerivAt_fe (by linarith [hz.1]) hz.2) ?_
    (fun z hz => Real.artanh_pos hz) hy0 hy1
  exact (hasDerivAt_fe (by norm_num) (by norm_num)).continuousAt.continuousWithinAt

/-! ## The three profile functions `g`, `R`, `Q`

```
g(y) = (1−y²)·L(y)/y ,   R(y) = f_e(y)/(y·L(y)) ,   Q(y) = (1−y²)·L(y)²/f_e(y) ,
```
so that `g = Q·R`.  In the notation of `NOTES.md` §5d, `g` is the curvature
profile of the bitangent construction, `R` the (normalized) value carried by a
BSC of bias `y`, and `Q` the ratio of the two.  The whole local-rigidity proof
is: `Q` is strictly decreasing, hence the value constraint `R(s) + R(t) < R(x)`
upgrades to `g(s) + g(t) < g(x)`, which is exactly `κ_s κ_t > 1`. -/

noncomputable def gFun (y : ℝ) : ℝ := (1 - y ^ 2) * artanh y / y

noncomputable def Rfun (y : ℝ) : ℝ := fe y / (y * artanh y)

noncomputable def Qfun (y : ℝ) : ℝ := (1 - y ^ 2) * artanh y ^ 2 / fe y

lemma gFun_pos {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : 0 < gFun y := by
  have h1 : 0 < 1 - y ^ 2 := by nlinarith
  have h2 : 0 < artanh y := Real.artanh_pos ⟨hy0, hy1⟩
  unfold gFun; positivity

lemma Rfun_pos {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : 0 < Rfun y := by
  have h2 : 0 < artanh y := Real.artanh_pos ⟨hy0, hy1⟩
  have h3 : 0 < fe y := fe_pos hy0 hy1
  unfold Rfun; positivity

lemma Qfun_pos {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : 0 < Qfun y := by
  have h1 : 0 < 1 - y ^ 2 := by nlinarith
  have h2 : 0 < artanh y := Real.artanh_pos ⟨hy0, hy1⟩
  have h3 : 0 < fe y := fe_pos hy0 hy1
  unfold Qfun; positivity

/-- **The factorization** `g = Q · R`. -/
theorem gFun_eq_Qfun_mul_Rfun {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    gFun y = Qfun y * Rfun y := by
  have h2 : artanh y ≠ 0 := ne_of_gt (Real.artanh_pos ⟨hy0, hy1⟩)
  have h3 : fe y ≠ 0 := ne_of_gt (fe_pos hy0 hy1)
  unfold gFun Qfun Rfun
  field_simp

/-- `g < 1`, i.e. `(1−y²)·artanh y < y`. -/
lemma gFun_lt_one {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : gFun y < 1 := by
  unfold gFun
  rw [div_lt_one hy0]
  have := artanh_mul_lt hy0 hy1
  linarith

/-- `1 − g(y) < y²`, i.e. `g(y) > 1 − y²`, which is just `y < artanh y`. -/
lemma one_sub_gFun_lt_sq {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : 1 - gFun y < y ^ 2 := by
  have hL := self_lt_artanh hy0 hy1
  have h1 : 0 < 1 - y ^ 2 := by nlinarith
  have : 1 - y ^ 2 < gFun y := by
    unfold gFun
    rw [lt_div_iff₀ hy0]
    nlinarith
  linarith

/-! ## Monotonicity -/

/-- Strict antitonicity on `(0,1)` from a negative derivative. -/
lemma strictAntiOn_Ioo_of_deriv_neg (f f' : ℝ → ℝ)
    (hd : ∀ z ∈ Ioo (0:ℝ) 1, HasDerivAt f (f' z) z)
    (hneg : ∀ z ∈ Ioo (0:ℝ) 1, f' z < 0) : StrictAntiOn f (Ioo (0:ℝ) 1) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (f' := f') (convex_Ioo 0 1)
    (fun z hz => ((hd z hz).continuousAt).continuousWithinAt) ?_ ?_
  · rw [interior_Ioo]; exact fun z hz => (hd z hz).hasDerivWithinAt
  · rw [interior_Ioo]; exact hneg

lemma hasDerivAt_gFun {z : ℝ} (h0 : 0 < z) (h1 : z < 1) :
    HasDerivAt gFun ((z - (1 + z ^ 2) * artanh z) / z ^ 2) z := by
  have hne : (1:ℝ) - z ^ 2 ≠ 0 := by nlinarith
  have hc : HasDerivAt (fun u : ℝ => (1 - u ^ 2) * artanh u) (1 - 2 * z * artanh z) z := by
    have h := (hasDerivAt_one_sub_sq z).mul (hasDerivAt_artanh (by linarith) h1)
    have heq : -(2 * z) * artanh z + (1 - z ^ 2) * (1 / (1 - z ^ 2)) = 1 - 2 * z * artanh z := by
      field_simp
      ring
    rw [heq] at h
    exact h
  have h := hc.fun_div (hasDerivAt_id' (x := z)) (ne_of_gt h0)
  have heq : ((1 - 2 * z * artanh z) * z - (1 - z ^ 2) * artanh z * 1) / z ^ 2
      = (z - (1 + z ^ 2) * artanh z) / z ^ 2 := by ring
  rw [heq] at h
  exact h

/-- `g` is strictly decreasing on `(0,1)`; its derivative is
`(y − (1+y²)·artanh y)/y² < 0` because `artanh y > y`. -/
theorem gFun_strictAntiOn : StrictAntiOn gFun (Ioo (0:ℝ) 1) := by
  refine strictAntiOn_Ioo_of_deriv_neg gFun (fun z => (z - (1 + z ^ 2) * artanh z) / z ^ 2)
    (fun z hz => hasDerivAt_gFun hz.1 hz.2) ?_
  intro z hz
  have hL := self_lt_artanh hz.1 hz.2
  have hLpos : 0 < artanh z := Real.artanh_pos hz
  have : z - (1 + z ^ 2) * artanh z < 0 := by nlinarith [hz.1]
  exact div_neg_of_neg_of_pos this (pow_pos hz.1 2)

/-- The inequality that makes `Q` decrease:
`2f_e(y)·(1 − y·artanh y) < (1 − y²)·artanh y ²`.  It follows from the trapezoid
bound `f_e ≤ y·artanh y/2` together with `y < artanh y`. -/
theorem two_fe_mul_lt {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    2 * fe y * (1 - y * artanh y) < (1 - y ^ 2) * artanh y ^ 2 := by
  have hL := self_lt_artanh hy0 hy1
  have hLpos : 0 < artanh y := Real.artanh_pos ⟨hy0, hy1⟩
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith
  have hP : 0 < fe y := fe_pos hy0 hy1
  have hR : 0 < (1 - y ^ 2) * artanh y ^ 2 := mul_pos hy2 (pow_pos hLpos 2)
  rcases le_or_gt (1 - y * artanh y) 0 with h | h
  · have h4 : 0 ≤ 2 * fe y * -(1 - y * artanh y) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  · have hPle := fe_le_half_mul hy0 hy1
    have h1 : 2 * fe y * (1 - y * artanh y) < y * artanh y * (1 - y * artanh y) := by
      nlinarith
    have h2 : y * artanh y * (1 - y * artanh y) ≤ (1 - y ^ 2) * artanh y ^ 2 := by
      nlinarith [mul_pos hLpos (sub_pos.mpr hL)]
    linarith

lemma hasDerivAt_Qfun {z : ℝ} (h0 : 0 < z) (h1 : z < 1) :
    HasDerivAt Qfun
      (artanh z * (2 * fe z * (1 - z * artanh z) - (1 - z ^ 2) * artanh z ^ 2) / fe z ^ 2) z := by
  have hne : (1:ℝ) - z ^ 2 ≠ 0 := by nlinarith
  have hL := hasDerivAt_artanh (by linarith : (-1:ℝ) < z) h1
  have hc : HasDerivAt (fun u : ℝ => (1 - u ^ 2) * artanh u ^ 2)
      (2 * artanh z - 2 * z * artanh z ^ 2) z := by
    have h := (hasDerivAt_one_sub_sq z).mul (hL.mul hL)
    simp only [Pi.mul_apply] at h
    have heq : -(2 * z) * (artanh z * artanh z)
        + (1 - z ^ 2) * (1 / (1 - z ^ 2) * artanh z + artanh z * (1 / (1 - z ^ 2)))
        = 2 * artanh z - 2 * z * artanh z ^ 2 := by
      field_simp
      ring
    rw [heq] at h
    have hfun : ((fun u : ℝ => 1 - u ^ 2) * (artanh * artanh))
        = fun u : ℝ => (1 - u ^ 2) * artanh u ^ 2 := by
      funext u; simp only [Pi.mul_apply]; ring
    rwa [hfun] at h
  have hP := fe_pos h0 h1
  have h := hc.fun_div (hasDerivAt_fe (by linarith) h1) (ne_of_gt hP)
  have heq : ((2 * artanh z - 2 * z * artanh z ^ 2) * fe z
      - (1 - z ^ 2) * artanh z ^ 2 * artanh z) / fe z ^ 2
      = artanh z * (2 * fe z * (1 - z * artanh z) - (1 - z ^ 2) * artanh z ^ 2) / fe z ^ 2 := by
    ring
  rw [heq] at h
  exact h

/-- **`Q` is strictly decreasing on `(0,1)`.**  This is the one nontrivial
analytic input of the local-rigidity theorem. -/
theorem Qfun_strictAntiOn : StrictAntiOn Qfun (Ioo (0:ℝ) 1) := by
  refine strictAntiOn_Ioo_of_deriv_neg Qfun
    (fun z => artanh z * (2 * fe z * (1 - z * artanh z) - (1 - z ^ 2) * artanh z ^ 2) / fe z ^ 2)
    (fun z hz => hasDerivAt_Qfun hz.1 hz.2) ?_
  intro z hz
  have hLpos : 0 < artanh z := Real.artanh_pos hz
  have hP : 0 < fe z := fe_pos hz.1 hz.2
  have hkey := two_fe_mul_lt hz.1 hz.2
  refine div_neg_of_neg_of_pos ?_ (by positivity)
  exact mul_neg_of_pos_of_neg hLpos (by linarith)

/-! ## The local-rigidity theorem -/

/-- **Step 5.**  If `x < s`, `x < t` and the value constraint `R(s) + R(t) < R(x)`
holds, then `g(s) + g(t) < g(x)`.  This is where the constraint enters — and it
is the only place it is used. -/
theorem gFun_add_lt {x s t : ℝ} (hx0 : 0 < x) (hs1 : s < 1) (ht1 : t < 1)
    (hxs : x < s) (hxt : x < t) (hR : Rfun s + Rfun t < Rfun x) :
    gFun s + gFun t < gFun x := by
  have hs0 : 0 < s := hx0.trans hxs
  have ht0 : 0 < t := hx0.trans hxt
  have hx1 : x < 1 := hxs.trans hs1
  have hQs : Qfun s ≤ Qfun x :=
    le_of_lt (Qfun_strictAntiOn ⟨hx0, hx1⟩ ⟨hs0, hs1⟩ hxs)
  have hQt : Qfun t ≤ Qfun x :=
    le_of_lt (Qfun_strictAntiOn ⟨hx0, hx1⟩ ⟨ht0, ht1⟩ hxt)
  have hQx : 0 < Qfun x := Qfun_pos hx0 hx1
  have hRs : 0 < Rfun s := Rfun_pos hs0 hs1
  have hRt : 0 < Rfun t := Rfun_pos ht0 ht1
  rw [gFun_eq_Qfun_mul_Rfun hs0 hs1, gFun_eq_Qfun_mul_Rfun ht0 ht1,
    gFun_eq_Qfun_mul_Rfun hx0 hx1]
  nlinarith

/-- **Step 3 + 5.**  The curvature ratios `κ_y = g(x)/g(y) − 1` satisfy
`κ_s · κ_t > 1`. -/
theorem kappa_prod_gt_one {x s t : ℝ} (hx0 : 0 < x) (hs1 : s < 1) (ht1 : t < 1)
    (hxs : x < s) (hxt : x < t) (hR : Rfun s + Rfun t < Rfun x) :
    1 < (gFun x / gFun s - 1) * (gFun x / gFun t - 1) := by
  have hs0 : 0 < s := hx0.trans hxs
  have ht0 : 0 < t := hx0.trans hxt
  have hx1 : x < 1 := hxs.trans hs1
  have ha : 0 < gFun s := gFun_pos hs0 hs1
  have hb : 0 < gFun t := gFun_pos ht0 ht1
  have hG : 0 < gFun x := gFun_pos hx0 hx1
  have key := gFun_add_lt hx0 hs1 ht1 hxs hxt hR
  have e1 : gFun x / gFun s - 1 = (gFun x - gFun s) / gFun s := by field_simp
  have e2 : gFun x / gFun t - 1 = (gFun x - gFun t) / gFun t := by field_simp
  rw [e1, e2, div_mul_div_comm, lt_div_iff₀ (by positivity)]
  nlinarith [mul_lt_mul_of_pos_left key hG]

/-- **Local rigidity (NOTES.md §5d, step 6).**  At a symmetric fixed point of
positive value the product of the two linearized skew gains is
`Λ·Λ' = (1−g(x))² / (x² κ_s κ_t) < x² < 1`, so the linearized alternating map is
a strict contraction on the skew coordinates: no asymmetric branch bifurcates. -/
theorem lambda_prod_lt {x s t : ℝ} (hx0 : 0 < x) (hs1 : s < 1) (ht1 : t < 1)
    (hxs : x < s) (hxt : x < t) (hR : Rfun s + Rfun t < Rfun x) :
    (1 - gFun x) ^ 2 / (x ^ 2 * ((gFun x / gFun s - 1) * (gFun x / gFun t - 1))) < x ^ 2 := by
  have hx1 : x < 1 := hxs.trans hs1
  have hK := kappa_prod_gt_one hx0 hs1 ht1 hxs hxt hR
  have hG1 : gFun x < 1 := gFun_lt_one hx0 hx1
  have hGs : 1 - gFun x < x ^ 2 := one_sub_gFun_lt_sq hx0 hx1
  have hden : 0 < x ^ 2 * ((gFun x / gFun s - 1) * (gFun x / gFun t - 1)) :=
    mul_pos (by positivity) (zero_lt_one.trans hK)
  rw [div_lt_iff₀ hden]
  have h1 : (1 - gFun x) ^ 2 < x ^ 4 := by nlinarith
  have h2 : x ^ 4 < x ^ 2 * (x ^ 2 * ((gFun x / gFun s - 1) * (gFun x / gFun t - 1))) := by
    nlinarith [pow_pos hx0 2]
  linarith

/-- The contraction statement in the form actually used: `Λ·Λ' < 1`. -/
theorem lambda_prod_lt_one {x s t : ℝ} (hx0 : 0 < x) (hs1 : s < 1) (ht1 : t < 1)
    (hxs : x < s) (hxt : x < t) (hR : Rfun s + Rfun t < Rfun x) :
    (1 - gFun x) ^ 2 / (x ^ 2 * ((gFun x / gFun s - 1) * (gFun x / gFun t - 1))) < 1 := by
  have hx1 : x < 1 := hxs.trans hs1
  have h := lambda_prod_lt hx0 hs1 ht1 hxs hxt hR
  nlinarith


/-! ### From `SignFlip.lean` -/

/-- The mirrored statement: opposite skews give `Ω > 0`.  That positive `Ω` is
the entire gain an asymmetric pair can have over the symmetric optimum. -/
theorem omegaTwoPoint_pos {δ a b c d : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hb0 : 0 < b) (hba : b < a) (ha1 : a ≤ 1)
    (hc0 : 0 < c) (hcd : c < d) (hd1 : d ≤ 1) :
    0 < OmegaTwoPoint δ a b c d := by
  have ha0 : 0 < a := hb0.trans hba
  have hd0 : 0 < d := hc0.trans hcd
  have hΔ := wFun_mixed_diff_pos hδ0 hδ1 hb0 hba ha1 hc0 hcd hd1
  have hneg : wFun δ (a * c) - wFun δ (a * d) - (wFun δ (b * c) - wFun δ (b * d)) < 0 := by
    linarith
  rw [omegaTwoPoint_eq ha0 hb0 hc0 hd0, neg_mul, neg_mul, neg_pos]
  exact mul_neg_of_pos_of_neg (mul_pos (by positivity) (by positivity)) hneg


/-! ### From `Lagrangian.lean` -/

lemma fe_abs (y : ℝ) : fe |y| = fe y := by
  rcases abs_choice y with h | h
  · rw [h]
  · rw [h, fe_neg]

lemma fe_nonneg {y : ℝ} (h : |y| < 1) : 0 ≤ fe y := by
  rw [← fe_abs]
  rcases eq_or_lt_of_le (abs_nonneg y) with h0 | h0
  · rw [← h0]; simp
  · exact le_of_lt (fe_pos h0 h)

/-! ## The kernel `f` and its chord -/

/-- **`f` lies below its chord on `[−a, a]`.**  The chord through
`(−a, f(−a))` and `(a, f(a))` is `z ↦ f_e(a) + z·fo(a)/a`, since `f_e` and `fo` are
the even and odd parts of `f`. -/
theorem fFun_le_chord {a v : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hv : |v| ≤ a) :
    fFun v ≤ fe a + v * (fo a / a) := by
  obtain ⟨hva, hav⟩ := abs_le.mp hv
  set θ : ℝ := (a + v) / (2 * a) with hθ
  have ha2 : (0 : ℝ) < 2 * a := by linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg (by linarith) (le_of_lt ha2)
  have hθ1 : 0 ≤ 1 - θ := by
    rw [hθ, sub_nonneg, div_le_one ha2]; linarith
  have hsum : θ + (1 - θ) = 1 := by ring
  have hm1 : (1 + a) ∈ Ici (0 : ℝ) := by simp; linarith
  have hm2 : (1 - a) ∈ Ici (0 : ℝ) := by simp; linarith
  have hcomb : θ * (1 + a) + (1 - θ) * (1 - a) = 1 + v := by
    rw [hθ]; field_simp; ring
  have h := Real.convexOn_mul_log.2 hm1 hm2 hθ0 hθ1 hsum
  simp only [smul_eq_mul] at h
  rw [hcomb] at h
  have hrhs : θ * ((1 + a) * log (1 + a)) + (1 - θ) * ((1 - a) * log (1 - a))
      = fe a + v * (fo a / a) := by
    rw [hθ, fe, fo]; field_simp; ring
  rw [hrhs] at h
  exact h

/-- Two-point Jensen against the chord: a mean-zero pair inside `[−a,a]` has
`f`-average at most `f_e(a)`. -/
theorem chord_expectation {a v₁ v₂ w₁ w₂ : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hw1 : 0 ≤ w₁) (hw2 : 0 ≤ w₂) (hsum : w₁ + w₂ = 1)
    (hmean : w₁ * v₁ + w₂ * v₂ = 0) (h1 : |v₁| ≤ a) (h2 : |v₂| ≤ a) :
    w₁ * fFun v₁ + w₂ * fFun v₂ ≤ fe a := by
  have b1 := mul_le_mul_of_nonneg_left (fFun_le_chord ha0 ha1 h1) hw1
  have b2 := mul_le_mul_of_nonneg_left (fFun_le_chord ha0 ha1 h2) hw2
  have key : w₁ * (fe a + v₁ * (fo a / a)) + w₂ * (fe a + v₂ * (fo a / a)) = fe a := by
    linear_combination fe a * hsum + (fo a / a) * hmean
  linarith

/-! ## Data processing in bias coordinates -/

/-- **One row of the data-processing inequality.**  For a fixed bias `s` of `X`
given `U = u`, averaging `f(δ·s·T)` over a mean-zero `T` in `[−1,1]` gives at
most `f_e(s)`.  This is `I(U;V) ≤ I(U;X)` restricted to one value of `U`. -/
theorem dpi_row {δ s t₁ t₂ q₁ q₂ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hs : |s| < 1)
    (ht1 : |t₁| ≤ 1) (ht2 : |t₂| ≤ 1)
    (hq1 : 0 ≤ q₁) (hq2 : 0 ≤ q₂) (hsum : q₁ + q₂ = 1) (hmean : q₁ * t₁ + q₂ * t₂ = 0) :
    q₁ * fFun (δ * (s * t₁)) + q₂ * fFun (δ * (s * t₂)) ≤ fe s := by
  rcases eq_or_lt_of_le (abs_nonneg s) with h0 | h0
  · have hs0 : s = 0 := abs_eq_zero.mp h0.symm
    simp [hs0]
  · have hb : ∀ t : ℝ, |t| ≤ 1 → |δ * (s * t)| ≤ |s| := by
      intro t ht
      rw [abs_mul, abs_mul, abs_of_pos hδ0]
      calc δ * (|s| * |t|) ≤ 1 * (|s| * 1) := by
            apply mul_le_mul hδ1 (by nlinarith [abs_nonneg s, abs_nonneg t]) (by positivity)
              (by norm_num)
        _ = |s| := by ring
    have := chord_expectation h0 hs hq1 hq2 hsum
      (by rw [show q₁ * (δ * (s * t₁)) + q₂ * (δ * (s * t₂)) = δ * s * (q₁ * t₁ + q₂ * t₂) from by
            ring, hmean, mul_zero])
      (hb t₁ ht1) (hb t₂ ht2)
    rwa [fe_abs] at this

/-- **Data processing**, `E f(δST) ≤ E f_e(S)`, i.e. `I(U;V) ≤ I(U;X)`, for
two-point `S` and `T`. -/
theorem lagrKernel_le {δ s₁ s₂ p₁ p₂ t₁ t₂ q₁ q₂ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hs1 : |s₁| < 1) (hs2 : |s₂| < 1)
    (ht1 : |t₁| ≤ 1) (ht2 : |t₂| ≤ 1)
    (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂)
    (hq1 : 0 ≤ q₁) (hq2 : 0 ≤ q₂) (hqsum : q₁ + q₂ = 1) (hqmean : q₁ * t₁ + q₂ * t₂ = 0) :
    p₁ * (q₁ * fFun (δ * (s₁ * t₁)) + q₂ * fFun (δ * (s₁ * t₂)))
      + p₂ * (q₁ * fFun (δ * (s₂ * t₁)) + q₂ * fFun (δ * (s₂ * t₂)))
      ≤ p₁ * fe s₁ + p₂ * fe s₂ := by
  have r1 := dpi_row hδ0 hδ1 hs1 ht1 ht2 hq1 hq2 hqsum hqmean
  have r2 := dpi_row hδ0 hδ1 hs2 ht1 ht2 hq1 hq2 hqsum hqmean
  have := mul_le_mul_of_nonneg_left r1 hp1
  have := mul_le_mul_of_nonneg_left r2 hp2
  linarith

/-- **The Lagrangian is non-positive once `μ ≥ 1`.**  Consequently `J ≤ 0`,
while the symmetric optimum is `≥ g(0,0) = 0`, so `J = J_sym` on that whole
region and `μ ∈ [0,1)` is WLOG (and symmetrically for `ν`). -/
theorem lagrangian_nonpos_of_one_le_mu {δ μ ν s₁ s₂ p₁ p₂ t₁ t₂ q₁ q₂ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hs1 : |s₁| < 1) (hs2 : |s₂| < 1)
    (ht1 : |t₁| < 1) (ht2 : |t₂| < 1)
    (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂)
    (hq1 : 0 ≤ q₁) (hq2 : 0 ≤ q₂) (hqsum : q₁ + q₂ = 1) (hqmean : q₁ * t₁ + q₂ * t₂ = 0)
    (hμ : 1 ≤ μ) (hν : 0 ≤ ν) :
    p₁ * (q₁ * fFun (δ * (s₁ * t₁)) + q₂ * fFun (δ * (s₁ * t₂)))
        + p₂ * (q₁ * fFun (δ * (s₂ * t₁)) + q₂ * fFun (δ * (s₂ * t₂)))
      - μ * (p₁ * fe s₁ + p₂ * fe s₂) - ν * (q₁ * fe t₁ + q₂ * fe t₂) ≤ 0 := by
  have hdpi := lagrKernel_le hδ0 hδ1 hs1 hs2 (le_of_lt ht1) (le_of_lt ht2)
    hp1 hp2 hq1 hq2 hqsum hqmean
  have hS : 0 ≤ p₁ * fe s₁ + p₂ * fe s₂ :=
    add_nonneg (mul_nonneg hp1 (fe_nonneg hs1)) (mul_nonneg hp2 (fe_nonneg hs2))
  have hT : 0 ≤ q₁ * fe t₁ + q₂ * fe t₂ :=
    add_nonneg (mul_nonneg hq1 (fe_nonneg ht1)) (mul_nonneg hq2 (fe_nonneg ht2))
  nlinarith


/-! ## Supermodularity of `f_e`

`A = (f_e(m+k) + f_e(m−k))/2` is the rate of the channel with conditional biases
`m ± k` (`NOTES.md` §5h).  It is at least `f_e(m) + f_e(k)`: the "shift" and the
"spread" each cost their own rate.  Since `f_e = ∫ artanh`, the whole statement
integrates the elementary

```
artanh(m+u) − artanh(m−u) ≥ 2·artanh u ,
```

which is the artanh addition formula: both sides are `artanh` of something, and
`2u/((1−u²) − ... )` comparison reduces to `m²(1−u)² ≤ m²(1+u)²`. -/

lemma artanh_add_sub_ge {m u : ℝ} (hm : 0 ≤ m) (hu : 0 ≤ u) (h : m + u < 1) :
    2 * artanh u ≤ artanh (m + u) - artanh (m - u) := by
  have hu1 : u < 1 := by linarith
  have p1 : (0:ℝ) < 1 + (m + u) := by linarith
  have p2 : (0:ℝ) < 1 - (m + u) := by linarith
  have p3 : (0:ℝ) < 1 + (m - u) := by linarith
  have p4 : (0:ℝ) < 1 - (m - u) := by linarith
  have p5 : (0:ℝ) < 1 + u := by linarith
  have p6 : (0:ℝ) < 1 - u := by linarith
  have hA : (0:ℝ) < (1 + u) ^ 2 - m ^ 2 := by nlinarith
  have hB : (0:ℝ) < (1 - u) ^ 2 - m ^ 2 := by nlinarith
  rw [artanh_eq_log_sub (by linarith) (by linarith),
    artanh_eq_log_sub (by linarith) (by linarith),
    artanh_eq_log_sub (by linarith) (by linarith)]
  have e1 : log (1 + (m + u)) + log (1 - (m - u)) = log ((1 + u) ^ 2 - m ^ 2) := by
    rw [← Real.log_mul (ne_of_gt p1) (ne_of_gt p4)]; ring_nf
  have e2 : log (1 - (m + u)) + log (1 + (m - u)) = log ((1 - u) ^ 2 - m ^ 2) := by
    rw [← Real.log_mul (ne_of_gt p2) (ne_of_gt p3)]; ring_nf
  have e3 : log (1 + u) + log (1 + u) = log ((1 + u) ^ 2) := by
    rw [← Real.log_mul (ne_of_gt p5) (ne_of_gt p5)]; ring_nf
  have e4 : log (1 - u) + log (1 - u) = log ((1 - u) ^ 2) := by
    rw [← Real.log_mul (ne_of_gt p6) (ne_of_gt p6)]; ring_nf
  have key : (1 + u) ^ 2 * ((1 - u) ^ 2 - m ^ 2) ≤ (1 - u) ^ 2 * ((1 + u) ^ 2 - m ^ 2) := by
    nlinarith [sq_nonneg m, mul_nonneg hu hm]
  have hlog := Real.log_le_log (by positivity) key
  rw [Real.log_mul (by positivity) (ne_of_gt hB), Real.log_mul (by positivity) (ne_of_gt hA)]
    at hlog
  linarith [e1, e2, e3, e4, hlog]

/-- **`f_e` is supermodular**: `f_e(m+k) + f_e(m−k) ≥ 2f_e(m) + 2f_e(k)`.  Hence the
channel rate `A = (f_e(m+k)+f_e(m−k))/2` is at least `f_e(m) + f_e(k)`. -/
theorem fe_supermodular {m k : ℝ} (hm : 0 ≤ m) (hk : 0 ≤ k) (h : m + k < 1) :
    2 * fe m + 2 * fe k ≤ fe (m + k) + fe (m - k) := by
  set G : ℝ → ℝ := fun x => fe (m + x) + fe (m - x) - 2 * fe m - 2 * fe x with hGdef
  have hderiv : ∀ x ∈ Icc (0:ℝ) k,
      HasDerivAt G (artanh (m + x) - artanh (m - x) - 2 * artanh x) x := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hxk : x ≤ k := hx.2
    have d1 : HasDerivAt (fun t : ℝ => fe (m + t)) (artanh (m + x)) x :=
      (hasDerivAt_fe (by linarith) (by linarith)).comp_const_add m x
    have d2 : HasDerivAt (fun t : ℝ => fe (m - t)) (-artanh (m - x)) x :=
      (hasDerivAt_fe (by linarith) (by linarith)).comp_const_sub m x
    have d3 : HasDerivAt (fun t : ℝ => 2 * fe t) (2 * artanh x) x :=
      (hasDerivAt_fe (by linarith) (by linarith)).const_mul 2
    have hd := ((d1.add d2).sub_const (2 * fe m)).sub d3
    have heq : artanh (m + x) + -artanh (m - x) - 2 * artanh x
        = artanh (m + x) - artanh (m - x) - 2 * artanh x := by ring
    rw [heq] at hd
    exact hd
  have hmono : MonotoneOn G (Icc 0 k) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 k)
      (f' := fun x => artanh (m + x) - artanh (m - x) - 2 * artanh x)
      (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt) ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have := artanh_add_sub_ge hm (le_of_lt hx.1) (by linarith [hx.2])
      linarith
  have h0 : G 0 = 0 := by simp [hGdef]; ring
  have := hmono (left_mem_Icc.mpr hk) (right_mem_Icc.mpr hk) hk
  rw [h0] at this
  simp only [hGdef] at this
  linarith


/-! ### From `MGL.lean` -/


/-- **Mrs. Gerber's Lemma, differential form, in bias coordinates.**  For a
composite bias factor `κ ∈ (0,1)` and a bias `q ∈ (0,1)`,

```
κ · (1 − q²) · artanh q  <  (1 − (κq)²) · artanh (κq) ,
```

which is the condition `Θ_κ'' ≤ 0` for `Θ_κ(u) = f_e(κ·f_e⁻¹(u))`.  Equivalent to
`gFun q < gFun (κq)`, i.e. to `gFun` being strictly decreasing. -/
theorem mgl_bias {κ q : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    κ * ((1 - q ^ 2) * artanh q) < (1 - (κ * q) ^ 2) * artanh (κ * q) := by
  have hkq0 : 0 < κ * q := mul_pos hκ0 hq0
  have hkq1 : κ * q < 1 := by nlinarith
  have hlt : κ * q < q := by nlinarith
  have h := gFun_strictAntiOn ⟨hkq0, hkq1⟩ ⟨hq0, hq1⟩ hlt
  have h2 := mul_lt_mul_of_pos_left h hkq0
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hkqne : κ * q ≠ 0 := ne_of_gt hkq0
  have e1 : κ * q * gFun q = κ * ((1 - q ^ 2) * artanh q) := by
    unfold gFun; field_simp
  have e2 : κ * q * gFun (κ * q) = (1 - (κ * q) ^ 2) * artanh (κ * q) := by
    unfold gFun; field_simp
  rwa [e1, e2] at h2

/-- The same, in the form `g(q) < g(κq)`: shrinking a bias by a factor `κ < 1`
strictly increases the profile `g`. -/
theorem gFun_lt_gFun_mul {κ q : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    gFun q < gFun (κ * q) :=
  gFun_strictAntiOn ⟨mul_pos hκ0 hq0, by nlinarith⟩ ⟨hq0, hq1⟩ (by nlinarith)


/-! ## Towards concavity: the rate-derivative ratio

Along the parametrization `u = f_e(q)`, the curve `u ↦ f_e(κq)` has slope
`κ·L(κq)/L(q)`.  So concavity of `Θ_κ` is exactly the statement that

```
mglRatio κ q = artanh (κq) / artanh q
```

is decreasing in `q`, which by the computation above is `mgl_bias`.  Working
with `mglRatio` lets us avoid ever constructing `f_e⁻¹`. -/

lemma hasDerivAt_artanh_mul {k t : ℝ} (h0 : -1 < k * t) (h1 : k * t < 1) :
    HasDerivAt (fun s : ℝ => artanh (k * s)) (k / (1 - (k * t) ^ 2)) t := by
  have hp : (1 : ℝ) + k * t ≠ 0 := by linarith
  have hm : (1 : ℝ) - k * t ≠ 0 := by linarith
  have hk : HasDerivAt (fun s : ℝ => k * s) k t := by simpa using (hasDerivAt_id t).const_mul k
  have ha : HasDerivAt (fun s : ℝ => 1 + k * s) k t := by simpa using hk.const_add 1
  have hb : HasDerivAt (fun s : ℝ => 1 - k * s) (-k) t := by simpa using hk.const_sub 1
  have h := ((ha.log hp).sub (hb.log hm)).div_const 2
  have heq : (k / (1 + k * t) - -k / (1 - k * t)) / 2 = k / (1 - (k * t) ^ 2) := by
    rw [show (1 : ℝ) - (k * t) ^ 2 = (1 + k * t) * (1 - k * t) by ring]
    field_simp; ring
  rw [heq] at h
  have hopen : IsOpen {s : ℝ | k * s ∈ Ioo (-1 : ℝ) 1} :=
    isOpen_Ioo.preimage (continuous_const.mul continuous_id)
  have hmem : t ∈ {s : ℝ | k * s ∈ Ioo (-1 : ℝ) 1} := ⟨h0, h1⟩
  have hev : (fun s : ℝ => artanh (k * s)) =ᶠ[nhds t]
      fun s : ℝ => (log (1 + k * s) - log (1 - k * s)) / 2 := by
    filter_upwards [hopen.mem_nhds hmem] with s hs
    exact artanh_eq_log_sub hs.1 hs.2
  exact h.congr_of_eventuallyEq hev

lemma hasDerivAt_fe_mul {k t : ℝ} (h0 : -1 < k * t) (h1 : k * t < 1) :
    HasDerivAt (fun s : ℝ => fe (k * s)) (artanh (k * t) * k) t := by
  have hp : (1 : ℝ) + k * t ≠ 0 := by linarith
  have hm : (1 : ℝ) - k * t ≠ 0 := by linarith
  have hk : HasDerivAt (fun s : ℝ => k * s) k t := by simpa using (hasDerivAt_id t).const_mul k
  have ha : HasDerivAt (fun s : ℝ => 1 + k * s) k t := by simpa using hk.const_add 1
  have hb : HasDerivAt (fun s : ℝ => 1 - k * s) (-k) t := by simpa using hk.const_sub 1
  have d1 : HasDerivAt (fun s : ℝ => (1 + k * s) * log (1 + k * s))
      (k * log (1 + k * t) + k) t := by
    have h := ha.mul (ha.log hp)
    have heq : k * log (1 + k * t) + (1 + k * t) * (k / (1 + k * t))
        = k * log (1 + k * t) + k := by field_simp
    rwa [heq] at h
  have d2 : HasDerivAt (fun s : ℝ => (1 - k * s) * log (1 - k * s))
      (-k * log (1 - k * t) - k) t := by
    have h := hb.mul (hb.log hm)
    have heq : -k * log (1 - k * t) + (1 - k * t) * (-k / (1 - k * t))
        = -k * log (1 - k * t) - k := by field_simp; ring
    rwa [heq] at h
  have h := (d1.add d2).div_const 2
  have heq : (k * log (1 + k * t) + k + (-k * log (1 - k * t) - k)) / 2
      = artanh (k * t) * k := by
    rw [artanh_eq_log_sub h0 h1]; ring
  rwa [heq] at h


/-- The slope of the curve `u = f_e(q) ↦ f_e(κq)` is `κ · mglRatio κ q`. -/
noncomputable def mglRatio (κ q : ℝ) : ℝ := artanh (κ * q) / artanh q

lemma hasDerivAt_mglRatio {κ q : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (mglRatio κ)
      ((κ / (1 - (κ * q) ^ 2) * artanh q - artanh (κ * q) * (1 / (1 - q ^ 2)))
        / artanh q ^ 2) q := by
  have hkq0 : (-1 : ℝ) < κ * q := by nlinarith
  have hkq1 : κ * q < 1 := by nlinarith
  have hLq : artanh q ≠ 0 := ne_of_gt (Real.artanh_pos ⟨hq0, hq1⟩)
  exact (hasDerivAt_artanh_mul hkq0 hkq1).fun_div (hasDerivAt_artanh (by linarith) hq1) hLq

/-- **`mglRatio` is strictly decreasing** — equivalently, `Θ_κ` is strictly
concave.  This is exactly `mgl_bias`. -/
theorem mglRatio_strictAntiOn {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    StrictAntiOn (mglRatio κ) (Ioo (0:ℝ) 1) := by
  refine strictAntiOn_Ioo_of_deriv_neg _
    (fun q => (κ / (1 - (κ * q) ^ 2) * artanh q - artanh (κ * q) * (1 / (1 - q ^ 2)))
      / artanh q ^ 2) (fun q hq => hasDerivAt_mglRatio hκ0 hκ1 hq.1 hq.2) ?_
  intro q hq
  have hq0 := hq.1
  have hq1 := hq.2
  have hkq0 : 0 < κ * q := mul_pos hκ0 hq0
  have hkq1 : κ * q < 1 := by nlinarith
  have hd1 : 0 < 1 - q ^ 2 := by nlinarith
  have hd2 : 0 < 1 - (κ * q) ^ 2 := by nlinarith
  have hLq : 0 < artanh q := Real.artanh_pos ⟨hq0, hq1⟩
  have hkey := mgl_bias hκ0 hκ1 hq0 hq1
  have h1ne : (1 : ℝ) - q ^ 2 ≠ 0 := ne_of_gt hd1
  have h2ne : (1 : ℝ) - (κ * q) ^ 2 ≠ 0 := ne_of_gt hd2
  have h2ne' : (1 : ℝ) - κ ^ 2 * q ^ 2 ≠ 0 := by
    rw [show (1 : ℝ) - κ ^ 2 * q ^ 2 = 1 - (κ * q) ^ 2 from by ring]; exact h2ne
  have hrw : κ / (1 - (κ * q) ^ 2) * artanh q - artanh (κ * q) * (1 / (1 - q ^ 2))
      = (κ * artanh q * (1 - q ^ 2) - artanh (κ * q) * (1 - (κ * q) ^ 2))
        / ((1 - (κ * q) ^ 2) * (1 - q ^ 2)) := by
    field_simp
  have hnum : κ / (1 - (κ * q) ^ 2) * artanh q - artanh (κ * q) * (1 / (1 - q ^ 2)) < 0 := by
    rw [hrw]
    exact div_neg_of_neg_of_pos (by nlinarith [hkey]) (mul_pos hd2 hd1)
  exact div_neg_of_neg_of_pos hnum (by positivity)

/-! ## Concavity as a chord bound, and Jensen -/

/-- `H(q) = f_e(κq) − α·f_e(q)`, the curve minus a chord slope. -/
noncomputable def mglH (κ α q : ℝ) : ℝ := fe (κ * q) - α * fe q

lemma hasDerivAt_mglH {κ α q : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasDerivAt (mglH κ α) (artanh (κ * q) * κ - α * artanh q) q := by
  have hkq0 : (-1 : ℝ) < κ * q := by nlinarith
  have hkq1 : κ * q < 1 := by nlinarith
  exact (hasDerivAt_fe_mul hkq0 hkq1).sub
    (((hasDerivAt_fe (by linarith) hq1)).const_mul α)

/-- `f_e` is strictly increasing on `[0,1)`, so a rate determines a bias. -/
theorem fe_strictMonoOn : StrictMonoOn fe (Ico (0:ℝ) 1) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := artanh) (convex_Ico 0 1)
    (fun z hz => ContinuousAt.continuousWithinAt
      (hasDerivAt_fe (by linarith [hz.1]) hz.2).continuousAt) ?_ ?_
  · rw [interior_Ico]
    exact fun z hz => (hasDerivAt_fe (by linarith [hz.1]) hz.2).hasDerivWithinAt
  · rw [interior_Ico]; exact fun z hz => Real.artanh_pos hz

lemma mglH_deriv_nonneg_iff {κ α x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 ≤ artanh (κ * x) * κ - α * artanh x ↔ α ≤ κ * mglRatio κ x := by
  have hL : 0 < artanh x := Real.artanh_pos ⟨hx0, hx1⟩
  rw [mglRatio, ← mul_div_assoc, le_div_iff₀ hL, sub_nonneg]
  constructor <;> intro h <;> linarith

/-- **The curve lies above its chords.**  With `α` the chord slope, `H` equals
its endpoint values at `q₁, q₂` and is `≥` them throughout `[q₁,q₂]`: `H′(x)` has
the sign of `κ·mglRatio κ x − α`, which by `mglRatio_strictAntiOn` changes at
most once, from `+` to `−`. -/
theorem mglH_ge_of_mem {κ α q₁ q₂ q : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hq1 : 0 < q₁) (hq2 : q₂ < 1)
    (hend : mglH κ α q₁ = mglH κ α q₂) (hq : q ∈ Icc q₁ q₂) :
    mglH κ α q₁ ≤ mglH κ α q := by
  have hq0 : 0 < q := lt_of_lt_of_le hq1 hq.1
  have hqlt : q < 1 := lt_of_le_of_lt hq.2 hq2
  have hcont : ∀ a b : ℝ, 0 < a → b < 1 → ContinuousOn (mglH κ α) (Icc a b) := by
    intro a b ha hb x hx
    simp only [mem_Icc] at hx
    have hc : ContinuousAt (mglH κ α) x :=
      (hasDerivAt_mglH hκ0 hκ1 (by linarith [hx.1]) (by linarith [hx.2])).continuousAt
    exact hc.continuousWithinAt
  have hderiv : ∀ a b : ℝ, 0 < a → b < 1 → ∀ x ∈ interior (Icc a b),
      HasDerivWithinAt (mglH κ α) (artanh (κ * x) * κ - α * artanh x) (interior (Icc a b)) x := by
    intro a b ha hb x hx
    rw [interior_Icc] at hx
    simp only [mem_Ioo] at hx
    exact (hasDerivAt_mglH hκ0 hκ1 (by linarith [hx.1]) (by linarith [hx.2])).hasDerivWithinAt
  rcases le_or_gt α (κ * mglRatio κ q) with hcase | hcase
  · -- `H` increases on `[q₁, q]`
    have hmono : MonotoneOn (mglH κ α) (Icc q₁ q) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc q₁ q)
        (hcont q₁ q hq1 hqlt) (hderiv q₁ q hq1 hqlt) ?_
      intro x hx
      rw [interior_Icc] at hx
      simp only [mem_Ioo] at hx
      have hx0 : 0 < x := lt_trans hq1 hx.1
      have hx1 : x < 1 := lt_trans hx.2 hqlt
      rw [mglH_deriv_nonneg_iff hx0 hx1]
      have := mglRatio_strictAntiOn hκ0 hκ1 ⟨hx0, hx1⟩ ⟨hq0, hqlt⟩ hx.2
      nlinarith
    exact hmono (left_mem_Icc.mpr hq.1) (right_mem_Icc.mpr hq.1) hq.1
  · -- `H` decreases on `[q, q₂]`
    have hanti : AntitoneOn (mglH κ α) (Icc q q₂) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc q q₂)
        (hcont q q₂ hq0 hq2) (hderiv q q₂ hq0 hq2) ?_
      intro x hx
      rw [interior_Icc] at hx
      simp only [mem_Ioo] at hx
      have hx0 : 0 < x := lt_trans hq0 hx.1
      have hx1 : x < 1 := lt_trans hx.2 hq2
      have hnot : ¬ (α ≤ κ * mglRatio κ x) := by
        have := mglRatio_strictAntiOn hκ0 hκ1 ⟨hq0, hqlt⟩ ⟨hx0, hx1⟩ hx.1
        nlinarith
      have := (mglH_deriv_nonneg_iff (κ := κ) (α := α) hx0 hx1).not.mpr hnot
      linarith [not_le.mp this]
    have := hanti (left_mem_Icc.mpr hq.2) (right_mem_Icc.mpr hq.2) hq.2
    linarith [hend]

/-- **Mrs. Gerber's Lemma, Jensen form.**  If `t` has the average rate of `q₁`
and `q₂`, then shrinking all three biases by `κ` gives
`w₁f_e(κq₁) + w₂f_e(κq₂) ≤ f_e(κt)`.  This is `Σ_T ≥ 0` of `NOTES.md` §5g, and it
never constructs `f_e⁻¹`.  (`q₁ ≤ t ≤ q₂` follows from `hmatch` and
`fe_strictMonoOn`.) -/
theorem mgl_jensen {κ q₁ q₂ t w₁ w₂ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hq1 : 0 < q₁) (hq2 : q₂ < 1) (ht1 : q₁ ≤ t) (ht2 : t ≤ q₂)
    (hsum : w₁ + w₂ = 1)
    (hmatch : w₁ * fe q₁ + w₂ * fe q₂ = fe t) :
    w₁ * fe (κ * q₁) + w₂ * fe (κ * q₂) ≤ fe (κ * t) := by
  have h12 : q₁ ≤ q₂ := le_trans ht1 ht2
  rcases eq_or_lt_of_le h12 with heq | hlt
  · have htq : t = q₁ := le_antisymm (heq ▸ ht2) ht1
    rw [htq, ← heq]
    have hone : w₁ * fe (κ * q₁) + w₂ * fe (κ * q₁) = fe (κ * q₁) := by
      linear_combination fe (κ * q₁) * hsum
    linarith
  · have hdiff : fe q₁ < fe q₂ :=
      fe_strictMonoOn ⟨le_of_lt hq1, lt_trans hlt hq2⟩ ⟨le_of_lt (lt_trans hq1 hlt), hq2⟩ hlt
    set α : ℝ := (fe (κ * q₂) - fe (κ * q₁)) / (fe q₂ - fe q₁) with hα
    have hne : fe q₂ - fe q₁ ≠ 0 := by linarith
    have hend : mglH κ α q₁ = mglH κ α q₂ := by
      simp only [mglH, hα]; field_simp; ring
    have hmain := mglH_ge_of_mem hκ0 hκ1 hq1 hq2 hend ⟨ht1, ht2⟩
    simp only [mglH] at hmain
    have hw1 : w₁ = 1 - w₂ := by linarith
    have hPt : fe t - fe q₁ = w₂ * (fe q₂ - fe q₁) := by
      rw [← hmatch, hw1]; ring
    have hαmul : α * (fe t - fe q₁) = w₂ * (fe (κ * q₂) - fe (κ * q₁)) := by
      rw [hPt, hα]; field_simp
    rw [hw1]
    linarith [hmain, hαmul]


/-! ### From `EvenOdd.lean` -/


/-! ## The even part is the trapezoid bound -/

/-- The even part of `η`, `η_e(z) = log(1−z²) + z·artanh z`. -/
noncomputable def etaEven (z : ℝ) : ℝ := log (1 - z ^ 2) + z * artanh z

/-- `η_e = 2f_e − z·artanh z`, so `η_e ≤ 0` is literally `f_e(z) ≤ z·artanh z/2`. -/
lemma etaEven_eq {z : ℝ} (h0 : -1 < z) (h1 : z < 1) :
    etaEven z = 2 * fe z - z * artanh z := by
  have hp : (1 : ℝ) + z ≠ 0 := by linarith
  have hm : (1 : ℝ) - z ≠ 0 := by linarith
  have hlog : log (1 - z ^ 2) = log (1 + z) + log (1 - z) := by
    rw [show (1 : ℝ) - z ^ 2 = (1 + z) * (1 - z) by ring, Real.log_mul hp hm]
  rw [etaEven, fe, artanh_eq_log_sub h0 h1, hlog]
  ring

/-- **The even part of `η` is non-positive**, pointwise on `(−1,1)`.  This is the
trapezoid bound `f_e(z) ≤ z·artanh z/2` (`fe_le_half_mul`) in disguise, and it is
the reason claim (A) is sharp exactly in the symmetric limit. -/
theorem etaEven_nonpos {z : ℝ} (h0 : -1 < z) (h1 : z < 1) : etaEven z ≤ 0 := by
  rcases lt_trichotomy z 0 with hz | hz | hz
  · -- `η_e` is even, so reduce to `−z > 0`
    have hP := fe_le_half_mul (y := -z) (by linarith) (by linarith)
    rw [fe_neg] at hP
    have harth : artanh (-z) = -artanh z := by
      rw [artanh_eq_log_sub (by linarith) (by linarith),
        artanh_eq_log_sub h0 h1, show (1:ℝ) + -z = 1 - z by ring,
        show (1:ℝ) - -z = 1 + z by ring]
      ring
    rw [harth] at hP
    rw [etaEven_eq h0 h1]
    nlinarith [hP]
  · subst hz; simp [etaEven, Real.artanh_zero]
  · have hP := fe_le_half_mul hz h1
    rw [etaEven_eq h0 h1]
    linarith

/-! ## The odd part -/

/-- The odd part of `η`, `η_o(z) = (1 + z/2)·log(1+z) − (1 − z/2)·log(1−z) − 2z`. -/
noncomputable def etaOdd (z : ℝ) : ℝ :=
  (1 + z / 2) * log (1 + z) - (1 - z / 2) * log (1 - z) - 2 * z

/-- `η_o` is odd. -/
lemma etaOdd_neg (z : ℝ) : etaOdd (-z) = -etaOdd z := by
  simp only [etaOdd]
  rw [show (1 : ℝ) + -z = 1 - z by ring, show (1 : ℝ) - -z = 1 + z by ring]
  ring

/-- The two parts reassemble `η(z) = (2+z)·log(1+z) − 2z`. -/
theorem etaEven_add_etaOdd {z : ℝ} (h0 : -1 < z) (h1 : z < 1) :
    etaEven z + etaOdd z = (2 + z) * log (1 + z) - 2 * z := by
  have hp : (1 : ℝ) + z ≠ 0 := by linarith
  have hm : (1 : ℝ) - z ≠ 0 := by linarith
  have hlog : log (1 - z ^ 2) = log (1 + z) + log (1 - z) := by
    rw [show (1 : ℝ) - z ^ 2 = (1 + z) * (1 - z) by ring, Real.log_mul hp hm]
  rw [etaEven, etaOdd, artanh_eq_log_sub h0 h1, hlog]
  ring

/-- `η_o′(z) = ½·log(1−z²) + z²/(1−z²)`. -/
lemma hasDerivAt_etaOdd {z : ℝ} (h0 : -1 < z) (h1 : z < 1) :
    HasDerivAt etaOdd (log (1 - z ^ 2) / 2 + z ^ 2 / (1 - z ^ 2)) z := by
  have hp : (0 : ℝ) < 1 + z := by linarith
  have hm : (0 : ℝ) < 1 - z := by linarith
  have hlp : HasDerivAt (fun x : ℝ => log (1 + x)) (1 / (1 + z)) z := by
    have := ((hasDerivAt_id z).const_add 1).log (ne_of_gt hp)
    simpa using this
  have hlm : HasDerivAt (fun x : ℝ => log (1 - x)) (-1 / (1 - z)) z := by
    have := ((hasDerivAt_id z).const_sub 1).log (ne_of_gt hm)
    simpa using this
  have hA : HasDerivAt (fun x : ℝ => (1 + x / 2) * log (1 + x))
      (1 / 2 * log (1 + z) + (1 + z / 2) * (1 / (1 + z))) z :=
    (((hasDerivAt_id z).div_const 2).const_add 1).mul hlp
  have h1' : HasDerivAt (fun x : ℝ => 1 - x / 2) (-(1 / 2)) z := by
    simpa using ((hasDerivAt_id z).div_const 2).const_sub 1
  have hB : HasDerivAt (fun x : ℝ => (1 - x / 2) * log (1 - x))
      (-(1 / 2) * log (1 - z) + (1 - z / 2) * (-1 / (1 - z))) z := h1'.mul hlm
  have hC : HasDerivAt (fun x : ℝ => 2 * x) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℝ)
  have h := (hA.sub hB).sub hC
  have hlog : log (1 - z ^ 2) = log (1 + z) + log (1 - z) := by
    rw [show (1 : ℝ) - z ^ 2 = (1 + z) * (1 - z) by ring,
      Real.log_mul (ne_of_gt hp) (ne_of_gt hm)]
  have hpne : (1 : ℝ) + z ≠ 0 := ne_of_gt hp
  have hmne : (1 : ℝ) - z ≠ 0 := ne_of_gt hm
  have heq : 1 / 2 * log (1 + z) + (1 + z / 2) * (1 / (1 + z))
      - (-(1 / 2) * log (1 - z) + (1 - z / 2) * (-1 / (1 - z))) - 2
      = log (1 - z ^ 2) / 2 + z ^ 2 / (1 - z ^ 2) := by
    rw [hlog, show (1 : ℝ) - z ^ 2 = (1 + z) * (1 - z) by ring]
    field_simp
    ring
  rwa [heq] at h

/-! ## The analytic core: `T > 0` -/

/-- `T(z) = 2·artanh z − 2z/(1−z²) + 2z³/(1−z²)²`.  Positivity of `T` is exactly
supermodularity of the odd kernel of `η_o`. -/
noncomputable def TFun (z : ℝ) : ℝ :=
  2 * artanh z - 2 * z / (1 - z ^ 2) + 2 * z ^ 3 / (1 - z ^ 2) ^ 2

/-- **The logarithms cancel**: `T′(z) = 2(z² + 3z⁴)/(1−z²)³`, a rational
function.  This is the whole content of claim (A)'s odd half. -/
lemma hasDerivAt_TFun {z : ℝ} (h0 : -1 < z) (h1 : z < 1) :
    HasDerivAt TFun (2 * (z ^ 2 + 3 * z ^ 4) / (1 - z ^ 2) ^ 3) z := by
  have hne : (1 : ℝ) - z ^ 2 ≠ 0 := by nlinarith
  have hsq : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * z)) z := by
    simpa using ((hasDerivAt_pow 2 z).const_sub 1)
  have hA : HasDerivAt (fun x : ℝ => 2 * artanh x) (2 * (1 / (1 - z ^ 2))) z :=
    (hasDerivAt_artanh h0 h1).const_mul 2
  have hB : HasDerivAt (fun x : ℝ => 2 * x / (1 - x ^ 2))
      ((2 * (1 - z ^ 2) - 2 * z * -(2 * z)) / (1 - z ^ 2) ^ 2) z := by
    have hnum : HasDerivAt (fun x : ℝ => 2 * x) 2 z := by
      simpa using (hasDerivAt_id z).const_mul (2 : ℝ)
    exact hnum.fun_div hsq hne
  have hC : HasDerivAt (fun x : ℝ => 2 * x ^ 3 / (1 - x ^ 2) ^ 2)
      ((2 * (3 * z ^ 2) * (1 - z ^ 2) ^ 2
        - 2 * z ^ 3 * (2 * (1 - z ^ 2) ^ 1 * -(2 * z))) / ((1 - z ^ 2) ^ 2) ^ 2) z := by
    have hnum : HasDerivAt (fun x : ℝ => 2 * x ^ 3) (2 * (3 * z ^ 2)) z := by
      simpa using (hasDerivAt_pow 3 z).const_mul (2 : ℝ)
    have hden : HasDerivAt (fun x : ℝ => (1 - x ^ 2) ^ 2)
        (2 * (1 - z ^ 2) ^ 1 * -(2 * z)) z := hsq.pow 2
    exact hnum.fun_div hden (pow_ne_zero 2 hne)
  have h := (hA.sub hB).add hC
  have heq : 2 * (1 / (1 - z ^ 2)) - (2 * (1 - z ^ 2) - 2 * z * -(2 * z)) / (1 - z ^ 2) ^ 2
      + (2 * (3 * z ^ 2) * (1 - z ^ 2) ^ 2
        - 2 * z ^ 3 * (2 * (1 - z ^ 2) ^ 1 * -(2 * z))) / ((1 - z ^ 2) ^ 2) ^ 2
      = 2 * (z ^ 2 + 3 * z ^ 4) / (1 - z ^ 2) ^ 3 := by
    field_simp
    ring
  rw [heq] at h
  exact h

/-- **`T > 0` on `(0,1)`.**  `T(0) = 0` and `T′ > 0`. -/
theorem TFun_pos {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) : 0 < TFun z := by
  have hzero : TFun 0 = 0 := by simp [TFun, Real.artanh_zero]
  have hmono : StrictMonoOn TFun (Ico (0:ℝ) 1) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun z =>
      2 * (z ^ 2 + 3 * z ^ 4) / (1 - z ^ 2) ^ 3) (convex_Ico 0 1) ?_ ?_ ?_
    · intro x hx
      exact ((hasDerivAt_TFun (by linarith [hx.1]) hx.2).continuousAt).continuousWithinAt
    · rw [interior_Ico]
      exact fun x hx => (hasDerivAt_TFun (by linarith [hx.1]) hx.2).hasDerivWithinAt
    · rw [interior_Ico]
      intro x hx
      have hx0 : 0 < x := hx.1
      have hb : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
      have hden : 0 < (1 - x ^ 2) ^ 3 := pow_pos hb 3
      have hnum : 0 < 2 * (x ^ 2 + 3 * x ^ 4) := by positivity
      exact div_pos hnum hden
  have := hmono (left_mem_Ico.mpr one_pos) ⟨le_of_lt hz0, hz1⟩ hz0
  rwa [hzero] at this

/-! ## The odd kernel and its supermodularity -/

/-- `η_o(k·s)` differentiated in `s`. -/
lemma hasDerivAt_etaOdd_mul {k t : ℝ} (h0 : -1 < k * t) (h1 : k * t < 1) :
    HasDerivAt (fun s : ℝ => etaOdd (k * s))
      ((log (1 - (k * t) ^ 2) / 2 + (k * t) ^ 2 / (1 - (k * t) ^ 2)) * k) t := by
  have hp : (0 : ℝ) < 1 + k * t := by linarith
  have hm : (0 : ℝ) < 1 - k * t := by linarith
  have hk : HasDerivAt (fun s : ℝ => k * s) k t := by simpa using (hasDerivAt_id t).const_mul k
  have ha : HasDerivAt (fun s : ℝ => 1 + k * s) k t := by simpa using hk.const_add 1
  have hb : HasDerivAt (fun s : ℝ => 1 - k * s) (-k) t := by simpa using hk.const_sub 1
  have hha : HasDerivAt (fun s : ℝ => 1 + k * s / 2) (k / 2) t := by
    have := (hk.div_const 2).const_add 1
    simpa using this
  have hhb : HasDerivAt (fun s : ℝ => 1 - k * s / 2) (-(k / 2)) t := by
    have := (hk.div_const 2).const_sub 1
    simpa using this
  have d1 : HasDerivAt (fun s : ℝ => (1 + k * s / 2) * log (1 + k * s))
      (k / 2 * log (1 + k * t) + (1 + k * t / 2) * (k / (1 + k * t))) t :=
    hha.mul (ha.log (ne_of_gt hp))
  have d2 : HasDerivAt (fun s : ℝ => (1 - k * s / 2) * log (1 - k * s))
      (-(k / 2) * log (1 - k * t) + (1 - k * t / 2) * (-k / (1 - k * t))) t :=
    hhb.mul (hb.log (ne_of_gt hm))
  have d3 : HasDerivAt (fun s : ℝ => 2 * (k * s)) (2 * k) t := by
    simpa using hk.const_mul (2 : ℝ)
  have h : HasDerivAt (fun s : ℝ => etaOdd (k * s))
      (k / 2 * log (1 + k * t) + (1 + k * t / 2) * (k / (1 + k * t))
        - (-(k / 2) * log (1 - k * t) + (1 - k * t / 2) * (-k / (1 - k * t))) - 2 * k) t := by
    simpa only [etaOdd] using (d1.fun_sub d2).fun_sub d3
  have hlog : log (1 - (k * t) ^ 2) = log (1 + k * t) + log (1 - k * t) := by
    rw [show (1 : ℝ) - (k * t) ^ 2 = (1 + k * t) * (1 - k * t) by ring,
      Real.log_mul (ne_of_gt hp) (ne_of_gt hm)]
  have heq : k / 2 * log (1 + k * t) + (1 + k * t / 2) * (k / (1 + k * t))
      - (-(k / 2) * log (1 - k * t) + (1 - k * t / 2) * (-k / (1 - k * t))) - 2 * k
      = (log (1 - (k * t) ^ 2) / 2 + (k * t) ^ 2 / (1 - (k * t) ^ 2)) * k := by
    rw [hlog, show (1 : ℝ) - (k * t) ^ 2 = (1 + k * t) * (1 - k * t) by ring]
    field_simp
    ring
  rwa [heq] at h

/-- The analogue of `fo_sub_mul_deriv`: `z·η_o′(z) − η_o(z) = 2z − 2·artanh z +
z³/(1−z²)`.  The logarithms cancel. -/
lemma etaOdd_deriv_sub {z : ℝ} (h0 : -1 < z) (h1 : z < 1) :
    z * (log (1 - z ^ 2) / 2 + z ^ 2 / (1 - z ^ 2)) - etaOdd z
      = 2 * z - 2 * artanh z + z ^ 3 / (1 - z ^ 2) := by
  have hp : (0 : ℝ) < 1 + z := by linarith
  have hm : (0 : ℝ) < 1 - z := by linarith
  have hlog : log (1 - z ^ 2) = log (1 + z) + log (1 - z) := by
    rw [show (1 : ℝ) - z ^ 2 = (1 + z) * (1 - z) by ring,
      Real.log_mul (ne_of_gt hp) (ne_of_gt hm)]
  rw [etaOdd, artanh_eq_log_sub h0 h1, hlog,
    show (1 : ℝ) - z ^ 2 = (1 + z) * (1 - z) by ring]
  field_simp
  ring

/-- `K(z) = (2z − 2·artanh z + z³/(1−z²))/z`.  This is `u·v′(u)` transported to
the `z = δu` variable. -/
noncomputable def KFun (z : ℝ) : ℝ :=
  (2 * z - 2 * artanh z + z ^ 3 / (1 - z ^ 2)) / z

lemma hasDerivAt_KFun {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt KFun (TFun z / z ^ 2) z := by
  have hne : (1 : ℝ) - z ^ 2 ≠ 0 := by nlinarith
  have h0 : (-1 : ℝ) < z := by linarith
  have hsq : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * z)) z := by
    simpa using ((hasDerivAt_pow 2 z).const_sub 1)
  have hP : HasDerivAt (fun x : ℝ => 2 * x - 2 * artanh x + x ^ 3 / (1 - x ^ 2))
      (2 - 2 * (1 / (1 - z ^ 2))
        + (3 * z ^ 2 * (1 - z ^ 2) - z ^ 3 * -(2 * z)) / (1 - z ^ 2) ^ 2) z := by
    have h1' : HasDerivAt (fun x : ℝ => 2 * x) 2 z := by
      simpa using (hasDerivAt_id z).const_mul (2 : ℝ)
    have h2' : HasDerivAt (fun x : ℝ => 2 * artanh x) (2 * (1 / (1 - z ^ 2))) z :=
      (hasDerivAt_artanh h0 hz1).const_mul 2
    have h3' : HasDerivAt (fun x : ℝ => x ^ 3 / (1 - x ^ 2))
        ((3 * z ^ 2 * (1 - z ^ 2) - z ^ 3 * -(2 * z)) / (1 - z ^ 2) ^ 2) z :=
      (hasDerivAt_pow 3 z).fun_div hsq hne
    simpa using (h1'.fun_sub h2').fun_add h3'
  have h := hP.fun_div (hasDerivAt_id' (x := z)) (ne_of_gt hz0)
  have heq : ((2 - 2 * (1 / (1 - z ^ 2))
        + (3 * z ^ 2 * (1 - z ^ 2) - z ^ 3 * -(2 * z)) / (1 - z ^ 2) ^ 2) * z
      - (2 * z - 2 * artanh z + z ^ 3 / (1 - z ^ 2)) * 1) / z ^ 2
      = TFun z / z ^ 2 := by
    simp only [TFun]
    field_simp
    ring
  rwa [heq] at h

/-- **`K` is strictly increasing on `(0,1)`** — this is supermodularity of the
odd kernel, and it is exactly `TFun_pos`. -/
theorem KFun_strictMonoOn : StrictMonoOn KFun (Ioo (0:ℝ) 1) := by
  refine strictMonoOn_Ioo_of_deriv_pos _ (fun z => TFun z / z ^ 2) ?_ ?_
  · exact fun z hz => hasDerivAt_KFun hz.1 hz.2
  · exact fun z hz => div_pos (TFun_pos hz.1 hz.2) (pow_pos hz.1 2)

/-- The odd kernel `v(u) = η_o(δu)/u`. -/
noncomputable def vFun (δ u : ℝ) : ℝ := etaOdd (δ * u) / u

/-- `N(u) = u·v′(u)`, in closed form via `etaOdd_deriv_sub`. -/
noncomputable def NFun (δ u : ℝ) : ℝ :=
  (2 * (δ * u) - 2 * artanh (δ * u) + (δ * u) ^ 3 / (1 - (δ * u) ^ 2)) / u

lemma NFun_eq {δ u : ℝ} (hδ : δ ≠ 0) (hu : u ≠ 0) : NFun δ u = δ * KFun (δ * u) := by
  simp only [NFun, KFun]
  field_simp

theorem NFun_strictMonoOn {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    StrictMonoOn (NFun δ) (Ioc (0:ℝ) 1) := by
  intro u hu v hv huv
  have hmem : ∀ {r : ℝ}, r ∈ Ioc (0:ℝ) 1 → δ * r ∈ Ioo (0:ℝ) 1 := by
    intro r hr
    exact ⟨mul_pos hδ0 hr.1, by nlinarith [hr.1, hr.2]⟩
  have h := KFun_strictMonoOn (hmem hu) (hmem hv) (by nlinarith [hu.1])
  rw [NFun_eq (ne_of_gt hδ0) (ne_of_gt hu.1), NFun_eq (ne_of_gt hδ0) (ne_of_gt hv.1)]
  have := mul_lt_mul_of_pos_left h hδ0
  linarith

/-- Derivative of the slice `s ↦ vFun δ (s·c)`. -/
lemma hasDerivAt_vFun_slice {δ c t : ℝ} (hδ0 : 0 < δ) (hc0 : 0 < c) (ht0 : 0 < t)
    (h1 : δ * (t * c) < 1) :
    HasDerivAt (fun s : ℝ => vFun δ (s * c)) (NFun δ (t * c) / (t * c) * c) t := by
  have htc : (0 : ℝ) < t * c := mul_pos ht0 hc0
  have hz0 : (-1 : ℝ) < δ * (t * c) := by nlinarith
  have hN : HasDerivAt (fun s : ℝ => etaOdd (δ * c * s))
      ((log (1 - (δ * c * t) ^ 2) / 2 + (δ * c * t) ^ 2 / (1 - (δ * c * t) ^ 2)) * (δ * c)) t :=
    hasDerivAt_etaOdd_mul (by nlinarith) (by nlinarith)
  rw [show δ * c * t = δ * (t * c) from by ring] at hN
  have hfun : (fun s : ℝ => etaOdd (δ * c * s)) = fun s : ℝ => etaOdd (δ * (s * c)) := by
    funext s; congr 1; ring
  rw [hfun] at hN
  have hD : HasDerivAt (fun s : ℝ => s * c) c t := by simpa using (hasDerivAt_id t).mul_const c
  have hv := hN.fun_div hD (ne_of_gt htc)
  have hkey := etaOdd_deriv_sub hz0 h1
  have hne : (1 : ℝ) - (δ * (t * c)) ^ 2 ≠ 0 := by nlinarith
  have heq : ((log (1 - (δ * (t * c)) ^ 2) / 2
        + (δ * (t * c)) ^ 2 / (1 - (δ * (t * c)) ^ 2)) * (δ * c) * (t * c)
      - etaOdd (δ * (t * c)) * c) / (t * c) ^ 2
      = NFun δ (t * c) / (t * c) * c := by
    simp only [NFun]
    rw [← hkey]
    field_simp
  rw [heq] at hv
  exact hv

/-- The slice `r ↦ v(r·c) − v(r·d)` is strictly increasing when `d < c`. -/
theorem vslice_strictMonoOn {δ c d : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hd0 : 0 < d) (hdc : d < c) (hc1 : c ≤ 1) :
    StrictMonoOn (fun r : ℝ => vFun δ (r * c) - vFun δ (r * d)) (Ioc (0:ℝ) 1) := by
  have hc0 : 0 < c := hd0.trans hdc
  have hd1 : d ≤ 1 := le_of_lt (hdc.trans_le hc1)
  refine strictMonoOn_Ioc_of_deriv_pos _
    (fun r => (NFun δ (r * c) - NFun δ (r * d)) / r) ?_ ?_
  · intro r hr
    have hr0 : 0 < r := hr.1
    have hrcle : r * c ≤ 1 := by nlinarith [hr.1, hr.2, hc0, hc1]
    have hrdle : r * d ≤ 1 := by nlinarith [hr.1, hr.2, hd0, hd1]
    have hrc1 : δ * (r * c) < 1 := by
      nlinarith [mul_nonneg (le_of_lt hδ0) (sub_nonneg.mpr hrcle)]
    have hrd1 : δ * (r * d) < 1 := by
      nlinarith [mul_nonneg (le_of_lt hδ0) (sub_nonneg.mpr hrdle)]
    have h := (hasDerivAt_vFun_slice hδ0 hc0 hr0 hrc1).sub
      (hasDerivAt_vFun_slice hδ0 hd0 hr0 hrd1)
    have heq : NFun δ (r * c) / (r * c) * c - NFun δ (r * d) / (r * d) * d
        = (NFun δ (r * c) - NFun δ (r * d)) / r := by
      field_simp
    rwa [heq] at h
  · intro r hr
    have hr0 : 0 < r := hr.1
    have hr1 : r ≤ 1 := le_of_lt hr.2
    have hmc : r * c ∈ Ioc (0:ℝ) 1 := ⟨mul_pos hr0 hc0, by nlinarith⟩
    have hmd : r * d ∈ Ioc (0:ℝ) 1 := ⟨mul_pos hr0 hd0, by nlinarith⟩
    have := NFun_strictMonoOn hδ0 hδ1 hmd hmc (by nlinarith)
    exact div_pos (by linarith) hr0

/-- **Strict supermodularity of the odd kernel of `η_o`.** -/
theorem vFun_mixed_diff_pos {δ a b c d : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hb0 : 0 < b) (hba : b < a) (ha1 : a ≤ 1)
    (hd0 : 0 < d) (hdc : d < c) (hc1 : c ≤ 1) :
    0 < vFun δ (a * c) - vFun δ (a * d) - (vFun δ (b * c) - vFun δ (b * d)) := by
  have hb1 : b ≤ 1 := le_of_lt (hba.trans_le ha1)
  have h : vFun δ (b * c) - vFun δ (b * d) < vFun δ (a * c) - vFun δ (a * d) :=
    vslice_strictMonoOn hδ0 hδ1 hd0 hdc hc1 ⟨hb0, hb1⟩ ⟨hb0.trans hba, ha1⟩ hba
  linarith

/-! ## The two-point statement -/

/-- `E[η_o(δ·S·T)]` for the two-point pair `S ∈ {a,−b}`, `T ∈ {c,−d}` with the
mean-zero weights, written out using that `η_o` is odd. -/
noncomputable def EtaOddTwoPoint (δ a b c d : ℝ) : ℝ :=
  (b * d * etaOdd (δ * (a * c)) - b * c * etaOdd (δ * (a * d))
    - a * d * etaOdd (δ * (b * c)) + a * c * etaOdd (δ * (b * d))) / ((a + b) * (c + d))

/-- `E[η_o] = λκ·Δ` with `λ = ab/(a+b)`, `κ = cd/(c+d)`.  Unlike `Ω`, there is no
sign flip here: `η_o` has **no linear part** (it starts at `z³`), so nothing is
subtracted off. -/
theorem etaOddTwoPoint_eq {δ a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    EtaOddTwoPoint δ a b c d
      = (a * b / (a + b)) * (c * d / (c + d))
        * (vFun δ (a * c) - vFun δ (a * d) - (vFun δ (b * c) - vFun δ (b * d))) := by
  have hab : a + b ≠ 0 := by positivity
  have hcd : c + d ≠ 0 := by positivity
  simp only [EtaOddTwoPoint, vFun]
  field_simp
  ring

/-- **The odd part is non-positive under opposite skews.**  If `b < a` but
`c < d` — the configuration `omegaTwoPoint_pos` forces at any maximizer — then
`E[η_o(δST)] < 0`. -/
theorem etaOddTwoPoint_neg {δ a b c d : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hb0 : 0 < b) (hba : b < a) (ha1 : a ≤ 1)
    (hc0 : 0 < c) (hcd : c < d) (hd1 : d ≤ 1) :
    EtaOddTwoPoint δ a b c d < 0 := by
  have ha0 : 0 < a := hb0.trans hba
  have hd0 : 0 < d := hc0.trans hcd
  have hΔ := vFun_mixed_diff_pos hδ0 hδ1 hb0 hba ha1 hc0 hcd hd1
  have hneg : vFun δ (a * c) - vFun δ (a * d) - (vFun δ (b * c) - vFun δ (b * d)) < 0 := by
    linarith
  rw [etaOddTwoPoint_eq ha0 hb0 hc0 hd0]
  exact mul_neg_of_pos_of_neg (mul_pos (by positivity) (by positivity)) hneg

/-- `I(U;V) − L(U;V) = E[(2+z)·log(1+z)]` for the two-point pair. -/
noncomputable def MutualSubLautum (δ a b c d : ℝ) : ℝ :=
  (b * d * ((2 + δ * (a * c)) * log (1 + δ * (a * c)))
    + b * c * ((2 - δ * (a * d)) * log (1 - δ * (a * d)))
    + a * d * ((2 - δ * (b * c)) * log (1 - δ * (b * c)))
    + a * c * ((2 + δ * (b * d)) * log (1 + δ * (b * d)))) / ((a + b) * (c + d))

/-- **Claim (A).**  For a two-point pair with **opposite skews** (`b < a` and
`c < d`), `I(U;V) ≤ L(U;V)`, i.e. `ρ(U;V) ≤ 1/2`.

Both halves are already in place: the even part of `η` is pointwise non-positive
by the trapezoid bound (`etaEven_nonpos`), and the odd part is negative by
supermodularity (`etaOddTwoPoint_neg`).  The hypothesis is exactly the
conclusion of the global sign-flip theorem `omegaTwoPoint_pos`, so it holds at
any maximizer; the bound is **false** without it (globally `sup ρ = 2 − 1/log 2
> 1/2`). -/
theorem mutual_le_lautum_of_opposite_skew {δ a b c d : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hb0 : 0 < b) (hba : b < a) (ha1 : a ≤ 1)
    (hc0 : 0 < c) (hcd : c < d) (hd1 : d ≤ 1) :
    MutualSubLautum δ a b c d < 0 := by
  have ha0 : 0 < a := hb0.trans hba
  have hd0 : 0 < d := hc0.trans hcd
  have hb1 : b ≤ 1 := le_of_lt (hba.trans_le ha1)
  have hc1 : c ≤ 1 := le_of_lt (hcd.trans_le hd1)
  -- every argument lies in `(−1,1)`
  have hbd : ∀ {x y : ℝ}, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 →
      (-1 : ℝ) < δ * (x * y) ∧ δ * (x * y) < 1 := by
    intro x y hx0 hx1 hy0 hy1
    have hxy : 0 < x * y := mul_pos hx0 hy0
    have hxy1 : x * y ≤ 1 := by nlinarith
    constructor
    · nlinarith
    · nlinarith
  obtain ⟨hac0, hac1⟩ := hbd ha0 ha1 hc0 hc1
  obtain ⟨had0, had1⟩ := hbd ha0 ha1 hd0 hd1
  obtain ⟨hbc0, hbc1⟩ := hbd hb0 hb1 hc0 hc1
  obtain ⟨hbd0, hbd1⟩ := hbd hb0 hb1 hd0 hd1
  -- `ξ(z) = η_e(z) + η_o(z) + 2z`, and the linear part cancels by mean-zero
  have hsplit : ∀ {z : ℝ}, -1 < z → z < 1 →
      (2 + z) * log (1 + z) = etaEven z + etaOdd z + 2 * z := by
    intro z h0 h1
    have := etaEven_add_etaOdd h0 h1
    linarith
  have hsplit' : ∀ {z : ℝ}, -1 < z → z < 1 →
      (2 - z) * log (1 - z) = etaEven z - etaOdd z - 2 * z := by
    intro z h0 h1
    have h := hsplit (z := -z) (by linarith) (by linarith)
    rw [show (1 : ℝ) + -z = 1 - z by ring, show (2 : ℝ) + -z = 2 - z by ring,
      etaOdd_neg] at h
    have heven : etaEven (-z) = etaEven z := by
      simp only [etaEven]
      rw [show (-z : ℝ) ^ 2 = z ^ 2 by ring]
      have harth : artanh (-z) = -artanh z := by
        rw [artanh_eq_log_sub (by linarith) (by linarith),
          artanh_eq_log_sub h0 h1, show (1:ℝ) + -z = 1 - z by ring,
          show (1:ℝ) - -z = 1 + z by ring]
        ring
      rw [harth]; ring
    rw [heven] at h
    linarith
  rw [MutualSubLautum, hsplit hac0 hac1, hsplit' had0 had1, hsplit' hbc0 hbc1,
    hsplit hbd0 hbd1]
  have hab : (0 : ℝ) < a + b := by linarith
  have hcd' : (0 : ℝ) < c + d := by linarith
  have hden : (0 : ℝ) < (a + b) * (c + d) := mul_pos hab hcd'
  rw [div_neg_iff]
  right
  refine ⟨?_, hden⟩
  -- the linear parts cancel; the even parts are ≤ 0; the odd part is < 0
  have hodd := etaOddTwoPoint_neg hδ0 hδ1 hb0 hba ha1 hc0 hcd hd1
  rw [EtaOddTwoPoint, div_neg_iff] at hodd
  have hoddnum : b * d * etaOdd (δ * (a * c)) - b * c * etaOdd (δ * (a * d))
      - a * d * etaOdd (δ * (b * c)) + a * c * etaOdd (δ * (b * d)) < 0 := by
    rcases hodd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h2 (not_lt.mpr (le_of_lt hden))
    · exact h1
  have e1 := etaEven_nonpos hac0 hac1
  have e2 := etaEven_nonpos had0 had1
  have e3 := etaEven_nonpos hbc0 hbc1
  have e4 := etaEven_nonpos hbd0 hbd1
  nlinarith [mul_nonneg (mul_nonneg (le_of_lt hb0) (le_of_lt hd0)) (neg_nonneg.mpr e1),
    mul_nonneg (mul_nonneg (le_of_lt hb0) (le_of_lt hc0)) (neg_nonneg.mpr e2),
    mul_nonneg (mul_nonneg (le_of_lt ha0) (le_of_lt hd0)) (neg_nonneg.mpr e3),
    mul_nonneg (mul_nonneg (le_of_lt ha0) (le_of_lt hc0)) (neg_nonneg.mpr e4)]


/-! ### From `SharpRho.lean` -/


/-! ## The constants -/

/-- `λ = 1/log 2 − 1`. -/
noncomputable def lamC : ℝ := 1 / Real.log 2 - 1

/-- The sharp constant `c₀ = 2 − 1/log 2`. -/
noncomputable def c0 : ℝ := 2 - 1 / Real.log 2

lemma c0_eq_one_sub_lamC : c0 = 1 - lamC := by unfold c0 lamC; ring

lemma log_two_pos' : (0:ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

lemma lamC_gt : (0.4426 : ℝ) < lamC := by
  have h := Real.log_two_lt_d9
  have hp := log_two_pos'
  have key : (1.4426 : ℝ) < 1 / Real.log 2 := by rw [lt_div_iff₀ hp]; nlinarith
  rw [lamC]; linarith

lemma lamC_lt : lamC < (0.4427 : ℝ) := by
  have h := Real.log_two_gt_d9
  have hp := log_two_pos'
  have key : 1 / Real.log 2 < (1.4427 : ℝ) := by rw [div_lt_iff₀ hp]; nlinarith
  rw [lamC]; linarith

lemma lamC_pos : 0 < lamC := by linarith [lamC_gt]

lemma two_lamC_lt_one : 2 * lamC < 1 := by linarith [lamC_lt]

lemma lamC_sq_add : 0 < lamC ^ 2 + 2 * lamC - 1 := by nlinarith [lamC_gt, lamC_lt]

/-- `ζ = (1−2λ)/λ²`, the point where `ψ′` changes sign on the positive side. -/
noncomputable def zetaC : ℝ := (1 - 2 * lamC) / lamC ^ 2

lemma zetaC_pos : 0 < zetaC := by
  rw [zetaC]
  exact div_pos (by linarith [two_lamC_lt_one]) (pow_pos lamC_pos 2)

lemma zetaC_lt_one : zetaC < 1 := by
  rw [zetaC, div_lt_one (pow_pos lamC_pos 2)]
  nlinarith [lamC_sq_add]

lemma one_add_lamC_mul_pos {z : ℝ} (h : -1 < z) : 0 < 1 + lamC * z := by
  nlinarith [lamC_pos, two_lamC_lt_one]

/-! ## The auxiliary function `ψ` -/

noncomputable def psiF (z : ℝ) : ℝ := Real.log (1 + z) - z / (1 + lamC * z)

@[simp] lemma psiF_zero : psiF 0 = 0 := by simp [psiF]

lemma psiF_one : psiF 1 = 0 := by
  have hp := log_two_pos'
  have h : (1:ℝ) + lamC * 1 = 1 / Real.log 2 := by rw [lamC]; ring
  rw [psiF, h, show (1:ℝ) + 1 = 2 by norm_num]
  field_simp
  ring

lemma hasDerivAt_psiF {z : ℝ} (h : -1 < z) :
    HasDerivAt psiF (1 / (1 + z) - 1 / (1 + lamC * z) ^ 2) z := by
  have hp : (1:ℝ) + z ≠ 0 := by linarith
  have hq : (0:ℝ) < 1 + lamC * z := one_add_lamC_mul_pos h
  have d1 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + z)) z := by
    have ha : HasDerivAt (fun t : ℝ => 1 + t) 1 z := by simpa using (hasDerivAt_id z).const_add 1
    simpa using ha.log hp
  have hden : HasDerivAt (fun t : ℝ => 1 + lamC * t) lamC z := by
    simpa using ((hasDerivAt_id z).const_mul lamC).const_add 1
  have d2 := (hasDerivAt_id' (x := z)).fun_div hden (ne_of_gt hq)
  have hnum : 1 * (1 + lamC * z) - z * lamC = 1 := by ring
  rw [hnum] at d2
  exact d1.sub d2

lemma psiF_deriv_nonneg {z : ℝ} (h : -1 < z)
    (hs : 0 ≤ z * (lamC ^ 2 * z + 2 * lamC - 1)) :
    0 ≤ 1 / (1 + z) - 1 / (1 + lamC * z) ^ 2 := by
  have hp : (0:ℝ) < 1 + z := by linarith
  have hq : (0:ℝ) < 1 + lamC * z := one_add_lamC_mul_pos h
  have hq2 : (0:ℝ) < (1 + lamC * z) ^ 2 := pow_pos hq 2
  have hrw : 1 / (1 + z) - 1 / (1 + lamC * z) ^ 2
      = ((1 + lamC * z) ^ 2 - (1 + z)) / ((1 + z) * (1 + lamC * z) ^ 2) := by
    rw [div_sub_div _ _ (ne_of_gt hp) (ne_of_gt hq2),
      show (1:ℝ) * (1 + lamC * z) ^ 2 - (1 + z) * 1 = (1 + lamC * z) ^ 2 - (1 + z) from by ring]
  rw [hrw]
  exact div_nonneg (by nlinarith [hs]) (le_of_lt (mul_pos hp hq2))

lemma psiF_deriv_nonpos {z : ℝ} (h : -1 < z)
    (hs : z * (lamC ^ 2 * z + 2 * lamC - 1) ≤ 0) :
    1 / (1 + z) - 1 / (1 + lamC * z) ^ 2 ≤ 0 := by
  have hp : (0:ℝ) < 1 + z := by linarith
  have hq : (0:ℝ) < 1 + lamC * z := one_add_lamC_mul_pos h
  have hq2 : (0:ℝ) < (1 + lamC * z) ^ 2 := pow_pos hq 2
  have hrw : 1 / (1 + z) - 1 / (1 + lamC * z) ^ 2
      = ((1 + lamC * z) ^ 2 - (1 + z)) / ((1 + z) * (1 + lamC * z) ^ 2) := by
    rw [div_sub_div _ _ (ne_of_gt hp) (ne_of_gt hq2),
      show (1:ℝ) * (1 + lamC * z) ^ 2 - (1 + z) * 1 = (1 + lamC * z) ^ 2 - (1 + z) from by ring]
  rw [hrw]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [hs]) (le_of_lt (mul_pos hp hq2))

/-! ## Monotonicity helpers on a closed interval -/

lemma monoOn_Icc (f f' : ℝ → ℝ) {p q : ℝ}
    (hd : ∀ x ∈ Icc p q, HasDerivAt f (f' x) x)
    (hs : ∀ x ∈ Ioo p q, 0 ≤ f' x) : MonotoneOn f (Icc p q) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Icc p q) ?_ ?_ ?_
  · intro x hx
    have hc : ContinuousAt f x := (hd x hx).continuousAt
    exact hc.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hd x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).hasDerivWithinAt
  · intro x hx; rw [interior_Icc] at hx; exact hs x hx

lemma antiOn_Icc (f f' : ℝ → ℝ) {p q : ℝ}
    (hd : ∀ x ∈ Icc p q, HasDerivAt f (f' x) x)
    (hs : ∀ x ∈ Ioo p q, f' x ≤ 0) : AntitoneOn f (Icc p q) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc p q) ?_ ?_ ?_
  · intro x hx
    have hc : ContinuousAt f x := (hd x hx).continuousAt
    exact hc.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hd x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).hasDerivWithinAt
  · intro x hx; rw [interior_Icc] at hx; exact hs x hx

/-! ## `ψ ≤ 0` -/

theorem psiF_nonpos {z : ℝ} (h0 : -1 < z) (h1 : z ≤ 1) : psiF z ≤ 0 := by
  have hdall : ∀ x : ℝ, -1 < x → HasDerivAt psiF
      (1 / (1 + x) - 1 / (1 + lamC * x) ^ 2) x := fun x hx => hasDerivAt_psiF hx
  rcases le_or_gt z 0 with hz | hz
  · -- `ψ` is increasing on `[z, 0]`, and `ψ 0 = 0`
    have hmono : MonotoneOn psiF (Icc z 0) := by
      refine monoOn_Icc psiF (fun x => 1 / (1 + x) - 1 / (1 + lamC * x) ^ 2)
        (fun x hx => hdall x (by linarith [hx.1])) ?_
      intro x hx
      refine psiF_deriv_nonneg (by linarith [hx.1]) ?_
      have hx0 : x ≤ 0 := le_of_lt hx.2
      nlinarith [lamC_pos, two_lamC_lt_one, sq_nonneg x, hx.1, h0]
    have := hmono (left_mem_Icc.mpr hz) (right_mem_Icc.mpr hz) hz
    simpa using this
  · rcases le_or_gt z zetaC with hzz | hzz
    · -- `ψ` is decreasing on `[0, z]`, and `ψ 0 = 0`
      have hanti : AntitoneOn psiF (Icc 0 z) := by
        refine antiOn_Icc psiF (fun x => 1 / (1 + x) - 1 / (1 + lamC * x) ^ 2)
          (fun x hx => hdall x (by linarith [hx.1])) ?_
        intro x hx
        refine psiF_deriv_nonpos (by linarith [hx.1]) ?_
        have hx0 : 0 ≤ x := le_of_lt hx.1
        have hxz : x ≤ zetaC := le_of_lt (lt_of_lt_of_le hx.2 hzz)
        have hkey : lamC ^ 2 * x + 2 * lamC - 1 ≤ 0 := by
          have : lamC ^ 2 * x ≤ lamC ^ 2 * zetaC :=
            mul_le_mul_of_nonneg_left hxz (le_of_lt (pow_pos lamC_pos 2))
          have hlne : lamC ≠ 0 := ne_of_gt lamC_pos
          have hz2 : lamC ^ 2 * zetaC = 1 - 2 * lamC := by
            rw [zetaC]; field_simp
          linarith [hz2 ▸ this]
        nlinarith [hx0, hkey]
      have := hanti (left_mem_Icc.mpr (le_of_lt hz)) (right_mem_Icc.mpr (le_of_lt hz))
        (le_of_lt hz)
      simpa using this
    · -- `ψ` is increasing on `[ζ, 1]`, and `ψ 1 = 0`
      have hz0 : 0 < zetaC := zetaC_pos
      have hmono : MonotoneOn psiF (Icc zetaC 1) := by
        refine monoOn_Icc psiF (fun x => 1 / (1 + x) - 1 / (1 + lamC * x) ^ 2)
          (fun x hx => hdall x (by linarith [hx.1, hz0])) ?_
        intro x hx
        refine psiF_deriv_nonneg (by linarith [hx.1, hz0]) ?_
        have hx0 : 0 < x := lt_of_lt_of_le hz0 (le_of_lt hx.1)
        have hkey : 0 ≤ lamC ^ 2 * x + 2 * lamC - 1 := by
          have hxz : zetaC ≤ x := le_of_lt hx.1
          have : lamC ^ 2 * zetaC ≤ lamC ^ 2 * x :=
            mul_le_mul_of_nonneg_left hxz (le_of_lt (pow_pos lamC_pos 2))
          have hlne : lamC ≠ 0 := ne_of_gt lamC_pos
          have hz2 : lamC ^ 2 * zetaC = 1 - 2 * lamC := by
            rw [zetaC]; field_simp
          linarith [hz2 ▸ this]
        nlinarith [hx0, hkey]
      have hmz : z ∈ Icc zetaC 1 := ⟨le_of_lt hzz, h1⟩
      have hm1 : (1:ℝ) ∈ Icc zetaC 1 := ⟨le_of_lt zetaC_lt_one, le_refl 1⟩
      have := hmono hmz hm1 h1
      rw [psiF_one] at this
      exact this

/-- **The pointwise inequality.**  `log(1+z)·(1 + λz) ≤ z` on `(−1,1]`, with
equality exactly at `z = 0` and `z = 1`. -/
theorem log_mul_one_add_lamC_le {z : ℝ} (h0 : -1 < z) (h1 : z ≤ 1) :
    Real.log (1 + z) * (1 + lamC * z) ≤ z := by
  have hq : (0:ℝ) < 1 + lamC * z := one_add_lamC_mul_pos h0
  have h := psiF_nonpos h0 h1
  rw [psiF, sub_nonpos, le_div_iff₀ hq] at h
  exact h

/-! ## (L1) for a four-atom law -/

/-- **(L1).**  For four points `z₁…z₄ ∈ (−1,1]` carrying non-negative weights of
mean zero, `I ≤ c₀ · 𝒥`.  The four atoms are the products `δ·s_i·t_j` of a
two-point pair, whose mean is `δ·E[S]·E[T] = 0`. -/
theorem mutual_le_c0_mul_jeffreys
    {z₁ z₂ z₃ z₄ w₁ w₂ w₃ w₄ : ℝ}
    (hz₁ : -1 < z₁) (hz₁' : z₁ ≤ 1) (hz₂ : -1 < z₂) (hz₂' : z₂ ≤ 1)
    (hz₃ : -1 < z₃) (hz₃' : z₃ ≤ 1) (hz₄ : -1 < z₄) (hz₄' : z₄ ≤ 1)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hw₄ : 0 ≤ w₄)
    (hmean : w₁ * z₁ + w₂ * z₂ + w₃ * z₃ + w₄ * z₄ = 0) :
    w₁ * ((1 + z₁) * Real.log (1 + z₁)) + w₂ * ((1 + z₂) * Real.log (1 + z₂))
        + w₃ * ((1 + z₃) * Real.log (1 + z₃)) + w₄ * ((1 + z₄) * Real.log (1 + z₄))
      ≤ c0 * (w₁ * (z₁ * Real.log (1 + z₁)) + w₂ * (z₂ * Real.log (1 + z₂))
        + w₃ * (z₃ * Real.log (1 + z₃)) + w₄ * (z₄ * Real.log (1 + z₄))) := by
  have key : ∀ {z : ℝ}, -1 < z → z ≤ 1 →
      (1 + z) * Real.log (1 + z) - c0 * (z * Real.log (1 + z)) ≤ z := by
    intro z hz hz'
    have h := log_mul_one_add_lamC_le hz hz'
    have hrw : (1 + z) * Real.log (1 + z) - c0 * (z * Real.log (1 + z))
        = Real.log (1 + z) * (1 + lamC * z) := by
      rw [c0_eq_one_sub_lamC]; ring
    rw [hrw]; exact h
  have b₁ := mul_le_mul_of_nonneg_left (key hz₁ hz₁') hw₁
  have b₂ := mul_le_mul_of_nonneg_left (key hz₂ hz₂') hw₂
  have b₃ := mul_le_mul_of_nonneg_left (key hz₃ hz₃') hw₃
  have b₄ := mul_le_mul_of_nonneg_left (key hz₄ hz₄') hw₄
  nlinarith [b₁, b₂, b₃, b₄, hmean]


/-! ### From `Contraction.lean` -/


/-! ## `w` is increasing -/

lemma hasDerivAt_wFun {δ t : ℝ} (hδ0 : 0 < δ) (ht0 : 0 < t) (h1 : δ * t < 1) :
    HasDerivAt (wFun δ) ((artanh (δ * t) - δ * t) / t ^ 2) t := by
  have h := hasDerivAt_wFun_slice hδ0 one_pos ht0 (by simpa using h1)
  simpa using h

/-- `w` is strictly increasing on `(0,1]`; its derivative is
`(artanh(δu) − δu)/u² > 0` by `self_lt_artanh`. -/
theorem wFun_strictMonoOn {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    StrictMonoOn (wFun δ) (Ioc (0:ℝ) 1) := by
  refine strictMonoOn_Ioc_of_deriv_pos _ (fun u => (artanh (δ * u) - δ * u) / u ^ 2) ?_ ?_
  · intro u hu
    exact hasDerivAt_wFun hδ0 hu.1
      (by nlinarith [mul_nonneg (le_of_lt hδ0) (sub_nonneg.mpr hu.2)])
  · intro u hu
    have hlt : δ * u < 1 := by nlinarith [hu.1, hu.2, hδ0, hδ1]
    have h := self_lt_artanh (mul_pos hδ0 hu.1) hlt
    exact div_pos (by linarith) (pow_pos hu.1 2)

/-! ## The odd part of the best-response objective -/

/-- `O(y) = w_c·fo(δcy) − w_d·fo(δdy)`, the odd part of
`G(y) = E_T f(δyT) − μf_e(y)` for `T ∈ {c,−d}`.  (The even part contributes
nothing to the skew, and `μ` drops out of `O` because `f_e` is even.) -/
noncomputable def oddPart (δ c d y : ℝ) : ℝ :=
  d / (c + d) * fo (δ * (c * y)) - c / (c + d) * fo (δ * (d * y))

/-- **`O(y) = κ·y·[w(dy) − w(cy)]`.**  The linear parts cancel because
`w_c·c = w_d·d = κ`; what is left is the genuinely nonlinear tilt. -/
theorem oddPart_eq {δ c d y : ℝ} (hc0 : 0 < c) (hd0 : 0 < d) (hy : y ≠ 0) :
    oddPart δ c d y = c * d / (c + d) * y * (wFun δ (d * y) - wFun δ (c * y)) := by
  have hcd : c + d ≠ 0 := by positivity
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hdne : d ≠ 0 := ne_of_gt hd0
  simp only [oddPart, wFun]
  field_simp
  ring

/-- The tilt has a definite sign: if `c < d` then `O(y) > 0` for `y > 0`.  So
the best response is pushed towards positive `y` — the global form of the sign
flip of `NOTES.md` §5c. -/
theorem oddPart_pos {δ c d y : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hc0 : 0 < c) (hcd : c < d) (hy0 : 0 < y) (hdy : d * y ≤ 1) :
    0 < oddPart δ c d y := by
  have hd0 : 0 < d := hc0.trans hcd
  have hcy : c * y < d * y := by nlinarith
  have hw := wFun_strictMonoOn hδ0 hδ1 ⟨mul_pos hc0 hy0, le_of_lt (hcy.trans_le hdy)⟩
    ⟨mul_pos hd0 hy0, hdy⟩ hcy
  rw [oddPart_eq hc0 hd0 (ne_of_gt hy0)]
  have hκ : 0 < c * d / (c + d) := by positivity
  have : 0 < wFun δ (d * y) - wFun δ (c * y) := by linarith
  positivity

/-! ## The skew force -/

/-- `∂V/∂v|_{v=0} = κ·[MFun(du) − MFun(cu)]`, the force pushing the best
response off symmetry. -/
noncomputable def forceFun (δ c d u : ℝ) : ℝ :=
  c * d / (c + d) * (MFun δ (d * u) - MFun δ (c * u))

/-- The derivative of `oddPart`. -/
noncomputable def oddPartDeriv (δ c d y : ℝ) : ℝ :=
  d / (c + d) * ((1 + log (1 - (δ * (c * y)) ^ 2) / 2) * (δ * c))
    - c / (c + d) * ((1 + log (1 - (δ * (d * y)) ^ 2) / 2) * (δ * d))

lemma oddPart_neg (δ c d y : ℝ) : oddPart δ c d (-y) = -oddPart δ c d y := by
  simp only [oddPart]
  rw [show δ * (c * -y) = -(δ * (c * y)) from by ring,
    show δ * (d * -y) = -(δ * (d * y)) from by ring, fo_neg, fo_neg]
  ring

lemma oddPartDeriv_neg (δ c d y : ℝ) : oddPartDeriv δ c d (-y) = oddPartDeriv δ c d y := by
  simp only [oddPartDeriv]
  rw [show (δ * (c * -y)) ^ 2 = (δ * (c * y)) ^ 2 from by ring,
    show (δ * (d * -y)) ^ 2 = (δ * (d * y)) ^ 2 from by ring]

lemma hasDerivAt_oddPart {δ c d y : ℝ}
    (hcy0 : -1 < δ * (c * y)) (hcy1 : δ * (c * y) < 1)
    (hdy0 : -1 < δ * (d * y)) (hdy1 : δ * (d * y) < 1) :
    HasDerivAt (oddPart δ c d) (oddPartDeriv δ c d y) y := by
  rw [oddPartDeriv]
  have hcfun : (fun s : ℝ => fo (δ * c * s)) = fun s : ℝ => fo (δ * (c * s)) := by
    funext s; congr 1; ring
  have hdfun : (fun s : ℝ => fo (δ * d * s)) = fun s : ℝ => fo (δ * (d * s)) := by
    funext s; congr 1; ring
  have hc : HasDerivAt (fun s : ℝ => fo (δ * (c * s)))
      ((1 + log (1 - (δ * (c * y)) ^ 2) / 2) * (δ * c)) y := by
    have h := hasDerivAt_fo_mul (k := δ * c) (t := y)
      (by rw [show δ * c * y = δ * (c * y) from by ring]; exact hcy0)
      (by rw [show δ * c * y = δ * (c * y) from by ring]; exact hcy1)
    rw [show δ * c * y = δ * (c * y) from by ring] at h
    rwa [hcfun] at h
  have hd : HasDerivAt (fun s : ℝ => fo (δ * (d * s)))
      ((1 + log (1 - (δ * (d * y)) ^ 2) / 2) * (δ * d)) y := by
    have h := hasDerivAt_fo_mul (k := δ * d) (t := y)
      (by rw [show δ * d * y = δ * (d * y) from by ring]; exact hdy0)
      (by rw [show δ * d * y = δ * (d * y) from by ring]; exact hdy1)
    rw [show δ * d * y = δ * (d * y) from by ring] at h
    rwa [hdfun] at h
  exact (hc.const_mul _).sub (hd.const_mul _)

/-- **`O′(u) − O(u)/u = κ·[MFun(du) − MFun(cu)]`.**  Pure algebra on top of
`fo_sub_mul_deriv`. -/
theorem oddPart_deriv_sub_eq {δ c d y : ℝ} (hc0 : 0 < c) (hd0 : 0 < d)
    (hy0 : 0 < y) (hcy0 : -1 < δ * (c * y)) (hcy1 : δ * (c * y) < 1)
    (hdy0 : -1 < δ * (d * y)) (hdy1 : δ * (d * y) < 1) :
    oddPartDeriv δ c d y - oddPart δ c d y / y = forceFun δ c d y := by
  rw [oddPartDeriv]
  have hcd : c + d ≠ 0 := by positivity
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hdne : d ≠ 0 := ne_of_gt hd0
  have hyne : y ≠ 0 := ne_of_gt hy0
  have hkc := fo_sub_mul_deriv hcy0 hcy1
  have hkd := fo_sub_mul_deriv hdy0 hdy1
  have hac : artanh (δ * (c * y))
      = fo (δ * (c * y)) - δ * (c * y) * (1 + log (1 - (δ * (c * y)) ^ 2) / 2)
        + δ * (c * y) := by linarith
  have had : artanh (δ * (d * y))
      = fo (δ * (d * y)) - δ * (d * y) * (1 + log (1 - (δ * (d * y)) ^ 2) / 2)
        + δ * (d * y) := by linarith
  simp only [oddPart, forceFun, MFun, hac, had]
  field_simp
  ring

/-- The force has a definite sign for **every** `u > 0`: if `c < d` it is
positive.  Immediate from `MFun_strictMonoOn`. -/
theorem forceFun_pos {δ c d u : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hc0 : 0 < c) (hcd : c < d) (hu0 : 0 < u) (hdu : d * u ≤ 1) :
    0 < forceFun δ c d u := by
  have hd0 : 0 < d := hc0.trans hcd
  have hcu : c * u < d * u := by nlinarith
  have hM := MFun_strictMonoOn hδ0 hδ1 ⟨mul_pos hc0 hu0, le_of_lt (hcu.trans_le hdu)⟩
    ⟨mul_pos hd0 hu0, hdu⟩ hcu
  have hκ : 0 < c * d / (c + d) := by positivity
  have : 0 < MFun δ (d * u) - MFun δ (c * u) := by linarith
  unfold forceFun
  positivity

/-! ## The two-atom value in centre / half-gap coordinates

A mean-zero two-point law with atoms `{v+u, v−u}` (`u > 0` the half-gap, `v` the
centre, so symmetry is `v = 0`) has weights `(u−v)/(2u)` and `(u+v)/(2u)`, hence
value

```
V(u,v) = [ (u−v)·G(v+u) + (u+v)·G(v−u) ] / (2u).
```

The best response is `max_{u,v} V`.  Below: the two partial derivatives, the
elimination showing that joint stationarity is equivalent to bitangency, and the
force `∂V/∂v|_{v=0}`. -/

/-- The value of the mean-zero two-point law with atoms `v ± u`. -/
noncomputable def envVal (G : ℝ → ℝ) (u v : ℝ) : ℝ :=
  ((u - v) * G (v + u) + (u + v) * G (v - u)) / (2 * u)

lemma hasDerivAt_envVal_v (G G' : ℝ → ℝ) {u v : ℝ}
    (h1 : HasDerivAt G (G' (v + u)) (v + u))
    (h2 : HasDerivAt G (G' (v - u)) (v - u)) :
    HasDerivAt (envVal G u)
      ((-G (v + u) + (u - v) * G' (v + u) + G (v - u) + (u + v) * G' (v - u)) / (2 * u)) v := by
  have hA : HasDerivAt (fun t : ℝ => G (t + u)) (G' (v + u)) v := h1.comp_add_const v u
  have hB : HasDerivAt (fun t : ℝ => G (t - u)) (G' (v - u)) v := h2.comp_sub_const v u
  have hp : HasDerivAt (fun t : ℝ => u - t) (-1) v := by simpa using (hasDerivAt_id v).const_sub u
  have hq : HasDerivAt (fun t : ℝ => u + t) 1 v := by simpa using (hasDerivAt_id v).const_add u
  have h := ((hp.mul hA).add (hq.mul hB)).div_const (2 * u)
  have heq : (-1 * G (v + u) + (u - v) * G' (v + u) + (1 * G (v - u) + (u + v) * G' (v - u)))
      / (2 * u)
      = (-G (v + u) + (u - v) * G' (v + u) + G (v - u) + (u + v) * G' (v - u)) / (2 * u) := by
    ring
  rw [heq] at h
  exact h

lemma hasDerivAt_envVal_u (G G' : ℝ → ℝ) {u v : ℝ} (hu : u ≠ 0)
    (h1 : HasDerivAt G (G' (v + u)) (v + u))
    (h2 : HasDerivAt G (G' (v - u)) (v - u)) :
    HasDerivAt (fun t : ℝ => envVal G t v)
      ((v * (G (v + u) - G (v - u))
        + u * ((u - v) * G' (v + u) - (u + v) * G' (v - u))) / (2 * u ^ 2)) u := by
  have hA : HasDerivAt (fun t : ℝ => G (v + t)) (G' (v + u)) u := h1.comp_const_add v u
  have hB : HasDerivAt (fun t : ℝ => G (v - t)) (-G' (v - u)) u := h2.comp_const_sub v u
  have hp : HasDerivAt (fun t : ℝ => t - v) 1 u := by simpa using (hasDerivAt_id u).sub_const v
  have hq : HasDerivAt (fun t : ℝ => t + v) 1 u := by simpa using (hasDerivAt_id u).add_const v
  have hD : HasDerivAt (fun t : ℝ => 2 * t) 2 u := by simpa using (hasDerivAt_id u).const_mul 2
  have h := ((hp.mul hA).add (hq.mul hB)).fun_div hD (by simpa using hu)
  simp only [Pi.add_apply, Pi.mul_apply] at h
  have heq : ((1 * G (v + u) + (u - v) * G' (v + u)
        + (1 * G (v - u) + (u + v) * -G' (v - u))) * (2 * u)
        - ((u - v) * G (v + u) + (u + v) * G (v - u)) * 2) / (2 * u) ^ 2
      = (v * (G (v + u) - G (v - u))
        + u * ((u - v) * G' (v + u) - (u + v) * G' (v - u))) / (2 * u ^ 2) := by
    field_simp
    ring
  rw [heq] at h
  exact h

/-- **Joint stationarity is bitangency.**  Eliminating between `∂V/∂v = 0` and
`∂V/∂u = 0` leaves `(u² − v²)·(G′(v+u) − G′(v−u)) = 0`; so away from the
degenerate `|v| = u` the two contact points have equal slope, which together
with `∂V/∂v = 0` is the chord condition. -/
theorem stationary_imp_bitangent {A B A' B' u v : ℝ}
    (hv : -A + (u - v) * A' + B + (u + v) * B' = 0)
    (hu : v * (A - B) + u * ((u - v) * A' - (u + v) * B') = 0) :
    (u ^ 2 - v ^ 2) * (A' - B') = 0 := by
  have h : A - B = (u - v) * A' + (u + v) * B' := by linarith
  rw [h] at hu
  linear_combination hu

/-- **The force at symmetry.**  Writing `G = G_e + O` with `G_e` even and `O`
odd (so `G_e′` is odd and `O′` even), the even part cancels out of
`∂V/∂v|_{v=0}` and what is left is `O′(u) − O(u)/u`. -/
theorem envVal_deriv_v_zero_of_split {Ge O Ge' O' : ℝ → ℝ} {u : ℝ} (hu : u ≠ 0)
    (hGe : Ge (-u) = Ge u) (hO : O (-u) = -O u)
    (hGe' : Ge' (-u) = -Ge' u) (hO' : O' (-u) = O' u) :
    (-(Ge u + O u) + (u - 0) * (Ge' u + O' u) + (Ge (-u) + O (-u))
        + (u + 0) * (Ge' (-u) + O' (-u))) / (2 * u)
      = O' u - O u / u := by
  rw [hGe, hO, hGe', hO']
  field_simp
  ring

/-- The force at symmetry, for the concrete objective: `∂V/∂v|_{v=0}` equals
`forceFun`, whose sign is `sign (d − c)` for every `u > 0` (`forceFun_pos`).
`Ge` is the even part of `G`, which drops out entirely. -/
theorem envVal_deriv_v_zero_eq_forceFun {δ c d u : ℝ} {Ge Ge' : ℝ → ℝ}
    (hc0 : 0 < c) (hd0 : 0 < d) (hu0 : 0 < u)
    (hcu0 : -1 < δ * (c * u)) (hcu1 : δ * (c * u) < 1)
    (hdu0 : -1 < δ * (d * u)) (hdu1 : δ * (d * u) < 1)
    (hGe : Ge (-u) = Ge u) (hGe' : Ge' (-u) = -Ge' u) :
    (-(Ge u + oddPart δ c d u) + (u - 0) * (Ge' u + oddPartDeriv δ c d u)
        + (Ge (-u) + oddPart δ c d (-u))
        + (u + 0) * (Ge' (-u) + oddPartDeriv δ c d (-u))) / (2 * u)
      = forceFun δ c d u := by
  rw [envVal_deriv_v_zero_of_split (ne_of_gt hu0) hGe (oddPart_neg δ c d u) hGe'
    (oddPartDeriv_neg δ c d u)]
  exact oddPart_deriv_sub_eq hc0 hd0 hu0 hcu0 hcu1 hdu0 hdu1


/-! ### From `BiasCoords.lean` -/

/-- **`I(U;X) = Σ_u π_u f_e(s_u)`** for a joint law whose second marginal is
uniform.  This is the bias parametrization of `NOTES.md` §2, and the bridge from
`mutualInfo` — the language of `regionA` and `AveragedBSCConjecture` — to the
coordinates every analytic result in this development is stated in. -/
theorem mutualInfo_eq_sum_fe_bias {q : Bool → Bool → ℝ}
    (hpos : ∀ u, 0 < marg₁ q u) (hsum : marg₁ q false + marg₁ q true = 1)
    (hb : ∀ u, -1 < biasOf q u ∧ biasOf q u < 1)
    (huni : ∀ x, marg₂ q x = 1 / 2) :
    mutualInfo q
      = marg₁ q false * fe (biasOf q false) + marg₁ q true * fe (biasOf q true) := by
  have hrow : ∀ u, negMulLog (q u false) + negMulLog (q u true)
      = negMulLog (marg₁ q u) + marg₁ q u * (Real.log 2 - fe (biasOf q u)) := by
    intro u
    rw [q_false_eq (hpos u), q_true_eq (hpos u)]
    exact negMulLog_row (hpos u) (hb u).1 (hb u).2
  have hm2 : entropy1 (marg₂ q) = Real.log 2 := by
    have hlog : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
    simp only [entropy1, huni false, huni true, Real.negMulLog, hlog]
    ring
  have he2 : entropy2 q
      = entropy1 (marg₁ q) + Real.log 2
        - (marg₁ q false * fe (biasOf q false) + marg₁ q true * fe (biasOf q true)) := by
    have hf := hrow false; have ht := hrow true
    simp only [entropy2, entropy1]
    linear_combination hf + ht + Real.log 2 * hsum
  simp only [mutualInfo, hm2, he2]
  ring

/-- **`I(U;X)` in bias coordinates**, for the joint law that `regionA` is
actually stated with. -/
theorem mutualInfo_jointUX_eq_bias {cL : Chan}
    (hpos : ∀ u, 0 < marg₁ (jointUX cL) u)
    (hb : ∀ u, -1 < biasOf (jointUX cL) u ∧ biasOf (jointUX cL) u < 1) :
    mutualInfo (jointUX cL)
      = marg₁ (jointUX cL) false * fe (biasOf (jointUX cL) false)
        + marg₁ (jointUX cL) true * fe (biasOf (jointUX cL) true) :=
  mutualInfo_eq_sum_fe_bias hpos (marg₁_jointUX_sum cL) hb (marg₂_jointUX cL)

/-- A linear functional bounded on `S` is bounded by the same constant on
`convexHull ℝ S`. -/
theorem convexHull_le_of_le {S : Set (ℝ × ℝ × ℝ)} {a b c d : ℝ}
    (h : ∀ x ∈ S, a * x.1 + b * x.2.1 + c * x.2.2 ≤ d) :
    ∀ x ∈ convexHull ℝ S, a * x.1 + b * x.2.1 + c * x.2.2 ≤ d := by
  have hconv : Convex ℝ {x : ℝ × ℝ × ℝ | a * x.1 + b * x.2.1 + c * x.2.2 ≤ d} := by
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have : a * (s * x.1 + t * y.1) + b * (s * x.2.1 + t * y.2.1)
        + c * (s * x.2.2 + t * y.2.2)
        = s * (a * x.1 + b * x.2.1 + c * x.2.2) + t * (a * y.1 + b * y.2.1 + c * y.2.2) := by
      ring
    show a * (s * x.1 + t * y.1) + b * (s * x.2.1 + t * y.2.1)
        + c * (s * x.2.2 + t * y.2.2) ≤ d
    rw [this]
    have h1 : s * (a * x.1 + b * x.2.1 + c * x.2.2) ≤ s * d := mul_le_mul_of_nonneg_left hx hs
    have h2 : t * (a * y.1 + b * y.2.1 + c * y.2.2) ≤ t * d := mul_le_mul_of_nonneg_left hy ht
    have h3 : s * d + t * d = d := by rw [← add_mul, hst, one_mul]
    linarith
  exact convexHull_min h hconv


/-! ### From `FixedPoint.lean` -/


/-! ## Coordinates -/

/-- `m = (b−a)/(a+b)`, the marginal bias of `X`. -/
noncomputable def mOf (a b : ℝ) : ℝ := (b - a) / (a + b)

/-- `k = 2ab/(a+b)`, the U-side spread. -/
noncomputable def kOf (a b : ℝ) : ℝ := 2 * a * b / (a + b)

lemma one_add_mOf {a b : ℝ} (hab : a + b ≠ 0) : 1 + mOf a b = 2 * b / (a + b) := by
  rw [mOf]; field_simp; ring

lemma one_sub_mOf {a b : ℝ} (hab : a + b ≠ 0) : 1 - mOf a b = 2 * a / (a + b) := by
  rw [mOf]; field_simp; ring

/-- The V-side X-biases `b₁ = m + kδc`, `b₂ = m − kδd`. -/
noncomputable def bOne (a b δ c : ℝ) : ℝ := mOf a b + kOf a b * δ * c

noncomputable def bTwo (a b δ d : ℝ) : ℝ := mOf a b - kOf a b * δ * d

/-- **The factorisation everything rests on.** -/
lemma one_add_bOne {a b δ c : ℝ} (hab : a + b ≠ 0) :
    1 + bOne a b δ c = (1 + mOf a b) * (1 + a * (δ * c)) := by
  rw [bOne, one_add_mOf hab, mOf, kOf]; field_simp; ring

lemma one_sub_bOne {a b δ c : ℝ} (hab : a + b ≠ 0) :
    1 - bOne a b δ c = (1 - mOf a b) * (1 - b * (δ * c)) := by
  rw [bOne, one_sub_mOf hab, mOf, kOf]; field_simp; ring

lemma one_add_bTwo {a b δ d : ℝ} (hab : a + b ≠ 0) :
    1 + bTwo a b δ d = (1 + mOf a b) * (1 - a * (δ * d)) := by
  rw [bTwo, one_add_mOf hab, mOf, kOf]; field_simp; ring

lemma one_sub_bTwo {a b δ d : ℝ} (hab : a + b ≠ 0) :
    1 - bTwo a b δ d = (1 - mOf a b) * (1 + b * (δ * d)) := by
  rw [bTwo, one_sub_mOf hab, mOf, kOf]; field_simp; ring

/-! ## The U-side: `D = artanh a + artanh b` and `A − f_e(m)` -/

/-- `D = artanh(m+k) − artanh(m−k)`. -/
noncomputable def DOf (a b : ℝ) : ℝ := artanh (mOf a b + kOf a b) - artanh (mOf a b - kOf a b)

/-- `A = ½[f_e(m+k) + f_e(m−k)]`. -/
noncomputable def AOf (a b : ℝ) : ℝ := (fe (mOf a b + kOf a b) + fe (mOf a b - kOf a b)) / 2

lemma one_add_v₀ {a b : ℝ} (hab : a + b ≠ 0) :
    1 + (mOf a b + kOf a b) = (1 + mOf a b) * (1 + a) := by
  rw [one_add_mOf hab, mOf, kOf]; field_simp; ring

lemma one_sub_v₀ {a b : ℝ} (hab : a + b ≠ 0) :
    1 - (mOf a b + kOf a b) = (1 - mOf a b) * (1 - b) := by
  rw [one_sub_mOf hab, mOf, kOf]; field_simp; ring

lemma one_add_v₁ {a b : ℝ} (hab : a + b ≠ 0) :
    1 + (mOf a b - kOf a b) = (1 + mOf a b) * (1 - a) := by
  rw [one_add_mOf hab, mOf, kOf]; field_simp; ring

lemma one_sub_v₁ {a b : ℝ} (hab : a + b ≠ 0) :
    1 - (mOf a b - kOf a b) = (1 - mOf a b) * (1 + b) := by
  rw [one_sub_mOf hab, mOf, kOf]; field_simp; ring

/-- **`D = artanh a + artanh b`.**  The `(1±m)` factors cancel between the two
`artanh`s. -/
theorem DOf_eq {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    DOf a b = artanh a + artanh b := by
  have hab : a + b ≠ 0 := by positivity
  have hm1 : 0 < 1 + mOf a b := by rw [one_add_mOf hab]; positivity
  have hm2 : 0 < 1 - mOf a b := by rw [one_sub_mOf hab]; positivity
  have hv₀0 : -1 < mOf a b + kOf a b := by
    have : 0 < 1 + (mOf a b + kOf a b) := by rw [one_add_v₀ hab]; positivity
    linarith
  have hv₀1 : mOf a b + kOf a b < 1 := by
    have : 0 < 1 - (mOf a b + kOf a b) := by
      rw [one_sub_v₀ hab]; exact mul_pos hm2 (by linarith)
    linarith
  have hv₁0 : -1 < mOf a b - kOf a b := by
    have : 0 < 1 + (mOf a b - kOf a b) := by
      rw [one_add_v₁ hab]; exact mul_pos hm1 (by linarith)
    linarith
  have hv₁1 : mOf a b - kOf a b < 1 := by
    have : 0 < 1 - (mOf a b - kOf a b) := by rw [one_sub_v₁ hab]; positivity
    linarith
  rw [DOf, artanh_eq_log_sub hv₀0 hv₀1, artanh_eq_log_sub hv₁0 hv₁1,
    artanh_eq_log_sub (by linarith) ha1, artanh_eq_log_sub (by linarith) hb1,
    one_add_v₀ hab, one_sub_v₀ hab, one_add_v₁ hab, one_sub_v₁ hab,
    Real.log_mul (ne_of_gt hm1) (by linarith), Real.log_mul (ne_of_gt hm2) (by linarith),
    Real.log_mul (ne_of_gt hm1) (by linarith), Real.log_mul (ne_of_gt hm2) (by linarith)]
  ring

/-- **`A − f_e(m) = ½[(1+m)f_e(a) + (1−m)f_e(b)]`** — mutual information computed from
the two sides of the `U—X` pair. -/
theorem AOf_sub_fe {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    AOf a b - fe (mOf a b) = ((1 + mOf a b) * fe a + (1 - mOf a b) * fe b) / 2 := by
  have hab : a + b ≠ 0 := by positivity
  have hm1 : 0 < 1 + mOf a b := by rw [one_add_mOf hab]; positivity
  have hm2 : 0 < 1 - mOf a b := by rw [one_sub_mOf hab]; positivity
  rw [AOf]
  simp only [fe]
  rw [one_add_v₀ hab, one_sub_v₀ hab, one_add_v₁ hab, one_sub_v₁ hab,
    Real.log_mul (ne_of_gt hm1) (by linarith), Real.log_mul (ne_of_gt hm2) (by linarith),
    Real.log_mul (ne_of_gt hm1) (by linarith), Real.log_mul (ne_of_gt hm2) (by linarith)]
  ring

/-! ## The ratio `ρ(U;X)` -/

/-- `G(p,q) = [f_e(p)/p + f_e(q)/q]/[artanh p + artanh q]`, the ratio `ρ` of a
mean-zero two-point pair. -/
noncomputable def GFun (p q : ℝ) : ℝ :=
  (fe p / p + fe q / q) / (artanh p + artanh q)

/-- **`ρ(U;X) = 2(A − f_e(m))/(kD) = G(a,b)`.** -/
theorem rhoUX_eq {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (AOf a b - fe (mOf a b)) / (kOf a b * DOf a b) = GFun a b := by
  have hab : a + b ≠ 0 := by positivity
  have hL : 0 < artanh a + artanh b := by
    have := Real.artanh_pos (Set.mem_Ioo.mpr ⟨ha0, ha1⟩)
    have := Real.artanh_pos (Set.mem_Ioo.mpr ⟨hb0, hb1⟩)
    linarith
  rw [AOf_sub_fe ha0 ha1 hb0 hb1, DOf_eq ha0 ha1 hb0 hb1, one_add_mOf hab, one_sub_mOf hab,
    kOf, GFun]
  field_simp

/-! ## The joint quantities and the closed form for `𝒥(U;V)` -/

/-- `κ = cd/(c+d)`. -/
noncomputable def kapOf (c d : ℝ) : ℝ := c * d / (c + d)

/-- `Δℓ = artanh b₁ − artanh b₂`. -/
noncomputable def DlOf (a b δ c d : ℝ) : ℝ := artanh (bOne a b δ c) - artanh (bTwo a b δ d)

/-- **`Δℓ` in terms of the four joint logarithms.**  The `(1±m)` factors cancel. -/
theorem DlOf_eq {a b δ c d : ℝ} (hab : a + b ≠ 0)
    (hm1 : 0 < 1 + mOf a b) (hm2 : 0 < 1 - mOf a b)
    (h1 : 0 < 1 + a * (δ * c)) (h2 : 0 < 1 - b * (δ * c))
    (h3 : 0 < 1 - a * (δ * d)) (h4 : 0 < 1 + b * (δ * d)) :
    DlOf a b δ c d
      = (log (1 + a * (δ * c)) + log (1 + b * (δ * d))
          - log (1 - a * (δ * d)) - log (1 - b * (δ * c))) / 2 := by
  have hb1a : -1 < bOne a b δ c := by
    have : 0 < 1 + bOne a b δ c := by rw [one_add_bOne hab]; exact mul_pos hm1 h1
    linarith
  have hb1b : bOne a b δ c < 1 := by
    have : 0 < 1 - bOne a b δ c := by rw [one_sub_bOne hab]; exact mul_pos hm2 h2
    linarith
  have hb2a : -1 < bTwo a b δ d := by
    have : 0 < 1 + bTwo a b δ d := by rw [one_add_bTwo hab]; exact mul_pos hm1 h3
    linarith
  have hb2b : bTwo a b δ d < 1 := by
    have : 0 < 1 - bTwo a b δ d := by rw [one_sub_bTwo hab]; exact mul_pos hm2 h4
    linarith
  rw [DlOf, artanh_eq_log_sub hb1a hb1b, artanh_eq_log_sub hb2a hb2b,
    one_add_bOne hab, one_sub_bOne hab, one_add_bTwo hab, one_sub_bTwo hab,
    Real.log_mul (ne_of_gt hm1) (ne_of_gt h1), Real.log_mul (ne_of_gt hm2) (ne_of_gt h2),
    Real.log_mul (ne_of_gt hm1) (ne_of_gt h3), Real.log_mul (ne_of_gt hm2) (ne_of_gt h4)]
  ring

/-- `𝒥(U;V) = E[z·log(1+z)]` for the two-point pair, written out over the four
atoms `z = δ·s·t`. -/
noncomputable def jeffreysTP (δ a b c d : ℝ) : ℝ :=
  (b * d * ((δ * (a * c)) * log (1 + δ * (a * c)))
    + b * c * ((-(δ * (a * d))) * log (1 - δ * (a * d)))
    + a * d * ((-(δ * (b * c))) * log (1 - δ * (b * c)))
    + a * c * ((δ * (b * d)) * log (1 + δ * (b * d)))) / ((a + b) * (c + d))

/-- **`𝒥(U;V) = k·δ·κ·Δℓ`.**  All four atoms carry the same coefficient
`δ·abcd`, which is exactly `k·δ·κ/2` times `(a+b)(c+d)`. -/
theorem jeffreysTP_eq {a b δ c d : ℝ} (hab : a + b ≠ 0) (hcd : c + d ≠ 0)
    (hm1 : 0 < 1 + mOf a b) (hm2 : 0 < 1 - mOf a b)
    (h1 : 0 < 1 + a * (δ * c)) (h2 : 0 < 1 - b * (δ * c))
    (h3 : 0 < 1 - a * (δ * d)) (h4 : 0 < 1 + b * (δ * d)) :
    jeffreysTP δ a b c d = kOf a b * δ * kapOf c d * DlOf a b δ c d := by
  rw [DlOf_eq hab hm1 hm2 h1 h2 h3 h4, jeffreysTP, kOf, kapOf]
  have e1 : δ * (a * c) = a * (δ * c) := by ring
  have e2 : δ * (a * d) = a * (δ * d) := by ring
  have e3 : δ * (b * c) = b * (δ * c) := by ring
  have e4 : δ * (b * d) = b * (δ * d) := by ring
  rw [e1, e2, e3, e4]
  field_simp
  ring

/-! ## The closed form for `I(U;V)` -/

/-- `I(U;V) = E[f(z)]`, `f(z) = (1+z)log(1+z)`, over the four atoms. -/
noncomputable def mutualTP (δ a b c d : ℝ) : ℝ :=
  (b * d * ((1 + δ * (a * c)) * log (1 + δ * (a * c)))
    + b * c * ((1 - δ * (a * d)) * log (1 - δ * (a * d)))
    + a * d * ((1 - δ * (b * c)) * log (1 - δ * (b * c)))
    + a * c * ((1 + δ * (b * d)) * log (1 + δ * (b * d)))) / ((a + b) * (c + d))

/-- **`I(U;V) = wc·f_e(b₁) + wd·f_e(b₂) − f_e(m)`.**  The `log(1±m)` terms cancel
because `wc·c = wd·d`; the remaining four terms match the four atoms exactly. -/
theorem mutualTP_eq {a b δ c d : ℝ} (hab : a + b ≠ 0) (hcd : c + d ≠ 0)
    (hm1 : 0 < 1 + mOf a b) (hm2 : 0 < 1 - mOf a b)
    (h1 : 0 < 1 + a * (δ * c)) (h2 : 0 < 1 - b * (δ * c))
    (h3 : 0 < 1 - a * (δ * d)) (h4 : 0 < 1 + b * (δ * d)) :
    mutualTP δ a b c d
      = (d / (c + d)) * fe (bOne a b δ c) + (c / (c + d)) * fe (bTwo a b δ d)
        - fe (mOf a b) := by
  rw [mutualTP]
  simp only [fe]
  rw [one_add_bOne hab, one_sub_bOne hab, one_add_bTwo hab, one_sub_bTwo hab,
    Real.log_mul (ne_of_gt hm1) (ne_of_gt h1), Real.log_mul (ne_of_gt hm2) (ne_of_gt h2),
    Real.log_mul (ne_of_gt hm1) (ne_of_gt h3), Real.log_mul (ne_of_gt hm2) (ne_of_gt h4),
    one_add_mOf hab, one_sub_mOf hab]
  have e1 : δ * (a * c) = a * (δ * c) := by ring
  have e2 : δ * (a * d) = a * (δ * d) := by ring
  have e3 : δ * (b * c) = b * (δ * c) := by ring
  have e4 : δ * (b * d) = b * (δ * d) := by ring
  rw [e1, e2, e3, e4]
  field_simp
  ring

/-! ## The route-2 identity -/

/-- `ν = kδΔℓ/(artanh c + artanh d)`. -/
noncomputable def nuOf (a b δ c d : ℝ) : ℝ :=
  kOf a b * δ * DlOf a b δ c d / (artanh c + artanh d)

/-- `μ = 2δκΔℓ/D`. -/
noncomputable def muOf (a b δ c d : ℝ) : ℝ :=
  2 * δ * kapOf c d * DlOf a b δ c d / DOf a b

/-- The Lagrangian value `Φ = I(U;V) − μ·I(U;X) − ν·I(Y;V)`, written in the form
used by `numerics/fixed_point_value.py`. -/
noncomputable def PhiVal (a b δ c d : ℝ) : ℝ :=
  -muOf a b δ c d * AOf a b - (1 - muOf a b δ c d) * fe (mOf a b)
    + (d / (c + d)) * (fe (bOne a b δ c) - nuOf a b δ c d * fe c)
    + (c / (c + d)) * (fe (bTwo a b δ d) - nuOf a b δ c d * fe d)

/-- **The route-2 identity**, in division-free form:
`Φ = I(U;V) − 𝒥(U;V)·[ρ(U;X) + ρ(Y;V)]`. -/
theorem route_identity {a b δ c d : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hc0 : 0 < c) (hc1 : c < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (hm1 : 0 < 1 + mOf a b) (hm2 : 0 < 1 - mOf a b)
    (h1 : 0 < 1 + a * (δ * c)) (h2 : 0 < 1 - b * (δ * c))
    (h3 : 0 < 1 - a * (δ * d)) (h4 : 0 < 1 + b * (δ * d)) :
    PhiVal a b δ c d
      = mutualTP δ a b c d - jeffreysTP δ a b c d * (GFun a b + GFun c d) := by
  have hab : a + b ≠ 0 := by positivity
  have hcd : c + d ≠ 0 := by positivity
  have hLcd : 0 < artanh c + artanh d := by
    have := Real.artanh_pos (Set.mem_Ioo.mpr ⟨hc0, hc1⟩)
    have := Real.artanh_pos (Set.mem_Ioo.mpr ⟨hd0, hd1⟩)
    linarith
  have hDpos : 0 < DOf a b := by
    rw [DOf_eq ha0 ha1 hb0 hb1]
    have := Real.artanh_pos (Set.mem_Ioo.mpr ⟨ha0, ha1⟩)
    have := Real.artanh_pos (Set.mem_Ioo.mpr ⟨hb0, hb1⟩)
    linarith
  have hJ : jeffreysTP δ a b c d = kOf a b * δ * kapOf c d * DlOf a b δ c d :=
    jeffreysTP_eq hab hcd hm1 hm2 h1 h2 h3 h4
  have hI : mutualTP δ a b c d
      = (d / (c + d)) * fe (bOne a b δ c) + (c / (c + d)) * fe (bTwo a b δ d)
        - fe (mOf a b) := mutualTP_eq hab hcd hm1 hm2 h1 h2 h3 h4
  -- `μ·I(U;X) = 𝒥·G(a,b)`
  have hmu : muOf a b δ c d * (AOf a b - fe (mOf a b))
      = jeffreysTP δ a b c d * GFun a b := by
    have hR : 2 * (AOf a b - fe (mOf a b)) / (kOf a b * DOf a b) = GFun a b :=
      rhoUX_eq ha0 ha1 hb0 hb1
    have hk : kOf a b ≠ 0 := by rw [kOf]; positivity
    rw [hJ, ← hR, muOf]
    field_simp
  -- `ν·I(Y;V) = 𝒥·G(c,d)`
  have hnu : nuOf a b δ c d * ((d / (c + d)) * fe c + (c / (c + d)) * fe d)
      = jeffreysTP δ a b c d * GFun c d := by
    rw [hJ, nuOf, GFun, kapOf]
    field_simp
  rw [PhiVal, hI]
  nlinarith [hmu, hnu]

/-- The same identity in ratio form: `Φ = 𝒥·[ρ(U;V) − ρ(U;X) − ρ(Y;V)]`, so
`Φ ≤ 0` is exactly `ρ(U;V) ≤ ρ(U;X) + ρ(Y;V)`. -/
theorem route_identity_ratio {a b δ c d : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hc0 : 0 < c) (hc1 : c < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (hm1 : 0 < 1 + mOf a b) (hm2 : 0 < 1 - mOf a b)
    (h1 : 0 < 1 + a * (δ * c)) (h2 : 0 < 1 - b * (δ * c))
    (h3 : 0 < 1 - a * (δ * d)) (h4 : 0 < 1 + b * (δ * d))
    (hJ0 : jeffreysTP δ a b c d ≠ 0) :
    PhiVal a b δ c d
      = jeffreysTP δ a b c d
          * (mutualTP δ a b c d / jeffreysTP δ a b c d - GFun a b - GFun c d) := by
  rw [route_identity ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1 hm1 hm2 h1 h2 h3 h4]
  field_simp
  ring

/-! ## The stationarity equations (E2) and (E4)

`(E2)` is `μ·D/2 = δκΔℓ`, which holds **by construction** once `μ` is defined as
`muOf` (that is what "E2 is consumed as the definition of `μ`" means in
`NOTES.md` §6).  `(E4)` is the remaining equation, and it is the one the
relaxation ladder identifies as irreducible.

What is proved here is that `(E4)` holds **automatically at symmetric points**
(`a = b`, `c = d`), so it carries only asymmetric content — which is why §5d,
working on the symmetric slice, never needed it.

The *variational* reading of `(E4)` — that solutions of `(E2)`,`(E4)` are exactly
the alternating-maximisation best responses — is supported numerically
(agreement to `5.6e-14`) but is **not** formalised: that needs a variational
setup this development does not have. -/

/-- `artanh` is odd. -/
lemma artanh_neg' {z : ℝ} (h0 : -1 < z) (h1 : z < 1) : artanh (-z) = -artanh z := by
  rw [artanh_eq_log_sub (by linarith) (by linarith), artanh_eq_log_sub h0 h1,
    show (1:ℝ) + -z = 1 - z by ring, show (1:ℝ) - -z = 1 + z by ring]
  ring

/-- **(E2)**, `μ·D/2 − δκΔℓ = 0`, holds by construction. -/
theorem E2_of_def {a b δ c d : ℝ} (hD : DOf a b ≠ 0) :
    muOf a b δ c d * (1 / 2) * DOf a b - δ * kapOf c d * DlOf a b δ c d = 0 := by
  rw [muOf]; field_simp; ring

/-- **(E4)**, the V-side stationarity equation. -/
noncomputable def E4Res (a b δ c d : ℝ) : ℝ :=
  fe (bOne a b δ c) - fe (bTwo a b δ d) - nuOf a b δ c d * (fe c - fe d)
    - (c + d) * (kOf a b * δ * artanh (bOne a b δ c) - nuOf a b δ c d * artanh c)

/-- **(E4) holds automatically at symmetric points.**  With `a = b` (so `m = 0`,
`k = a`) and `c = d`, both `f_e`-differences vanish by evenness, and
`ν·artanh c = kδ·artanh b₁` because `Δℓ = 2·artanh b₁` and
`artanh c + artanh d = 2·artanh c`.  Hence `(E4)` carries only the asymmetric
content of the fixed-point system. -/
theorem E4Res_symmetric {a c δ : ℝ} (ha0 : 0 < a) (hc0 : 0 < c) (hc1 : c < 1)
    (hb0 : -1 < a * (δ * c)) (hb1 : a * (δ * c) < 1) :
    E4Res a a δ c c = 0 := by
  have hab : a + a ≠ 0 := by positivity
  have hm : mOf a a = 0 := by rw [mOf]; simp
  have hk : kOf a a = a := by rw [kOf]; field_simp; ring
  have hb1e : bOne a a δ c = a * (δ * c) := by rw [bOne, hm, hk]; ring
  have hb2e : bTwo a a δ c = -(a * (δ * c)) := by rw [bTwo, hm, hk]; ring
  have hLc : artanh c ≠ 0 := ne_of_gt (Real.artanh_pos (Set.mem_Ioo.mpr ⟨hc0, hc1⟩))
  have hDl : DlOf a a δ c c = 2 * artanh (a * (δ * c)) := by
    rw [DlOf, hb1e, hb2e, artanh_neg' hb0 hb1]; ring
  have hnu : nuOf a a δ c c = a * δ * artanh (a * (δ * c)) / artanh c := by
    rw [nuOf, hDl, hk]; field_simp; ring
  rw [E4Res, hb1e, hb2e, hnu, hk]
  rw [show fe (-(a * (δ * c))) = fe (a * (δ * c)) from fe_neg _]
  field_simp
  ring

/-! ## The variational characterisation of (E4)

With `μ`, `ν` held **fixed**, the V-side Lagrangian as a function of the V-side
atoms is

```
Φ(c,d) = const + (d/(c+d))·[f_e(b₁) − ν·f_e(c)] + (c/(c+d))·[f_e(b₂) − ν·f_e(d)]
```

Writing `g₁(c) = f_e(b₁(c)) − ν·f_e(c)` and `C₂ = f_e(b₂) − ν·f_e(d)`, the numerator is
`N(c) = d·g₁(c) + c·C₂` and

```
∂Φ/∂c = [N′(c)(c+d) − N(c)]/(c+d)² = −d·E4Res/(c+d)²
∂Φ/∂d = +c·E4Res′/(c+d)²
```

so **(E4) is precisely the `c`-stationarity of the V-side Lagrangian**, and its
companion `E4Res′` is the `d`-stationarity.  Both vanish at symmetric points. -/

/-- The V-side Lagrangian with `μ`, `ν` as free parameters. -/
noncomputable def PhiPar (a b δ μ ν c d : ℝ) : ℝ :=
  -μ * AOf a b - (1 - μ) * fe (mOf a b)
    + (d / (c + d)) * (fe (bOne a b δ c) - ν * fe c)
    + (c / (c + d)) * (fe (bTwo a b δ d) - ν * fe d)

/-- (E4) with `ν` a free parameter. -/
noncomputable def E4ResPar (a b δ ν c d : ℝ) : ℝ :=
  fe (bOne a b δ c) - fe (bTwo a b δ d) - ν * (fe c - fe d)
    - (c + d) * (kOf a b * δ * artanh (bOne a b δ c) - ν * artanh c)

/-- The `d`-stationarity companion of (E4). -/
noncomputable def E4ResPar' (a b δ ν c d : ℝ) : ℝ :=
  fe (bOne a b δ c) - fe (bTwo a b δ d) - ν * (fe c - fe d)
    - (c + d) * (kOf a b * δ * artanh (bTwo a b δ d) + ν * artanh d)

lemma E4Res_eq_par (a b δ c d : ℝ) :
    E4Res a b δ c d = E4ResPar a b δ (nuOf a b δ c d) c d := rfl

/-- **The variational characterisation of (E4): `∂Φ/∂c = −d·E4Res/(c+d)²`.** -/
theorem hasDerivAt_PhiPar_c {a b δ μ ν c d : ℝ} (hcd : c + d ≠ 0)
    (hb0 : -1 < bOne a b δ c) (hb1 : bOne a b δ c < 1)
    (hc0 : -1 < c) (hc1 : c < 1) :
    HasDerivAt (fun x : ℝ => PhiPar a b δ μ ν x d)
      (-(d * E4ResPar a b δ ν c d) / (c + d) ^ 2) c := by
  have hden : HasDerivAt (fun x : ℝ => x + d) 1 c := by simpa using (hasDerivAt_id c).add_const d
  have hw1 : HasDerivAt (fun x : ℝ => d / (x + d)) (-d / (c + d) ^ 2) c := by
    have h := (hasDerivAt_const c d).fun_div hden hcd
    have heq : (0 * (c + d) - d * 1) / (c + d) ^ 2 = -d / (c + d) ^ 2 := by ring
    rwa [heq] at h
  have hw2 : HasDerivAt (fun x : ℝ => x / (x + d)) (d / (c + d) ^ 2) c := by
    have h := (hasDerivAt_id' (x := c)).fun_div hden hcd
    have heq : (1 * (c + d) - c * 1) / (c + d) ^ 2 = d / (c + d) ^ 2 := by ring
    rw [heq] at h
    exact h
  have hbfun : (fun x : ℝ => fe (bOne a b δ x))
      = fun x : ℝ => fe (mOf a b + kOf a b * δ * x) := by
    funext x; rw [bOne]
  have hB : HasDerivAt (fun x : ℝ => fe (bOne a b δ x))
      (artanh (bOne a b δ c) * (kOf a b * δ)) c := by
    rw [hbfun, bOne] at *
    exact hasDerivAt_fe_affine (K := kOf a b * δ) hb0 hb1
  have hC : HasDerivAt fe (artanh c) c := hasDerivAt_fe hc0 hc1
  have hg₁ : HasDerivAt (fun x : ℝ => fe (bOne a b δ x) - ν * fe x)
      (artanh (bOne a b δ c) * (kOf a b * δ) - ν * artanh c) c :=
    hB.fun_sub (hC.const_mul ν)
  have h := ((hw1.fun_mul hg₁).fun_add
    (hw2.mul_const (fe (bTwo a b δ d) - ν * fe d))).const_add
      (-μ * AOf a b - (1 - μ) * fe (mOf a b))
  have hfun : (fun x : ℝ => -μ * AOf a b - (1 - μ) * fe (mOf a b)
      + (d / (x + d) * (fe (bOne a b δ x) - ν * fe x)
        + x / (x + d) * (fe (bTwo a b δ d) - ν * fe d)))
      = fun x : ℝ => PhiPar a b δ μ ν x d := by
    funext x; rw [PhiPar]; ring
  rw [hfun] at h
  have heq : -d / (c + d) ^ 2 * (fe (bOne a b δ c) - ν * fe c)
      + d / (c + d) ^ 2 * (fe (bTwo a b δ d) - ν * fe d)
      + d / (c + d) * (artanh (bOne a b δ c) * (kOf a b * δ) - ν * artanh c)
      = -(d * E4ResPar a b δ ν c d) / (c + d) ^ 2 := by
    rw [E4ResPar]
    field_simp
    ring
  have hcollect : -d / (c + d) ^ 2 * (fe (bOne a b δ c) - ν * fe c)
      + d / (c + d) * (artanh (bOne a b δ c) * (kOf a b * δ) - ν * artanh c)
      + d / (c + d) ^ 2 * (fe (bTwo a b δ d) - ν * fe d)
      = -(d * E4ResPar a b δ ν c d) / (c + d) ^ 2 := by
    rw [← heq]; ring
  rwa [hcollect] at h

/-- **(E4) is exactly the `c`-stationarity.**  For `d ≠ 0`, the derivative
vanishes iff `E4Res = 0`. -/
theorem E4ResPar_eq_zero_iff {a b δ μ ν c d : ℝ} (hcd : c + d ≠ 0) (hd : d ≠ 0)
    (hb0 : -1 < bOne a b δ c) (hb1 : bOne a b δ c < 1)
    (hc0 : -1 < c) (hc1 : c < 1) :
    deriv (fun x : ℝ => PhiPar a b δ μ ν x d) c = 0 ↔ E4ResPar a b δ ν c d = 0 := by
  rw [(hasDerivAt_PhiPar_c hcd hb0 hb1 hc0 hc1).deriv]
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · have : d * E4ResPar a b δ ν c d = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hd
      · exact h'
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hcd
  · intro h; left; rw [h]; ring

/-- **`∂Φ/∂d = c·E4Res′/(c+d)²`.** -/
theorem hasDerivAt_PhiPar_d {a b δ μ ν c d : ℝ} (hcd : c + d ≠ 0)
    (hb0 : -1 < bTwo a b δ d) (hb1 : bTwo a b δ d < 1)
    (hd0 : -1 < d) (hd1 : d < 1) :
    HasDerivAt (fun y : ℝ => PhiPar a b δ μ ν c y)
      (c * E4ResPar' a b δ ν c d / (c + d) ^ 2) d := by
  have hcd' : c + d ≠ 0 := hcd
  have hden : HasDerivAt (fun y : ℝ => c + y) 1 d := by simpa using (hasDerivAt_id d).const_add c
  have hw1 : HasDerivAt (fun y : ℝ => y / (c + y)) (c / (c + d) ^ 2) d := by
    have h := (hasDerivAt_id' (x := d)).fun_div hden hcd'
    have heq : (1 * (c + d) - d * 1) / (c + d) ^ 2 = c / (c + d) ^ 2 := by ring
    rw [heq] at h; exact h
  have hw2 : HasDerivAt (fun y : ℝ => c / (c + y)) (-c / (c + d) ^ 2) d := by
    have h := (hasDerivAt_const d c).fun_div hden hcd'
    have heq : (0 * (c + d) - c * 1) / (c + d) ^ 2 = -c / (c + d) ^ 2 := by ring
    rw [heq] at h; exact h
  have hbfun : (fun y : ℝ => fe (bTwo a b δ y))
      = fun y : ℝ => fe (mOf a b + -(kOf a b * δ) * y) := by
    funext y; rw [bTwo]; ring_nf
  have hB : HasDerivAt (fun y : ℝ => fe (bTwo a b δ y))
      (artanh (bTwo a b δ d) * -(kOf a b * δ)) d := by
    rw [hbfun]
    have hb0' : -1 < mOf a b + -(kOf a b * δ) * d := by rw [bTwo] at hb0; linarith [hb0]
    have hb1' : mOf a b + -(kOf a b * δ) * d < 1 := by rw [bTwo] at hb1; linarith [hb1]
    have := hasDerivAt_fe_affine (p := mOf a b) (K := -(kOf a b * δ)) hb0' hb1'
    have hrw : mOf a b + -(kOf a b * δ) * d = bTwo a b δ d := by rw [bTwo]; ring
    rwa [hrw] at this
  have hC : HasDerivAt fe (artanh d) d := hasDerivAt_fe hd0 hd1
  have hC₂ : HasDerivAt (fun y : ℝ => fe (bTwo a b δ y) - ν * fe y)
      (artanh (bTwo a b δ d) * -(kOf a b * δ) - ν * artanh d) d :=
    hB.fun_sub (hC.const_mul ν)
  have h := ((hw1.mul_const (fe (bOne a b δ c) - ν * fe c)).fun_add
    (hw2.fun_mul hC₂)).const_add (-μ * AOf a b - (1 - μ) * fe (mOf a b))
  have hfun : (fun y : ℝ => -μ * AOf a b - (1 - μ) * fe (mOf a b)
      + (y / (c + y) * (fe (bOne a b δ c) - ν * fe c)
        + c / (c + y) * (fe (bTwo a b δ y) - ν * fe y)))
      = fun y : ℝ => PhiPar a b δ μ ν c y := by
    funext y; rw [PhiPar]; ring
  rw [hfun] at h
  have heq : c / (c + d) ^ 2 * (fe (bOne a b δ c) - ν * fe c)
      + (-c / (c + d) ^ 2 * (fe (bTwo a b δ d) - ν * fe d)
        + c / (c + d) * (artanh (bTwo a b δ d) * -(kOf a b * δ) - ν * artanh d))
      = c * E4ResPar' a b δ ν c d / (c + d) ^ 2 := by
    rw [E4ResPar']
    field_simp
    ring
  rwa [heq] at h

/-- **The two stationarity equations differ by exactly the defining relation for
`ν`.** -/
theorem E4ResPar_sub_E4ResPar' (a b δ ν c d : ℝ) :
    E4ResPar a b δ ν c d - E4ResPar' a b δ ν c d
      = -((c + d) * (kOf a b * δ * DlOf a b δ c d - ν * (artanh c + artanh d))) := by
  rw [E4ResPar, E4ResPar', DlOf]; ring

/-- **With `ν` at its defining value the two stationarity equations coincide.**
So the single equation (E4) encodes *both* the `c`- and the `d`-stationarity of
the V-side Lagrangian. -/
theorem E4ResPar_eq_E4ResPar'_of_nuOf {a b δ c d : ℝ}
    (hL : artanh c + artanh d ≠ 0) :
    E4ResPar a b δ (nuOf a b δ c d) c d = E4ResPar' a b δ (nuOf a b δ c d) c d := by
  have h := E4ResPar_sub_E4ResPar' a b δ (nuOf a b δ c d) c d
  have hz : kOf a b * δ * DlOf a b δ c d - nuOf a b δ c d * (artanh c + artanh d) = 0 := by
    rw [nuOf]; field_simp; ring
  rw [hz] at h
  simp at h
  linarith [h]

/-- **The variational characterisation of (E4), complete.**  At `ν = nuOf` and
with `c,d ≠ 0`, the V-side Lagrangian is stationary in **both** `c` and `d`
exactly when `E4Res = 0`. -/
theorem E4Res_eq_zero_iff_stationary {a b δ μ c d : ℝ}
    (hcd : c + d ≠ 0) (hd : d ≠ 0)
    (hL : artanh c + artanh d ≠ 0)
    (hb0 : -1 < bOne a b δ c) (hb1 : bOne a b δ c < 1)
    (hb2 : -1 < bTwo a b δ d) (hb3 : bTwo a b δ d < 1)
    (hc0 : -1 < c) (hc1 : c < 1) (hd0 : -1 < d) (hd1 : d < 1) :
    (deriv (fun x : ℝ => PhiPar a b δ μ (nuOf a b δ c d) x d) c = 0
      ∧ deriv (fun y : ℝ => PhiPar a b δ μ (nuOf a b δ c d) c y) d = 0)
      ↔ E4Res a b δ c d = 0 := by
  have hsq : (c + d) ^ 2 ≠ 0 := pow_ne_zero 2 hcd
  rw [(hasDerivAt_PhiPar_c hcd hb0 hb1 hc0 hc1).deriv,
    (hasDerivAt_PhiPar_d hcd hb2 hb3 hd0 hd1).deriv, E4Res_eq_par,
    ← E4ResPar_eq_E4ResPar'_of_nuOf (a := a) (b := b) (δ := δ) hL]
  constructor
  · rintro ⟨h, -⟩
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · have : d * E4ResPar a b δ (nuOf a b δ c d) c d = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hd
      · exact h'
    · exact absurd h hsq
  · intro h
    refine ⟨?_, ?_⟩
    · rw [h]; simp
    · rw [h]; simp

/-! ## An argument from (E4): the bitangency reduction

Collapse the V-side into a single scalar function of one atom,

```
φ(t) = f_e(m + kδt) − ν·f_e(t)
```

The V-side of a fixed point is the **mean-zero** two-point law `T ∈ {c, −d}`
with weights `wc = d/(c+d)`, `wd = c/(c+d)`, and

```
φ(c)  = f_e(b₁) − ν·f_e(c)        φ(−d) = f_e(b₂) − ν·f_e(d)
φ′(c) = kδ·L(b₁) − ν·L(c)     φ′(−d) = kδ·L(b₂) + ν·L(d)
```

so `φ′(c)` is *exactly* the bracket appearing in (E4).  Hence

* **(E4)** says `φ(c) − φ(−d) = (c+d)·φ′(c)`: the chord through the two atoms has
  slope `φ′(c)` (`E4ResPar_eq_zero_iff_chord`);
* **`ν = nuOf`** says `φ′(c) = φ′(−d)` (`phiV'_eq_of_nuOf`).

Together the chord is **bitangent** to `φ` at `c` and `−d`.  Because `E T = 0`,
the value of the mixture is the bitangent line evaluated at `0`, and since
`φ(0) = f_e(m)`,

```
Φ = [φ(c) − c·φ′(c)] − φ(0) − μ·I(U;X)          PhiVal_eq_tangent_gain
```

i.e. **`Φ ≤ 0` ⟺ (concave-envelope gain of `φ` at `0`) ≤ `μ·I(U;X)`**
(`PhiVal_nonpos_iff_gain_le`).  This is the reduction §5d uses on the symmetric
slice, now available at a general (E4) point.  It also explains why `φ` cannot be
concave at a genuine fixed point: bitangency at two *distinct* points `c > 0 >
−d` forces non-concavity, so the trivial case is vacuous. -/

/-- The V-side scalar function `φ(t) = f_e(m + kδt) − ν·f_e(t)`. -/
noncomputable def phiV (a b δ ν t : ℝ) : ℝ :=
  fe (mOf a b + kOf a b * δ * t) - ν * fe t

/-- Its derivative `φ′(t) = kδ·artanh(m + kδt) − ν·artanh t`. -/
noncomputable def phiV' (a b δ ν t : ℝ) : ℝ :=
  kOf a b * δ * artanh (mOf a b + kOf a b * δ * t) - ν * artanh t

lemma phiV_c (a b δ ν c : ℝ) : phiV a b δ ν c = fe (bOne a b δ c) - ν * fe c := by
  rw [phiV, bOne]

lemma phiV_neg_d (a b δ ν d : ℝ) :
    phiV a b δ ν (-d) = fe (bTwo a b δ d) - ν * fe d := by
  rw [phiV, bTwo, fe_neg]
  ring_nf

lemma phiV'_c (a b δ ν c : ℝ) :
    phiV' a b δ ν c = kOf a b * δ * artanh (bOne a b δ c) - ν * artanh c := by
  rw [phiV', bOne]

lemma phiV'_neg_d {a b δ ν d : ℝ} (hd0 : -1 < d) (hd1 : d < 1) :
    phiV' a b δ ν (-d) = kOf a b * δ * artanh (bTwo a b δ d) + ν * artanh d := by
  rw [phiV', bTwo, artanh_neg' hd0 hd1]
  ring_nf

lemma hasDerivAt_phiV {a b δ ν t : ℝ}
    (h0 : -1 < mOf a b + kOf a b * δ * t) (h1 : mOf a b + kOf a b * δ * t < 1)
    (ht0 : -1 < t) (ht1 : t < 1) :
    HasDerivAt (phiV a b δ ν) (phiV' a b δ ν t) t := by
  have hA := hasDerivAt_fe_affine (p := mOf a b) (K := kOf a b * δ) h0 h1
  have hB := (hasDerivAt_fe ht0 ht1).const_mul ν
  have h := hA.fun_sub hB
  have heq : artanh (mOf a b + kOf a b * δ * t) * (kOf a b * δ) - ν * artanh t
      = phiV' a b δ ν t := by rw [phiV']; ring
  rw [heq] at h
  exact h

/-- **(E4) is the chord condition.** -/
theorem E4ResPar_eq_zero_iff_chord (a b δ ν c d : ℝ) :
    E4ResPar a b δ ν c d = 0
      ↔ phiV a b δ ν c - phiV a b δ ν (-d) = (c + d) * phiV' a b δ ν c := by
  rw [E4ResPar, phiV_c, phiV_neg_d, phiV'_c]
  constructor <;> intro h <;> linarith

/-- **`ν = nuOf` is the equal-slope condition**: the chord is tangent at *both*
atoms. -/
theorem phiV'_eq_of_nuOf {a b δ c d : ℝ} (hd0 : -1 < d) (hd1 : d < 1)
    (hL : artanh c + artanh d ≠ 0) :
    phiV' a b δ (nuOf a b δ c d) c = phiV' a b δ (nuOf a b δ c d) (-d) := by
  rw [phiV'_c, phiV'_neg_d hd0 hd1, nuOf, DlOf, bOne, bTwo]
  field_simp
  ring

/-- **The mixture value is the tangent line at `0`.**  Under (E4) the mean-zero
two-point average of `φ` equals `φ(c) − c·φ′(c)`. -/
theorem mixture_eq_tangent {a b δ ν c d : ℝ} (hcd : c + d ≠ 0)
    (hE4 : E4ResPar a b δ ν c d = 0) :
    (d / (c + d)) * phiV a b δ ν c + (c / (c + d)) * phiV a b δ ν (-d)
      = phiV a b δ ν c - c * phiV' a b δ ν c := by
  have h := (E4ResPar_eq_zero_iff_chord a b δ ν c d).mp hE4
  field_simp
  linear_combination (-c) * h

/-- **The bitangency reduction.**  At any (E4) point,
`Φ = [φ(c) − c·φ′(c)] − φ(0) − μ·I(U;X)`, where `φ(0) = f_e(m)` and
`I(U;X) = A − f_e(m)`.  The first bracket is the value at `0` of the bitangent
line — the concave-envelope value of `φ` at `0`. -/
theorem PhiVal_eq_tangent_gain {a b δ μ ν c d : ℝ} (hcd : c + d ≠ 0)
    (hE4 : E4ResPar a b δ ν c d = 0) :
    PhiPar a b δ μ ν c d
      = (phiV a b δ ν c - c * phiV' a b δ ν c) - phiV a b δ ν 0
        - μ * (AOf a b - fe (mOf a b)) := by
  have hmix := mixture_eq_tangent hcd hE4
  have h0 : phiV a b δ ν 0 = fe (mOf a b) := by rw [phiV]; simp [fe_zero]
  rw [PhiPar, h0, ← hmix, phiV_c, phiV_neg_d]
  ring

/-- **The conjecture at an (E4) point is exactly a concave-envelope bound.**
`Φ ≤ 0` iff the gain of the bitangent line over `φ` at `0` is at most
`μ·I(U;X)`. -/
theorem PhiVal_nonpos_iff_gain_le {a b δ μ ν c d : ℝ} (hcd : c + d ≠ 0)
    (hE4 : E4ResPar a b δ ν c d = 0) :
    PhiPar a b δ μ ν c d ≤ 0
      ↔ (phiV a b δ ν c - c * phiV' a b δ ν c) - phiV a b δ ν 0
          ≤ μ * (AOf a b - fe (mOf a b)) := by
  rw [PhiVal_eq_tangent_gain hcd hE4]
  constructor <;> intro h <;> linarith

/-- **A sufficient condition.**  If the bitangent line does not rise above `φ(0)`
— i.e. `φ` has no concave-envelope gain at `0` — then `Φ ≤ 0` for every
non-negative price `μ`, since `I(U;X) ≥ 0`.  (At a genuine fixed point the two
tangency points are distinct, `c > 0 > −d`, so this case is vacuous; it is
recorded because it isolates *where* the difficulty sits: entirely in the gain.)
-/
theorem PhiVal_nonpos_of_no_gain {a b δ μ ν c d : ℝ} (hcd : c + d ≠ 0)
    (hE4 : E4ResPar a b δ ν c d = 0)
    (hμ : 0 ≤ μ) (hIUX : 0 ≤ AOf a b - fe (mOf a b))
    (hgain : (phiV a b δ ν c - c * phiV' a b δ ν c) - phiV a b δ ν 0 ≤ 0) :
    PhiPar a b δ μ ν c d ≤ 0 := by
  rw [PhiVal_nonpos_iff_gain_le hcd hE4]
  have : 0 ≤ μ * (AOf a b - fe (mOf a b)) := mul_nonneg hμ hIUX
  linarith

/-! ## Bounding the gain by MGL

MGL in bias coordinates *is* `mgl_jensen`: it governs the **pure scaling**
`s ↦ κ·s` that a BSC performs on a bias.  Applied to the V-side two-point law it
collapses the gain from an optimisation over laws to a **one-dimensional**
quantity: for any `t` matching the mixture in the sense `E[f_e(T)] = f_e(t)`,

```
E[f_e(κT)] − ν·E[f_e(T)]  ≤  f_e(κt) − ν·f_e(t)
```

No inverse `f_e⁻¹` is ever constructed — `t` enters as a hypothesis.

**Scope, stated honestly.**  This applies to `φ` only when `m = 0`, where
`φ(t) = f_e(kδ·t) − ν·f_e(t)` is a pure scaling.  For `m ≠ 0` the argument is the
*affine* `m + kδt`, which is not a channel scaling, and the two natural affine
analogues are **false**: with `f_e(τ*) = E[f_e(T)]`,

```
E[f_e(m+κT)] ≤ f_e(m+κτ*)                     fails by +0.32
E[f_e(m+κT)] ≤ ½[f_e(m+κτ*) + f_e(m−κτ*)]       fails by +0.019
```

(`numerics`, 165k samples).  So MGL as it stands bounds the gain on the
symmetric U-side only; the offset case needs a genuinely different ingredient,
not a repackaging of MGL.  Note `m = 0` forces `c = d` at a bitangent point —
`φ` is then even, so its bitangency points are symmetric — which is exactly the
slice §5d already settles.  The value here is that it pins down *what* an
affine MGL would have to supply. -/

/-- **The MGL gain bound.**  The two-point V-side objective is dominated by its
one-point (scalar) counterpart at any matching `t`. -/
theorem gain_le_of_mgl {κ ν q₁ q₂ t w₁ w₂ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hq1 : 0 < q₁) (hq2 : q₂ < 1) (ht1 : q₁ ≤ t) (ht2 : t ≤ q₂)
    (hsum : w₁ + w₂ = 1)
    (hmatch : w₁ * fe q₁ + w₂ * fe q₂ = fe t) :
    (w₁ * fe (κ * q₁) + w₂ * fe (κ * q₂)) - ν * (w₁ * fe q₁ + w₂ * fe q₂)
      ≤ fe (κ * t) - ν * fe t := by
  have h := mgl_jensen hκ0 hκ1 hq1 hq2 ht1 ht2 hsum hmatch
  rw [hmatch]
  linarith

lemma kOf_self {a : ℝ} (ha : a ≠ 0) : kOf a a = a := by
  rw [kOf]; field_simp; ring

lemma mOf_self (a : ℝ) : mOf a a = 0 := by rw [mOf]; simp

/-- `φ` on a symmetric U-side is the pure scaling `f_e(aδ·t) − ν·f_e(t)`. -/
lemma phiV_symm {a δ ν t : ℝ} (ha : a ≠ 0) :
    phiV a a δ ν t = fe (a * δ * t) - ν * fe t := by
  rw [phiV, mOf_self, kOf_self ha]; ring_nf

lemma phiV_symm_zero {a δ ν : ℝ} (ha : a ≠ 0) : phiV a a δ ν 0 = 0 := by
  rw [phiV_symm ha]; simp [fe_zero]

/-- **The gain of a symmetric-U-side fixed point is bounded by a one-dimensional
quantity.**  With `κ = aδ` and any `t` matching the V-side mixture, the
concave-envelope gain of `φ` at `0` is at most `φ(t)` — the same function
evaluated at a *single* point.  This is the MGL collapse. -/
theorem gain_le_phiV_of_mgl {a δ ν c d t : ℝ} (ha0 : 0 < a)
    (hκ0 : 0 < a * δ) (hκ1 : a * δ < 1)
    (hc0 : 0 < c) (hd1 : d < 1) (ht1 : c ≤ t) (ht2 : t ≤ d)
    (hcd : c + d ≠ 0)
    (hmatch : (d / (c + d)) * fe c + (c / (c + d)) * fe d = fe t) :
    (d / (c + d)) * phiV a a δ ν c + (c / (c + d)) * phiV a a δ ν (-d)
        - phiV a a δ ν 0
      ≤ phiV a a δ ν t := by
  have ha : a ≠ 0 := ne_of_gt ha0
  have hsum : d / (c + d) + c / (c + d) = 1 := by field_simp; ring
  have hneg : phiV a a δ ν (-d) = fe (a * δ * d) - ν * fe d := by
    rw [phiV_symm ha, show a * δ * -d = -(a * δ * d) by ring, fe_neg, fe_neg]
  have h := gain_le_of_mgl (κ := a * δ) (ν := ν) (q₁ := c) (q₂ := d) (t := t)
    (w₁ := d / (c + d)) (w₂ := c / (c + d)) hκ0 hκ1 hc0 hd1 ht1 ht2 hsum hmatch
  rw [phiV_symm ha, hneg, phiV_symm_zero ha, phiV_symm ha]
  linarith

/-! ## A closed form for the tangent gain — the missing inequality made explicit

The tangent-line gain at `x`, `Tan(x) = φ(x) − x·φ′(x) − φ(0)`, has an
**elementary closed form**: no `f_e`, no integrals, only `artanh` and
`A(y) = −½log(1−y²)`.  It follows from `f_e(y) = y·artanh y − A(y)` by pure
algebra — the `κ·x·L(m+κx)` terms cancel:

```
Tan(x) = ν·A(x) − A(m+κx) + A(m) + m·[L(m+κx) − L(m)]
```

At a bitangent (E4) point `Tan(c) = Tan(−d) = gain`, so the conjecture at such a
point is exactly

```
ν·A(c) − A(b₁) + A(m) + m·[L(b₁) − L(m)]  ≤  μ·(A − f_e(m))
```

an inequality in five real variables with no inverse function, no optimisation
and no integral. -/

/-- `A(y) = −½·log(1−y²)`. -/
noncomputable def AFun (y : ℝ) : ℝ := -(log (1 - y ^ 2)) / 2

/-- `f_e(y) = y·artanh y − A(y)`. -/
lemma fe_eq_mul_sub_AFun {y : ℝ} (h0 : -1 < y) (h1 : y < 1) :
    fe y = y * artanh y - AFun y := by
  have hp : (0 : ℝ) < 1 + y := by linarith
  have hm : (0 : ℝ) < 1 - y := by linarith
  have hlog : log (1 - y ^ 2) = log (1 + y) + log (1 - y) := by
    rw [show (1 : ℝ) - y ^ 2 = (1 + y) * (1 - y) by ring,
      Real.log_mul (ne_of_gt hp) (ne_of_gt hm)]
  rw [fe, AFun, artanh_eq_log_sub h0 h1, hlog]
  ring

lemma phiV_zero (a b δ ν : ℝ) : phiV a b δ ν 0 = fe (mOf a b) := by
  rw [phiV]; simp [fe_zero]

/-- The tangent-line gain of `φ` at `x`, measured against `φ(0)`. -/
noncomputable def tanGain (a b δ ν x : ℝ) : ℝ :=
  phiV a b δ ν x - x * phiV' a b δ ν x - phiV a b δ ν 0

/-- **Closed form for the tangent gain.**  Everything reduces to `artanh` and
`A`; the `κ·x·artanh(m+κx)` terms cancel identically. -/
theorem tanGain_eq {a b δ ν x : ℝ}
    (hx0 : -1 < x) (hx1 : x < 1)
    (hy0 : -1 < mOf a b + kOf a b * δ * x) (hy1 : mOf a b + kOf a b * δ * x < 1)
    (hm0 : -1 < mOf a b) (hm1 : mOf a b < 1) :
    tanGain a b δ ν x
      = ν * AFun x - AFun (mOf a b + kOf a b * δ * x) + AFun (mOf a b)
        + mOf a b * (artanh (mOf a b + kOf a b * δ * x) - artanh (mOf a b)) := by
  rw [tanGain, phiV_zero, phiV, phiV',
    fe_eq_mul_sub_AFun hy0 hy1, fe_eq_mul_sub_AFun hx0 hx1,
    fe_eq_mul_sub_AFun hm0 hm1]
  ring

/-- **The missing inequality, stated.**  At an (E4) point the conjecture is
`tanGain ≤ μ·I(U;X)`; combined with `PhiVal_nonpos_iff_gain_le` this is
`Φ ≤ 0`. -/
theorem PhiVal_nonpos_iff_tanGain_le {a b δ μ ν c d : ℝ} (hcd : c + d ≠ 0)
    (hE4 : E4ResPar a b δ ν c d = 0) :
    PhiPar a b δ μ ν c d ≤ 0
      ↔ tanGain a b δ ν c ≤ μ * (AOf a b - fe (mOf a b)) := by
  rw [PhiVal_nonpos_iff_gain_le hcd hE4, tanGain]

/-! ## Venue 1: the mirror pair

At a bitangent point the tangent gain is the same seen from either atom,
`Tan(c) = Tan(−d)`.  Feeding the closed form `tanGain_eq` into that equality
gives **(E4) with no `f_e` at all**:

```
ν·[A(c) − A(d)] = A(b₁) − A(b₂) − m·Δℓ                    mirror_identity
```

and, substituting `ν = kδΔℓ/(L(c)+L(d))`,

```
A(b₁) − A(b₂) = Δℓ·[ m + kδ·(A(c) − A(d))/(L(c) + L(d)) ]        (★)
```

Separately, the *weighted* average of the two tangent forms collapses because
`wc·c = wd·d = κ_V`, giving closed forms for `I` and the Lautum information that
need no fixed-point hypothesis at all:

```
I(U;V) = 𝒥 + A(m) − Ā + m·(L̄ − L(m))          Ā = E_V[A(b_v)],  L̄ = E_V[L(b_v)]
L(U;V) = Ā − A(m) − m·(L̄ − L(m))
```

**What this does and does not give.**  (★) puts the *constraint* into the same
elementary class (`log`, `artanh`) as the target (M) — previously the constraint
still carried `f_e`.  It does **not** prove (M): (★) is an identity-level
restatement, and identities cannot yield the inequality.  Its value is that the
constrained problem is now entirely elementary, which is exactly the
precondition for venue 4 (interval arithmetic / branch-and-bound). -/

lemma AFun_neg (y : ℝ) : AFun (-y) = AFun y := by rw [AFun, AFun]; ring_nf

/-- **The mirror property**: at an (E4) point with equal slopes, the tangent gain
is the same from either atom. -/
theorem tanGain_mirror {a b δ ν c d : ℝ}
    (hE4 : E4ResPar a b δ ν c d = 0)
    (hslope : phiV' a b δ ν c = phiV' a b δ ν (-d)) :
    tanGain a b δ ν c = tanGain a b δ ν (-d) := by
  have hchord := (E4ResPar_eq_zero_iff_chord a b δ ν c d).mp hE4
  rw [tanGain, tanGain]
  linear_combination hchord + d * hslope

/-- **(E4) with no `f_e`.**  Equating the two closed forms of the tangent gain. -/
theorem mirror_identity {a b δ ν c d : ℝ}
    (hE4 : E4ResPar a b δ ν c d = 0)
    (hslope : phiV' a b δ ν c = phiV' a b δ ν (-d))
    (hc0 : -1 < c) (hc1 : c < 1) (hd0 : -1 < d) (hd1 : d < 1)
    (hy0 : -1 < bOne a b δ c) (hy1 : bOne a b δ c < 1)
    (hz0 : -1 < bTwo a b δ d) (hz1 : bTwo a b δ d < 1)
    (hm0 : -1 < mOf a b) (hm1 : mOf a b < 1) :
    ν * (AFun c - AFun d)
      = AFun (bOne a b δ c) - AFun (bTwo a b δ d)
        - mOf a b * (artanh (bOne a b δ c) - artanh (bTwo a b δ d)) := by
  have hmir := tanGain_mirror hE4 hslope
  have hb2 : mOf a b + kOf a b * δ * -d = bTwo a b δ d := by rw [bTwo]; ring
  have h1 := tanGain_eq (a := a) (b := b) (δ := δ) (ν := ν) (x := c) hc0 hc1
    (by rw [bOne] at hy0; exact hy0) (by rw [bOne] at hy1; exact hy1) hm0 hm1
  have h2 := tanGain_eq (a := a) (b := b) (δ := δ) (ν := ν) (x := -d)
    (by linarith) (by linarith)
    (by rw [hb2]; exact hz0) (by rw [hb2]; exact hz1) hm0 hm1
  rw [hb2] at h2
  rw [show mOf a b + kOf a b * δ * c = bOne a b δ c from by rw [bOne]] at h1
  rw [AFun_neg] at h2
  rw [h1, h2] at hmir
  linarith [hmir]

/-! ### Closed forms for `I` and the Lautum information -/

noncomputable def ABar (a b δ c d : ℝ) : ℝ :=
  (d / (c + d)) * AFun (bOne a b δ c) + (c / (c + d)) * AFun (bTwo a b δ d)

noncomputable def LBar (a b δ c d : ℝ) : ℝ :=
  (d / (c + d)) * artanh (bOne a b δ c) + (c / (c + d)) * artanh (bTwo a b δ d)

/-- **`I(U;V) = 𝒥 + A(m) − Ā + m·(L̄ − L(m))`.**  The `f_e`'s dissolve into
`y·artanh y − A(y)`, and `wc·c = wd·d = κ_V` turns the surviving `artanh` terms
into exactly `𝒥 = kδκ_V·Δℓ`.  No fixed-point hypothesis is used. -/
theorem mutualTP_eq_jeffreys_add {a b δ c d : ℝ} (hab : a + b ≠ 0) (hcd : c + d ≠ 0)
    (hm1 : 0 < 1 + mOf a b) (hm2 : 0 < 1 - mOf a b)
    (h1 : 0 < 1 + a * (δ * c)) (h2 : 0 < 1 - b * (δ * c))
    (h3 : 0 < 1 - a * (δ * d)) (h4 : 0 < 1 + b * (δ * d))
    (hy0 : -1 < bOne a b δ c) (hy1 : bOne a b δ c < 1)
    (hz0 : -1 < bTwo a b δ d) (hz1 : bTwo a b δ d < 1)
    (hmm0 : -1 < mOf a b) (hmm1 : mOf a b < 1) :
    mutualTP δ a b c d
      = jeffreysTP δ a b c d + AFun (mOf a b) - ABar a b δ c d
        + mOf a b * (LBar a b δ c d - artanh (mOf a b)) := by
  rw [mutualTP_eq hab hcd hm1 hm2 h1 h2 h3 h4,
    jeffreysTP_eq hab hcd hm1 hm2 h1 h2 h3 h4,
    fe_eq_mul_sub_AFun hy0 hy1, fe_eq_mul_sub_AFun hz0 hz1,
    fe_eq_mul_sub_AFun hmm0 hmm1, ABar, LBar, DlOf, kapOf, bOne, bTwo]
  field_simp
  ring

/-- **The Lautum information in closed form**: `L(U;V) = Ā − A(m) − m·(L̄ − L(m))`. -/
theorem lautum_closed {a b δ c d : ℝ} (hab : a + b ≠ 0) (hcd : c + d ≠ 0)
    (hm1 : 0 < 1 + mOf a b) (hm2 : 0 < 1 - mOf a b)
    (h1 : 0 < 1 + a * (δ * c)) (h2 : 0 < 1 - b * (δ * c))
    (h3 : 0 < 1 - a * (δ * d)) (h4 : 0 < 1 + b * (δ * d))
    (hy0 : -1 < bOne a b δ c) (hy1 : bOne a b δ c < 1)
    (hz0 : -1 < bTwo a b δ d) (hz1 : bTwo a b δ d < 1)
    (hmm0 : -1 < mOf a b) (hmm1 : mOf a b < 1) :
    jeffreysTP δ a b c d - mutualTP δ a b c d
      = ABar a b δ c d - AFun (mOf a b) - mOf a b * (LBar a b δ c d - artanh (mOf a b)) := by
  rw [mutualTP_eq_jeffreys_add hab hcd hm1 hm2 h1 h2 h3 h4 hy0 hy1 hz0 hz1 hmm0 hmm1]
  ring

/-! ## Venue 5: (M) is a one-sided threshold on `ν`

`Tan(c) = ν·A(c) − A(b₁) + A(m) + m·[L(b₁) − L(m)]` is **linear in `ν`** with
coefficient `A(c) > 0`, and the right-hand side `μ·I(U;X)` contains no `ν` at
all.  So (M) is exactly a threshold condition:

```
(M)  ⟺  ν ≤ ν* := [ μ·I(U;X) + A(b₁) − A(m) − m·(L(b₁) − L(m)) ] / A(c)
```

`ν` is pinned at a fixed point by `ν = kδΔℓ/(L(c)+L(d))`, so the conjecture at
an (E4) point is the single scalar comparison `ν ≤ ν*`.  Note this is *not* a
decoupling: `ν*` depends on the same data as `ν`, so bounding the two at
independently chosen configurations is precisely the eleven-times-refuted error. -/

lemma AFun_pos {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : 0 < AFun y := by
  rw [AFun]
  have h1 : (0:ℝ) < 1 - y ^ 2 := by nlinarith
  have h2 : (1:ℝ) - y ^ 2 < 1 := by nlinarith
  have := Real.log_neg h1 h2
  linarith

lemma AFun_nonneg {y : ℝ} (hy0 : -1 < y) (hy1 : y < 1) : 0 ≤ AFun y := by
  rw [AFun]
  have h1 : (0:ℝ) < 1 - y ^ 2 := by nlinarith
  have h2 : (1:ℝ) - y ^ 2 ≤ 1 := by nlinarith
  have := Real.log_nonpos (le_of_lt h1) h2
  linarith

/-- **Venue 5: the conjecture at an (E4) point is the threshold `ν ≤ ν*`.** -/
theorem PhiVal_nonpos_iff_nu_le {a b δ μ ν c d : ℝ} (hcd : c + d ≠ 0)
    (hE4 : E4ResPar a b δ ν c d = 0)
    (hc0 : 0 < c) (hc1 : c < 1)
    (hy0 : -1 < bOne a b δ c) (hy1 : bOne a b δ c < 1)
    (hm0 : -1 < mOf a b) (hm1 : mOf a b < 1) :
    PhiPar a b δ μ ν c d ≤ 0
      ↔ ν ≤ (μ * (AOf a b - fe (mOf a b)) + AFun (bOne a b δ c) - AFun (mOf a b)
              - mOf a b * (artanh (bOne a b δ c) - artanh (mOf a b))) / AFun c := by
  have hA : 0 < AFun c := AFun_pos hc0 hc1
  have hb : mOf a b + kOf a b * δ * c = bOne a b δ c := by rw [bOne]
  have ht := tanGain_eq (a := a) (b := b) (δ := δ) (ν := ν) (x := c)
    (by linarith) hc1 (by rw [hb]; exact hy0) (by rw [hb]; exact hy1) hm0 hm1
  rw [hb] at ht
  rw [PhiVal_nonpos_iff_tanGain_le hcd hE4, ht, le_div_iff₀ hA]
  constructor <;> intro h <;> linarith

/-! ## `G` in terms of `A`, and the two-sided bound `0 < G < 1/2`

`f_e(y)/y = artanh y − A(y)/y` turns `G` into a *deficit* form:

```
G(p,q) = 1 − [A(p)/p + A(q)/q]/(L(p) + L(q))
```

and the trapezoid bound `f_e(y) < y·artanh y/2` gives `G(p,q) < 1/2` — i.e. both
`ρ(U;X)` and `ρ(Y;V)` lie strictly below `1/2`, the same fact that drives (A).
Together with (A) this yields `margin > G(a,b) + G(c,d) − 1/2`; since (B)
(`G+G ≥ 1/2`) is refuted, a *uniform* margin cannot come from this route — see
`NOTES.md` §6. -/

theorem GFun_eq_one_sub {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hL : artanh p + artanh q ≠ 0) :
    GFun p q = 1 - (AFun p / p + AFun q / q) / (artanh p + artanh q) := by
  rw [GFun, fe_eq_mul_sub_AFun (by linarith) hp1, fe_eq_mul_sub_AFun (by linarith) hq1]
  field_simp
  ring

theorem GFun_pos {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    0 < GFun p q := by
  have hLp := Real.artanh_pos (Set.mem_Ioo.mpr ⟨hp0, hp1⟩)
  have hLq := Real.artanh_pos (Set.mem_Ioo.mpr ⟨hq0, hq1⟩)
  have hPp := fe_pos hp0 hp1
  have hPq := fe_pos hq0 hq1
  rw [GFun]
  exact div_pos (by positivity) (by linarith)

/-- **`ρ(U;X) < 1/2` and `ρ(Y;V) < 1/2`** — the trapezoid bound again. -/
theorem GFun_lt_half {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    GFun p q < 1 / 2 := by
  have hLp := Real.artanh_pos (Set.mem_Ioo.mpr ⟨hp0, hp1⟩)
  have hLq := Real.artanh_pos (Set.mem_Ioo.mpr ⟨hq0, hq1⟩)
  have hL : 0 < artanh p + artanh q := by linarith
  have hp := fe_le_half_mul hp0 hp1
  have hq := fe_le_half_mul hq0 hq1
  rw [GFun, div_lt_iff₀ hL]
  have h1 : fe p / p < artanh p / 2 := by
    rw [div_lt_div_iff₀ hp0 (by norm_num : (0:ℝ) < 2)]
    linarith
  have h2 : fe q / q < artanh q / 2 := by
    rw [div_lt_div_iff₀ hq0 (by norm_num : (0:ℝ) < 2)]
    linarith
  linarith

/-! ## The conjecture in its correct form: `F ≤ J_sym`

The conjecture is `sup_𝒜 F = sup_ℬ F`, i.e. `F ≤ J_sym := sup_ℬ F`.  It is **not**
`F ≤ 0`: since `g(0,0) = 0` we have `J_sym ≥ 0`, so `F ≤ 0` is *sufficient* but
not necessary — and it genuinely fails near the symmetric locus (see `NOTES.md`
§6).

The `SignFlip` decomposition gives the correct statement directly.  With

```
g(p,q) = f_e(δpq) − μ·f_e(p) − ν·f_e(q)        (= the value of the BSC pair (p,q))
```

the Lagrangian of a two-point pair splits into a part seeing only *magnitudes*
and the odd gain `Ω`:

```
F = Σ wᵢⱼ · g(|sᵢ|,|tⱼ|) + Ω
```

The first term is an average of four values of `g`, hence at most `max g ≤ J_sym`.
Therefore

> **`Ω ≤ 0`  ⟹  `F ≤ J_sym`**

and `omegaTwoPoint_neg` proves `Ω < 0` whenever the two skews point the *same*
way.  So **same-direction skews never beat the symmetric optimum** — half the
configuration space is disposed of unconditionally, with no multiplier
hypothesis and no fixed-point hypothesis. -/

/-- The variance of `|S|`, the driver of the Jensen gap: it vanishes exactly on
the symmetric locus `a = b`. -/
theorem absVar_eq {a b : ℝ} (hab : a + b ≠ 0) :
    a * b - kOf a b ^ 2 = a * b * (a - b) ^ 2 / (a + b) ^ 2 := by
  rw [kOf]; field_simp; ring

/-- `E[|S|] = k` and `E[|S|²] = ab`. -/
theorem absMean_eq {a b : ℝ} (hab : a + b ≠ 0) :
    (b * a + a * b) / (a + b) = kOf a b := by
  rw [kOf]; field_simp; ring

theorem absSq_eq {a b : ℝ} (hab : a + b ≠ 0) :
    (b * a ^ 2 + a * b ^ 2) / (a + b) = a * b := by
  field_simp

/-- The magnitude average never exceeds the largest of the four corner values. -/
theorem gSum_le_max4 {δ μ ν a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    gSum δ μ ν a b c d
      ≤ max (max (gSym δ μ ν a c) (gSym δ μ ν a d))
            (max (gSym δ μ ν b c) (gSym δ μ ν b d)) :=
  gSum_le_of_le (le_of_lt ha) (le_of_lt hb) (le_of_lt hc) (le_of_lt hd)
    (by linarith) (by linarith)
    (le_max_of_le_left (le_max_left _ _)) (le_max_of_le_left (le_max_right _ _))
    (le_max_of_le_right (le_max_left _ _)) (le_max_of_le_right (le_max_right _ _))

/-- **(S) stated.**  `deficit := M − gSum` for any common bound `M` on the four
corner values; the open claim is `Ω ≤ deficit`, and it is *equivalent* to
`F ≤ M`.  With `M = J_sym` this is exactly the conjecture on the opposite-skew
half. -/
theorem lagrTwoPoint_le_iff_omega_le_deficit {δ μ ν a b c d M : ℝ}
    (hab : a + b ≠ 0) (hcd : c + d ≠ 0) :
    lagrTwoPoint δ μ ν a b c d ≤ M
      ↔ OmegaTwoPoint δ a b c d ≤ M - gSum δ μ ν a b c d := by
  rw [lagrTwoPoint_eq_gSum_add_Omega hab hcd]
  constructor <;> intro h <;> linarith

/-! ## The second-order coefficients and the discriminant for (S)

Expanding `a,b = s ± α`, `c,d = t ∓ β` about a critical point `(s,t)` of `g`
(so `μ = δt·L(z)/L(s)`, `ν = δs·L(z)/L(t)`, `z = δst`):

```
Ω      ≈ α·β · E(z)/(s·t)              E(z) := z/(1−z²) − artanh z  > 0
−g_pp  = (z/s²)·A_s                    A_s  := s·L(z)/((1−s²)L(s)) − z/(1−z²)
−g_qq  = (z/t²)·A_t                    A_t  := t·L(z)/((1−t²)L(t)) − z/(1−z²)
deficit ≈ ½(z/s²)A_s·α² + ½(z/t²)A_t·β²
```

`E > 0` is `artanh_lt_div`, and `E` is exactly the numerator of `(MFun δ)′`
(`hasDerivAt_MFun`) — the same object that drives the sign flip.  The
second-order form of (S) is then a quadratic-form positivity, and the `s²t²`
cancels:

> **discriminant:  `E(z)² ≤ z²·A_s·A_t`**    (`secondOrder_of_discriminant`)

⚠ The discriminant is **false** at merely *local* critical points (ratio up to
`2.074`); it holds — with a factor `~2000` to spare — only when `(s,t)` is the
**global** maximiser of `g`, which is the hypothesis the deficit actually needs.
See `NOTES.md` §6. -/

/-- `E(z) = z/(1−z²) − artanh z`, the excess driving `Ω`. -/
noncomputable def EFun (z : ℝ) : ℝ := z / (1 - z ^ 2) - artanh z

theorem EFun_pos {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) : 0 < EFun z := by
  have := artanh_lt_div hz0 hz1
  rw [EFun]; linarith

/-- **`E` is the numerator of `(MFun δ)′`** — the derivative whose positivity is
the supermodularity behind the global sign flip. -/
lemma hasDerivAt_MFun {δ u : ℝ} (hu : u ≠ 0) (h0 : -1 < δ * u) (h1 : δ * u < 1) :
    HasDerivAt (MFun δ) (EFun (δ * u) / u ^ 2) u := by
  have hne : (1 : ℝ) - (δ * u) ^ 2 ≠ 0 := by nlinarith
  have hA := hasDerivAt_artanh_mul h0 h1
  have h := (hA.fun_div (hasDerivAt_id' (x := u)) hu).sub_const δ
  have hfun : (fun x : ℝ => artanh (δ * x) / x - δ) = MFun δ := by
    funext x; rw [MFun]
  rw [hfun] at h
  have heq : (δ / (1 - (δ * u) ^ 2) * u - artanh (δ * u) * 1) / u ^ 2
      = EFun (δ * u) / u ^ 2 := by
    rw [EFun]; field_simp
  rwa [heq] at h

/-- `A_s = s·artanh z/((1−s²)·artanh s) − z/(1−z²)`; `A_s > 0` is exactly
`g_pp < 0`, i.e. local maximality in the `s` direction. -/
noncomputable def AFactor (s z : ℝ) : ℝ :=
  s * artanh z / ((1 - s ^ 2) * artanh s) - z / (1 - z ^ 2)

/-- **The quadratic-form step.**  `c₁α² + c₂β² ≥ P·αβ` for all `α,β` exactly when
`P² ≤ 4c₁c₂` — proved from `4c₁(c₁α² + c₂β² − Pαβ) = (2c₁α − Pβ)² + (4c₁c₂ − P²)β²`. -/
theorem quadForm_nonneg {c₁ c₂ P α β : ℝ} (hc₁ : 0 < c₁) (_hc₂ : 0 < c₂)
    (hdisc : P ^ 2 ≤ 4 * c₁ * c₂) :
    0 ≤ c₁ * α ^ 2 + c₂ * β ^ 2 - P * α * β := by
  have key : 0 ≤ (2 * c₁ * α - P * β) ^ 2 + (4 * c₁ * c₂ - P ^ 2) * β ^ 2 := by
    have h1 : (0:ℝ) ≤ (2 * c₁ * α - P * β) ^ 2 := sq_nonneg _
    have h2 : (0:ℝ) ≤ (4 * c₁ * c₂ - P ^ 2) * β ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg β)
    linarith
  nlinarith [key, hc₁]

/-- **(S) to second order follows from the discriminant.**  With
`c₁ = ½(z/s²)A_s`, `c₂ = ½(z/t²)A_t`, `P = E(z)/(st)`, the condition
`E(z)² ≤ z²·A_s·A_t` gives `deficit ≥ Ω` for every skew pair `(α,β)`. -/
theorem secondOrder_of_discriminant {s t z As At α β : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hz : 0 < z) (hAs : 0 < As) (hAt : 0 < At)
    (hdisc : EFun z ^ 2 ≤ z ^ 2 * (As * At)) :
    EFun z / (s * t) * α * β
      ≤ (z / s ^ 2 * As) / 2 * α ^ 2 + (z / t ^ 2 * At) / 2 * β ^ 2 := by
  set c₁ : ℝ := (z / s ^ 2 * As) / 2 with hc₁def
  set c₂ : ℝ := (z / t ^ 2 * At) / 2 with hc₂def
  have hc₁ : 0 < c₁ := by rw [hc₁def]; positivity
  have hc₂ : 0 < c₂ := by rw [hc₂def]; positivity
  have hst : (0:ℝ) < s ^ 2 * t ^ 2 := by positivity
  have hd : (EFun z / (s * t)) ^ 2 ≤ 4 * c₁ * c₂ := by
    rw [hc₁def, hc₂def]
    rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < (s * t) ^ 2)]
    have : 4 * ((z / s ^ 2 * As) / 2) * ((z / t ^ 2 * At) / 2) * (s * t) ^ 2
        = z ^ 2 * (As * At) := by field_simp; ring
    rw [this]
    exact hdisc
  have := quadForm_nonneg (α := α) (β := β) hc₁ hc₂ hd
  linarith

/-! ## 6c: an exact, global, multiplier-free reduction of (S)

The second-order route only reaches infinitesimal skews.  This reduction is
**exact** — no expansion — and eliminates `μ` and `ν` entirely.

Pick the symmetric competitor by **MGL matching**: choose `s`, `t` with

```
f_e(s) = E[f_e(|S|)] = (b·f_e(a) + a·f_e(b))/(a+b),    f_e(t) = E[f_e(|T|)]
```

(such `s,t` exist: `f_e` is continuous and increasing from `0` to `log 2`, and the
averages lie in that range).  Then `(s,t)` is a legitimate BSC pair, so
`J_sym ≥ g(s,t)`.  In `g(s,t) − Σ wᵢⱼ·g(|sᵢ|,|tⱼ|)` the multiplier terms cancel
**identically** — the same averages appear on both sides — leaving

```
g(s,t) − gSum = f_e(δst) − E[f_e(δ|S||T|)]        the MGL gap, ≥ 0 by mgl_jensen
```

Therefore

> **(S′)**  `Ω ≤ f_e(δst) − E[f_e(δ|S||T|)]`   ⟹   `F ≤ g(s,t) ≤ J_sym`

with **no `μ`, no `ν`, and no maximisation over the symmetric family**.  This is
the honest replacement for the second-order discriminant: same content, valid for
*all* skews, and stated purely in terms of `f_e` and `Ω`. -/

/-- `E[f_e(δ|S||T|)]`, the four-atom average of `f_e` at the product magnitudes. -/
noncomputable def feProd (δ a b c d : ℝ) : ℝ :=
  (b * d * fe (δ * (a * c)) + b * c * fe (δ * (a * d))
    + a * d * fe (δ * (b * c)) + a * c * fe (δ * (b * d))) / ((a + b) * (c + d))

/-- The MGL gap `f_e(δst) − E[f_e(δ|S||T|)]`, non-negative by `mgl_jensen`. -/
noncomputable def mglGap (δ a b c d s t : ℝ) : ℝ := fe (δ * (s * t)) - feProd δ a b c d

/-- **The multipliers cancel.**  Under MGL matching, `g(s,t) − gSum` is the MGL
gap — independent of `μ` and `ν`. -/
theorem gSym_sub_gSum_eq {δ μ ν a b c d s t : ℝ} (hab : a + b ≠ 0) (hcd : c + d ≠ 0)
    (hs : (b * fe a + a * fe b) / (a + b) = fe s)
    (ht : (d * fe c + c * fe d) / (c + d) = fe t) :
    gSym δ μ ν s t - gSum δ μ ν a b c d = mglGap δ a b c d s t := by
  rw [gSym, gSum, gSym, gSym, gSym, gSym, mglGap, feProd, ← hs, ← ht]
  field_simp
  ring

/-- **(S′) is equivalent to beating the matched symmetric pair.** -/
theorem lagrTwoPoint_le_gSym_iff {δ μ ν a b c d s t : ℝ}
    (hab : a + b ≠ 0) (hcd : c + d ≠ 0)
    (hs : (b * fe a + a * fe b) / (a + b) = fe s)
    (ht : (d * fe c + c * fe d) / (c + d) = fe t) :
    lagrTwoPoint δ μ ν a b c d ≤ gSym δ μ ν s t
      ↔ OmegaTwoPoint δ a b c d ≤ mglGap δ a b c d s t := by
  rw [lagrTwoPoint_eq_gSum_add_Omega hab hcd, ← gSym_sub_gSum_eq (μ := μ) (ν := ν) hab hcd hs ht]
  constructor <;> intro h <;> linarith

/-- **(S′) ⟹ the conjecture at that configuration.**  If the odd gain is at most
the MGL gap, then `F` does not beat the matched symmetric pair, hence not
`J_sym`. -/
theorem lagrTwoPoint_le_of_omega_le_mglGap {δ μ ν a b c d s t M : ℝ}
    (hab : a + b ≠ 0) (hcd : c + d ≠ 0)
    (hs : (b * fe a + a * fe b) / (a + b) = fe s)
    (ht : (d * fe c + c * fe d) / (c + d) = fe t)
    (hM : gSym δ μ ν s t ≤ M)
    (hS : OmegaTwoPoint δ a b c d ≤ mglGap δ a b c d s t) :
    lagrTwoPoint δ μ ν a b c d ≤ M :=
  le_trans ((lagrTwoPoint_le_gSym_iff hab hcd hs ht).mpr hS) hM

/-! ## Why (S) has room: `f_e(δpq)` is supermodular

Instantiating the reduction at the **argmax** of `g` eliminates `μ,ν` by
duality.  For a fixed configuration the conjecture must hold for *all*
`(μ,ν) ≥ 0`, and with `u = f_e(p)`, `v = f_e(q)`,
`Φ(u,v) := f_e(δ·f_e⁻¹(u)·f_e⁻¹(v))`, `U₀ = E[f_e(|S|)]`, `V₀ = E[f_e(|T|)]`:

```
max g − gSum = max_{u,v}[ Φ(u,v) − μ(u−U₀) − ν(v−V₀) ] − E[Φ(uᵢ,vⱼ)]
```

and minimising over `(μ,ν)` is Legendre duality, returning the **concave
envelope**:

> **(S\*)**  `Ω ≤ conc(Φ)(U₀,V₀) − E[Φ(uᵢ,vⱼ)]`

MGL is precisely *one-variable* concavity of `Φ`.  Were `Φ` jointly concave we
would have `conc(Φ) = Φ` and (S\*) would collapse to the refuted (S′) — so the
framework **requires** joint concavity to fail.  It does, everywhere: the
diagonal Hessian entries are `≤ 0` (MGL) but the cross term is large and
positive, `det < 0` at every sampled point (`NOTES.md` §6).

The cross term is supermodularity, and in `(p,q)` coordinates it needs no `f_e⁻¹`:
a monotone reparametrisation preserves supermodularity, and

```
∂²/∂p∂q f_e(δpq) = δ·[artanh z + z/(1−z²)] > 0,     z = δpq
```

Equivalently, the `p`-slice `f_e(δpq₂) − f_e(δpq₁)` has derivative
`[z₂·artanh z₂ − z₁·artanh z₁]/p`, positive because `z ↦ z·artanh z` is strictly
increasing.  **So the very mechanism that generates the odd gain `Ω`
(supermodularity) is what creates the concave-envelope slack that must absorb
it.** -/

/-- The corner spread is non-negative. -/
theorem gSum_le_gMax4 {δ μ ν a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    gSum δ μ ν a b c d ≤ gMax4 δ μ ν a b c d :=
  gSum_le_max4 ha hb hc hd

/-- **`Δ_g < 0` under opposite skews**, by supermodularity of `f_e(δpq)`. -/
theorem gSym_mixed_diff_neg {δ μ ν a b c d : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hb0 : 0 < b) (hba : b < a) (ha1 : a ≤ 1)
    (hc0 : 0 < c) (hcd : c < d) (hd1 : d ≤ 1) :
    gSym δ μ ν a c - gSym δ μ ν a d - gSym δ μ ν b c + gSym δ μ ν b d < 0 := by
  rw [gSym_mixed_diff_eq]
  have h := fe_mul_supermodular (δ := δ) (p₁ := b) (p₂ := a) (q₁ := c) (q₂ := d)
    hδ0 hδ1 hb0 hba ha1 hc0 hcd hd1
  linarith

/-- **The pointwise fact the whole (S4) argument rests on.** -/
theorem le_one_add_sq_mul_artanh {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    z ≤ (1 + z ^ 2) * artanh z := by
  have h := self_lt_artanh hz0 hz1
  nlinarith [sq_nonneg z, Real.artanh_pos (Set.mem_Ioo.mpr ⟨hz0, hz1⟩)]

lemma gSum_swap (δ μ ν a b c d : ℝ) :
    gSum δ μ ν b a d c = gSum δ μ ν a b c d := by
  rw [gSum, gSum]; ring

lemma gMax4_swap (δ μ ν a b c d : ℝ) :
    gMax4 δ μ ν b a d c = gMax4 δ μ ν a b c d := by
  rw [gMax4, gMax4]
  rw [max_comm (gSym δ μ ν b d) (gSym δ μ ν b c), max_comm (gSym δ μ ν a d) (gSym δ μ ν a c)]
  exact max_comm _ _


/-! ### From `Closedness.lean` -/


/-! ## The space of transition functions -/

/-- Transition functions of binary channels: non-negative with unit row sums. -/
def TrSet : Set (Bool → Bool → ℝ) :=
  {f | (∀ i j, 0 ≤ f i j) ∧ ∀ i, f i false + f i true = 1}

lemma mem_TrSet_of_chan (c : Chan) : c.tr ∈ TrSet := ⟨c.nonneg, c.sum_one⟩

/-- Every transition function in `TrSet` comes from a `Chan`. -/
noncomputable def chanOfTr {f : Bool → Bool → ℝ} (hf : f ∈ TrSet) : Chan where
  tr := f
  nonneg := hf.1
  sum_one := hf.2

@[simp] lemma chanOfTr_tr {f : Bool → Bool → ℝ} (hf : f ∈ TrSet) :
    (chanOfTr hf).tr = f := rfl

lemma TrSet_le_one {f : Bool → Bool → ℝ} (hf : f ∈ TrSet) (i j : Bool) : f i j ≤ 1 := by
  obtain ⟨hpos, hsum⟩ := hf
  cases j
  · have := hsum i; have := hpos i true; linarith
  · have := hsum i; have := hpos i false; linarith

lemma isClosed_TrSet : IsClosed TrSet := by
  have h1 : IsClosed {f : Bool → Bool → ℝ | ∀ i j, 0 ≤ f i j} := by
    have : {f : Bool → Bool → ℝ | ∀ i j, 0 ≤ f i j}
        = ⋂ i, ⋂ j, {f : Bool → Bool → ℝ | 0 ≤ f i j} := by
      ext f; simp [Set.mem_iInter]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const (by fun_prop)
  have h2 : IsClosed {f : Bool → Bool → ℝ | ∀ i, f i false + f i true = 1} := by
    have : {f : Bool → Bool → ℝ | ∀ i, f i false + f i true = 1}
        = ⋂ i, {f : Bool → Bool → ℝ | f i false + f i true = 1} := by
      ext f; simp [Set.mem_iInter]
    rw [this]
    exact isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const
  exact h1.inter h2

lemma isBounded_TrSet : Bornology.IsBounded TrSet := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨1, fun f hf => ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [hf.1 i j], TrSet_le_one hf i j⟩

lemma isCompact_TrSet : IsCompact TrSet :=
  Metric.isCompact_of_isClosed_isBounded isClosed_TrSet isBounded_TrSet

/-! ## The value map and the cone -/

/-- The triple `(I(U;V), I(U;X), I(Y;V))` as a function of the two transition
functions.  Depends on a `Chan` only through its `tr` field, which is why the
whole argument can be run on `TrSet`. -/
noncomputable def valOf (p : ℝ) (fg : (Bool → Bool → ℝ) × (Bool → Bool → ℝ)) : ℝ × ℝ × ℝ :=
  (mutualInfo (fun u v => dsbs p false false * fg.1 false u * fg.2 false v
      + dsbs p false true * fg.1 false u * fg.2 true v
      + dsbs p true false * fg.1 true u * fg.2 false v
      + dsbs p true true * fg.1 true u * fg.2 true v),
   mutualInfo (fun u x => fg.1 x u / 2),
   mutualInfo (fun y v => fg.2 y v / 2))

lemma valOf_chan (p : ℝ) (cL cR : Chan) :
    valOf p (cL.tr, cR.tr)
      = (mutualInfo (jointUV p cL cR), mutualInfo (jointUX cL), mutualInfo (jointYV cR)) := rfl

lemma continuous_valOf (p : ℝ) : Continuous (valOf p) := by
  unfold valOf mutualInfo entropy1 entropy2 marg₁ marg₂
  fun_prop

/-- The compact set of attainable value triples. -/
def valSet (p : ℝ) : Set (ℝ × ℝ × ℝ) := valOf p '' (TrSet ×ˢ TrSet)

lemma isCompact_valSet (p : ℝ) : IsCompact (valSet p) :=
  (isCompact_TrSet.prod isCompact_TrSet).image (continuous_valOf p)

theorem regionA_eq_add_cone (p : ℝ) : regionA p = valSet p + coneC := by
  ext R
  constructor
  · rintro ⟨cL, cR, h1, h2, h3⟩
    refine ⟨valOf p (cL.tr, cR.tr), ⟨(cL.tr, cR.tr), ⟨mem_TrSet_of_chan cL, mem_TrSet_of_chan cR⟩, rfl⟩,
      R - valOf p (cL.tr, cR.tr), ?_, by ring⟩
    rw [valOf_chan]
    exact ⟨by simp; linarith, by simp; linarith, by simp; linarith⟩
  · rintro ⟨k, ⟨fg, ⟨hf, hg⟩, rfl⟩, c, hc, rfl⟩
    refine ⟨chanOfTr hf, chanOfTr hg, ?_, ?_, ?_⟩
    · have hrfl : mutualInfo (jointUX (chanOfTr hf)) = (valOf p fg).2.1 := rfl
      rw [hrfl]
      simp only [Prod.snd_add, Prod.fst_add]
      linarith [hc.2.1]
    · have hrfl : mutualInfo (jointYV (chanOfTr hg)) = (valOf p fg).2.2 := rfl
      rw [hrfl]
      simp only [Prod.snd_add]
      linarith [hc.2.2]
    · have hrfl : mutualInfo (jointUV p (chanOfTr hf) (chanOfTr hg)) = (valOf p fg).1 := rfl
      rw [hrfl]
      simp only [Prod.fst_add]
      linarith [hc.1]

theorem isClosed_regionA (p : ℝ) : IsClosed (regionA p) := by
  rw [regionA_eq_add_cone]
  exact isClosed_coneC.add_left_of_isCompact (isCompact_valSet p)

/-! ## `regionB` is closed

`ℬ` is parametrised by just `(a,b) ∈ [0,1]²`, so the same argument is shorter. -/

theorem isClosed_regionB (p : ℝ) : IsClosed (regionB p) := by
  rw [regionB_eq_add_cone]
  exact isClosed_coneC.add_left_of_isCompact (isCompact_valBSet p)

/-! ## Convex hulls of compact sets in `ℝ³`

Mathlib (v4.32.2) has only `Set.Finite.isCompact_convexHull`; the general
finite-dimensional statement is missing.  We supply it for `ℝ³` by the standard
Carathéodory route: every point of `convexHull S` is a convex combination of at
most `4` points of `S`, so

```
convexHull S = (fun wx => ∑ i, wx.1 i • wx.2 i) '' (stdSimplex ℝ (Fin 4) ×ˢ {x | ∀ i, x i ∈ S})
```

a continuous image of a compact set. -/

theorem isClosed_convexHull_regionA (p : ℝ) : IsClosed (convexHull ℝ (regionA p)) := by
  rw [regionA_eq_add_cone, convexHull_add, convex_coneC.convexHull_eq]
  exact isClosed_coneC.add_left_of_isCompact (isCompact_convexHull (isCompact_valSet p))

/-! ## The support-function reduction

`ℬ` contains `(0,0,0)` (both channels useless) and is down-closed in `R₀`,
up-closed in `R₁,R₂`, so it contains the whole orthant
`{R₀ ≤ 0, R₁ ≥ 0, R₂ ≥ 0}`.  That pins the sign of any separating functional:
its `R₀`-coefficient must be `> 0` and its `R₁,R₂`-coefficients `≤ 0`, i.e. after
normalisation it is exactly `F = R₀ − μR₁ − νR₂` with `μ, ν ≥ 0`.  Hence the
support inequality for that one family implies `𝒜 ⊆ conv ℬ`. -/


/-! ### From `Bridge.lean` -/


/-! ## The `V`-side bias formula, via transposition -/

theorem mutualInfo_jointYV_eq_bias {cR : Chan}
    (hpos : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hb : ∀ v, -1 < biasOfSnd (jointYV cR) v ∧ biasOfSnd (jointYV cR) v < 1) :
    mutualInfo (jointYV cR)
      = marg₂ (jointYV cR) false * fe (biasOfSnd (jointYV cR) false)
        + marg₂ (jointYV cR) true * fe (biasOfSnd (jointYV cR) true) := by
  have htr : ∀ v, marg₁ (fun v y => jointYV cR y v) v = marg₂ (jointYV cR) v := by
    intro v; simp [marg₁, marg₂]
  have hbtr : ∀ v, biasOf (fun v y => jointYV cR y v) v = biasOfSnd (jointYV cR) v := by
    intro v; simp [biasOf, biasOfSnd, marg₁, marg₂]
  have hmarg2 : ∀ y, marg₂ (fun v y => jointYV cR y v) y = 1 / 2 := by
    intro y
    have := marg₁_jointYV cR y
    simpa [marg₂, marg₁] using this
  have hsum : marg₁ (fun v y => jointYV cR y v) false
      + marg₁ (fun v y => jointYV cR y v) true = 1 := by
    rw [htr false, htr true]; exact marg₂_jointYV_sum cR
  have h := mutualInfo_eq_sum_fe_bias (q := fun v y => jointYV cR y v)
    (fun v => by rw [htr v]; exact hpos v) hsum
    (fun v => by rw [hbtr v]; exact hb v) hmarg2
  rw [htr false, htr true, hbtr false, hbtr true] at h
  rw [← mutualInfo_transpose (jointYV cR)]
  exact h

/-! ## The weights are forced by mean-zero -/

/-- **The Lagrangian of a binary channel pair is `lagrTwoPoint`.**  With
`a = s_false`, `b = −s_true`, `c = t_false`, `d = −t_true`, the mean-zero
relations pin the weights and every term matches. -/
theorem lagrangian_eq_lagrTwoPoint {p μ ν : ℝ} {cL cR : Chan}
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hbL : ∀ u, -1 < biasOf (jointUX cL) u ∧ biasOf (jointUX cL) u < 1)
    (hbR : ∀ v, -1 < biasOfSnd (jointYV cR) v ∧ biasOfSnd (jointYV cR) v < 1)
    (hker : ∀ u v, 0 < 1 + (1 - 2 * p) * biasOf (jointUX cL) u * biasOfSnd (jointYV cR) v)
    (hneL : biasOf (jointUX cL) false - biasOf (jointUX cL) true ≠ 0)
    (hneR : biasOfSnd (jointYV cR) false - biasOfSnd (jointYV cR) true ≠ 0) :
    mutualInfo (jointUV p cL cR) - μ * mutualInfo (jointUX cL) - ν * mutualInfo (jointYV cR)
      = lagrTwoPoint (1 - 2 * p) μ ν
          (biasOf (jointUX cL) false) (-biasOf (jointUX cL) true)
          (biasOfSnd (jointYV cR) false) (-biasOfSnd (jointYV cR) true) := by
  rw [mutualInfo_jointUV_eq_kernel_sum p cL cR hpi hrho hker,
    mutualInfo_jointUX_eq_bias hpi hbL, mutualInfo_jointYV_eq_bias hrho hbR,
    pi_false_eq (hpi false) (hpi true) hneL, pi_true_eq (hpi false) (hpi true) hneL,
    rho_false_eq (hrho false) (hrho true) hneR, rho_true_eq (hrho false) (hrho true) hneR,
    lagrTwoPoint]
  have a1 : (1 - 2 * p) * (biasOf (jointUX cL) false * biasOfSnd (jointYV cR) false)
      = (1 - 2 * p) * biasOf (jointUX cL) false * biasOfSnd (jointYV cR) false := by ring
  have a2 : -((1 - 2 * p) * (biasOf (jointUX cL) false * -biasOfSnd (jointYV cR) true))
      = (1 - 2 * p) * biasOf (jointUX cL) false * biasOfSnd (jointYV cR) true := by ring
  have a3 : -((1 - 2 * p) * (-biasOf (jointUX cL) true * biasOfSnd (jointYV cR) false))
      = (1 - 2 * p) * biasOf (jointUX cL) true * biasOfSnd (jointYV cR) false := by ring
  have a4 : (1 - 2 * p) * (-biasOf (jointUX cL) true * -biasOfSnd (jointYV cR) true)
      = (1 - 2 * p) * biasOf (jointUX cL) true * biasOfSnd (jointYV cR) true := by ring
  have hL' : biasOf (jointUX cL) false + -biasOf (jointUX cL) true ≠ 0 := by
    intro h; exact hneL (by linarith)
  have hR' : biasOfSnd (jointYV cR) false + -biasOfSnd (jointYV cR) true ≠ 0 := by
    intro h; exact hneR (by linarith)
  rw [a1, a2, a3, a4, fe_neg (biasOf (jointUX cL) true),
    fe_neg (biasOfSnd (jointYV cR) true)]
  field_simp
  ring


/-! ### From `Assembly.lean` -/

/-- `negMulLog` of a product splits (valid also at `0`). -/
lemma negMulLog_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog (a * b) = b * Real.negMulLog a + a * Real.negMulLog b := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp [Real.negMulLog]
  rcases eq_or_lt_of_le hb with rfl | hb'
  · simp [Real.negMulLog]
  · simp only [Real.negMulLog]
    rw [Real.log_mul (ne_of_gt ha') (ne_of_gt hb')]
    ring

/-- A product law carries no mutual information. -/
theorem mutualInfo_eq_zero_of_product {q : Bool → Bool → ℝ}
    (hnn : ∀ u v, 0 ≤ q u v)
    (hprod : ∀ u v, q u v = marg₁ q u * marg₂ q v)
    (h1 : marg₁ q false + marg₁ q true = 1) (h2 : marg₂ q false + marg₂ q true = 1) :
    mutualInfo q = 0 := by
  have hm1 : ∀ u, 0 ≤ marg₁ q u := by
    intro u; simp only [marg₁]; exact add_nonneg (hnn u false) (hnn u true)
  have hm2 : ∀ v, 0 ≤ marg₂ q v := by
    intro v; simp only [marg₂]; exact add_nonneg (hnn false v) (hnn true v)
  have hsplit : ∀ u v, Real.negMulLog (q u v)
      = marg₂ q v * Real.negMulLog (marg₁ q u) + marg₁ q u * Real.negMulLog (marg₂ q v) := by
    intro u v; rw [hprod u v]; exact negMulLog_mul (hm1 u) (hm2 v)
  simp only [mutualInfo, entropy1, entropy2]
  rw [hsplit false false, hsplit false true, hsplit true false, hsplit true true]
  linear_combination
    (-(Real.negMulLog (marg₁ q false) + Real.negMulLog (marg₁ q true))) * h2
      + (-(Real.negMulLog (marg₂ q false) + Real.negMulLog (marg₂ q true))) * h1


/-! ## Closed-range versions of the bias formulas -/


/-! ## Axiom checks -/

#print axioms mgl_jensen
#print axioms mutual_le_c0_mul_jeffreys
#print axioms lambda_prod_lt_one
#print axioms mutual_le_lautum_of_opposite_skew
#print axioms convexHull_le_of_le
#print axioms forceFun_pos
#print axioms stationary_imp_bitangent
#print axioms oddPart_deriv_sub_eq

end BSCAveraging.Legacy
