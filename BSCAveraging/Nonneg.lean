import BSCAveraging.BSC

/-! # Nonnegativity of mutual information

`mutualInfo` is defined here as a bare algebraic expression in the four joint
probabilities, so its nonnegativity is a theorem rather than a definitional
fact.  The proof is the usual Gibbs argument via `log x ≤ x - 1`, done term by
term (`log_ratio_term_le`) and summed over the four cells.

Consequences used later: `mutualInfo_jointUX_nonneg` / `mutualInfo_jointYV_nonneg`
(the `R₁`, `R₂` constraints in region `𝒜` are never vacuous) and
`h2_le_log_two` (binary entropy is at most `log 2`).

See `BSCAveraging.Basic`. -/

open Real

namespace BSCAveraging

/-- The single-cell Gibbs estimate.  With `q` the joint probability of a cell
and `a`, `b` its two marginals (so `q ≤ a` and `q ≤ b`),
`q·log(a·b) - q·log q ≤ a·b - q`.  Also valid at `q = 0`, where the convention
`log 0 = 0` makes the left side vanish. -/
lemma log_ratio_term_le {q a b : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hqa : q ≤ a) (hqb : q ≤ b) :
    q * (log a + log b) - q * log q ≤ a * b - q := by
  rcases eq_or_lt_of_le hq with h | h
  · rw [← h]; simpa using mul_nonneg ha hb
  · have ha0 : 0 < a := lt_of_lt_of_le h hqa
    have hb0 : 0 < b := lt_of_lt_of_le h hqb
    have hpos : 0 < a * b / q := div_pos (mul_pos ha0 hb0) h
    have hlog : log (a * b / q) ≤ a * b / q - 1 := Real.log_le_sub_one_of_pos hpos
    have hsplit : log (a * b / q) = log a + log b - log q := by
      rw [Real.log_div (by positivity) (ne_of_gt h),
        Real.log_mul (ne_of_gt ha0) (ne_of_gt hb0)]
    rw [hsplit] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt h)
    have hq' : q * (a * b / q - 1) = a * b - q := by field_simp
    rw [hq'] at hmul
    linarith

/-- Mutual information written out cell by cell, as
`Σ q(u,v) · [log q(u,v) - log P(u) - log P(v)]`.  A pure `ring` identity, since
`marg₁` and `marg₂` are sums of the cells. -/
lemma mutualInfo_eq_sum (q : Bool → Bool → ℝ) :
    mutualInfo q =
      (q false false * log (q false false)
        - q false false * (log (marg₁ q false) + log (marg₂ q false)))
      + (q false true * log (q false true)
        - q false true * (log (marg₁ q false) + log (marg₂ q true)))
      + (q true false * log (q true false)
        - q true false * (log (marg₁ q true) + log (marg₂ q false)))
      + (q true true * log (q true true)
        - q true true * (log (marg₁ q true) + log (marg₂ q true))) := by
  simp only [mutualInfo, entropy1, entropy2, negMulLog, marg₁, marg₂]
  ring

/-- Mutual information of a joint distribution on `Bool × Bool` is nonnegative. -/
theorem mutualInfo_nonneg {q : Bool → Bool → ℝ} (hq : ∀ u v, 0 ≤ q u v)
    (hsum : q false false + q false true + q true false + q true true = 1) :
    0 ≤ mutualInfo q := by
  have hm1F : marg₁ q false = q false false + q false true := rfl
  have hm1T : marg₁ q true = q true false + q true true := rfl
  have hm2F : marg₂ q false = q false false + q true false := rfl
  have hm2T : marg₂ q true = q false true + q true true := rfl
  -- the four cell estimates
  have h0FF := hq false false
  have h0FT := hq false true
  have h0TF := hq true false
  have h0TT := hq true true
  have hm1F0 : 0 ≤ marg₁ q false := by rw [hm1F]; linarith
  have hm1T0 : 0 ≤ marg₁ q true := by rw [hm1T]; linarith
  have hm2F0 : 0 ≤ marg₂ q false := by rw [hm2F]; linarith
  have hm2T0 : 0 ≤ marg₂ q true := by rw [hm2T]; linarith
  have tFF := log_ratio_term_le (q := q false false) (a := marg₁ q false) (b := marg₂ q false)
    h0FF hm1F0 hm2F0 (by rw [hm1F]; linarith) (by rw [hm2F]; linarith)
  have tFT := log_ratio_term_le (q := q false true) (a := marg₁ q false) (b := marg₂ q true)
    h0FT hm1F0 hm2T0 (by rw [hm1F]; linarith) (by rw [hm2T]; linarith)
  have tTF := log_ratio_term_le (q := q true false) (a := marg₁ q true) (b := marg₂ q false)
    h0TF hm1T0 hm2F0 (by rw [hm1T]; linarith) (by rw [hm2F]; linarith)
  have tTT := log_ratio_term_le (q := q true true) (a := marg₁ q true) (b := marg₂ q true)
    h0TT hm1T0 hm2T0 (by rw [hm1T]; linarith) (by rw [hm2T]; linarith)
  -- the marginals sum to one, so the four products `marg₁ u * marg₂ v` sum to one
  have hs1 : marg₁ q false + marg₁ q true = 1 := by rw [hm1F, hm1T]; linarith
  have hs2 : marg₂ q false + marg₂ q true = 1 := by rw [hm2F, hm2T]; linarith
  have hprod : marg₁ q false * marg₂ q false + marg₁ q false * marg₂ q true
      + marg₁ q true * marg₂ q false + marg₁ q true * marg₂ q true = 1 := by
    linear_combination (marg₂ q false + marg₂ q true) * hs1 + hs2
  rw [mutualInfo_eq_sum q]
  linarith [tFF, tFT, tTF, tTT, hprod, hsum]

/-! ## Marginals dominate cells, and `I ≤ log 2` -/

lemma le_marg₁ {q : Bool → Bool → ℝ} (hq : ∀ u x, 0 ≤ q u x) (u x : Bool) :
    q u x ≤ marg₁ q u := by
  cases x <;> (simp only [marg₁]; linarith [hq u false, hq u true])

lemma le_marg₂ {q : Bool → Bool → ℝ} (hq : ∀ u x, 0 ≤ q u x) (u x : Bool) :
    q u x ≤ marg₂ q x := by
  cases u <;> (simp only [marg₂]; linarith [hq false x, hq true x])

lemma dsbs_nonneg {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x y : Bool) : 0 ≤ dsbs c x y := by
  unfold dsbs; split <;> linarith

lemma dsbs_sum {c : ℝ} : dsbs c false false + dsbs c false true
    + dsbs c true false + dsbs c true true = 1 := by
  simp [dsbs]; ring

/-- Binary entropy is at most `log 2` (in nats). -/
theorem h2_le_log_two {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : h2 c ≤ log 2 := by
  have := mutualInfo_nonneg (dsbs_nonneg hc0 hc1) dsbs_sum
  rw [mutualInfo_dsbs hc0 hc1] at this
  linarith

lemma jointUX_nonneg (cL : Chan) (u x : Bool) : 0 ≤ jointUX cL u x := by
  have := cL.nonneg x u; unfold jointUX; linarith

lemma jointUX_sum (cL : Chan) : jointUX cL false false + jointUX cL false true
    + jointUX cL true false + jointUX cL true true = 1 := by
  have h1 := cL.sum_one false
  have h2 := cL.sum_one true
  unfold jointUX; linarith

lemma jointYV_nonneg (cR : Chan) (y v : Bool) : 0 ≤ jointYV cR y v := by
  have := cR.nonneg y v; unfold jointYV; linarith

lemma jointYV_sum (cR : Chan) : jointYV cR false false + jointYV cR false true
    + jointYV cR true false + jointYV cR true true = 1 := by
  have h1 := cR.sum_one false
  have h2 := cR.sum_one true
  unfold jointYV; linarith

/-- `I(U; X) ≥ 0`. -/
theorem mutualInfo_jointUX_nonneg (cL : Chan) : 0 ≤ mutualInfo (jointUX cL) :=
  mutualInfo_nonneg (jointUX_nonneg cL) (jointUX_sum cL)

/-- `I(Y; V) ≥ 0`. -/
theorem mutualInfo_jointYV_nonneg (cR : Chan) : 0 ≤ mutualInfo (jointYV cR) :=
  mutualInfo_nonneg (jointYV_nonneg cR) (jointYV_sum cR)

/-! ## `I ≤ log 2` -/

end BSCAveraging
