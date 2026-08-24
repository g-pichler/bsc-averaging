import BSCAveraging.Definitions

/-! # Mutual information of binary symmetric channels in series

The computations that make the region `ℬ` explicit:

* `mutualInfo_dsbs`: `I(X; Y) = log 2 - h₂ p` for a DSBS with parameter `p`;
* `jointUX_bsc`, `jointYV_bsc`: the `(U, X)` and `(Y, V)` laws for a BSC are
  themselves DSBS laws, so `I(U; X) = log 2 - h₂ a`;
* `jointUV_bsc`: three BSCs in series (`a`, then `p`, then `b`) form a BSC with
  crossover `a ∗ p ∗ b`, hence `I(U; V) = log 2 - h₂ (a ∗ p ∗ b)`.

Also the degenerate case `p = 1/2`: there `X` and `Y` are independent, so
`I(U; V) = 0` for *every* pair of channels (`mutualInfo_jointUV_half`).

See `BSCAveraging.Basic`. -/

open Real

namespace BSCAveraging

/-! ## An entropy identity for halving -/

/-- Splitting a mass `x` into two halves costs exactly `x · log 2` extra
entropy.  Stated so that it also holds at `x = 0`, where `log 0 = 0`. -/
lemma negMulLog_half_add (x : ℝ) (hx : 0 ≤ x) :
    negMulLog (x / 2) + negMulLog (x / 2) = negMulLog x + x * log 2 := by
  rcases eq_or_lt_of_le hx with h | h
  · simp [← h]
  · have hx0 : x ≠ 0 := ne_of_gt h
    have : Real.log (x / 2) = Real.log x - Real.log 2 := Real.log_div hx0 (by norm_num)
    simp only [negMulLog, this]
    ring

/-! ## The DSBS law: marginals, entropy, mutual information -/

@[simp] lemma marg₁_dsbs (c : ℝ) : marg₁ (dsbs c) = fun _ => (1 : ℝ) / 2 := by
  funext u; cases u <;> simp [marg₁, dsbs] <;> ring

@[simp] lemma marg₂_dsbs (c : ℝ) : marg₂ (dsbs c) = fun _ => (1 : ℝ) / 2 := by
  funext v; cases v <;> simp [marg₂, dsbs] <;> ring

@[simp] lemma entropy1_const_half : entropy1 (fun _ => (1 : ℝ) / 2) = log 2 := by
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  simp only [entropy1, negMulLog, hlog]
  ring

lemma entropy2_dsbs {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    entropy2 (dsbs c) = h2 c + log 2 := by
  have hc' : (0 : ℝ) ≤ 1 - c := by linarith
  have e1 := negMulLog_half_add (1 - c) hc'
  have e2 := negMulLog_half_add c hc0
  simp only [entropy2, dsbs, h2]
  norm_num
  linarith [e1, e2]

/-- Mutual information of a doubly symmetric binary source with parameter `c`
is `log 2 - h₂ c` (in nats; `1 - H(c)` in bits). -/
theorem mutualInfo_dsbs {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    mutualInfo (dsbs c) = log 2 - h2 c := by
  rw [mutualInfo, marg₁_dsbs, marg₂_dsbs, entropy1_const_half, entropy2_dsbs hc0 hc1]
  ring

/-! ## Binary symmetric channels -/

@[simp] lemma jointUX_bsc {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    jointUX (bsc a ha0 ha1) = dsbs a := by
  funext u x; cases u <;> cases x <;> simp [jointUX, bscTr, dsbs]

@[simp] lemma jointYV_bsc {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    jointYV (bsc b hb0 hb1) = dsbs b := by
  funext y v; cases y <;> cases v <;> simp [jointYV, bscTr, dsbs]

/-- Three binary symmetric channels in series — crossovers `a`, `p`, `b` — form
a single binary symmetric channel with crossover `a ∗ p ∗ b`. -/
theorem jointUV_bsc {a b p : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    jointUV p (bsc a ha0 ha1) (bsc b hb0 hb1) = dsbs ((a ⊛ p) ⊛ b) := by
  funext u v
  cases u <;> cases v <;> simp [jointUV, bscTr, dsbs, bconv] <;> ring

/-- `I(U; X) = log 2 - h₂ a` when `X → U` is a BSC with crossover `a`. -/
theorem mutualInfo_jointUX_bsc {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    mutualInfo (jointUX (bsc a ha0 ha1)) = log 2 - h2 a := by
  rw [jointUX_bsc, mutualInfo_dsbs ha0 ha1]

/-- `I(Y; V) = log 2 - h₂ b` when `Y → V` is a BSC with crossover `b`. -/
theorem mutualInfo_jointYV_bsc {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    mutualInfo (jointYV (bsc b hb0 hb1)) = log 2 - h2 b := by
  rw [jointYV_bsc, mutualInfo_dsbs hb0 hb1]

/-- `I(U; V) = log 2 - h₂ (a ∗ p ∗ b)` for the all-symmetric chain. -/
theorem mutualInfo_jointUV_bsc {a b p : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mutualInfo (jointUV p (bsc a ha0 ha1) (bsc b hb0 hb1)) = log 2 - h2 ((a ⊛ p) ⊛ b) := by
  have h1 : 0 ≤ a ⊛ p := bconv_nonneg ha0 ha1 hp0 hp1
  have h2' : a ⊛ p ≤ 1 := bconv_le_one ha0 ha1 hp0 hp1
  rw [jointUV_bsc, mutualInfo_dsbs (bconv_nonneg h1 h2' hb0 hb1) (bconv_le_one h1 h2' hb0 hb1)]

/-! ## Product distributions have zero mutual information -/

/-- A product joint law carries no mutual information. -/
theorem mutualInfo_of_prod {m₁ m₂ : Bool → ℝ} (h₁ : m₁ false + m₁ true = 1)
    (h₂ : m₂ false + m₂ true = 1) : mutualInfo (fun u v => m₁ u * m₂ v) = 0 := by
  have e1 : marg₁ (fun u v => m₁ u * m₂ v) = m₁ := by
    funext u; simp only [marg₁]; rw [← mul_add, h₂, mul_one]
  have e2 : marg₂ (fun u v => m₁ u * m₂ v) = m₂ := by
    funext v; simp only [marg₂]; rw [← add_mul, h₁, one_mul]
  have e3 : entropy2 (fun u v => m₁ u * m₂ v) = entropy1 m₁ + entropy1 m₂ := by
    simp only [entropy2, entropy1, Real.negMulLog_mul]
    linear_combination (negMulLog (m₁ false) + negMulLog (m₁ true)) * h₂
      + (negMulLog (m₂ false) + negMulLog (m₂ true)) * h₁
  rw [mutualInfo, e1, e2, e3]
  ring

/-! ## The degenerate case `p = 1/2`: `X` and `Y` are independent -/

/-- At `p = 1/2` the joint law of `(U, V)` is a product law, for *any* pair of
channels. -/
lemma jointUV_half_eq_prod (cL cR : Chan) :
    jointUV (1 / 2) cL cR
      = fun u v => ((cL.tr false u + cL.tr true u) / 2) * ((cR.tr false v + cR.tr true v) / 2) := by
  funext u v
  simp only [jointUV, dsbs]
  norm_num
  ring

/-- At `p = 1/2` no pair of channels extracts any mutual information:
`I(U; V) = 0`. -/
theorem mutualInfo_jointUV_half (cL cR : Chan) : mutualInfo (jointUV (1 / 2) cL cR) = 0 := by
  rw [jointUV_half_eq_prod]
  refine mutualInfo_of_prod ?_ ?_
  · have := cL.sum_one false
    have := cL.sum_one true
    linarith
  · have := cR.sum_one false
    have := cR.sum_one true
    linarith

end BSCAveraging
