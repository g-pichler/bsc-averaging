import BSCAveraging.Nonneg

/-! # The data processing inequality

Pushing the second coordinate of a joint law on `Bool × Bool` through a channel
cannot increase mutual information (`mutualInfo_compose_le`).  Everything is
elementary and explicit: the two-term log-sum inequality (`log_sum_two`), itself
a double application of the Gibbs estimate `q·log r - q·log q ≤ r - q`
(`gibbs_term`), applied once per cell of the output law.

See `BSCAveraging.Basic`. -/

open Real

namespace BSCAveraging

/-! ## Analytic core -/

/-- The Gibbs estimate `q·log r - q·log q ≤ r - q`, valid at `q = 0` too. -/
lemma gibbs_term {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) (h : q ≠ 0 → r ≠ 0) :
    q * log r - q * log q ≤ r - q := by
  rcases eq_or_lt_of_le hq with hq0 | hq0
  · rw [← hq0]; simpa using hr
  · have hr0 : 0 < r := lt_of_le_of_ne hr (Ne.symm (h (ne_of_gt hq0)))
    have hlog : log (r / q) ≤ r / q - 1 := Real.log_le_sub_one_of_pos (div_pos hr0 hq0)
    rw [Real.log_div (ne_of_gt hr0) (ne_of_gt hq0)] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hq0)
    have hq' : q * (r / q - 1) = r - q := by field_simp
    rw [hq'] at hmul
    linarith

/-- Splitting a log of a product, guarded by domination: if `c ≠ 0` forces both
factors to be nonzero, then `c·log(x·y) = c·(log x + log y)`. -/
lemma mul_log_mul₂ {c x y : ℝ} (h : c ≠ 0 → x ≠ 0 ∧ y ≠ 0) :
    c * log (x * y) = c * (log x + log y) := by
  rcases eq_or_ne c 0 with h0 | h0
  · simp [h0]
  · obtain ⟨hx, hy⟩ := h h0
    rw [Real.log_mul hx hy]

/-- Three-factor version of `mul_log_mul₂`. -/
lemma mul_log_mul₃ {c x y z : ℝ} (h : c ≠ 0 → x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0) :
    c * log (x * y * z) = c * (log x + log y + log z) := by
  rcases eq_or_ne c 0 with h0 | h0
  · simp [h0]
  · obtain ⟨hx, hy, hz⟩ := h h0
    rw [Real.log_mul (mul_ne_zero hx hy) hz, Real.log_mul hx hy]

/-- The two-term log-sum inequality:
`(a₁+a₂)·log((a₁+a₂)/(b₁+b₂)) ≤ Σ aᵢ·log(aᵢ/bᵢ)`, written without division. -/
lemma log_sum_two {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (h₁ : a₁ ≠ 0 → b₁ ≠ 0) (h₂ : a₂ ≠ 0 → b₂ ≠ 0) :
    (a₁ + a₂) * log (a₁ + a₂) - (a₁ + a₂) * log (b₁ + b₂)
      ≤ (a₁ * log a₁ - a₁ * log b₁) + (a₂ * log a₂ - a₂ * log b₂) := by
  rcases eq_or_lt_of_le ha₁ with h1 | h1
  · -- `a₁ = 0`: reduces to monotonicity of `log`
    rcases eq_or_lt_of_le ha₂ with h2 | h2
    · rw [← h1, ← h2]; norm_num
    · have hb₂0 : 0 < b₂ := lt_of_le_of_ne hb₂ (Ne.symm (h₂ (ne_of_gt h2)))
      have hmono : log b₂ ≤ log (b₁ + b₂) :=
        Real.log_le_log hb₂0 (by linarith)
      have := mul_le_mul_of_nonneg_left hmono (le_of_lt h2)
      rw [← h1]
      simp only [zero_add, zero_mul, sub_zero, Real.log_zero, mul_zero]
      linarith
  rcases eq_or_lt_of_le ha₂ with h2 | h2
  · have hb₁0 : 0 < b₁ := lt_of_le_of_ne hb₁ (Ne.symm (h₁ (ne_of_gt h1)))
    have hmono : log b₁ ≤ log (b₁ + b₂) :=
      Real.log_le_log hb₁0 (by linarith)
    have := mul_le_mul_of_nonneg_left hmono (le_of_lt h1)
    rw [← h2]
    simp only [add_zero, zero_mul, sub_zero, Real.log_zero, mul_zero]
    linarith
  -- the generic case: everything strictly positive
  have hb₁0 : 0 < b₁ := lt_of_le_of_ne hb₁ (Ne.symm (h₁ (ne_of_gt h1)))
  have hb₂0 : 0 < b₂ := lt_of_le_of_ne hb₂ (Ne.symm (h₂ (ne_of_gt h2)))
  have hA : 0 < a₁ + a₂ := by linarith
  have hB : 0 < b₁ + b₂ := by linarith
  have k₁ := gibbs_term (q := a₁) (r := b₁ * (a₁ + a₂) / (b₁ + b₂)) (le_of_lt h1)
    (le_of_lt (div_pos (mul_pos hb₁0 hA) hB)) (fun _ => ne_of_gt (div_pos (mul_pos hb₁0 hA) hB))
  have k₂ := gibbs_term (q := a₂) (r := b₂ * (a₁ + a₂) / (b₁ + b₂)) (le_of_lt h2)
    (le_of_lt (div_pos (mul_pos hb₂0 hA) hB)) (fun _ => ne_of_gt (div_pos (mul_pos hb₂0 hA) hB))
  have l₁ : log (b₁ * (a₁ + a₂) / (b₁ + b₂)) = log b₁ + log (a₁ + a₂) - log (b₁ + b₂) := by
    rw [Real.log_div (ne_of_gt (mul_pos hb₁0 hA)) (ne_of_gt hB),
      Real.log_mul (ne_of_gt hb₁0) (ne_of_gt hA)]
  have l₂ : log (b₂ * (a₁ + a₂) / (b₁ + b₂)) = log b₂ + log (a₁ + a₂) - log (b₁ + b₂) := by
    rw [Real.log_div (ne_of_gt (mul_pos hb₂0 hA)) (ne_of_gt hB),
      Real.log_mul (ne_of_gt hb₂0) (ne_of_gt hA)]
  rw [l₁] at k₁
  rw [l₂] at k₂
  have hsplit : b₁ * (a₁ + a₂) / (b₁ + b₂) + b₂ * (a₁ + a₂) / (b₁ + b₂) = a₁ + a₂ := by
    field_simp
  nlinarith [k₁, k₂, hsplit]

/-! ## Composition of a joint law with a channel -/

/-- Push the second coordinate of `q` through the channel `W`. -/
noncomputable def compose (q W : Bool → Bool → ℝ) (u v : Bool) : ℝ :=
  q u false * W false v + q u true * W true v

lemma compose_nonneg {q W : Bool → Bool → ℝ} (hq : ∀ u x, 0 ≤ q u x) (hW : ∀ x v, 0 ≤ W x v)
    (u v : Bool) : 0 ≤ compose q W u v :=
  add_nonneg (mul_nonneg (hq u false) (hW false v)) (mul_nonneg (hq u true) (hW true v))

lemma marg₁_compose {q W : Bool → Bool → ℝ} (hWs : ∀ x, W x false + W x true = 1) :
    marg₁ (compose q W) = marg₁ q := by
  funext u
  simp only [marg₁, compose]
  linear_combination (q u false) * hWs false + (q u true) * hWs true

lemma marg₂_compose (q W : Bool → Bool → ℝ) (v : Bool) :
    marg₂ (compose q W) v = marg₂ q false * W false v + marg₂ q true * W true v := by
  simp only [marg₂, compose]; ring

/-- One cell of the data processing inequality. -/
lemma compose_cell_le {q W : Bool → Bool → ℝ} (hq : ∀ u x, 0 ≤ q u x) (hW : ∀ x v, 0 ≤ W x v)
    (u v : Bool) :
    compose q W u v * log (compose q W u v)
        - compose q W u v * (log (marg₁ q u) + log (marg₂ (compose q W) v))
      ≤ (q u false * W false v) * (log (q u false) - (log (marg₁ q u) + log (marg₂ q false)))
        + (q u true * W true v) * (log (q u true) - (log (marg₁ q u) + log (marg₂ q true))) := by
  set a₁ := q u false * W false v with ha₁def
  set a₂ := q u true * W true v with ha₂def
  set b₁ := marg₁ q u * marg₂ q false * W false v with hb₁def
  set b₂ := marg₁ q u * marg₂ q true * W true v with hb₂def
  have ha₁ : 0 ≤ a₁ := mul_nonneg (hq u false) (hW false v)
  have ha₂ : 0 ≤ a₂ := mul_nonneg (hq u true) (hW true v)
  have hm1 : 0 ≤ marg₁ q u := le_trans (hq u false) (le_marg₁ hq u false)
  have hm2F : 0 ≤ marg₂ q false := le_trans (hq u false) (le_marg₂ hq u false)
  have hm2T : 0 ≤ marg₂ q true := le_trans (hq u true) (le_marg₂ hq u true)
  have hb₁ : 0 ≤ b₁ := mul_nonneg (mul_nonneg hm1 hm2F) (hW false v)
  have hb₂ : 0 ≤ b₂ := mul_nonneg (mul_nonneg hm1 hm2T) (hW true v)
  -- domination: a nonzero cell forces all three factors of the reference to be nonzero
  have dom₁ : a₁ ≠ 0 → q u false ≠ 0 ∧ marg₁ q u ≠ 0 ∧ marg₂ q false ≠ 0 ∧ W false v ≠ 0 := by
    intro h
    have h1 : q u false ≠ 0 := fun hz => h (by rw [ha₁def, hz]; ring)
    have h2 : W false v ≠ 0 := fun hz => h (by rw [ha₁def, hz]; ring)
    have hp : 0 < q u false := lt_of_le_of_ne (hq u false) (Ne.symm h1)
    exact ⟨h1, ne_of_gt (lt_of_lt_of_le hp (le_marg₁ hq u false)),
      ne_of_gt (lt_of_lt_of_le hp (le_marg₂ hq u false)), h2⟩
  have dom₂ : a₂ ≠ 0 → q u true ≠ 0 ∧ marg₁ q u ≠ 0 ∧ marg₂ q true ≠ 0 ∧ W true v ≠ 0 := by
    intro h
    have h1 : q u true ≠ 0 := fun hz => h (by rw [ha₂def, hz]; ring)
    have h2 : W true v ≠ 0 := fun hz => h (by rw [ha₂def, hz]; ring)
    have hp : 0 < q u true := lt_of_le_of_ne (hq u true) (Ne.symm h1)
    exact ⟨h1, ne_of_gt (lt_of_lt_of_le hp (le_marg₁ hq u true)),
      ne_of_gt (lt_of_lt_of_le hp (le_marg₂ hq u true)), h2⟩
  have hb₁ne : a₁ ≠ 0 → b₁ ≠ 0 := by
    intro h
    obtain ⟨_, h2, h3, h4⟩ := dom₁ h
    exact mul_ne_zero (mul_ne_zero h2 h3) h4
  have hb₂ne : a₂ ≠ 0 → b₂ ≠ 0 := by
    intro h
    obtain ⟨_, h2, h3, h4⟩ := dom₂ h
    exact mul_ne_zero (mul_ne_zero h2 h3) h4
  have key := log_sum_two ha₁ ha₂ hb₁ hb₂ hb₁ne hb₂ne
  -- identify the two sums
  have hsum_a : a₁ + a₂ = compose q W u v := rfl
  have hsum_b : b₁ + b₂ = marg₁ q u * marg₂ (compose q W) v := by
    rw [marg₂_compose, hb₁def, hb₂def]; ring
  -- split the logarithms
  have hlogb : compose q W u v * log (b₁ + b₂)
      = compose q W u v * (log (marg₁ q u) + log (marg₂ (compose q W) v)) := by
    rw [hsum_b]
    refine mul_log_mul₂ (fun hne => ⟨?_, ?_⟩)
    · rcases eq_or_ne a₁ 0 with h | h
      · refine (dom₂ ?_).2.1
        intro hz
        exact hne (by rw [← hsum_a, h, hz]; ring)
      · exact (dom₁ h).2.1
    · intro hz
      apply hne
      have h1 : compose q W u v ≤ marg₂ (compose q W) v :=
        le_marg₂ (fun u' v' => compose_nonneg hq hW u' v') u v
      have h0 : 0 ≤ compose q W u v := compose_nonneg hq hW u v
      rw [hz] at h1
      linarith
  have hloga₁ : a₁ * log a₁ = a₁ * (log (q u false) + log (W false v)) :=
    mul_log_mul₂ (fun h => ⟨(dom₁ h).1, (dom₁ h).2.2.2⟩)
  have hloga₂ : a₂ * log a₂ = a₂ * (log (q u true) + log (W true v)) :=
    mul_log_mul₂ (fun h => ⟨(dom₂ h).1, (dom₂ h).2.2.2⟩)
  have hlogb₁ : a₁ * log b₁
      = a₁ * (log (marg₁ q u) + log (marg₂ q false) + log (W false v)) :=
    mul_log_mul₃ (fun h => ⟨(dom₁ h).2.1, (dom₁ h).2.2.1, (dom₁ h).2.2.2⟩)
  have hlogb₂ : a₂ * log b₂
      = a₂ * (log (marg₁ q u) + log (marg₂ q true) + log (W true v)) :=
    mul_log_mul₃ (fun h => ⟨(dom₂ h).2.1, (dom₂ h).2.2.1, (dom₂ h).2.2.2⟩)
  rw [hsum_a, hlogb, hloga₁, hloga₂, hlogb₁, hlogb₂] at key
  linarith [key]

/-- **Data processing**: pushing the second coordinate through a channel cannot
increase mutual information. -/
theorem mutualInfo_compose_le {q W : Bool → Bool → ℝ} (hq : ∀ u x, 0 ≤ q u x)
    (hW : ∀ x v, 0 ≤ W x v) (hWs : ∀ x, W x false + W x true = 1) :
    mutualInfo (compose q W) ≤ mutualInfo q := by
  have cFF := compose_cell_le hq hW false false
  have cFT := compose_cell_le hq hW false true
  have cTF := compose_cell_le hq hW true false
  have cTT := compose_cell_le hq hW true true
  have hlhs : mutualInfo (compose q W) =
      (compose q W false false * log (compose q W false false)
          - compose q W false false * (log (marg₁ q false) + log (marg₂ (compose q W) false)))
        + (compose q W false true * log (compose q W false true)
          - compose q W false true * (log (marg₁ q false) + log (marg₂ (compose q W) true)))
        + (compose q W true false * log (compose q W true false)
          - compose q W true false * (log (marg₁ q true) + log (marg₂ (compose q W) false)))
        + (compose q W true true * log (compose q W true true)
          - compose q W true true * (log (marg₁ q true) + log (marg₂ (compose q W) true))) := by
    rw [mutualInfo_eq_sum (compose q W), marg₁_compose hWs]
  have hrhs :
      ((q false false * W false false) * (log (q false false)
            - (log (marg₁ q false) + log (marg₂ q false)))
          + (q false true * W true false) * (log (q false true)
            - (log (marg₁ q false) + log (marg₂ q true))))
        + ((q false false * W false true) * (log (q false false)
            - (log (marg₁ q false) + log (marg₂ q false)))
          + (q false true * W true true) * (log (q false true)
            - (log (marg₁ q false) + log (marg₂ q true))))
        + ((q true false * W false false) * (log (q true false)
            - (log (marg₁ q true) + log (marg₂ q false)))
          + (q true true * W true false) * (log (q true true)
            - (log (marg₁ q true) + log (marg₂ q true))))
        + ((q true false * W false true) * (log (q true false)
            - (log (marg₁ q true) + log (marg₂ q false)))
          + (q true true * W true true) * (log (q true true)
            - (log (marg₁ q true) + log (marg₂ q true))))
      = mutualInfo q := by
    rw [mutualInfo_eq_sum q]
    linear_combination
      (q false false * (log (q false false) - (log (marg₁ q false) + log (marg₂ q false)))
        + q true false * (log (q true false) - (log (marg₁ q true) + log (marg₂ q false))))
          * hWs false
      + (q false true * (log (q false true) - (log (marg₁ q false) + log (marg₂ q true)))
        + q true true * (log (q true true) - (log (marg₁ q true) + log (marg₂ q true))))
          * hWs true
  rw [hlhs, ← hrhs]
  linarith [cFF, cFT, cTF, cTT]

/-! ## Transposition -/

/-- Mutual information is symmetric in its two arguments. -/
lemma mutualInfo_transpose (q : Bool → Bool → ℝ) :
    mutualInfo (fun u v => q v u) = mutualInfo q := by
  simp only [mutualInfo, entropy1, entropy2, negMulLog, marg₁, marg₂]
  ring

/-! ## The chain `U — X — Y — V` as two compositions -/

lemma bscTr_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x v : Bool) : 0 ≤ bscTr p x v := by
  unfold bscTr; split <;> linarith

lemma bscTr_sum (p : ℝ) (x : Bool) : bscTr p x false + bscTr p x true = 1 := by
  cases x <;> simp [bscTr]

/-- `(U, V)` is `(U, X)` pushed through the source channel and then through
`cR`. -/
lemma jointUV_eq_compose (p : ℝ) (cL cR : Chan) :
    jointUV p cL cR = compose (compose (jointUX cL) (bscTr p)) cR.tr := by
  funext u v
  cases u <;> cases v <;> simp [jointUV, compose, jointUX, bscTr, dsbs] <;> ring

/-- The mirror image: `(V, U)` is `(V, Y)` pushed through the source channel and
then through `cL`. -/
lemma jointUV_transpose_eq_compose (p : ℝ) (cL cR : Chan) :
    (fun v u => jointUV p cL cR u v)
      = compose (compose (fun v y => jointYV cR y v) (bscTr p)) cL.tr := by
  funext v u
  cases u <;> cases v <;> simp [jointUV, compose, jointYV, bscTr, dsbs] <;> ring

/-- **Data processing along the chain**: `I(U;V) ≤ I(U;X)`. -/
theorem mutualInfo_jointUV_le_jointUX {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (cL cR : Chan) :
    mutualInfo (jointUV p cL cR) ≤ mutualInfo (jointUX cL) := by
  rw [jointUV_eq_compose]
  have h1 : ∀ u x, 0 ≤ jointUX cL u x := jointUX_nonneg cL
  have hmid : ∀ u y, 0 ≤ compose (jointUX cL) (bscTr p) u y :=
    fun u y => compose_nonneg h1 (bscTr_nonneg hp0 hp1) u y
  exact le_trans
    (mutualInfo_compose_le hmid (fun y v => cR.nonneg y v) (fun y => cR.sum_one y))
    (mutualInfo_compose_le h1 (bscTr_nonneg hp0 hp1) (bscTr_sum p))

/-- **Data processing along the chain**: `I(U;V) ≤ I(Y;V)`. -/
theorem mutualInfo_jointUV_le_jointYV {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (cL cR : Chan) :
    mutualInfo (jointUV p cL cR) ≤ mutualInfo (jointYV cR) := by
  have hT : ∀ v y, 0 ≤ jointYV cR y v := fun v y => jointYV_nonneg cR y v
  have hmid : ∀ v x, 0 ≤ compose (fun v y => jointYV cR y v) (bscTr p) v x :=
    fun v x => compose_nonneg hT (bscTr_nonneg hp0 hp1) v x
  calc mutualInfo (jointUV p cL cR)
      = mutualInfo (compose (compose (fun v y => jointYV cR y v) (bscTr p)) cL.tr) := by
        rw [← mutualInfo_transpose (jointUV p cL cR), jointUV_transpose_eq_compose]
    _ ≤ mutualInfo (compose (fun v y => jointYV cR y v) (bscTr p)) :=
        mutualInfo_compose_le hmid (fun x u => cL.nonneg x u) (fun x => cL.sum_one x)
    _ ≤ mutualInfo (fun v y => jointYV cR y v) :=
        mutualInfo_compose_le hT (bscTr_nonneg hp0 hp1) (bscTr_sum p)
    _ = mutualInfo (jointYV cR) := mutualInfo_transpose (jointYV cR)

/-! ## Mirroring a channel: the `S ↦ -S` symmetry

Relabelling the *input* of `cL` (`x ↦ ¬x`) leaves `I(U;X)` unchanged — the input
is uniform — but replaces the source parameter `p` by `1 - p`.  In the bias
coordinates of `NOTES.md` this is exactly the sign flip `S ↦ -S`, the engine of
the symmetrization analysis: the symmetrized configuration has
`I(U;V) = ½[I_p(U;V) + I_{1-p}(U;V)]`, the even part. -/

/-- Relabel the input of a channel. -/
noncomputable def mirror (c : Chan) : Chan where
  tr x u := c.tr (!x) u
  nonneg _ _ := c.nonneg _ _
  sum_one _ := c.sum_one _

@[simp] lemma mirror_tr (c : Chan) (x u : Bool) : (mirror c).tr x u = c.tr (!x) u := rfl

/-- Flipping the label of the second coordinate does not change mutual
information. -/
lemma mutualInfo_flip₂ (q : Bool → Bool → ℝ) :
    mutualInfo (fun u x => q u (!x)) = mutualInfo q := by
  simp only [mutualInfo, entropy1, entropy2, negMulLog, marg₁, marg₂,
    Bool.not_false, Bool.not_true]
  ring_nf

@[simp] lemma mutualInfo_jointUX_mirror (cL : Chan) :
    mutualInfo (jointUX (mirror cL)) = mutualInfo (jointUX cL) := by
  have : jointUX (mirror cL) = fun u x => jointUX cL u (!x) := by
    funext u x; cases x <;> simp [jointUX]
  rw [this, mutualInfo_flip₂]

/-- Mirroring the left channel is the same as flipping the source parameter. -/
lemma jointUV_mirror (p : ℝ) (cL cR : Chan) :
    jointUV p (mirror cL) cR = jointUV (1 - p) cL cR := by
  funext u v
  cases u <;> cases v <;> simp [jointUV, dsbs] <;> ring

@[simp] lemma mutualInfo_jointUV_mirror (p : ℝ) (cL cR : Chan) :
    mutualInfo (jointUV p (mirror cL) cR) = mutualInfo (jointUV (1 - p) cL cR) := by
  rw [jointUV_mirror]

/-- `(Y, U)` is the source law pushed through `cL`. -/
lemma jointUY_transpose_eq_compose (p : ℝ) (cL : Chan) :
    (fun y u => compose (jointUX cL) (bscTr p) u y) = compose (dsbs p) cL.tr := by
  funext y u
  cases y <;> cases u <;> simp [compose, jointUX, bscTr, dsbs] <;> ring

/-- **The cut-set bound**: no pair of channels extracts more than the source
itself carries, `I(U;V) ≤ I(X;Y) = log 2 - h₂ p`. -/
theorem mutualInfo_jointUV_le_source {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (cL cR : Chan) :
    mutualInfo (jointUV p cL cR) ≤ log 2 - h2 p := by
  have h1 : ∀ u x, 0 ≤ jointUX cL u x := jointUX_nonneg cL
  have hmid : ∀ u y, 0 ≤ compose (jointUX cL) (bscTr p) u y :=
    fun u y => compose_nonneg h1 (bscTr_nonneg hp0 hp1) u y
  rw [jointUV_eq_compose]
  calc mutualInfo (compose (compose (jointUX cL) (bscTr p)) cR.tr)
      ≤ mutualInfo (compose (jointUX cL) (bscTr p)) :=
        mutualInfo_compose_le hmid (fun y v => cR.nonneg y v) (fun y => cR.sum_one y)
    _ = mutualInfo (fun y u => compose (jointUX cL) (bscTr p) u y) :=
        mutualInfo_transpose (fun y u => compose (jointUX cL) (bscTr p) u y)
    _ = mutualInfo (compose (dsbs p) cL.tr) := by rw [jointUY_transpose_eq_compose]
    _ ≤ mutualInfo (dsbs p) :=
        mutualInfo_compose_le (fun x y => dsbs_nonneg hp0 hp1 x y)
          (fun x u => cL.nonneg x u) (fun x => cL.sum_one x)
    _ = log 2 - h2 p := mutualInfo_dsbs hp0 hp1

end BSCAveraging
