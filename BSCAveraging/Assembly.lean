import BSCAveraging.Bridge
import BSCAveraging.Closedness
import BSCAveraging.BSC

/-! # Assembling the conjecture from the two-point theorem

Two ingredients are proved elsewhere:

* `regionA_subset_convexHull_regionB` — the support-function reduction;
* `lagrTwoPoint_le_of_corner_bounds_closed` — the two-point theorem on the
  closed box (`FixedPoint.lean`).

The identification of the Lagrangian with `lagrTwoPoint` is completed here, on
the closed box and so with degenerate rows allowed: `mutualInfo_jointUX_eq_bias_closed`
and its `V`-side analogue rewrite each mutual information in bias coordinates,
and `lagrangian_eq_lagrTwoPoint_closed` puts the two together, using the weight
identities of `Bridge.lean`.

The rest is the dictionary between **biases** (used by `lagrTwoPoint`) and
**crossovers** (used by `regionB`),

```
f_e(1 − 2α) = log 2 − h₂ α,        1 − 2(α ⊛ β) = (1−2α)(1−2β)
```

the sign normalisation that puts the two-point data in `[0,1]`, and the reflection
`p ↦ 1 − p` that carries the result past `p = 1/2` (`averagedBSCConjecture_one_sub`,
`averagedBSCConjecture_all`).

See `BSCAveraging.Basic`. -/

open Real

namespace BSCAveraging

/-! ## Biases versus crossovers -/

/-- Binary convolution multiplies biases. -/
theorem one_sub_two_mul_bconv (x y : ℝ) : 1 - 2 * (x ⊛ y) = (1 - 2 * x) * (1 - 2 * y) := by
  unfold bconv; ring

/-- `f_e` of a bias is `log 2` minus the binary entropy of the crossover. -/
theorem fe_one_sub_two_mul {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    fe (1 - 2 * α) = log 2 - h2 α := by
  rcases eq_or_lt_of_le h0 with h | hα0
  · rw [← h]
    norm_num [fe, h2]
  rcases eq_or_lt_of_le h1 with h | hα1
  · rw [h]
    norm_num [fe, h2]
  · have e1 : 1 + (1 - 2 * α) = 2 * (1 - α) := by ring
    have e2 : 1 - (1 - 2 * α) = 2 * α := by ring
    rw [fe, e1, e2, Real.log_mul (by norm_num) (by linarith),
      Real.log_mul (by norm_num) (by linarith), h2, Real.negMulLog, Real.negMulLog]
    ring

/-- The bias of the composed channel is the product of the biases. -/
theorem fe_bconv_bconv {α β p : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    fe ((1 - 2 * α) * (1 - 2 * p) * (1 - 2 * β)) = log 2 - h2 ((α ⊛ p) ⊛ β) := by
  have h1 : 0 ≤ α ⊛ p := bconv_nonneg hα0 hα1 hp0 hp1
  have h2' : α ⊛ p ≤ 1 := bconv_le_one hα0 hα1 hp0 hp1
  have hab0 : 0 ≤ (α ⊛ p) ⊛ β := bconv_nonneg h1 h2' hβ0 hβ1
  have hab1 : (α ⊛ p) ⊛ β ≤ 1 := bconv_le_one h1 h2' hβ0 hβ1
  rw [← fe_one_sub_two_mul hab0 hab1, one_sub_two_mul_bconv, one_sub_two_mul_bconv]

/-! ## Every symmetric value is realised in `ℬ` -/

/-- For biases `P, Q ∈ [0,1]` the BSC pair with crossovers `(1−P)/2`, `(1−Q)/2`
lies in `ℬ` and realises `gSym` as its Lagrangian value. -/
theorem exists_regionB_point {p μ ν P Q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) :
    ∃ S ∈ regionB p, gSym (1 - 2 * p) μ ν P Q = S.1 - μ * S.2.1 - ν * S.2.2 := by
  set α := (1 - P) / 2 with hα
  set β := (1 - Q) / 2 with hβ
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  have hα1 : α ≤ 1 := by rw [hα]; linarith
  have hβ0 : 0 ≤ β := by rw [hβ]; linarith
  have hβ1 : β ≤ 1 := by rw [hβ]; linarith
  have hPα : 1 - 2 * α = P := by rw [hα]; ring
  have hQβ : 1 - 2 * β = Q := by rw [hβ]; ring
  refine ⟨(log 2 - h2 ((α ⊛ p) ⊛ β), log 2 - h2 α, log 2 - h2 β),
    ⟨α, β, hα0, hα1, hβ0, hβ1, le_refl _, le_refl _, le_refl _⟩, ?_⟩
  have hprod : (1 - 2 * p) * (P * Q) = (1 - 2 * α) * (1 - 2 * p) * (1 - 2 * β) := by
    rw [hPα, hQβ]; ring
  rw [gSym, hprod, fe_bconv_bconv hα0 hα1 hβ0 hβ1 hp0 hp1, ← hPα, ← hQβ,
    fe_one_sub_two_mul hα0 hα1, fe_one_sub_two_mul hβ0 hβ1]

/-! ## Sign normalisation

Relabelling `U` maps the two-point data `(a,b)` to `(−b,−a)` and leaves the
Lagrangian unchanged.  Since mean-zero forces `s_false` and `s_true` to have
opposite signs, one of the two labellings has both entries `≥ 0`. -/

set_option maxHeartbeats 1000000 in
theorem lagrTwoPoint_neg_swap (δ μ ν a b c d : ℝ) :
    lagrTwoPoint δ μ ν (-b) (-a) c d = lagrTwoPoint δ μ ν a b c d := by
  have e1 : δ * (-b * c) = -(δ * (b * c)) := by ring
  have e2 : -(δ * (-b * d)) = δ * (b * d) := by ring
  have e3 : -(δ * (-a * c)) = δ * (a * c) := by ring
  have e4 : δ * (-a * d) = -(δ * (a * d)) := by ring
  rw [lagrTwoPoint, lagrTwoPoint, e1, e2, e3, e4, fe_neg a, fe_neg b]
  rcases eq_or_ne (a + b) 0 with h | h
  · have h' : -b + -a = 0 := by linarith
    rw [h, h']; simp
  · have h' : -b + -a ≠ 0 := by intro hc; exact h (by linarith)
    field_simp
    ring

/-- The two bias entries have opposite signs: either `(s, −t)` are both `≥ 0`, or
`(t, −s)` are. -/
lemma bias_sign_cases {s t πf πt : ℝ} (hf : 0 < πf) (ht : 0 < πt)
    (hz : πf * s + πt * t = 0) : (0 ≤ s ∧ 0 ≤ -t) ∨ (0 ≤ t ∧ 0 ≤ -s) := by
  rcases le_or_gt 0 s with hs | hs
  · left
    exact ⟨hs, by nlinarith⟩
  · right
    exact ⟨by nlinarith, by linarith⟩


/-! ## The assembly -/

/-- `gMax4` is attained at one of the four corners. -/
lemma gMax4_eq_corner (δ μ ν a b c d : ℝ) :
    gMax4 δ μ ν a b c d = gSym δ μ ν a c ∨ gMax4 δ μ ν a b c d = gSym δ μ ν a d
      ∨ gMax4 δ μ ν a b c d = gSym δ μ ν b c ∨ gMax4 δ μ ν a b c d = gSym δ μ ν b d := by
  unfold gMax4
  rcases max_choice (max (gSym δ μ ν a c) (gSym δ μ ν a d))
    (max (gSym δ μ ν b c) (gSym δ μ ν b d)) with h | h <;> rw [h]
  · rcases max_choice (gSym δ μ ν a c) (gSym δ μ ν a d) with h' | h' <;> rw [h']
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases max_choice (gSym δ μ ν b c) (gSym δ μ ν b d) with h' | h' <;> rw [h']
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

set_option maxHeartbeats 1000000 in
/-- V-side relabelling invariance. -/
theorem lagrTwoPoint_neg_swap_snd (δ μ ν a b c d : ℝ) :
    lagrTwoPoint δ μ ν a b (-d) (-c) = lagrTwoPoint δ μ ν a b c d := by
  have e1 : δ * (a * -d) = -(δ * (a * d)) := by ring
  have e2 : -(δ * (a * -c)) = δ * (a * c) := by ring
  have e3 : -(δ * (b * -d)) = δ * (b * d) := by ring
  have e4 : δ * (b * -c) = -(δ * (b * c)) := by ring
  rw [lagrTwoPoint, lagrTwoPoint, e1, e2, e3, e4, fe_neg c, fe_neg d]
  rcases eq_or_ne (c + d) 0 with h | h
  · have h' : -d + -c = 0 := by linarith
    rw [h, h']; simp
  · have h' : -d + -c ≠ 0 := by intro hc; exact h (by linarith)
    field_simp
    ring

set_option maxHeartbeats 800000 in
/-- **Domination, for normalised two-point data.**  The two-point theorem bounds
`F` by `gMax4`, and `gMax4` is realised by an actual BSC pair in `ℬ`. -/
theorem exists_regionB_dominating_normalised {p μ ν A B C D : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ0 : 0 < 1 - 2 * p) (hδ1 : 1 - 2 * p < 1)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (hD0 : 0 ≤ D) (hD1 : D ≤ 1)
    (hAB : 0 < A + B) (hCD : 0 < C + D) :
    ∃ S ∈ regionB p,
      lagrTwoPoint (1 - 2 * p) μ ν A B C D ≤ S.1 - μ * S.2.1 - ν * S.2.2 := by
  set M := gMax4 (1 - 2 * p) μ ν A B C D with hM
  have k1 : gSym (1 - 2 * p) μ ν A C ≤ M := by
    rw [hM, gMax4]; exact le_max_of_le_left (le_max_left _ _)
  have k2 : gSym (1 - 2 * p) μ ν A D ≤ M := by
    rw [hM, gMax4]; exact le_max_of_le_left (le_max_right _ _)
  have k3 : gSym (1 - 2 * p) μ ν B C ≤ M := by
    rw [hM, gMax4]; exact le_max_of_le_right (le_max_left _ _)
  have k4 : gSym (1 - 2 * p) μ ν B D ≤ M := by
    rw [hM, gMax4]; exact le_max_of_le_right (le_max_right _ _)
  have hbound := lagrTwoPoint_le_of_corner_bounds_closed hδ0 hδ1 hA0 hA1 hB0 hB1 hC0 hC1 hD0 hD1
    hAB hCD k1 k2 k3 k4
  rcases gMax4_eq_corner (1 - 2 * p) μ ν A B C D with h | h | h | h
  · obtain ⟨S, hS, hval⟩ := exists_regionB_point (μ := μ) (ν := ν) hp0 hp1 hA0 hA1 hC0 hC1
    exact ⟨S, hS, by rw [← hval, ← h]; exact hbound⟩
  · obtain ⟨S, hS, hval⟩ := exists_regionB_point (μ := μ) (ν := ν) hp0 hp1 hA0 hA1 hD0 hD1
    exact ⟨S, hS, by rw [← hval, ← h]; exact hbound⟩
  · obtain ⟨S, hS, hval⟩ := exists_regionB_point (μ := μ) (ν := ν) hp0 hp1 hB0 hB1 hC0 hC1
    exact ⟨S, hS, by rw [← hval, ← h]; exact hbound⟩
  · obtain ⟨S, hS, hval⟩ := exists_regionB_point (μ := μ) (ν := ν) hp0 hp1 hB0 hB1 hD0 hD1
    exact ⟨S, hS, by rw [← hval, ← h]; exact hbound⟩


/-! ## Biases at `±1` are not degenerate

A bias of `±1` means the row is deterministic (e.g. `cL` the identity channel,
`U = X`).  That is a perfectly ordinary configuration — `I(U;V)` need not vanish
— so it is *not* a degenerate branch but a case the bias formula must cover.
The row identity extends to the closed range because `f_e(±1) = log 2` exactly
cancels the vanishing entropy of a deterministic row. -/

@[simp] theorem fe_one : fe 1 = log 2 := by norm_num [fe]

@[simp] theorem fe_neg_one : fe (-1) = log 2 := by norm_num [fe]

/-- `negMulLog_row` on the **closed** range `|s| ≤ 1`. -/
theorem negMulLog_row_closed {w s : ℝ} (hw : 0 < w) (hs0 : -1 ≤ s) (hs1 : s ≤ 1) :
    Real.negMulLog (w * ((1 + s) / 2)) + Real.negMulLog (w * ((1 - s) / 2))
      = Real.negMulLog w + w * (log 2 - fe s) := by
  rcases eq_or_lt_of_le hs0 with h | hlo
  · rw [← h]
    norm_num [Real.negMulLog]
  rcases eq_or_lt_of_le hs1 with h | hhi
  · rw [h]
    norm_num [Real.negMulLog]
  · exact negMulLog_row hw hlo hhi

/-- `I = Σ_u π_u f_e(s_u)` with the biases only required to lie in `[−1,1]`. -/
theorem mutualInfo_eq_sum_fe_bias_closed {q : Bool → Bool → ℝ}
    (hpos : ∀ u, 0 < marg₁ q u) (hsum : marg₁ q false + marg₁ q true = 1)
    (hb : ∀ u, -1 ≤ biasOf q u ∧ biasOf q u ≤ 1)
    (huni : ∀ x, marg₂ q x = 1 / 2) :
    mutualInfo q = marg₁ q false * fe (biasOf q false) + marg₁ q true * fe (biasOf q true) := by
  have hrow : ∀ u, Real.negMulLog (q u false) + Real.negMulLog (q u true)
      = Real.negMulLog (marg₁ q u) + marg₁ q u * (log 2 - fe (biasOf q u)) := by
    intro u
    rw [q_false_eq (hpos u), q_true_eq (hpos u)]
    exact negMulLog_row_closed (hpos u) (hb u).1 (hb u).2
  have h2 : entropy2 q = Real.negMulLog (marg₁ q false) + Real.negMulLog (marg₁ q true)
      + (marg₁ q false * (log 2 - fe (biasOf q false))
        + marg₁ q true * (log 2 - fe (biasOf q true))) := by
    simp only [entropy2]
    have e1 := hrow false
    have e2 := hrow true
    linarith
  have h1 : entropy1 (marg₂ q) = log 2 := by
    simp only [entropy1, huni, Real.negMulLog]
    rw [show Real.log (1/2 : ℝ) = -Real.log 2 by rw [one_div, Real.log_inv]]
    ring
  have hlog : marg₁ q false * log 2 + marg₁ q true * log 2 = log 2 := by
    rw [← add_mul, hsum]; ring
  rw [mutualInfo, h1, h2]
  simp only [entropy1]
  linear_combination -hlog

/-! ## The two genuinely degenerate branches -/

/-- A joint law with a zero row carries no mutual information. -/
theorem mutualInfo_eq_zero_of_row_zero {q : Bool → Bool → ℝ} {u₀ : Bool}
    (hz : ∀ v, q u₀ v = 0)
    (hsum : q false false + q false true + q true false + q true true = 1) :
    mutualInfo q = 0 := by
  have h0 := hz false
  have h1 := hz true
  cases u₀
  · have hone : q true false + q true true = 1 := by linarith
    simp only [mutualInfo, entropy1, entropy2, marg₁, marg₂, h0, h1, hone, zero_add]
    norm_num [Real.negMulLog]
  · have hone : q false false + q false true = 1 := by linarith
    simp only [mutualInfo, entropy1, entropy2, marg₁, marg₂, h0, h1, hone, add_zero]
    norm_num [Real.negMulLog]

lemma biasOf_mem_Icc {q : Bool → Bool → ℝ} {u : Bool} (hnn : ∀ u v, 0 ≤ q u v)
    (hpos : 0 < marg₁ q u) : -1 ≤ biasOf q u ∧ biasOf q u ≤ 1 := by
  have h1 := hnn u false
  have h2 := hnn u true
  simp only [marg₁] at hpos
  constructor <;> rw [biasOf, marg₁] <;>
    [rw [le_div_iff₀ hpos]; rw [div_le_iff₀ hpos]] <;> linarith

theorem mutualInfo_jointUX_eq_bias_closed {cL : Chan}
    (hpos : ∀ u, 0 < marg₁ (jointUX cL) u) :
    mutualInfo (jointUX cL)
      = marg₁ (jointUX cL) false * fe (biasOf (jointUX cL) false)
        + marg₁ (jointUX cL) true * fe (biasOf (jointUX cL) true) := by
  have hnn : ∀ u x, 0 ≤ jointUX cL u x := by
    intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
  exact mutualInfo_eq_sum_fe_bias_closed hpos (marg₁_jointUX_sum cL)
    (fun u => biasOf_mem_Icc hnn (hpos u)) (marg₂_jointUX cL)

theorem mutualInfo_jointYV_eq_bias_closed {cR : Chan}
    (hpos : ∀ v, 0 < marg₂ (jointYV cR) v) :
    mutualInfo (jointYV cR)
      = marg₂ (jointYV cR) false * fe (biasOfSnd (jointYV cR) false)
        + marg₂ (jointYV cR) true * fe (biasOfSnd (jointYV cR) true) := by
  have htr : ∀ v, marg₁ (fun v y => jointYV cR y v) v = marg₂ (jointYV cR) v := by
    intro v; simp [marg₁, marg₂]
  have hbtr : ∀ v, biasOf (fun v y => jointYV cR y v) v = biasOfSnd (jointYV cR) v := by
    intro v; simp [biasOf, biasOfSnd, marg₁, marg₂]
  have hnn : ∀ v y, 0 ≤ (fun v y => jointYV cR y v) v y := by
    intro v y; simp only [jointYV]; have := cR.nonneg y v; linarith
  have hmarg2 : ∀ y, marg₂ (fun v y => jointYV cR y v) y = 1 / 2 := by
    intro y; have := marg₁_jointYV cR y; simpa [marg₂, marg₁] using this
  have hsum : marg₁ (fun v y => jointYV cR y v) false
      + marg₁ (fun v y => jointYV cR y v) true = 1 := by
    rw [htr false, htr true]; exact marg₂_jointYV_sum cR
  have h := mutualInfo_eq_sum_fe_bias_closed (q := fun v y => jointYV cR y v)
    (fun v => by rw [htr v]; exact hpos v) hsum
    (fun v => biasOf_mem_Icc hnn (by rw [htr v]; exact hpos v)) hmarg2
  rw [htr false, htr true, hbtr false, hbtr true] at h
  rw [← mutualInfo_transpose (jointYV cR)]
  exact h

/-- `lagrangian_eq_lagrTwoPoint` with the bias-range and kernel hypotheses
*derived* rather than assumed: positive marginals already force `|bias| ≤ 1`, and
`δ < 1` already forces the kernel positive. -/
theorem lagrangian_eq_lagrTwoPoint_closed {p μ ν : ℝ} {cL cR : Chan}
    (hδ0 : 0 < 1 - 2 * p) (hδ1 : 1 - 2 * p < 1)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hneL : biasOf (jointUX cL) false - biasOf (jointUX cL) true ≠ 0)
    (hneR : biasOfSnd (jointYV cR) false - biasOfSnd (jointYV cR) true ≠ 0) :
    mutualInfo (jointUV p cL cR) - μ * mutualInfo (jointUX cL) - ν * mutualInfo (jointYV cR)
      = lagrTwoPoint (1 - 2 * p) μ ν
          (biasOf (jointUX cL) false) (-biasOf (jointUX cL) true)
          (biasOfSnd (jointYV cR) false) (-biasOfSnd (jointYV cR) true) := by
  have hnnL : ∀ u x, 0 ≤ jointUX cL u x := by
    intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
  have hnnR : ∀ v y, 0 ≤ (fun v y => jointYV cR y v) v y := by
    intro v y; simp only [jointYV]; have := cR.nonneg y v; linarith
  have hbL : ∀ u, -1 ≤ biasOf (jointUX cL) u ∧ biasOf (jointUX cL) u ≤ 1 :=
    fun u => biasOf_mem_Icc hnnL (hpi u)
  have htr : ∀ v, marg₁ (fun v y => jointYV cR y v) v = marg₂ (jointYV cR) v := by
    intro v; simp [marg₁, marg₂]
  have hbtr : ∀ v, biasOf (fun v y => jointYV cR y v) v = biasOfSnd (jointYV cR) v := by
    intro v; simp [biasOf, biasOfSnd, marg₁, marg₂]
  have hbR : ∀ v, -1 ≤ biasOfSnd (jointYV cR) v ∧ biasOfSnd (jointYV cR) v ≤ 1 := by
    intro v
    have := biasOf_mem_Icc hnnR (u := v) (by rw [htr v]; exact hrho v)
    rwa [hbtr v] at this
  have hker : ∀ u v, 0 < 1 + (1 - 2 * p) * biasOf (jointUX cL) u * biasOfSnd (jointYV cR) v := by
    intro u v
    have h1 := (hbL u).1; have h2 := (hbL u).2
    have h3 := (hbR v).1; have h4 := (hbR v).2
    have hprod : -1 ≤ biasOf (jointUX cL) u * biasOfSnd (jointYV cR) v := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + biasOf (jointUX cL) u)
          (by linarith : (0:ℝ) ≤ 1 + biasOfSnd (jointYV cR) v),
        mul_nonneg (by linarith : (0:ℝ) ≤ 1 - biasOf (jointUX cL) u)
          (by linarith : (0:ℝ) ≤ 1 - biasOfSnd (jointYV cR) v)]
    have hmul := mul_le_mul_of_nonneg_left hprod (le_of_lt hδ0)
    nlinarith [hmul]
  rw [mutualInfo_jointUV_eq_kernel_sum p cL cR hpi hrho hker,
    mutualInfo_jointUX_eq_bias_closed hpi, mutualInfo_jointYV_eq_bias_closed hrho,
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

/-- **Domination for a regular channel pair.** -/
theorem exists_regionB_dominating {p μ ν : ℝ} {R : ℝ × ℝ × ℝ} {cL cR : Chan}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ0 : 0 < 1 - 2 * p) (hδ1 : 1 - 2 * p < 1)
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hRA : mutualInfo (jointUX cL) ≤ R.2.1) (hRB : mutualInfo (jointYV cR) ≤ R.2.2)
    (hRC : R.1 ≤ mutualInfo (jointUV p cL cR))
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hneL : biasOf (jointUX cL) false - biasOf (jointUX cL) true ≠ 0)
    (hneR : biasOfSnd (jointYV cR) false - biasOfSnd (jointYV cR) true ≠ 0) :
    ∃ S ∈ regionB p, R.1 - μ * R.2.1 - ν * R.2.2 ≤ S.1 - μ * S.2.1 - ν * S.2.2 := by
  have hnnL0 : ∀ u x, 0 ≤ jointUX cL u x := by
    intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
  have hnnR0 : ∀ v y, 0 ≤ (fun v y => jointYV cR y v) v y := by
    intro v y; simp only [jointYV]; have := cR.nonneg y v; linarith
  have hbL : ∀ u, -1 ≤ biasOf (jointUX cL) u ∧ biasOf (jointUX cL) u ≤ 1 :=
    fun u => biasOf_mem_Icc hnnL0 (hpi u)
  have htr0 : ∀ v, marg₁ (fun v y => jointYV cR y v) v = marg₂ (jointYV cR) v := by
    intro v; simp [marg₁, marg₂]
  have hbtr0 : ∀ v, biasOf (fun v y => jointYV cR y v) v = biasOfSnd (jointYV cR) v := by
    intro v; simp [biasOf, biasOfSnd, marg₁, marg₂]
  have hbR : ∀ v, -1 ≤ biasOfSnd (jointYV cR) v ∧ biasOfSnd (jointYV cR) v ≤ 1 := by
    intro v
    have := biasOf_mem_Icc hnnR0 (u := v) (by rw [htr0 v]; exact hrho v)
    rwa [hbtr0 v] at this
  set sf := biasOf (jointUX cL) false with hsfd
  set st := biasOf (jointUX cL) true with hstd
  set tf := biasOfSnd (jointYV cR) false with htfd
  set tt := biasOfSnd (jointYV cR) true with httd
  have hVswap : ∀ a b : ℝ,
      lagrTwoPoint (1 - 2 * p) μ ν a b tt (-tf)
        = lagrTwoPoint (1 - 2 * p) μ ν a b tf (-tt) := by
    intro a b
    have h := lagrTwoPoint_neg_swap_snd (1 - 2 * p) μ ν a b tf (-tt)
    simpa using h
  have hUswap : ∀ C D : ℝ,
      lagrTwoPoint (1 - 2 * p) μ ν st (-sf) C D
        = lagrTwoPoint (1 - 2 * p) μ ν sf (-st) C D := by
    intro C D
    have h := lagrTwoPoint_neg_swap (1 - 2 * p) μ ν sf (-st) C D
    simpa using h
  have hL : R.1 - μ * R.2.1 - ν * R.2.2
      ≤ mutualInfo (jointUV p cL cR) - μ * mutualInfo (jointUX cL)
        - ν * mutualInfo (jointYV cR) := by
    have h1 := mul_le_mul_of_nonneg_left hRA hμ
    have h2 := mul_le_mul_of_nonneg_left hRB hν
    linarith
  rw [lagrangian_eq_lagrTwoPoint_closed hδ0 hδ1 hpi hrho hneL hneR] at hL
  have hzL := pi_bias_sum_zero cL (hpi false) (hpi true)
  have hzR := rho_bias_sum_zero cR (hrho false) (hrho true)
  have hLne : sf ≠ st := by intro h; exact hneL (by rw [h]; ring)
  have hRne : tf ≠ tt := by intro h; exact hneR (by rw [h]; ring)
  obtain ⟨C, D, hC0, hC1, hD0, hD1, hCD, hCeq⟩ :
      ∃ C D : ℝ, 0 ≤ C ∧ C ≤ 1 ∧ 0 ≤ D ∧ D ≤ 1 ∧ 0 < C + D ∧
        ∀ a b : ℝ, lagrTwoPoint (1 - 2 * p) μ ν a b C D
          = lagrTwoPoint (1 - 2 * p) μ ν a b tf (-tt) := by
    rcases bias_sign_cases (hrho false) (hrho true) hzR with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨tf, -tt, h1, (hbR false).2, h2, by linarith [(hbR true).1], ?_,
        fun a b => rfl⟩
      rcases lt_or_gt_of_ne hRne with h | h <;> linarith
    · refine ⟨tt, -tf, h1, (hbR true).2, h2, by linarith [(hbR false).1], ?_, hVswap⟩
      rcases lt_or_gt_of_ne hRne with h | h <;> linarith
  obtain ⟨A, B, hA0, hA1, hB0, hB1, hAB, hAeq⟩ :
      ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ 0 ≤ B ∧ B ≤ 1 ∧ 0 < A + B ∧
        lagrTwoPoint (1 - 2 * p) μ ν A B C D
          = lagrTwoPoint (1 - 2 * p) μ ν sf (-st) C D := by
    rcases bias_sign_cases (hpi false) (hpi true) hzL with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨sf, -st, h1, (hbL false).2, h2, by linarith [(hbL true).1], ?_, rfl⟩
      rcases lt_or_gt_of_ne hLne with h | h <;> linarith
    · refine ⟨st, -sf, h1, (hbL true).2, h2, by linarith [(hbL false).1], ?_,
        hUswap C D⟩
      rcases lt_or_gt_of_ne hLne with h | h <;> linarith
  rw [← hCeq sf (-st), ← hAeq] at hL
  obtain ⟨S, hS, hSval⟩ := exists_regionB_dominating_normalised (μ := μ) (ν := ν)
    hp0 hp1 hδ0 hδ1 hA0 hA1 hB0 hB1 hC0 hC1 hD0 hD1 hAB hCD
  exact ⟨S, hS, le_trans hL hSval⟩


/-! ## Every point of `𝒜` is dominated — all cases -/

lemma jointUX_sum_one (cL : Chan) :
    jointUX cL false false + jointUX cL false true + jointUX cL true false
      + jointUX cL true true = 1 := by
  simp only [jointUX]
  have h1 := cL.sum_one false
  have h2 := cL.sum_one true
  linarith

lemma jointYV_sum_one (cR : Chan) :
    jointYV cR false false + jointYV cR false true + jointYV cR true false
      + jointYV cR true true = 1 := by
  simp only [jointYV]
  have h1 := cR.sum_one false
  have h2 := cR.sum_one true
  linarith

/-- **Domination, unconditionally.** -/
theorem exists_regionB_dominating_all {p μ ν : ℝ} {R : ℝ × ℝ × ℝ}
    (hδ0 : 0 < 1 - 2 * p) (hδ1 : 1 - 2 * p < 1)
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hR : R ∈ regionA p) :
    ∃ S ∈ regionB p, R.1 - μ * R.2.1 - ν * R.2.2 ≤ S.1 - μ * S.2.1 - ν * S.2.2 := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : p ≤ 1 := by linarith
  obtain ⟨cL, cR, hRA, hRB, hRC⟩ := hR
  have htriv : ((0:ℝ), (0:ℝ), (0:ℝ)) ∈ regionB p :=
    orthant_subset_regionB p (by norm_num) (by norm_num) (by norm_num)
  -- if the joint information vanishes, the trivial point dominates
  have hzero : mutualInfo (jointUV p cL cR) ≤ 0 →
      ∃ S ∈ regionB p, R.1 - μ * R.2.1 - ν * R.2.2 ≤ S.1 - μ * S.2.1 - ν * S.2.2 := by
    intro h
    refine ⟨((0:ℝ), (0:ℝ), (0:ℝ)), htriv, ?_⟩
    have hnnL : ∀ u x, 0 ≤ jointUX cL u x := by
      intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
    have hnnR : ∀ y v, 0 ≤ jointYV cR y v := by
      intro y v; simp only [jointYV]; have := cR.nonneg y v; linarith
    have h1 : 0 ≤ R.2.1 :=
      le_trans (mutualInfo_nonneg hnnL (jointUX_sum_one cL)) hRA
    have h2 : 0 ≤ R.2.2 :=
      le_trans (mutualInfo_nonneg hnnR (jointYV_sum_one cR)) hRB
    have h3 : R.1 ≤ 0 := le_trans hRC h
    have := mul_nonneg hμ h1
    have := mul_nonneg hν h2
    simp only
    linarith
  by_cases hpi : ∀ u, 0 < marg₁ (jointUX cL) u
  case neg =>
    push Not at hpi
    obtain ⟨u₀, hu₀⟩ := hpi
    have hnn : ∀ u x, 0 ≤ jointUX cL u x := by
      intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
    have hm0 : marg₁ (jointUX cL) u₀ = 0 :=
      le_antisymm hu₀ (by simp only [marg₁]; exact add_nonneg (hnn u₀ false) (hnn u₀ true))
    have hrow : ∀ x, jointUX cL u₀ x = 0 := by
      intro x
      simp only [marg₁] at hm0
      have ha := hnn u₀ false; have hb := hnn u₀ true
      cases x <;> linarith
    have hUX := mutualInfo_eq_zero_of_row_zero hrow (jointUX_sum_one cL)
    exact hzero (le_trans (mutualInfo_jointUV_le_jointUX hp0 hp1 cL cR) (le_of_eq hUX))
  case pos =>
  by_cases hrho : ∀ v, 0 < marg₂ (jointYV cR) v
  case neg =>
    push Not at hrho
    obtain ⟨v₀, hv₀⟩ := hrho
    have hnn : ∀ y v, 0 ≤ jointYV cR y v := by
      intro y v; simp only [jointYV]; have := cR.nonneg y v; linarith
    have hm0 : marg₂ (jointYV cR) v₀ = 0 :=
      le_antisymm hv₀ (by simp only [marg₂]; exact add_nonneg (hnn false v₀) (hnn true v₀))
    set qT : Bool → Bool → ℝ := fun v y => jointYV cR y v with hqT
    have hrow : ∀ y, qT v₀ y = 0 := by
      intro y
      simp only [marg₂] at hm0
      have ha := hnn false v₀; have hb := hnn true v₀
      cases y <;> simp only [hqT] <;> linarith
    have hsum : qT false false + qT false true + qT true false + qT true true = 1 := by
      simp only [hqT]; have := jointYV_sum_one cR; linarith
    have hYV := mutualInfo_eq_zero_of_row_zero hrow hsum
    rw [hqT] at hYV
    rw [mutualInfo_transpose (jointYV cR)] at hYV
    exact hzero (le_trans (mutualInfo_jointUV_le_jointYV hp0 hp1 cL cR) (le_of_eq hYV))
  case pos =>
  by_cases hneL : biasOf (jointUX cL) false - biasOf (jointUX cL) true ≠ 0
  case neg =>
    push Not at hneL
    have hz := pi_bias_sum_zero cL (hpi false) (hpi true)
    have hs := marg₁_jointUX_sum cL
    have h0 : biasOf (jointUX cL) false = 0 := by nlinarith [hpi false, hpi true]
    have h1 : biasOf (jointUX cL) true = 0 := by linarith
    have hUX : mutualInfo (jointUX cL) = 0 := by
      rw [mutualInfo_jointUX_eq_bias_closed hpi, h0, h1]
      norm_num [fe]
    exact hzero (le_trans (mutualInfo_jointUV_le_jointUX hp0 hp1 cL cR) (le_of_eq hUX))
  case pos =>
  by_cases hneR : biasOfSnd (jointYV cR) false - biasOfSnd (jointYV cR) true ≠ 0
  case neg =>
    push Not at hneR
    have hz := rho_bias_sum_zero cR (hrho false) (hrho true)
    have hs := marg₂_jointYV_sum cR
    have h0 : biasOfSnd (jointYV cR) false = 0 := by nlinarith [hrho false, hrho true]
    have h1 : biasOfSnd (jointYV cR) true = 0 := by linarith
    have hYV : mutualInfo (jointYV cR) = 0 := by
      rw [mutualInfo_jointYV_eq_bias_closed hrho, h0, h1]
      norm_num [fe]
    exact hzero (le_trans (mutualInfo_jointUV_le_jointYV hp0 hp1 cL cR) (le_of_eq hYV))
  case pos =>
    exact exists_regionB_dominating hp0 hp1 hδ0 hδ1 hμ hν hRA hRB hRC hpi hrho hneL hneR

/-! ## ★ The conjecture -/

/-- **MathOverflow 285151 / Conjecture 5.2, for `0 < p < 1/2`.**

`conv 𝒜 = conv ℬ`: averaged binary symmetric channels do maximise mutual
information.  The endpoints are already known — `p = 1/2` is
`averagedBSCConjecture_half` and `p = 0` is `averagedBSCConjecture_zero`. -/
theorem averagedBSCConjecture_of_lt_half {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    AveragedBSCConjecture p := by
  have hδ0 : 0 < 1 - 2 * p := by linarith
  have hδ1 : 1 - 2 * p < 1 := by linarith
  rw [averagedBSCConjecture_iff (by linarith) (by linarith)]
  exact regionA_subset_convexHull_regionB
    (fun μ ν hμ hν R hR => exists_regionB_dominating_all hδ0 hδ1 hμ hν hR)

/-- **The conjecture for every `p ∈ [0, 1/2]`.** -/
theorem averagedBSCConjecture_of_mem {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    AveragedBSCConjecture p := by
  rcases eq_or_lt_of_le hp0 with h | h
  · rw [← h]; exact averagedBSCConjecture_zero
  rcases eq_or_lt_of_le hp1 with h' | h'
  · rw [h']; exact averagedBSCConjecture_half
  · exact averagedBSCConjecture_of_lt_half h h'

/-! ## The reflection `p ↦ 1 − p`, and the conjecture on all of `[0,1]`

For `p > 1/2` the source is the `1−p` source with one coordinate relabelled, so
nothing new happens.  On the `𝒜` side this is `mirror` (already in
`DataProcessing`); on the `ℬ` side it is the identity
`(a ⊛ (1−p)) ⊛ b = 1 − ((a ⊛ p) ⊛ b)` together with `h₂(1−y) = h₂ y`. -/

lemma h2_one_sub (y : ℝ) : h2 (1 - y) = h2 y := by
  simp only [h2, show (1:ℝ) - (1 - y) = y by ring]
  ring

lemma bconv_one_sub_right (a p : ℝ) : a ⊛ (1 - p) = 1 - a ⊛ p := by
  unfold bconv; ring

lemma bconv_one_sub_left (x b : ℝ) : (1 - x) ⊛ b = 1 - x ⊛ b := by
  unfold bconv; ring

theorem regionB_one_sub (p : ℝ) : regionB (1 - p) = regionB p := by
  ext R
  constructor <;> rintro ⟨a, b, ha0, ha1, hb0, hb1, h1, h2', h3⟩ <;>
    refine ⟨a, b, ha0, ha1, hb0, hb1, h1, h2', ?_⟩
  · rwa [bconv_one_sub_right, bconv_one_sub_left, h2_one_sub] at h3
  · rwa [bconv_one_sub_right, bconv_one_sub_left, h2_one_sub]

theorem regionA_one_sub_subset (p : ℝ) : regionA (1 - p) ⊆ regionA p := by
  rintro R ⟨cL, cR, h1, h2', h3⟩
  exact ⟨mirror cL, cR, by rwa [mutualInfo_jointUX_mirror], h2',
    by rwa [mutualInfo_jointUV_mirror]⟩

theorem regionA_one_sub (p : ℝ) : regionA (1 - p) = regionA p := by
  refine Set.Subset.antisymm (regionA_one_sub_subset p) ?_
  have h := regionA_one_sub_subset (1 - p)
  rwa [show (1:ℝ) - (1 - p) = p by ring] at h

/-- **The conjecture is invariant under `p ↦ 1 − p`.** -/
theorem averagedBSCConjecture_one_sub {p : ℝ} (h : AveragedBSCConjecture (1 - p)) :
    AveragedBSCConjecture p := by
  rw [AveragedBSCConjecture, ← regionA_one_sub p, ← regionB_one_sub p]
  exact h

/-- **★ MathOverflow 285151, for every `p ∈ [0,1]`.** -/
theorem averagedBSCConjecture_all {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    AveragedBSCConjecture p := by
  rcases le_or_gt p (1 / 2) with h | h
  · exact averagedBSCConjecture_of_mem hp0 h
  · exact averagedBSCConjecture_one_sub
      (averagedBSCConjecture_of_mem (by linarith) (by linarith))

end BSCAveraging
