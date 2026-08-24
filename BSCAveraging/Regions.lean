import BSCAveraging.Nonneg

/-! # The regions `𝒜` and `ℬ`, and the conjecture

MathOverflow 285151, *Do averaged binary symmetric channels maximize mutual
information?* (asked by Georg Pichler, 2017; unanswered).

Let `(X, Y)` be a doubly symmetric binary source with parameter `p ∈ [0, 1/2]`.

* `regionA p` — the `(R₀, R₁, R₂)` such that **some** pair of binary channels
  `X → U`, `Y → V` (the Markov chain `U — X — Y — V`) satisfies
  `I(U;X) ≤ R₁`, `I(Y;V) ≤ R₂`, `R₀ ≤ I(U;V)`.
* `regionB p` — the same, restricted to *symmetric* channels, where the three
  mutual informations become `log 2 - h₂ a`, `log 2 - h₂ b` and
  `log 2 - h₂ (a ∗ p ∗ b)`.

`AveragedBSCConjecture p` is the open question `conv 𝒜 = conv ℬ`.  What is
proved here: `ℬ ⊆ 𝒜` (`regionB_subset_regionA`), hence one hull inclusion
(`convexHull_regionB_subset`); the reduction of the conjecture to the single
remaining inclusion `𝒜 ⊆ conv ℬ` (`averagedBSCConjecture_iff`); and the
degenerate case `p = 1/2`, where `𝒜 = ℬ` outright (`regionA_half_eq_regionB_half`,
`averagedBSCConjecture_half`).

Note on the source question: it writes the first two constraints of `ℬ` as
`R₁ ≥ 1 - H(a ∗ p)` and `R₂ ≥ 1 - H(b ∗ p)`.  That is a slip — with `X → U` a
BSC of crossover `a` one has `I(U;X) = 1 - H(a)`, which is also how the
predecessor question (MO 213084) states it, and it is what makes `ℬ ⊆ 𝒜` true.
The consistent version is formalized here.

See `BSCAveraging.Basic`. -/

open Real

namespace BSCAveraging

/-! ## The two regions -/

/-- Region `𝒜`: points `(R₀, R₁, R₂)` attainable with *arbitrary* binary
channels `X → U` and `Y → V`. -/
def regionA (p : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {R | ∃ cL cR : Chan,
      mutualInfo (jointUX cL) ≤ R.2.1 ∧
      mutualInfo (jointYV cR) ≤ R.2.2 ∧
      R.1 ≤ mutualInfo (jointUV p cL cR)}

/-- Region `ℬ`: the same points, attained with *binary symmetric* channels of
crossover `a` and `b`. -/
def regionB (p : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {R | ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧
      log 2 - h2 a ≤ R.2.1 ∧
      log 2 - h2 b ≤ R.2.2 ∧
      R.1 ≤ log 2 - h2 ((a ⊛ p) ⊛ b)}

/-! ## Monotonicity: both regions are down-closed in `R₀`, up-closed in `R₁, R₂` -/

lemma regionB_mono {p : ℝ} {R S : ℝ × ℝ × ℝ} (hR : R ∈ regionB p)
    (h0 : S.1 ≤ R.1) (h1 : R.2.1 ≤ S.2.1) (h2 : R.2.2 ≤ S.2.2) : S ∈ regionB p := by
  obtain ⟨a, b, ha0, ha1, hb0, hb1, hA, hB, hC⟩ := hR
  exact ⟨a, b, ha0, ha1, hb0, hb1, hA.trans h1, hB.trans h2, h0.trans hC⟩

/-! ## The easy inclusion `ℬ ⊆ 𝒜` -/

/-- Symmetric channels are channels: `ℬ ⊆ 𝒜`. -/
theorem regionB_subset_regionA {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    regionB p ⊆ regionA p := by
  rintro R ⟨a, b, ha0, ha1, hb0, hb1, hA, hB, hC⟩
  refine ⟨bsc a ha0 ha1, bsc b hb0 hb1, ?_, ?_, ?_⟩
  · rwa [mutualInfo_jointUX_bsc]
  · rwa [mutualInfo_jointYV_bsc]
  · rwa [mutualInfo_jointUV_bsc ha0 ha1 hb0 hb1 hp0 hp1]

/-- Consequently one hull inclusion is free. -/
theorem convexHull_regionB_subset {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    convexHull ℝ (regionB p) ⊆ convexHull ℝ (regionA p) :=
  convexHull_mono (regionB_subset_regionA hp0 hp1)

/-! ## The conjecture -/

/-- **The open question** (MathOverflow 285151): is the convex hull of `𝒜`
equal to the convex hull of `ℬ`?  I.e. do averaged binary symmetric channels
already exhaust everything arbitrary binary channels can achieve? -/
def AveragedBSCConjecture (p : ℝ) : Prop :=
  convexHull ℝ (regionA p) = convexHull ℝ (regionB p)

/-- Since `ℬ ⊆ 𝒜`, only one inclusion is at stake: the conjecture is exactly
the statement that every point of `𝒜` is a convex combination of points of
`ℬ`. -/
theorem averagedBSCConjecture_iff {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    AveragedBSCConjecture p ↔ regionA p ⊆ convexHull ℝ (regionB p) := by
  constructor
  · intro h R hR
    exact h ▸ subset_convexHull ℝ (regionA p) hR
  · intro h
    exact Set.Subset.antisymm (convexHull_min h (convex_convexHull ℝ _))
      (convexHull_regionB_subset hp0 hp1)

/-! ## The degenerate case `p = 1/2`: `X ⊥ Y` -/

@[simp] lemma mutualInfo_jointUX_useless : mutualInfo (jointUX uselessChan) = 0 := by
  unfold uselessChan
  rw [mutualInfo_jointUX_bsc, h2_half]
  ring

@[simp] lemma mutualInfo_jointYV_useless : mutualInfo (jointYV uselessChan) = 0 := by
  unfold uselessChan
  rw [mutualInfo_jointYV_bsc, h2_half]
  ring

/-- At `p = 1/2` region `𝒜` degenerates to `{R₀ ≤ 0, R₁ ≥ 0, R₂ ≥ 0}`. -/
theorem regionA_half :
    regionA (1 / 2) = {R : ℝ × ℝ × ℝ | R.1 ≤ 0 ∧ 0 ≤ R.2.1 ∧ 0 ≤ R.2.2} := by
  ext R
  constructor
  · rintro ⟨cL, cR, hA, hB, hC⟩
    rw [mutualInfo_jointUV_half] at hC
    exact ⟨hC, (mutualInfo_jointUX_nonneg cL).trans hA, (mutualInfo_jointYV_nonneg cR).trans hB⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨uselessChan, uselessChan, ?_, ?_, ?_⟩
    · rw [mutualInfo_jointUX_useless]; exact h1
    · rw [mutualInfo_jointYV_useless]; exact h2
    · rw [mutualInfo_jointUV_half]; exact h0

/-- At `p = 1/2` region `ℬ` degenerates to the same set. -/
theorem regionB_half :
    regionB (1 / 2) = {R : ℝ × ℝ × ℝ | R.1 ≤ 0 ∧ 0 ≤ R.2.1 ∧ 0 ≤ R.2.2} := by
  ext R
  constructor
  · rintro ⟨a, b, ha0, ha1, hb0, hb1, hA, hB, hC⟩
    rw [bconv_half_right, bconv_half_left, h2_half] at hC
    have hA' : h2 a ≤ log 2 := h2_le_log_two ha0 ha1
    have hB' : h2 b ≤ log 2 := h2_le_log_two hb0 hb1
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · rw [h2_half]; linarith
    · rw [h2_half]; linarith
    · rw [bconv_half_right, h2_half]; linarith

/-- At `p = 1/2` the two regions coincide, without taking convex hulls. -/
theorem regionA_half_eq_regionB_half : regionA (1 / 2) = regionB (1 / 2) := by
  rw [regionA_half, regionB_half]

/-- The conjecture holds at `p = 1/2`. -/
theorem averagedBSCConjecture_half : AveragedBSCConjecture (1 / 2) := by
  unfold AveragedBSCConjecture
  rw [regionA_half_eq_regionB_half]

end BSCAveraging
