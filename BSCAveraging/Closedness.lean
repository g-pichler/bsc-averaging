import BSCAveraging.Regions
import BSCAveraging.Zero
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.LocallyConvex.Separation

/-! # The regions are closed

`regionA` and `regionB` are closed, and so are their convex hulls.  The argument
is the obvious one and needs no information theory:

```
T      := {f : Bool → Bool → ℝ | f ≥ 0, row sums 1}      compact (closed + bounded in ℝ⁴)
val p  : T × T → ℝ³,  (f,g) ↦ (I(U;V), I(U;X), I(Y;V))    continuous
K p    := val p '' (T ×ˢ T)                               compact
C      := {c | c₀ ≤ 0, c₁ ≥ 0, c₂ ≥ 0}                    closed convex cone
regionA p = K p + C                                       compact + closed ⇒ closed
```

and `convexHull (K + C) = convexHull K + C` with `convexHull K` compact, so the
hulls are closed too.  A `Chan` is exactly a member of `T` together with its
proofs, so nothing is lost by working with the transition functions.

See `BSCAveraging.Basic`. -/

open Real Set Pointwise

namespace BSCAveraging
/-- The recession cone: down in `R₀`, up in `R₁` and `R₂`. -/
def coneC : Set (ℝ × ℝ × ℝ) := {c | c.1 ≤ 0 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2}

lemma isClosed_coneC : IsClosed coneC := by
  have : coneC = {c : ℝ × ℝ × ℝ | c.1 ≤ 0} ∩ ({c : ℝ × ℝ × ℝ | 0 ≤ c.2.1}
      ∩ {c : ℝ × ℝ × ℝ | 0 ≤ c.2.2}) := by
    ext c; simp [coneC]
  rw [this]
  exact (isClosed_le (by fun_prop) continuous_const).inter
    ((isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_le continuous_const (by fun_prop)))

lemma convex_coneC : Convex ℝ coneC := by
  intro x hx y hy s t hs ht _
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · have h1 : s * x.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs hx1
    have h2 : t * y.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hy1
    linarith
  · have h1 : 0 ≤ s * x.2.1 := mul_nonneg hs hx2
    have h2 : 0 ≤ t * y.2.1 := mul_nonneg ht hy2
    linarith
  · have h1 : 0 ≤ s * x.2.2 := mul_nonneg hs hx3
    have h2 : 0 ≤ t * y.2.2 := mul_nonneg ht hy3
    linarith

/-! ## `regionA = valSet + coneC`, hence closed -/

/-- The value triple of the symmetric pair with crossovers `a`, `b`. -/
noncomputable def valB (p : ℝ) (ab : ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (log 2 - h2 ((ab.1 ⊛ p) ⊛ ab.2), log 2 - h2 ab.1, log 2 - h2 ab.2)

lemma continuous_valB (p : ℝ) : Continuous (valB p) := by
  unfold valB h2 bconv
  fun_prop

def valBSet (p : ℝ) : Set (ℝ × ℝ × ℝ) := valB p '' (Icc 0 1 ×ˢ Icc 0 1)

lemma isCompact_valBSet (p : ℝ) : IsCompact (valBSet p) :=
  ((isCompact_Icc (a := (0:ℝ)) (b := 1)).prod
    (isCompact_Icc (a := (0:ℝ)) (b := 1))).image (continuous_valB p)

theorem regionB_eq_add_cone (p : ℝ) : regionB p = valBSet p + coneC := by
  ext R
  constructor
  · rintro ⟨a, b, ha0, ha1, hb0, hb1, h1, h2, h3⟩
    refine ⟨valB p (a, b), ⟨(a, b), ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩, rfl⟩,
      R - valB p (a, b), ?_, by ring⟩
    exact ⟨by simp [valB]; linarith, by simp [valB]; linarith, by simp [valB]; linarith⟩
  · rintro ⟨k, ⟨ab, ⟨⟨ha0, ha1⟩, hb0, hb1⟩, rfl⟩, c, hc, rfl⟩
    refine ⟨ab.1, ab.2, ha0, ha1, hb0, hb1, ?_, ?_, ?_⟩
    · simp only [valB, Prod.snd_add, Prod.fst_add]; linarith [hc.2.1]
    · simp only [valB, Prod.snd_add]; linarith [hc.2.2]
    · simp only [valB, Prod.fst_add]; linarith [hc.1]

/-- The combination map. -/
noncomputable def combMap (wx : (Fin 4 → ℝ) × (Fin 4 → ℝ × ℝ × ℝ)) : ℝ × ℝ × ℝ :=
  ∑ i, wx.1 i • wx.2 i

lemma continuous_combMap : Continuous combMap := by
  unfold combMap
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd)

/-- Every convex combination of points of `S` lies in `convexHull S`. -/
lemma combMap_mem_convexHull {S : Set (ℝ × ℝ × ℝ)} {w : Fin 4 → ℝ} {x : Fin 4 → ℝ × ℝ × ℝ}
    (hw : w ∈ stdSimplex ℝ (Fin 4)) (hx : ∀ i, x i ∈ S) :
    combMap (w, x) ∈ convexHull ℝ S := by
  refine (convex_convexHull ℝ S).sum_mem (fun i _ => hw.1 i) ?_ (fun i _ => subset_convexHull ℝ S (hx i))
  simpa using hw.2

/-- Carathéodory in `ℝ³`: every point of `convexHull S` is a convex combination
of exactly four points of `S` (repetitions and zero weights allowed). -/
lemma exists_comb_of_mem_convexHull {S : Set (ℝ × ℝ × ℝ)} (hS : S.Nonempty)
    {x : ℝ × ℝ × ℝ} (hx : x ∈ convexHull ℝ S) :
    ∃ w : Fin 4 → ℝ, ∃ z : Fin 4 → ℝ × ℝ × ℝ,
      w ∈ stdSimplex ℝ (Fin 4) ∧ (∀ i, z i ∈ S) ∧ combMap (w, z) = x := by
  obtain ⟨s₀, hs₀⟩ := hS
  obtain ⟨ι, _, z, w, hzs, hai, hwpos, hwsum, hwx⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ Fintype.card (Fin 4) := by
    have h := hai.card_le_finrank_succ
    have hle : Module.finrank ℝ ↥(vectorSpan ℝ (Set.range z))
        ≤ Module.finrank ℝ (ℝ × ℝ × ℝ) := Submodule.finrank_le _
    have hrk : Module.finrank ℝ (ℝ × ℝ × ℝ) = 3 := by simp
    simp only [Fintype.card_fin]
    omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨Function.extend f w 0, Function.extend f z (fun _ => s₀), ⟨?_, ?_⟩, ?_, ?_⟩
  · -- non-negativity
    intro j
    by_cases h : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := h
      rw [f.injective.extend_apply]
      exact le_of_lt (hwpos i)
    · rw [Function.extend_apply' _ _ _ h]; simp
  · -- weights sum to one
    have hz : ∀ j ∉ Finset.univ.map f, Function.extend f w 0 j = 0 := by
      intro j hj
      have : ¬ ∃ i, f i = j := by
        intro ⟨i, hi⟩; exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, hi⟩)
      rw [Function.extend_apply' _ _ _ this]; simp
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map f)) (fun j _ hj => hz j hj),
      Finset.sum_map]
    simpa [f.injective.extend_apply] using hwsum
  · -- points lie in `S`
    intro j
    by_cases h : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := h
      rw [f.injective.extend_apply]
      exact hzs ⟨i, rfl⟩
    · rw [Function.extend_apply' _ _ _ h]; exact hs₀
  · -- the combination is `x`
    have hz : ∀ j ∉ Finset.univ.map f,
        Function.extend f w 0 j • Function.extend f z (fun _ => s₀) j = 0 := by
      intro j hj
      have : ¬ ∃ i, f i = j := by
        intro ⟨i, hi⟩; exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, hi⟩)
      rw [Function.extend_apply' _ _ _ this]; simp
    show ∑ j, Function.extend f w 0 j • Function.extend f z (fun _ => s₀) j = x
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map f)) (fun j _ hj => hz j hj),
      Finset.sum_map]
    simpa [f.injective.extend_apply] using hwx

theorem convexHull_eq_combMap_image {S : Set (ℝ × ℝ × ℝ)} (hS : S.Nonempty) :
    convexHull ℝ S
      = combMap '' (stdSimplex ℝ (Fin 4) ×ˢ {x : Fin 4 → ℝ × ℝ × ℝ | ∀ i, x i ∈ S}) := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, z, hw, hz, hcomb⟩ := exists_comb_of_mem_convexHull hS hx
    exact ⟨(w, z), ⟨hw, hz⟩, hcomb⟩
  · rintro ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
    exact combMap_mem_convexHull hw hz

/-- **Convex hull of a compact set in `ℝ³` is compact.**  Missing from Mathlib
v4.32.0, supplied here. -/
theorem isCompact_convexHull {S : Set (ℝ × ℝ × ℝ)} (hS : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · rw [convexHull_eq_combMap_image hne]
    refine IsCompact.image ?_ continuous_combMap
    refine (isCompact_stdSimplex (𝕜 := ℝ) (ι := Fin 4)).prod ?_
    have : {x : Fin 4 → ℝ × ℝ × ℝ | ∀ i, x i ∈ S} = Set.univ.pi fun _ => S := by
      ext x; simp [Set.mem_pi]
    rw [this]
    exact isCompact_univ_pi fun _ => hS

/-! ## The convex hulls are closed

`conv (K + C) = conv K + C` because `C` is convex, and `conv K` is compact by
`isCompact_convexHull`.  So both hulls are `compact + closed`, hence closed —
which is exactly what the separation step of the support-function reduction
needs. -/

theorem isClosed_convexHull_regionB (p : ℝ) : IsClosed (convexHull ℝ (regionB p)) := by
  rw [regionB_eq_add_cone, convexHull_add, convex_coneC.convexHull_eq]
  exact isClosed_coneC.add_left_of_isCompact (isCompact_convexHull (isCompact_valBSet p))

lemma orthant_subset_regionB (p : ℝ) {R : ℝ × ℝ × ℝ}
    (hz0 : R.1 ≤ 0) (hz1 : 0 ≤ R.2.1) (hz2 : 0 ≤ R.2.2) : R ∈ regionB p := by
  have hh : h2 (1/2 : ℝ) = log 2 := h2_half
  refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · rw [hh]; linarith
  · rw [hh]; linarith
  · have hb : ((1/2 : ℝ) ⊛ p) ⊛ (1/2 : ℝ) = 1/2 := by unfold bconv; ring
    rw [hb, hh]; linarith

/-- **The support-function reduction.**  If every point of `𝒜` is dominated, in
every direction `F = R₀ − μR₁ − νR₂` with `μ,ν ≥ 0`, by some point of `ℬ`, then
`𝒜 ⊆ conv ℬ`. -/
theorem regionA_subset_convexHull_regionB {p : ℝ}
    (hsupp : ∀ μ ν : ℝ, 0 ≤ μ → 0 ≤ ν → ∀ R ∈ regionA p, ∃ S ∈ regionB p,
      R.1 - μ * R.2.1 - ν * R.2.2 ≤ S.1 - μ * S.2.1 - ν * S.2.2) :
    regionA p ⊆ convexHull ℝ (regionB p) := by
  intro R hR
  by_contra hnot
  obtain ⟨f, u, hlt, hgt⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (regionB p)) (isClosed_convexHull_regionB p) hnot
  have hsub : ∀ S ∈ regionB p, f S < u := fun S hS => hlt S (subset_convexHull ℝ _ hS)
  set l0 := f (1, 0, 0) with hl0
  set l1 := f (0, 1, 0) with hl1
  set l2 := f (0, 0, 1) with hl2
  have hf : ∀ x : ℝ × ℝ × ℝ, f x = x.1 * l0 + x.2.1 * l1 + x.2.2 * l2 := by
    intro x
    have hx : x = x.1 • ((1:ℝ), (0:ℝ), (0:ℝ)) + x.2.1 • ((0:ℝ), (1:ℝ), (0:ℝ))
        + x.2.2 • ((0:ℝ), (0:ℝ), (1:ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hx]
    rw [map_add, map_add, map_smul, map_smul, map_smul]
    simp only [hl0, hl1, hl2, smul_eq_mul]
  -- `f` is bounded above on the orthant, forcing the signs of `l0, l1, l2`
  have key1 : ∀ T : ℝ, 0 ≤ T → T * l1 < u := by
    intro T hT
    have h := hsub _ (orthant_subset_regionB p (R := ((0:ℝ), T, (0:ℝ)))
      (by norm_num) hT (by norm_num))
    rw [hf] at h; simpa using h
  have key2 : ∀ T : ℝ, 0 ≤ T → T * l2 < u := by
    intro T hT
    have h := hsub _ (orthant_subset_regionB p (R := ((0:ℝ), (0:ℝ), T))
      (by norm_num) (by norm_num) hT)
    rw [hf] at h; simpa using h
  have key0 : ∀ T : ℝ, 0 ≤ T → -T * l0 < u := by
    intro T hT
    have h := hsub _ (orthant_subset_regionB p (R := ((-T : ℝ), (0:ℝ), (0:ℝ)))
      (by simpa using hT) (by norm_num) (by norm_num))
    rw [hf] at h; simpa using h
  have hl1le : l1 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hT : (0:ℝ) ≤ (|u| + 1) / l1 := div_nonneg (by positivity) (le_of_lt hpos)
    have := key1 _ hT
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at this
    linarith [le_abs_self u]
  have hl2le : l2 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hT : (0:ℝ) ≤ (|u| + 1) / l2 := div_nonneg (by positivity) (le_of_lt hpos)
    have := key2 _ hT
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at this
    linarith [le_abs_self u]
  have hl0ge : 0 ≤ l0 := by
    by_contra hneg
    push Not at hneg
    have hT : (0:ℝ) ≤ (|u| + 1) / (-l0) := div_nonneg (by positivity) (by linarith)
    have := key0 _ hT
    rw [show -((|u| + 1) / (-l0)) * l0 = (|u| + 1) / (-l0) * (-l0) by ring,
      div_mul_cancel₀ _ (by linarith : -l0 ≠ 0)] at this
    linarith [le_abs_self u]
  have hl0pos : 0 < l0 := by
    rcases lt_or_eq_of_le hl0ge with h | h
    · exact h
    · exfalso
      have h1 := hsub _ (orthant_subset_regionB p (R := ((0:ℝ), (0:ℝ), (0:ℝ)))
        (by norm_num) (by norm_num) (by norm_num))
      rw [hf] at h1
      have hu : 0 < u := by simpa using h1
      have hR1 : 0 ≤ R.2.1 := regionA_snd_fst_nonneg hR
      have hR2 : 0 ≤ R.2.2 := regionA_snd_snd_nonneg hR
      rw [hf] at hgt
      have p0 : R.1 * l0 = 0 := by rw [← h]; ring
      have p1 : R.2.1 * l1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hR1 hl1le
      have p2 : R.2.2 * l2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hR2 hl2le
      linarith
  -- normalise: the separating functional is `l0 · F` with `μ = −l1/l0`, `ν = −l2/l0`
  obtain ⟨S, hS, hFS⟩ := hsupp (-l1 / l0) (-l2 / l0)
    (div_nonneg (by linarith) (le_of_lt hl0pos)) (div_nonneg (by linarith) (le_of_lt hl0pos))
    R hR
  have hexp : ∀ x : ℝ × ℝ × ℝ,
      l0 * (x.1 - (-l1 / l0) * x.2.1 - (-l2 / l0) * x.2.2)
        = x.1 * l0 + x.2.1 * l1 + x.2.2 * l2 := by
    intro x; field_simp; ring
  have hmul := mul_le_mul_of_nonneg_left hFS (le_of_lt hl0pos)
  rw [hexp R, hexp S] at hmul
  have hfS := hsub S hS
  rw [hf] at hgt hfS
  linarith


end BSCAveraging
