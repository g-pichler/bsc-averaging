import BSCAveraging.Regions
import BSCAveraging.DataProcessing

/-! # The regions at `p = 0`, and the data processing outer bound

Two things:

* **Data processing on the region** (any `p`): `𝒜 ⊆ {R₀ ≤ R₁} ∩ {R₀ ≤ R₂}`,
  together with `0 ≤ R₁`, `0 ≤ R₂` and the source bound `R₀ ≤ log 2 − h₂ p`
  (`regionA_fst_le_snd_fst`, `regionA_fst_le_snd_snd`, `regionA_snd_fst_nonneg`,
  `regionA_snd_snd_nonneg`, `regionA_fst_le_source`).  Together they put `𝒜`
  inside the explicit `outerBound` (`regionA_subset_outerBound`).
* **The case `p = 0`** (`X = Y`): the conjecture holds
  (`averagedBSCConjecture_zero`), even though `𝒜 ≠ ℬ` there — the MO 213084
  counterexample lives at `p = 0`.  The reason the hulls still agree: at `p = 0`
  the data processing bound `R₀ ≤ min (R₁, R₂)` is already achieved by
  *time-sharing* the two extreme symmetric choices, the useless channel pair
  (giving `(0,0,0)`, `origin_mem_regionB_zero`) and the noiseless pair (giving
  `(log 2, log 2, log 2)`, `top_mem_regionB_zero`).

See `BSCAveraging.Basic`. -/

open Real

namespace BSCAveraging

/-! ## The data processing outer bound on `𝒜` -/

theorem regionA_fst_le_snd_fst {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R : ℝ × ℝ × ℝ}
    (hR : R ∈ regionA p) : R.1 ≤ R.2.1 := by
  obtain ⟨cL, cR, hA, _, hC⟩ := hR
  exact hC.trans ((mutualInfo_jointUV_le_jointUX hp0 hp1 cL cR).trans hA)

theorem regionA_fst_le_snd_snd {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R : ℝ × ℝ × ℝ}
    (hR : R ∈ regionA p) : R.1 ≤ R.2.2 := by
  obtain ⟨cL, cR, _, hB, hC⟩ := hR
  exact hC.trans ((mutualInfo_jointUV_le_jointYV hp0 hp1 cL cR).trans hB)

theorem regionA_snd_fst_nonneg {p : ℝ} {R : ℝ × ℝ × ℝ} (hR : R ∈ regionA p) : 0 ≤ R.2.1 := by
  obtain ⟨cL, _, hA, _, _⟩ := hR
  exact (mutualInfo_jointUX_nonneg cL).trans hA

theorem regionA_snd_snd_nonneg {p : ℝ} {R : ℝ × ℝ × ℝ} (hR : R ∈ regionA p) : 0 ≤ R.2.2 := by
  obtain ⟨_, cR, _, hB, _⟩ := hR
  exact (mutualInfo_jointYV_nonneg cR).trans hB

theorem regionA_fst_le_source {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R : ℝ × ℝ × ℝ}
    (hR : R ∈ regionA p) : R.1 ≤ log 2 - h2 p := by
  obtain ⟨cL, cR, _, _, hC⟩ := hR
  exact hC.trans (mutualInfo_jointUV_le_source hp0 hp1 cL cR)

/-! ## The outer bound, and its hull -/

/-- Everything the data processing and cut-set bounds give: an intersection of
half-spaces, hence convex, hence a bound on `conv 𝒜` and not just on `𝒜`. -/
def outerBound (p : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {R | R.1 ≤ R.2.1 ∧ R.1 ≤ R.2.2 ∧ R.1 ≤ log 2 - h2 p ∧ 0 ≤ R.2.1 ∧ 0 ≤ R.2.2}

theorem regionA_subset_outerBound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    regionA p ⊆ outerBound p := fun _ hR =>
  ⟨regionA_fst_le_snd_fst hp0 hp1 hR, regionA_fst_le_snd_snd hp0 hp1 hR,
    regionA_fst_le_source hp0 hp1 hR, regionA_snd_fst_nonneg hR, regionA_snd_snd_nonneg hR⟩

/-- The useless channel pair. -/
lemma origin_mem_regionB_zero : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ regionB 0 := by
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · rw [h2_half]; simp
  · rw [h2_half]; simp
  · rw [bconv_zero_right, bconv_half_left, h2_half]; simp

/-- The noiseless channel pair. -/
lemma top_mem_regionB_zero : ((log 2 : ℝ), (log 2 : ℝ), (log 2 : ℝ)) ∈ regionB 0 := by
  refine ⟨0, 0, le_refl _, by norm_num, le_refl _, by norm_num, ?_, ?_, ?_⟩
  · rw [h2_zero]; simp
  · rw [h2_zero]; simp
  · rw [bconv_zero_right, bconv_zero_right, h2_zero]; simp

/-! ## `p = 0`: the conjecture holds -/

/-- At `p = 0` every point of `𝒜` is a convex combination of two points of `ℬ`:
the data processing bound `R₀ ≤ min (R₁, R₂)` is attained by time-sharing the
noiseless and the useless symmetric pair. -/
theorem outerBound_zero_subset_convexHull : outerBound 0 ⊆ convexHull ℝ (regionB 0) := by
  intro R hR
  obtain ⟨hd1, hd2, hcap, hn1, hn2⟩ := hR
  rw [h2_zero, sub_zero] at hcap
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
  have hlt : R.1 ≤ log 2 := hcap
  by_cases hbig : log 2 ≤ R.2.1 ∧ log 2 ≤ R.2.2
  · -- `R` already dominates the noiseless point, hence lies in `ℬ` itself
    exact subset_convexHull ℝ _ (regionB_mono top_mem_regionB_zero hlt hbig.1 hbig.2)
  · -- otherwise time-share, with weight `t / log 2` on the noiseless point
    set t : ℝ := min R.2.1 R.2.2 with ht
    have ht0 : 0 ≤ t := le_min hn1 hn2
    have hRt : R.1 ≤ t := le_min hd1 hd2
    have htlt : t < log 2 := by
      rcases not_and_or.mp hbig with h | h
      · exact lt_of_le_of_lt (min_le_left _ _) (lt_of_not_ge h)
      · exact lt_of_le_of_lt (min_le_right _ _) (lt_of_not_ge h)
    set lam : ℝ := t / log 2 with hlam
    have hlam0 : 0 ≤ lam := div_nonneg ht0 (le_of_lt hlog2)
    have hlam1 : lam < 1 := (div_lt_one hlog2).mpr htlt
    have hlt2 : lam * log 2 = t := by rw [hlam]; field_simp
    have hne : (1 : ℝ) - lam ≠ 0 := by linarith
    set Q : ℝ × ℝ × ℝ :=
      ((R.1 - lam * log 2) / (1 - lam), (R.2.1 - lam * log 2) / (1 - lam),
        (R.2.2 - lam * log 2) / (1 - lam)) with hQdef
    have hQ : Q ∈ regionB 0 := by
      refine regionB_mono origin_mem_regionB_zero ?_ ?_ ?_
      · exact div_nonpos_of_nonpos_of_nonneg (by rw [hlt2]; linarith) (by linarith)
      · exact div_nonneg (by rw [hlt2]; linarith [min_le_left R.2.1 R.2.2]) (by linarith)
      · exact div_nonneg (by rw [hlt2]; linarith [min_le_right R.2.1 R.2.2]) (by linarith)
    have hcomb : lam • ((log 2 : ℝ), (log 2 : ℝ), (log 2 : ℝ)) + (1 - lam) • Q = R := by
      have e1 : lam * log 2 + (1 - lam) * ((R.1 - lam * log 2) / (1 - lam)) = R.1 := by
        field_simp; ring
      have e2 : lam * log 2 + (1 - lam) * ((R.2.1 - lam * log 2) / (1 - lam)) = R.2.1 := by
        field_simp; ring
      have e3 : lam * log 2 + (1 - lam) * ((R.2.2 - lam * log 2) / (1 - lam)) = R.2.2 := by
        field_simp; ring
      simp only [hQdef, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, e1, e2, e3]
    exact segment_subset_convexHull top_mem_regionB_zero hQ
      ⟨lam, 1 - lam, hlam0, by linarith, by ring, hcomb⟩

theorem regionA_zero_subset_convexHull : regionA 0 ⊆ convexHull ℝ (regionB 0) :=
  fun _ hR => outerBound_zero_subset_convexHull (regionA_subset_outerBound le_rfl (by norm_num) hR)

/-- **The conjecture holds at `p = 0`** — although `𝒜 ≠ ℬ` there. -/
theorem averagedBSCConjecture_zero : AveragedBSCConjecture 0 :=
  (averagedBSCConjecture_iff le_rfl (by norm_num)).mpr regionA_zero_subset_convexHull

end BSCAveraging
