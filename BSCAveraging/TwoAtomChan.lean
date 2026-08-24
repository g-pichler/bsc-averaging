import BSCAveraging.Conj12
import BSCAveraging.KKT

/-! # The two-atom channel family, and value/rate as `twoAtomL`

`NOTES.md` §7c⁹.  This is the plumbing both `(B)` and `(C)` were waiting on.

At `p = 0` the `U`-side marginal on `X` is uniform, so *every* binary channel
has mean-zero biases (`pi_bias_sum_zero`).  With mass one that **forces** the
weights from the atoms,

```
π_true = −s_false/(s_true − s_false),      π_false = s_true/(s_true − s_false),
```

so both the rate and the value are the explicit one-variable functions
`twoAtomL f_e` and `twoAtomL (atomValue cR)` of the positive atom.  Conversely
`chanOfAtoms` realises any admissible atom pair as a `Chan`. -/

namespace BSCAveraging

open BSCAveraging.KKT

/-! ### Weights are forced -/

/-- Mass one and mean zero determine the two-atom weights. -/
theorem weights_of_mass_mean {w₁ w₂ x₁ x₂ : ℝ} (hne : x₁ ≠ x₂)
    (hsum : w₁ + w₂ = 1) (hmz : w₁ * x₁ + w₂ * x₂ = 0) :
    w₁ = -x₂ / (x₁ - x₂) ∧ w₂ = x₁ / (x₁ - x₂) := by
  have hD : x₁ - x₂ ≠ 0 := sub_ne_zero_of_ne hne
  constructor
  · field_simp
    linear_combination hmz - x₂ * hsum
  · field_simp
    linear_combination (-1 : ℝ) * hmz + x₁ * hsum

/-! ### Step 2: the rate and the value as `twoAtomL` -/

/-- **The rate is `twoAtomL f_e`.** -/
theorem mutualInfo_jointUX_eq_twoAtomL {cL : Chan}
    (hpos : ∀ u, 0 < marg₁ (jointUX cL) u)
    (hne : biasOf (jointUX cL) true ≠ biasOf (jointUX cL) false) :
    mutualInfo (jointUX cL)
      = twoAtomL fe (biasOf (jointUX cL) false) (biasOf (jointUX cL) true) := by
  have hsum : marg₁ (jointUX cL) true + marg₁ (jointUX cL) false = 1 := by
    have := marg₁_jointUX_sum cL; linarith
  have hmz : marg₁ (jointUX cL) true * biasOf (jointUX cL) true
      + marg₁ (jointUX cL) false * biasOf (jointUX cL) false = 0 := by
    have := pi_bias_sum_zero cL (hpos false) (hpos true); linarith
  obtain ⟨e1, e2⟩ := weights_of_mass_mean hne hsum hmz
  rw [mutualInfo_jointUX_eq_bias_closed hpos, twoAtomL, e1, e2]
  ring

/-- **The value is `twoAtomL (atomValue cR)`.** -/
theorem mutualInfo_jointUV_eq_twoAtomL {cL cR : Chan}
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hker : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u
      * biasOfSnd (jointYV cR) v)
    (hne : biasOf (jointUX cL) true ≠ biasOf (jointUX cL) false) :
    mutualInfo (jointUV 0 cL cR)
      = twoAtomL (atomValue cR) (biasOf (jointUX cL) false) (biasOf (jointUX cL) true) := by
  have hsum : marg₁ (jointUX cL) true + marg₁ (jointUX cL) false = 1 := by
    have := marg₁_jointUX_sum cL; linarith
  have hmz : marg₁ (jointUX cL) true * biasOf (jointUX cL) true
      + marg₁ (jointUX cL) false * biasOf (jointUX cL) false = 0 := by
    have := pi_bias_sum_zero cL (hpi false) (hpi true); linarith
  obtain ⟨e1, e2⟩ := weights_of_mass_mean hne hsum hmz
  rw [mutualInfo_jointUV_eq_kernel_sum_of_nonneg 0 cL cR hpi hrho hker, twoAtomL,
    atomValue, atomValue, e1, e2]
  ring_nf

/-! ### Step 1: realising an atom pair as a channel -/

section OfAtoms

variable {a b : ℝ}

/-- The forced weight of the positive atom. -/
noncomputable def wOf (a b : ℝ) : ℝ := -b / (a - b)

lemma wOf_pos (ha0 : 0 < a) (hb0 : b < 0) : 0 < wOf a b := by
  unfold wOf; apply div_pos (by linarith) (by linarith)

lemma wOf_lt_one (ha0 : 0 < a) (hb0 : b < 0) : wOf a b < 1 := by
  unfold wOf
  rw [div_lt_one (by linarith)]
  linarith

lemma chanOfAtoms_bounds (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0) (hb1 : -1 < b) :
    0 ≤ wOf a b * (1 + a) ∧ wOf a b * (1 + a) ≤ 1 ∧
    0 ≤ wOf a b * (1 - a) ∧ wOf a b * (1 - a) ≤ 1 := by
  have hw0 := wOf_pos ha0 hb0
  have hD : (0:ℝ) < a - b := by linarith
  have hwe : wOf a b = -b / (a - b) := rfl
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · rw [hwe, div_mul_eq_mul_div, div_le_one hD]
    nlinarith
  · rw [hwe, div_mul_eq_mul_div, div_le_one hD]
    nlinarith

/-- **The channel with prescribed atoms.**  Realises the two-atom mean-zero law
with biases `a > 0 > b`. -/
noncomputable def chanOfAtoms (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0) (hb1 : -1 < b) :
    Chan :=
  chanOf (wOf a b * (1 + a)) (wOf a b * (1 - a))
    (chanOfAtoms_bounds ha0 ha1 hb0 hb1).1
    (chanOfAtoms_bounds ha0 ha1 hb0 hb1).2.1
    (chanOfAtoms_bounds ha0 ha1 hb0 hb1).2.2.1
    (chanOfAtoms_bounds ha0 ha1 hb0 hb1).2.2.2

lemma marg₁_chanOfAtoms (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0) (hb1 : -1 < b) :
    marg₁ (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) true = wOf a b ∧
      marg₁ (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) false = 1 - wOf a b := by
  constructor <;>
    · simp only [marg₁, jointUX, chanOfAtoms, chanOf, chanTr, cond_true, cond_false]
      ring

lemma biasOf_chanOfAtoms (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0) (hb1 : -1 < b) :
    biasOf (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) true = a ∧
      biasOf (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) false = b := by
  have hw0 := wOf_pos ha0 hb0
  have hw1 := wOf_lt_one ha0 hb0
  obtain ⟨m1, m0⟩ := marg₁_chanOfAtoms ha0 ha1 hb0 hb1
  have hD : (0:ℝ) < a - b := by linarith
  have hwe : wOf a b = -b / (a - b) := rfl
  constructor
  · rw [biasOf, m1]
    simp only [jointUX, chanOfAtoms, chanOf, chanTr, cond_true, cond_false]
    field_simp
    ring
  · rw [biasOf, m0]
    simp only [jointUX, chanOfAtoms, chanOf, chanTr, cond_true, cond_false]
    rw [hwe]
    have h1 : (1:ℝ) - -b / (a - b) = a / (a - b) := by field_simp; ring
    rw [h1]
    field_simp
    ring

lemma marg₁_chanOfAtoms_pos (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0) (hb1 : -1 < b) :
    ∀ u, 0 < marg₁ (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) u := by
  obtain ⟨m1, m0⟩ := marg₁_chanOfAtoms ha0 ha1 hb0 hb1
  intro u
  cases u
  · rw [m0]; linarith [wOf_lt_one ha0 hb0]
  · rw [m1]; exact wOf_pos ha0 hb0

/-- **The payoff.**  Along the atom family, the rate and the value are literally
the one-variable functions `twoAtomL f_e` and `twoAtomL (atomValue cR)` of the
positive atom — whose derivatives are `hasDerivAt_twoAtomL_fst`. -/
theorem rate_chanOfAtoms (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0) (hb1 : -1 < b) :
    mutualInfo (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) = twoAtomL fe b a := by
  obtain ⟨e1, e0⟩ := biasOf_chanOfAtoms ha0 ha1 hb0 hb1
  have hne : biasOf (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) true
      ≠ biasOf (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) false := by
    rw [e1, e0]; intro h; linarith
  rw [mutualInfo_jointUX_eq_twoAtomL (marg₁_chanOfAtoms_pos ha0 ha1 hb0 hb1) hne, e1, e0]

theorem value_chanOfAtoms {cR : Chan} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0)
    (hb1 : -1 < b) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hker : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ))
      * biasOf (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) u * biasOfSnd (jointYV cR) v) :
    mutualInfo (jointUV 0 (chanOfAtoms ha0 ha1 hb0 hb1) cR)
      = twoAtomL (atomValue cR) b a := by
  obtain ⟨e1, e0⟩ := biasOf_chanOfAtoms ha0 ha1 hb0 hb1
  have hne : biasOf (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) true
      ≠ biasOf (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) false := by
    rw [e1, e0]; intro h; linarith
  rw [mutualInfo_jointUV_eq_twoAtomL (marg₁_chanOfAtoms_pos ha0 ha1 hb0 hb1) hrho hker hne,
    e1, e0]

end OfAtoms

end BSCAveraging
