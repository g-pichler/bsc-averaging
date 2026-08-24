import BSCAveraging.KKT

/-! # `KKT` — exploration companion

The declarations of `BSCAveraging.KKT` that are **not** used by any of the
three theorems of `BSCAveraging.Basic`.  Section headers are copied from the
main file so the two read in parallel. -/

/-! # First-order conditions for the one-sided problem

`NOTES.md` §7c⁸.  Two elementary steps replace the Lagrange-multiplier
machinery that `Bitangency` was waiting for.  Note that `Chan` is a *binary*
channel, so the competitor set consists of **two-atom laws**: domination over
all of `[−1,1]` is neither what maximality gives nor what §7c⁗ needs.  What is
needed is stationarity, and that yields the four bitangency equations exactly.

* `kkt_of_directional` — pure linear algebra: if `∇V·d ≤ 0` for every direction
  with `∇R·d < 0`, and `∇R ≠ 0`, then `∇V = λ∇R` with `λ ≥ 0`.
* `le_zero_of_deriv_of_max` — the calculus input, via slopes: along a straight
  line on which `R` strictly decreases, feasibility is automatic for small
  `t > 0`, so the directional derivative of `V` is `≤ 0`.  **No implicit
  function theorem.**
* `bitangency_of_stationary` — the algebraic core: with the two-atom weights
  forced by mass and mean, stationarity in the atom positions says exactly that
  `η = φ − λψ` has both its derivatives equal to its own chord slope, i.e. the
  four bitangency equations.
-/

namespace BSCAveraging.KKT

open Filter Topology


/-! ### The two-atom family and its derivatives

With mass and mean fixed, the weights of a two-atom law are *determined* by the
atoms: `w₁ = −x₂/(x₁−x₂)`, `w₂ = x₁/(x₁−x₂)`.  So any linear functional
`μ ↦ ⟨φ,μ⟩` becomes the explicit function `twoAtomL φ` below, and its partial
derivatives are exactly the left-hand sides of `cleared_of_grad`. -/


lemma hasDerivAt_twoAtomL_fst {φ φ' : ℝ → ℝ} {x₁ x₂ : ℝ} (hx : x₂ < x₁)
    (hφ : HasDerivAt φ (φ' x₁) x₁) :
    HasDerivAt (twoAtomL φ x₂)
      ((x₂ / (x₁ - x₂) ^ 2) * (φ x₁ - φ x₂) + (-x₂ / (x₁ - x₂)) * φ' x₁) x₁ := by
  have hD : x₁ - x₂ ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hden : HasDerivAt (fun y : ℝ => y - x₂) 1 x₁ := by
    simpa using (hasDerivAt_id x₁).sub_const x₂
  have h1 : HasDerivAt (fun y : ℝ => -x₂ / (y - x₂)) (x₂ / (x₁ - x₂) ^ 2) x₁ := by
    have := ((hasDerivAt_const x₁ (-x₂)).div hden hD)
    refine hd_congr this ?_
    field_simp
    ring
  have h2 : HasDerivAt (fun y : ℝ => y / (y - x₂)) (-x₂ / (x₁ - x₂) ^ 2) x₁ := by
    have := ((hasDerivAt_id x₁).div hden hD)
    refine hd_congr this ?_
    simp only [id_eq]
    field_simp
    ring
  have := (h1.mul hφ).add (h2.mul_const (φ x₂))
  refine hd_congr this ?_
  field_simp
  ring

/-- `⟨φ, μ⟩` for the two-atom mean-zero law, as a function of the *second* atom. -/
noncomputable def twoAtomR (φ : ℝ → ℝ) (x₁ z : ℝ) : ℝ :=
  (-z / (x₁ - z)) * φ x₁ + (x₁ / (x₁ - z)) * φ z

lemma hasDerivAt_twoAtomR_snd {φ φ' : ℝ → ℝ} {x₁ x₂ : ℝ} (hx : x₂ < x₁)
    (hφ : HasDerivAt φ (φ' x₂) x₂) :
    HasDerivAt (twoAtomR φ x₁)
      ((x₁ / (x₁ - x₂) ^ 2) * (φ x₂ - φ x₁) + (x₁ / (x₁ - x₂)) * φ' x₂) x₂ := by
  have hD : x₁ - x₂ ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hden : HasDerivAt (fun z : ℝ => x₁ - z) (-1) x₂ := by
    simpa using (hasDerivAt_id x₂).const_sub x₁
  have h1 : HasDerivAt (fun z : ℝ => -z / (x₁ - z)) (-x₁ / (x₁ - x₂) ^ 2) x₂ := by
    have := (((hasDerivAt_id x₂).neg).div hden hD)
    refine hd_congr this ?_
    simp only [id_eq, Pi.neg_apply]
    field_simp
    ring
  have h2 : HasDerivAt (fun z : ℝ => x₁ / (x₁ - z)) (x₁ / (x₁ - x₂) ^ 2) x₂ := by
    have := ((hasDerivAt_const x₂ x₁).div hden hD)
    refine hd_congr this ?_
    field_simp
    ring
  have := (h1.mul_const (φ x₁)).add (h2.mul hφ)
  refine hd_congr this ?_
  field_simp
  ring

end BSCAveraging.KKT
