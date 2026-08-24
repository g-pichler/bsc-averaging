import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

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

lemma hd_congr {f : ℝ → ℝ} {d d' x : ℝ} (h : HasDerivAt f d x) (he : d = d') :
    HasDerivAt f d' x := he ▸ h

/-- Along a ray, a positive derivative gives strict increase. -/
lemma eventually_gt_of_deriv_pos {f : ℝ → ℝ} {a : ℝ} (h : HasDerivAt f a 0) (ha : 0 < a) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), f 0 < f t := by
  have hs := hasDerivAt_iff_tendsto_slope.mp h
  have hev : ∀ᶠ t in 𝓝[≠] (0:ℝ), 0 < slope f 0 t := hs (eventually_gt_nhds ha)
  have hle : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] (0:ℝ) := nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
  filter_upwards [hle hev, self_mem_nhdsWithin] with t ht htpos
  rw [slope_def_field, div_pos_iff] at ht
  rcases ht with ⟨h1, _⟩ | ⟨_, h2⟩
  · linarith
  · exact absurd (by simpa using htpos : (0:ℝ) < t) (by simpa using not_lt.mpr (by linarith))

/-- Along a ray, a negative derivative gives strict decrease. -/
lemma eventually_lt_of_deriv_neg {f : ℝ → ℝ} {a : ℝ} (h : HasDerivAt f a 0) (ha : a < 0) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), f t < f 0 := by
  have h' : HasDerivAt (fun t => -f t) (-a) 0 := h.neg
  have := eventually_gt_of_deriv_pos h' (by linarith)
  filter_upwards [this] with t ht
  linarith

/-- **The calculus input.**  If `V` cannot beat `V 0` at feasible nearby points
and `R` strictly decreases along the ray, the derivative of `V` is `≤ 0`. -/
theorem le_zero_of_deriv_of_max {V R : ℝ → ℝ} {a b : ℝ}
    (hV : HasDerivAt V a 0) (hR : HasDerivAt R b 0) (hb : b < 0)
    (hmax : ∀ᶠ t in 𝓝[>] (0:ℝ), R t ≤ R 0 → V t ≤ V 0) : a ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  have h1 := eventually_gt_of_deriv_pos hV hpos
  have h2 := eventually_lt_of_deriv_neg hR hb
  obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := ((h1.and h2).and hmax).exists
  exact absurd (ht3 (le_of_lt ht2)) (not_le.mpr ht1)

/-- The mirror for a **minimiser**: along a direction in which the rate strictly
increases, the value cannot decrease. -/
theorem le_zero_of_deriv_of_min {V R : ℝ → ℝ} {a b : ℝ}
    (hV : HasDerivAt V a 0) (hR : HasDerivAt R b 0) (hb : 0 < b)
    (hmin : ∀ᶠ t in 𝓝[>] (0:ℝ), R 0 ≤ R t → V 0 ≤ V t) : 0 ≤ a := by
  by_contra hneg
  push_neg at hneg
  have h1 := eventually_lt_of_deriv_neg hV hneg
  have h2 := eventually_gt_of_deriv_pos hR hb
  obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := ((h1.and h2).and hmin).exists
  exact absurd (ht3 (le_of_lt ht2)) (not_le.mpr ht1)

/-- **Two-dimensional KKT**, as linear algebra. -/
theorem kkt_of_directional {va vb ra rb : ℝ} (hne : ¬ (ra = 0 ∧ rb = 0))
    (hline : ∀ d₁ d₂ : ℝ, ra * d₁ + rb * d₂ < 0 → va * d₁ + vb * d₂ ≤ 0) :
    ∃ lam : ℝ, 0 ≤ lam ∧ va = lam * ra ∧ vb = lam * rb := by
  have hsq : (0:ℝ) < ra ^ 2 + rb ^ 2 := by
    rcases not_and_or.mp hne with h | h
    · have : 0 < ra ^ 2 := by positivity
      nlinarith [sq_nonneg rb]
    · have : 0 < rb ^ 2 := by positivity
      nlinarith [sq_nonneg ra]
  -- `λ ≥ 0` from the direction `−∇R`
  have hC : 0 ≤ va * ra + vb * rb := by
    have := hline (-ra) (-rb) (by nlinarith)
    nlinarith [this]
  -- the orthogonal direction, perturbed
  have hkey : ∀ ε : ℝ, 0 < ε → va * (-rb) + vb * ra ≤ ε * (va * ra + vb * rb) := by
    intro ε hε
    have := hline (-rb - ε * ra) (ra - ε * rb) (by nlinarith)
    nlinarith [this]
  have hkey' : ∀ ε : ℝ, 0 < ε → -(va * (-rb) + vb * ra) ≤ ε * (va * ra + vb * rb) := by
    intro ε hε
    have := hline (rb - ε * ra) (-ra - ε * rb) (by nlinarith)
    nlinarith [this]
  have hsmall : ∀ X : ℝ, (∀ ε : ℝ, 0 < ε → X ≤ ε * (va * ra + vb * rb)) → X ≤ 0 := by
    intro X hX
    by_contra hc
    push_neg at hc
    have hden : (0:ℝ) < 2 * (va * ra + vb * rb) + 2 := by linarith
    have := hX (X / (2 * (va * ra + vb * rb) + 2)) (by positivity)
    rw [div_mul_eq_mul_div, le_div_iff₀ hden] at this
    nlinarith [this]
  have h1 := hsmall _ hkey
  have h2 := hsmall _ hkey'
  have horth : va * (-rb) + vb * ra = 0 := by linarith
  refine ⟨(va * ra + vb * rb) / (ra ^ 2 + rb ^ 2), div_nonneg hC (le_of_lt hsq), ?_, ?_⟩
  · rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hsq)]
    linear_combination (-rb) * horth
  · rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hsq)]
    linear_combination ra * horth

/-- **Stationarity is bitangency.**  `η = φ − λψ` has both derivatives equal to
its own chord slope, so an affine function matches `φ − λψ` in value and slope
at both atoms. -/
theorem bitangency_of_stationary {φ ψ φ' ψ' : ℝ → ℝ} {x₁ x₂ lam : ℝ} (hx : x₂ < x₁)
    (hA : (φ x₁ - φ x₂) - (x₁ - x₂) * φ' x₁
        = lam * ((ψ x₁ - ψ x₂) - (x₁ - x₂) * ψ' x₁))
    (hB : (φ x₁ - φ x₂) - (x₁ - x₂) * φ' x₂
        = lam * ((ψ x₁ - ψ x₂) - (x₁ - x₂) * ψ' x₂)) :
    ∃ l₀ l₁ : ℝ,
      φ x₁ = l₀ + l₁ * x₁ + lam * ψ x₁ ∧ φ x₂ = l₀ + l₁ * x₂ + lam * ψ x₂ ∧
      φ' x₁ = l₁ + lam * ψ' x₁ ∧ φ' x₂ = l₁ + lam * ψ' x₂ := by
  have hD : x₁ - x₂ ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  set l₁ := ((φ x₁ - lam * ψ x₁) - (φ x₂ - lam * ψ x₂)) / (x₁ - x₂) with hl₁
  refine ⟨φ x₁ - lam * ψ x₁ - l₁ * x₁, l₁, by ring, ?_, ?_, ?_⟩
  · rw [hl₁]; field_simp; ring
  · rw [hl₁]; field_simp; linarith [hA]
  · rw [hl₁]; field_simp; linarith [hB]

/-- Clearing the raw stationarity equations (weights `−x₂/(x₁−x₂)`,
`x₁/(x₁−x₂)`) into the form `bitangency_of_stationary` consumes. -/
theorem cleared_of_grad {φ ψ φ' ψ' : ℝ → ℝ} {x₁ x₂ lam : ℝ} (hx : x₂ < x₁)
    (hx1 : x₁ ≠ 0) (hx2 : x₂ ≠ 0)
    (hA : (x₂ / (x₁ - x₂) ^ 2) * (φ x₁ - φ x₂) + (-x₂ / (x₁ - x₂)) * φ' x₁
        = lam * ((x₂ / (x₁ - x₂) ^ 2) * (ψ x₁ - ψ x₂) + (-x₂ / (x₁ - x₂)) * ψ' x₁))
    (hB : (x₁ / (x₁ - x₂) ^ 2) * (φ x₂ - φ x₁) + (x₁ / (x₁ - x₂)) * φ' x₂
        = lam * ((x₁ / (x₁ - x₂) ^ 2) * (ψ x₂ - ψ x₁) + (x₁ / (x₁ - x₂)) * ψ' x₂)) :
    (φ x₁ - φ x₂) - (x₁ - x₂) * φ' x₁
        = lam * ((ψ x₁ - ψ x₂) - (x₁ - x₂) * ψ' x₁)
      ∧ (φ x₁ - φ x₂) - (x₁ - x₂) * φ' x₂
        = lam * ((ψ x₁ - ψ x₂) - (x₁ - x₂) * ψ' x₂) := by
  have hD : x₁ - x₂ ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  constructor
  · field_simp at hA
    field_simp
    nlinarith [hA]
  · field_simp at hB
    field_simp
    nlinarith [hB]

/-! ### The two-atom family and its derivatives

With mass and mean fixed, the weights of a two-atom law are *determined* by the
atoms: `w₁ = −x₂/(x₁−x₂)`, `w₂ = x₁/(x₁−x₂)`.  So any linear functional
`μ ↦ ⟨φ,μ⟩` becomes the explicit function `twoAtomL φ` below, and its partial
derivatives are exactly the left-hand sides of `cleared_of_grad`. -/

/-- `⟨φ, μ⟩` for the two-atom mean-zero law with atoms `y` and `x₂`. -/
noncomputable def twoAtomL (φ : ℝ → ℝ) (x₂ y : ℝ) : ℝ :=
  (-x₂ / (y - x₂)) * φ y + (y / (y - x₂)) * φ x₂




end BSCAveraging.KKT
