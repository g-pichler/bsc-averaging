import BSCAveraging.Conj12
import BSCAveraging.LogCosh

/-! # From `Chan`-level bitangency to the `θ`-coordinate form

`NOTES.md` §7c⁶/§7c⁷.  `LogCosh.lean` proves the analysis of `(B)` in the
`θ = artanh` coordinates, for the slack `Dsl` and the atom value `Gval`.  This
file is the translation layer:

* `fe_tanh` — `f_e(tanh σ) = σ tanh σ − L(σ)`;
* `weights_of_mean_zero` — the mean-zero condition *forces* the two-atom weights
  to be `sinh δ cosh γ/sinh(γ+δ)` and `sinh γ cosh δ/sinh(γ+δ)`;
* `atomValue_eq_Gval` — hence the `Chan`-level atom value is `Gval`;
* `Dsl_eq_slack` — hence the `Chan`-level slack is `Dsl`.

What is still missing for `(B)` is only `Bitangency` itself (Lagrange
multipliers for the one-sided linear program). -/

namespace BSCAveraging

open Real BSCAveraging.LC

/-- `f_e(tanh σ) = σ·tanh σ − log cosh σ`. -/
theorem fe_tanh (σ : ℝ) : fe (Real.tanh σ) = σ * Real.tanh σ - LC σ := by
  have hc : (0:ℝ) < Real.cosh σ := Real.cosh_pos σ
  have h1 : 1 + Real.tanh σ = Real.exp σ / Real.cosh σ := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    field_simp
    ring
  have h2 : 1 - Real.tanh σ = Real.exp (-σ) / Real.cosh σ := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    field_simp
    ring
  have hp : (0:ℝ) < Real.exp σ / Real.cosh σ := by positivity
  have hm : (0:ℝ) < Real.exp (-σ) / Real.cosh σ := by positivity
  rw [fe, h1, h2, Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hc),
    Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hc), Real.log_exp, Real.log_exp, LC]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  linear_combination (-2 * σ) * Real.sinh_eq σ
    + (2 * Real.log (Real.cosh σ)) * Real.cosh_eq σ

/-- The mean-zero condition forces the two-atom weights. -/
theorem weights_of_mean_zero {ρ₀ ρ₁ γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (hsum : ρ₀ + ρ₁ = 1) (hmz : ρ₀ * Real.tanh γ + ρ₁ * -Real.tanh δ = 0) :
    ρ₀ = Real.sinh δ * Real.cosh γ / Real.sinh (γ + δ)
      ∧ ρ₁ = Real.sinh γ * Real.cosh δ / Real.sinh (γ + δ) := by
  have hcγ : (0:ℝ) < Real.cosh γ := Real.cosh_pos γ
  have hcδ : (0:ℝ) < Real.cosh δ := Real.cosh_pos δ
  have hsγ : 0 < Real.sinh γ := Real.sinh_pos_iff.mpr hγ
  have hsδ : 0 < Real.sinh δ := Real.sinh_pos_iff.mpr hδ
  have hS : Real.sinh (γ + δ) = Real.sinh γ * Real.cosh δ + Real.cosh γ * Real.sinh δ :=
    Real.sinh_add γ δ
  have hSpos : 0 < Real.sinh (γ + δ) := by rw [hS]; positivity
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh] at hmz
  have hρ₁ : ρ₁ = 1 - ρ₀ := by linarith
  subst hρ₁
  constructor
  · field_simp at hmz
    rw [hS]
    field_simp
    nlinarith [hmz]
  · field_simp at hmz
    rw [hS]
    field_simp
    nlinarith [hmz]

/-- The `Chan`-level atom value is `Gval` in `θ` coordinates. -/
theorem atomValue_eq_Gval {cR : Chan} {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (hf : 0 < marg₂ (jointYV cR) false) (ht : 0 < marg₂ (jointYV cR) true)
    (h0 : biasOfSnd (jointYV cR) false = Real.tanh γ)
    (h1 : biasOfSnd (jointYV cR) true = -Real.tanh δ) (σ : ℝ) :
    atomValue cR (Real.tanh σ) = Gval γ δ σ := by
  have hsum := marg₂_jointYV_sum cR
  have hmz := rho_bias_sum_zero cR hf ht
  rw [h0, h1] at hmz
  obtain ⟨e0, e1⟩ := weights_of_mean_zero hγ hδ hsum hmz
  rw [atomValue, h0, h1, e0, e1, Gval, fFun, fFun, fF, fF]
  ring_nf

/-- The `Chan`-level slack is `Dsl` in `θ` coordinates. -/
theorem Dsl_eq_slack {cR : Chan} {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (hf : 0 < marg₂ (jointYV cR) false) (ht : 0 < marg₂ (jointYV cR) true)
    (h0 : biasOfSnd (jointYV cR) false = Real.tanh γ)
    (h1 : biasOfSnd (jointYV cR) true = -Real.tanh δ) (l₀ l₁ l₂ σ : ℝ) :
    l₀ + l₁ * Real.tanh σ + l₂ * fe (Real.tanh σ) - atomValue cR (Real.tanh σ)
      = Dsl l₀ l₁ l₂ γ δ σ := by
  rw [fe_tanh, atomValue_eq_Gval hγ hδ hf ht h0 h1, Dsl]

end BSCAveraging
