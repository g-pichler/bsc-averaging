import BSCAveraging.KernelCertFast
import BSCAveraging.KernelAlgebra

/-! # From the cleared certificate to the kernel lemma

`KernelCertFast.lean` proves `0 ≤ kerQR θ₁ θ₂ θ₃ u v`, the *cleared* kernel in
ordered bi-simplex coordinates.  Here we

* identify `kerQR` with `kernelSum · kernelDen`, the denominator being a product
  of manifestly positive factors (`kerQR_eq`);
* drop the ordering hypothesis, the sum being symmetric in the `θᵢ`;

proving the kernel lemma in its unordered form (`kernelSum_nonneg`).

The clearing identity is proved in **abstract letters** (`kernel_clear_abstract`,
twelve opaque variables): expanding it in `θ₁,θ₂,θ₃,u,v` would be a degree-21
polynomial identity, which `ring` cannot do in reasonable time, whereas in the
letters `Aᵢ,aᵢ,bᵢ,wᵢ` it is a few dozen monomials. -/

namespace BSCAveraging

open Reflect

/-- The kernel sum `Σ_i f(θ_i)(g(θ_j)+g(θ_k))(r_i² − r_j r_k)` of `KernelLemma`. -/
noncomputable def kernelSum (θ₁ θ₂ θ₃ u v : ℝ) : ℝ :=
  (1 - θ₁) / (1 - θ₁ * u)
      * ((1 - θ₂) / (1 - θ₂ * (u * v)) + (1 - θ₃) / (1 - θ₃ * (u * v)))
      * (((1 - θ₁ * u) / (1 - θ₁ * v)) ^ 2
          - (1 - θ₂ * u) / (1 - θ₂ * v) * ((1 - θ₃ * u) / (1 - θ₃ * v)))
    + (1 - θ₂) / (1 - θ₂ * u)
      * ((1 - θ₁) / (1 - θ₁ * (u * v)) + (1 - θ₃) / (1 - θ₃ * (u * v)))
      * (((1 - θ₂ * u) / (1 - θ₂ * v)) ^ 2
          - (1 - θ₁ * u) / (1 - θ₁ * v) * ((1 - θ₃ * u) / (1 - θ₃ * v)))
    + (1 - θ₃) / (1 - θ₃ * u)
      * ((1 - θ₁) / (1 - θ₁ * (u * v)) + (1 - θ₂) / (1 - θ₂ * (u * v)))
      * (((1 - θ₃ * u) / (1 - θ₃ * v)) ^ 2
          - (1 - θ₁ * u) / (1 - θ₁ * v) * ((1 - θ₂ * u) / (1 - θ₂ * v)))

/-- The cleared denominator `∏aᵢ·∏wᵢ·∏bᵢ²`. -/
noncomputable def kernelDen (θ₁ θ₂ θ₃ u v : ℝ) : ℝ :=
  (1 - θ₁ * u) * (1 - θ₂ * u) * (1 - θ₃ * u)
    * ((1 - θ₁ * (u * v)) * (1 - θ₂ * (u * v)) * (1 - θ₃ * (u * v)))
    * ((1 - θ₁ * v) ^ 2 * (1 - θ₂ * v) ^ 2 * (1 - θ₃ * v) ^ 2)

lemma one_sub_mul_pos {θ w : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (hw : 0 ≤ w) (hw' : w < 1) :
    0 < 1 - θ * w := by nlinarith

lemma kernelDen_pos {θ₁ θ₂ θ₃ u v : ℝ} (h₁ : 0 ≤ θ₁) (h₁' : θ₁ ≤ 1) (h₂ : 0 ≤ θ₂)
    (h₂' : θ₂ ≤ 1) (h₃ : 0 ≤ θ₃) (h₃' : θ₃ ≤ 1) (hv0 : 0 ≤ v) (hvu : v ≤ u) (hu1 : u < 1) :
    0 < kernelDen θ₁ θ₂ θ₃ u v := by
  have hu0 : 0 ≤ u := le_trans hv0 hvu
  have hv1 : v < 1 := lt_of_le_of_lt hvu hu1
  have huv0 : 0 ≤ u * v := mul_nonneg hu0 hv0
  have huv1 : u * v < 1 := by nlinarith
  have a₁ := one_sub_mul_pos h₁ h₁' hu0 hu1
  have a₂ := one_sub_mul_pos h₂ h₂' hu0 hu1
  have a₃ := one_sub_mul_pos h₃ h₃' hu0 hu1
  have w₁ := one_sub_mul_pos h₁ h₁' huv0 huv1
  have w₂ := one_sub_mul_pos h₂ h₂' huv0 huv1
  have w₃ := one_sub_mul_pos h₃ h₃' huv0 huv1
  have b₁ := one_sub_mul_pos h₁ h₁' hv0 hv1
  have b₂ := one_sub_mul_pos h₂ h₂' hv0 hv1
  have b₃ := one_sub_mul_pos h₃ h₃' hv0 hv1
  unfold kernelDen
  positivity

/-- The clearing identity in abstract letters. -/
lemma kernel_clear_abstract (A₁ A₂ A₃ a₁ a₂ a₃ b₁ b₂ b₃ w₁ w₂ w₃ : ℝ)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hb₃ : b₃ ≠ 0)
    (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) (hw₃ : w₃ ≠ 0) :
    A₁ * (a₂ * a₃) * (A₂ * (w₁ * w₃) + A₃ * (w₁ * w₂))
        * (a₁ ^ 2 * (b₂ ^ 2 * b₃ ^ 2) - a₂ * a₃ * (b₁ ^ 2 * (b₂ * b₃)))
      + A₂ * (a₃ * a₁) * (A₃ * (w₂ * w₁) + A₁ * (w₂ * w₃))
        * (a₂ ^ 2 * (b₃ ^ 2 * b₁ ^ 2) - a₃ * a₁ * (b₂ ^ 2 * (b₃ * b₁)))
      + A₃ * (a₁ * a₂) * (A₁ * (w₃ * w₂) + A₂ * (w₃ * w₁))
        * (a₃ ^ 2 * (b₁ ^ 2 * b₂ ^ 2) - a₁ * a₂ * (b₃ ^ 2 * (b₁ * b₂)))
      = (A₁ / a₁ * (A₂ / w₂ + A₃ / w₃) * ((a₁ / b₁) ^ 2 - a₂ / b₂ * (a₃ / b₃))
          + A₂ / a₂ * (A₁ / w₁ + A₃ / w₃) * ((a₂ / b₂) ^ 2 - a₁ / b₁ * (a₃ / b₃))
          + A₃ / a₃ * (A₁ / w₁ + A₂ / w₂) * ((a₃ / b₃) ^ 2 - a₁ / b₁ * (a₂ / b₂)))
        * (a₁ * a₂ * a₃ * (w₁ * w₂ * w₃) * (b₁ ^ 2 * b₂ ^ 2 * b₃ ^ 2)) := by
  field_simp
  ring

/-- `kerQR` is exactly the kernel sum times the positive denominator. -/
theorem kerQR_eq {θ₁ θ₂ θ₃ u v : ℝ}
    (ha₁ : 1 - θ₁ * u ≠ 0) (ha₂ : 1 - θ₂ * u ≠ 0) (ha₃ : 1 - θ₃ * u ≠ 0)
    (hb₁ : 1 - θ₁ * v ≠ 0) (hb₂ : 1 - θ₂ * v ≠ 0) (hb₃ : 1 - θ₃ * v ≠ 0)
    (hw₁ : 1 - θ₁ * (u * v) ≠ 0) (hw₂ : 1 - θ₂ * (u * v) ≠ 0) (hw₃ : 1 - θ₃ * (u * v) ≠ 0) :
    kerQR θ₁ θ₂ θ₃ u v = kernelSum θ₁ θ₂ θ₃ u v * kernelDen θ₁ θ₂ θ₃ u v := by
  have hT : θ₁ + (θ₂ - θ₁) + ((θ₃ - θ₂) + (1 - θ₃)) = 1 := by ring
  have hS : v + ((u - v) + (1 - u)) = 1 := by ring
  have hU : v + (u - v) = u := by ring
  have hΘ₂ : θ₁ + (θ₂ - θ₁) = θ₂ := by ring
  have hΘ₃ : θ₂ + (θ₃ - θ₂) = θ₃ := by ring
  rw [kerQR, eval_kerQPE]
  simp only [Matrix.cons_val]
  simp only [hT, hS]
  simp only [hΘ₂, hΘ₃, hU, one_pow, mul_one]
  rw [kernelSum, kernelDen]
  exact kernel_clear_abstract (1 - θ₁) (1 - θ₂) (1 - θ₃) (1 - θ₁ * u) (1 - θ₂ * u)
    (1 - θ₃ * u) (1 - θ₁ * v) (1 - θ₂ * v) (1 - θ₃ * v) (1 - θ₁ * (u * v))
    (1 - θ₂ * (u * v)) (1 - θ₃ * (u * v)) ha₁ ha₂ ha₃ hb₁ hb₂ hb₃ hw₁ hw₂ hw₃

/-- The kernel sum, for **ordered** `θ`s. -/
theorem kernelSum_nonneg_ordered {θ₁ θ₂ θ₃ u v : ℝ} (h0 : 0 ≤ θ₁) (h12 : θ₁ ≤ θ₂)
    (h23 : θ₂ ≤ θ₃) (h31 : θ₃ ≤ 1) (hv0 : 0 ≤ v) (hvu : v ≤ u) (hu1 : u < 1) :
    0 ≤ kernelSum θ₁ θ₂ θ₃ u v := by
  have h₁ : 0 ≤ θ₁ := h0
  have h₂ : 0 ≤ θ₂ := le_trans h0 h12
  have h₃ : 0 ≤ θ₃ := le_trans h₂ h23
  have h₁' : θ₁ ≤ 1 := le_trans (le_trans h12 h23) h31
  have h₂' : θ₂ ≤ 1 := le_trans h23 h31
  have hu0 : 0 ≤ u := le_trans hv0 hvu
  have hv1 : v < 1 := lt_of_le_of_lt hvu hu1
  have huv0 : 0 ≤ u * v := mul_nonneg hu0 hv0
  have huv1 : u * v < 1 := by nlinarith
  have hden := kernelDen_pos h₁ h₁' h₂ h₂' h₃ h31 hv0 hvu hu1
  have hQ := kerQR_nonneg h0 h12 h23 h31 hv0 hvu (le_of_lt hu1)
  rw [kerQR_eq (ne_of_gt (one_sub_mul_pos h₁ h₁' hu0 hu1))
      (ne_of_gt (one_sub_mul_pos h₂ h₂' hu0 hu1))
      (ne_of_gt (one_sub_mul_pos h₃ h31 hu0 hu1))
      (ne_of_gt (one_sub_mul_pos h₁ h₁' hv0 hv1))
      (ne_of_gt (one_sub_mul_pos h₂ h₂' hv0 hv1))
      (ne_of_gt (one_sub_mul_pos h₃ h31 hv0 hv1))
      (ne_of_gt (one_sub_mul_pos h₁ h₁' huv0 huv1))
      (ne_of_gt (one_sub_mul_pos h₂ h₂' huv0 huv1))
      (ne_of_gt (one_sub_mul_pos h₃ h31 huv0 huv1))] at hQ
  exact (mul_nonneg_iff_of_pos_right hden).mp hQ

/-- The kernel sum is symmetric in the `θᵢ`. -/
lemma kernelSum_swap₁₂ (θ₁ θ₂ θ₃ u v : ℝ) :
    kernelSum θ₁ θ₂ θ₃ u v = kernelSum θ₂ θ₁ θ₃ u v := by
  rw [kernelSum, kernelSum]; ring

lemma kernelSum_swap₂₃ (θ₁ θ₂ θ₃ u v : ℝ) :
    kernelSum θ₁ θ₂ θ₃ u v = kernelSum θ₁ θ₃ θ₂ u v := by
  rw [kernelSum, kernelSum]; ring

/-- **The kernel lemma**, with the ordering hypothesis removed. -/
theorem kernelSum_nonneg {θ₁ θ₂ θ₃ u v : ℝ} (h₁ : 0 ≤ θ₁) (h₁' : θ₁ ≤ 1)
    (h₂ : 0 ≤ θ₂) (h₂' : θ₂ ≤ 1) (h₃ : 0 ≤ θ₃) (h₃' : θ₃ ≤ 1)
    (hv0 : 0 ≤ v) (hvu : v ≤ u) (hu1 : u < 1) :
    0 ≤ kernelSum θ₁ θ₂ θ₃ u v := by
  rcases le_total θ₁ θ₂ with h12 | h12 <;> rcases le_total θ₂ θ₃ with h23 | h23 <;>
    rcases le_total θ₁ θ₃ with h13 | h13
  · exact kernelSum_nonneg_ordered h₁ h12 h23 h₃' hv0 hvu hu1
  · exact kernelSum_nonneg_ordered h₁ h12 h23 h₃' hv0 hvu hu1
  · rw [kernelSum_swap₂₃]
    exact kernelSum_nonneg_ordered h₁ h13 h23 h₂' hv0 hvu hu1
  · rw [kernelSum_swap₂₃, kernelSum_swap₁₂]
    exact kernelSum_nonneg_ordered h₃ h13 h12 h₂' hv0 hvu hu1
  · rw [kernelSum_swap₁₂]
    exact kernelSum_nonneg_ordered h₂ h12 h13 h₃' hv0 hvu hu1
  · rw [kernelSum_swap₁₂, kernelSum_swap₂₃]
    exact kernelSum_nonneg_ordered h₂ h23 h13 h₁' hv0 hvu hu1
  · rw [kernelSum_swap₁₂, kernelSum_swap₂₃]
    exact kernelSum_nonneg_ordered h₂ (by linarith) (by linarith) h₁' hv0 hvu hu1
  · rw [kernelSum_swap₂₃, kernelSum_swap₁₂, kernelSum_swap₂₃]
    exact kernelSum_nonneg_ordered h₃ h23 h12 h₁' hv0 hvu hu1


end BSCAveraging
