import BSCAveraging.Exploration.KernelCertBern
import BSCAveraging.KernelBridge

/-! # The bridge to the `(y, A, B)` coordinates

`KernelCertBern.lean` certifies the cleared kernel in the coordinates of
`NOTES.md` §7j.  This file connects that certificate to `kernelSum`, so that the
smaller tree can replace the one in `KernelCertFast.lean`.

The substitution is
```
y_i = θ_i/(1−θ_i) ,  z₁ = y₁ , z₂ = y₂−y₁ , z₃ = y₃−y₂ ,
s = 1−v ,  s' = v ,  w = (u−v)/(1−v) ,  w' = (1−u)/(1−v) ,
```
chosen so that both units evaluate to `1` and the tree's factors become

```
F̂_i = 1 + y_i(1−u) = (1−θ_iu)/(1−θ_i) ,
Ĝ_i = 1 + y_i(1−uv) = (1−θ_iuv)/(1−θ_i) ,
Ĥ_i = 1 + y_i(1−v) = (1−θ_iv)/(1−θ_i) ,
```
with no scaling factor left over.  Then `f_i = 1/F̂_i`, `g_i = 1/Ĝ_i` and
`r_i = F̂_i/Ĥ_i`, and the clearing identity is the same abstract-letters
computation as in `KernelBridge.lean`, in nine letters instead of twelve. -/

namespace BSCAveraging.Reflect

open BSCAveraging

/-- The clearing identity, in abstract letters. -/
lemma clearB_abstract (F₁ F₂ F₃ G₁ G₂ G₃ H₁ H₂ H₃ : ℝ)
    (hF₁ : F₁ ≠ 0) (hF₂ : F₂ ≠ 0) (hF₃ : F₃ ≠ 0)
    (hG₁ : G₁ ≠ 0) (hG₂ : G₂ ≠ 0) (hG₃ : G₃ ≠ 0)
    (hH₁ : H₁ ≠ 0) (hH₂ : H₂ ≠ 0) (hH₃ : H₃ ≠ 0) :
    F₂ * F₃ * (G₁ * (G₂ + G₃)) * (H₂ * H₃ * (F₁ ^ 2 * H₂ * H₃ - F₂ * F₃ * H₁ ^ 2))
      + F₃ * F₁ * (G₂ * (G₃ + G₁)) * (H₃ * H₁ * (F₂ ^ 2 * H₃ * H₁ - F₃ * F₁ * H₂ ^ 2))
      + F₁ * F₂ * (G₃ * (G₁ + G₂)) * (H₁ * H₂ * (F₃ ^ 2 * H₁ * H₂ - F₁ * F₂ * H₃ ^ 2))
      = (1 / F₁ * (1 / G₂ + 1 / G₃) * ((F₁ / H₁) ^ 2 - F₂ / H₂ * (F₃ / H₃))
          + 1 / F₂ * (1 / G₁ + 1 / G₃) * ((F₂ / H₂) ^ 2 - F₁ / H₁ * (F₃ / H₃))
          + 1 / F₃ * (1 / G₁ + 1 / G₂) * ((F₃ / H₃) ^ 2 - F₁ / H₁ * (F₂ / H₂)))
        * (F₁ * F₂ * F₃ * (G₁ * G₂ * G₃) * (H₁ ^ 2 * H₂ ^ 2 * H₃ ^ 2)) := by
  field_simp
  ring

/-- The three hatted terms sum to the kernel times the cleared denominator. -/
lemma termB_sum_eq {θ₁ θ₂ θ₃ u v : ℝ}
    (hd₁ : (1:ℝ) - θ₁ ≠ 0) (hd₂ : (1:ℝ) - θ₂ ≠ 0) (hd₃ : (1:ℝ) - θ₃ ≠ 0)
    (ha₁ : (1:ℝ) - θ₁ * u ≠ 0) (ha₂ : (1:ℝ) - θ₂ * u ≠ 0) (ha₃ : (1:ℝ) - θ₃ * u ≠ 0)
    (hb₁ : (1:ℝ) - θ₁ * v ≠ 0) (hb₂ : (1:ℝ) - θ₂ * v ≠ 0) (hb₃ : (1:ℝ) - θ₃ * v ≠ 0)
    (hw₁ : (1:ℝ) - θ₁ * (u * v) ≠ 0) (hw₂ : (1:ℝ) - θ₂ * (u * v) ≠ 0)
    (hw₃ : (1:ℝ) - θ₃ * (u * v) ≠ 0) :
    termB (yOf θ₁) (yOf θ₂) (yOf θ₃) u v + termB (yOf θ₂) (yOf θ₃) (yOf θ₁) u v
        + termB (yOf θ₃) (yOf θ₁) (yOf θ₂) u v
      = kernelSum θ₁ θ₂ θ₃ u v
        * (FB (yOf θ₁) u * FB (yOf θ₂) u * FB (yOf θ₃) u
            * (GB (yOf θ₁) u v * GB (yOf θ₂) u v * GB (yOf θ₃) u v)
            * (HB (yOf θ₁) v ^ 2 * HB (yOf θ₂) v ^ 2 * HB (yOf θ₃) v ^ 2)) := by
  have nF₁ : FB (yOf θ₁) u ≠ 0 := by rw [FB_yOf hd₁]; exact div_ne_zero ha₁ hd₁
  have nF₂ : FB (yOf θ₂) u ≠ 0 := by rw [FB_yOf hd₂]; exact div_ne_zero ha₂ hd₂
  have nF₃ : FB (yOf θ₃) u ≠ 0 := by rw [FB_yOf hd₃]; exact div_ne_zero ha₃ hd₃
  have nG₁ : GB (yOf θ₁) u v ≠ 0 := by rw [GB_yOf hd₁]; exact div_ne_zero hw₁ hd₁
  have nG₂ : GB (yOf θ₂) u v ≠ 0 := by rw [GB_yOf hd₂]; exact div_ne_zero hw₂ hd₂
  have nG₃ : GB (yOf θ₃) u v ≠ 0 := by rw [GB_yOf hd₃]; exact div_ne_zero hw₃ hd₃
  have nH₁ : HB (yOf θ₁) v ≠ 0 := by rw [HB_yOf hd₁]; exact div_ne_zero hb₁ hd₁
  have nH₂ : HB (yOf θ₂) v ≠ 0 := by rw [HB_yOf hd₂]; exact div_ne_zero hb₂ hd₂
  have nH₃ : HB (yOf θ₃) v ≠ 0 := by rw [HB_yOf hd₃]; exact div_ne_zero hb₃ hd₃
  have hclear := clearB_abstract (FB (yOf θ₁) u) (FB (yOf θ₂) u) (FB (yOf θ₃) u)
    (GB (yOf θ₁) u v) (GB (yOf θ₂) u v) (GB (yOf θ₃) u v)
    (HB (yOf θ₁) v) (HB (yOf θ₂) v) (HB (yOf θ₃) v)
    nF₁ nF₂ nF₃ nG₁ nG₂ nG₃ nH₁ nH₂ nH₃
  rw [show termB (yOf θ₁) (yOf θ₂) (yOf θ₃) u v + termB (yOf θ₂) (yOf θ₃) (yOf θ₁) u v
        + termB (yOf θ₃) (yOf θ₁) (yOf θ₂) u v = _ from rfl]
  simp only [termB]
  rw [hclear]
  congr 1
  rw [kernelSum]
  rw [one_div_FB hd₁ ha₁, one_div_FB hd₂ ha₂, one_div_FB hd₃ ha₃,
    one_div_GB hd₁ hw₁, one_div_GB hd₂ hw₂, one_div_GB hd₃ hw₃,
    FB_div_HB hd₁ hb₁, FB_div_HB hd₂ hb₂, FB_div_HB hd₃ hb₃]

/-- **The bridge.**  The kernel sum is nonnegative for ordered `θ`s in `[0,1)`,
by the small certificate. -/
theorem kernelSum_nonneg_B {θ₁ θ₂ θ₃ u v : ℝ}
    (h0 : 0 ≤ θ₁) (h12 : θ₁ ≤ θ₂) (h23 : θ₂ ≤ θ₃) (h31 : θ₃ < 1)
    (hv0 : 0 ≤ v) (hvu : v ≤ u) (hu1 : u < 1) :
    0 ≤ kernelSum θ₁ θ₂ θ₃ u v := by
  have h₂ : 0 ≤ θ₂ := le_trans h0 h12
  have h₃ : 0 ≤ θ₃ := le_trans h₂ h23
  have h₁' : θ₁ < 1 := lt_of_le_of_lt (le_trans h12 h23) h31
  have h₂' : θ₂ < 1 := lt_of_le_of_lt h23 h31
  have hu0 : 0 ≤ u := le_trans hv0 hvu
  have hv1 : v < 1 := lt_of_le_of_lt hvu hu1
  have hvne : (1:ℝ) - v ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hd₁ : (1:ℝ) - θ₁ ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hd₂ : (1:ℝ) - θ₂ ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hd₃ : (1:ℝ) - θ₃ ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have huv0 : 0 ≤ u * v := mul_nonneg hu0 hv0
  have huv1 : u * v < 1 := by nlinarith
  have pa : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → (0:ℝ) < 1 - θ * u := fun θ a b => by nlinarith
  have pb : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → (0:ℝ) < 1 - θ * v := fun θ a b => by nlinarith
  have pw : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → (0:ℝ) < 1 - θ * (u * v) := fun θ a b => by nlinarith
  -- the certificate applies at the substituted point
  have hnn : 0 ≤ PE.eval ![yOf θ₁, yOf θ₂ - yOf θ₁, yOf θ₃ - yOf θ₂, 1 - v, v,
      (u - v) / (1 - v), (1 - u) / (1 - v)] kerBPE := by
    refine PE.eval_nonneg_of_norm ?_ kerBPE kerBPE_allNonneg
    intro i
    fin_cases i
    · exact yOf_nonneg h0 h₁'
    · simpa using sub_nonneg.mpr (yOf_mono h0 h12 h₂')
    · simpa using sub_nonneg.mpr (yOf_mono h₂ h23 h31)
    · simpa using le_of_lt (by linarith : (0:ℝ) < 1 - v)
    · simpa using hv0
    · simpa using div_nonneg (by linarith) (by linarith : (0:ℝ) ≤ 1 - v)
    · simpa using div_nonneg (by linarith) (by linarith : (0:ℝ) ≤ 1 - v)
  rw [eval_kerBPE_subst _ _ _ _ _ hvne,
    termB_sum_eq hd₁ hd₂ hd₃ (ne_of_gt (pa θ₁ h0 h₁')) (ne_of_gt (pa θ₂ h₂ h₂'))
      (ne_of_gt (pa θ₃ h₃ h31)) (ne_of_gt (pb θ₁ h0 h₁')) (ne_of_gt (pb θ₂ h₂ h₂'))
      (ne_of_gt (pb θ₃ h₃ h31)) (ne_of_gt (pw θ₁ h0 h₁')) (ne_of_gt (pw θ₂ h₂ h₂'))
      (ne_of_gt (pw θ₃ h₃ h31))] at hnn
  have hD : (0:ℝ) < FB (yOf θ₁) u * FB (yOf θ₂) u * FB (yOf θ₃) u
      * (GB (yOf θ₁) u v * GB (yOf θ₂) u v * GB (yOf θ₃) u v)
      * (HB (yOf θ₁) v ^ 2 * HB (yOf θ₂) v ^ 2 * HB (yOf θ₃) v ^ 2) := by
    have f₁ := FB_pos h0 h₁' hu0 hu1
    have f₂ := FB_pos h₂ h₂' hu0 hu1
    have f₃ := FB_pos h₃ h31 hu0 hu1
    have g₁ := GB_pos h0 h₁' huv0 huv1
    have g₂ := GB_pos h₂ h₂' huv0 huv1
    have g₃ := GB_pos h₃ h31 huv0 huv1
    have k₁ := HB_pos h0 h₁' hv0 hv1
    have k₂ := HB_pos h₂ h₂' hv0 hv1
    have k₃ := HB_pos h₃ h31 hv0 hv1
    positivity
  exact (mul_nonneg_iff_of_pos_right hD).mp hnn

/-- The kernel lemma from the small certificate, ordering hypothesis removed.

Still restricted to `θᵢ < 1`, where `y = θ/(1−θ)` is finite; `KernelBridge.lean`
proves the `θᵢ ≤ 1` version, which the diagonal reduction needs at the endpoint
of its integral.  Closing that gap here means a continuity argument in a scaling
parameter `c ↑ 1`, which is the one piece missing before this can replace
`KernelCertFast.lean` in the main build. -/
theorem kernelSum_nonneg_B' {θ₁ θ₂ θ₃ u v : ℝ} (h₁ : 0 ≤ θ₁) (h₁' : θ₁ < 1)
    (h₂ : 0 ≤ θ₂) (h₂' : θ₂ < 1) (h₃ : 0 ≤ θ₃) (h₃' : θ₃ < 1)
    (hv0 : 0 ≤ v) (hvu : v ≤ u) (hu1 : u < 1) :
    0 ≤ kernelSum θ₁ θ₂ θ₃ u v := by
  rcases le_total θ₁ θ₂ with h12 | h12 <;> rcases le_total θ₂ θ₃ with h23 | h23 <;>
    rcases le_total θ₁ θ₃ with h13 | h13
  · exact kernelSum_nonneg_B h₁ h12 h23 h₃' hv0 hvu hu1
  · exact kernelSum_nonneg_B h₁ h12 h23 h₃' hv0 hvu hu1
  · rw [kernelSum_swap₂₃]
    exact kernelSum_nonneg_B h₁ h13 h23 h₂' hv0 hvu hu1
  · rw [kernelSum_swap₂₃, kernelSum_swap₁₂]
    exact kernelSum_nonneg_B h₃ h13 h12 h₂' hv0 hvu hu1
  · rw [kernelSum_swap₁₂]
    exact kernelSum_nonneg_B h₂ h12 h13 h₃' hv0 hvu hu1
  · rw [kernelSum_swap₁₂, kernelSum_swap₂₃]
    exact kernelSum_nonneg_B h₂ h23 h13 h₁' hv0 hvu hu1
  · rw [kernelSum_swap₁₂, kernelSum_swap₂₃]
    exact kernelSum_nonneg_B h₂ (by linarith) (by linarith) h₁' hv0 hvu hu1
  · rw [kernelSum_swap₂₃, kernelSum_swap₁₂, kernelSum_swap₂₃]
    exact kernelSum_nonneg_B h₃ h23 h12 h₁' hv0 hvu hu1

end BSCAveraging.Reflect
