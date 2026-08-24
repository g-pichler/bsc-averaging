import BSCAveraging.MixtureRep
import BSCAveraging.KernelBridge

/-! # The diagonal reduction

`NOTES.md` §7f, step (iii).  With `A, B, C` the three linear functionals of the
mixture representation (`MixtureRep.lean`),

```
N(α,β) := A(β)·B(α)·C(α) − A(α)·B(β)·C(β) ,
```

and the diagonal reduction is `N ≥ 0` for `β ≤ α`.  Each factor is a
one-dimensional integral over the mixing variable `s ∈ [0,1]` (`θ = s²`), so
each of the two products is an *iterated* triple integral — no Fubini is needed,
because a product of one-dimensional integrals factors out of an iterated
integral by `integral_const_mul` alone.

Summing over the six permutations of the three dummy variables leaves the value
unchanged, `Σ_σ ∭ P∘σ = 6N`, while the *integrand* becomes symmetric and is a
positive multiple of the kernel sum of `KernelBridge.lean`.  Hence `6N ≥ 0`. -/

namespace BSCAveraging.Core

open MeasureTheory

/-- An iterated triple integral of a finite sum of product terms factors into a
finite sum of products of one-dimensional integrals. -/
lemma integral3_sum {n : ℕ} (F G H : Fin n → ℝ → ℝ)
    (hF : ∀ i, ContinuousOn (F i) (Set.uIcc (0:ℝ) 1))
    (hG : ∀ i, ContinuousOn (G i) (Set.uIcc (0:ℝ) 1))
    (hH : ∀ i, ContinuousOn (H i) (Set.uIcc (0:ℝ) 1)) :
    (∫ s₁ in (0:ℝ)..1, ∫ s₂ in (0:ℝ)..1, ∫ s₃ in (0:ℝ)..1,
        ∑ i, F i s₁ * (G i s₂ * H i s₃))
      = ∑ i, (∫ s in (0:ℝ)..1, F i s)
          * ((∫ s in (0:ℝ)..1, G i s) * (∫ s in (0:ℝ)..1, H i s)) := by
  have iF : ∀ i, IntervalIntegrable (F i) volume 0 1 := fun i => (hF i).intervalIntegrable
  have iG : ∀ i, IntervalIntegrable (G i) volume 0 1 := fun i => (hG i).intervalIntegrable
  have iH : ∀ i, IntervalIntegrable (H i) volume 0 1 := fun i => (hH i).intervalIntegrable
  have step1 : ∀ s₁ s₂ : ℝ, (∫ s₃ in (0:ℝ)..1, ∑ i, F i s₁ * (G i s₂ * H i s₃))
      = ∑ i, F i s₁ * (G i s₂ * ∫ s in (0:ℝ)..1, H i s) := by
    intro s₁ s₂
    rw [intervalIntegral.integral_finset_sum
      (fun i _ => ((iH i).const_mul (G i s₂)).const_mul (F i s₁))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have step2 : ∀ s₁ : ℝ, (∫ s₂ in (0:ℝ)..1, ∑ i, F i s₁ * (G i s₂ * ∫ s in (0:ℝ)..1, H i s))
      = ∑ i, F i s₁ * ((∫ s in (0:ℝ)..1, G i s) * ∫ s in (0:ℝ)..1, H i s) := by
    intro s₁
    rw [intervalIntegral.integral_finset_sum
      (fun i _ => (((iG i).mul_const (∫ s in (0:ℝ)..1, H i s)).const_mul (F i s₁)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
  simp only [step1, step2]
  rw [intervalIntegral.integral_finset_sum
    (fun i _ => ((iF i).mul_const
      ((∫ s in (0:ℝ)..1, G i s) * ∫ s in (0:ℝ)..1, H i s)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_mul_const]


/-! ### The three integrands -/

/-- `A`-integrand: `θ ↦ v(1−θ)/(1−θv)²` at `θ = s²`, `v = z²`. -/
noncomputable def aIf (z : ℝ) : ℝ → ℝ := fun s => z ^ 2 * (1 - s ^ 2) / (1 - s ^ 2 * z ^ 2) ^ 2

/-- `B`-integrand: `θ ↦ (1−u)/(1−θu)` at `θ = s²`, `u = z²`. -/
noncomputable def bIf (z : ℝ) : ℝ → ℝ := fun s => (1 - z ^ 2) / (1 - s ^ 2 * z ^ 2)

/-- `C`-integrand: `θ ↦ (1−θ)z²/(1−θz²) − (1−θ)t/(1−θt)` at `θ = s²`. -/
noncomputable def cIf (z2 t : ℝ) : ℝ → ℝ :=
  fun s => (1 - s ^ 2) * z2 / (1 - s ^ 2 * z2) - (1 - s ^ 2) * t / (1 - s ^ 2 * t)

lemma continuousOn_aIf {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    ContinuousOn (aIf z) (Set.uIcc (0:ℝ) 1) := by
  rw [Set.uIcc_of_le (by norm_num)]
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro s hs; exact pow_ne_zero 2 (one_sub_sq_ne hs.1 hs.2 hz0 hz1)

lemma continuousOn_bIf {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    ContinuousOn (bIf z) (Set.uIcc (0:ℝ) 1) := by
  rw [Set.uIcc_of_le (by norm_num)]
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro s hs; exact one_sub_sq_ne hs.1 hs.2 hz0 hz1

lemma continuousOn_cIf {z t : ℝ} (hz0 : 0 < z) (hz1 : z < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    ContinuousOn (cIf (z ^ 2) t) (Set.uIcc (0:ℝ) 1) := by
  rw [Set.uIcc_of_le (by norm_num)]
  refine ContinuousOn.sub (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
  · intro s hs; exact one_sub_sq_ne hs.1 hs.2 hz0 hz1
  · intro s hs
    have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    have : s ^ 2 * t < 1 := by nlinarith [sq_nonneg s]
    intro h; linarith

lemma integral_aIf {α : ℝ} (ha0 : 0 < α) (ha1 : α < 1) :
    (∫ s in (0:ℝ)..1, aIf α s) = Aval α := (Aval_eq_integral ha0 ha1).symm

lemma integral_bIf {α : ℝ} (ha0 : 0 < α) (ha1 : α < 1) :
    (∫ s in (0:ℝ)..1, bIf α s) = gFun α := (gFun_eq_integral ha0 ha1).symm

/-- `∫ cIf = C`, the third functional. -/
lemma integral_cIf {α β : ℝ} (ha0 : 0 < α) (ha1 : α < 1) (hb0 : 0 < β) (hb1 : β < 1) :
    (∫ s in (0:ℝ)..1, cIf (α ^ 2) (α ^ 2 * β ^ 2) s) = gFun (α * β) - gFun α := by
  have hx0 : 0 < α * β := mul_pos ha0 hb0
  have hx1 : α * β < 1 := by nlinarith
  have hsq : (α * β) ^ 2 = α ^ 2 * β ^ 2 := by ring
  have h1 : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) * α ^ 2 / (1 - s ^ 2 * α ^ 2))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro s hs; exact one_sub_sq_ne hs.1 hs.2 ha0 ha1
  have h2 : IntervalIntegrable
      (fun s : ℝ => (1 - s ^ 2) * (α ^ 2 * β ^ 2) / (1 - s ^ 2 * (α ^ 2 * β ^ 2))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro s hs
    have := one_sub_sq_ne hs.1 hs.2 hx0 hx1
    rwa [hsq] at this
  have e1 := one_sub_gFun_eq_integral ha0 ha1
  have e2 := one_sub_gFun_eq_integral hx0 hx1
  rw [hsq] at e2
  simp only [cIf]
  rw [intervalIntegral.integral_sub h1 h2, ← e1, ← e2]
  ring

/-! ### The diagonal reduction -/

/-- `N(α,β) = A(β)B(α)C(α) − A(α)B(β)C(β)`. -/
noncomputable def Nfun (α β : ℝ) : ℝ :=
  Aval β * (gFun α * (gFun (α * β) - gFun α))
    - Aval α * (gFun β * (gFun (α * β) - gFun β))

private noncomputable def Fv (α β : ℝ) : Fin 12 → ℝ → ℝ := ![aIf β, aIf β, bIf α, cIf (α ^ 2) (α ^ 2 * β ^ 2), bIf α, cIf (α ^ 2) (α ^ 2 * β ^ 2), (fun s => -(aIf α s)), (fun s => -(aIf α s)), (fun s => -(bIf β s)), (fun s => -(cIf (β ^ 2) (α ^ 2 * β ^ 2) s)), (fun s => -(bIf β s)), (fun s => -(cIf (β ^ 2) (α ^ 2 * β ^ 2) s))]
private noncomputable def Gv (α β : ℝ) : Fin 12 → ℝ → ℝ := ![bIf α, cIf (α ^ 2) (α ^ 2 * β ^ 2), aIf β, aIf β, cIf (α ^ 2) (α ^ 2 * β ^ 2), bIf α, bIf β, cIf (β ^ 2) (α ^ 2 * β ^ 2), aIf α, aIf α, cIf (β ^ 2) (α ^ 2 * β ^ 2), bIf β]
private noncomputable def Hv (α β : ℝ) : Fin 12 → ℝ → ℝ := ![cIf (α ^ 2) (α ^ 2 * β ^ 2), bIf α, cIf (α ^ 2) (α ^ 2 * β ^ 2), bIf α, aIf β, aIf β, cIf (β ^ 2) (α ^ 2 * β ^ 2), bIf β, cIf (β ^ 2) (α ^ 2 * β ^ 2), bIf β, aIf α, aIf α]

lemma cIf_closed {z2 t s : ℝ} (h1 : 1 - s ^ 2 * z2 ≠ 0) (h2 : 1 - s ^ 2 * t ≠ 0) :
    cIf z2 t s = (1 - s ^ 2) * (z2 - t) / ((1 - s ^ 2 * z2) * (1 - s ^ 2 * t)) := by
  simp only [cIf]; field_simp; ring

/-- The symmetrised integrand is a positive multiple of the kernel sum. -/
lemma sym_pointwise {α β s₁ s₂ s₃ : ℝ} (ha0 : 0 < α) (ha1 : α < 1) (hb0 : 0 < β) (hb1 : β < 1)
    (k₁ : 0 ≤ s₁) (k₁' : s₁ ≤ 1) (k₂ : 0 ≤ s₂) (k₂' : s₂ ≤ 1) (k₃ : 0 ≤ s₃) (k₃' : s₃ ≤ 1) :
    (∑ i, Fv α β i s₁ * (Gv α β i s₂ * Hv α β i s₃))
      = α ^ 2 * β ^ 2 * (1 - α ^ 2) * (1 - β ^ 2)
          / ((1 - s₁ ^ 2 * α ^ 2) * (1 - s₂ ^ 2 * α ^ 2) * (1 - s₃ ^ 2 * α ^ 2))
        * kernelSum (s₁ ^ 2) (s₂ ^ 2) (s₃ ^ 2) (α ^ 2) (β ^ 2) := by
  have hx0 : 0 < α * β := mul_pos ha0 hb0
  have hx1 : α * β < 1 := by nlinarith
  have hsq : (α * β) ^ 2 = α ^ 2 * β ^ 2 := by ring
  have hA : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (1 : ℝ) - s ^ 2 * α ^ 2 ≠ 0 :=
    fun s h h' => one_sub_sq_ne h h' ha0 ha1
  have hB : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (1 : ℝ) - s ^ 2 * β ^ 2 ≠ 0 :=
    fun s h h' => one_sub_sq_ne h h' hb0 hb1
  have hW : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (1 : ℝ) - s ^ 2 * (α ^ 2 * β ^ 2) ≠ 0 := by
    intro s h h'
    have := one_sub_sq_ne h h' hx0 hx1
    rwa [hsq] at this
  simp only [Fv, Gv, Hv, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]
  rw [cIf_closed (hA s₁ k₁ k₁') (hW s₁ k₁ k₁'), cIf_closed (hA s₂ k₂ k₂') (hW s₂ k₂ k₂'),
    cIf_closed (hA s₃ k₃ k₃') (hW s₃ k₃ k₃'), cIf_closed (hB s₁ k₁ k₁') (hW s₁ k₁ k₁'),
    cIf_closed (hB s₂ k₂ k₂') (hW s₂ k₂ k₂'), cIf_closed (hB s₃ k₃ k₃') (hW s₃ k₃ k₃')]
  simp only [aIf, bIf, kernelSum]
  have e1 : α ^ 2 - α ^ 2 * β ^ 2 = α ^ 2 * (1 - β ^ 2) := by ring
  have e2 : β ^ 2 - α ^ 2 * β ^ 2 = β ^ 2 * (1 - α ^ 2) := by ring
  rw [e1, e2]
  have n₁ := hA s₁ k₁ k₁'; have n₂ := hA s₂ k₂ k₂'; have n₃ := hA s₃ k₃ k₃'
  have m₁ := hB s₁ k₁ k₁'; have m₂ := hB s₂ k₂ k₂'; have m₃ := hB s₃ k₃ k₃'
  have p₁ := hW s₁ k₁ k₁'; have p₂ := hW s₂ k₂ k₂'; have p₃ := hW s₃ k₃ k₃'
  set A₁ := 1 - s₁ ^ 2 with hA₁
  set A₂ := 1 - s₂ ^ 2 with hA₂
  set A₃ := 1 - s₃ ^ 2 with hA₃
  set a₁ := 1 - s₁ ^ 2 * α ^ 2 with ha₁d
  set a₂ := 1 - s₂ ^ 2 * α ^ 2 with ha₂d
  set a₃ := 1 - s₃ ^ 2 * α ^ 2 with ha₃d
  set b₁ := 1 - s₁ ^ 2 * β ^ 2 with hb₁d
  set b₂ := 1 - s₂ ^ 2 * β ^ 2 with hb₂d
  set b₃ := 1 - s₃ ^ 2 * β ^ 2 with hb₃d
  set w₁ := 1 - s₁ ^ 2 * (α ^ 2 * β ^ 2) with hw₁d
  set w₂ := 1 - s₂ ^ 2 * (α ^ 2 * β ^ 2) with hw₂d
  set w₃ := 1 - s₃ ^ 2 * (α ^ 2 * β ^ 2) with hw₃d
  set u := α ^ 2 with hud
  set v := β ^ 2 with hvd
  field_simp
  ring

lemma integral_cIf' {α β : ℝ} (ha0 : 0 < α) (ha1 : α < 1) (hb0 : 0 < β) (hb1 : β < 1) :
    (∫ s in (0:ℝ)..1, cIf (β ^ 2) (α ^ 2 * β ^ 2) s) = gFun (α * β) - gFun β := by
  have h := integral_cIf hb0 hb1 ha0 ha1
  rw [show β ^ 2 * α ^ 2 = α ^ 2 * β ^ 2 by ring, show β * α = α * β by ring] at h
  exact h

/-- **The diagonal reduction**: `N ≥ 0` for `0 < β ≤ α < 1`. -/
theorem Nfun_nonneg {α β : ℝ} (hb0 : 0 < β) (hba : β ≤ α) (ha1 : α < 1) : 0 ≤ Nfun α β := by
  have ha0 : 0 < α := lt_of_lt_of_le hb0 hba
  have hb1 : β < 1 := lt_of_le_of_lt hba ha1
  have ht0 : 0 < α ^ 2 * β ^ 2 := by positivity
  have hα2 : α ^ 2 < 1 := by nlinarith
  have hβ2 : β ^ 2 < 1 := by nlinarith
  have ht1 : α ^ 2 * β ^ 2 < 1 := by nlinarith
  have ca : ContinuousOn (aIf α) (Set.uIcc (0:ℝ) 1) := continuousOn_aIf ha0 ha1
  have ca' : ContinuousOn (aIf β) (Set.uIcc (0:ℝ) 1) := continuousOn_aIf hb0 hb1
  have cb : ContinuousOn (bIf α) (Set.uIcc (0:ℝ) 1) := continuousOn_bIf ha0 ha1
  have cb' : ContinuousOn (bIf β) (Set.uIcc (0:ℝ) 1) := continuousOn_bIf hb0 hb1
  have cc : ContinuousOn (cIf (α ^ 2) (α ^ 2 * β ^ 2)) (Set.uIcc (0:ℝ) 1) :=
    continuousOn_cIf ha0 ha1 ht0 ht1
  have cc' : ContinuousOn (cIf (β ^ 2) (α ^ 2 * β ^ 2)) (Set.uIcc (0:ℝ) 1) :=
    continuousOn_cIf hb0 hb1 ht0 ht1
  have cF : ∀ i, ContinuousOn (Fv α β i) (Set.uIcc (0:ℝ) 1) := by
    intro i; fin_cases i <;>
      simp only [Fv, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
      first
        | exact ca | exact ca' | exact cb | exact cb' | exact cc | exact cc'
        | exact ca.neg | exact ca'.neg | exact cb.neg | exact cb'.neg
        | exact cc.neg | exact cc'.neg
  have cG : ∀ i, ContinuousOn (Gv α β i) (Set.uIcc (0:ℝ) 1) := by
    intro i; fin_cases i <;>
      simp only [Gv, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
      first
        | exact ca | exact ca' | exact cb | exact cb' | exact cc | exact cc'
  have cH : ∀ i, ContinuousOn (Hv α β i) (Set.uIcc (0:ℝ) 1) := by
    intro i; fin_cases i <;>
      simp only [Hv, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
      first
        | exact ca | exact ca' | exact cb | exact cb' | exact cc | exact cc'
  have hsum : (∑ i, (∫ s in (0:ℝ)..1, Fv α β i s)
        * ((∫ s in (0:ℝ)..1, Gv α β i s) * (∫ s in (0:ℝ)..1, Hv α β i s))) = 6 * Nfun α β := by
    simp only [Fv, Gv, Hv, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, add_zero, intervalIntegral.integral_neg]
    rw [integral_aIf ha0 ha1, integral_aIf hb0 hb1, integral_bIf ha0 ha1, integral_bIf hb0 hb1,
      integral_cIf ha0 ha1 hb0 hb1, integral_cIf' ha0 ha1 hb0 hb1, Nfun]
    ring
  have hnn : 0 ≤ ∫ s₁ in (0:ℝ)..1, ∫ s₂ in (0:ℝ)..1, ∫ s₃ in (0:ℝ)..1,
      ∑ i, Fv α β i s₁ * (Gv α β i s₂ * Hv α β i s₃) := by
    refine intervalIntegral.integral_nonneg (by norm_num) fun s₁ hs₁ => ?_
    refine intervalIntegral.integral_nonneg (by norm_num) fun s₂ hs₂ => ?_
    refine intervalIntegral.integral_nonneg (by norm_num) fun s₃ hs₃ => ?_
    rw [sym_pointwise ha0 ha1 hb0 hb1 hs₁.1 hs₁.2 hs₂.1 hs₂.2 hs₃.1 hs₃.2]
    have hk : 0 ≤ kernelSum (s₁ ^ 2) (s₂ ^ 2) (s₃ ^ 2) (α ^ 2) (β ^ 2) := by
      refine kernelSum_nonneg (by positivity) ?_ (by positivity) ?_ (by positivity) ?_
        (by positivity) (by nlinarith) (by nlinarith [sq_nonneg α])
      · nlinarith [hs₁.1, hs₁.2]
      · nlinarith [hs₂.1, hs₂.2]
      · nlinarith [hs₃.1, hs₃.2]
    have hd₁ : 0 < 1 - s₁ ^ 2 * α ^ 2 := lt_of_le_of_ne (le_of_lt (by
      have := one_sub_sq_ne hs₁.1 hs₁.2 ha0 ha1
      rcases lt_or_gt_of_ne this with h | h
      · exfalso; nlinarith [sq_nonneg s₁, sq_nonneg α, hs₁.1, hs₁.2]
      · exact h)) (Ne.symm (one_sub_sq_ne hs₁.1 hs₁.2 ha0 ha1))
    have hd₂ : 0 < 1 - s₂ ^ 2 * α ^ 2 := by
      have : s₂ ^ 2 * α ^ 2 < 1 := sq_mul_sq_lt_one hs₂.1 hs₂.2 ha0 ha1
      linarith
    have hd₃ : 0 < 1 - s₃ ^ 2 * α ^ 2 := by
      have : s₃ ^ 2 * α ^ 2 < 1 := sq_mul_sq_lt_one hs₃.1 hs₃.2 ha0 ha1
      linarith
    have hpos : 0 < α ^ 2 * β ^ 2 * (1 - α ^ 2) * (1 - β ^ 2)
        / ((1 - s₁ ^ 2 * α ^ 2) * (1 - s₂ ^ 2 * α ^ 2) * (1 - s₃ ^ 2 * α ^ 2)) := by
      have h1 : 0 < 1 - α ^ 2 := by nlinarith
      have h2 : 0 < 1 - β ^ 2 := by nlinarith
      positivity
    exact mul_nonneg (le_of_lt hpos) hk
  rw [integral3_sum (Fv α β) (Gv α β) (Hv α β) cF cG cH, hsum] at hnn
  linarith

end BSCAveraging.Core
