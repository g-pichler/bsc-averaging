import BSCAveraging.CFinish

/-! # Conjecture 2 of Entropy 24(9):1321, at `p = 0`

The minimisation mirror of `CFinish.lean`.  The four steps are the same:

* `(A′)` a minimiser exists;
* `(B′)` an interior minimiser is a BSC pair;
* `(C′)` the BSC pair is a saddle, so it is not a minimiser either — the very
  same `hessian_indefinite`, read in the other direction;
* `(D′)` at a corner the Z/Z pair is optimal — `bestResponse_ge_of_certificate`
  with the mirror certificate `MDFun_nonpos`, plus monotonicity of `mzsValue`.

This file starts with `(D′)`, which needs only one new ingredient beyond the
mirror certificate that `PZero.lean` already has: `mzsValue a ·` is increasing.
-/

open Real

namespace BSCAveraging

variable {a d : ℝ}

/-! ## `(D′)`: the corner bound for the minimisation

### `mzsValue` in closed form -/

/-- The numerator of `mzsValue` over `(1+a)(1+d)`. -/
noncomputable def mzsNum (a d : ℝ) : ℝ :=
  d * ((1 - a) * log (1 - a)) + (1 + d * a) * log (1 + d * a)
    + 2 * a * d * log 2 + a * ((1 - d) * log (1 - d))

theorem mzsValue_eq (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    mzsValue a d = mzsNum a d / ((1 + a) * (1 + d)) := by
  have h1a : (0:ℝ) < 1 + a := by linarith
  have h1d : (0:ℝ) < 1 + d := by linarith
  simp only [mzsValue, phiZ, fFun, mzsNum]
  rw [show (1:ℝ) + -a = 1 - a by ring, show -(d * -a) = d * a by ring,
    show (1:ℝ) + -(d * 1) = 1 - d by ring, show (1:ℝ) + 1 = 2 by norm_num]
  field_simp
  ring

/-- The `d`-derivative of the numerator. -/
noncomputable def mzsNum' (a d : ℝ) : ℝ :=
  (1 - a) * log (1 - a) + a * log (1 + d * a) + 2 * a * log 2 - a * log (1 - d)

theorem hasDerivAt_mzsNum (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    HasDerivAt (fun t => mzsNum a t) (mzsNum' a d) d := by
  have hda : (0:ℝ) < 1 + d * a := by nlinarith
  have h1d : (0:ℝ) < 1 - d := by linarith
  have e1 : HasDerivAt (fun t : ℝ => t * ((1 - a) * log (1 - a))) ((1 - a) * log (1 - a)) d := by
    simpa using (hasDerivAt_id d).mul_const ((1 - a) * log (1 - a))
  have hu : HasDerivAt (fun t : ℝ => 1 + t * a) a d := by
    simpa using ((hasDerivAt_id d).mul_const a).const_add 1
  have e2 : HasDerivAt (fun t : ℝ => (1 + t * a) * log (1 + t * a))
      (a * log (1 + d * a) + a) d := by
    have hl : HasDerivAt (fun t : ℝ => log (1 + t * a)) (a / (1 + d * a)) d := by
      simpa [div_eq_mul_inv] using hu.log (ne_of_gt hda)
    have := hu.mul hl
    refine (Core.hd_congr this ?_)
    field_simp
  have e3 : HasDerivAt (fun t : ℝ => 2 * a * t * log 2) (2 * a * log 2) d := by
    simpa [mul_comm, mul_assoc] using (((hasDerivAt_id d).const_mul (2 * a)).mul_const (log 2))
  have hv : HasDerivAt (fun t : ℝ => 1 - t) (-1) d := by
    simpa using (hasDerivAt_id d).const_sub 1
  have e4 : HasDerivAt (fun t : ℝ => a * ((1 - t) * log (1 - t))) (-(a * log (1 - d)) - a) d := by
    have hl : HasDerivAt (fun t : ℝ => log (1 - t)) (-1 / (1 - d)) d := by
      simpa [div_eq_mul_inv] using hv.log (ne_of_gt h1d)
    have := (hv.mul hl).const_mul a
    refine (Core.hd_congr this ?_)
    field_simp
    ring
  have := ((e1.add e2).add e3).add e4
  refine Core.hd_congr this ?_
  simp only [mzsNum']
  ring

/-- The key inequality behind monotonicity: `N′·(1+d) − N > 0`. -/
theorem mzs_deriv_num_pos (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    0 < mzsNum' a d * (1 + d) - mzsNum a d := by
  have h1a : (0:ℝ) < 1 - a := by linarith
  have h1d : (0:ℝ) < 1 - d := by linarith
  have hda : (0:ℝ) < 1 + d * a := by nlinarith
  -- the difference collapses to two logarithms
  have hcollapse : mzsNum' a d * (1 + d) - mzsNum a d
      = (1 - a) * log (1 - a) - (1 - a) * log (1 + d * a) + 2 * a * log 2
        - 2 * a * log (1 - d) := by
    simp only [mzsNum, mzsNum']; ring
  rw [hcollapse]
  -- `−(1−a)·log(1−a) ≤ a`
  have hA : -((1 - a) * log (1 - a)) ≤ a := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / (1 - a) by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt h1a), Real.log_one, zero_sub] at h
    have hid : (1:ℝ) / (1 - a) - 1 = a / (1 - a) := by
      field_simp
      ring
    rw [hid] at h
    have h3 : (1 - a) * (-log (1 - a)) ≤ (1 - a) * (a / (1 - a)) :=
      mul_le_mul_of_nonneg_left h (le_of_lt h1a)
    have h4 : (1 - a) * (a / (1 - a)) = a := by field_simp
    nlinarith [h3, h4]
  -- `(1−a)·log(1+da) ≤ d·a`
  have hB : (1 - a) * log (1 + d * a) ≤ d * a := by
    have h := Real.log_le_sub_one_of_pos hda
    have hnn : 0 ≤ log (1 + d * a) := Real.log_nonneg (by nlinarith)
    nlinarith
  -- `−log(1−d) ≥ d`
  have hC : d ≤ -log (1 - d) := by
    have h := Real.log_le_sub_one_of_pos h1d
    linarith
  -- `log 2 > 1/2`
  have hlog2 : (1:ℝ) / 2 < log 2 := by
    have := Real.log_two_gt_d9; linarith
  nlinarith
theorem hasDerivAt_mzsValue_snd (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    HasDerivAt (fun t => mzsValue a t)
      ((mzsNum' a d * (1 + d) - mzsNum a d) / ((1 + a) * (1 + d) ^ 2)) d := by
  have h1a : (0:ℝ) < 1 + a := by linarith
  have h1d : (0:ℝ) < 1 + d := by linarith
  have heq : (fun t => mzsValue a t) =ᶠ[nhds d] fun t => mzsNum a t / ((1 + a) * (1 + t)) := by
    have hnb : Set.Ioo (0:ℝ) 1 ∈ nhds d := Ioo_mem_nhds hd0 hd1
    filter_upwards [hnb] with t ht using mzsValue_eq ha0 ha1 ht.1 ht.2
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have hden : HasDerivAt (fun t : ℝ => (1 + a) * (1 + t)) (1 + a) d := by
    simpa using ((hasDerivAt_id d).const_add 1).const_mul (1 + a)
  have hne : (1 + a) * (1 + d) ≠ 0 := by positivity
  refine Core.hd_congr ((hasDerivAt_mzsNum ha0 ha1 hd0 hd1).div hden hne) ?_
  field_simp

theorem continuousOn_phiZ_fst (s : ℝ) :
    ContinuousOn (fun t : ℝ => phiZ t s) (Set.Ioc (0:ℝ) 1) := by
  have hne : ∀ t ∈ Set.Ioc (0:ℝ) 1, (1:ℝ) + t ≠ 0 := by
    intro t ht; have := ht.1; positivity
  simp only [phiZ]
  refine ContinuousOn.add ?_ ?_
  · exact (continuousOn_id.div (continuousOn_const.add continuousOn_id) hne).mul continuousOn_const
  · exact (continuousOn_const.div (continuousOn_const.add continuousOn_id) hne).mul
      (continuous_fFun.comp_continuousOn (by fun_prop))

theorem continuousOn_mzsValue_snd (a : ℝ) :
    ContinuousOn (fun t : ℝ => mzsValue a t) (Set.Ioc (0:ℝ) 1) := by
  simp only [mzsValue]
  exact (continuousOn_const.mul (continuousOn_phiZ_fst _)).add
    (continuousOn_const.mul (continuousOn_phiZ_fst _))

/-- `mzsValue a 1 = zsRate a`: at the deterministic `V`-side the certificate
bound is exactly the `U`-side rate. -/
theorem mzsValue_at_one (ha0 : 0 < a) (ha1 : a < 1) : mzsValue a 1 = zsRate a := by
  have h1a : (0:ℝ) < 1 + a := by linarith
  simp only [mzsValue, phiZ, zsRate, fe, fFun]
  norm_num
  field_simp
  ring_nf

theorem mzsValue_strictMonoOn_snd (ha0 : 0 < a) (ha1 : a < 1) :
    StrictMonoOn (fun t : ℝ => mzsValue a t) (Set.Ioo (0:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0:ℝ) 1)
  · intro x hx
    exact ((hasDerivAt_mzsValue_snd ha0 ha1 hx.1 hx.2).continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(hasDerivAt_mzsValue_snd ha0 ha1 hx.1 hx.2).deriv]
    have hnum := mzs_deriv_num_pos ha0 ha1 hx.1 hx.2
    have hden : (0:ℝ) < (1 + a) * (1 + x) ^ 2 := by nlinarith [hx.1]
    exact div_pos hnum hden

/-- The value half of `(D′)`: a **larger** S-parameter gives a larger value, so a
`V`-side corner over budget is no help to the minimiser. -/
theorem mzsValue_mono_snd {d' : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (h0 : 0 < d) (h1 : d < 1)
    (h0' : 0 < d') (h1' : d' < 1) (hle : d ≤ d') : mzsValue a d ≤ mzsValue a d' := by
  rcases eq_or_lt_of_le hle with h | h
  · rw [h]
  · exact le_of_lt (mzsValue_strictMonoOn_snd ha0 ha1 ⟨h0, h1⟩ ⟨h0', h1'⟩ h)

theorem mzsValue_strictMonoOn_snd' (ha0 : 0 < a) (ha1 : a < 1) :
    StrictMonoOn (fun t : ℝ => mzsValue a t) (Set.Ioc (0:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc (0:ℝ) 1) (continuousOn_mzsValue_snd a)
  intro x hx
  rw [interior_Ioc] at hx
  rw [(hasDerivAt_mzsValue_snd ha0 ha1 hx.1 hx.2).deriv]
  have hnum := mzs_deriv_num_pos ha0 ha1 hx.1 hx.2
  have hden : (0:ℝ) < (1 + a) * (1 + x) ^ 2 := by nlinarith [hx.1]
  exact div_pos hnum hden

/-- `mzsValue a d < zsRate a` for `d < 1`: the deterministic `V`-side is the
extreme case of `(D′)`. -/
theorem mzsValue_lt_zsRate (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    mzsValue a d < zsRate a := by
  rw [← mzsValue_at_one ha0 ha1]
  exact mzsValue_strictMonoOn_snd' ha0 ha1 ⟨hd0, le_of_lt hd1⟩ ⟨one_pos, le_refl 1⟩ hd1

/-! ### The corner bound -/

/-- **`(D′)`.**  If the `V`-side has an atom at `±1` and both rate constraints
are met from below, the value is at least `mzsValue a d`.  Mirror of
`cornerBound`: `bestResponse_ge_of_certificate` with `MDFun_nonpos`, reflected
by `σ`, then tightness and monotonicity. -/
theorem cornerBoundMin {cL cR : Chan} (ha0 : 0 < a) (ha1 : a < 1)
    (hd0 : 0 < d) (hd1 : d < 1) (hpi : ∀ u, 0 < marg₁ (jointUX cL) u)
    (hrho : ∀ v, 0 < marg₂ (jointYV cR) v) (hc : VSideCorner cR)
    (hCu : zsRate a ≤ mutualInfo (jointUX cL))
    (hCv : zsRate d ≤ mutualInfo (jointYV cR)) :
    mzsValue a d ≤ mutualInfo (jointUV 0 cL cR) := by
  obtain ⟨d', σ, hd0', hd1', hσ, hrate, hphi⟩ := corner_phiZ hrho hc
  -- `d' = 1` — a deterministic `V`-side — is allowed here, unlike in `cornerBound`
  by_cases hd'1 : d' = 1
  · subst hd'1
    have hker : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u
        * biasOfSnd (jointYV cR) v := by
      intro u v
      have hnnL : ∀ u x, 0 ≤ jointUX cL u x := by
        intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
      have hnnR : ∀ v y, 0 ≤ (fun v y => jointYV cR y v) v y := by
        intro v y; simp only [jointYV]; have := cR.nonneg y v; linarith
      obtain ⟨h1, h2⟩ := biasOf_mem_Icc hnnL (hpi u)
      obtain ⟨h3, h4⟩ := by
        have h := biasOf_mem_Icc (q := fun v y => jointYV cR y v) hnnR (u := v) (by
          simpa [marg₁, marg₂] using hrho v)
        exact (show -1 ≤ biasOfSnd (jointYV cR) v ∧ biasOfSnd (jointYV cR) v ≤ 1 by
          simpa [biasOf, biasOfSnd, marg₁, marg₂] using h)
      nlinarith
    have hbound := bestResponse_ge_of_certificate (p := 0) (l₀ := 0) (l₁ := 0) (l₂ := 1)
      hpi hrho hker zero_le_one ?_ hCu
    · have := mzsValue_lt_zsRate ha0 ha1 hd0 hd1
      linarith
    · intro s hs0 hs1
      have hL : (1 - 2 * (0:ℝ)) * s = s := by ring
      simp only [hL]
      rw [hphi s]
      have hP : phiZ 1 (σ * s) = fe s := by
        have : fe (σ * s) = fe s := by rcases hσ with h | h <;> subst h <;> simp [fe_neg]
        rw [← this]
        simp only [phiZ, fe, fFun]
        norm_num
        ring
      rw [hP]; linarith
  have hd'lt : d' < 1 := lt_of_le_of_ne hd1' hd'1
  have hdd : d ≤ d' := by
    apply le_of_zsRate_le hd0 hd1 hd0' hd'lt
    rw [← hrate]; exact hCv
  have hnnL : ∀ u x, 0 ≤ jointUX cL u x := by
    intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
  have hnnR : ∀ v y, 0 ≤ (fun v y => jointYV cR y v) v y := by
    intro v y; simp only [jointYV]; have := cR.nonneg y v; linarith
  have hbdL : ∀ u, -1 ≤ biasOf (jointUX cL) u ∧ biasOf (jointUX cL) u ≤ 1 :=
    fun u => biasOf_mem_Icc hnnL (hpi u)
  have hbdR : ∀ v, -1 ≤ biasOfSnd (jointYV cR) v ∧ biasOfSnd (jointYV cR) v ≤ 1 := by
    intro v
    have h := biasOf_mem_Icc (q := fun v y => jointYV cR y v) hnnR (u := v) (by
      simpa [marg₁, marg₂] using hrho v)
    simpa [biasOf, biasOfSnd, marg₁, marg₂] using h
  have hker : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u
      * biasOfSnd (jointYV cR) v := by
    intro u v
    obtain ⟨h1, h2⟩ := hbdL u
    obtain ⟨h3, h4⟩ := hbdR v
    nlinarith
  have hbound := bestResponse_ge_of_certificate (p := 0) (l₀ := mlam0 a d')
    (l₁ := σ * mlam1 a d') (l₂ := mlam2 a d') hpi hrho hker
    (le_of_lt (mlam2_pos ha0 ha1 hd0' hd'lt)) ?_ hCu
  · have ht := certificate_tight_mirror ha0 ha1 hd0' hd'lt
    have hm := mzsValue_mono_snd ha0 ha1 hd0 hd1 hd0' hd'lt hdd
    linarith
  · intro s hs0 hs1
    have hσs0 : -1 ≤ σ * s := by rcases hσ with h | h <;> subst h <;> linarith
    have hσs1 : σ * s ≤ 1 := by rcases hσ with h | h <;> subst h <;> linarith
    have hcert := MDFun_nonpos ha0 ha1 hd0' hd'lt hσs0 hσs1
    rw [MDFun, GFun] at hcert
    have hfe : fe (σ * s) = fe s := by
      rcases hσ with h | h <;> subst h <;> simp [fe_neg]
    have hL : (1 - 2 * (0:ℝ)) * s = s := by ring
    simp only [hL]
    rw [hphi s]
    rw [hfe] at hcert
    have hmul : σ * mlam1 a d' * s = mlam1 a d' * (σ * s) := by ring
    rw [hmul]
    linarith

/-! ### The mirror of `(D′)`

`mzsValue` is symmetric — its closed form `mzsNum a d / ((1+a)(1+d))` has
`mzsNum a d = mzsNum d a` termwise — so the side-swap of `CFinish.lean` gives
the `U`-side corner bound for free. -/

theorem mzsNum_symm (a d : ℝ) : mzsNum a d = mzsNum d a := by
  simp only [mzsNum]
  rw [show d * a = a * d by ring]
  ring

theorem mzsValue_symm (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    mzsValue a d = mzsValue d a := by
  rw [mzsValue_eq ha0 ha1 hd0 hd1, mzsValue_eq hd0 hd1 ha0 ha1, mzsNum_symm]
  ring_nf

/-- **The mirror of `(D′)`.** -/
theorem cornerBoundMinU {cL cR : Chan} (ha0 : 0 < a) (ha1 : a < 1)
    (hd0 : 0 < d) (hd1 : d < 1) (hpi : ∀ u, 0 < marg₁ (jointUX cL) u)
    (hrho : ∀ v, 0 < marg₂ (jointYV cR) v) (hc : USideCorner cL)
    (hCu : zsRate a ≤ mutualInfo (jointUX cL))
    (hCv : zsRate d ≤ mutualInfo (jointYV cR)) :
    mzsValue a d ≤ mutualInfo (jointUV 0 cL cR) := by
  have hCu' : zsRate d ≤ mutualInfo (jointUX cR) := by
    rw [mutualInfo_jointUX_eq_jointYV]; exact hCv
  have hCv' : zsRate a ≤ mutualInfo (jointYV cL) := by
    rw [← mutualInfo_jointUX_eq_jointYV]; exact hCu
  have h := cornerBoundMin hd0 hd1 ha0 ha1 hrho hpi hc hCu' hCv'
  rwa [mutualInfo_jointUV_symm, ← mzsValue_symm ha0 ha1 hd0 hd1] at h

/-! ## `(C′)`: the BSC pair is not a minimiser

The mirror of `(C)`, and **cheaper**: for the maximisation the second-order gain
had to come from the indefinite direction of the Hessian, which is exactly the
saddle inequality `(iii)`.  For the minimisation a *pure `U`-side* perturbation
suffices — `d₂ = 0` gives `form = F_pp < 0` — so `(C′)` needs only `Fpp_neg`,
not `saddle_iii`.

The corrections now push both rates *up* (feasible for `R ≥ C`) while the value
still drops. -/

theorem not_min_of_second_order2 {gain gain' fU fU' fV fV' : ℝ → ℝ} {c cU cV : ℝ}
    (hg : ∀ᶠ x in nhds (0:ℝ), HasDerivAt gain (gain' x) x) (hg0 : gain 0 = 0)
    (hg'0 : gain' 0 = 0) (hg' : HasDerivAt gain' c 0) (hc : c < 0)
    (hU : ∀ᶠ x in nhds (0:ℝ), HasDerivAt fU (fU' x) x) (hU0 : fU 0 = 0)
    (hU'0 : fU' 0 = 0) (hU' : HasDerivAt fU' cU 0) (hcU : 0 < cU)
    (hV : ∀ᶠ x in nhds (0:ℝ), HasDerivAt fV (fV' x) x) (hV0 : fV 0 = 0)
    (hV'0 : fV' 0 = 0) (hV' : HasDerivAt fV' cV 0) (hcV : 0 < cV)
    (hmin : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 ≤ fU ε → 0 ≤ fV ε → 0 ≤ gain ε) :
    False := by
  have h1 := neg_of_second_deriv_neg hg hg0 hg'0 hg' hc
  have h2 := pos_of_second_deriv_pos hU hU0 hU'0 hU' hcU
  have h3 := pos_of_second_deriv_pos hV hV0 hV'0 hV' hcV
  obtain ⟨ε, ⟨⟨hε1, hε2⟩, hε3⟩, hε4⟩ := (((h1.and h2).and h3).and hmin).exists
  exact absurd (hε4 (le_of_lt hε2) (le_of_lt hε3)) (not_le.mpr hε1)

/-- The value of an atom-built pair is at least a minimiser's value. -/
theorem curve_min_bound {Cu Cv : ℝ} {cL cR : Chan} (hmn : IsMinPairC Cu Cv cL cR)
    {a b c e : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0) (hb1 : -1 < b)
    (hc0 : 0 < c) (hc1 : c < 1) (he0 : e < 0) (he1 : -1 < e)
    (hRU : Cu ≤ (-b / (a - b)) * fe a + (a / (a - b)) * fe b)
    (hRV : Cv ≤ (-e / (c - e)) * fe c + (c / (c - e)) * fe e) :
    mutualInfo (jointUV 0 cL cR)
      ≤ (-b / (a - b)) * ((-e / (c - e)) * fFun (a * c) + (c / (c - e)) * fFun (a * e))
        + (a / (a - b)) * ((-e / (c - e)) * fFun (b * c) + (c / (c - e)) * fFun (b * e)) := by
  have hfeas : FeasibleMin Cu Cv (chanOfAtoms ha0 ha1 hb0 hb1) (chanOfAtomsV hc0 hc1 he0 he1) := by
    constructor
    · rw [rate_pair_atoms ha0 ha1 hb0 hb1]; exact hRU
    · rw [rateV_pair_atoms hc0 hc1 he0 he1]; exact hRV
  have h := hmn.2 _ _ hfeas
  rwa [value_pair_atoms ha0 ha1 hb0 hb1 hc0 hc1 he0 he1] at h

/-- Mirror of `hmax_discharge`. -/
theorem hmin_discharge {Cu Cv : ℝ} {cL cR : Chan} {s t d₁ d₂ e₁ e₂ f₁ f₂ : ℝ}
    (hmn : IsMinPairC Cu Cv cL cR) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hRU : Cu ≤ rateCurve s d₁ e₁ e₂ 0) (hRV : Cv ≤ rateCurve t d₂ f₁ f₂ 0) :
    ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      0 ≤ rateCurve s d₁ e₁ e₂ ε - rateCurve s d₁ e₁ e₂ 0 →
      0 ≤ rateCurve t d₂ f₁ f₂ ε - rateCurve t d₂ f₁ f₂ 0 →
      0 ≤ valueCurve s t d₁ d₂ e₁ e₂ f₁ f₂ ε - mutualInfo (jointUV 0 cL cR) := by
  have hev : ∀ᶠ ε in nhds (0:ℝ),
      (0 < atomC s d₁ e₁ ε ∧ atomC s d₁ e₁ ε < 1)
      ∧ (atomC (-s) d₁ e₂ ε < 0 ∧ -1 < atomC (-s) d₁ e₂ ε)
      ∧ (0 < atomC t d₂ f₁ ε ∧ atomC t d₂ f₁ ε < 1)
      ∧ (atomC (-t) d₂ f₂ ε < 0 ∧ -1 < atomC (-t) d₂ f₂ ε) := by
    filter_upwards [atom_pos_eventually (d := d₁) (e := e₁) hs0 hs1,
      atom_neg_eventually (d := d₁) (e := e₂) (by linarith : (-s) < 0) (by linarith),
      atom_pos_eventually (d := d₂) (e := f₁) ht0 ht1,
      atom_neg_eventually (d := d₂) (e := f₂) (by linarith : (-t) < 0) (by linarith)]
      with ε h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩
  filter_upwards [nhdsWithin_le_nhds hev] with ε ⟨⟨pa0, pa1⟩, ⟨pb0, pb1⟩, ⟨pc0, pc1⟩, ⟨pd0, pd1⟩⟩
    hU hV
  have hgU : atomC s d₁ e₁ ε - atomC (-s) d₁ e₂ ε ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hgV : atomC t d₂ f₁ ε - atomC (-t) d₂ f₂ ε ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hRU' : Cu ≤ (-(atomC (-s) d₁ e₂ ε) / (atomC s d₁ e₁ ε - atomC (-s) d₁ e₂ ε))
        * fe (atomC s d₁ e₁ ε)
      + (atomC s d₁ e₁ ε / (atomC s d₁ e₁ ε - atomC (-s) d₁ e₂ ε))
        * fe (atomC (-s) d₁ e₂ ε) := by
    rw [← rateCurve_eq hgU]; linarith
  have hRV' : Cv ≤ (-(atomC (-t) d₂ f₂ ε) / (atomC t d₂ f₁ ε - atomC (-t) d₂ f₂ ε))
        * fe (atomC t d₂ f₁ ε)
      + (atomC t d₂ f₁ ε / (atomC t d₂ f₁ ε - atomC (-t) d₂ f₂ ε))
        * fe (atomC (-t) d₂ f₂ ε) := by
    rw [← rateCurve_eq hgV]; linarith
  have h := curve_min_bound hmn pa0 pa1 pb0 pb1 pc0 pc1 pd0 pd1 hRU' hRV'
  rw [← valueCurve_eq hgU hgV] at h
  linarith

theorem curve_contradiction_min {s t d₁ d₂ e₁ e₂ f₁ f₂ Vstar : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hV0 : Vstar = (1 / 2 : ℝ) * (fFun (s * t) + fFun (-(s * t))))
    (hgainneg : 2 * d₁ * d₂ * Core.Fpq s t
        + (t ^ 2 * d₁ ^ 2 + s ^ 2 * d₂ ^ 2)
          * (1 / (1 - (s * t) ^ 2) - 2 * Real.artanh (s * t) / (s * t))
        + Real.artanh (s * t) * (t * (e₁ - e₂) + s * (f₁ - f₂)) < 0)
    (hUpos : 0 < d₁ ^ 2 * (1 / (1 - s ^ 2) - 2 * Real.artanh s / s)
        + Real.artanh s * (e₁ - e₂))
    (hVpos : 0 < d₂ ^ 2 * (1 / (1 - t ^ 2) - 2 * Real.artanh t / t)
        + Real.artanh t * (f₁ - f₂))
    (hmin : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      0 ≤ rateCurve s d₁ e₁ e₂ ε - rateCurve s d₁ e₁ e₂ 0 →
      0 ≤ rateCurve t d₂ f₁ f₂ ε - rateCurve t d₂ f₁ f₂ 0 →
      0 ≤ valueCurve s t d₁ d₂ e₁ e₂ f₁ f₂ ε - Vstar) : False := by
  refine not_min_of_second_order2
    (gain := fun ε => valueCurve s t d₁ d₂ e₁ e₂ f₁ f₂ ε - Vstar)
    (gain' := valueCurve' s t d₁ d₂ e₁ e₂ f₁ f₂)
    (fU := fun ε => rateCurve s d₁ e₁ e₂ ε - rateCurve s d₁ e₁ e₂ 0)
    (fU' := rateCurve' s d₁ e₁ e₂)
    (fV := fun ε => rateCurve t d₂ f₁ f₂ ε - rateCurve t d₂ f₁ f₂ 0)
    (fV' := rateCurve' t d₂ f₁ f₂)
    ?_ ?_ (valueCurve'_zero hs0 ht0) (hasDerivAt_valueCurve' hs0 hs1 ht0 ht1) hgainneg
    ?_ (by ring) (rateCurve'_zero hs0 hs1) (hasDerivAt_rateCurve' hs0 hs1) hUpos
    ?_ (by ring) (rateCurve'_zero ht0 ht1) (hasDerivAt_rateCurve' ht0 ht1) hVpos hmin
  · filter_upwards [hasDerivAt_valueCurve hs0 hs1 ht0 ht1] with ε hε using hε.sub_const Vstar
  · rw [hV0, valueCurve_zero hs0 ht0]; ring
  · filter_upwards [hasDerivAt_rateCurve (e₁ := e₁) (e₂ := e₂) hs0 hs1] with ε hε
      using hε.sub_const _
  · filter_upwards [hasDerivAt_rateCurve (e₁ := f₁) (e₂ := f₂) ht0 ht1] with ε hε
      using hε.sub_const _

/-- Mirror of `exists_good_corrections`: with the Hessian form **negative**, the
rate drift can be made strictly positive on both sides while the value gain
stays strictly negative. -/
theorem exists_bad_corrections {Vlin RlinU RlinV lamU lamV form : ℝ}
    (hlamU : 0 ≤ lamU) (hlamV : 0 ≤ lamV)
    (hform : Vlin - lamU * RlinU - lamV * RlinV = form) (hneg : form < 0) :
    ∃ A B : ℝ, 0 < RlinU + A ∧ 0 < RlinV + B ∧ Vlin + lamU * A + lamV * B < 0 := by
  set η := -form / (2 * (lamU + lamV + 1)) with hη
  have hden : (0:ℝ) < 2 * (lamU + lamV + 1) := by linarith
  have hη0 : 0 < η := by rw [hη]; exact div_pos (by linarith) hden
  refine ⟨-RlinU + η, -RlinV + η, by linarith, by linarith, ?_⟩
  have hkey : Vlin + lamU * (-RlinU + η) + lamV * (-RlinV + η)
      = form + (lamU + lamV) * η := by rw [← hform]; ring
  rw [hkey]
  have hbound : (lamU + lamV) * η ≤ -form / 2 := by
    rw [hη, mul_div_assoc']
    rw [div_le_div_iff₀ hden (by norm_num)]
    nlinarith [hneg, hlamU, hlamV]
  linarith

theorem exists_curve_corrections_min {s t d₁ d₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hform : Core.Fpp s t * d₁ ^ 2 + 2 * Core.Fpq s t * d₁ * d₂
      + Core.Fqq s t * d₂ ^ 2 < 0) :
    ∃ e₁ e₂ f₁ f₂ : ℝ,
      (0 < d₁ ^ 2 * (1 / (1 - s ^ 2) - 2 * Real.artanh s / s)
          + Real.artanh s * (e₁ - e₂))
        ∧ (0 < d₂ ^ 2 * (1 / (1 - t ^ 2) - 2 * Real.artanh t / t)
          + Real.artanh t * (f₁ - f₂))
        ∧ (2 * d₁ * d₂ * Core.Fpq s t
          + (t ^ 2 * d₁ ^ 2 + s ^ 2 * d₂ ^ 2)
            * (1 / (1 - (s * t) ^ 2) - 2 * Real.artanh (s * t) / (s * t))
          + Real.artanh (s * t) * (t * (e₁ - e₂) + s * (f₁ - f₂)) < 0) := by
  have hst : 0 < s * t := mul_pos hs0 ht0
  have hst1 : s * t < 1 := by nlinarith
  have has : 0 < Real.artanh s := Real.artanh_pos ⟨hs0, hs1⟩
  have hat : 0 < Real.artanh t := Real.artanh_pos ⟨ht0, ht1⟩
  have hax : 0 < Real.artanh (s * t) := Real.artanh_pos ⟨hst, hst1⟩
  have hlamU : (0:ℝ) ≤ t * Real.artanh (s * t) / Real.artanh s := by positivity
  have hlamV : (0:ℝ) ≤ s * Real.artanh (s * t) / Real.artanh t := by positivity
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_bad_corrections hlamU hlamV
    (Vlin := 2 * d₁ * d₂ * Core.Fpq s t
      + (t ^ 2 * d₁ ^ 2 + s ^ 2 * d₂ ^ 2)
        * (1 / (1 - (s * t) ^ 2) - 2 * Real.artanh (s * t) / (s * t)))
    (RlinU := d₁ ^ 2 * (1 / (1 - s ^ 2) - 2 * Real.artanh s / s))
    (RlinV := d₂ ^ 2 * (1 / (1 - t ^ 2) - 2 * Real.artanh t / t))
    (form := Core.Fpp s t * d₁ ^ 2 + 2 * Core.Fpq s t * d₁ * d₂ + Core.Fqq s t * d₂ ^ 2)
    (total_second_order_eq hs0 hs1 ht0 ht1 (ne_of_gt has) (ne_of_gt hat)) hform
  have hns : Real.artanh s ≠ 0 := ne_of_gt has
  have hnt : Real.artanh t ≠ 0 := ne_of_gt hat
  refine ⟨A / Real.artanh s, 0, B / Real.artanh t, 0, ?_, ?_, ?_⟩
  · have : Real.artanh s * (A / Real.artanh s - 0) = A := by
      rw [sub_zero]; field_simp
    rw [this]; linarith
  · have : Real.artanh t * (B / Real.artanh t - 0) = B := by
      rw [sub_zero]; field_simp
    rw [this]; linarith
  · have hexp : Real.artanh (s * t)
          * (t * (A / Real.artanh s - 0) + s * (B / Real.artanh t - 0))
        = (t * Real.artanh (s * t) / Real.artanh s) * A
          + (s * Real.artanh (s * t) / Real.artanh t) * B := by
      field_simp; ring
    rw [hexp]; linarith

/-- **`(C′)` at the level of biases.**  A pair whose bias magnitudes are `s` and
`t` in `(0,1)`, with the BSC value, cannot be a minimiser. -/
theorem symmetric_not_min {Cu Cv : ℝ} {cL cR : Chan} {s t : ℝ}
    (hmn : IsMinPairC Cu Cv cL cR) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hRU : Cu ≤ fe s) (hRV : Cv ≤ fe t)
    (hV0 : mutualInfo (jointUV 0 cL cR)
      = (1 / 2 : ℝ) * (fFun (s * t) + fFun (-(s * t)))) : False := by
  have hform : Core.Fpp s t * (1:ℝ) ^ 2 + 2 * Core.Fpq s t * (1:ℝ) * 0
      + Core.Fqq s t * (0:ℝ) ^ 2 < 0 := by
    have h := Core.Fpp_neg hs0 hs1 ht0 ht1
    nlinarith [h]
  obtain ⟨e₁, e₂, f₁, f₂, hU, hV, hG⟩ :=
    exists_curve_corrections_min (d₁ := 1) (d₂ := 0) hs0 hs1 ht0 ht1 hform
  refine curve_contradiction_min hs0 hs1 ht0 ht1 hV0 hG hU hV ?_
  refine hmin_discharge hmn hs0 hs1 ht0 ht1 ?_ ?_
  · rw [rateCurve_zero hs0]; exact hRU
  · rw [rateCurve_zero ht0]; exact hRV

/-! ## The assembly -/

theorem zsRate_pos (ha0 : 0 < a) (ha1 : a < 1) : 0 < zsRate a := by
  have h1a : (0:ℝ) < 1 + a := by linarith
  have key : ∀ x : ℝ, 0 < x → x - 1 ≤ x * Real.log x := by
    intro x hx
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / x by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hx), Real.log_one, zero_sub] at h
    have h2 : x * (-Real.log x) ≤ x * (1 / x - 1) := mul_le_mul_of_nonneg_left h (le_of_lt hx)
    have h3 : x * (1 / x - 1) = 1 - x := by field_simp
    rw [h3] at h2; linarith
  have hP : 0 ≤ fe a := by
    have k1 := key (1 + a) (by linarith)
    have k2 := key (1 - a) (by linarith)
    rw [fe]; linarith
  have hlog : 0 < a * Real.log 2 := by
    have := Real.log_two_gt_d9; positivity
  rw [zsRate]
  positivity

theorem mutualInfo_jointUX_eq_zero_of_deg {cL : Chan} {u₀ : Bool}
    (h : marg₁ (jointUX cL) u₀ = 0) : mutualInfo (jointUX cL) = 0 := by
  have hnn0 := cL.nonneg false u₀
  have hnn1 := cL.nonneg true u₀
  have h' : cL.tr false u₀ + cL.tr true u₀ = 0 := by
    simp only [marg₁, jointUX] at h; linarith
  have hz0 : cL.tr false u₀ = 0 := by linarith
  have hz1 : cL.tr true u₀ = 0 := by linarith
  refine mutualInfo_eq_zero_of_row_zero (u₀ := u₀) (fun x => by
    simp only [jointUX]; cases x <;> simp [hz0, hz1]) ?_
  have h0 := cL.sum_one false
  have h1 := cL.sum_one true
  simp only [jointUX]
  linarith

theorem mutualInfo_jointYV_eq_zero_of_deg {cR : Chan} {v₀ : Bool}
    (h : marg₂ (jointYV cR) v₀ = 0) : mutualInfo (jointYV cR) = 0 := by
  have hnn0 := cR.nonneg v₀ false
  have hnn1 := cR.nonneg v₀ true
  rw [← mutualInfo_transpose (jointYV cR)]
  refine mutualInfo_eq_zero_of_row_zero (u₀ := v₀) (fun y => ?_) ?_
  · have h' : cR.tr false v₀ + cR.tr true v₀ = 0 := by
      simp only [marg₂, jointYV] at h; linarith
    have hz0 : cR.tr false v₀ = 0 := by
      have := cR.nonneg false v₀; have := cR.nonneg true v₀; linarith
    have hz1 : cR.tr true v₀ = 0 := by
      have := cR.nonneg false v₀; have := cR.nonneg true v₀; linarith
    simp only [jointYV]; cases y <;> simp [hz0, hz1]
  · have h0 := cR.sum_one false
    have h1 := cR.sum_one true
    simp only [jointYV]
    linarith

/-- **`(C′)` as a statement about BSC pairs.**  A non-corner BSC pair is not a
minimiser. -/
theorem bscNotMin (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    {cL cR : Chan} (hmn : IsMinPairC (zsRate a) (zsRate d) cL cR)
    (hUc : ¬ USideCorner cL) (hVc : ¬ VSideCorner cR) : ¬ BothBSC cL cR := by
  rintro ⟨⟨α, hα0, hα1, rfl⟩, β, hβ0, hβ1, rfl⟩
  have hrU : mutualInfo (jointUX (bsc α hα0 hα1)) = fe (1 - 2 * α) := by
    rw [mutualInfo_jointUX_bsc hα0 hα1, fe_one_sub_two_mul hα0 hα1]
  have hrV : mutualInfo (jointYV (bsc β hβ0 hβ1)) = fe (1 - 2 * β) := by
    rw [mutualInfo_jointYV_bsc hβ0 hβ1, fe_one_sub_two_mul hβ0 hβ1]
  have hbc0 : 0 ≤ α ⊛ β := bconv_nonneg hα0 hα1 hβ0 hβ1
  have hbc1 : α ⊛ β ≤ 1 := bconv_le_one hα0 hα1 hβ0 hβ1
  have hval : mutualInfo (jointUV 0 (bsc α hα0 hα1) (bsc β hβ0 hβ1))
      = fe ((1 - 2 * α) * (1 - 2 * β)) := by
    have hz : α ⊛ (0:ℝ) = α := by simp [bconv]
    rw [mutualInfo_jointUV_bsc hα0 hα1 hβ0 hβ1 le_rfl zero_le_one, hz,
      ← fe_one_sub_two_mul hbc0 hbc1, one_sub_two_mul_bconv]
  have hUlt : zsRate a ≤ fe (1 - 2 * α) := by rw [← hrU]; exact hmn.1.1
  have hVlt : zsRate d ≤ fe (1 - 2 * β) := by rw [← hrV]; exact hmn.1.2
  obtain ⟨hbU1, hbU0⟩ := biasOf_bsc hα0 hα1
  obtain ⟨hbV0, hbV1⟩ := biasOfSnd_bsc hβ0 hβ1
  -- no corner: `|1 − 2α| < 1`
  have hs1 : |1 - 2 * α| < 1 := by
    rcases lt_or_eq_of_le ((abs_le.mpr ⟨by linarith, by linarith⟩ : |1 - 2 * α| ≤ 1)) with h | h
    · exact h
    · exact absurd (⟨false, by rw [hbU0]; exact (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h⟩ :
        USideCorner (bsc α hα0 hα1)) hUc
  have ht1 : |1 - 2 * β| < 1 := by
    rcases lt_or_eq_of_le ((abs_le.mpr ⟨by linarith, by linarith⟩ : |1 - 2 * β| ≤ 1)) with h | h
    · exact h
    · exact absurd (⟨false, by rw [hbV0]; exact (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h⟩ :
        VSideCorner (bsc β hβ0 hβ1)) hVc
  -- non-degenerate: a zero bias would make the rate zero
  have hs0 : 0 < |1 - 2 * α| := by
    rcases eq_or_lt_of_le (abs_nonneg (1 - 2 * α)) with h | h
    · exfalso
      have hz : (1:ℝ) - 2 * α = 0 := abs_eq_zero.mp h.symm
      rw [hz, fe_zero] at hUlt
      linarith [zsRate_pos ha0 ha1]
    · exact h
  have ht0 : 0 < |1 - 2 * β| := by
    rcases eq_or_lt_of_le (abs_nonneg (1 - 2 * β)) with h | h
    · exfalso
      have hz : (1:ℝ) - 2 * β = 0 := abs_eq_zero.mp h.symm
      rw [hz, fe_zero] at hVlt
      linarith [zsRate_pos hd0 hd1]
    · exact h
  refine symmetric_not_min (s := |1 - 2 * α|) (t := |1 - 2 * β|) hmn hs0 hs1 ht0 ht1 ?_ ?_ ?_
  · rw [fe_abs]; exact hUlt
  · rw [fe_abs]; exact hVlt
  · rw [hval, ← fe_eq_half_fFun, ← abs_mul, fe_abs]

/-- **Conjecture 2 of Entropy 24(9):1321, at `p = 0`.** -/
theorem conjecture2_p0_holds : Conjecture2_p0 := by
  intro a d ha0 ha1 hd0 hd1 cL cR hpi hCu hCv
  have hCv' : zsRate d ≤ mutualInfo (jointYV cR) := by
    rw [← sChan_rate hd0 hd1]; exact hCv
  have hfeas : FeasibleMin (zsRate a) (zsRate d) cL cR := ⟨hCu, hCv'⟩
  obtain ⟨cL', cR', hmn⟩ := minExistsC _ _ ⟨cL, cR, hfeas⟩
  have h1 := hmn.2 cL cR hfeas
  refine le_trans ?_ h1
  -- the minimiser is non-degenerate, since the rates are positive
  have hL : ∀ u, 0 < marg₁ (jointUX cL') u := by
    intro u
    rcases lt_or_eq_of_le (show (0:ℝ) ≤ marg₁ (jointUX cL') u by
      simp only [marg₁, jointUX]
      have := cL'.nonneg false u; have := cL'.nonneg true u; linarith) with h | h
    · exact h
    · exfalso
      have := mutualInfo_jointUX_eq_zero_of_deg h.symm
      have := hmn.1.1
      linarith [zsRate_pos ha0 ha1]
  have hR : ∀ v, 0 < marg₂ (jointYV cR') v := by
    intro v
    rcases lt_or_eq_of_le (show (0:ℝ) ≤ marg₂ (jointYV cR') v by
      simp only [marg₂, jointYV]
      have := cR'.nonneg false v; have := cR'.nonneg true v; linarith) with h | h
    · exact h
    · exfalso
      have := mutualInfo_jointYV_eq_zero_of_deg h.symm
      have := hmn.1.2
      linarith [zsRate_pos hd0 hd1]
  by_cases hVc : VSideCorner cR'
  · exact cornerBoundMin ha0 ha1 hd0 hd1 hL hR hVc hmn.1.1 hmn.1.2
  · by_cases hUc : USideCorner cL'
    · exact cornerBoundMinU ha0 ha1 hd0 hd1 hL hR hUc hmn.1.1 hmn.1.2
    · -- no corner: `(B′)` makes it a BSC pair, `(C′)` says it is not a minimum
      exfalso
      have hdeg : biasOf (jointUX cL') true ≠ 0 := by
        intro h
        have hz := value_zero_of_bias_zero hL hR (bias_all_zero hL h)
        have hrz : mutualInfo (jointUX cL') = 0 := by
          have hb := bias_all_zero hL h
          have := mutualInfo_jointUX_eq_bias_closed hL
          rw [hb false, hb true, fe_zero] at this
          simpa using this
        have := hmn.1.1
        linarith [zsRate_pos ha0 ha1]
      have hdegV : biasOfSnd (jointYV cR') false ≠ 0 := by
        intro h
        have hmz := rho_bias_sum_zero cR' (hR false) (hR true)
        rw [h, mul_zero, zero_add] at hmz
        have hv1 : biasOfSnd (jointYV cR') true = 0 :=
          (mul_eq_zero.mp hmz).resolve_left (ne_of_gt (hR true))
        have hrz : mutualInfo (jointYV cR') = 0 := by
          have := mutualInfo_jointYV_eq_bias_closed hR
          rw [h, hv1, fe_zero] at this
          simpa using this
        have := hmn.1.2
        linarith [zsRate_pos hd0 hd1]
      exact absurd (interiorIsBSC_of_noCorner (Or.inr hmn) hL hR hUc hVc hdeg hdegV)
        (bscNotMin ha0 ha1 hd0 hd1 hmn hUc hVc)

end BSCAveraging
