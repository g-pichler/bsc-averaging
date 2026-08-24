import BSCAveraging.BFinish

/-! # `(B)`: the `V`-side mirror

Same statements as `BFinish.lean` with `jointYV`/`marg₂`/`biasOfSnd` in place of
`jointUX`/`marg₁`/`biasOf`.  The positive `V`-atom sits at index `false`, so the
two-atom pair is `(c, d) = (biasOfSnd false, biasOfSnd true)` with `c > 0 > d`. -/

namespace BSCAveraging

open BSCAveraging.KKT

/-- The `V`-side atom value: `ψ_S(t) = Σ_u π_u f(s_u t)`. -/
noncomputable def atomValueV (cL : Chan) (t : ℝ) : ℝ :=
  marg₁ (jointUX cL) false * fFun (biasOf (jointUX cL) false * t)
    + marg₁ (jointUX cL) true * fFun (biasOf (jointUX cL) true * t)

/-- The `V`-side rate as `twoAtomL f_e`. -/
theorem mutualInfo_jointYV_eq_twoAtomL {cR : Chan}
    (hpos : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hne : biasOfSnd (jointYV cR) false ≠ biasOfSnd (jointYV cR) true) :
    mutualInfo (jointYV cR)
      = twoAtomL fe (biasOfSnd (jointYV cR) true) (biasOfSnd (jointYV cR) false) := by
  have hsum : marg₂ (jointYV cR) false + marg₂ (jointYV cR) true = 1 := marg₂_jointYV_sum cR
  have hmz : marg₂ (jointYV cR) false * biasOfSnd (jointYV cR) false
      + marg₂ (jointYV cR) true * biasOfSnd (jointYV cR) true = 0 :=
    rho_bias_sum_zero cR (hpos false) (hpos true)
  obtain ⟨e1, e2⟩ := weights_of_mass_mean hne hsum hmz
  rw [mutualInfo_jointYV_eq_bias_closed hpos, twoAtomL, e1, e2]

/-- The value as a `V`-side two-atom functional. -/
theorem mutualInfo_jointUV_eq_twoAtomLV {cL cR : Chan}
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hker : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u
      * biasOfSnd (jointYV cR) v)
    (hne : biasOfSnd (jointYV cR) false ≠ biasOfSnd (jointYV cR) true) :
    mutualInfo (jointUV 0 cL cR)
      = twoAtomL (atomValueV cL) (biasOfSnd (jointYV cR) true)
          (biasOfSnd (jointYV cR) false) := by
  have hsum : marg₂ (jointYV cR) false + marg₂ (jointYV cR) true = 1 := marg₂_jointYV_sum cR
  have hmz : marg₂ (jointYV cR) false * biasOfSnd (jointYV cR) false
      + marg₂ (jointYV cR) true * biasOfSnd (jointYV cR) true = 0 :=
    rho_bias_sum_zero cR (hrho false) (hrho true)
  obtain ⟨e1, e2⟩ := weights_of_mass_mean hne hsum hmz
  rw [mutualInfo_jointUV_eq_kernel_sum_of_nonneg 0 cL cR hpi hrho hker, twoAtomL,
    atomValueV, atomValueV, e1, e2]
  ring_nf

/-! ### The `V`-side channel with prescribed atoms -/

section OfAtomsV

variable {c d : ℝ}

lemma chanOfAtomsV_bounds (hc0 : 0 < c) (hc1 : c < 1) (hd0 : d < 0) (hd1 : -1 < d) :
    0 ≤ 1 - wOf c d * (1 + c) ∧ 1 - wOf c d * (1 + c) ≤ 1 ∧
    0 ≤ 1 - wOf c d * (1 - c) ∧ 1 - wOf c d * (1 - c) ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := chanOfAtoms_bounds hc0 hc1 hd0 hd1
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The `V`-side channel with atoms `c > 0 > d` (positive atom at index `false`). -/
noncomputable def chanOfAtomsV (hc0 : 0 < c) (hc1 : c < 1) (hd0 : d < 0) (hd1 : -1 < d) :
    Chan :=
  chanOf (1 - wOf c d * (1 + c)) (1 - wOf c d * (1 - c))
    (chanOfAtomsV_bounds hc0 hc1 hd0 hd1).1
    (chanOfAtomsV_bounds hc0 hc1 hd0 hd1).2.1
    (chanOfAtomsV_bounds hc0 hc1 hd0 hd1).2.2.1
    (chanOfAtomsV_bounds hc0 hc1 hd0 hd1).2.2.2

lemma marg₂_chanOfAtomsV (hc0 : 0 < c) (hc1 : c < 1) (hd0 : d < 0) (hd1 : -1 < d) :
    marg₂ (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) false = wOf c d ∧
      marg₂ (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) true = 1 - wOf c d := by
  constructor <;>
    · simp only [marg₂, jointYV, chanOfAtomsV, chanOf, chanTr, cond_true, cond_false]
      ring

lemma biasOfSnd_chanOfAtomsV (hc0 : 0 < c) (hc1 : c < 1) (hd0 : d < 0) (hd1 : -1 < d) :
    biasOfSnd (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) false = c ∧
      biasOfSnd (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) true = d := by
  have hw0 := wOf_pos hc0 hd0
  have hw1 := wOf_lt_one hc0 hd0
  obtain ⟨m0, m1⟩ := marg₂_chanOfAtomsV hc0 hc1 hd0 hd1
  have hD : (0:ℝ) < c - d := by linarith
  have hwe : wOf c d = -d / (c - d) := rfl
  constructor
  · rw [biasOfSnd, m0]
    simp only [jointYV, chanOfAtomsV, chanOf, chanTr, cond_true, cond_false]
    field_simp
    ring
  · rw [biasOfSnd, m1]
    simp only [jointYV, chanOfAtomsV, chanOf, chanTr, cond_true, cond_false]
    rw [hwe]
    have h1 : (1:ℝ) - -d / (c - d) = c / (c - d) := by field_simp; ring
    rw [h1]
    field_simp
    ring

lemma marg₂_chanOfAtomsV_pos (hc0 : 0 < c) (hc1 : c < 1) (hd0 : d < 0) (hd1 : -1 < d) :
    ∀ v, 0 < marg₂ (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) v := by
  obtain ⟨m0, m1⟩ := marg₂_chanOfAtomsV hc0 hc1 hd0 hd1
  intro v
  cases v
  · rw [m0]; exact wOf_pos hc0 hd0
  · rw [m1]; linarith [wOf_lt_one hc0 hd0]

theorem rateV_chanOfAtomsV (hc0 : 0 < c) (hc1 : c < 1) (hd0 : d < 0) (hd1 : -1 < d) :
    mutualInfo (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) = twoAtomL fe d c := by
  obtain ⟨e0, e1⟩ := biasOfSnd_chanOfAtomsV hc0 hc1 hd0 hd1
  have hne : biasOfSnd (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) false
      ≠ biasOfSnd (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) true := by
    rw [e0, e1]; intro h; linarith
  rw [mutualInfo_jointYV_eq_twoAtomL (marg₂_chanOfAtomsV_pos hc0 hc1 hd0 hd1) hne, e0, e1]

theorem valueV_chanOfAtomsV {cL : Chan} (hc0 : 0 < c) (hc1 : c < 1) (hd0 : d < 0)
    (hd1 : -1 < d) (hpi : ∀ u, 0 < marg₁ (jointUX cL) u)
    (hker : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u
      * biasOfSnd (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) v) :
    mutualInfo (jointUV 0 cL (chanOfAtomsV hc0 hc1 hd0 hd1))
      = twoAtomL (atomValueV cL) d c := by
  obtain ⟨e0, e1⟩ := biasOfSnd_chanOfAtomsV hc0 hc1 hd0 hd1
  have hne : biasOfSnd (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) false
      ≠ biasOfSnd (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) true := by
    rw [e0, e1]; intro h; linarith
  rw [mutualInfo_jointUV_eq_twoAtomLV hpi (marg₂_chanOfAtomsV_pos hc0 hc1 hd0 hd1) hker hne,
    e0, e1]

end OfAtomsV

/-! ### The `V`-side derivative and stationarity -/

/-- The derivative of the `V`-side atom value. -/
noncomputable def atomValueV' (cL : Chan) (t : ℝ) : ℝ :=
  marg₁ (jointUX cL) false * biasOf (jointUX cL) false
      * (Real.log (1 + biasOf (jointUX cL) false * t) + 1)
    + marg₁ (jointUX cL) true * biasOf (jointUX cL) true
      * (Real.log (1 + biasOf (jointUX cL) true * t) + 1)

lemma hasDerivAt_atomValueV {cL : Chan} {t : ℝ} (ht : |t| < 1)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) :
    HasDerivAt (atomValueV cL) (atomValueV' cL t) t := by
  have hnn : ∀ u x, 0 ≤ jointUX cL u x := by
    intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
  have hb : ∀ u, |biasOf (jointUX cL) u| ≤ 1 := by
    intro u
    have h := biasOf_mem_Icc hnn (hpi u)
    rw [abs_le]; exact ⟨h.1, h.2⟩
  have hpos : ∀ u, 0 < 1 + biasOf (jointUX cL) u * t := by
    intro u
    have h1 : |biasOf (jointUX cL) u * t| < 1 := by
      calc |biasOf (jointUX cL) u * t| = |biasOf (jointUX cL) u| * |t| := abs_mul _ _
        _ ≤ 1 * |t| := by apply mul_le_mul_of_nonneg_right (hb u) (abs_nonneg t)
        _ < 1 := by simpa using ht
    linarith [(abs_lt.mp h1).1]
  have hd : ∀ u, HasDerivAt (fun t : ℝ => fFun (biasOf (jointUX cL) u * t))
      ((Real.log (1 + biasOf (jointUX cL) u * t) + 1) * biasOf (jointUX cL) u) t := by
    intro u
    have hin : HasDerivAt (fun t : ℝ => biasOf (jointUX cL) u * t)
        (biasOf (jointUX cL) u) t := by
      simpa using (hasDerivAt_id t).const_mul (biasOf (jointUX cL) u)
    have h := (hasDerivAt_fFun (hpos u)).comp t hin
    rwa [Function.comp_def] at h
  have := ((hd false).const_mul (marg₁ (jointUX cL) false)).add
    ((hd true).const_mul (marg₁ (jointUX cL) true))
  refine hd_congr this ?_
  rw [atomValueV']
  ring

lemma eventually_atomsV {c d d₁ d₂ : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hd0 : d < 0)
    (hd1 : -1 < d) :
    ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      0 < c + t * d₁ ∧ c + t * d₁ < 1 ∧ d + t * d₂ < 0 ∧ -1 < d + t * d₂ :=
  eventually_atoms hc0 hc1 hd0 hd1

/-- **`(B)`'s first-order condition on the `V` side.** -/
theorem stationary_of_maximiserV {Cu Cv : ℝ} {cL cR : Chan} {c d : ℝ}
    (hmx : OptPairC Cu Cv cL cR)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hc : biasOfSnd (jointYV cR) false = c) (hd : biasOfSnd (jointYV cR) true = d)
    (hc0 : 0 < c) (hc1 : c < 1) (hd0 : d < 0) (hd1 : -1 < d) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      Dfst (atomValueV cL) (atomValueV' cL) c d = lam * Dfst fe Real.artanh c d
      ∧ Dsnd (atomValueV cL) (atomValueV' cL) c d = lam * Dsnd fe Real.artanh c d := by
  have hcd : d < c := by linarith
  have hne : biasOfSnd (jointYV cR) false ≠ biasOfSnd (jointYV cR) true := by
    rw [hc, hd]; intro h; linarith
  have hnn : ∀ u x, 0 ≤ jointUX cL u x := by
    intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
  have hbL : ∀ u, |biasOf (jointUX cL) u| ≤ 1 := by
    intro u
    have h := biasOf_mem_Icc hnn (hpi u)
    rw [abs_le]; exact ⟨h.1, h.2⟩
  have hkerOf : ∀ {c' d' : ℝ} (p1 : 0 < c') (p2 : c' < 1) (p3 : d' < 0) (p4 : -1 < d'),
      ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u
        * biasOfSnd (jointYV (chanOfAtomsV p1 p2 p3 p4)) v := by
    intro c' d' p1 p2 p3 p4 u v
    obtain ⟨e0, e1⟩ := biasOfSnd_chanOfAtomsV p1 p2 p3 p4
    have hs : |biasOfSnd (jointYV (chanOfAtomsV p1 p2 p3 p4)) v| ≤ 1 := by
      cases v
      · rw [e0, abs_le]; constructor <;> linarith
      · rw [e1, abs_le]; constructor <;> linarith
    have hbnd : |(1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u
        * biasOfSnd (jointYV (chanOfAtomsV p1 p2 p3 p4)) v| ≤ 1 := by
      rw [abs_mul, abs_mul, show |(1 - 2 * (0:ℝ))| = 1 by norm_num, one_mul]
      calc |biasOf (jointUX cL) u| * |biasOfSnd (jointYV (chanOfAtomsV p1 p2 p3 p4)) v|
          ≤ 1 * 1 := mul_le_mul (hbL u) hs (abs_nonneg _) zero_le_one
        _ = 1 := by ring
    linarith [(abs_le.mp hbnd).1]
  have hkerR : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u
      * biasOfSnd (jointYV cR) v := by
    intro u v
    have hs : |biasOfSnd (jointYV cR) v| ≤ 1 := by
      cases v
      · rw [hc, abs_le]; constructor <;> linarith
      · rw [hd, abs_le]; constructor <;> linarith
    have hbnd : |(1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u * biasOfSnd (jointYV cR) v| ≤ 1 := by
      rw [abs_mul, abs_mul, show |(1 - 2 * (0:ℝ))| = 1 by norm_num, one_mul]
      calc |biasOf (jointUX cL) u| * |biasOfSnd (jointYV cR) v| ≤ 1 * 1 :=
            mul_le_mul (hbL u) hs (abs_nonneg _) zero_le_one
        _ = 1 := by ring
    linarith [(abs_le.mp hbnd).1]
  have hrate0 : mutualInfo (jointYV cR) = twoAtomL fe d c := by
    rw [mutualInfo_jointYV_eq_twoAtomL hrho hne, hc, hd]
  have hval0 : mutualInfo (jointUV 0 cL cR) = twoAtomL (atomValueV cL) d c := by
    rw [mutualInfo_jointUV_eq_twoAtomLV hpi hrho hkerR hne, hc, hd]
  have hdc := hasDerivAt_atomValueV (t := c) (by rw [abs_lt]; constructor <;> linarith) hpi
  have hdd := hasDerivAt_atomValueV (t := d) (by rw [abs_lt]; constructor <;> linarith) hpi
  have hpc := hasDerivAt_fe' (z := c) (by linarith) hc1
  have hpd := hasDerivAt_fe' (z := d) hd1 (by linarith)
  have hgne : ¬ (Dfst fe Real.artanh c d = 0 ∧ Dsnd fe Real.artanh c d = 0) := by
    have := Dfst_fe_pos hc0 hc1 hd0 hd1
    intro hcc; rw [hcc.1] at this; exact lt_irrefl 0 this
  rcases hmx with hmx | hmx
  · refine stationary_of_max hcd hdc hdd hpc hpd hgne (fun e₁ e₂ => ?_)
    filter_upwards [eventually_atomsV (d₁ := e₁) (d₂ := e₂) hc0 hc1 hd0 hd1]
      with t ⟨p1, p2, p3, p4⟩ hle
    have hrate' := rateV_chanOfAtomsV p1 p2 p3 p4
    have hval' := valueV_chanOfAtomsV p1 p2 p3 p4 hpi (hkerOf p1 p2 p3 p4)
    have hfeas : FeasibleC Cu Cv cL (chanOfAtomsV p1 p2 p3 p4) := by
      refine ⟨hmx.1.1, ?_⟩
      rw [hrate']
      calc twoAtomL fe (d + t * e₂) (c + t * e₁) ≤ twoAtomL fe d c := hle
        _ = mutualInfo (jointYV cR) := hrate0.symm
        _ ≤ Cv := hmx.1.2
    have hbeat := hmx.2 _ _ hfeas
    rw [hval'] at hbeat
    rw [← hval0]
    exact hbeat
  · refine stationary_of_min hcd hdc hdd hpc hpd hgne (fun e₁ e₂ => ?_)
    filter_upwards [eventually_atomsV (d₁ := e₁) (d₂ := e₂) hc0 hc1 hd0 hd1]
      with t ⟨p1, p2, p3, p4⟩ hle
    have hrate' := rateV_chanOfAtomsV p1 p2 p3 p4
    have hval' := valueV_chanOfAtomsV p1 p2 p3 p4 hpi (hkerOf p1 p2 p3 p4)
    have hfeas : FeasibleMin Cu Cv cL (chanOfAtomsV p1 p2 p3 p4) := by
      refine ⟨hmx.1.1, ?_⟩
      rw [hrate']
      calc Cv ≤ mutualInfo (jointYV cR) := hmx.1.2
        _ = twoAtomL fe d c := hrate0
        _ ≤ twoAtomL fe (d + t * e₂) (c + t * e₁) := hle
    have hbeat := hmx.2 _ _ hfeas
    rw [hval'] at hbeat
    rw [← hval0]
    exact hbeat

/-! ### The `V`-side residual, and both skews -/

theorem atomValueV_eq_Gval {cL : Chan} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u)
    (h1 : biasOf (jointUX cL) true = Real.tanh α)
    (h0 : biasOf (jointUX cL) false = -Real.tanh β) (τ : ℝ) :
    atomValueV cL (Real.tanh τ) = LC.Gval α β τ := by
  have hsum : marg₁ (jointUX cL) true + marg₁ (jointUX cL) false = 1 := by
    have := marg₁_jointUX_sum cL; linarith
  have hmz : marg₁ (jointUX cL) true * Real.tanh α
      + marg₁ (jointUX cL) false * -Real.tanh β = 0 := by
    have := pi_bias_sum_zero cL (hpi false) (hpi true)
    rw [h1, h0] at this; linarith
  obtain ⟨e1, e0⟩ := weights_of_mean_zero hα hβ hsum hmz
  rw [atomValueV, h1, h0, e1, e0, LC.Gval, fFun, fFun, LC.fF, LC.fF]
  ring_nf

theorem atomValueV'_eq {cL : Chan} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u)
    (h1 : biasOf (jointUX cL) true = Real.tanh α)
    (h0 : biasOf (jointUX cL) false = -Real.tanh β) (τ : ℝ) :
    atomValueV' cL (Real.tanh τ)
      = LC.kco α β * (LC.LC (τ + α) - LC.LC (τ - β) - LC.LC α + LC.LC β) := by
  have hcτ : (0:ℝ) < Real.cosh τ := Real.cosh_pos τ
  have habs : |Real.tanh τ| < 1 := Real.abs_tanh_lt_one τ
  have hcomp : HasDerivAt (fun s : ℝ => atomValueV cL (Real.tanh s))
      (atomValueV' cL (Real.tanh τ) * (1 / Real.cosh τ ^ 2)) τ := by
    have h := (hasDerivAt_atomValueV habs hpi).comp τ (LC.hasDerivAt_tanh τ)
    rwa [Function.comp_def] at h
  have hfun : (fun s : ℝ => atomValueV cL (Real.tanh s)) = LC.Gval α β := by
    funext s; exact atomValueV_eq_Gval hα hβ hpi h1 h0 s
  rw [hfun] at hcomp
  have hG := LC.hasDerivAt_Gval hα hβ τ
  have := hcomp.unique hG
  field_simp at this
  linarith

/-- **`(B)`, `V`-side: the mirror residual vanishes.** -/
theorem residual_zero_of_maximiserV {Cu Cv : ℝ} {cL cR : Chan} {α β γ δ : ℝ}
    (hmx : OptPairC Cu Cv cL cR)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hUa : biasOf (jointUX cL) true = Real.tanh α)
    (hUb : biasOf (jointUX cL) false = -Real.tanh β)
    (hV0 : biasOfSnd (jointYV cR) false = Real.tanh γ)
    (hV1 : biasOfSnd (jointYV cR) true = -Real.tanh δ) :
    LC.RS ((γ + δ) / 2) ((α + β) / 2) ((γ - δ) / 2) ((α - β) / 2) = 0 := by
  have htγ : 0 < Real.tanh γ := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hγ) (Real.cosh_pos γ)
  have htδ : 0 < Real.tanh δ := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hδ) (Real.cosh_pos δ)
  have hc0 : 0 < Real.tanh γ := htγ
  have hc1 : Real.tanh γ < 1 := by linarith [(abs_lt.mp (Real.abs_tanh_lt_one γ)).2]
  have hd0 : -Real.tanh δ < 0 := by linarith
  have hd1 : -1 < -Real.tanh δ := by linarith [(abs_lt.mp (Real.abs_tanh_lt_one δ)).2]
  obtain ⟨lam, hlam0, hA, hB⟩ :=
    stationary_of_maximiserV hmx hpi hrho hV0 hV1 hc0 hc1 hd0 hd1
  simp only [Dfst, Dsnd] at hA hB
  obtain ⟨hA', hB'⟩ := KKT.cleared_of_grad (φ := atomValueV cL) (ψ := fe)
    (φ' := atomValueV' cL) (ψ' := Real.artanh) (by linarith) (ne_of_gt hc0) (ne_of_lt hd0)
    hA (by linarith [hB])
  obtain ⟨l₀, l₁, e1, e2, e3, e4⟩ :=
    KKT.bitangency_of_stationary (φ := atomValueV cL) (ψ := fe)
      (φ' := atomValueV' cL) (ψ' := Real.artanh) (by linarith) hA' hB'
  have hdtanh : -Real.tanh δ = Real.tanh (-δ) := by rw [Real.tanh_neg]
  have hslack : ∀ τ : ℝ, l₀ + l₁ * Real.tanh τ + lam * fe (Real.tanh τ)
      - atomValueV cL (Real.tanh τ) = LC.Dsl l₀ l₁ lam α β τ := by
    intro τ
    rw [LC.Dsl, atomValueV_eq_Gval hα hβ hpi hUa hUb τ, fe_tanh]
  have hDγ : LC.Dsl l₀ l₁ lam α β γ = 0 := by rw [← hslack γ]; linarith [e1]
  have hDδ : LC.Dsl l₀ l₁ lam α β (-δ) = 0 := by
    rw [← hslack (-δ), ← hdtanh]; linarith [e2]
  have hTc : l₁ + lam * γ
      = LC.kco α β * (LC.LC (γ + α) - LC.LC (γ - β) - LC.LC α + LC.LC β) := by
    rw [← atomValueV'_eq hα hβ hpi hUa hUb γ]
    have : Real.artanh (Real.tanh γ) = γ := Real.artanh_tanh γ
    rw [this] at e3; linarith [e3]
  have hTd : l₁ + lam * (-δ)
      = LC.kco α β * (LC.LC (-δ + α) - LC.LC (-δ - β) - LC.LC α + LC.LC β) := by
    rw [← atomValueV'_eq hα hβ hpi hUa hUb (-δ), ← hdtanh]
    have : Real.artanh (-Real.tanh δ) = -δ := by rw [hdtanh, Real.artanh_tanh]
    rw [this] at e4; linarith [e4]
  have hm : (0:ℝ) < (γ + δ) / 2 := by linarith
  have hα' : (0:ℝ) < (α + β) / 2 + (α - β) / 2 := by linarith
  have hβ' : (0:ℝ) < (α + β) / 2 - (α - β) / 2 := by linarith
  have eγ : (γ + δ) / 2 + (γ - δ) / 2 = γ := by ring
  have eδ : (γ - δ) / 2 - (γ + δ) / 2 = -δ := by ring
  refine LC.bitangent_residual_zero (l₀ := l₀) (l₁ := l₁) (l₂ := lam) hm hα' hβ' ?_ ?_ ?_ ?_
  · rw [eγ, show (α + β) / 2 + (α - β) / 2 = α by ring,
      show (α + β) / 2 - (α - β) / 2 = β by ring]
    exact hDγ
  · rw [eδ, show (α + β) / 2 + (α - β) / 2 = α by ring,
      show (α + β) / 2 - (α - β) / 2 = β by ring]
    exact hDδ
  · rw [eγ, show (γ - δ) / 2 + (α - β) / 2 + (γ + δ) / 2 = γ + (α - β) / 2 by ring,
      ← LC.Gker ((α + β) / 2) ((α - β) / 2) γ,
      show (α + β) / 2 + (α - β) / 2 = α from by ring,
      show (α + β) / 2 - (α - β) / 2 = β from by ring]
    exact hTc
  · rw [eδ, show (γ - δ) / 2 + (α - β) / 2 - (γ + δ) / 2 = -δ + (α - β) / 2 by ring,
      ← LC.Gker ((α + β) / 2) ((α - β) / 2) (-δ),
      show (α + β) / 2 + (α - β) / 2 = α from by ring,
      show (α + β) / 2 - (α - β) / 2 = β from by ring]
    exact hTd

/-- **`(B)`'s analytic conclusion at the `Chan` level**: at a maximiser with
interior atoms on both sides, both skews vanish — the two channels are
symmetric. -/
theorem skews_vanish_of_maximiser {Cu Cv : ℝ} {cL cR : Chan} {α β γ δ : ℝ}
    (hmx : OptPairC Cu Cv cL cR)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hUa : biasOf (jointUX cL) true = Real.tanh α)
    (hUb : biasOf (jointUX cL) false = -Real.tanh β)
    (hV0 : biasOfSnd (jointYV cR) false = Real.tanh γ)
    (hV1 : biasOfSnd (jointYV cR) true = -Real.tanh δ) :
    α = β ∧ γ = δ := by
  have hS := residual_zero_of_maximiser hmx hpi hrho hα hβ hγ hδ hUa hUb hV0 hV1
  have hT := residual_zero_of_maximiserV hmx hpi hrho hα hβ hγ hδ hUa hUb hV0 hV1
  obtain ⟨hu, hv⟩ := LC.skews_vanish (m := (α + β) / 2) (n := (γ + δ) / 2)
    (u := (α - β) / 2) (v := (γ - δ) / 2) (by linarith) (by linarith) hS hT
  constructor <;> linarith

/-! ### Reading off `BothBSC` -/

lemma Chan.ext' {c₁ c₂ : Chan} (h : c₁.tr = c₂.tr) : c₁ = c₂ := by
  cases c₁; cases c₂; simp only [Chan.mk.injEq]; exact h

/-- A channel with balanced marginals **is** a BSC. -/
theorem bsc_of_balanced {c : Chan} (h : marg₁ (jointUX c) true = 1 / 2) :
    ∃ (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1), c = bsc a h0 h1 := by
  obtain ⟨hb0, hb1⟩ := chan_param_mem c false
  refine ⟨c.tr false true, hb0, hb1, Chan.ext' ?_⟩
  have hXY : c.tr false true + c.tr true true = 1 := by
    simp only [marg₁, jointUX] at h
    linarith
  rw [bsc_tr]
  funext i j
  have hc := congrFun (congrFun (chan_eq_chanOf c) i) j
  have hY : c.tr true true = 1 - c.tr false true := by linarith
  rw [hc]
  cases i <;> cases j <;> simp only [chanTr, bscTr, hY, cond_true, cond_false] <;>
    norm_num

/-- A channel with balanced marginals on the `V` side is a BSC. -/
theorem bsc_of_balancedV {c : Chan} (h : marg₂ (jointYV c) true = 1 / 2) :
    ∃ (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1), c = bsc a h0 h1 := by
  refine bsc_of_balanced (c := c) ?_
  simpa [marg₁, marg₂, jointUX, jointYV] using h

/-- **`(B)` at the `Chan` level.**  At a maximiser whose atoms are interior on
both sides, both channels are binary symmetric. -/
theorem bothBSC_of_maximiser {Cu Cv : ℝ} {cL cR : Chan} {α β γ δ : ℝ}
    (hmx : OptPairC Cu Cv cL cR)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hUa : biasOf (jointUX cL) true = Real.tanh α)
    (hUb : biasOf (jointUX cL) false = -Real.tanh β)
    (hV0 : biasOfSnd (jointYV cR) false = Real.tanh γ)
    (hV1 : biasOfSnd (jointYV cR) true = -Real.tanh δ) :
    BothBSC cL cR := by
  obtain ⟨hab, hcd⟩ := skews_vanish_of_maximiser hmx hpi hrho hα hβ hγ hδ hUa hUb hV0 hV1
  have htα : 0 < Real.tanh α := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hα) (Real.cosh_pos α)
  have htγ : 0 < Real.tanh γ := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hγ) (Real.cosh_pos γ)
  constructor
  · refine bsc_of_balanced ?_
    have hsum : marg₁ (jointUX cL) true + marg₁ (jointUX cL) false = 1 := by
      have := marg₁_jointUX_sum cL; linarith
    have hmz := pi_bias_sum_zero cL (hpi false) (hpi true)
    rw [hUa, hUb, ← hab] at hmz
    have : marg₁ (jointUX cL) true * Real.tanh α
        = marg₁ (jointUX cL) false * Real.tanh α := by linarith
    have heq : marg₁ (jointUX cL) true = marg₁ (jointUX cL) false :=
      mul_right_cancel₀ (ne_of_gt htα) this
    linarith
  · refine bsc_of_balancedV ?_
    have hsum : marg₂ (jointYV cR) false + marg₂ (jointYV cR) true = 1 := marg₂_jointYV_sum cR
    have hmz := rho_bias_sum_zero cR (hrho false) (hrho true)
    rw [hV0, hV1, ← hcd] at hmz
    have : marg₂ (jointYV cR) false * Real.tanh γ
        = marg₂ (jointYV cR) true * Real.tanh γ := by linarith
    have heq : marg₂ (jointYV cR) false = marg₂ (jointYV cR) true :=
      mul_right_cancel₀ (ne_of_gt htγ) this
    linarith

/-! ### Relabelling the `U` letters

The whole development fixes the *orientation* of the two atoms (positive at
`true` on the `U` side, at `false` on the `V` side).  Relabelling is a symmetry:
`swapU` swaps the two `U` letters, leaves every information quantity fixed, and
turns a BSC into a BSC.  This lets the opposite orientation be handled without
duplicating the analysis. -/

/-- Swap the two `U` letters. -/
noncomputable def swapU (c : Chan) : Chan where
  tr := fun x u => c.tr x (!u)
  nonneg i j := c.nonneg i (!j)
  sum_one i := by have := c.sum_one i; simpa using by linarith

@[simp] lemma jointUX_swapU (c : Chan) (u x : Bool) :
    jointUX (swapU c) u x = jointUX c (!u) x := rfl

@[simp] lemma marg₁_swapU (c : Chan) (u : Bool) :
    marg₁ (jointUX (swapU c)) u = marg₁ (jointUX c) (!u) := rfl

@[simp] lemma biasOf_swapU (c : Chan) (u : Bool) :
    biasOf (jointUX (swapU c)) u = biasOf (jointUX c) (!u) := rfl

lemma marg₂_jointUX_swapU (c : Chan) (x : Bool) :
    marg₂ (jointUX (swapU c)) x = marg₂ (jointUX c) x := by
  simp only [marg₂, jointUX, swapU]
  cases x <;> simp <;> ring

lemma entropy1_swapU (c : Chan) :
    entropy1 (marg₁ (jointUX (swapU c))) = entropy1 (marg₁ (jointUX c)) := by
  simp only [entropy1, marg₁_swapU]
  simp only [Bool.not_false, Bool.not_true]
  ring

lemma entropy2_swapU (c : Chan) :
    entropy2 (jointUX (swapU c)) = entropy2 (jointUX c) := by
  simp only [entropy2, jointUX, swapU]
  simp only [Bool.not_false, Bool.not_true]
  ring

lemma mutualInfo_jointUX_swapU (c : Chan) :
    mutualInfo (jointUX (swapU c)) = mutualInfo (jointUX c) := by
  have h : marg₂ (jointUX (swapU c)) = marg₂ (jointUX c) := funext (marg₂_jointUX_swapU c)
  rw [mutualInfo, mutualInfo, entropy1_swapU, entropy2_swapU, h]

@[simp] lemma jointUV_swapU (p : ℝ) (cL cR : Chan) (u v : Bool) :
    jointUV p (swapU cL) cR u v = jointUV p cL cR (!u) v := rfl

lemma mutualInfo_jointUV_swapU (p : ℝ) (cL cR : Chan) :
    mutualInfo (jointUV p (swapU cL) cR) = mutualInfo (jointUV p cL cR) := by
  have h1 : entropy1 (marg₁ (jointUV p (swapU cL) cR)) = entropy1 (marg₁ (jointUV p cL cR)) := by
    simp only [entropy1, marg₁, jointUV_swapU, Bool.not_false, Bool.not_true]
    ring
  have h2 : marg₂ (jointUV p (swapU cL) cR) = marg₂ (jointUV p cL cR) := by
    funext v
    simp only [marg₂, jointUV_swapU, Bool.not_false, Bool.not_true]
    ring
  have h3 : entropy2 (jointUV p (swapU cL) cR) = entropy2 (jointUV p cL cR) := by
    simp only [entropy2, jointUV_swapU, Bool.not_false, Bool.not_true]
    ring
  rw [mutualInfo, mutualInfo, h1, h2, h3]

lemma swapU_involutive (c : Chan) : swapU (swapU c) = c := by
  refine Chan.ext' ?_
  funext x u
  simp [swapU]

lemma swapU_bsc (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    swapU (bsc a h0 h1) = bsc (1 - a) (by linarith) (by linarith) := by
  refine Chan.ext' ?_
  funext x u
  simp only [swapU, bsc_tr, bscTr]
  cases x <;> cases u <;> norm_num

/-- `BothBSC` transfers back along a `U`-relabelling. -/
lemma bothBSC_of_swapU {cL cR : Chan} (h : BothBSC (swapU cL) cR) : BothBSC cL cR := by
  obtain ⟨⟨a, h0, h1, ha⟩, hR⟩ := h
  refine ⟨⟨1 - a, by linarith, by linarith, ?_⟩, hR⟩
  have := congrArg swapU ha
  rw [swapU_involutive, swapU_bsc] at this
  exact this

/-- **`(B)`, both `U`-orientations.**  Only the `V`-side orientation is fixed;
the `U`-side one is handled by relabelling. -/
theorem bothBSC_of_maximiser_any {Cu Cv : ℝ} {cL cR : Chan} {α β γ δ : ℝ}
    (hmx : OptPairC Cu Cv cL cR)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hU : (biasOf (jointUX cL) true = Real.tanh α
            ∧ biasOf (jointUX cL) false = -Real.tanh β)
          ∨ (biasOf (jointUX cL) false = Real.tanh α
            ∧ biasOf (jointUX cL) true = -Real.tanh β))
    (hV0 : biasOfSnd (jointYV cR) false = Real.tanh γ)
    (hV1 : biasOfSnd (jointYV cR) true = -Real.tanh δ) :
    BothBSC cL cR := by
  rcases hU with ⟨h1, h0⟩ | ⟨h0, h1⟩
  · exact bothBSC_of_maximiser hmx hpi hrho hα hβ hγ hδ h1 h0 hV0 hV1
  · -- relabel the `U` letters
    refine bothBSC_of_swapU ?_
    have hmx' : OptPairC Cu Cv (swapU cL) cR := by
      rcases hmx with hmx | hmx
      · refine Or.inl ⟨⟨?_, hmx.1.2⟩, ?_⟩
        · rw [mutualInfo_jointUX_swapU]; exact hmx.1.1
        · intro cL' cR' hf
          rw [mutualInfo_jointUV_swapU]
          exact hmx.2 cL' cR' hf
      · refine Or.inr ⟨⟨?_, hmx.1.2⟩, ?_⟩
        · rw [mutualInfo_jointUX_swapU]; exact hmx.1.1
        · intro cL' cR' hf
          rw [mutualInfo_jointUV_swapU]
          exact hmx.2 cL' cR' hf
    refine bothBSC_of_maximiser hmx' ?_ hrho hα hβ hγ hδ ?_ ?_ hV0 hV1
    · intro u; rw [marg₁_swapU]; exact hpi _
    · rw [biasOf_swapU]; simpa using h0
    · rw [biasOf_swapU]; simpa using h1

/-! ### The same relabelling on the `V` side

`swapU` swaps the *second* index of `tr`, which is `U` in `jointUX` and `V` in
`jointYV`.  So the very same operation relabels the `V` letters. -/

@[simp] lemma jointYV_swapU (c : Chan) (y v : Bool) :
    jointYV (swapU c) y v = jointYV c y (!v) := rfl

@[simp] lemma marg₂_swapU (c : Chan) (v : Bool) :
    marg₂ (jointYV (swapU c)) v = marg₂ (jointYV c) (!v) := rfl

@[simp] lemma biasOfSnd_swapU (c : Chan) (v : Bool) :
    biasOfSnd (jointYV (swapU c)) v = biasOfSnd (jointYV c) (!v) := rfl

lemma mutualInfo_jointYV_swapU (c : Chan) :
    mutualInfo (jointYV (swapU c)) = mutualInfo (jointYV c) := by
  have h1 : marg₁ (jointYV (swapU c)) = marg₁ (jointYV c) := by
    funext y
    simp only [marg₁, jointYV_swapU, Bool.not_false, Bool.not_true]
    ring
  have h2 : entropy1 (marg₂ (jointYV (swapU c))) = entropy1 (marg₂ (jointYV c)) := by
    simp only [entropy1, marg₂_swapU, Bool.not_false, Bool.not_true]
    ring
  have h3 : entropy2 (jointYV (swapU c)) = entropy2 (jointYV c) := by
    simp only [entropy2, jointYV_swapU, Bool.not_false, Bool.not_true]
    ring
  rw [mutualInfo, mutualInfo, h1, h2, h3]

@[simp] lemma jointUV_swapV (p : ℝ) (cL cR : Chan) (u v : Bool) :
    jointUV p cL (swapU cR) u v = jointUV p cL cR u (!v) := rfl

lemma mutualInfo_jointUV_swapV (p : ℝ) (cL cR : Chan) :
    mutualInfo (jointUV p cL (swapU cR)) = mutualInfo (jointUV p cL cR) := by
  have h1 : marg₁ (jointUV p cL (swapU cR)) = marg₁ (jointUV p cL cR) := by
    funext u
    simp only [marg₁, jointUV_swapV, Bool.not_false, Bool.not_true]
    ring
  have h2 : entropy1 (marg₂ (jointUV p cL (swapU cR))) = entropy1 (marg₂ (jointUV p cL cR)) := by
    simp only [entropy1, marg₂, jointUV_swapV, Bool.not_false, Bool.not_true]
    ring
  have h3 : entropy2 (jointUV p cL (swapU cR)) = entropy2 (jointUV p cL cR) := by
    simp only [entropy2, jointUV_swapV, Bool.not_false, Bool.not_true]
    ring
  rw [mutualInfo, mutualInfo, h1, h2, h3]

lemma bothBSC_of_swapV {cL cR : Chan} (h : BothBSC cL (swapU cR)) : BothBSC cL cR := by
  obtain ⟨hL, a, h0, h1, ha⟩ := h
  refine ⟨hL, 1 - a, by linarith, by linarith, ?_⟩
  have := congrArg swapU ha
  rw [swapU_involutive, swapU_bsc] at this
  exact this

/-- **`(B)`, gauge-free.**  `BothBSC` at a maximiser for *any* orientation of the
atoms on either side. -/
theorem bothBSC_of_maximiser_free {Cu Cv : ℝ} {cL cR : Chan} {α β γ δ : ℝ}
    (hmx : OptPairC Cu Cv cL cR)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hU : (biasOf (jointUX cL) true = Real.tanh α
            ∧ biasOf (jointUX cL) false = -Real.tanh β)
          ∨ (biasOf (jointUX cL) false = Real.tanh α
            ∧ biasOf (jointUX cL) true = -Real.tanh β))
    (hV : (biasOfSnd (jointYV cR) false = Real.tanh γ
            ∧ biasOfSnd (jointYV cR) true = -Real.tanh δ)
          ∨ (biasOfSnd (jointYV cR) true = Real.tanh γ
            ∧ biasOfSnd (jointYV cR) false = -Real.tanh δ)) :
    BothBSC cL cR := by
  rcases hV with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · exact bothBSC_of_maximiser_any hmx hpi hrho hα hβ hγ hδ hU h0 h1
  · refine bothBSC_of_swapV ?_
    have hmx' : OptPairC Cu Cv cL (swapU cR) := by
      rcases hmx with hmx | hmx
      · refine Or.inl ⟨⟨hmx.1.1, ?_⟩, ?_⟩
        · rw [mutualInfo_jointYV_swapU]; exact hmx.1.2
        · intro cL' cR' hf
          rw [mutualInfo_jointUV_swapV]
          exact hmx.2 cL' cR' hf
      · refine Or.inr ⟨⟨hmx.1.1, ?_⟩, ?_⟩
        · rw [mutualInfo_jointYV_swapU]; exact hmx.1.2
        · intro cL' cR' hf
          rw [mutualInfo_jointUV_swapV]
          exact hmx.2 cL' cR' hf
    refine bothBSC_of_maximiser_any hmx' hpi ?_ hα hβ hγ hδ hU ?_ ?_
    · intro v; rw [marg₂_swapU]; exact hrho _
    · rw [biasOfSnd_swapU]; simpa using h1
    · rw [biasOfSnd_swapU]; simpa using h0

/-! ### Extracting the `θ`-parametrisation -/

lemma exists_theta_U {c : Chan} (hpos : ∀ u, 0 < marg₁ (jointUX c) u)
    (hnc : ∀ u, |biasOf (jointUX c) u| < 1) (hne : biasOf (jointUX c) true ≠ 0) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      ((biasOf (jointUX c) true = Real.tanh α ∧ biasOf (jointUX c) false = -Real.tanh β)
        ∨ (biasOf (jointUX c) false = Real.tanh α
            ∧ biasOf (jointUX c) true = -Real.tanh β)) := by
  have hmz := pi_bias_sum_zero c (hpos false) (hpos true)
  set s := biasOf (jointUX c) true with hs
  set r := biasOf (jointUX c) false with hr
  have hst := abs_lt.mp (hnc true)
  have hrt := abs_lt.mp (hnc false)
  have hopp : marg₁ (jointUX c) false * r = -(marg₁ (jointUX c) true * s) := by linarith
  rcases lt_or_gt_of_ne hne with hneg | hpos'
  · -- `s < 0`, so `r > 0`
    have hr0 : 0 < r := by
      by_contra hc
      push_neg at hc
      nlinarith [hpos false, hpos true]
    refine ⟨Real.artanh r, Real.artanh (-s), Real.artanh_pos ⟨hr0, hrt.2⟩,
      Real.artanh_pos ⟨by linarith, by linarith⟩, Or.inr ⟨?_, ?_⟩⟩
    · exact (Real.tanh_artanh ⟨by linarith, hrt.2⟩).symm
    · rw [Real.tanh_artanh ⟨by linarith, by linarith⟩]; ring
  · -- `s > 0`, so `r < 0`
    have hr0 : r < 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [hpos false, hpos true]
    refine ⟨Real.artanh s, Real.artanh (-r), Real.artanh_pos ⟨hpos', hst.2⟩,
      Real.artanh_pos ⟨by linarith, by linarith⟩, Or.inl ⟨?_, ?_⟩⟩
    · exact (Real.tanh_artanh ⟨by linarith, hst.2⟩).symm
    · rw [Real.tanh_artanh ⟨by linarith, by linarith⟩]; ring

lemma exists_theta_V {c : Chan} (hpos : ∀ v, 0 < marg₂ (jointYV c) v)
    (hnc : ∀ v, |biasOfSnd (jointYV c) v| < 1) (hne : biasOfSnd (jointYV c) false ≠ 0) :
    ∃ γ δ : ℝ, 0 < γ ∧ 0 < δ ∧
      ((biasOfSnd (jointYV c) false = Real.tanh γ
          ∧ biasOfSnd (jointYV c) true = -Real.tanh δ)
        ∨ (biasOfSnd (jointYV c) true = Real.tanh γ
            ∧ biasOfSnd (jointYV c) false = -Real.tanh δ)) := by
  have hmz := rho_bias_sum_zero c (hpos false) (hpos true)
  set s := biasOfSnd (jointYV c) false with hs
  set r := biasOfSnd (jointYV c) true with hr
  have hst := abs_lt.mp (hnc false)
  have hrt := abs_lt.mp (hnc true)
  rcases lt_or_gt_of_ne hne with hneg | hpos'
  · have hr0 : 0 < r := by
      by_contra hc
      push_neg at hc
      nlinarith [hpos false, hpos true]
    refine ⟨Real.artanh r, Real.artanh (-s), Real.artanh_pos ⟨hr0, hrt.2⟩,
      Real.artanh_pos ⟨by linarith, by linarith⟩, Or.inr ⟨?_, ?_⟩⟩
    · exact (Real.tanh_artanh ⟨by linarith, hrt.2⟩).symm
    · rw [Real.tanh_artanh ⟨by linarith, by linarith⟩]; ring
  · have hr0 : r < 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [hpos false, hpos true]
    refine ⟨Real.artanh s, Real.artanh (-r), Real.artanh_pos ⟨hpos', hst.2⟩,
      Real.artanh_pos ⟨by linarith, by linarith⟩, Or.inl ⟨?_, ?_⟩⟩
    · exact (Real.tanh_artanh ⟨by linarith, hst.2⟩).symm
    · rw [Real.tanh_artanh ⟨by linarith, by linarith⟩]; ring

/-- **`(B)`, with clean hypotheses.**  A maximiser whose atoms are interior
(`|bias| < 1`) and non-degenerate (not both zero) on each side is a BSC pair. -/
theorem bothBSC_of_interior {Cu Cv : ℝ} {cL cR : Chan}
    (hmx : OptPairC Cu Cv cL cR)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hUnc : ∀ u, |biasOf (jointUX cL) u| < 1) (hUne : biasOf (jointUX cL) true ≠ 0)
    (hVnc : ∀ v, |biasOfSnd (jointYV cR) v| < 1)
    (hVne : biasOfSnd (jointYV cR) false ≠ 0) :
    BothBSC cL cR := by
  obtain ⟨α, β, hα, hβ, hU⟩ := exists_theta_U hpi hUnc hUne
  obtain ⟨γ, δ, hγ, hδ, hV⟩ := exists_theta_V hrho hVnc hVne
  exact bothBSC_of_maximiser_free hmx hpi hrho hα hβ hγ hδ hU hV

/-- The `U`-side sits at a corner: some letter has bias `±1`. -/
def USideCorner (cL : Chan) : Prop :=
  ∃ u, biasOf (jointUX cL) u = 1 ∨ biasOf (jointUX cL) u = -1

/-- **`(B)` in the shape of `InteriorIsBSC`.**  The two extra hypotheses beyond
`InteriorIsBSC`'s are `¬USideCorner` — not implied by `¬VSideCorner`, and not
vacuous, since the conjectured optimum is a *double* corner — and
non-degeneracy, the case the assembly disposes of separately by `zsValue_pos`. -/
theorem interiorIsBSC_of_noCorner {Cu Cv : ℝ} {cL cR : Chan}
    (hmx : OptPairC Cu Cv cL cR)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hUc : ¬ USideCorner cL) (hVc : ¬ VSideCorner cR)
    (hUne : biasOf (jointUX cL) true ≠ 0) (hVne : biasOfSnd (jointYV cR) false ≠ 0) :
    BothBSC cL cR := by
  have hnnU : ∀ u x, 0 ≤ jointUX cL u x := by
    intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
  have hnnV : ∀ v y, 0 ≤ (fun v y => jointYV cR y v) v y := by
    intro v y; simp only [jointYV]; have := cR.nonneg y v; linarith
  have hUnc : ∀ u, |biasOf (jointUX cL) u| < 1 := by
    intro u
    obtain ⟨h1, h2⟩ := biasOf_mem_Icc hnnU (hpi u)
    have hne1 : biasOf (jointUX cL) u ≠ 1 := fun h => hUc ⟨u, Or.inl h⟩
    have hne2 : biasOf (jointUX cL) u ≠ -1 := fun h => hUc ⟨u, Or.inr h⟩
    rw [abs_lt]
    exact ⟨lt_of_le_of_ne h1 (Ne.symm hne2), lt_of_le_of_ne h2 hne1⟩
  have hVnc : ∀ v, |biasOfSnd (jointYV cR) v| < 1 := by
    intro v
    obtain ⟨h1, h2⟩ := biasOf_mem_Icc (q := fun v y => jointYV cR y v) hnnV (u := v)
      (by simpa [marg₁, marg₂, jointYV] using hrho v)
    have hne1 : biasOfSnd (jointYV cR) v ≠ 1 := fun h => hVc ⟨v, Or.inl h⟩
    have hne2 : biasOfSnd (jointYV cR) v ≠ -1 := fun h => hVc ⟨v, Or.inr h⟩
    rw [abs_lt]
    exact ⟨lt_of_le_of_ne h1 (Ne.symm hne2), lt_of_le_of_ne h2 hne1⟩
  exact bothBSC_of_interior hmx hpi hrho hUnc hUne hVnc hVne

end BSCAveraging
