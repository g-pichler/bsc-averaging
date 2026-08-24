import BSCAveraging.TwoAtomChan
import BSCAveraging.BitangencyBridge

/-! # `(B)`: assembling the pieces

`NOTES.md` §7c⁹–§7c¹⁰.  Along the two-atom family the value and the rate are
`twoAtomL φ b a` and `twoAtomL ψ b a` (`TwoAtomChan.lean`).  This file
differentiates them along an arbitrary straight line in `(a,b)`, feeds the
result to the KKT lemma, and lands on the four bitangency equations. -/

namespace BSCAveraging

open BSCAveraging.KKT

/-- Partial derivative of `twoAtomL φ b a` in the first atom. -/
noncomputable def Dfst (φ φ' : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b / (a - b) ^ 2) * (φ a - φ b) + (-b / (a - b)) * φ' a

/-- Partial derivative of `twoAtomL φ b a` in the second atom. -/
noncomputable def Dsnd (φ φ' : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (a / (a - b) ^ 2) * (φ b - φ a) + (a / (a - b)) * φ' b

/-- **The directional derivative** of the two-atom functional along a line. -/
theorem hasDerivAt_twoAtomL_line {φ φ' : ℝ → ℝ} {a b d₁ d₂ : ℝ} (hab : b < a)
    (hφa : HasDerivAt φ (φ' a) a) (hφb : HasDerivAt φ (φ' b) b) :
    HasDerivAt (fun t : ℝ => twoAtomL φ (b + t * d₂) (a + t * d₁))
      (Dfst φ φ' a b * d₁ + Dsnd φ φ' a b * d₂) 0 := by
  have hD : a - b ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hp : HasDerivAt (fun t : ℝ => a + t * d₁) d₁ 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).mul_const d₁).const_add a)
  have hx : HasDerivAt (fun t : ℝ => b + t * d₂) d₂ 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).mul_const d₂).const_add b)
  have hu : HasDerivAt (fun t : ℝ => -(b + t * d₂)) (-d₂) 0 := hx.neg
  have hv : HasDerivAt (fun t : ℝ => (a + t * d₁) - (b + t * d₂)) (d₁ - d₂) 0 := hp.sub hx
  have hv0 : (a + (0:ℝ) * d₁) - (b + (0:ℝ) * d₂) = a - b := by ring
  have hvne : (a + (0:ℝ) * d₁) - (b + (0:ℝ) * d₂) ≠ 0 := by rw [hv0]; exact hD
  have hq1 := hu.div hv hvne
  have hq2 := hp.div hv hvne
  have hcφa : HasDerivAt (fun t : ℝ => φ (a + t * d₁)) (φ' a * d₁) 0 := by
    have hφa' : HasDerivAt φ (φ' a) ((fun t : ℝ => a + t * d₁) 0) := by simpa using hφa
    have h := hφa'.comp 0 hp
    simpa [Function.comp_def] using h
  have hcφb : HasDerivAt (fun t : ℝ => φ (b + t * d₂)) (φ' b * d₂) 0 := by
    have hφb' : HasDerivAt φ (φ' b) ((fun t : ℝ => b + t * d₂) 0) := by simpa using hφb
    have h := hφb'.comp 0 hx
    simpa [Function.comp_def] using h
  have hsum := (hq1.mul hcφa).add (hq2.mul hcφb)
  refine hd_congr hsum ?_
  norm_num
  rw [Dfst, Dsnd]
  field_simp
  ring

/-- **Stationarity from maximality.**  If the two-atom value cannot be improved
by any feasible move along a straight line, and the rate gradient is nonzero,
then the two gradients are proportional with a nonnegative multiplier. -/
theorem stationary_of_max {φ ψ φ' ψ' : ℝ → ℝ} {a b : ℝ} (hab : b < a)
    (hφa : HasDerivAt φ (φ' a) a) (hφb : HasDerivAt φ (φ' b) b)
    (hψa : HasDerivAt ψ (ψ' a) a) (hψb : HasDerivAt ψ (ψ' b) b)
    (hne : ¬ (Dfst ψ ψ' a b = 0 ∧ Dsnd ψ ψ' a b = 0))
    (hmax : ∀ d₁ d₂ : ℝ, ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      twoAtomL ψ (b + t * d₂) (a + t * d₁) ≤ twoAtomL ψ b a →
      twoAtomL φ (b + t * d₂) (a + t * d₁) ≤ twoAtomL φ b a) :
    ∃ lam : ℝ, 0 ≤ lam ∧ Dfst φ φ' a b = lam * Dfst ψ ψ' a b
      ∧ Dsnd φ φ' a b = lam * Dsnd ψ ψ' a b := by
  refine kkt_of_directional hne (fun d₁ d₂ hd => ?_)
  have hV := hasDerivAt_twoAtomL_line (φ := φ) (φ' := φ') hab hφa hφb (d₁ := d₁) (d₂ := d₂)
  have hR := hasDerivAt_twoAtomL_line (φ := ψ) (φ' := ψ') hab hψa hψb (d₁ := d₁) (d₂ := d₂)
  refine le_zero_of_deriv_of_max hV hR (by linarith) ?_
  filter_upwards [hmax d₁ d₂] with t ht
  simpa using ht

/-- **The mirror for a minimiser.**  Feasible directions are now those in which
the rate *increases*; along them the value cannot decrease.  Negating the
direction turns that into exactly `kkt_of_directional`'s hypothesis, so the
conclusion — and the sign of `λ` — is the same. -/
theorem stationary_of_min {φ ψ φ' ψ' : ℝ → ℝ} {a b : ℝ} (hab : b < a)
    (hφa : HasDerivAt φ (φ' a) a) (hφb : HasDerivAt φ (φ' b) b)
    (hψa : HasDerivAt ψ (ψ' a) a) (hψb : HasDerivAt ψ (ψ' b) b)
    (hne : ¬ (Dfst ψ ψ' a b = 0 ∧ Dsnd ψ ψ' a b = 0))
    (hmin : ∀ d₁ d₂ : ℝ, ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      twoAtomL ψ b a ≤ twoAtomL ψ (b + t * d₂) (a + t * d₁) →
      twoAtomL φ b a ≤ twoAtomL φ (b + t * d₂) (a + t * d₁)) :
    ∃ lam : ℝ, 0 ≤ lam ∧ Dfst φ φ' a b = lam * Dfst ψ ψ' a b
      ∧ Dsnd φ φ' a b = lam * Dsnd ψ ψ' a b := by
  refine kkt_of_directional hne (fun d₁ d₂ hd => ?_)
  have hV := hasDerivAt_twoAtomL_line (φ := φ) (φ' := φ') hab hφa hφb
    (d₁ := -d₁) (d₂ := -d₂)
  have hR := hasDerivAt_twoAtomL_line (φ := ψ) (φ' := ψ') hab hψa hψb
    (d₁ := -d₁) (d₂ := -d₂)
  have hpos : 0 < Dfst ψ ψ' a b * -d₁ + Dsnd ψ ψ' a b * -d₂ := by
    have he : Dfst ψ ψ' a b * -d₁ + Dsnd ψ ψ' a b * -d₂
        = -(Dfst ψ ψ' a b * d₁ + Dsnd ψ ψ' a b * d₂) := by ring
    rw [he]; linarith
  have hkey := le_zero_of_deriv_of_min hV hR hpos ?_
  · have he : Dfst φ φ' a b * -d₁ + Dsnd φ φ' a b * -d₂
        = -(Dfst φ φ' a b * d₁ + Dsnd φ φ' a b * d₂) := by ring
    rw [he] at hkey
    linarith
  · filter_upwards [hmin (-d₁) (-d₂)] with t ht
    simpa using ht

/-! ### The two one-sided derivatives -/

/-- `f(z) = (1+z)log(1+z)` has derivative `log(1+z)+1`. -/
lemma hasDerivAt_fFun {z : ℝ} (hz : 0 < 1 + z) :
    HasDerivAt fFun (Real.log (1 + z) + 1) z := by
  have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 z := by simpa using (hasDerivAt_id z).const_add 1
  have h2 : HasDerivAt (fun z : ℝ => Real.log (1 + z)) (1 / (1 + z)) z := by
    have := h1.log (ne_of_gt hz)
    simpa using this
  refine hd_congr (h1.mul h2) ?_
  field_simp

/-- The derivative of the atom value. -/
noncomputable def atomValue' (cR : Chan) (s : ℝ) : ℝ :=
  marg₂ (jointYV cR) false * biasOfSnd (jointYV cR) false
      * (Real.log (1 + s * biasOfSnd (jointYV cR) false) + 1)
    + marg₂ (jointYV cR) true * biasOfSnd (jointYV cR) true
      * (Real.log (1 + s * biasOfSnd (jointYV cR) true) + 1)

lemma hasDerivAt_atomValue {cR : Chan} {s : ℝ} (hs : |s| < 1)
    (hrho : ∀ v, 0 < marg₂ (jointYV cR) v) :
    HasDerivAt (atomValue cR) (atomValue' cR s) s := by
  have hnn : ∀ v y, 0 ≤ (fun v y => jointYV cR y v) v y := by
    intro v y; simp only [jointYV]; have := cR.nonneg y v; linarith
  have hb : ∀ v, |biasOfSnd (jointYV cR) v| ≤ 1 := by
    intro v
    have h := biasOf_mem_Icc (q := fun v y => jointYV cR y v) hnn (u := v) (by
      simpa [marg₁, marg₂, jointYV] using hrho v)
    rw [abs_le]
    exact ⟨h.1, h.2⟩
  have hpos : ∀ v, 0 < 1 + s * biasOfSnd (jointYV cR) v := by
    intro v
    have h1 : |s * biasOfSnd (jointYV cR) v| < 1 := by
      calc |s * biasOfSnd (jointYV cR) v| = |s| * |biasOfSnd (jointYV cR) v| := abs_mul _ _
        _ ≤ |s| * 1 := by
            apply mul_le_mul_of_nonneg_left (hb v) (abs_nonneg s)
        _ < 1 := by simpa using hs
    have := abs_lt.mp h1
    linarith [this.1]
  have hd : ∀ v, HasDerivAt (fun s : ℝ => fFun (s * biasOfSnd (jointYV cR) v))
      ((Real.log (1 + s * biasOfSnd (jointYV cR) v) + 1) * biasOfSnd (jointYV cR) v) s := by
    intro v
    have hin : HasDerivAt (fun s : ℝ => s * biasOfSnd (jointYV cR) v)
        (biasOfSnd (jointYV cR) v) s := by
      simpa using (hasDerivAt_id s).mul_const (biasOfSnd (jointYV cR) v)
    have h := (hasDerivAt_fFun (hpos v)).comp s hin
    rwa [Function.comp_def] at h
  have := ((hd false).const_mul (marg₂ (jointYV cR) false)).add
    ((hd true).const_mul (marg₂ (jointYV cR) true))
  refine hd_congr this ?_
  rw [atomValue']
  ring

/-- **The rate gradient does not vanish.**  `f_e` is strictly convex with
`f_e′ = artanh`, so `D_fst f_e > 0` when `b < 0 < a`. -/
theorem Dfst_fe_pos {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0) (hb1 : -1 < b) :
    0 < Dfst fe Real.artanh a b := by
  have hab : b < a := by linarith
  have hD : (0:ℝ) < a - b := by linarith
  -- strict tangent bound for `f_e` at `a`, evaluated at `b`
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope fe Real.artanh hab
    (fun x hx => ((hasDerivAt_fe' (by linarith [hx.1]) (by linarith [hx.2])).continuousAt
      ).continuousWithinAt)
    (fun x hx => hasDerivAt_fe' (by linarith [hx.1]) (by linarith [hx.2]))
  have hlt : Real.artanh ξ < Real.artanh a :=
    Real.artanh_lt_artanh (by linarith [hξ.1]) ha1 hξ.2
  have hkey : fe a - fe b - (a - b) * Real.artanh a < 0 := by
    rw [eq_comm, div_eq_iff (by linarith : a - b ≠ 0)] at hslope
    nlinarith [hslope, hlt, hD]
  rw [Dfst]
  have hb' : b < 0 := hb0
  have : (b / (a - b) ^ 2) * (fe a - fe b) + (-b / (a - b)) * Real.artanh a
      = (-b / (a - b) ^ 2) * (-(fe a - fe b) + (a - b) * Real.artanh a) := by
    field_simp
    ring
  rw [this]
  apply mul_pos (div_pos (by linarith) (by positivity)) (by linarith)

/-! ### The Chan-level statement -/

lemma eventually_atoms {a b d₁ d₂ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0)
    (hb1 : -1 < b) :
    ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      0 < a + t * d₁ ∧ a + t * d₁ < 1 ∧ b + t * d₂ < 0 ∧ -1 < b + t * d₂ := by
  have c1 : Filter.Tendsto (fun t : ℝ => a + t * d₁) (nhds 0) (nhds a) := by
    have : Continuous (fun t : ℝ => a + t * d₁) := by fun_prop
    simpa using this.tendsto 0
  have c2 : Filter.Tendsto (fun t : ℝ => b + t * d₂) (nhds 0) (nhds b) := by
    have : Continuous (fun t : ℝ => b + t * d₂) := by fun_prop
    simpa using this.tendsto 0
  have e1 := c1.eventually (eventually_gt_nhds ha0)
  have e2 := c1.eventually (eventually_lt_nhds ha1)
  have e3 := c2.eventually (eventually_lt_nhds hb0)
  have e4 := c2.eventually (eventually_gt_nhds hb1)
  filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, nhdsWithin_le_nhds e3,
    nhdsWithin_le_nhds e4] with t h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- **`(B)`'s first-order condition, at the `Chan` level.**  A maximiser's
`U`-side satisfies the stationarity `∇V = λ∇R` in the atom positions — the
correct form of `Bitangency` for a binary channel. -/
theorem stationary_of_maximiser {Cu Cv : ℝ} {cL cR : Chan} {a b : ℝ}
    (hmx : OptPairC Cu Cv cL cR)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (ha : biasOf (jointUX cL) true = a) (hb : biasOf (jointUX cL) false = b)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0) (hb1 : -1 < b) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      Dfst (atomValue cR) (atomValue' cR) a b = lam * Dfst fe Real.artanh a b
      ∧ Dsnd (atomValue cR) (atomValue' cR) a b = lam * Dsnd fe Real.artanh a b := by
  have hab : b < a := by linarith
  have hne : biasOf (jointUX cL) true ≠ biasOf (jointUX cL) false := by
    rw [ha, hb]; intro h; linarith
  -- bias bounds for `cR`
  have hnnR : ∀ v y, 0 ≤ (fun v y => jointYV cR y v) v y := by
    intro v y; simp only [jointYV]; have := cR.nonneg y v; linarith
  have hbR : ∀ v, |biasOfSnd (jointYV cR) v| ≤ 1 := by
    intro v
    have h := biasOf_mem_Icc (q := fun v y => jointYV cR y v) hnnR (u := v) (by
      simpa [marg₁, marg₂, jointYV] using hrho v)
    rw [abs_le]; exact ⟨h.1, h.2⟩
  -- the kernel hypothesis for any admissible atom pair
  have hkerOf : ∀ {a' b' : ℝ} (ha0' : 0 < a') (ha1' : a' < 1) (hb0' : b' < 0)
      (hb1' : -1 < b'), ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ))
        * biasOf (jointUX (chanOfAtoms ha0' ha1' hb0' hb1')) u * biasOfSnd (jointYV cR) v := by
    intro a' b' ha0' ha1' hb0' hb1' u v
    obtain ⟨e1, e0⟩ := biasOf_chanOfAtoms ha0' ha1' hb0' hb1'
    have hs : |biasOf (jointUX (chanOfAtoms ha0' ha1' hb0' hb1')) u| ≤ 1 := by
      cases u
      · rw [e0, abs_le]; constructor <;> linarith
      · rw [e1, abs_le]; constructor <;> linarith
    have : |(1 - 2 * (0:ℝ)) * biasOf (jointUX (chanOfAtoms ha0' ha1' hb0' hb1')) u
        * biasOfSnd (jointYV cR) v| ≤ 1 := by
      rw [abs_mul, abs_mul]
      have h1 : |(1 - 2 * (0:ℝ))| = 1 := by norm_num
      rw [h1, one_mul]
      calc |biasOf (jointUX (chanOfAtoms ha0' ha1' hb0' hb1')) u| * |biasOfSnd (jointYV cR) v|
          ≤ 1 * 1 := mul_le_mul hs (hbR v) (abs_nonneg _) zero_le_one
        _ = 1 := by ring
    linarith [(abs_le.mp this).1]
  -- rate and value of the original pair
  have hrate0 : mutualInfo (jointUX cL) = twoAtomL fe b a := by
    rw [mutualInfo_jointUX_eq_twoAtomL hpi hne, ha, hb]
  have hkerL : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u
      * biasOfSnd (jointYV cR) v := by
    intro u v
    have hs : |biasOf (jointUX cL) u| ≤ 1 := by
      cases u
      · rw [hb, abs_le]; constructor <;> linarith
      · rw [ha, abs_le]; constructor <;> linarith
    have : |(1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u * biasOfSnd (jointYV cR) v| ≤ 1 := by
      rw [abs_mul, abs_mul]
      have h1 : |(1 - 2 * (0:ℝ))| = 1 := by norm_num
      rw [h1, one_mul]
      calc |biasOf (jointUX cL) u| * |biasOfSnd (jointYV cR) v| ≤ 1 * 1 :=
            mul_le_mul hs (hbR v) (abs_nonneg _) zero_le_one
        _ = 1 := by ring
    linarith [(abs_le.mp this).1]
  have hval0 : mutualInfo (jointUV 0 cL cR) = twoAtomL (atomValue cR) b a := by
    rw [mutualInfo_jointUV_eq_twoAtomL hpi hrho hkerL hne, ha, hb]
  have hda := hasDerivAt_atomValue (s := a) (by rw [abs_lt]; constructor <;> linarith) hrho
  have hdb := hasDerivAt_atomValue (s := b) (by rw [abs_lt]; constructor <;> linarith) hrho
  have hpa := hasDerivAt_fe' (z := a) (by linarith) ha1
  have hpb := hasDerivAt_fe' (z := b) hb1 (by linarith)
  have hgne : ¬ (Dfst fe Real.artanh a b = 0 ∧ Dsnd fe Real.artanh a b = 0) := by
    have := Dfst_fe_pos ha0 ha1 hb0 hb1
    intro hc; rw [hc.1] at this; exact lt_irrefl 0 this
  rcases hmx with hmx | hmx
  · refine stationary_of_max hab hda hdb hpa hpb hgne (fun d₁ d₂ => ?_)
    filter_upwards [eventually_atoms (d₁ := d₁) (d₂ := d₂) ha0 ha1 hb0 hb1]
      with t ⟨p1, p2, p3, p4⟩ hle
    have hrate' := rate_chanOfAtoms p1 p2 p3 p4
    have hval' := value_chanOfAtoms p1 p2 p3 p4 hrho (hkerOf p1 p2 p3 p4)
    have hfeas : FeasibleC Cu Cv (chanOfAtoms p1 p2 p3 p4) cR := by
      refine ⟨?_, hmx.1.2⟩
      rw [hrate']
      calc twoAtomL fe (b + t * d₂) (a + t * d₁) ≤ twoAtomL fe b a := hle
        _ = mutualInfo (jointUX cL) := hrate0.symm
        _ ≤ Cu := hmx.1.1
    have := hmx.2 _ _ hfeas
    rw [hval'] at this
    rw [← hval0]
    exact this
  · refine stationary_of_min hab hda hdb hpa hpb hgne (fun d₁ d₂ => ?_)
    filter_upwards [eventually_atoms (d₁ := d₁) (d₂ := d₂) ha0 ha1 hb0 hb1]
      with t ⟨p1, p2, p3, p4⟩ hle
    have hrate' := rate_chanOfAtoms p1 p2 p3 p4
    have hval' := value_chanOfAtoms p1 p2 p3 p4 hrho (hkerOf p1 p2 p3 p4)
    have hfeas : FeasibleMin Cu Cv (chanOfAtoms p1 p2 p3 p4) cR := by
      refine ⟨?_, hmx.1.2⟩
      rw [hrate']
      calc Cu ≤ mutualInfo (jointUX cL) := hmx.1.1
        _ = twoAtomL fe b a := hrate0
        _ ≤ twoAtomL fe (b + t * d₂) (a + t * d₁) := hle
    have := hmx.2 _ _ hfeas
    rw [hval'] at this
    rw [← hval0]
    exact this

/-- The derivative of the atom value, in `θ` coordinates. -/
theorem atomValue'_eq {cR : Chan} {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (hf : 0 < marg₂ (jointYV cR) false) (ht : 0 < marg₂ (jointYV cR) true)
    (h0 : biasOfSnd (jointYV cR) false = Real.tanh γ)
    (h1 : biasOfSnd (jointYV cR) true = -Real.tanh δ) (σ : ℝ) :
    atomValue' cR (Real.tanh σ)
      = LC.kco γ δ * (LC.LC (σ + γ) - LC.LC (σ - δ) - LC.LC γ + LC.LC δ) := by
  have hrho : ∀ v, 0 < marg₂ (jointYV cR) v := by intro v; cases v <;> assumption
  have hcσ : (0:ℝ) < Real.cosh σ := Real.cosh_pos σ
  have habs : |Real.tanh σ| < 1 := Real.abs_tanh_lt_one σ
  -- the composite, two ways
  have hcomp : HasDerivAt (fun s : ℝ => atomValue cR (Real.tanh s))
      (atomValue' cR (Real.tanh σ) * (1 / Real.cosh σ ^ 2)) σ := by
    have h := (hasDerivAt_atomValue habs hrho).comp σ (LC.hasDerivAt_tanh σ)
    rwa [Function.comp_def] at h
  have hfun : (fun s : ℝ => atomValue cR (Real.tanh s)) = LC.Gval γ δ := by
    funext s; exact atomValue_eq_Gval hγ hδ hf ht h0 h1 s
  rw [hfun] at hcomp
  have hG := LC.hasDerivAt_Gval hγ hδ σ
  have := hcomp.unique hG
  field_simp at this
  linarith

/-- **`(B)`, `U`-side: a maximiser's residual vanishes.**  From the four
bitangency equations in `θ` coordinates, `R_S = 0`. -/
theorem residual_zero_of_maximiser {Cu Cv : ℝ} {cL cR : Chan} {α β γ δ : ℝ}
    (hmx : OptPairC Cu Cv cL cR)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hUa : biasOf (jointUX cL) true = Real.tanh α)
    (hUb : biasOf (jointUX cL) false = -Real.tanh β)
    (hV0 : biasOfSnd (jointYV cR) false = Real.tanh γ)
    (hV1 : biasOfSnd (jointYV cR) true = -Real.tanh δ) :
    LC.RS ((α + β) / 2) ((γ + δ) / 2) ((α - β) / 2) ((γ - δ) / 2) = 0 := by
  set a := Real.tanh α with hadef
  set b := -Real.tanh β with hbdef
  have htα : 0 < Real.tanh α := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hα) (Real.cosh_pos α)
  have htβ : 0 < Real.tanh β := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβ) (Real.cosh_pos β)
  have ha0 : 0 < a := by rw [hadef]; exact htα
  have ha1 : a < 1 := by
    rw [hadef]; linarith [(abs_lt.mp (Real.abs_tanh_lt_one α)).2]
  have hb0 : b < 0 := by rw [hbdef]; linarith
  have hb1 : -1 < b := by
    rw [hbdef]; linarith [(abs_lt.mp (Real.abs_tanh_lt_one β)).2]
  obtain ⟨lam, hlam0, hA, hB⟩ :=
    stationary_of_maximiser hmx hpi hrho hUa hUb ha0 ha1 hb0 hb1
  simp only [Dfst, Dsnd] at hA hB
  obtain ⟨hA', hB'⟩ := KKT.cleared_of_grad (φ := atomValue cR) (ψ := fe)
    (φ' := atomValue' cR) (ψ' := Real.artanh) (by linarith) (ne_of_gt ha0) (ne_of_lt hb0)
    hA (by linarith [hB])
  obtain ⟨l₀, l₁, e1, e2, e3, e4⟩ :=
    KKT.bitangency_of_stationary (φ := atomValue cR) (ψ := fe)
      (φ' := atomValue' cR) (ψ' := Real.artanh) (by linarith) hA' hB'
  -- translate to `θ`
  have hn : γ = (γ + δ) / 2 + (γ - δ) / 2 := by ring
  have hd : δ = (γ + δ) / 2 - (γ - δ) / 2 := by ring
  have hbtanh : b = Real.tanh (-β) := by rw [hbdef, Real.tanh_neg]
  have hslack : ∀ σ : ℝ, l₀ + l₁ * Real.tanh σ + lam * fe (Real.tanh σ)
      - atomValue cR (Real.tanh σ) = LC.Dsl l₀ l₁ lam γ δ σ :=
    fun σ => Dsl_eq_slack hγ hδ (hrho false) (hrho true) hV0 hV1 l₀ l₁ lam σ
  have hDα : LC.Dsl l₀ l₁ lam γ δ α = 0 := by
    rw [← hslack α, ← hadef]; linarith [e1]
  have hDβ : LC.Dsl l₀ l₁ lam γ δ (-β) = 0 := by
    rw [← hslack (-β), ← hbtanh]; linarith [e2]
  have hTa : l₁ + lam * α
      = LC.kco γ δ * (LC.LC (α + γ) - LC.LC (α - δ) - LC.LC γ + LC.LC δ) := by
    rw [← atomValue'_eq hγ hδ (hrho false) (hrho true) hV0 hV1 α, ← hadef]
    have : Real.artanh a = α := by rw [hadef, Real.artanh_tanh]
    rw [this] at e3; linarith [e3]
  have hTb : l₁ + lam * (-β)
      = LC.kco γ δ * (LC.LC (-β + γ) - LC.LC (-β - δ) - LC.LC γ + LC.LC δ) := by
    rw [← atomValue'_eq hγ hδ (hrho false) (hrho true) hV0 hV1 (-β), ← hbtanh]
    have : Real.artanh b = -β := by rw [hbtanh, Real.artanh_tanh]
    rw [this] at e4; linarith [e4]
  -- feed `bitangent_residual_zero`
  have hm : (0:ℝ) < (α + β) / 2 := by linarith
  have hγ' : (0:ℝ) < (γ + δ) / 2 + (γ - δ) / 2 := by linarith
  have hδ' : (0:ℝ) < (γ + δ) / 2 - (γ - δ) / 2 := by linarith
  have eα : (α + β) / 2 + (α - β) / 2 = α := by ring
  have eβ : (α - β) / 2 - (α + β) / 2 = -β := by ring
  refine LC.bitangent_residual_zero (l₀ := l₀) (l₁ := l₁) (l₂ := lam) hm hγ' hδ' ?_ ?_ ?_ ?_
  · rw [eα, ← hn, ← hd]; exact hDα
  · rw [eβ, ← hn, ← hd]; exact hDβ
  · rw [eα, show (α - β) / 2 + (γ - δ) / 2 + (α + β) / 2 = α + (γ - δ) / 2 by ring,
      ← LC.Gker ((γ + δ) / 2) ((γ - δ) / 2) α,
      show (γ + δ) / 2 + (γ - δ) / 2 = γ from by ring,
      show (γ + δ) / 2 - (γ - δ) / 2 = δ from by ring]
    exact hTa
  · rw [eβ, show (α - β) / 2 + (γ - δ) / 2 - (α + β) / 2 = -β + (γ - δ) / 2 by ring,
      ← LC.Gker ((γ + δ) / 2) ((γ - δ) / 2) (-β),
      show (γ + δ) / 2 + (γ - δ) / 2 = γ from by ring,
      show (γ + δ) / 2 - (γ - δ) / 2 = δ from by ring]
    exact hTb

end BSCAveraging
