import BSCAveraging.DiagReduction

/-! # The saddle inequality (iii)

The last analytic link of the `p = 0` chain.  With `g y = (1−y²)artanh y / y`
and `x = αβ`, (iii) reads

```
(1 − g(x))²·g(α)g(β)  >  x²·(g(x)−g(α))(g(x)−g(β))       for α,β ∈ (0,1).
```

The proof:

* `Rat x α = (g(x)−g(α))(g(x)−g(x/α)) / (g(α)g(x/α))` has derivative
  `−(2g(x)/α)·N(α,x/α)/(g(α)g(x/α))²`, because `B + C = g(x)` is constant along
  the hyperbola;
* `N ≥ 0` is the diagonal reduction (`Nfun_nonneg`), so `Rat x` is antitone on
  `[√x, 1)` — the value is maximal on the diagonal;
* on the diagonal `diag_pos` (which is `core_pos`) gives the strict inequality.
-/

namespace BSCAveraging.Core

open Real

/-! ### Calculus for `g` -/

lemma gFun_pos {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : 0 < gFun y := by
  have h1 : 0 < 1 - y ^ 2 := by nlinarith
  have h2 : 0 < Real.artanh y := Real.artanh_pos ⟨hy0, hy1⟩
  rw [gFun]; positivity

lemma Aval_pos {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : 0 < Aval y := by
  have h := self_lt_artanh hy0 hy1
  have h2 : y < (1 + y ^ 2) * Real.artanh y := by nlinarith [sq_nonneg y]
  rw [Aval]
  apply div_pos (by linarith) (by linarith)

/-- `g′(y) = −2·A(y)/y`. -/
lemma hasDerivAt_gFun {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt gFun (-(2 * Aval y / y)) y := by
  have hne : y ≠ 0 := ne_of_gt hy0
  have hy2 : (1 : ℝ) - y ^ 2 ≠ 0 := by nlinarith
  have hart : HasDerivAt Real.artanh (1 / (1 - y ^ 2)) y := hasDerivAt_artanh (by linarith) hy1
  have hnum : HasDerivAt (fun t : ℝ => (1 - t ^ 2) * Real.artanh t)
      (-(2 * y) * Real.artanh y + (1 - y ^ 2) * (1 / (1 - y ^ 2))) y := by
    refine HasDerivAt.mul ?_ hart
    simpa using ((hasDerivAt_pow 2 y).const_sub 1)
  have hdiv := hnum.div (hasDerivAt_id' (𝕜 := ℝ) (x := y)) hne
  have heq : ((-(2 * y) * Real.artanh y + (1 - y ^ 2) * (1 / (1 - y ^ 2))) * y
      - (1 - y ^ 2) * Real.artanh y * 1) / y ^ 2 = -(2 * Aval y / y) := by
    rw [Aval]; field_simp; ring
  have hg : gFun = fun t : ℝ => (1 - t ^ 2) * Real.artanh t / t := rfl
  rw [hg]
  exact hd_congr hdiv heq

lemma differentiableAt_gFun {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    DifferentiableAt ℝ gFun y := (hasDerivAt_gFun hy0 hy1).differentiableAt

lemma deriv_gFun {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    deriv gFun y = -(2 * Aval y / y) := (hasDerivAt_gFun hy0 hy1).deriv

/-- `g` is strictly decreasing on `(0,1)`. -/
lemma gFun_strictAntiOn : StrictAntiOn gFun (Set.Ioo (0:ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · intro y hy
    exact (differentiableAt_gFun hy.1 hy.2).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    rw [deriv_gFun hy.1 hy.2]
    have hA := Aval_pos hy.1 hy.2
    have hy0 := hy.1
    have hpos : 0 < 2 * Aval y / y := by positivity
    linarith

/-! ### The ratio along the hyperbola `αβ = x` -/

/-- `R x α = C(α)·C(x/α) / (B(α)·B(x/α))`. -/
noncomputable def Rat (x α : ℝ) : ℝ :=
  ((gFun x - gFun α) * (gFun x - gFun (x / α))) / (gFun α * gFun (x / α))

/-- `R′ = −(2g(x)/α)·N/(B(α)B(β))²`: the key derivative, where `B + C = g(x)`
is constant along the hyperbola. -/
lemma hasDerivAt_Rat {x α : ℝ} (hx0 : 0 < x) (hxa : x < α) (ha1 : α < 1) :
    HasDerivAt (Rat x)
      (-(2 * gFun x / α) * Nfun α (x / α) / (gFun α * gFun (x / α)) ^ 2) α := by
  have hα0 : 0 < α := lt_trans hx0 hxa
  have hαne : α ≠ 0 := ne_of_gt hα0
  have hβ0 : 0 < x / α := div_pos hx0 hα0
  have hβ1 : x / α < 1 := (div_lt_one hα0).mpr hxa
  have hβx : α * (x / α) = x := by field_simp
  have hga : 0 < gFun α := gFun_pos hα0 ha1
  have hgb : 0 < gFun (x / α) := gFun_pos hβ0 hβ1
  have hQne : gFun α * gFun (x / α) ≠ 0 := by positivity
  -- derivative of `a ↦ x/a`
  have hinv : HasDerivAt (fun a : ℝ => x / a) (-(x / α ^ 2)) α :=
    hd_congr ((hasDerivAt_const α x).div (hasDerivAt_id' (𝕜 := ℝ) (x := α)) hαne)
      (by field_simp; ring)
  have hgb' : HasDerivAt (fun a : ℝ => gFun (x / a))
      (-(2 * Aval (x / α) / (x / α)) * -(x / α ^ 2)) α := by
    have h := (hasDerivAt_gFun hβ0 hβ1).comp α hinv
    rwa [Function.comp_def] at h
  have hga' : HasDerivAt gFun (-(2 * Aval α / α)) α := hasDerivAt_gFun hα0 ha1
  have hP := (hga'.const_sub (gFun x)).mul (hgb'.const_sub (gFun x))
  have hQ := hga'.mul hgb'
  have hR := hP.div hQ hQne
  have hf : Rat x = fun a : ℝ =>
      ((gFun x - gFun a) * (gFun x - gFun (x / a))) / (gFun a * gFun (x / a)) := rfl
  rw [hf]
  refine hd_congr hR ?_
  simp only [Pi.mul_apply, Pi.div_apply]
  rw [Nfun, hβx]
  set b := x / α with hbdef
  have hbne : b ≠ 0 := ne_of_gt hβ0
  have hx : x = α * b := by rw [hbdef]; field_simp
  rw [hx]
  field_simp
  ring

lemma Rat_antitoneOn {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    AntitoneOn (Rat x) (Set.Ico (Real.sqrt x) 1) := by
  have hy0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hysq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hy1 : Real.sqrt x < 1 := by nlinarith
  have hxy : x < Real.sqrt x := by nlinarith
  have hkey : ∀ α ∈ Set.Ico (Real.sqrt x) 1, x < α ∧ α < 1 := by
    intro α hα; exact ⟨lt_of_lt_of_le hxy hα.1, hα.2⟩
  refine antitoneOn_of_deriv_nonpos (convex_Ico _ _) ?_ ?_ ?_
  · intro α hα
    obtain ⟨h1, h2⟩ := hkey α hα
    exact (hasDerivAt_Rat hx0 h1 h2).differentiableAt.continuousAt.continuousWithinAt
  · intro α hα
    rw [interior_Ico] at hα
    exact ((hasDerivAt_Rat hx0 (lt_of_lt_of_le hxy (le_of_lt hα.1)) hα.2).differentiableAt).differentiableWithinAt
  · intro α hα
    rw [interior_Ico] at hα
    have h1 : x < α := lt_of_lt_of_le hxy (le_of_lt hα.1)
    have h2 : α < 1 := hα.2
    have hα0 : 0 < α := lt_trans hx0 h1
    rw [(hasDerivAt_Rat hx0 h1 h2).deriv]
    have hβ0 : 0 < x / α := div_pos hx0 hα0
    have hβα : x / α ≤ α := by
      rw [div_le_iff₀ hα0]
      nlinarith [hα.1, hysq, hy0]
    have hN : 0 ≤ Nfun α (x / α) := Nfun_nonneg hβ0 hβα h2
    have hgx : 0 < gFun x := gFun_pos hx0 hx1
    have hQ : 0 < (gFun α * gFun (x / α)) ^ 2 := by
      have := gFun_pos hα0 h2
      have := gFun_pos hβ0 ((div_lt_one hα0).mpr h1)
      positivity
    have hnum : -(2 * gFun x / α) * Nfun α (x / α) ≤ 0 := by
      have : 0 < 2 * gFun x / α := by positivity
      nlinarith
    exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hQ)

lemma diag_pos' {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    0 < (1 - gFun (y ^ 2)) * gFun y - y ^ 2 * (gFun (y ^ 2) - gFun y) := by
  have hθ : 0 < Real.artanh y := Real.artanh_pos ⟨hy0, hy1⟩
  have ht : Real.tanh (Real.artanh y) = y := Real.tanh_artanh ⟨by linarith, hy1⟩
  have h := diag_pos hθ
  rwa [ht] at h

/-- **The saddle inequality (iii)**, cleared of denominators. -/
theorem saddle_iii {α β : ℝ} (ha0 : 0 < α) (ha1 : α < 1) (hb0 : 0 < β) (hb1 : β < 1) :
    (α * β) ^ 2 * ((gFun (α * β) - gFun α) * (gFun (α * β) - gFun β))
      < (1 - gFun (α * β)) ^ 2 * (gFun α * gFun β) := by
  wlog hba : β ≤ α generalizing α β
  · have h := this hb0 hb1 ha0 ha1 (le_of_lt (lt_of_not_ge hba))
    rw [mul_comm β α] at h
    linarith [h]
  set x := α * β with hxdef
  have hx0 : 0 < x := mul_pos ha0 hb0
  have hx1 : x < 1 := by nlinarith
  have hy0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hysq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hy1 : Real.sqrt x < 1 := by nlinarith
  have hxy : x < Real.sqrt x := by nlinarith
  set y := Real.sqrt x with hydef
  have hαy : y ≤ α := by
    rw [hydef]
    calc Real.sqrt x ≤ Real.sqrt (α ^ 2) := Real.sqrt_le_sqrt (by rw [hxdef]; nlinarith)
      _ = α := Real.sqrt_sq ha0.le
  have hαmem : α ∈ Set.Ico y 1 := ⟨hαy, ha1⟩
  have hymem : y ∈ Set.Ico y 1 := ⟨le_refl _, hy1⟩
  have hmono := Rat_antitoneOn hx0 hx1 hymem hαmem hαy
  -- identify the two values
  have hxa : x / α = β := by rw [hxdef]; field_simp
  have hxy' : x / y = y := by
    rw [← hysq]; field_simp
  have hga : 0 < gFun α := gFun_pos ha0 ha1
  have hgb : 0 < gFun β := gFun_pos hb0 hb1
  have hgy : 0 < gFun y := gFun_pos hy0 hy1
  have hgx : 0 < gFun x := gFun_pos hx0 hx1
  rw [Rat, Rat, hxa, hxy'] at hmono
  -- the diagonal value is below `(1 − g x)²/x²`
  have hdiag := diag_pos' hy0 hy1
  rw [hysq] at hdiag
  have hCy : 0 < gFun x - gFun y := by
    have := gFun_strictAntiOn (Set.mem_Ioo.mpr ⟨hx0, hx1⟩) (Set.mem_Ioo.mpr ⟨hy0, hy1⟩) hxy
    linarith
  have hkey : (gFun x - gFun y) * x < (1 - gFun x) * gFun y := by nlinarith
  have hsq : ((gFun x - gFun y) * (gFun x - gFun y)) / (gFun y * gFun y)
      < (1 - gFun x) ^ 2 / x ^ 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hp : 0 < (gFun x - gFun y) * x := by positivity
    have hq : (gFun x - gFun y) * x < (1 - gFun x) * gFun y := hkey
    have hd : 0 < (1 - gFun x) * gFun y - (gFun x - gFun y) * x := by linarith
    have hs : 0 < (1 - gFun x) * gFun y + (gFun x - gFun y) * x := by linarith
    nlinarith [mul_pos hd hs]
  have hCα : gFun x - gFun α ≥ 0 := by
    rcases eq_or_lt_of_le hαy with h | h
    · rw [← h]; linarith [hCy]
    · have := gFun_strictAntiOn (Set.mem_Ioo.mpr ⟨hx0, hx1⟩) (Set.mem_Ioo.mpr ⟨ha0, ha1⟩)
        (lt_trans hxy h)
      linarith
  have hfinal : (gFun x - gFun α) * (gFun x - gFun β) / (gFun α * gFun β)
      < (1 - gFun x) ^ 2 / x ^ 2 := lt_of_le_of_lt hmono hsq
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hfinal
  nlinarith [hfinal, hga, hgb, hx0]

end BSCAveraging.Core
