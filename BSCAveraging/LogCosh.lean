import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # `L = log cosh` and the odd kernels `M_g`

The elementary layer of `NOTES.md` §7c⁗ (interior uniqueness at `p = 0`).

`L(w) = log cosh w` is even, convex, with `L′ = tanh`, `L″ = 1 − tanh² = sech²`.
The kernels are `M_g(w) = L(w+g) − L(w−g)`, odd in `w` and in `g`, concave in
`w > 0` when `g > 0`.  The two facts §7c⁗ needs from this layer are

* `MG_div_antitoneOn` — `M_v(t)/t` is decreasing on `t > 0`;
* `phi_antitoneOn` — `ϕ(g) = (L(Y) − L(Y−2g))/g` is decreasing, which is exactly
  the tangent-line inequality for the convex `L`.

Together they give the inequality `(♦)` of §7c⁗ step 5. -/

namespace BSCAveraging.LC

open Real

lemma hd_congr {f : ℝ → ℝ} {d d' x : ℝ} (h : HasDerivAt f d x) (he : d = d') :
    HasDerivAt f d' x := he ▸ h

/-- `L(w) = log cosh w`. -/
noncomputable def LC (w : ℝ) : ℝ := Real.log (Real.cosh w)

lemma hasDerivAt_LC (w : ℝ) : HasDerivAt LC (Real.tanh w) w := by
  have h := (Real.hasDerivAt_cosh w).log (ne_of_gt (Real.cosh_pos w))
  rwa [← Real.tanh_eq_sinh_div_cosh] at h

/-- `L″ = sech²`. -/
lemma hasDerivAt_tanh (w : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh w ^ 2) w := by
  have hc : Real.cosh w ≠ 0 := ne_of_gt (Real.cosh_pos w)
  have h := (Real.hasDerivAt_sinh w).div (Real.hasDerivAt_cosh w) hc
  have hfun : (Real.sinh / Real.cosh : ℝ → ℝ) = Real.tanh := by
    funext x; exact (Real.tanh_eq_sinh_div_cosh x).symm
  rw [hfun] at h
  have hnum : Real.cosh w * Real.cosh w - Real.sinh w * Real.sinh w = 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq w]
  rw [hnum] at h
  exact h

lemma LC_even (w : ℝ) : LC (-w) = LC w := by simp [LC, Real.cosh_neg]

lemma tanh_monotone : Monotone Real.tanh := by
  have : StrictMono Real.tanh := by
    apply strictMono_of_deriv_pos
    intro w
    rw [(hasDerivAt_tanh w).deriv]
    positivity
  exact this.monotone

/-- Tangent-line inequality for a function whose derivative is monotone
(i.e. for a convex function). -/
lemma tangent_le_of_monotone_deriv {f f' : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (f' x) x)
    (hm : Monotone f') (z y : ℝ) : f z + f' z * (y - z) ≤ f y := by
  set h : ℝ → ℝ := fun t => f t - (f z + f' z * (t - z)) with hhdef
  have hh : ∀ t, HasDerivAt h (f' t - f' z) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => f z + f' z * (t - z)) (f' z) t := by
      have := (((hasDerivAt_id t).sub_const z).const_mul (f' z)).const_add (f z)
      simpa using this
    exact (hd t).sub h1
  have hz : h z = 0 := by simp [hhdef]
  rcases le_total z y with hzy | hzy
  · have : MonotoneOn h (Set.Ici z) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici z)
        (fun t _ => ((hh t).continuousAt).continuousWithinAt)
        (fun t _ => (hh t).differentiableAt.differentiableWithinAt)
      intro t ht
      rw [interior_Ici] at ht
      rw [(hh t).deriv]
      have := hm (le_of_lt ht)
      linarith
    have := this (Set.self_mem_Ici) (Set.mem_Ici.mpr hzy) hzy
    rw [hz] at this
    simp only [hhdef] at this
    linarith
  · have : AntitoneOn h (Set.Iic z) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic z)
        (fun t _ => ((hh t).continuousAt).continuousWithinAt)
        (fun t _ => (hh t).differentiableAt.differentiableWithinAt)
      intro t ht
      rw [interior_Iic] at ht
      rw [(hh t).deriv]
      have := hm (le_of_lt ht)
      linarith
    have := this (Set.mem_Iic.mpr hzy) (Set.self_mem_Iic) hzy
    rw [hz] at this
    simp only [hhdef] at this
    linarith

/-- The tangent line to `L` lies below `L`. -/
lemma LC_tangent_le (z y : ℝ) : LC z + Real.tanh z * (y - z) ≤ LC y :=
  tangent_le_of_monotone_deriv hasDerivAt_LC tanh_monotone z y

lemma continuous_LC : Continuous LC :=
  Real.continuous_cosh.log (fun x => ne_of_gt (Real.cosh_pos x))

lemma continuous_sech_sq (c : ℝ) : Continuous (fun w : ℝ => 1 / Real.cosh (w - c) ^ 2) := by
  refine continuous_const.div (by fun_prop) (fun x => pow_ne_zero 2 (ne_of_gt (Real.cosh_pos _)))

/-- The odd kernel `M_g(w) = L(w+g) − L(w−g)`. -/
noncomputable def MG (g w : ℝ) : ℝ := LC (w + g) - LC (w - g)

lemma MG_odd (g w : ℝ) : MG g (-w) = - MG g w := by
  simp only [MG]
  rw [show -w + g = -(w - g) by ring, show -w - g = -(w + g) by ring, LC_even, LC_even]
  ring


lemma hasDerivAt_MG (g w : ℝ) :
    HasDerivAt (MG g) (Real.tanh (w + g) - Real.tanh (w - g)) w := by
  have h1 : HasDerivAt (fun x : ℝ => LC (x + g)) (Real.tanh (w + g)) w := by
    have h := (hasDerivAt_LC (w + g)).comp w ((hasDerivAt_id w).add_const g)
    simpa [Function.comp_def] using h
  have h2 : HasDerivAt (fun x : ℝ => LC (x - g)) (Real.tanh (w - g)) w := by
    have h := (hasDerivAt_LC (w - g)).comp w ((hasDerivAt_id w).sub_const g)
    simpa [Function.comp_def] using h
  exact h1.sub h2

lemma MG_pos {g w : ℝ} (hg : 0 < g) (hw : 0 < w) : 0 < MG g w := by
  have h1 : |w - g| < w + g := by
    rw [abs_lt]; constructor <;> linarith
  have h2 : Real.cosh (w - g) < Real.cosh (w + g) := by
    rw [← Real.cosh_abs (w - g)]
    exact Real.cosh_strictMonoOn (Set.mem_Ici.mpr (abs_nonneg _))
      (Set.mem_Ici.mpr (by linarith)) h1
  have h3 : 0 < Real.cosh (w - g) := Real.cosh_pos _
  exact sub_pos.mpr (Real.log_lt_log h3 h2)

lemma MG_symm (g w : ℝ) : MG g w = MG w g := by
  simp only [MG]
  rw [show w + g = g + w by ring, show w - g = -(g - w) by ring, LC_even]

/-- `sech²` is strictly decreasing in `|·|`: `M_g′` is antitone on `[0,∞)`. -/
lemma MG_deriv_antitoneOn {g : ℝ} (hg : 0 < g) :
    AntitoneOn (fun w : ℝ => Real.tanh (w + g) - Real.tanh (w - g)) (Set.Ici (0:ℝ)) := by
  have hd : ∀ w : ℝ, HasDerivAt (fun w : ℝ => Real.tanh (w + g) - Real.tanh (w - g))
      (1 / Real.cosh (w + g) ^ 2 - 1 / Real.cosh (w - g) ^ 2) w := by
    intro w
    have h1 : HasDerivAt (fun x : ℝ => Real.tanh (x + g)) (1 / Real.cosh (w + g) ^ 2) w := by
      have h := (hasDerivAt_tanh (w + g)).comp w ((hasDerivAt_id w).add_const g)
      simpa [Function.comp_def] using h
    have h2 : HasDerivAt (fun x : ℝ => Real.tanh (x - g)) (1 / Real.cosh (w - g) ^ 2) w := by
      have h := (hasDerivAt_tanh (w - g)).comp w ((hasDerivAt_id w).sub_const g)
      simpa [Function.comp_def] using h
    exact h1.sub h2
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun w _ => ((hd w).continuousAt).continuousWithinAt)
    (fun w _ => (hd w).differentiableAt.differentiableWithinAt)
  intro w hw
  rw [interior_Ici] at hw
  simp only [Set.mem_Ioi] at hw
  rw [(hd w).deriv]
  have habs : |w - g| < w + g := by rw [abs_lt]; constructor <;> linarith
  have hlt : Real.cosh (w - g) < Real.cosh (w + g) := by
    rw [← Real.cosh_abs (w - g)]
    exact Real.cosh_strictMonoOn (Set.mem_Ici.mpr (abs_nonneg _))
      (Set.mem_Ici.mpr (by linarith)) habs
  have h1 : 0 < Real.cosh (w - g) := Real.cosh_pos _
  have h2 : 0 < Real.cosh (w + g) := Real.cosh_pos _
  have : 1 / Real.cosh (w + g) ^ 2 ≤ 1 / Real.cosh (w - g) ^ 2 := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  linarith

/-- `M_g` is concave on `[0,∞)`, so it lies above its tangents there:
`t·M_g′(t) ≤ M_g(t)`. -/
lemma MG_tangent {g t : ℝ} (hg : 0 < g) (ht : 0 < t) :
    t * (Real.tanh (t + g) - Real.tanh (t - g)) ≤ MG g t := by
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (MG g)
    (fun w => Real.tanh (w + g) - Real.tanh (w - g)) ht
    (fun w _ => ((hasDerivAt_MG g w).continuousAt).continuousWithinAt)
    (fun w _ => hasDerivAt_MG g w)
  have hz : MG g 0 = 0 := by
    have := MG_odd g 0; simp at this; linarith [this]
  rw [hz, sub_zero] at hslope
  have hmono := MG_deriv_antitoneOn hg (Set.mem_Ici.mpr (le_of_lt hξ.1))
    (Set.mem_Ici.mpr (le_of_lt ht)) (le_of_lt hξ.2)
  have hmono' : Real.tanh (t + g) - Real.tanh (t - g)
      ≤ Real.tanh (ξ + g) - Real.tanh (ξ - g) := hmono
  rw [hslope, sub_zero] at hmono'
  have h2 : 0 ≤ (MG g t / t - (Real.tanh (t + g) - Real.tanh (t - g))) * t :=
    mul_nonneg (by linarith) (le_of_lt ht)
  have ht' : t ≠ 0 := ne_of_gt ht
  field_simp at h2
  linarith

/-- `M_v(t)/t` is decreasing on `t > 0`. -/
lemma MG_div_antitoneOn {g : ℝ} (hg : 0 < g) :
    AntitoneOn (fun t : ℝ => MG g t / t) (Set.Ioi (0:ℝ)) := by
  have hd : ∀ t : ℝ, t ≠ 0 → HasDerivAt (fun t : ℝ => MG g t / t)
      (((Real.tanh (t + g) - Real.tanh (t - g)) * t - MG g t) / t ^ 2) t := by
    intro t ht
    have hM : HasDerivAt (fun t : ℝ => MG g t)
        (Real.tanh (t + g) - Real.tanh (t - g)) t := hasDerivAt_MG g t
    exact hd_congr (hM.div (hasDerivAt_id' (𝕜 := ℝ) (x := t)) ht) (by ring)
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun t ht => ((hd t (ne_of_gt ht)).continuousAt).continuousWithinAt)
    (fun t ht => by
      rw [interior_Ioi] at ht
      exact (hd t (ne_of_gt ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [interior_Ioi] at ht
  rw [(hd t (ne_of_gt ht)).deriv]
  have := MG_tangent hg ht
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  nlinarith

/-- `ϕ(g) = (L(Y) − L(Y−2g))/g` is decreasing — the tangent-line inequality for
the convex `L`. -/
lemma phi_antitoneOn (Y : ℝ) :
    AntitoneOn (fun g : ℝ => (LC Y - LC (Y - 2 * g)) / g) (Set.Ioi (0:ℝ)) := by
  have hd : ∀ g : ℝ, g ≠ 0 → HasDerivAt (fun g : ℝ => (LC Y - LC (Y - 2 * g)) / g)
      ((2 * Real.tanh (Y - 2 * g) * g - (LC Y - LC (Y - 2 * g))) / g ^ 2) g := by
    intro g hg
    have h1 : HasDerivAt (fun g : ℝ => LC Y - LC (Y - 2 * g))
        (2 * Real.tanh (Y - 2 * g)) g := by
      have hin : HasDerivAt (fun g : ℝ => Y - 2 * g) (-2) g := by
        simpa using ((hasDerivAt_id g).const_mul (2:ℝ)).const_sub Y
      have h := (hasDerivAt_LC (Y - 2 * g)).comp g hin
      rw [Function.comp_def] at h
      have h2 : HasDerivAt (fun x : ℝ => LC (Y - 2 * x)) (Real.tanh (Y - 2 * g) * -2) g := h
      exact hd_congr (h2.const_sub (LC Y)) (by ring)
    exact hd_congr (h1.div (hasDerivAt_id' (𝕜 := ℝ) (x := g)) hg) (by ring)
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun g hg => ((hd g (ne_of_gt hg)).continuousAt).continuousWithinAt)
    (fun g hg => by
      rw [interior_Ioi] at hg
      exact (hd g (ne_of_gt hg)).differentiableAt.differentiableWithinAt)
  intro g hg
  rw [interior_Ioi] at hg
  rw [(hd g (ne_of_gt hg)).deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have := LC_tangent_le (Y - 2 * g) Y
  have he : Y - (Y - 2 * g) = 2 * g := by ring
  rw [he] at this
  linarith

/-- **(♦)** of §7c⁗ step 5: `m·M_v(m−X) ≥ (m−X)·M_m(v−X)` for `X ≥ 0`,
`0 < m−X`.  Both sides are `Φ(g, Y−g)` for the *same* `Y = m+v−X`, so it is
`ϕ` decreasing. -/
theorem diamond {m v X : ℝ} (hmX : 0 < m - X) (hX : 0 ≤ X) :
    (m - X) * MG m (v - X) ≤ m * MG v (m - X) := by
  have hm : 0 < m := by linarith
  set Y := m + v - X with hY
  have e1 : MG v (m - X) = LC Y - LC (Y - 2 * (m - X)) := by
    simp only [MG, hY]
    rw [show m - X + v = m + v - X by ring, show m - X - v = -(m + v - X - 2 * (m - X)) by ring,
      LC_even]
  have e2 : MG m (v - X) = LC Y - LC (Y - 2 * m) := by
    simp only [MG, hY]
    rw [show v - X + m = m + v - X by ring, show v - X - m = m + v - X - 2 * m by ring]
  have hmono := phi_antitoneOn Y (Set.mem_Ioi.mpr hmX) (Set.mem_Ioi.mpr hm) (by linarith)
  rw [e1, e2]
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at hmono
  linarith

/-! ### The Green identity

If `F` and `G` both vanish at the ends of the window, then `∫ F·G″ = ∫ F″·G`:
the Wronskian `F G′ − F′ G` is an antiderivative of `F G″ − F″ G` and vanishes
at both ends.  No integration-by-parts lemma is needed — one application of
`integral_eq_sub_of_hasDerivAt`. -/
lemma green_identity {a b : ℝ} {F F' F'' G G' G'' : ℝ → ℝ}
    (hF : ∀ w, HasDerivAt F (F' w) w) (hF' : ∀ w, HasDerivAt F' (F'' w) w)
    (hG : ∀ w, HasDerivAt G (G' w) w) (hG' : ∀ w, HasDerivAt G' (G'' w) w)
    (cF : Continuous F) (cF'' : Continuous F'') (cG : Continuous G) (cG'' : Continuous G'')
    (hFa : F a = 0) (hFb : F b = 0) (hGa : G a = 0) (hGb : G b = 0) :
    (∫ w in a..b, F w * G'' w) = ∫ w in a..b, F'' w * G w := by
  have hW : ∀ w : ℝ, HasDerivAt (fun w : ℝ => F w * G' w - F' w * G w)
      (F w * G'' w - F'' w * G w) w := by
    intro w
    have h1 := (hF w).mul (hG' w)
    have h2 := (hF' w).mul (hG w)
    exact hd_congr (h1.sub h2) (by ring)
  have hint : (∫ w in a..b, (F w * G'' w - F'' w * G w))
      = (F b * G' b - F' b * G b) - (F a * G' a - F' a * G a) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => hW w) ?_
    apply Continuous.intervalIntegrable
    fun_prop
  rw [hFa, hFb, hGa, hGb] at hint
  simp only [zero_mul, mul_zero, sub_zero, zero_sub, sub_self] at hint
  have hsplit : (∫ w in a..b, (F w * G'' w - F'' w * G w))
      = (∫ w in a..b, F w * G'' w) - ∫ w in a..b, F'' w * G w := by
    apply intervalIntegral.integral_sub
    · exact (cF.mul cG'').intervalIntegrable a b
    · exact (cF''.mul cG).intervalIntegrable a b
  rw [hsplit] at hint
  linarith

/-! ### The window, the deficit, and the bitangency residual -/

/-- `M_n″(w) = sech²(w+n) − sech²(w−n)`; odd in `w`, negative for `w,n > 0`. -/
noncomputable def MGpp (n w : ℝ) : ℝ :=
  1 / Real.cosh (w + n) ^ 2 - 1 / Real.cosh (w - n) ^ 2

lemma MGpp_odd (n w : ℝ) : MGpp n (-w) = - MGpp n w := by
  simp only [MGpp]
  rw [show -w + n = -(w - n) by ring, show -w - n = -(w + n) by ring,
    Real.cosh_neg, Real.cosh_neg]
  ring

lemma MGpp_neg {n w : ℝ} (hn : 0 < n) (hw : 0 < w) : MGpp n w < 0 := by
  have habs : |w - n| < w + n := by rw [abs_lt]; constructor <;> linarith
  have hlt : Real.cosh (w - n) < Real.cosh (w + n) := by
    rw [← Real.cosh_abs (w - n)]
    exact Real.cosh_strictMonoOn (Set.mem_Ici.mpr (abs_nonneg _))
      (Set.mem_Ici.mpr (by linarith)) habs
  have h1 : 0 < Real.cosh (w - n) := Real.cosh_pos _
  have : 1 / Real.cosh (w + n) ^ 2 < 1 / Real.cosh (w - n) ^ 2 := by
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  simp only [MGpp]; linarith

lemma hasDerivAt_MGp (n w : ℝ) :
    HasDerivAt (fun w : ℝ => Real.tanh (w + n) - Real.tanh (w - n)) (MGpp n w) w := by
  have h1 : HasDerivAt (fun x : ℝ => Real.tanh (x + n)) (1 / Real.cosh (w + n) ^ 2) w := by
    have h := (hasDerivAt_tanh (w + n)).comp w ((hasDerivAt_id w).add_const n)
    simpa [Function.comp_def] using h
  have h2 : HasDerivAt (fun x : ℝ => Real.tanh (x - n)) (1 / Real.cosh (w - n) ^ 2) w := by
    have h := (hasDerivAt_tanh (w - n)).comp w ((hasDerivAt_id w).sub_const n)
    simpa [Function.comp_def] using h
  exact h1.sub h2

/-- The deficit of `M_n` against its chord over `[X−m, X+m]`. -/
noncomputable def Dfun (n m X : ℝ) (w : ℝ) : ℝ :=
  MG n w - (MG n (X - m) + (MG n (X + m) - MG n (X - m)) * (w - (X - m)) / (2 * m))

/-- `L(·−v)` minus its chord over the same window. -/
noncomputable def Kfun (v m X : ℝ) (w : ℝ) : ℝ :=
  LC (w - v)
    - (LC (X - m - v) + (LC (X + m - v) - LC (X - m - v)) * (w - (X - m)) / (2 * m))

lemma Dfun_left {n m X : ℝ} : Dfun n m X (X - m) = 0 := by simp [Dfun]

lemma Dfun_right {n m X : ℝ} (hm : 0 < m) : Dfun n m X (X + m) = 0 := by
  simp only [Dfun]
  have : X + m - (X - m) = 2 * m := by ring
  rw [this]
  field_simp
  ring

lemma Kfun_left {v m X : ℝ} : Kfun v m X (X - m) = 0 := by simp [Kfun]

lemma Kfun_right {v m X : ℝ} (hm : 0 < m) : Kfun v m X (X + m) = 0 := by
  simp only [Kfun]
  have h1 : X + m - (X - m) = 2 * m := by ring
  have h2 : X + m - v = X + m - v := rfl
  rw [h1]
  field_simp
  ring

lemma hasDerivAt_Dfun (n m X w : ℝ) (hm : 0 < m) :
    HasDerivAt (Dfun n m X)
      ((Real.tanh (w + n) - Real.tanh (w - n))
        - (MG n (X + m) - MG n (X - m)) / (2 * m)) w := by
  have h1 : HasDerivAt (fun w : ℝ =>
      MG n (X - m) + (MG n (X + m) - MG n (X - m)) * (w - (X - m)) / (2 * m))
      ((MG n (X + m) - MG n (X - m)) / (2 * m)) w := by
    have h := (((hasDerivAt_id w).sub_const (X - m)).const_mul
      (MG n (X + m) - MG n (X - m))).div_const (2 * m)
    exact hd_congr (h.const_add (MG n (X - m))) (by ring)
  exact (hasDerivAt_MG n w).sub h1

lemma hasDerivAt_Kfun (v m X w : ℝ) (hm : 0 < m) :
    HasDerivAt (Kfun v m X)
      (Real.tanh (w - v) - (LC (X + m - v) - LC (X - m - v)) / (2 * m)) w := by
  have h0 : HasDerivAt (fun w : ℝ => LC (w - v)) (Real.tanh (w - v)) w := by
    have h := (hasDerivAt_LC (w - v)).comp w ((hasDerivAt_id w).sub_const v)
    simpa [Function.comp_def] using h
  have h1 : HasDerivAt (fun w : ℝ =>
      LC (X - m - v) + (LC (X + m - v) - LC (X - m - v)) * (w - (X - m)) / (2 * m))
      ((LC (X + m - v) - LC (X - m - v)) / (2 * m)) w := by
    have h := (((hasDerivAt_id w).sub_const (X - m)).const_mul
      (LC (X + m - v) - LC (X - m - v))).div_const (2 * m)
    exact hd_congr (h.const_add (LC (X - m - v))) (by ring)
  exact h0.sub h1

/-- A function with nonincreasing derivative and zero boundary values is
nonnegative on the interval (concavity, by two mean-value theorems). -/
lemma nonneg_of_antitone_deriv_zero_ends {H H' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ w, HasDerivAt H (H' w) w) (hanti : AntitoneOn H' (Set.Icc a b))
    (hHa : H a = 0) (hHb : H b = 0) {w : ℝ} (hw : w ∈ Set.Icc a b) : 0 ≤ H w := by
  rcases eq_or_lt_of_le hw.1 with h | h1
  · rw [← h, hHa]
  rcases eq_or_lt_of_le hw.2 with h | h2
  · rw [h, hHb]
  by_contra hneg
  push_neg at hneg
  obtain ⟨ξ₁, hξ₁, e₁⟩ := exists_hasDerivAt_eq_slope H H' h1
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
  obtain ⟨ξ₂, hξ₂, e₂⟩ := exists_hasDerivAt_eq_slope H H' h2
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
  rw [hHa, sub_zero] at e₁
  rw [hHb, zero_sub] at e₂
  have hd1 : H' ξ₁ < 0 := by
    rw [e₁]; exact div_neg_of_neg_of_pos hneg (by linarith [hξ₁.1, hξ₁.2])
  have hd2 : 0 < H' ξ₂ := by
    rw [e₂]; exact div_pos (by linarith) (by linarith [hξ₂.1, hξ₂.2])
  have := hanti ⟨le_of_lt hξ₁.1, le_of_lt (lt_trans hξ₁.2 h2)⟩
    ⟨le_of_lt (lt_trans h1 hξ₂.1), le_of_lt hξ₂.2⟩
    (le_of_lt (lt_trans hξ₁.2 hξ₂.1))
  linarith

/-- `K ≤ 0` on the window: `L(·−v)` lies below its chord. -/
lemma Kfun_nonpos {v m X : ℝ} (hm : 0 < m) {w : ℝ}
    (hw : w ∈ Set.Icc (X - m) (X + m)) : Kfun v m X w ≤ 0 := by
  set E := (LC (X + m - v) - LC (X - m - v)) / (2 * m) with hE
  have hd : ∀ z : ℝ, HasDerivAt (fun z : ℝ => - Kfun v m X z) (E - Real.tanh (z - v)) z := by
    intro z
    exact hd_congr (hasDerivAt_Kfun v m X z hm).neg (by rw [hE]; ring)
  have hanti : AntitoneOn (fun z : ℝ => E - Real.tanh (z - v)) (Set.Icc (X - m) (X + m)) := by
    intro p _ q _ hpq
    have := tanh_monotone (show p - v ≤ q - v by linarith)
    simpa using by linarith
  have := nonneg_of_antitone_deriv_zero_ends (by linarith : X - m < X + m) hd hanti
    (by rw [Kfun_left]; ring) (by rw [Kfun_right hm]; ring) hw
  linarith

/-- **The Green identity for the window**: the residual equals `∫ M_n″·K`. -/
theorem residual_green {m n v X : ℝ} (hm : 0 < m) :
    (∫ w in (X - m)..(X + m), Dfun n m X w * (1 / Real.cosh (w - v) ^ 2))
      = ∫ w in (X - m)..(X + m), MGpp n w * Kfun v m X w := by
  have hDd : ∀ w : ℝ, HasDerivAt (Dfun n m X)
      ((Real.tanh (w + n) - Real.tanh (w - n))
        - (MG n (X + m) - MG n (X - m)) / (2 * m)) w := fun w => hasDerivAt_Dfun n m X w hm
  have hDd' : ∀ w : ℝ, HasDerivAt (fun w : ℝ => (Real.tanh (w + n) - Real.tanh (w - n))
      - (MG n (X + m) - MG n (X - m)) / (2 * m)) (MGpp n w) w := by
    intro w
    exact (hasDerivAt_MGp n w).sub_const _
  have hKd : ∀ w : ℝ, HasDerivAt (Kfun v m X)
      (Real.tanh (w - v) - (LC (X + m - v) - LC (X - m - v)) / (2 * m)) w :=
    fun w => hasDerivAt_Kfun v m X w hm
  have hKd' : ∀ w : ℝ, HasDerivAt (fun w : ℝ =>
      Real.tanh (w - v) - (LC (X + m - v) - LC (X - m - v)) / (2 * m))
      (1 / Real.cosh (w - v) ^ 2) w := by
    intro w
    have h := (hasDerivAt_tanh (w - v)).comp w ((hasDerivAt_id w).sub_const v)
    have h2 : HasDerivAt (fun x : ℝ => Real.tanh (x - v)) (1 / Real.cosh (w - v) ^ 2) w := by
      simpa [Function.comp_def] using h
    exact h2.sub_const _
  have hcosh : ∀ z : ℝ, Real.cosh z ≠ 0 := fun z => ne_of_gt (Real.cosh_pos z)
  have cLCs : ∀ c : ℝ, Continuous (fun w : ℝ => LC (w + c)) :=
    fun c => continuous_LC.comp (by fun_prop)
  have cD : Continuous (Dfun n m X) := by
    unfold Dfun MG
    exact ((cLCs n).sub (by
      have := cLCs (-n); simpa [sub_eq_add_neg] using this)).sub (by fun_prop)
  have cMGpp : Continuous (MGpp n) := by
    unfold MGpp
    refine Continuous.sub ?_ ?_
    · exact continuous_const.div (by fun_prop)
        (fun x => pow_ne_zero 2 (ne_of_gt (Real.cosh_pos _)))
    · exact continuous_const.div (by fun_prop)
        (fun x => pow_ne_zero 2 (ne_of_gt (Real.cosh_pos _)))
  have cK : Continuous (Kfun v m X) := by
    unfold Kfun
    refine Continuous.sub ?_ (by fun_prop)
    have := cLCs (-v); simpa [sub_eq_add_neg] using this
  exact green_identity hDd hDd' hKd hKd' cD cMGpp cK (continuous_sech_sq v)
    Dfun_left (Dfun_right hm) Kfun_left (Kfun_right hm)

/-- Strict version: strictly decreasing derivative and zero ends give strict
positivity in the interior. -/
lemma pos_of_strictAnti_deriv_zero_ends {H H' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ w, HasDerivAt H (H' w) w) (hanti : StrictAntiOn H' (Set.Icc a b))
    (hHa : H a = 0) (hHb : H b = 0) {w : ℝ} (hw : w ∈ Set.Ioo a b) : 0 < H w := by
  obtain ⟨h1, h2⟩ := hw
  by_contra hneg
  push_neg at hneg
  obtain ⟨ξ₁, hξ₁, e₁⟩ := exists_hasDerivAt_eq_slope H H' h1
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
  obtain ⟨ξ₂, hξ₂, e₂⟩ := exists_hasDerivAt_eq_slope H H' h2
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
  rw [hHa, sub_zero] at e₁
  rw [hHb, zero_sub] at e₂
  have hd1 : H' ξ₁ ≤ 0 := by
    rw [e₁]; exact div_nonpos_of_nonpos_of_nonneg hneg (by linarith [hξ₁.1, hξ₁.2])
  have hd2 : 0 ≤ H' ξ₂ := by
    rw [e₂]; exact div_nonneg (by linarith) (by linarith [hξ₂.1, hξ₂.2])
  have := hanti ⟨le_of_lt hξ₁.1, le_of_lt (lt_trans hξ₁.2 h2)⟩
    ⟨le_of_lt (lt_trans h1 hξ₂.1), le_of_lt hξ₂.2⟩ (lt_trans hξ₁.2 hξ₂.1)
  linarith

lemma Kfun_neg {v m X : ℝ} (hm : 0 < m) {w : ℝ}
    (hw : w ∈ Set.Ioo (X - m) (X + m)) : Kfun v m X w < 0 := by
  set E := (LC (X + m - v) - LC (X - m - v)) / (2 * m) with hE
  have hd : ∀ z : ℝ, HasDerivAt (fun z : ℝ => - Kfun v m X z) (E - Real.tanh (z - v)) z := by
    intro z
    exact hd_congr (hasDerivAt_Kfun v m X z hm).neg (by rw [hE]; ring)
  have hanti : StrictAntiOn (fun z : ℝ => E - Real.tanh (z - v)) (Set.Icc (X - m) (X + m)) := by
    intro p _ q _ hpq
    have hstr : StrictMono Real.tanh := by
      apply strictMono_of_deriv_pos
      intro w; rw [(hasDerivAt_tanh w).deriv]; positivity
    have := hstr (show p - v < q - v by linarith)
    simpa using by linarith
  have := pos_of_strictAnti_deriv_zero_ends hd hanti
    (by rw [Kfun_left]; ring) (by rw [Kfun_right hm]; ring) hw
  linarith

/-- `M_v(t)/t` is *strictly* decreasing on `t > 0`. -/
lemma MG_div_strictAntiOn {g : ℝ} (hg : 0 < g) :
    StrictAntiOn (fun t : ℝ => MG g t / t) (Set.Ioi (0:ℝ)) := by
  have hd : ∀ t : ℝ, t ≠ 0 → HasDerivAt (fun t : ℝ => MG g t / t)
      (((Real.tanh (t + g) - Real.tanh (t - g)) * t - MG g t) / t ^ 2) t := by
    intro t ht
    have hM : HasDerivAt (fun t : ℝ => MG g t)
        (Real.tanh (t + g) - Real.tanh (t - g)) t := hasDerivAt_MG g t
    exact hd_congr (hM.div (hasDerivAt_id' (𝕜 := ℝ) (x := t)) ht) (by ring)
  have hstrict : StrictAntiOn (fun w : ℝ => Real.tanh (w + g) - Real.tanh (w - g))
      (Set.Ioi (0:ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
      (fun w _ => ((hasDerivAt_MGp g w).continuousAt).continuousWithinAt)
    intro w hw
    rw [interior_Ioi] at hw
    rw [(hasDerivAt_MGp g w).deriv]
    exact MGpp_neg hg hw
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun t ht => ((hd t (ne_of_gt ht)).continuousAt).continuousWithinAt)
  intro t ht
  rw [interior_Ioi] at ht
  simp only [Set.mem_Ioi] at ht
  rw [(hd t (ne_of_gt ht)).deriv]
  -- strict tangent bound: `t·M′(t) < M(t)`
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (MG g)
    (fun w => Real.tanh (w + g) - Real.tanh (w - g)) ht
    (fun w _ => ((hasDerivAt_MG g w).continuousAt).continuousWithinAt)
    (fun w _ => hasDerivAt_MG g w)
  have hz : MG g 0 = 0 := by have := MG_odd g 0; simp at this; linarith [this]
  simp only [hz, sub_zero] at hslope
  have hlt := hstrict (Set.mem_Ioi.mpr hξ.1) (Set.mem_Ioi.mpr ht) hξ.2
  have hlt' : Real.tanh (t + g) - Real.tanh (t - g) < MG g t / t := by
    rw [← hslope]; exact hlt
  apply div_neg_of_neg_of_pos _ (by positivity)
  have h2 := (lt_div_iff₀ ht).mp hlt'
  linarith

/-- The reflection difference of `K`. -/
lemma Kfun_reflect {v m u t : ℝ} (hm : 0 < m) :
    Kfun v m (u + v) t - Kfun v m (u + v) (-t) = - MG v t - t * MG m u / m := by
  simp only [Kfun, MG]
  rw [show -t - v = -(t + v) by ring, LC_even]
  rw [show u + v + m - v = u + m by ring, show u + v - m - v = u - m by ring]
  field_simp
  ring

lemma continuous_MG (g : ℝ) : Continuous (MG g) := by
  unfold MG
  exact (continuous_LC.comp (by fun_prop)).sub (continuous_LC.comp (by fun_prop))

lemma continuous_MGpp (n : ℝ) : Continuous (MGpp n) := by
  unfold MGpp
  refine Continuous.sub ?_ ?_ <;>
    exact continuous_const.div (by fun_prop)
      (fun x => pow_ne_zero 2 (ne_of_gt (Real.cosh_pos _)))

/-- **The bitangency residual** of §7c⁗, `R_S`. -/
noncomputable def RS (m n u v : ℝ) : ℝ :=
  ∫ w in (u + v - m)..(u + v + m), Dfun n m (u + v) w * (1 / Real.cosh (w - v) ^ 2)

private lemma cont_integrand (n v m X : ℝ) :
    Continuous (fun w : ℝ => MGpp n w * Kfun v m X w) := by
  have cLCs : ∀ c : ℝ, Continuous (fun w : ℝ => LC (w + c)) :=
    fun c => continuous_LC.comp (by fun_prop)
  have cMGpp : Continuous (MGpp n) := continuous_MGpp n
  have cK : Continuous (Kfun v m X) := by
    unfold Kfun
    refine Continuous.sub ?_ (by fun_prop)
    have := cLCs (-v); simpa [sub_eq_add_neg] using this
  exact cMGpp.mul cK

/-- **(★)** of §7c⁗: for `v > 0` and `X = u+v ≥ 0` the residual is strictly
positive. -/
theorem residual_pos {m n u v : ℝ} (hm : 0 < m) (hn : 0 < n) (hv : 0 ≤ v)
    (hX : 0 ≤ u + v) (hne : 0 < v ∨ 0 < u + v) : 0 < RS m n u v := by
  set X := u + v with hXdef
  set F : ℝ → ℝ := fun w => MGpp n w * Kfun v m X w with hF
  have hcont : Continuous F := cont_integrand n v m X
  rw [RS, ← hXdef, residual_green hm]
  show (0:ℝ) < ∫ w in (X - m)..(X + m), F w
  have hab : X - m < X + m := by linarith
  rcases le_or_gt m X with hmX | hmX
  · -- the window lies in the concave half
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcont.intervalIntegrable _ _) _ hab
    intro w hw
    have hw0 : 0 < w := lt_of_le_of_lt (by linarith) hw.1
    exact mul_pos_of_neg_of_neg (MGpp_neg hn hw0) (Kfun_neg hm ⟨hw.1, hw.2⟩)
  · -- fold the symmetric part
    set c := m - X with hc
    have hc0 : 0 < c := by simp only [hc]; linarith
    have hcb : c ≤ X + m := by simp only [hc]; linarith
    have hac : X - m = -c := by simp only [hc]; ring
    -- the reflected integrand
    have hrefl : ∀ t : ℝ, F (-t) + F t = MGpp n t * (- MG v t - t * MG m u / m) := by
      intro t
      simp only [hF, MGpp_odd, hXdef]
      rw [← Kfun_reflect (v := v) (m := m) (u := u) (t := t) hm]
      ring
    have hfold : (∫ w in (-c)..c, F w)
        = ∫ t in (0:ℝ)..c, MGpp n t * (- MG v t - t * MG m u / m) := by
      have h1 : (∫ w in (-c)..(0:ℝ), F w) = ∫ t in (0:ℝ)..c, F (-t) := by
        have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := c) (f := F)
        rw [h]; norm_num
      have h2 : (∫ w in (-c)..(0:ℝ), F w) + (∫ w in (0:ℝ)..c, F w) = ∫ w in (-c)..c, F w :=
        intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
      have h3 : (∫ t in (0:ℝ)..c, F (-t)) + (∫ t in (0:ℝ)..c, F t)
          = ∫ t in (0:ℝ)..c, (F (-t) + F t) :=
        (intervalIntegral.integral_add
          ((hcont.comp continuous_neg).intervalIntegrable _ _)
          (hcont.intervalIntegrable _ _)).symm
      rw [← h2, h1, h3]
      exact intervalIntegral.integral_congr (fun t _ => hrefl t)
    -- the folded integrand is nonnegative
    have hkey : ∀ t : ℝ, 0 < t → t ≤ c → 0 ≤ MG v t + t * MG m u / m := by
      intro t ht0 htc
      rcases le_or_gt 0 u with hu | hu
      · have h1 : 0 ≤ MG m u := by
          rcases eq_or_lt_of_le hu with h | h
          · rw [← h]; norm_num [MG, LC_even]
          · exact le_of_lt (by rw [MG_symm]; exact MG_pos h hm)
        have h2 : 0 ≤ MG v t := by
          rcases eq_or_lt_of_le hv with h | h
          · rw [← h]; simp [MG]
          · exact le_of_lt (MG_pos h ht0)
        have h3 : 0 ≤ t * MG m u / m := by positivity
        linarith
      · -- `u < 0`: then `v > 0` automatically, and we use `M_v(t)/t` decreasing and (♦)
        have hv0 : 0 < v := by simp only [hXdef] at hX; linarith
        have hvX : 0 < v - X := by simp only [hXdef]; linarith
        have hmono := MG_div_antitoneOn hv0 (Set.mem_Ioi.mpr ht0) (Set.mem_Ioi.mpr hc0) htc
        have hd := diamond (m := m) (v := v) (X := X) (by simp only [hc] at hc0; linarith) hX
        have hMu : MG m u = - MG m (v - X) := by
          have : u = -(v - X) := by simp only [hXdef]; ring
          rw [this, MG_odd]
        rw [hMu]
        have hcv : MG m (v - X) / m ≤ MG v c / c := by
          rw [div_le_div_iff₀ hm hc0]
          simp only [hc]
          linarith [hd]
        have h1 : MG m (v - X) / m ≤ MG v t / t := le_trans hcv hmono
        have h2 : t * (MG m (v - X) / m) ≤ MG v t := by
          have := mul_le_mul_of_nonneg_left h1 (le_of_lt ht0)
          rw [mul_div_cancel₀ _ (ne_of_gt ht0)] at this
          linarith [this]
        have : t * (- MG m (v - X)) / m = - (t * (MG m (v - X) / m)) := by ring
        rw [this]
        linarith
    have hpiece1 : 0 ≤ ∫ t in (0:ℝ)..c, MGpp n t * (- MG v t - t * MG m u / m) := by
      apply intervalIntegral.integral_nonneg (le_of_lt hc0)
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h]; norm_num [MGpp, Real.cosh_neg]
      · have h1 := MGpp_neg hn h
        have h2 := hkey t h ht.2
        nlinarith
    have hpiece2 : 0 ≤ ∫ w in c..(X + m), F w := by
      apply intervalIntegral.integral_nonneg hcb
      intro w hw
      have hw0 : 0 < w := lt_of_lt_of_le hc0 hw.1
      have h1 := MGpp_neg hn hw0
      have h2 := Kfun_nonpos (v := v) (m := m) (X := X) hm
        (w := w) ⟨by simp only [hac]; linarith [hw.1, hc0], hw.2⟩
      simp only [hF]
      nlinarith
    have hsum : (∫ w in (X - m)..c, F w) + (∫ w in c..(X + m), F w)
        = ∫ w in (X - m)..(X + m), F w :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    rw [← hsum, hac, hfold]
    rcases eq_or_lt_of_le hX with hX0 | hX0
    · -- `X = 0`: the symmetric part is strictly positive
      have hcm : c = m := by simp only [hc, ← hX0]; ring
      have hz : (∫ w in c..(X + m), F w) = 0 := by
        have : c = X + m := by simp only [hcm, ← hX0]; ring
        rw [this, intervalIntegral.integral_same]
      rw [hz, add_zero]
      have hcf : Continuous (fun t : ℝ => MGpp n t * (- MG v t - t * MG m u / m)) :=
        (continuous_MGpp n).mul (((continuous_MG v).neg).sub (by fun_prop))
      apply intervalIntegral.intervalIntegral_pos_of_pos_on
        (hcf.intervalIntegrable _ _) _ hc0
      intro t ht
      have hu : u = -v := by simp only [hXdef] at hX0; linarith
      have hv0 : 0 < v := by
        rcases hne with h | h
        · exact h
        · exfalso; simp only [hXdef] at hX0 h; linarith
      have hstrict := MG_div_strictAntiOn hv0 (Set.mem_Ioi.mpr ht.1)
        (Set.mem_Ioi.mpr (by linarith : (0:ℝ) < c)) ht.2
      have hMu : MG m u = - MG v m := by rw [hu, MG_odd, MG_symm]
      rw [hMu, hcm] at *
      have h1 : MG v m / m < MG v t / t := by rw [hcm] at hstrict; exact hstrict
      have h2 : t * (MG v m / m) < MG v t := by
        have := mul_lt_mul_of_pos_left h1 ht.1
        rw [mul_div_cancel₀ _ (ne_of_gt ht.1)] at this
        linarith
      refine mul_pos_of_neg_of_neg (MGpp_neg hn ht.1) ?_
      have : t * -MG v m / m = - (t * (MG v m / m)) := by ring
      rw [this]
      linarith
    · -- `X > 0`: the outer part is strictly positive
      have hcb' : c < X + m := by simp only [hc]; linarith
      have hpos : 0 < ∫ w in c..(X + m), F w := by
        apply intervalIntegral.intervalIntegral_pos_of_pos_on
          (hcont.intervalIntegrable _ _) _ hcb'
        intro w hw
        have hw0 : 0 < w := lt_trans hc0 hw.1
        exact mul_pos_of_neg_of_neg (MGpp_neg hn hw0)
          (Kfun_neg hm ⟨by simp only [hac]; linarith [hw.1, hc0], hw.2⟩)
      linarith

/-- The deficit is odd under `(X,w) ↦ (−X,−w)`. -/
lemma Dfun_odd {n m X w : ℝ} (hm : 0 < m) :
    Dfun n m (-X) (-w) = - Dfun n m X w := by
  simp only [Dfun]
  rw [show -X - m = -(X + m) by ring, show -X + m = -(X - m) by ring,
    MG_odd, MG_odd, MG_odd]
  field_simp
  ring

/-- `R_S` is odd under `(u,v) ↦ (−u,−v)`. -/
theorem RS_odd {m n u v : ℝ} (hm : 0 < m) : RS m n (-u) (-v) = - RS m n u v := by
  have hX : -u + -v = -(u + v) := by ring
  simp only [RS, hX]
  have hcomp : ∀ f : ℝ → ℝ, (∫ x in (-(u+v) - m)..(-(u+v) + m), f x)
      = ∫ x in ((u+v) - m)..((u+v) + m), f (-x) := by
    intro f
    have h := intervalIntegral.integral_comp_neg (a := ((u+v) - m)) (b := ((u+v) + m)) (f := f)
    rw [h]
    congr 1 <;> ring
  rw [hcomp]
  rw [show (∫ x in ((u+v) - m)..((u+v) + m),
      Dfun n m (-(u+v)) (-x) * (1 / Real.cosh (-x - -v) ^ 2))
      = ∫ x in ((u+v) - m)..((u+v) + m),
        -(Dfun n m (u+v) x * (1 / Real.cosh (x - v) ^ 2)) from ?_]
  · exact intervalIntegral.integral_neg
  · refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [Dfun_odd hm, show -x - -v = -(x - v) by ring, Real.cosh_neg]
    ring

/-- **Interior uniqueness at `p = 0`** (§7c⁗): if both bitangency residuals
vanish then both skews do, i.e. the interior fixed point is the symmetric
(BSC) pair. -/
theorem skews_vanish {m n u v : ℝ} (hm : 0 < m) (hn : 0 < n)
    (hS : RS m n u v = 0) (hT : RS n m v u = 0) : u = 0 ∧ v = 0 := by
  have hSneg : RS m n (-u) (-v) = 0 := by rw [RS_odd hm, hS]; ring
  have hTneg : RS n m (-v) (-u) = 0 := by rw [RS_odd hn, hT]; ring
  have hX0 : u + v = 0 := by
    rcases lt_trichotomy (u + v) 0 with h | h | h
    · exfalso
      rcases le_or_gt 0 (-v) with hv | hv
      · have h2 := residual_pos (m := m) (n := n) (u := -u) (v := -v) hm hn hv
          (by linarith) (Or.inr (by linarith))
        rw [hSneg] at h2; exact lt_irrefl 0 h2
      · have hu : 0 ≤ -u := by linarith
        have h2 := residual_pos (m := n) (n := m) (u := -v) (v := -u) hn hm hu
          (by linarith) (Or.inr (by linarith))
        rw [hTneg] at h2; exact lt_irrefl 0 h2
    · exact h
    · exfalso
      rcases le_or_gt 0 v with hv | hv
      · have h2 := residual_pos (m := m) (n := n) (u := u) (v := v) hm hn hv
          (by linarith) (Or.inr (by linarith))
        rw [hS] at h2; exact lt_irrefl 0 h2
      · have hu : 0 ≤ u := by linarith
        have h2 := residual_pos (m := n) (n := m) (u := v) (v := u) hn hm hu
          (by linarith) (Or.inr (by linarith))
        rw [hT] at h2; exact lt_irrefl 0 h2
  have hv0 : v = 0 := by
    rcases lt_trichotomy v 0 with h | h | h
    · exfalso
      have h2 := residual_pos (m := m) (n := n) (u := -u) (v := -v) hm hn
        (by linarith : (0:ℝ) ≤ -v) (by linarith) (Or.inl (by linarith))
      rw [hSneg] at h2; exact lt_irrefl 0 h2
    · exact h
    · exfalso
      have h2 := residual_pos (m := m) (n := n) (u := u) (v := v) hm hn
        (le_of_lt h) (by linarith) (Or.inl h)
      rw [hS] at h2; exact lt_irrefl 0 h2
  exact ⟨by linarith, hv0⟩

/-! ### From bitangency to the residual

`NOTES.md` §7c⁗.  In `θ = artanh` coordinates the `U`-side slack is

```
D(σ) = l₀ + l₁·tanh σ + l₂·f_e(tanh σ) − G(σ) ,   f_e(tanh σ) = σ tanh σ − L(σ),
```

with `G` the atom value against the two-atom `V`-side `(tanh γ, −tanh δ)`.  The
key collapse is that the *mean-zero* weights make both mixed coefficients equal
to `k = sinh γ sinh δ / sinh(γ+δ)`, so

```
G′(σ)·cosh²σ = k·[ L(σ+γ) − L(σ−δ) − L(γ) + L(δ) ] = k·[ M_n(σ+v) − M_n(v) ],
```

`n = (γ+δ)/2`, `v = (γ−δ)/2`: the odd-kernel form.  The two tangency conditions
then say that the affine function `l₁ + l₂σ` matches `k·M_n` at the two window
ends, i.e. it *is* the chord, and the two value conditions say the integral of
the difference against `sech²` vanishes — which is exactly `R_S = 0`. -/

/-- `f(z) = (1+z)·log(1+z)`. -/
noncomputable def fF (z : ℝ) : ℝ := (1 + z) * Real.log (1 + z)

/-- `k = sinh γ · sinh δ / sinh(γ+δ)`, the common mixed weight. -/
noncomputable def kco (γ δ : ℝ) : ℝ := Real.sinh γ * Real.sinh δ / Real.sinh (γ + δ)

lemma kco_pos {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) : 0 < kco γ δ := by
  have h1 : 0 < Real.sinh γ := Real.sinh_pos_iff.mpr hγ
  have h2 : 0 < Real.sinh δ := Real.sinh_pos_iff.mpr hδ
  have h3 : 0 < Real.sinh (γ + δ) := Real.sinh_pos_iff.mpr (by linarith)
  unfold kco; positivity

lemma one_add_tanh_mul (x y : ℝ) :
    1 + Real.tanh x * Real.tanh y = Real.cosh (x + y) / (Real.cosh x * Real.cosh y) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.cosh_add]
  have h1 : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have h2 : Real.cosh y ≠ 0 := ne_of_gt (Real.cosh_pos y)
  field_simp

lemma log_one_add_tanh_mul (x y : ℝ) :
    Real.log (1 + Real.tanh x * Real.tanh y) = LC (x + y) - LC x - LC y := by
  rw [one_add_tanh_mul, Real.log_div (ne_of_gt (Real.cosh_pos _))
    (by positivity), Real.log_mul (ne_of_gt (Real.cosh_pos _)) (ne_of_gt (Real.cosh_pos _))]
  simp only [LC]; ring

/-- The atom value of the `U`-side against the two-atom `V`-side `(tanh γ, −tanh δ)`,
in `θ` coordinates. -/
noncomputable def Gval (γ δ σ : ℝ) : ℝ :=
  (Real.sinh δ * Real.cosh γ / Real.sinh (γ + δ)) * fF (Real.tanh σ * Real.tanh γ)
    + (Real.sinh γ * Real.cosh δ / Real.sinh (γ + δ)) * fF (-(Real.tanh σ * Real.tanh δ))

/-- **The odd-kernel form**: `G′(σ)·cosh²σ = k·[L(σ+γ) − L(σ−δ) − L(γ) + L(δ)]`. -/
theorem hasDerivAt_Gval {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) (σ : ℝ) :
    HasDerivAt (Gval γ δ)
      (kco γ δ * (LC (σ + γ) - LC (σ - δ) - LC γ + LC δ) / Real.cosh σ ^ 2) σ := by
  have hcγ : (0:ℝ) < Real.cosh γ := Real.cosh_pos γ
  have hcδ : (0:ℝ) < Real.cosh δ := Real.cosh_pos δ
  have hcσ : (0:ℝ) < Real.cosh σ := Real.cosh_pos σ
  have hsγ : 0 < Real.sinh γ := Real.sinh_pos_iff.mpr hγ
  have hsδ : 0 < Real.sinh δ := Real.sinh_pos_iff.mpr hδ
  have hsum : 0 < Real.sinh (γ + δ) := Real.sinh_pos_iff.mpr (by linarith)
  -- `1 + tanh σ tanh γ > 0` and `1 − tanh σ tanh δ > 0`
  have hp : 0 < 1 + Real.tanh σ * Real.tanh γ := by
    rw [one_add_tanh_mul]; positivity
  have hm : 0 < 1 + -(Real.tanh σ * Real.tanh δ) := by
    have := one_add_tanh_mul σ (-δ)
    rw [Real.tanh_neg] at this
    rw [show 1 + -(Real.tanh σ * Real.tanh δ) = 1 + Real.tanh σ * -Real.tanh δ by ring, this]
    positivity
  -- derivative of `fF ∘ (tanh · c)`
  have hfF : ∀ c : ℝ, ∀ z : ℝ, 0 < 1 + z → HasDerivAt fF (Real.log (1 + z) + 1) z := by
    intro c z hz
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 z := by simpa using (hasDerivAt_id z).const_add 1
    have h2 : HasDerivAt (fun z : ℝ => Real.log (1 + z)) (1 / (1 + z)) z := by
      have := h1.log (ne_of_gt hz)
      simpa using this
    have := h1.mul h2
    refine hd_congr this ?_
    field_simp
  have hT : HasDerivAt Real.tanh (1 / Real.cosh σ ^ 2) σ := hasDerivAt_tanh σ
  have h1 : HasDerivAt (fun s : ℝ => fF (Real.tanh s * Real.tanh γ))
      ((Real.log (1 + Real.tanh σ * Real.tanh γ) + 1) * (Real.tanh γ / Real.cosh σ ^ 2)) σ := by
    have hin : HasDerivAt (fun s : ℝ => Real.tanh s * Real.tanh γ)
        (Real.tanh γ / Real.cosh σ ^ 2) σ :=
      hd_congr (hT.mul_const (Real.tanh γ)) (by ring)
    have := (hfF (Real.tanh γ) _ hp).comp σ hin
    rwa [Function.comp_def] at this
  have h2 : HasDerivAt (fun s : ℝ => fF (-(Real.tanh s * Real.tanh δ)))
      ((Real.log (1 + -(Real.tanh σ * Real.tanh δ)) + 1)
        * (-(Real.tanh δ) / Real.cosh σ ^ 2)) σ := by
    have hin : HasDerivAt (fun s : ℝ => -(Real.tanh s * Real.tanh δ))
        (-(Real.tanh δ) / Real.cosh σ ^ 2) σ :=
      hd_congr ((hT.mul_const (Real.tanh δ)).neg) (by ring)
    have := (hfF (-(Real.tanh δ)) _ hm).comp σ hin
    rwa [Function.comp_def] at this
  have hfin := (h1.const_mul (Real.sinh δ * Real.cosh γ / Real.sinh (γ + δ))).add
    (h2.const_mul (Real.sinh γ * Real.cosh δ / Real.sinh (γ + δ)))
  refine hd_congr hfin ?_
  -- the two mixed weights are both `k`, and the constants cancel by mean-zero
  have e1 : Real.log (1 + Real.tanh σ * Real.tanh γ) = LC (σ + γ) - LC σ - LC γ :=
    log_one_add_tanh_mul σ γ
  have e2 : Real.log (1 + -(Real.tanh σ * Real.tanh δ)) = LC (σ - δ) - LC σ - LC δ := by
    have := log_one_add_tanh_mul σ (-δ)
    rw [Real.tanh_neg, LC_even] at this
    rw [show 1 + -(Real.tanh σ * Real.tanh δ) = 1 + Real.tanh σ * -Real.tanh δ by ring, this]
    ring_nf
  rw [e1, e2, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, kco]
  have hsadd : Real.sinh (γ + δ) = Real.sinh γ * Real.cosh δ + Real.cosh γ * Real.sinh δ :=
    Real.sinh_add γ δ
  field_simp
  ring

/-- The `U`-side slack in `θ` coordinates. -/
noncomputable def Dsl (l₀ l₁ l₂ γ δ σ : ℝ) : ℝ :=
  l₀ + l₁ * Real.tanh σ + l₂ * (σ * Real.tanh σ - LC σ) - Gval γ δ σ

/-- The odd-kernel rewriting of the `G`-kernel. -/
lemma Gker (n v σ : ℝ) :
    LC (σ + (n + v)) - LC (σ - (n - v)) - LC (n + v) + LC (n - v)
      = MG n (σ + v) - MG n v := by
  simp only [MG]
  rw [show σ + v + n = σ + (n + v) by ring, show σ + v - n = σ - (n - v) by ring,
    show v + n = n + v by ring, show v - n = -(n - v) by ring, LC_even]
  ring


lemma hasDerivAt_Dsl {n v : ℝ} (hγ : 0 < n + v) (hδ : 0 < n - v) (l₀ l₁ l₂ σ : ℝ) :
    HasDerivAt (Dsl l₀ l₁ l₂ (n + v) (n - v))
      (((l₁ + l₂ * σ) - kco (n + v) (n - v) * (MG n (σ + v) - MG n v))
        / Real.cosh σ ^ 2) σ := by
  have hcσ : (0:ℝ) < Real.cosh σ := Real.cosh_pos σ
  have h1 : HasDerivAt (fun s : ℝ => l₁ * Real.tanh s) (l₁ / Real.cosh σ ^ 2) σ :=
    hd_congr ((hasDerivAt_tanh σ).const_mul l₁) (by ring)
  have h2 : HasDerivAt (fun s : ℝ => l₂ * (s * Real.tanh s - LC s))
      (l₂ * σ / Real.cosh σ ^ 2) σ := by
    have hmul : HasDerivAt (fun s : ℝ => s * Real.tanh s)
        (Real.tanh σ + σ / Real.cosh σ ^ 2) σ := by
      refine hd_congr ((hasDerivAt_id σ).mul (hasDerivAt_tanh σ)) ?_
      simp only [id_eq]; ring
    refine hd_congr ((hmul.sub (hasDerivAt_LC σ)).const_mul l₂) ?_
    field_simp
    ring
  have h3 := hasDerivAt_Gval hγ hδ σ
  rw [Gker n v σ] at h3
  refine hd_congr (((h1.const_add l₀).add h2).sub h3) ?_
  field_simp

/-- **Bitangency forces the residual to vanish.** -/
theorem bitangent_residual_zero {m n u v l₀ l₁ l₂ : ℝ}
    (hm : 0 < m) (hγ : 0 < n + v) (hδ : 0 < n - v)
    (hDα : Dsl l₀ l₁ l₂ (n + v) (n - v) (m + u) = 0)
    (hDβ : Dsl l₀ l₁ l₂ (n + v) (n - v) (u - m) = 0)
    (hTα : l₁ + l₂ * (m + u) = kco (n + v) (n - v) * (MG n (u + v + m) - MG n v))
    (hTβ : l₁ + l₂ * (u - m) = kco (n + v) (n - v) * (MG n (u + v - m) - MG n v)) :
    RS m n u v = 0 := by
  set k := kco (n + v) (n - v) with hk
  have hk0 : 0 < k := kco_pos hγ hδ
  set F : ℝ → ℝ := fun σ =>
    ((l₁ + l₂ * σ) - k * (MG n (σ + v) - MG n v)) / Real.cosh σ ^ 2 with hFdef
  have hcontF : Continuous F := by
    rw [hFdef]
    refine Continuous.div ?_ (by fun_prop)
      (fun x => pow_ne_zero 2 (ne_of_gt (Real.cosh_pos x)))
    have c1 : Continuous (fun σ : ℝ => MG n (σ + v)) := (continuous_MG n).comp (by fun_prop)
    exact (continuous_const.add (continuous_const.mul continuous_id)).sub
      (continuous_const.mul (c1.sub continuous_const))
  -- (A) the two value conditions
  have hzero : (∫ σ in (u - m)..(m + u), F σ) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun σ _ => hasDerivAt_Dsl hγ hδ l₀ l₁ l₂ σ) (hcontF.intervalIntegrable _ _), hDα, hDβ]
    ring
  -- (B) shift the window
  have hsub : (∫ w in (u + v - m)..(u + v + m), F (w - v)) = ∫ σ in (u - m)..(m + u), F σ := by
    rw [intervalIntegral.integral_comp_sub_right F v]
    congr 1 <;> ring
  -- (C) the affine function is the chord
  have h2m : (2:ℝ) * m ≠ 0 := by positivity
  have hl2 : l₂ * (2 * m) = k * (MG n (u + v + m) - MG n (u + v - m)) := by
    linarith [hTα, hTβ]
  have hchord2m : ∀ w : ℝ, (l₁ + l₂ * (w - v) + k * MG n v) * (2 * m)
      = k * (MG n (u + v - m) * (2 * m)
        + (MG n (u + v + m) - MG n (u + v - m)) * (w - (u + v - m))) := by
    intro w
    linear_combination (2 * m) * hTβ + (w - u - v + m) * hl2
  have hchord : ∀ w : ℝ, l₁ + l₂ * (w - v) + k * MG n v
      = k * (MG n (u + v - m)
        + (MG n (u + v + m) - MG n (u + v - m)) * (w - (u + v - m)) / (2 * m)) := by
    intro w
    have := hchord2m w
    field_simp
    linarith [this]
  have hint : ∀ w : ℝ, F (w - v)
      = -(k * (Dfun n m (u + v) w * (1 / Real.cosh (w - v) ^ 2))) := by
    intro w
    have hcw : Real.cosh (w - v) ≠ 0 := ne_of_gt (Real.cosh_pos _)
    rw [hFdef]
    simp only [Dfun, show w - v + v = w by ring]
    rw [show l₁ + l₂ * (w - v) - k * (MG n w - MG n v)
        = -(k * (MG n w - (MG n (u + v - m)
            + (MG n (u + v + m) - MG n (u + v - m)) * (w - (u + v - m)) / (2 * m))))
        from by linear_combination hchord w]
    field_simp
  -- (D) conclude
  have hfin : (∫ w in (u + v - m)..(u + v + m),
      -(k * (Dfun n m (u + v) w * (1 / Real.cosh (w - v) ^ 2)))) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun w => F (w - v)) (fun w _ => (hint w).symm),
      hsub, hzero]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hfin
  rw [RS]
  have := neg_eq_zero.mp hfin
  exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hk0)



end BSCAveraging.LC
