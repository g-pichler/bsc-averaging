import BSCAveraging.BestResponse
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The `p = 0` certificate: the best response to an S-channel is a Z-channel

`BestResponse.lean` reduces the one-sided problem to a certificate `(★)` in a
single real variable.  This file *builds* the certificate for `p = 0` against
the S-channel `T = (+1, −d)`, which is what Conjecture 1 of Dikshtein–
Ordentlich–Shamai (Entropy **24**(9):1321, 2022) requires.

With `f(z) = (1+z)log(1+z)` the atom value is

```
φ_d(s) = (d/(1+d))·f(s) + (1/(1+d))·f(−d·s)
```

and the three contact conditions `D(a) = D′(a) = 0`, `D(−1) = 0` for the slack
`D = λ₀ + λ₁ s + λ₂ f_e(s) − φ_d(s)` have the **closed-form** solution

```
λ₂ = log((1−d·a)/(1+d)) / log((1−a)/2)                                    (lam2)
λ₁ = (d/(1+d))·(log(1+a) − log(1−d·a)) − λ₂·artanh a                      (lam1)
λ₀ = log(1+d) + λ₁ − λ₂·log 2                                             (lam0)
```

Two collapses make the whole thing elementary.

* **`D″` is linear after clearing denominators**: the `s²` terms cancel, and

  ```
  D″(s)·(1−s²)(1−d·s) = (λ₂ − d) + d(1−λ₂)·s =: N(s)                (DFun''_eq)
  ```

  so `D″` changes sign at most once, from `−` to `+` (the slope `d(1−λ₂)` is
  positive because `λ₂ < 1`, which is just `(1+a)(1−d) > 0`).

* **the one inequality needed, `N(a) ≥ 0`, is the log-sum inequality**: it says
  `λ₂ ≥ d(1−a)/(1−d·a)`, i.e.

  ```
  d(1−a)·log(2/(1−a)) ≤ (1−d·a)·log((1+d)/(1−d·a))
  ```

  which is `log_sum_two` applied to the pairs `(1−d, 1−d)` and `(d(1−a), 2d)`,
  whose sums are `1−d·a` and `1+d`.                                (key_log_sum)

Given those, `D ≥ 0` is three monotonicity steps: `D` is convex to the right of
the sign change of `N`, where `D(a) = D′(a) = 0` pins it at zero, and concave to
the left, where the chord through `D(−1) = 0` does the rest.

See `NOTES.md` §7. -/

open Real Set

namespace BSCAveraging

/-! ## Definitions -/

/-- The atom value at `p = 0` against the S-channel `T = (+1, −d)`. -/
noncomputable def phiZ (d s : ℝ) : ℝ :=
  (d / (1 + d)) * fFun s + (1 / (1 + d)) * fFun (-(d * s))

/-- Its derivative in `s`. -/
noncomputable def phiZ' (d s : ℝ) : ℝ :=
  (d / (1 + d)) * (log (1 + s) - log (1 - d * s))

/-- The rate multiplier of the certificate, in closed form. -/
noncomputable def lam2 (a d : ℝ) : ℝ := log ((1 - d * a) / (1 + d)) / log ((1 - a) / 2)

/-- The mean multiplier: forced by the tangency `D′(a) = 0`. -/
noncomputable def lam1 (a d : ℝ) : ℝ := phiZ' d a - lam2 a d * artanh a

/-- The constant: forced by the endpoint contact `D(−1) = 0`. -/
noncomputable def lam0 (a d : ℝ) : ℝ := log (1 + d) + lam1 a d - lam2 a d * log 2

/-- The slack of a certificate with arbitrary multipliers,
`G(s) = λ₀ + λ₁ s + λ₂ f_e(s) − φ_d(s)`.  Both conjectures use it, with different
multipliers and opposite target signs. -/
noncomputable def GFun (l0 l1 l2 d s : ℝ) : ℝ := l0 + l1 * s + l2 * fe s - phiZ d s

/-- Its derivative. -/
noncomputable def GFun' (l1 l2 d s : ℝ) : ℝ := l1 + l2 * artanh s - phiZ' d s

/-- Its second derivative, before clearing denominators. -/
noncomputable def GFun'' (l2 d s : ℝ) : ℝ :=
  l2 * (1 / (1 - s ^ 2)) - d / (1 + d) * (1 / (1 + s) + d / (1 - d * s))

/-- The numerator of the second derivative: **linear** in `s`. -/
noncomputable def GN (l2 d s : ℝ) : ℝ := l2 - d + d * (1 - l2) * s

/-- The Conjecture 1 slack. -/
noncomputable def DFun (a d s : ℝ) : ℝ := GFun (lam0 a d) (lam1 a d) (lam2 a d) d s

/-! ## The key inequality: log-sum -/

/-- **The one inequality the certificate needs.**  Instance of the two-term
log-sum inequality with the pairs `(1−d, 1−d)` and `(d(1−a), 2d)`, whose sums
are `1−d·a` and `1+d`. -/
theorem key_log_sum {a d : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    d * (1 - a) * (log 2 - log (1 - a))
      ≤ (1 - d * a) * (log (1 + d) - log (1 - d * a)) := by
  rcases eq_or_lt_of_le hd0 with hd | hd0'
  · simp [← hd]
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hda : (0 : ℝ) < 1 - d * a := by nlinarith
  have hsum : (1 - d) + d * (1 - a) = 1 - d * a := by ring
  have hsum' : (1 - d) + 2 * d = 1 + d := by ring
  have hls := log_sum_two (a₁ := 1 - d) (a₂ := d * (1 - a)) (b₁ := 1 - d) (b₂ := 2 * d)
    (by linarith) (by positivity) (by linarith) (by positivity)
    (fun h => h) (fun _ => by positivity)
  rw [hsum, hsum'] at hls
  have hsplit : log (d * (1 - a)) = log d + log (1 - a) :=
    Real.log_mul (ne_of_gt hd0') (ne_of_gt h1a)
  have hsplit' : log (2 * d) = log 2 + log d := Real.log_mul two_ne_zero (ne_of_gt hd0')
  rw [hsplit, hsplit'] at hls
  nlinarith [hls]

/-! ## Elementary facts about `λ₂` -/

section Lam2

variable {a d : ℝ}

lemma log_quot_neg (ha0 : 0 < a) (ha1 : a < 1) : log ((1 - a) / 2) < 0 := by
  have h1 : (0 : ℝ) < 1 - a := by linarith
  refine Real.log_neg (by positivity) ?_
  linarith

lemma log_quot_neg' (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    log ((1 - d * a) / (1 + d)) < 0 := by
  have hda : (0 : ℝ) < 1 - d * a := by nlinarith
  refine Real.log_neg (by positivity) ?_
  rw [div_lt_one (by linarith)]
  nlinarith

/-- `λ₂ > 0`: a ratio of two negative logarithms. -/
theorem lam2_pos (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) : 0 < lam2 a d :=
  div_pos_of_neg_of_neg (log_quot_neg' ha0 ha1 hd0 hd1) (log_quot_neg ha0 ha1)

/-- `λ₂ < 1`, which after clearing logs is just `(1+a)(1−d) > 0`. -/
theorem lam2_lt_one (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) : lam2 a d < 1 := by
  have hden := log_quot_neg ha0 ha1
  rw [lam2, div_lt_one_of_neg hden]
  have hda : (0 : ℝ) < 1 - d * a := by nlinarith
  have h1a : (0 : ℝ) < 1 - a := by linarith
  refine Real.log_lt_log (by positivity) ?_
  rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
  nlinarith

end Lam2

/-! ## The contact conditions `D(−1) = 0`, `D(a) = 0`, and `N(a) ≥ 0` -/

section Contacts

variable {a d : ℝ}

@[simp] lemma fFun_neg_one : fFun (-1) = 0 := by simp [fFun]

/-- `φ_d(−1) = log(1+d)`: the `(−1,+1)` cell is impossible, so only the second
term survives. -/
lemma phiZ_neg_one (hd0 : 0 < d) : phiZ d (-1) = log (1 + d) := by
  have h : (1 : ℝ) + d ≠ 0 := by positivity
  simp only [phiZ, fFun, mul_neg, mul_one, neg_neg]
  field_simp
  norm_num

/-- `φ_d(a) − (1+a)·φ_d′(a) = log(1 − d·a)`: the `log(1+a)` terms cancel. -/
lemma phiZ_sub_tangent (hd0 : 0 < d) : phiZ d a - (1 + a) * phiZ' d a = log (1 - d * a) := by
  have h : (1 : ℝ) + d ≠ 0 := by positivity
  simp only [phiZ, phiZ', fFun]
  field_simp
  ring

/-- `f_e(a) − log 2 − (1+a)·artanh a = log(1−a) − log 2`: the `log(1+a)` terms
cancel here too. -/
lemma fe_sub_tangent (ha0 : -1 < a) (ha1 : a < 1) :
    fe a - log 2 - (1 + a) * artanh a = log (1 - a) - log 2 := by
  rw [fe, artanh_eq_log_sub ha0 ha1]
  ring

/-- The endpoint contact, true by the definition of `λ₀`. -/
theorem DFun_neg_one (hd0 : 0 < d) : DFun a d (-1) = 0 := by
  simp only [DFun, GFun, lam0, fe_neg_one, phiZ_neg_one hd0]
  ring

/-- The tangency contact.  This is where the closed form of `λ₂` is used. -/
theorem DFun_at_a (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    DFun a d a = 0 := by
  have hda : (0 : ℝ) < 1 - d * a := by nlinarith
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hden : log ((1 - a) / 2) ≠ 0 := ne_of_lt (log_quot_neg ha0 ha1)
  have hlam : lam2 a d * log ((1 - a) / 2) = log ((1 - d * a) / (1 + d)) :=
    div_mul_cancel₀ _ hden
  have e1 : log ((1 - a) / 2) = log (1 - a) - log 2 :=
    Real.log_div (ne_of_gt h1a) two_ne_zero
  have e2 : log ((1 - d * a) / (1 + d)) = log (1 - d * a) - log (1 + d) :=
    Real.log_div (ne_of_gt hda) (by positivity)
  have hP := fe_sub_tangent (a := a) (by linarith) ha1
  have hφ := phiZ_sub_tangent (a := a) hd0
  simp only [DFun, GFun, lam0, lam1]
  rw [e1, e2] at hlam
  linear_combination (-1 : ℝ) * hφ + lam2 a d * hP + hlam

/-- **`N(a) ≥ 0`**, i.e. `λ₂ ≥ d(1−a)/(1−d·a)` — the log-sum inequality in the
form the convexity argument needs. -/
theorem N_at_a_nonneg (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    0 ≤ lam2 a d - d + d * (1 - lam2 a d) * a := by
  have hda : (0 : ℝ) < 1 - d * a := by nlinarith
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hM : 0 < log 2 - log (1 - a) := by
    have := Real.log_lt_log h1a (show (1 : ℝ) - a < 2 by linarith)
    linarith
  have e1 : log ((1 - a) / 2) = -(log 2 - log (1 - a)) := by
    rw [Real.log_div (ne_of_gt h1a) two_ne_zero]; ring
  have e2 : log ((1 - d * a) / (1 + d)) = -(log (1 + d) - log (1 - d * a)) := by
    rw [Real.log_div (ne_of_gt hda) (by positivity)]; ring
  have hlam : lam2 a d = (log (1 + d) - log (1 - d * a)) / (log 2 - log (1 - a)) := by
    rw [lam2, e1, e2, neg_div_neg_eq]
  have hkey := key_log_sum (le_of_lt ha0) ha1 (le_of_lt hd0) (le_of_lt hd1)
  have hge : d * (1 - a) / (1 - d * a) ≤ lam2 a d := by
    rw [hlam, div_le_div_iff₀ hda hM]
    nlinarith [hkey]
  have : d * (1 - a) ≤ lam2 a d * (1 - d * a) := by
    rw [div_le_iff₀ hda] at hge; linarith
  nlinarith [this]

end Contacts


/-! ## Continuity and derivatives (generic in the multipliers) -/

section Calculus

variable {l0 l1 l2 d : ℝ}

lemma continuous_fFun : Continuous fFun := by
  have h : Continuous fun z : ℝ => (1 + z) * log (1 + z) :=
    Real.continuous_mul_log.comp (continuous_const.add continuous_id)
  exact h

lemma continuous_fe : Continuous fe := by
  have h1 : Continuous fun y : ℝ => (1 + y) * log (1 + y) :=
    Real.continuous_mul_log.comp (continuous_const.add continuous_id)
  have h2 : Continuous fun y : ℝ => (1 - y) * log (1 - y) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  exact (h1.add h2).div_const 2

lemma continuous_phiZ : Continuous (phiZ d) := by
  have h : Continuous fun u : ℝ => fFun (-(d * u)) :=
    continuous_fFun.comp (continuous_const.mul continuous_id).neg
  exact (continuous_const.mul continuous_fFun).add (continuous_const.mul h)

lemma continuous_GFun : Continuous (GFun l0 l1 l2 d) :=
  ((continuous_const.add (continuous_const.mul continuous_id)).add
    (continuous_const.mul continuous_fe)).sub continuous_phiZ

/-- `φ_d` written out, with `1 + (−d·u)` normalised to `1 − d·u`. -/
lemma phiZ_eq (d : ℝ) : phiZ d = fun u : ℝ =>
    d / (1 + d) * ((1 + u) * log (1 + u)) + 1 / (1 + d) * ((1 - d * u) * log (1 - d * u)) := by
  funext u
  simp only [phiZ, fFun]
  ring_nf

/-- The derivative of the atom value. -/
lemma hasDerivAt_phiZ {s : ℝ} (hd0 : 0 < d) (hd1 : d < 1) (hs0 : -1 < s) (hs1 : s < 1) :
    HasDerivAt (phiZ d) (phiZ' d s) s := by
  have hne : (1 : ℝ) + d ≠ 0 := by positivity
  have hs : (1 : ℝ) + s ≠ 0 := by linarith
  have hds : (0 : ℝ) < 1 - d * s := by nlinarith
  have h1 : HasDerivAt (fun u : ℝ => 1 + u) 1 s := by simpa using (hasDerivAt_id s).const_add 1
  have h2 : HasDerivAt (fun u : ℝ => 1 - d * u) (-d) s := by
    simpa using ((hasDerivAt_id s).const_mul d).const_sub 1
  have hA := h1.mul (h1.log hs)
  have hB := h2.mul (h2.log (ne_of_gt hds))
  have h := (hA.const_mul (d / (1 + d))).add (hB.const_mul (1 / (1 + d)))
  rw [phiZ_eq]
  have heq : d / (1 + d) * (1 * log (1 + s) + (1 + s) * (1 / (1 + s)))
      + 1 / (1 + d) * (-d * log (1 - d * s) + (1 - d * s) * (-d / (1 - d * s)))
      = phiZ' d s := by
    simp only [phiZ']
    field_simp
    ring
  rw [heq] at h
  exact h

lemma hasDerivAt_GFun {s : ℝ} (hd0 : 0 < d) (hd1 : d < 1) (hs0 : -1 < s) (hs1 : s < 1) :
    HasDerivAt (GFun l0 l1 l2 d) (GFun' l1 l2 d s) s := by
  have hfe : HasDerivAt fe (artanh s) s := by
    have h := hasDerivAt_fe_affine (p := 0) (K := 1) (x := s) (by simpa using hs0)
      (by simpa using hs1)
    simpa using h
  have h := (((hasDerivAt_const s l0).add ((hasDerivAt_id s).const_mul l1)).add
    (hfe.const_mul l2)).sub (hasDerivAt_phiZ hd0 hd1 hs0 hs1)
  have heq : 0 + l1 * 1 + l2 * artanh s - phiZ' d s = GFun' l1 l2 d s := by
    simp only [GFun']; ring
  rw [heq] at h
  exact h

lemma hasDerivAt_GFun' {s : ℝ} (hd0 : 0 < d) (hd1 : d < 1) (hs0 : -1 < s) (hs1 : s < 1) :
    HasDerivAt (GFun' l1 l2 d) (GFun'' l2 d s) s := by
  have hne : (1 : ℝ) + d ≠ 0 := by positivity
  have hs : (1 : ℝ) + s ≠ 0 := by linarith
  have hds : (0 : ℝ) < 1 - d * s := by nlinarith
  have hart : HasDerivAt artanh (1 / (1 - s ^ 2)) s := hasDerivAt_artanh hs0 hs1
  have h1 : HasDerivAt (fun u : ℝ => 1 + u) 1 s := by simpa using (hasDerivAt_id s).const_add 1
  have h2 : HasDerivAt (fun u : ℝ => 1 - d * u) (-d) s := by
    simpa using ((hasDerivAt_id s).const_mul d).const_sub 1
  have hphi : HasDerivAt (phiZ' d) (d / (1 + d) * (1 / (1 + s) - -d / (1 - d * s))) s :=
    (((h1.log hs).sub (h2.log (ne_of_gt hds)))).const_mul (d / (1 + d))
  have h := ((hasDerivAt_const s l1).add (hart.const_mul l2)).sub hphi
  have heq : 0 + l2 * (1 / (1 - s ^ 2))
      - d / (1 + d) * (1 / (1 + s) - -d / (1 - d * s)) = GFun'' l2 d s := by
    simp only [GFun'']
    field_simp
    ring
  rw [heq] at h
  exact h

/-- **The collapse**: clearing denominators in `G″` leaves a *linear* function —
the `s²` terms cancel. -/
theorem GFun''_eq {s : ℝ} (hd0 : 0 < d) (hs0 : -1 < s) (hs1 : s < 1) (hds : 0 < 1 - d * s) :
    GFun'' l2 d s = GN l2 d s / ((1 - s ^ 2) * (1 - d * s)) := by
  have h1 : (1 : ℝ) + s ≠ 0 := by linarith
  have h2 : (1 : ℝ) - s ≠ 0 := by linarith
  have h3 : (1 : ℝ) - s ^ 2 ≠ 0 := by
    have hf : (1 : ℝ) - s ^ 2 = (1 + s) * (1 - s) := by ring
    rw [hf]; exact mul_ne_zero h1 h2
  have h4 : (1 : ℝ) + d ≠ 0 := by positivity
  have h5 : (1 : ℝ) - d * s ≠ 0 := ne_of_gt hds
  have h5' : (1 : ℝ) - s * d ≠ 0 := by rw [mul_comm]; exact h5
  have hfac : (1 : ℝ) - s ^ 2 = (1 + s) * (1 - s) := by ring
  rw [eq_div_iff (mul_ne_zero h3 h5)]
  simp only [GFun'', GN, hfac]
  field_simp
  ring

end Calculus

/-! ## The two shapes -/

section Shapes

variable {l0 l1 l2 d : ℝ}

lemma GN_mono (hd0 : 0 < d) (hl2 : l2 < 1) {x y : ℝ} (hxy : x ≤ y) :
    GN l2 d x ≤ GN l2 d y := by
  have hslope : 0 < d * (1 - l2) := by nlinarith
  simp only [GN]
  nlinarith [mul_le_mul_of_nonneg_left hxy (le_of_lt hslope)]

lemma GN_strictMono (hd0 : 0 < d) (hl2 : l2 < 1) {x y : ℝ} (hxy : x < y) :
    GN l2 d x < GN l2 d y := by
  have hslope : 0 < d * (1 - l2) := by nlinarith
  simp only [GN]
  nlinarith [mul_lt_mul_of_pos_left hxy hslope]

/-- Where `N ≥ 0`, `G′` is increasing. -/
lemma GFun'_le_of_GN_nonneg (hd0 : 0 < d) (hd1 : d < 1) (hl2 : l2 < 1) {x y : ℝ}
    (hx : -1 < x) (hxy : x ≤ y) (hy : y < 1) (hN : 0 ≤ GN l2 d x) :
    GFun' l1 l2 d x ≤ GFun' l1 l2 d y := by
  have hmem : ∀ z ∈ Icc x y, -1 < z ∧ z < 1 := fun z hz =>
    ⟨lt_of_lt_of_le hx hz.1, lt_of_le_of_lt hz.2 hy⟩
  have hcont : ContinuousOn (GFun' l1 l2 d) (Icc x y) := fun z hz =>
    ((hasDerivAt_GFun' hd0 hd1 (hmem z hz).1 (hmem z hz).2).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ (GFun' l1 l2 d) (interior (Icc x y)) := by
    rw [interior_Icc]
    exact fun z hz => DifferentiableAt.differentiableWithinAt (hasDerivAt_GFun' hd0 hd1
      (lt_of_lt_of_le hx (le_of_lt hz.1)) (lt_trans hz.2 hy)).differentiableAt
  have hderiv : ∀ z ∈ interior (Icc x y), 0 ≤ deriv (GFun' l1 l2 d) z := by
    rw [interior_Icc]
    intro z hz
    have hz0 : -1 < z := lt_of_lt_of_le hx (le_of_lt hz.1)
    have hz1 : z < 1 := lt_trans hz.2 hy
    have hds : (0 : ℝ) < 1 - d * z := by
      rcases le_or_gt 0 z with hz' | hz' <;> nlinarith
    rw [(hasDerivAt_GFun' hd0 hd1 hz0 hz1).deriv, GFun''_eq hd0 hz0 hz1 hds]
    exact div_nonneg (le_trans hN (GN_mono hd0 hl2 (le_of_lt hz.1)))
      (le_of_lt (mul_pos (by nlinarith) hds))
  exact monotoneOn_of_deriv_nonneg (convex_Icc x y) hcont hdiff hderiv
    (left_mem_Icc.2 hxy) (right_mem_Icc.2 hxy) hxy

/-- Where `N ≤ 0`, `G′` is decreasing. -/
lemma GFun'_ge_of_GN_nonpos (hd0 : 0 < d) (hd1 : d < 1) (hl2 : l2 < 1) {x y : ℝ}
    (hx : -1 < x) (hxy : x ≤ y) (hy : y < 1) (hN : GN l2 d y ≤ 0) :
    GFun' l1 l2 d y ≤ GFun' l1 l2 d x := by
  have hmem : ∀ z ∈ Icc x y, -1 < z ∧ z < 1 := fun z hz =>
    ⟨lt_of_lt_of_le hx hz.1, lt_of_le_of_lt hz.2 hy⟩
  have hcont : ContinuousOn (GFun' l1 l2 d) (Icc x y) := fun z hz =>
    ((hasDerivAt_GFun' hd0 hd1 (hmem z hz).1 (hmem z hz).2).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ (GFun' l1 l2 d) (interior (Icc x y)) := by
    rw [interior_Icc]
    exact fun z hz => DifferentiableAt.differentiableWithinAt (hasDerivAt_GFun' hd0 hd1
      (lt_of_lt_of_le hx (le_of_lt hz.1)) (lt_trans hz.2 hy)).differentiableAt
  have hderiv : ∀ z ∈ interior (Icc x y), deriv (GFun' l1 l2 d) z ≤ 0 := by
    rw [interior_Icc]
    intro z hz
    have hz0 : -1 < z := lt_of_lt_of_le hx (le_of_lt hz.1)
    have hz1 : z < 1 := lt_trans hz.2 hy
    have hds : (0 : ℝ) < 1 - d * z := by
      rcases le_or_gt 0 z with hz' | hz' <;> nlinarith
    rw [(hasDerivAt_GFun' hd0 hd1 hz0 hz1).deriv, GFun''_eq hd0 hz0 hz1 hds]
    exact div_nonpos_of_nonpos_of_nonneg (le_trans (GN_mono hd0 hl2 (le_of_lt hz.2)) hN)
      (le_of_lt (mul_pos (by nlinarith) hds))
  exact antitoneOn_of_deriv_nonpos (convex_Icc x y) hcont hdiff hderiv
    (left_mem_Icc.2 hxy) (right_mem_Icc.2 hxy) hxy

/-- **Shape A** (Conjecture 1): a double zero at an interior `x₀` with `N(x₀) ≥ 0`,
a simple zero at `−1`, and `G ≥ 0` throughout. -/
theorem GFun_nonneg_of_contacts (hd0 : 0 < d) (hd1 : d < 1) (hl2 : l2 < 1)
    {x₀ : ℝ} (hx0 : -1 < x₀) (hx1 : x₀ < 1)
    (hT : GFun' l1 l2 d x₀ = 0) (hC : GFun l0 l1 l2 d x₀ = 0)
    (hE : GFun l0 l1 l2 d (-1) = 0) (hN : 0 ≤ GN l2 d x₀)
    {s : ℝ} (hs0 : -1 ≤ s) (hs1 : s ≤ 1) : 0 ≤ GFun l0 l1 l2 d s := by
  -- right of `x₀`
  have hright : ∀ t : ℝ, x₀ ≤ t → t ≤ 1 → 0 ≤ GFun l0 l1 l2 d t := by
    intro t ht ht1
    have hdiff : DifferentiableOn ℝ (GFun l0 l1 l2 d) (interior (Icc x₀ 1)) := by
      rw [interior_Icc]
      exact fun z hz => DifferentiableAt.differentiableWithinAt
        (hasDerivAt_GFun hd0 hd1 (by linarith [hz.1]) hz.2).differentiableAt
    have hderiv : ∀ z ∈ interior (Icc x₀ 1), 0 ≤ deriv (GFun l0 l1 l2 d) z := by
      rw [interior_Icc]
      intro z hz
      rw [(hasDerivAt_GFun hd0 hd1 (by linarith [hz.1]) hz.2).deriv]
      have h := GFun'_le_of_GN_nonneg hd0 hd1 hl2 (l1 := l1) (x := x₀) (y := z) hx0
        (le_of_lt hz.1) hz.2 hN
      rw [hT] at h; exact h
    have hmono := monotoneOn_of_deriv_nonneg (convex_Icc x₀ 1) continuous_GFun.continuousOn
      hdiff hderiv
    have h := hmono (left_mem_Icc.2 (le_of_lt hx1)) ⟨ht, ht1⟩ ht
    rwa [hC] at h
  -- between the sign change and `x₀`
  have hmid : ∀ t : ℝ, -1 ≤ t → t ≤ x₀ → 0 ≤ GN l2 d t → 0 ≤ GFun l0 l1 l2 d t := by
    intro t ht0 ht hNt
    have hdiff : DifferentiableOn ℝ (GFun l0 l1 l2 d) (interior (Icc t x₀)) := by
      rw [interior_Icc]
      exact fun z hz => DifferentiableAt.differentiableWithinAt
        (hasDerivAt_GFun hd0 hd1 (lt_of_le_of_lt ht0 hz.1)
          (lt_of_lt_of_le hz.2 (le_of_lt hx1))).differentiableAt
    have hderiv : ∀ z ∈ interior (Icc t x₀), deriv (GFun l0 l1 l2 d) z ≤ 0 := by
      rw [interior_Icc]
      intro z hz
      have hz0 : -1 < z := lt_of_le_of_lt ht0 hz.1
      rw [(hasDerivAt_GFun hd0 hd1 hz0 (lt_of_lt_of_le hz.2 (le_of_lt hx1))).deriv]
      have hNz : 0 ≤ GN l2 d z := le_trans hNt (GN_mono hd0 hl2 (le_of_lt hz.1))
      have h := GFun'_le_of_GN_nonneg hd0 hd1 hl2 (l1 := l1) (x := z) (y := x₀) hz0
        (le_of_lt hz.2) hx1 hNz
      rw [hT] at h; exact h
    have hanti := antitoneOn_of_deriv_nonpos (convex_Icc t x₀) continuous_GFun.continuousOn
      hdiff hderiv
    have h := hanti (left_mem_Icc.2 ht) (right_mem_Icc.2 ht) ht
    rwa [hC] at h
  rcases le_or_gt x₀ s with h | h
  · exact hright s h hs1
  rcases le_or_gt 0 (GN l2 d s) with hN' | hN'
  · exact hmid s hs0 (le_of_lt h) hN'
  -- left of the sign change: two mean value theorems against the monotonicity of `G′`
  rcases eq_or_lt_of_le hs0 with hEq | hs0'
  · rw [← hEq, hE]
  have hslope : 0 < d * (1 - l2) := by nlinarith
  have hne : d * (1 - l2) ≠ 0 := ne_of_gt hslope
  have hl2' : (1 : ℝ) - l2 ≠ 0 := ne_of_gt (by linarith)
  set r : ℝ := (d - l2) / (d * (1 - l2)) with hr
  have hNr : GN l2 d r = 0 := by
    have hcancel : d * (1 - l2) * r = d - l2 := by rw [hr]; field_simp
    simp only [GN]; linarith [hcancel]
  have hsr : s < r := by
    by_contra hcon
    have := GN_mono hd0 hl2 (not_lt.mp hcon)
    rw [hNr] at this; linarith
  have hra : r ≤ x₀ := by
    by_contra hcon
    have := GN_strictMono hd0 hl2 (not_le.mp hcon)
    rw [hNr] at this; linarith
  have hr1 : r < 1 := lt_of_le_of_lt hra hx1
  have hDr : 0 ≤ GFun l0 l1 l2 d r := hmid r (by linarith) hra (le_of_eq hNr.symm)
  by_contra hneg0
  have hneg : GFun l0 l1 l2 d s < 0 := not_le.mp hneg0
  obtain ⟨c₁, hc₁mem, hc₁⟩ := exists_hasDerivAt_eq_slope (GFun l0 l1 l2 d) (GFun' l1 l2 d) hs0'
    continuous_GFun.continuousOn
    (fun z hz => hasDerivAt_GFun hd0 hd1 hz.1 (by linarith [hz.2, hx1]))
  obtain ⟨c₂, hc₂mem, hc₂⟩ := exists_hasDerivAt_eq_slope (GFun l0 l1 l2 d) (GFun' l1 l2 d) hsr
    continuous_GFun.continuousOn
    (fun z hz => hasDerivAt_GFun hd0 hd1 (by linarith [hz.1]) (by linarith [hz.2]))
  rw [hE] at hc₁
  have hc₁neg : GFun' l1 l2 d c₁ < 0 := by
    rw [hc₁]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hc₂pos : 0 < GFun' l1 l2 d c₂ := by
    rw [hc₂]; exact div_pos (by linarith) (by linarith)
  have hNc₂ : GN l2 d c₂ ≤ 0 := by
    have := GN_strictMono hd0 hl2 hc₂mem.2; rw [hNr] at this; linarith
  have := GFun'_ge_of_GN_nonpos hd0 hd1 hl2 (l1 := l1) (x := c₁) (y := c₂)
    hc₁mem.1 (le_of_lt (lt_trans hc₁mem.2 hc₂mem.1)) (lt_trans hc₂mem.2 hr1) hNc₂
  linarith

/-- **Shape B** (Conjecture 2): a double zero at an interior `x₀` with `N(x₀) ≤ 0`,
a simple zero at `+1`, and `G ≤ 0` throughout.  The mirror of Shape A: `G` is
concave through `x₀` and convex on the far side. -/
theorem GFun_nonpos_of_contacts (hd0 : 0 < d) (hd1 : d < 1) (hl2 : l2 < 1)
    {x₀ : ℝ} (hx0 : -1 < x₀) (hx1 : x₀ < 1)
    (hT : GFun' l1 l2 d x₀ = 0) (hC : GFun l0 l1 l2 d x₀ = 0)
    (hE : GFun l0 l1 l2 d 1 = 0) (hN : GN l2 d x₀ ≤ 0)
    {s : ℝ} (hs0 : -1 ≤ s) (hs1 : s ≤ 1) : GFun l0 l1 l2 d s ≤ 0 := by
  -- on `[t, x₀]` with `N ≤ 0`: `G′ ≥ G′(x₀) = 0`, so `G` increases into the double zero
  have hleft : ∀ t : ℝ, -1 ≤ t → t ≤ x₀ → GFun l0 l1 l2 d t ≤ 0 := by
    intro t ht0 ht
    have hdiff : DifferentiableOn ℝ (GFun l0 l1 l2 d) (interior (Icc t x₀)) := by
      rw [interior_Icc]
      exact fun z hz => DifferentiableAt.differentiableWithinAt
        (hasDerivAt_GFun hd0 hd1 (lt_of_le_of_lt ht0 hz.1)
          (lt_of_lt_of_le hz.2 (le_of_lt hx1))).differentiableAt
    have hderiv : ∀ z ∈ interior (Icc t x₀), 0 ≤ deriv (GFun l0 l1 l2 d) z := by
      rw [interior_Icc]
      intro z hz
      have hz0 : -1 < z := lt_of_le_of_lt ht0 hz.1
      rw [(hasDerivAt_GFun hd0 hd1 hz0 (lt_of_lt_of_le hz.2 (le_of_lt hx1))).deriv]
      have h := GFun'_ge_of_GN_nonpos hd0 hd1 hl2 (l1 := l1) (x := z) (y := x₀) hz0
        (le_of_lt hz.2) hx1 hN
      rw [hT] at h; exact h
    have hmono := monotoneOn_of_deriv_nonneg (convex_Icc t x₀) continuous_GFun.continuousOn
      hdiff hderiv
    have h := hmono (left_mem_Icc.2 ht) (right_mem_Icc.2 ht) ht
    rwa [hC] at h
  -- on `[x₀, t]` still inside `N ≤ 0`: `G′ ≤ 0`, so `G` decreases away from it
  have hmid : ∀ t : ℝ, x₀ ≤ t → t ≤ 1 → GN l2 d t ≤ 0 → GFun l0 l1 l2 d t ≤ 0 := by
    intro t ht ht1 hNt
    have hdiff : DifferentiableOn ℝ (GFun l0 l1 l2 d) (interior (Icc x₀ t)) := by
      rw [interior_Icc]
      exact fun z hz => DifferentiableAt.differentiableWithinAt
        (hasDerivAt_GFun hd0 hd1 (by linarith [hz.1]) (lt_of_lt_of_le hz.2 ht1)).differentiableAt
    have hderiv : ∀ z ∈ interior (Icc x₀ t), deriv (GFun l0 l1 l2 d) z ≤ 0 := by
      rw [interior_Icc]
      intro z hz
      have hz1 : z < 1 := lt_of_lt_of_le hz.2 ht1
      rw [(hasDerivAt_GFun hd0 hd1 (by linarith [hz.1]) hz1).deriv]
      have hNz : GN l2 d z ≤ 0 := le_trans (GN_mono hd0 hl2 (le_of_lt hz.2)) hNt
      have h := GFun'_ge_of_GN_nonpos hd0 hd1 hl2 (l1 := l1) (x := x₀) (y := z) hx0
        (le_of_lt hz.1) hz1 hNz
      rw [hT] at h; exact h
    have hanti := antitoneOn_of_deriv_nonpos (convex_Icc x₀ t) continuous_GFun.continuousOn
      hdiff hderiv
    have h := hanti (left_mem_Icc.2 ht) (right_mem_Icc.2 ht) ht
    rwa [hC] at h
  rcases le_or_gt s x₀ with h | h
  · exact hleft s hs0 h
  rcases le_or_gt (GN l2 d s) 0 with hN' | hN'
  · exact hmid s (le_of_lt h) hs1 hN'
  -- beyond the sign change: convex, pinned by `G(1) = 0`
  rcases eq_or_lt_of_le hs1 with hEq | hs1'
  · rw [hEq]; exact le_of_eq hE
  have hslope : 0 < d * (1 - l2) := by nlinarith
  have hne : d * (1 - l2) ≠ 0 := ne_of_gt hslope
  have hl2' : (1 : ℝ) - l2 ≠ 0 := ne_of_gt (by linarith)
  set r : ℝ := (d - l2) / (d * (1 - l2)) with hr
  have hNr : GN l2 d r = 0 := by
    have hcancel : d * (1 - l2) * r = d - l2 := by rw [hr]; field_simp
    simp only [GN]; linarith [hcancel]
  have hrs : r < s := by
    by_contra hcon
    have := GN_mono hd0 hl2 (not_lt.mp hcon)
    rw [hNr] at this; linarith
  have hx0r : x₀ ≤ r := by
    by_contra hcon
    have := GN_strictMono hd0 hl2 (not_le.mp hcon)
    rw [hNr] at this; linarith
  have hrm1 : -1 < r := lt_of_lt_of_le hx0 hx0r
  have hDr : GFun l0 l1 l2 d r ≤ 0 := hmid r hx0r (by linarith) (le_of_eq hNr)
  by_contra hpos0
  have hpos : 0 < GFun l0 l1 l2 d s := not_le.mp hpos0
  obtain ⟨c₁, hc₁mem, hc₁⟩ := exists_hasDerivAt_eq_slope (GFun l0 l1 l2 d) (GFun' l1 l2 d) hrs
    continuous_GFun.continuousOn
    (fun z hz => hasDerivAt_GFun hd0 hd1 (by linarith [hz.1]) (by linarith [hz.2]))
  obtain ⟨c₂, hc₂mem, hc₂⟩ := exists_hasDerivAt_eq_slope (GFun l0 l1 l2 d) (GFun' l1 l2 d) hs1'
    continuous_GFun.continuousOn
    (fun z hz => hasDerivAt_GFun hd0 hd1 (by linarith [hz.1]) hz.2)
  rw [hE] at hc₂
  have hc₁pos : 0 < GFun' l1 l2 d c₁ := by
    rw [hc₁]; exact div_pos (by linarith) (by linarith)
  have hc₂neg : GFun' l1 l2 d c₂ < 0 := by
    rw [hc₂]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hNc₁ : 0 ≤ GN l2 d c₁ := by
    have := GN_strictMono hd0 hl2 hc₁mem.1; rw [hNr] at this; linarith
  have := GFun'_le_of_GN_nonneg hd0 hd1 hl2 (l1 := l1) (x := c₁) (y := c₂)
    (lt_trans hrm1 hc₁mem.1) (le_of_lt (lt_trans hc₁mem.2 hc₂mem.1)) hc₂mem.2 hNc₁
  linarith

end Shapes

/-! ## Conjecture 1: the Z-channel is a global best response to the S-channel -/

section ConjOne

variable {a d : ℝ}

/-- `D′(a) = 0`: true by the definition of `λ₁`. -/
@[simp] theorem DFun'_at_a : GFun' (lam1 a d) (lam2 a d) d a = 0 := by
  simp only [GFun', lam1]; ring

/-- **The certificate**: `D ≥ 0` on `[−1,1]`, with contact exactly at the two
atoms `a` and `−1` of the Z-channel. -/
theorem DFun_nonneg (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    {s : ℝ} (hs0 : -1 ≤ s) (hs1 : s ≤ 1) : 0 ≤ DFun a d s :=
  GFun_nonneg_of_contacts hd0 hd1 (lam2_lt_one ha0 ha1 hd0 hd1) (by linarith) ha1
    DFun'_at_a (DFun_at_a ha0 ha1 hd0 hd1) (DFun_neg_one hd0)
    (by simpa [GN] using N_at_a_nonneg ha0 ha1 hd0 hd1) hs0 hs1

end ConjOne

/-! ## Conjecture 2: the mirror certificate

Conjecture 2 asks for the *minimum* of `I(U;V)`, attained (conjecturally) by two
Z-channels.  Against the same `T = (+1,−d)` the conjectured best response is
`S = (+1,−a)`, so the contacts move to `s = −a` (tangency) and `s = +1`
(endpoint), and the certificate flips sign: `G ≤ 0`, i.e. `φ_d` lies *above* the
affine function.  Shape B does the work. -/

section ConjTwo

variable {a d : ℝ}

/-- **The mirror key inequality**.  Unlike Conjecture 1's, this is not a log-sum
instance — it follows from two applications of `log x ≤ x − 1`, sandwiching both
sides against `d(1+a)`. -/
theorem key_mirror (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    d * (1 - a) * (log 2 - log (1 - a)) ≤ (1 + d * a) * (log (1 + d * a) - log (1 - d)) := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have h1d : (0 : ℝ) < 1 - d := by linarith
  have hda : (0 : ℝ) < 1 + d * a := by positivity
  have hA : log 2 - log (1 - a) ≤ (1 + a) / (1 - a) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 / (1 - a) by positivity)
    rw [Real.log_div two_ne_zero (ne_of_gt h1a)] at h
    have hval : (2 : ℝ) / (1 - a) - 1 = (1 + a) / (1 - a) := by field_simp; ring
    rw [hval] at h
    exact h
  have hB : d ≤ -log (1 - d) := by
    have h := Real.log_le_sub_one_of_pos h1d
    linarith
  have hC : d * a / (1 + d * a) ≤ log (1 + d * a) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / (1 + d * a) by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hda), Real.log_one] at h
    have hval : (1 : ℝ) / (1 + d * a) - 1 = -(d * a / (1 + d * a)) := by
      field_simp
      ring
    rw [hval] at h
    linarith
  have hleft : d * (1 - a) * (log 2 - log (1 - a)) ≤ d * (1 + a) := by
    have h := mul_le_mul_of_nonneg_left hA (le_of_lt (mul_pos hd0 h1a))
    have hval : d * (1 - a) * ((1 + a) / (1 - a)) = d * (1 + a) := by field_simp
    rw [hval] at h
    exact h
  have hright : d * (1 + a) ≤ (1 + d * a) * (log (1 + d * a) - log (1 - d)) := by
    have hsum : d * a / (1 + d * a) + d ≤ log (1 + d * a) - log (1 - d) := by linarith
    have h := mul_le_mul_of_nonneg_left hsum (le_of_lt hda)
    have hval : (1 + d * a) * (d * a / (1 + d * a) + d) = d * a + d * (1 + d * a) := by
      field_simp
    rw [hval] at h
    nlinarith [h, mul_pos (mul_pos hd0 hd0) ha0]
  linarith

/-- The mirror multiplier, again in closed form. -/
noncomputable def mlam2 (a d : ℝ) : ℝ :=
  (2 * d * (log 2 - log (1 - a)) - (1 - d) * (log (1 + d * a) - log (1 - d)))
    / ((1 + d) * (log 2 - log (1 - a)))

noncomputable def mlam1 (a d : ℝ) : ℝ := phiZ' d (-a) - mlam2 a d * artanh (-a)

noncomputable def mlam0 (a d : ℝ) : ℝ := phiZ d 1 - mlam1 a d - mlam2 a d * log 2

/-- The Conjecture 2 slack. -/
noncomputable def MDFun (a d s : ℝ) : ℝ := GFun (mlam0 a d) (mlam1 a d) (mlam2 a d) d s

lemma logM_pos (ha0 : 0 < a) (ha1 : a < 1) : 0 < log 2 - log (1 - a) := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have := Real.log_lt_log h1a (show (1:ℝ) - a < 2 by linarith)
  linarith

lemma logL_pos (ha0 : 0 < a) (hd0 : 0 < d) (hd1 : d < 1) :
    0 < log (1 + d * a) - log (1 - d) := by
  have h1d : (0 : ℝ) < 1 - d := by linarith
  have := Real.log_lt_log h1d (show (1:ℝ) - d < 1 + d * a by nlinarith)
  linarith

/-- `φ_d(1) − φ_d(−a) − (1+a)·φ_d′(−a)`, cleared. -/
lemma phiZ_one_sub_tangent (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    phiZ d 1 - phiZ d (-a) - (1 + a) * phiZ' d (-a)
      = (2 * d * (log 2 - log (1 - a)) - (1 - d) * (log (1 + d * a) - log (1 - d)))
        / (1 + d) := by
  have hne : (1 : ℝ) + d ≠ 0 := by positivity
  rw [phiZ_eq]
  simp only [phiZ']
  rw [show (1 : ℝ) + 1 = 2 by ring, show (1 : ℝ) - d * 1 = 1 - d by ring,
    show (1 : ℝ) + -a = 1 - a by ring, show (1 : ℝ) - d * -a = 1 + d * a by ring]
  field_simp
  ring

/-- The endpoint contact of the mirror certificate. -/
theorem MDFun_one : MDFun a d 1 = 0 := by
  simp only [MDFun, GFun, mlam0, fe_one]; ring

@[simp] theorem MDFun'_at_neg_a : GFun' (mlam1 a d) (mlam2 a d) d (-a) = 0 := by
  simp only [GFun', mlam1]; ring

lemma mlam2_lt_one (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    mlam2 a d < 1 := by
  have hM := logM_pos ha0 ha1
  have hL := logL_pos ha0 hd0 hd1
  rw [mlam2, div_lt_one (by positivity)]
  nlinarith

lemma artanh_neg_eq {x : ℝ} (h0 : -1 < x) (h1 : x < 1) : artanh (-x) = -artanh x := by
  rw [artanh_eq_log_sub (by linarith) (by linarith), artanh_eq_log_sub h0 h1,
    show (1 : ℝ) + -x = 1 - x by ring, show (1 : ℝ) - -x = 1 + x by ring]
  ring

/-- The tangency contact of the mirror certificate.  Here the closed form of
`mlam2` is used. -/
theorem MDFun_at_neg_a (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    MDFun a d (-a) = 0 := by
  have hM := logM_pos ha0 ha1
  have hne : (1 : ℝ) + d ≠ 0 := by positivity
  have hP := fe_sub_tangent (a := a) (by linarith) ha1
  have hφ := phiZ_one_sub_tangent ha0 ha1 hd0 hd1
  have hmul : mlam2 a d * ((1 + d) * (log 2 - log (1 - a)))
      = 2 * d * (log 2 - log (1 - a)) - (1 - d) * (log (1 + d * a) - log (1 - d)) :=
    div_mul_cancel₀ _ (by positivity)
  have hφ2 : (1 + d) * (phiZ d 1 - phiZ d (-a) - (1 + a) * phiZ' d (-a))
      = 2 * d * (log 2 - log (1 - a)) - (1 - d) * (log (1 + d * a) - log (1 - d)) := by
    rw [hφ]; field_simp
  simp only [MDFun, GFun, mlam0, mlam1, fe_neg,
    artanh_neg_eq (show (-1:ℝ) < a by linarith) ha1]
  refine mul_left_cancel₀ hne ?_
  rw [mul_zero]
  linear_combination hφ2 - hmul + (1 + d) * mlam2 a d * hP

/-- `N(−a) ≤ 0`: the mirror key inequality in the form Shape B needs. -/
theorem mN_at_neg_a_nonpos (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    GN (mlam2 a d) d (-a) ≤ 0 := by
  have hM := logM_pos ha0 ha1
  have h1d : (0 : ℝ) < 1 - d := by linarith
  have hkey := key_mirror ha0 ha1 hd0 hd1
  have hmul : mlam2 a d * ((1 + d) * (log 2 - log (1 - a)))
      = 2 * d * (log 2 - log (1 - a)) - (1 - d) * (log (1 + d * a) - log (1 - d)) :=
    div_mul_cancel₀ _ (by positivity)
  have hpos : (0 : ℝ) < (1 + d) * (log 2 - log (1 - a)) := by positivity
  have hgoal : mlam2 a d * (1 + d * a) ≤ d * (1 + a) := by
    have h1 : mlam2 a d * (1 + d * a) * ((1 + d) * (log 2 - log (1 - a)))
        = (2 * d * (log 2 - log (1 - a))
            - (1 - d) * (log (1 + d * a) - log (1 - d))) * (1 + d * a) := by
      rw [show mlam2 a d * (1 + d * a) * ((1 + d) * (log 2 - log (1 - a)))
        = mlam2 a d * ((1 + d) * (log 2 - log (1 - a))) * (1 + d * a) from by ring, hmul]
    have hstep : mlam2 a d * (1 + d * a) * ((1 + d) * (log 2 - log (1 - a)))
        ≤ d * (1 + a) * ((1 + d) * (log 2 - log (1 - a))) := by
      rw [h1]
      nlinarith [mul_nonneg (le_of_lt h1d) (sub_nonneg.mpr hkey)]
    exact le_of_mul_le_mul_right hstep hpos
  simp only [GN]
  nlinarith [hgoal]

/-- **The mirror certificate**: `D ≤ 0` on `[−1,1]`, contacts at `−a` and `+1`,
so the Z-channel `(+1,−a)` is a global best response *for the minimum* — what
Conjecture 2 asks for. -/
theorem MDFun_nonpos (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    {s : ℝ} (hs0 : -1 ≤ s) (hs1 : s ≤ 1) : MDFun a d s ≤ 0 :=
  GFun_nonpos_of_contacts hd0 hd1 (mlam2_lt_one ha0 ha1 hd0 hd1) (by linarith) (by linarith)
    MDFun'_at_neg_a (MDFun_at_neg_a ha0 ha1 hd0 hd1) MDFun_one
    (mN_at_neg_a_nonpos ha0 ha1 hd0 hd1) hs0 hs1

end ConjTwo

/-! ## The S-channel, and the certificate as a statement about channels

`DFun_nonneg` is about one real variable.  This section turns it into a bound on
`I(U;V)` for *arbitrary* binary `cL`, by exhibiting the S-channel as a `Chan`
and computing its marginals and biases: with `x = (1−d)/(1+d)` the transition
matrix below has `ρ_false = d/(1+d)`, `ρ_true = 1/(1+d)` and bias atoms
`t_false = +1`, `t_true = −d`, which is exactly the `T` that `phiZ` encodes. -/

section SChannel

variable {d : ℝ}

/-- Transition matrix of the S-channel with parameter `d`: the *other*
crossover vanishes, `P(V=0 | Y=1) = 0`, i.e. `tr true false = 0`. -/
noncomputable def sChanTr (d : ℝ) (y v : Bool) : ℝ :=
  bif y then (bif v then 1 else 0) else (bif v then (1 - d) / (1 + d) else 1 - (1 - d) / (1 + d))

/-- The S-channel with parameter `d ∈ (0,1)`. -/
noncomputable def sChan (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) : Chan where
  tr := sChanTr d
  nonneg i j := by
    have h : (0:ℝ) < 1 + d := by linarith
    have h1 : (1 - d) / (1 + d) ≤ 1 := by rw [div_le_one h]; linarith
    have h2 : (0:ℝ) ≤ (1 - d) / (1 + d) := by positivity
    cases i <;> cases j <;> simp only [sChanTr, cond_true, cond_false] <;> linarith
  sum_one i := by
    have h : (1:ℝ) + d ≠ 0 := by positivity
    cases i <;> simp only [sChanTr, cond_true, cond_false] <;> ring

@[simp] lemma sChan_tr (hd0 : 0 < d) (hd1 : d < 1) : (sChan d hd0 hd1).tr = sChanTr d := rfl

lemma marg₂_sChan (hd0 : 0 < d) (hd1 : d < 1) :
    marg₂ (jointYV (sChan d hd0 hd1)) false = d / (1 + d) ∧
    marg₂ (jointYV (sChan d hd0 hd1)) true = 1 / (1 + d) := by
  have h : (1:ℝ) + d ≠ 0 := by positivity
  constructor <;>
    · simp only [marg₂, jointYV, sChan_tr, sChanTr, cond_true, cond_false]
      field_simp
      ring

lemma biasOfSnd_sChan (hd0 : 0 < d) (hd1 : d < 1) :
    biasOfSnd (jointYV (sChan d hd0 hd1)) false = 1 ∧
    biasOfSnd (jointYV (sChan d hd0 hd1)) true = -d := by
  have h : (1:ℝ) + d ≠ 0 := by positivity
  have hd : d ≠ 0 := ne_of_gt hd0
  obtain ⟨h1, h2⟩ := marg₂_sChan hd0 hd1
  constructor
  · rw [biasOfSnd, h1]
    simp only [jointYV, sChan_tr, sChanTr, cond_true, cond_false]
    field_simp
    ring
  · rw [biasOfSnd, h2]
    simp only [jointYV, sChan_tr, sChanTr, cond_true, cond_false]
    field_simp
    ring


/-- **The mirror multiplier is positive.**  Needed to feed
`bestResponse_ge_of_certificate`, whose rate step requires `λ₂ ≥ 0`.  With
`M = log 2 − log(1−a) > 0` and `L = log(1+da) − log(1−d)`, positivity of
`2dM − (1−d)L` follows from three instances of `log x ≤ x − 1`
(`−log(1−a) ≥ a`, `log(1+da) ≤ da`, `(1−d)·(−log(1−d)) ≤ d`) together with
`2 log 2 > 1`: the numerator is at least `d(2log 2 − 1) + d²a > 0`. -/
theorem mlam2_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    0 < mlam2 a d := by
  have hM : 0 < log 2 - log (1 - a) := logM_pos ha0 ha1
  have hd' : (0 : ℝ) < 1 - d := by linarith
  have hden : 0 < (1 + d) * (log 2 - log (1 - a)) := by positivity
  rw [mlam2]
  refine div_pos ?_ hden
  have h1 : log (1 - a) ≤ -a := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 - a by linarith); linarith
  have h2 : log (1 + d * a) ≤ d * a := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + d * a by positivity); linarith
  have h3 : (1 - d) * (-log (1 - d)) ≤ d := by
    have hinv := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 - d)⁻¹ by positivity)
    rw [Real.log_inv] at hinv
    have he : (1 - d)⁻¹ - 1 = d / (1 - d) := by field_simp; ring
    rw [he] at hinv
    have : (1 - d) * (-log (1 - d)) ≤ (1 - d) * (d / (1 - d)) :=
      mul_le_mul_of_nonneg_left hinv (le_of_lt hd')
    calc (1 - d) * (-log (1 - d)) ≤ (1 - d) * (d / (1 - d)) := this
      _ = d := by field_simp
  have hlog2 : 1 < 2 * log 2 := by
    have := Real.log_two_gt_d9; linarith
  nlinarith [mul_pos hd0 ha0, mul_nonneg (le_of_lt hd0) (le_of_lt ha0),
    mul_le_mul_of_nonneg_left h1 (le_of_lt hd0),
    mul_le_mul_of_nonneg_left h2 (le_of_lt hd'),
    mul_pos (mul_pos hd0 hd0) ha0]


end SChannel

end BSCAveraging
