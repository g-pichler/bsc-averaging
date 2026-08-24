import BSCAveraging.Rigidity

/-! # The global sign-flip theorem

`NOTES.md` §5e splits the Lagrangian objective into a part that sees only the
*magnitudes* of the two biases and a part that sees only their *signs*:

```
f(z) = (1+z)·log(1+z) = f_e(z) + fo(z),   f_e even, fo odd,
F(S,T) = E[g(|S|,|T|)] + Ω,    Ω = E[fo(δ·S·T)],
```

and the supremum of `F` over *symmetric* pairs is exactly `max g`.  So the whole
possible gain of an asymmetric pair over the symmetric optimum is `Ω`.  Because
`E S = E T = 0` and `S ⊥ T`, the linear part of `fo` drops out of `Ω`:

```
fo(δu) = δu − W(u),   W(u) = Σ_{k odd ≥ 3} (δu)^k / (k(k−1)) ≥ 0,
Ω = − E[ sign S · sign T · W(|S|·|T|) ].
```

For a two-point pair `S ∈ {a,−b}`, `T ∈ {c,−d}` this is `Ω = −λκ·Δ` with
`λ = ab/(a+b)`, `κ = cd/(c+d)` and `Δ` the mixed second difference of the kernel
`(r,q) ↦ w(r·q)`, `w(u) = W(u)/u`.  That kernel is strictly **supermodular**, so
`Δ` has the sign of `(a−b)(c−d)`, and therefore

> **`Ω > 0` if and only if the two skews point opposite ways.**

Hence at any maximizer the two skews are anti-correlated — globally, with no
linearization (`NOTES.md` §5c had only the linearized statement).

The supermodularity collapses to one elementary fact.  The identity
`fo z − z·fo′ z = artanh z − z` gives `w′(u) = (artanh(δu) − δu)/u²`, so the
cross derivative of `w(r·q)` is positive exactly when `z ↦ artanh z / z` is
increasing, i.e. exactly when `artanh z < z/(1 − z²)` — which is `artanh_lt_div`
of `BSCAveraging.Rigidity`.

See `BSCAveraging.Basic`. -/

open Real Set

namespace BSCAveraging

/-! ## Monotonicity helpers -/

lemma strictMonoOn_Ioo_of_deriv_pos (f f' : ℝ → ℝ)
    (hd : ∀ z ∈ Ioo (0:ℝ) 1, HasDerivAt f (f' z) z)
    (hpos : ∀ z ∈ Ioo (0:ℝ) 1, 0 < f' z) : StrictMonoOn f (Ioo (0:ℝ) 1) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := f') (convex_Ioo 0 1)
    (fun z hz => ((hd z hz).continuousAt).continuousWithinAt) ?_ ?_
  · rw [interior_Ioo]; exact fun z hz => (hd z hz).hasDerivWithinAt
  · rw [interior_Ioo]; exact hpos

lemma strictMonoOn_Ioc_of_deriv_pos (f f' : ℝ → ℝ)
    (hd : ∀ z ∈ Ioc (0:ℝ) 1, HasDerivAt f (f' z) z)
    (hpos : ∀ z ∈ Ioo (0:ℝ) 1, 0 < f' z) : StrictMonoOn f (Ioc (0:ℝ) 1) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := f') (convex_Ioc 0 1)
    (fun z hz => ((hd z hz).continuousAt).continuousWithinAt) ?_ ?_
  · rw [interior_Ioc]; exact fun z hz => (hd z ⟨hz.1, le_of_lt hz.2⟩).hasDerivWithinAt
  · rw [interior_Ioc]; exact hpos

/-! ## `artanh y / y` is increasing -/

/-- **`z ↦ artanh z / z` is strictly increasing on `(0,1)`.**  Its derivative is
`(z/(1−z²) − artanh z)/z²`, positive by `artanh_lt_div`.  Everything below rests
on this. -/
theorem artanh_div_strictMonoOn :
    StrictMonoOn (fun z : ℝ => artanh z / z) (Ioo (0:ℝ) 1) := by
  refine strictMonoOn_Ioo_of_deriv_pos _
    (fun z => (z / (1 - z ^ 2) - artanh z) / z ^ 2) ?_ ?_
  · intro z hz
    have h := (hasDerivAt_artanh (by linarith [hz.1]) hz.2).fun_div
      (hasDerivAt_id' (x := z)) (ne_of_gt hz.1)
    have heq : (1 / (1 - z ^ 2) * z - artanh z * 1) / z ^ 2
        = (z / (1 - z ^ 2) - artanh z) / z ^ 2 := by ring
    rwa [heq] at h
  · intro z hz
    have := artanh_lt_div hz.1 hz.2
    exact div_pos (by linarith) (pow_pos hz.1 2)

/-! ## The odd part of `f` -/

/-- The odd part of `f(z) = (1+z)·log(1+z)`. -/
noncomputable def fo (z : ℝ) : ℝ := ((1 + z) * log (1 + z) - (1 - z) * log (1 - z)) / 2

@[simp] lemma fo_zero : fo 0 = 0 := by simp [fo]

lemma fo_neg (z : ℝ) : fo (-z) = -fo z := by
  simp only [fo]
  rw [show (1 : ℝ) + -z = 1 - z by ring, show (1 : ℝ) - -z = 1 + z by ring]
  ring

/-- The derivative of `s ↦ fo (k·s)`, proved from scratch rather than by the
chain rule: `HasDerivAt.comp` produces a `Function.comp` with a different
`AddCommGroup` instance path on `ℝ`, which does not match syntactically. -/
lemma hasDerivAt_fo_mul {k t : ℝ} (h0 : -1 < k * t) (h1 : k * t < 1) :
    HasDerivAt (fun s : ℝ => fo (k * s)) ((1 + log (1 - (k * t) ^ 2) / 2) * k) t := by
  have hp : (1 : ℝ) + k * t ≠ 0 := by linarith
  have hm : (1 : ℝ) - k * t ≠ 0 := by linarith
  have hk : HasDerivAt (fun s : ℝ => k * s) k t := by simpa using (hasDerivAt_id t).const_mul k
  have ha : HasDerivAt (fun s : ℝ => 1 + k * s) k t := by simpa using hk.const_add 1
  have hb : HasDerivAt (fun s : ℝ => 1 - k * s) (-k) t := by simpa using hk.const_sub 1
  have d1 : HasDerivAt (fun s : ℝ => (1 + k * s) * log (1 + k * s))
      (k * log (1 + k * t) + k) t := by
    have h := ha.mul (ha.log hp)
    have heq : k * log (1 + k * t) + (1 + k * t) * (k / (1 + k * t))
        = k * log (1 + k * t) + k := by field_simp
    rwa [heq] at h
  have d2 : HasDerivAt (fun s : ℝ => (1 - k * s) * log (1 - k * s))
      (-k * log (1 - k * t) - k) t := by
    have h := hb.mul (hb.log hm)
    have heq : -k * log (1 - k * t) + (1 - k * t) * (-k / (1 - k * t))
        = -k * log (1 - k * t) - k := by field_simp; ring
    rwa [heq] at h
  have h := (d1.sub d2).div_const 2
  have hlog : log (1 - (k * t) ^ 2) = log (1 + k * t) + log (1 - k * t) := by
    rw [show (1 : ℝ) - (k * t) ^ 2 = (1 + k * t) * (1 - k * t) by ring, Real.log_mul hp hm]
  have heq : (k * log (1 + k * t) + k - (-k * log (1 - k * t) - k)) / 2
      = (1 + log (1 - (k * t) ^ 2) / 2) * k := by rw [hlog]; ring
  rwa [heq] at h

/-- **The key identity** `fo z − z·fo′ z = artanh z − z`.  It is what turns the
supermodularity of the odd kernel into a statement about `artanh z / z`. -/
theorem fo_sub_mul_deriv {z : ℝ} (h0 : -1 < z) (h1 : z < 1) :
    fo z - z * (1 + log (1 - z ^ 2) / 2) = artanh z - z := by
  have hp : (1 : ℝ) + z ≠ 0 := by linarith
  have hm : (1 : ℝ) - z ≠ 0 := by linarith
  have hlog : log (1 - z ^ 2) = log (1 + z) + log (1 - z) := by
    rw [show (1 : ℝ) - z ^ 2 = (1 + z) * (1 - z) by ring, Real.log_mul hp hm]
  rw [artanh_eq_log_sub h0 h1, fo, hlog]
  ring

/-! ## The profile `w` and its supermodularity -/

/-- `wFun δ u = δ − fo(δu)/u = W(u)/u`, where `W(u) = δu − fo(δu) ≥ 0` is the
part of the odd kernel that survives the mean-zero constraint. -/
noncomputable def wFun (δ u : ℝ) : ℝ := δ - fo (δ * u) / u

/-- `MFun δ u = artanh(δu)/u − δ`.  Supermodularity of `(r,q) ↦ wFun δ (r·q)` is
exactly strict monotonicity of this. -/
noncomputable def MFun (δ u : ℝ) : ℝ := artanh (δ * u) / u - δ

lemma MFun_eq {δ u : ℝ} (hδ : δ ≠ 0) (hu : u ≠ 0) :
    MFun δ u = δ * ((fun z : ℝ => artanh z / z) (δ * u)) - δ := by
  simp only [MFun]
  field_simp

theorem MFun_strictMonoOn {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    StrictMonoOn (MFun δ) (Ioc (0:ℝ) 1) := by
  intro u hu v hv huv
  have hmem : ∀ {r : ℝ}, r ∈ Ioc (0:ℝ) 1 → δ * r ∈ Ioo (0:ℝ) 1 := by
    intro r hr
    exact ⟨mul_pos hδ0 hr.1, by nlinarith [hr.1, hr.2]⟩
  have h := artanh_div_strictMonoOn (hmem hu) (hmem hv) (by nlinarith [hu.1])
  rw [MFun_eq (ne_of_gt hδ0) (ne_of_gt hu.1), MFun_eq (ne_of_gt hδ0) (ne_of_gt hv.1)]
  have := mul_lt_mul_of_pos_left h hδ0
  linarith

/-- Derivative of the slice `s ↦ wFun δ (s·c)`. -/
lemma hasDerivAt_wFun_slice {δ c t : ℝ} (hδ0 : 0 < δ) (hc0 : 0 < c) (ht0 : 0 < t)
    (h1 : δ * (t * c) < 1) :
    HasDerivAt (fun s : ℝ => wFun δ (s * c))
      ((artanh (δ * (t * c)) - δ * (t * c)) / (t * c) ^ 2 * c) t := by
  have htc : (0 : ℝ) < t * c := mul_pos ht0 hc0
  have hz0 : (-1 : ℝ) < δ * (t * c) := by nlinarith
  have hN : HasDerivAt (fun s : ℝ => fo (δ * c * s))
      ((1 + log (1 - (δ * c * t) ^ 2) / 2) * (δ * c)) t :=
    hasDerivAt_fo_mul (by nlinarith) (by nlinarith)
  rw [show δ * c * t = δ * (t * c) from by ring] at hN
  have hfun : (fun s : ℝ => fo (δ * c * s)) = fun s : ℝ => fo (δ * (s * c)) := by
    funext s; congr 1; ring
  rw [hfun] at hN
  have hD : HasDerivAt (fun s : ℝ => s * c) c t := by simpa using (hasDerivAt_id t).mul_const c
  have hw := (hN.fun_div hD (ne_of_gt htc)).const_sub δ
  have hkey := fo_sub_mul_deriv hz0 h1
  have hnum : (1 + log (1 - (δ * (t * c)) ^ 2) / 2) * (δ * c) * (t * c) - fo (δ * (t * c)) * c
      = -(c * (artanh (δ * (t * c)) - δ * (t * c))) := by
    rw [← hkey]; ring
  have heq : -(((1 + log (1 - (δ * (t * c)) ^ 2) / 2) * (δ * c) * (t * c)
        - fo (δ * (t * c)) * c) / (t * c) ^ 2)
      = (artanh (δ * (t * c)) - δ * (t * c)) / (t * c) ^ 2 * c := by
    rw [hnum]; ring
  rw [heq] at hw
  exact hw

/-- The one-variable slice `r ↦ w(r·c) − w(r·d)` is strictly increasing when
`d < c`.  Its derivative is `(MFun δ (r·c) − MFun δ (r·d))/r`. -/
theorem slice_strictMonoOn {δ c d : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hd0 : 0 < d) (hdc : d < c) (hc1 : c ≤ 1) :
    StrictMonoOn (fun r : ℝ => wFun δ (r * c) - wFun δ (r * d)) (Ioc (0:ℝ) 1) := by
  have hc0 : 0 < c := hd0.trans hdc
  have hd1 : d ≤ 1 := le_of_lt (hdc.trans_le hc1)
  refine strictMonoOn_Ioc_of_deriv_pos _
    (fun r => (MFun δ (r * c) - MFun δ (r * d)) / r) ?_ ?_
  · intro r hr
    have hr0 : 0 < r := hr.1
    have hrcle : r * c ≤ 1 := by nlinarith [hr.1, hr.2, hc0, hc1]
    have hrdle : r * d ≤ 1 := by nlinarith [hr.1, hr.2, hd0, hd1]
    have hrc1 : δ * (r * c) < 1 := by
      nlinarith [mul_nonneg (le_of_lt hδ0) (sub_nonneg.mpr hrcle)]
    have hrd1 : δ * (r * d) < 1 := by
      nlinarith [mul_nonneg (le_of_lt hδ0) (sub_nonneg.mpr hrdle)]
    have h := (hasDerivAt_wFun_slice hδ0 hc0 hr0 hrc1).sub
      (hasDerivAt_wFun_slice hδ0 hd0 hr0 hrd1)
    have hrne : r ≠ 0 := ne_of_gt hr0
    have hcne : c ≠ 0 := ne_of_gt hc0
    have hdne : d ≠ 0 := ne_of_gt hd0
    have heq : (artanh (δ * (r * c)) - δ * (r * c)) / (r * c) ^ 2 * c
        - (artanh (δ * (r * d)) - δ * (r * d)) / (r * d) ^ 2 * d
        = (MFun δ (r * c) - MFun δ (r * d)) / r := by
      simp only [MFun]
      field_simp
    rwa [heq] at h
  · intro r hr
    have hr0 : 0 < r := hr.1
    have hr1 : r ≤ 1 := le_of_lt hr.2
    have hmc : r * c ∈ Ioc (0:ℝ) 1 := ⟨mul_pos hr0 hc0, by nlinarith⟩
    have hmd : r * d ∈ Ioc (0:ℝ) 1 := ⟨mul_pos hr0 hd0, by nlinarith⟩
    have := MFun_strictMonoOn hδ0 hδ1 hmd hmc (by nlinarith)
    exact div_pos (by linarith) hr0

/-- **Strict supermodularity of the odd kernel.**  For `0 < b < a ≤ 1` and
`0 < d < c ≤ 1` the mixed second difference of `(r,q) ↦ wFun δ (r·q)` is
positive. -/
theorem wFun_mixed_diff_pos {δ a b c d : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hb0 : 0 < b) (hba : b < a) (ha1 : a ≤ 1)
    (hd0 : 0 < d) (hdc : d < c) (hc1 : c ≤ 1) :
    0 < wFun δ (a * c) - wFun δ (a * d) - (wFun δ (b * c) - wFun δ (b * d)) := by
  have hb1 : b ≤ 1 := le_of_lt (hba.trans_le ha1)
  have h : wFun δ (b * c) - wFun δ (b * d) < wFun δ (a * c) - wFun δ (a * d) :=
    slice_strictMonoOn hδ0 hδ1 hd0 hdc hc1 ⟨hb0, hb1⟩ ⟨hb0.trans hba, ha1⟩ hba
  linarith

/-! ## The sign of `Ω` -/

/-- `Ω = E[fo(δ·S·T)]` for the two-point pair `S ∈ {a,−b}`, `T ∈ {c,−d}` with
the mean-zero weights `P(S=a) = b/(a+b)`, `P(T=c) = d/(c+d)`, written out (using
that `fo` is odd). -/
noncomputable def OmegaTwoPoint (δ a b c d : ℝ) : ℝ :=
  (b * d * fo (δ * (a * c)) - b * c * fo (δ * (a * d))
    - a * d * fo (δ * (b * c)) + a * c * fo (δ * (b * d))) / ((a + b) * (c + d))

/-- `Ω = −λκ·Δ` with `λ = ab/(a+b)`, `κ = cd/(c+d)`.  The constant `δ` parts of
`wFun` cancel in the mixed difference, so only the `fo` parts survive. -/
theorem omegaTwoPoint_eq {δ a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    OmegaTwoPoint δ a b c d
      = -(a * b / (a + b)) * (c * d / (c + d))
        * (wFun δ (a * c) - wFun δ (a * d) - (wFun δ (b * c) - wFun δ (b * d))) := by
  have hab : a + b ≠ 0 := by positivity
  have hcd : c + d ≠ 0 := by positivity
  have hane : a ≠ 0 := ne_of_gt ha
  have hbne : b ≠ 0 := ne_of_gt hb
  have hcne : c ≠ 0 := ne_of_gt hc
  have hdne : d ≠ 0 := ne_of_gt hd
  simp only [OmegaTwoPoint, wFun]
  field_simp
  ring

/-- **Global sign flip.**  If the two skews point the same way (`b < a` and
`d < c`) then `Ω < 0`, so relabelling one side (`S ↦ −S`) strictly increases the
objective.  Hence at any maximizer the two skews are anti-correlated. -/
theorem omegaTwoPoint_neg {δ a b c d : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hb0 : 0 < b) (hba : b < a) (ha1 : a ≤ 1)
    (hd0 : 0 < d) (hdc : d < c) (hc1 : c ≤ 1) :
    OmegaTwoPoint δ a b c d < 0 := by
  have ha0 : 0 < a := hb0.trans hba
  have hc0 : 0 < c := hd0.trans hdc
  rw [omegaTwoPoint_eq ha0 hb0 hc0 hd0, neg_mul, neg_mul, neg_lt_zero]
  exact mul_pos (mul_pos (by positivity) (by positivity))
    (wFun_mixed_diff_pos hδ0 hδ1 hb0 hba ha1 hd0 hdc hc1)

end BSCAveraging
