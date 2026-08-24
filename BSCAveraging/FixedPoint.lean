import BSCAveraging.Lagrangian

/-! # The fixed-point manifold: closed forms, the route-2 identity, and (E4)

`NOTES.md` §6 records a set of identities on the alternating-maximisation
fixed-point manifold, all verified numerically to `< 4e-14`.  This file proves
them.

A fixed point is parametrised by the two-point data `a,b` (U-side) and `c,d`
(V-side) together with `δ`.  The `(m,k)` coordinates are *defined* from `a,b`:

```
m = (b−a)/(a+b),   k = 2ab/(a+b)        (equivalently a = k/(1+m), b = k/(1−m))
```

so that `1 + m = 2b/(a+b)` and `1 − m = 2a/(a+b)`.  Everything then rests on one
factorisation, proved in `one_add_bOne` and friends:

```
1 + b₁ = (1+m)(1 + aδc),     1 − b₁ = (1−m)(1 − bδc)
1 + b₂ = (1+m)(1 − aδd),     1 − b₂ = (1−m)(1 + bδd)
```

From it: `D = artanh a + artanh b` (`DOf_eq`), `Δℓ` is a combination of the four
joint logarithms (`DlOf_eq`), and the `log(1±m)` terms in `I(U;V)` cancel because
`wc·c = wd·d`, giving `mutualTP_eq`.  The results are

```
𝒥(U;V) = k·δ·κ·Δℓ                                     jeffreysTP_eq
I(U;V) = wc·f_e(b₁) + wd·f_e(b₂) − f_e(m)                   mutualTP_eq
ρ(U;X) = 2(A − f_e(m))/(k·D) = G(a,b)                   rhoUX_eq
Φ      = k·δ·κ·Δℓ · [ρ(U;V) − G(a,b) − G(c,d)]        route_identity
```

For (E4) this file proves the statement that is actually settled: that it holds
**automatically at symmetric points**, so it carries only asymmetric content.
Its *variational* characterisation — that solutions of (E2),(E4) are exactly the
best responses — is supported by numerics (`5.6e-14`) but is **not** claimed
here; formalising it needs the variational setup, which this development does
not yet have.

See `BSCAveraging.Basic`. -/

open Real Set

namespace BSCAveraging
/-- `f_e` composed with an affine map. -/
lemma hasDerivAt_fe_affine {p K x : ℝ} (h0 : -1 < p + K * x) (h1 : p + K * x < 1) :
    HasDerivAt (fun t : ℝ => fe (p + K * t)) (artanh (p + K * x) * K) x := by
  have hp : (0 : ℝ) < 1 + (p + K * x) := by linarith
  have hm : (0 : ℝ) < 1 - (p + K * x) := by linarith
  have hK : HasDerivAt (fun t : ℝ => p + K * t) K x := by
    simpa using ((hasDerivAt_id x).const_mul K).const_add p
  have ha : HasDerivAt (fun t : ℝ => 1 + (p + K * t)) K x := by simpa using hK.const_add 1
  have hb : HasDerivAt (fun t : ℝ => 1 - (p + K * t)) (-K) x := by simpa using hK.const_sub 1
  have d1 : HasDerivAt (fun t : ℝ => (1 + (p + K * t)) * log (1 + (p + K * t)))
      (K * log (1 + (p + K * x)) + (1 + (p + K * x)) * (K / (1 + (p + K * x)))) x :=
    ha.mul (ha.log (ne_of_gt hp))
  have d2 : HasDerivAt (fun t : ℝ => (1 - (p + K * t)) * log (1 - (p + K * t)))
      (-K * log (1 - (p + K * x)) + (1 - (p + K * x)) * (-K / (1 - (p + K * x)))) x :=
    hb.mul (hb.log (ne_of_gt hm))
  have h : HasDerivAt (fun t : ℝ => fe (p + K * t))
      ((K * log (1 + (p + K * x)) + (1 + (p + K * x)) * (K / (1 + (p + K * x)))
        + (-K * log (1 - (p + K * x)) + (1 - (p + K * x)) * (-K / (1 - (p + K * x))))) / 2) x := by
    simpa only [fe] using (d1.fun_add d2).div_const 2
  have heq : (K * log (1 + (p + K * x)) + (1 + (p + K * x)) * (K / (1 + (p + K * x)))
      + (-K * log (1 - (p + K * x)) + (1 - (p + K * x)) * (-K / (1 - (p + K * x))))) / 2
      = artanh (p + K * x) * K := by
    rw [artanh_eq_log_sub h0 h1]
    field_simp
    ring
  rwa [heq] at h

/-- `g(p,q) = f_e(δpq) − μf_e(p) − νf_e(q)`, the value of the symmetric (BSC) pair. -/
noncomputable def gSym (δ μ ν p q : ℝ) : ℝ := fe (δ * (p * q)) - μ * fe p - ν * fe q

/-- The Lagrangian `F = E[f(δST)] − μ·E[f_e(S)] − ν·E[f_e(T)]` of the two-point pair. -/
noncomputable def lagrTwoPoint (δ μ ν a b c d : ℝ) : ℝ :=
  (b * d * fFun (δ * (a * c)) + b * c * fFun (-(δ * (a * d)))
    + a * d * fFun (-(δ * (b * c))) + a * c * fFun (δ * (b * d))) / ((a + b) * (c + d))
  - μ * ((b * fe a + a * fe b) / (a + b)) - ν * ((d * fe c + c * fe d) / (c + d))

/-- The magnitude part `Σ wᵢⱼ·g(|sᵢ|,|tⱼ|)`. -/
noncomputable def gSum (δ μ ν a b c d : ℝ) : ℝ :=
  (b * d * gSym δ μ ν a c + b * c * gSym δ μ ν a d
    + a * d * gSym δ μ ν b c + a * c * gSym δ μ ν b d) / ((a + b) * (c + d))

/-- **The magnitude/sign split**: `F = Σ wᵢⱼ g(|sᵢ|,|tⱼ|) + Ω`. -/
theorem lagrTwoPoint_eq_gSum_add_Omega {δ μ ν a b c d : ℝ}
    (hab : a + b ≠ 0) (hcd : c + d ≠ 0) :
    lagrTwoPoint δ μ ν a b c d = gSum δ μ ν a b c d + OmegaTwoPoint δ a b c d := by
  simp only [lagrTwoPoint, gSum, gSym, OmegaTwoPoint, fFun_eq_fe_add_fo]
  rw [show -(δ * (a * d)) = -(δ * (a * d)) from rfl]
  rw [fe_neg (δ * (a * d)), fe_neg (δ * (b * c)), fo_neg, fo_neg]
  field_simp
  ring

/-- The magnitude part is an average of four values of `g`, hence bounded by any
common upper bound for them. -/
theorem gSum_le_of_le {δ μ ν a b c d M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hab : 0 < a + b) (hcd : 0 < c + d)
    (h1 : gSym δ μ ν a c ≤ M) (h2 : gSym δ μ ν a d ≤ M)
    (h3 : gSym δ μ ν b c ≤ M) (h4 : gSym δ μ ν b d ≤ M) :
    gSum δ μ ν a b c d ≤ M := by
  have hden : (0:ℝ) < (a + b) * (c + d) := mul_pos hab hcd
  rw [gSum, div_le_iff₀ hden]
  nlinarith [mul_nonneg hb hd, mul_nonneg hb hc, mul_nonneg ha hd, mul_nonneg ha hc,
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hb hd),
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hb hc),
    mul_le_mul_of_nonneg_left h3 (mul_nonneg ha hd),
    mul_le_mul_of_nonneg_left h4 (mul_nonneg ha hc)]

/-- **`Ω ≤ 0` implies the conjecture at that configuration.**  `M` is any bound
for `g` on the four magnitude pairs — in particular `J_sym = sup_ℬ F`. -/
theorem lagrTwoPoint_le_of_omega_nonpos {δ μ ν a b c d M : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hab : 0 < a + b) (hcd : 0 < c + d)
    (h1 : gSym δ μ ν a c ≤ M) (h2 : gSym δ μ ν a d ≤ M)
    (h3 : gSym δ μ ν b c ≤ M) (h4 : gSym δ μ ν b d ≤ M)
    (hΩ : OmegaTwoPoint δ a b c d ≤ 0) :
    lagrTwoPoint δ μ ν a b c d ≤ M := by
  rw [lagrTwoPoint_eq_gSum_add_Omega (ne_of_gt hab) (ne_of_gt hcd)]
  have := gSum_le_of_le ha hb hc hd hab hcd h1 h2 h3 h4
  linarith

/-- **Same-direction skews never beat the symmetric optimum.**  If `b < a` and
`d < c` then `Ω < 0` (`omegaTwoPoint_neg`), so `F < J_sym` strictly — with no
multiplier hypothesis and no fixed-point hypothesis.  Half the configuration
space is disposed of unconditionally. -/
theorem lagrTwoPoint_lt_of_same_skew {δ μ ν a b c d M : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hb0 : 0 < b) (hba : b < a) (ha1 : a ≤ 1)
    (hd0 : 0 < d) (hdc : d < c) (hc1 : c ≤ 1)
    (h1 : gSym δ μ ν a c ≤ M) (h2 : gSym δ μ ν a d ≤ M)
    (h3 : gSym δ μ ν b c ≤ M) (h4 : gSym δ μ ν b d ≤ M) :
    lagrTwoPoint δ μ ν a b c d < M := by
  have ha0 : 0 < a := hb0.trans hba
  have hc0 : 0 < c := hd0.trans hdc
  have hab : a + b ≠ 0 := by positivity
  have hcd : c + d ≠ 0 := by positivity
  have hΩ := omegaTwoPoint_neg hδ0 hδ1 hb0 hba ha1 hd0 hdc hc1
  rw [lagrTwoPoint_eq_gSum_add_Omega hab hcd]
  have := gSum_le_of_le (le_of_lt ha0) (le_of_lt hb0) (le_of_lt hc0) (le_of_lt hd0)
    (by linarith) (by linarith) h1 h2 h3 h4
  linarith

/-! ## (S): the remaining half, and its two drivers

After `lagrTwoPoint_lt_of_same_skew` only the **opposite-skew** case is open,
where `Ω > 0` (opposite skews flip the rectangle in `wFun_mixed_diff_pos`).  There the target is

> **(S)**  `Ω  ≤  max g − Σ wᵢⱼ·g(|sᵢ|,|tⱼ|)`

— the odd gain is at most the deficit of the magnitude-average from its maximum.
Both sides are `≥ 0`.

The two sides have matching order.  Writing `|S| ∈ {a,b}` with probabilities
`(b,a)/(a+b)` and `|T| ∈ {c,d}` with `(d,c)/(c+d)`:

```
E|S| = 2ab/(a+b) = k          E[|S|²] = ab
Var|S| = ab − k² = ab(a−b)²/(a+b)²                     absVar_eq
```

so the Jensen gap driving the deficit is quadratic in `(a−b)` and `(c−d)`
separately, while `Ω` is a *mixed* second difference, bilinear in
`(a−b)·(c−d)`.  Both vanish on the symmetric locus (`omegaTwoPoint_zero_of_fst_eq`,
`..._snd_eq`), so (S) is a comparison of two quadratic forms — the general-position
version of §5d's local rigidity, and by AM–GM a `2×2` discriminant condition. -/

/-- `Ω = 0` when the U-side is unskewed. -/
theorem omegaTwoPoint_zero_of_fst_eq (δ a c d : ℝ) : OmegaTwoPoint δ a a c d = 0 := by
  rw [OmegaTwoPoint]; ring_nf

/-- `Ω = 0` when the V-side is unskewed. -/
theorem omegaTwoPoint_zero_of_snd_eq (δ a b c : ℝ) : OmegaTwoPoint δ a b c c = 0 := by
  rw [OmegaTwoPoint]; ring_nf

/-- `z ↦ z·artanh z` is strictly increasing on `[0,1)`; its derivative is
`artanh z + z/(1−z²) > 0`. -/
theorem mulArtanh_strictMonoOn : StrictMonoOn (fun z : ℝ => z * artanh z) (Ico (0:ℝ) 1) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun z => artanh z + z / (1 - z ^ 2))
    (convex_Ico 0 1) ?_ ?_ ?_
  · intro x hx
    have h := (hasDerivAt_id' (x := x)).fun_mul
      (hasDerivAt_artanh (by linarith [hx.1]) hx.2)
    exact (h.continuousAt).continuousWithinAt
  · rw [interior_Ico]
    intro x hx
    have h := (hasDerivAt_id' (x := x)).fun_mul
      (hasDerivAt_artanh (by linarith [hx.1]) hx.2)
    have heq : 1 * artanh x + x * (1 / (1 - x ^ 2)) = artanh x + x / (1 - x ^ 2) := by ring
    rw [heq] at h
    exact h.hasDerivWithinAt
  · rw [interior_Ico]
    intro x hx
    have h1 : 0 < artanh x := Real.artanh_pos (Set.mem_Ioo.mpr ⟨hx.1, hx.2⟩)
    have h2 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have h3 : 0 < x / (1 - x ^ 2) := div_pos hx.1 h2
    linarith

/-- Derivative of the slice `r ↦ f_e(δ·r·q)`. -/
lemma hasDerivAt_fe_mul_slice {δ q r : ℝ} (h0 : -1 < δ * (r * q)) (h1 : δ * (r * q) < 1) :
    HasDerivAt (fun x : ℝ => fe (δ * (x * q))) (artanh (δ * (r * q)) * (δ * q)) r := by
  have e : δ * q * r = δ * (r * q) := by ring
  have h0' : (-1 : ℝ) < 0 + δ * q * r := by rw [zero_add, e]; exact h0
  have h1' : (0 : ℝ) + δ * q * r < 1 := by rw [zero_add, e]; exact h1
  have h := hasDerivAt_fe_affine (p := 0) (K := δ * q) (x := r) h0' h1'
  have hfun : (fun t : ℝ => fe (0 + δ * q * t)) = fun x : ℝ => fe (δ * (x * q)) := by
    funext t; congr 1; ring
  rw [hfun, zero_add, e] at h
  exact h

/-- The slice `r ↦ f_e(δ·r·q₂) − f_e(δ·r·q₁)` is strictly increasing for `q₁ < q₂`. -/
theorem fe_mul_slice_strictMonoOn {δ q₁ q₂ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hq0 : 0 < q₁) (hq : q₁ < q₂) (hq1 : q₂ ≤ 1) :
    StrictMonoOn (fun r : ℝ => fe (δ * (r * q₂)) - fe (δ * (r * q₁))) (Ioc (0:ℝ) 1) := by
  have hq₂0 : 0 < q₂ := hq0.trans hq
  have hrange : ∀ {r q : ℝ}, 0 < r → r ≤ 1 → 0 < q → q ≤ 1 →
      -1 < δ * (r * q) ∧ δ * (r * q) < 1 := by
    intro r q hr0 hr1 hqq0 hqq1
    have hp : 0 < δ * (r * q) := by positivity
    have hle : r * q ≤ 1 := by nlinarith
    constructor
    · linarith
    · nlinarith [mul_pos hr0 hqq0]
  refine strictMonoOn_Ioc_of_deriv_pos _
    (fun r => artanh (δ * (r * q₂)) * (δ * q₂) - artanh (δ * (r * q₁)) * (δ * q₁)) ?_ ?_
  · intro r hr
    obtain ⟨a0, a1⟩ := hrange hr.1 hr.2 hq₂0 hq1
    obtain ⟨b0, b1⟩ := hrange hr.1 hr.2 hq0 (le_of_lt (hq.trans_le hq1))
    exact (hasDerivAt_fe_mul_slice a0 a1).sub (hasDerivAt_fe_mul_slice b0 b1)
  · intro r hr
    have hr0 : 0 < r := hr.1
    have hr1' : r ≤ 1 := le_of_lt hr.2
    obtain ⟨a0, a1⟩ := hrange hr.1 hr1' hq₂0 hq1
    obtain ⟨b0, b1⟩ := hrange hr.1 hr1' hq0 (le_of_lt (hq.trans_le hq1))
    -- `artanh(zᵢ)·δqᵢ = zᵢ·artanh(zᵢ)/r`, and `z ↦ z·artanh z` is increasing
    have hmem₁ : δ * (r * q₁) ∈ Ico (0:ℝ) 1 := ⟨by positivity, b1⟩
    have hmem₂ : δ * (r * q₂) ∈ Ico (0:ℝ) 1 := ⟨by positivity, a1⟩
    have hlt : δ * (r * q₁) < δ * (r * q₂) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hq hr0) hδ0
    have hM := mulArtanh_strictMonoOn hmem₁ hmem₂ hlt
    simp only at hM
    have key : artanh (δ * (r * q₂)) * (δ * q₂) - artanh (δ * (r * q₁)) * (δ * q₁)
        = (δ * (r * q₂) * artanh (δ * (r * q₂))
            - δ * (r * q₁) * artanh (δ * (r * q₁))) / r := by
      field_simp
    rw [key]
    exact div_pos (by linarith) hr0

/-- **`(p,q) ↦ f_e(δpq)` is strictly supermodular.**  This is the cross term that
destroys joint concavity of `Φ` in the entropy coordinates, and hence the source
of the concave-envelope slack available to (S). -/
theorem fe_mul_supermodular {δ p₁ p₂ q₁ q₂ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hp0 : 0 < p₁) (hp : p₁ < p₂) (hp1 : p₂ ≤ 1)
    (hq0 : 0 < q₁) (hq : q₁ < q₂) (hq1 : q₂ ≤ 1) :
    fe (δ * (p₁ * q₁)) + fe (δ * (p₂ * q₂))
      > fe (δ * (p₁ * q₂)) + fe (δ * (p₂ * q₁)) := by
  have h := fe_mul_slice_strictMonoOn hδ0 hδ1 hq0 hq hq1
    (Set.mem_Ioc.mpr ⟨hp0, le_of_lt (hp.trans_le hp1)⟩)
    (Set.mem_Ioc.mpr ⟨hp0.trans hp, hp1⟩) hp
  simp only at h
  linarith

/-! ## (S4): the finite four-corner form

`max g ≥ g` at each of the four corners `(a,c), (a,d), (b,c), (b,d)`, and `gSum`
is exactly their weighted average.  So a **purely finite** sufficient condition
for the conjecture is

> **(S4)**  `Ω ≤ gMax4 − gSum`   (the spread of the four corner values)

No continuum maximisation, no concave envelope, no `f_e⁻¹`.  Since
`gMax4 − gSum ≥ 0` always (`gSum_le_of_le`), (S4) asks only that the odd gain be
dominated by the spread the four corners already exhibit.

Numerically `min_{μ,ν≥0}[gMax4 − gSum]` is a small **LP** (all four differences
are affine in `μ,ν`), and at the configuration that refutes (S′) it gives ratio
`Ω/spread = 0.428 ≤ 1` — the finite bound suffices there where the MGL-matched
one fails.  See `NOTES.md` §6. -/

/-- The largest of the four corner values of `g`. -/
noncomputable def gMax4 (δ μ ν a b c d : ℝ) : ℝ :=
  max (max (gSym δ μ ν a c) (gSym δ μ ν a d)) (max (gSym δ μ ν b c) (gSym δ μ ν b d))

/-- Any common bound on the four corners bounds `gMax4`. -/
theorem gMax4_le {δ μ ν a b c d M : ℝ}
    (h1 : gSym δ μ ν a c ≤ M) (h2 : gSym δ μ ν a d ≤ M)
    (h3 : gSym δ μ ν b c ≤ M) (h4 : gSym δ μ ν b d ≤ M) :
    gMax4 δ μ ν a b c d ≤ M :=
  max_le (max_le h1 h2) (max_le h3 h4)

/-- **The spread bound ⟹ `F ≤ gMax4`.** -/
theorem lagrTwoPoint_le_gMax4_of_omega_le_spread {δ μ ν a b c d : ℝ}
    (hab : a + b ≠ 0) (hcd : c + d ≠ 0)
    (hspread : OmegaTwoPoint δ a b c d ≤ gMax4 δ μ ν a b c d - gSum δ μ ν a b c d) :
    lagrTwoPoint δ μ ν a b c d ≤ gMax4 δ μ ν a b c d := by
  rw [lagrTwoPoint_eq_gSum_add_Omega hab hcd]
  linarith

/-- **The spread bound ⟹ the conjecture at that configuration.**  With
`M = J_sym` this is `F ≤ J_sym`, from a purely finite hypothesis. -/
theorem lagrTwoPoint_le_of_omega_le_spread {δ μ ν a b c d M : ℝ}
    (hab : a + b ≠ 0) (hcd : c + d ≠ 0)
    (h1 : gSym δ μ ν a c ≤ M) (h2 : gSym δ μ ν a d ≤ M)
    (h3 : gSym δ μ ν b c ≤ M) (h4 : gSym δ μ ν b d ≤ M)
    (hspread : OmegaTwoPoint δ a b c d ≤ gMax4 δ μ ν a b c d - gSum δ μ ν a b c d) :
    lagrTwoPoint δ μ ν a b c d ≤ M :=
  le_trans (lagrTwoPoint_le_gMax4_of_omega_le_spread hab hcd hspread) (gMax4_le h1 h2 h3 h4)

/-! ## The two mixed differences

Both sides of (S4) are governed by mixed second differences at the *same*
configuration, which is what makes them comparable (unlike every refuted
cross-configuration decoupling).

* **`Δ_g` is multiplier-free.**  In a mixed difference the `μf_e(pᵢ)` and `νf_e(qⱼ)`
  terms cancel — each depends on one index only — leaving
  `Δ_g = f_e(z_ac) − f_e(z_ad) − f_e(z_bc) + f_e(z_bd)`, and this is **negative** under
  opposite skews by `fe_mul_supermodular`.
* **`Ω = λκ·Δ_φ`** exactly, with `φ(u) = fo(δu)/u = δ − wFun δ u`, and `Δ_φ > 0`
  under opposite skews (`wFun_mixed_diff_pos`, rectangle flipped).

So `Δ_g < 0 < Δ_φ`: the two mixed differences have **opposite signs**, both
driven by supermodularity — of `f_e(δpq)` and of the odd kernel respectively. -/

/-- **`Δ_g` is multiplier-free**: `μ` and `ν` cancel in the mixed difference. -/
theorem gSym_mixed_diff_eq (δ μ ν a b c d : ℝ) :
    gSym δ μ ν a c - gSym δ μ ν a d - gSym δ μ ν b c + gSym δ μ ν b d
      = fe (δ * (a * c)) - fe (δ * (a * d)) - fe (δ * (b * c)) + fe (δ * (b * d)) := by
  simp only [gSym]; ring

/-- `φ(u) = fo(δu)/u`, the odd profile; `wFun δ u = δ − φ(u)`. -/
noncomputable def phiOdd (δ u : ℝ) : ℝ := fo (δ * u) / u

lemma wFun_eq_sub_phiOdd (δ u : ℝ) : wFun δ u = δ - phiOdd δ u := by
  rw [wFun, phiOdd]

/-- **`Ω = λκ·Δ_φ`**, the mixed difference of the odd profile. -/
theorem omegaTwoPoint_eq_phiOdd {δ a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    OmegaTwoPoint δ a b c d
      = (a * b / (a + b)) * (c * d / (c + d))
        * (phiOdd δ (a * c) - phiOdd δ (a * d) - phiOdd δ (b * c) + phiOdd δ (b * d)) := by
  rw [omegaTwoPoint_eq ha hb hc hd]
  simp only [wFun_eq_sub_phiOdd]
  ring

/-! ## Towards a proof of (S4)

Three steps, all resting on one pointwise fact.

```
STEP 1   Ω ≤ λκδ·|Δ_g|                    ⟸  z ≤ (1+z²)·artanh z
STEP 2   gMax4 − gSum ≥ min(w_ac,w_bd)·|Δ_g|     (2×2 algebra)
STEP 3   λκδ ≤ min(w_ac,w_bd)             ⟺  a·c·δ ≤ 1  and  b·d·δ ≤ 1
────────────────────────────────────────────────────────────────────────
         Ω ≤ gMax4 − gSum                 = (S4)
```

Step 1 goes through `u·H′(u) = δ[1 − L(z)/z + z·L(z)]` for
`H(u) = fo(δu)/u + δ·f_e(δu)`, whose `z`-derivative is `L(z)(1+1/z²) − 1/z`,
non-negative exactly when `(1+z²)·artanh z ≥ z` — which is `self_lt_artanh`.
So the whole argument reduces to that single inequality. -/

/-- **STEP 2.**  The corner spread dominates `min(w_ac,w_bd)·|Δ_g|`.  Pure 2×2
algebra: drop two non-negative terms, use `w ≥ w_min`, then `2·gMax4 ≥ g_ad + g_bc`. -/
theorem spread_ge_min_weight_mul {δ μ ν a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    min (b * d / ((a + b) * (c + d))) (a * c / ((a + b) * (c + d)))
        * (gSym δ μ ν a d + gSym δ μ ν b c - gSym δ μ ν a c - gSym δ μ ν b d)
      ≤ gMax4 δ μ ν a b c d - gSum δ μ ν a b c d := by
  have hab : (0:ℝ) < a + b := by linarith
  have hcd : (0:ℝ) < c + d := by linarith
  have hN : (0:ℝ) < (a + b) * (c + d) := mul_pos hab hcd
  set M := gMax4 δ μ ν a b c d with hM
  have hac : gSym δ μ ν a c ≤ M := le_max_of_le_left (le_max_left _ _)
  have had : gSym δ μ ν a d ≤ M := le_max_of_le_left (le_max_right _ _)
  have hbc : gSym δ μ ν b c ≤ M := le_max_of_le_right (le_max_left _ _)
  have hbd : gSym δ μ ν b d ≤ M := le_max_of_le_right (le_max_right _ _)
  set wmin := min (b * d / ((a + b) * (c + d))) (a * c / ((a + b) * (c + d))) with hw
  have hw1 : wmin ≤ b * d / ((a + b) * (c + d)) := min_le_left _ _
  have hw2 : wmin ≤ a * c / ((a + b) * (c + d)) := min_le_right _ _
  have hwpos : 0 < wmin := lt_min (by positivity) (by positivity)
  -- expand `gMax4 − gSum` as a weighted sum of the four non-negative gaps
  have hexp : M - gSum δ μ ν a b c d
      = (b * d / ((a + b) * (c + d))) * (M - gSym δ μ ν a c)
        + (b * c / ((a + b) * (c + d))) * (M - gSym δ μ ν a d)
        + (a * d / ((a + b) * (c + d))) * (M - gSym δ μ ν b c)
        + (a * c / ((a + b) * (c + d))) * (M - gSym δ μ ν b d) := by
    rw [gSum]; field_simp; ring
  rw [hexp]
  have t2 : 0 ≤ (b * c / ((a + b) * (c + d))) * (M - gSym δ μ ν a d) :=
    mul_nonneg (by positivity) (by linarith)
  have t3 : 0 ≤ (a * d / ((a + b) * (c + d))) * (M - gSym δ μ ν b c) :=
    mul_nonneg (by positivity) (by linarith)
  have e1 : wmin * (M - gSym δ μ ν a c)
      ≤ (b * d / ((a + b) * (c + d))) * (M - gSym δ μ ν a c) :=
    mul_le_mul_of_nonneg_right hw1 (by linarith)
  have e2 : wmin * (M - gSym δ μ ν b d)
      ≤ (a * c / ((a + b) * (c + d))) * (M - gSym δ μ ν b d) :=
    mul_le_mul_of_nonneg_right hw2 (by linarith)
  -- `2M ≥ g_ad + g_bc`
  have hkey : wmin * (gSym δ μ ν a d + gSym δ μ ν b c - gSym δ μ ν a c - gSym δ μ ν b d)
      ≤ wmin * (M - gSym δ μ ν a c) + wmin * (M - gSym δ μ ν b d) := by
    have : gSym δ μ ν a d + gSym δ μ ν b c - gSym δ μ ν a c - gSym δ μ ν b d
        ≤ (M - gSym δ μ ν a c) + (M - gSym δ μ ν b d) := by linarith
    nlinarith [hwpos, this]
  linarith

/-- **STEP 3.**  `λκδ ≤ min(w_ac, w_bd)`, because `acδ ≤ 1` and `bdδ ≤ 1`. -/
theorem lam_kap_mul_le_min_weight {δ a b c d : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (a * b / (a + b)) * (c * d / (c + d)) * δ
      ≤ min (b * d / ((a + b) * (c + d))) (a * c / ((a + b) * (c + d))) := by
  have hab : (0:ℝ) < a + b := by linarith
  have hcd : (0:ℝ) < c + d := by linarith
  have hN : (0:ℝ) < (a + b) * (c + d) := mul_pos hab hcd
  have hac1 : a * c ≤ 1 := mul_le_one₀ ha1 (le_of_lt hc0) hc1
  have hbd1 : b * d ≤ 1 := mul_le_one₀ hb1 (le_of_lt hd0) hd1
  have hac : a * c * δ ≤ 1 := mul_le_one₀ hac1 (le_of_lt hδ0) hδ1
  have hbd : b * d * δ ≤ 1 := mul_le_one₀ hbd1 (le_of_lt hδ0) hδ1
  refine le_min ?_ ?_
  · have hid : b * d / ((a + b) * (c + d)) - (a * b / (a + b)) * (c * d / (c + d)) * δ
        = b * d * (1 - a * c * δ) / ((a + b) * (c + d)) := by
      field_simp
    have : 0 ≤ b * d * (1 - a * c * δ) / ((a + b) * (c + d)) := by
      apply div_nonneg _ (le_of_lt hN)
      have : 0 ≤ 1 - a * c * δ := by linarith
      positivity
    linarith [hid, this]
  · have hid : a * c / ((a + b) * (c + d)) - (a * b / (a + b)) * (c * d / (c + d)) * δ
        = a * c * (1 - b * d * δ) / ((a + b) * (c + d)) := by
      field_simp
    have : 0 ≤ a * c * (1 - b * d * δ) / ((a + b) * (c + d)) := by
      apply div_nonneg _ (le_of_lt hN)
      have : 0 ≤ 1 - b * d * δ := by linarith
      positivity
    linarith [hid, this]

/-! ### The heart of STEP 1

`u·H′(u) = δ·K(δu)` for `H(u) = fo(δu)/u + δ·f_e(δu)`, where

```
K(z) = 1 − artanh z / z + z·artanh z,      K′(z) = artanh z·(1 + 1/z²) − 1/z
```

and `K′ ≥ 0` is exactly `z ≤ (1+z²)·artanh z`.  Monotonicity of `u·H′(u)` makes
the slice `r ↦ H(rc) − H(rd)` decreasing, hence the mixed difference of `H`
non-positive — which is `Δ_φ + δ·Δ_g ≤ 0`, i.e. STEP 1. -/

/-- Strict form of the pointwise fact. -/
theorem lt_one_add_sq_mul_artanh {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    z < (1 + z ^ 2) * artanh z := by
  have h := self_lt_artanh hz0 hz1
  nlinarith [sq_nonneg z, Real.artanh_pos (Set.mem_Ioo.mpr ⟨hz0, hz1⟩)]

/-- `K(z) = 1 − artanh z / z + z·artanh z`. -/
noncomputable def KStepFun (z : ℝ) : ℝ := 1 - artanh z / z + z * artanh z

lemma hasDerivAt_KStepFun {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt KStepFun (artanh z * (1 + 1 / z ^ 2) - 1 / z) z := by
  have h0 : (-1:ℝ) < z := by linarith
  have hne : z ≠ 0 := ne_of_gt hz0
  have hsq : (1:ℝ) - z ^ 2 ≠ 0 := by nlinarith
  have hA := hasDerivAt_artanh h0 hz1
  have h1 : HasDerivAt (fun x : ℝ => artanh x / x)
      ((1 / (1 - z ^ 2) * z - artanh z * 1) / z ^ 2) z :=
    hA.fun_div (hasDerivAt_id' (x := z)) hne
  have h2 : HasDerivAt (fun x : ℝ => x * artanh x)
      (1 * artanh z + z * (1 / (1 - z ^ 2))) z :=
    (hasDerivAt_id' (x := z)).fun_mul hA
  have h := (h1.const_sub 1).fun_add h2
  have heq : -((1 / (1 - z ^ 2) * z - artanh z * 1) / z ^ 2)
      + (1 * artanh z + z * (1 / (1 - z ^ 2)))
      = artanh z * (1 + 1 / z ^ 2) - 1 / z := by
    field_simp
    ring
  rw [heq] at h
  exact h

/-- **`K` is strictly increasing on `(0,1)`** — equivalent to
`z < (1+z²)·artanh z`. -/
theorem KStepFun_strictMonoOn : StrictMonoOn KStepFun (Ioo (0:ℝ) 1) := by
  refine strictMonoOn_Ioo_of_deriv_pos _
    (fun z => artanh z * (1 + 1 / z ^ 2) - 1 / z) ?_ ?_
  · exact fun z hz => hasDerivAt_KStepFun hz.1 hz.2
  · intro z hz
    have hz0 : 0 < z := hz.1
    have h := lt_one_add_sq_mul_artanh hz0 hz.2
    have hzz : (0:ℝ) < z ^ 2 := pow_pos hz0 2
    have key : artanh z * (1 + 1 / z ^ 2) - 1 / z
        = ((1 + z ^ 2) * artanh z - z) / z ^ 2 := by
      field_simp; ring
    rw [key]
    exact div_pos (by linarith) hzz

/-! ### STEP 1 completed: the mixed difference of `H` is negative -/

/-- `H(u) = fo(δu)/u + δ·f_e(δu)`; its mixed difference is `Δ_φ + δ·Δ_g`. -/
noncomputable def HStep (δ u : ℝ) : ℝ := phiOdd δ u + δ * fe (δ * u)

/-- Slice derivative of `H`: `d/dr H(rq) = δ·K(δrq)/r`. -/
lemma hasDerivAt_HStep_slice {δ q r : ℝ} (hδ0 : 0 < δ) (hq0 : 0 < q) (hr0 : 0 < r)
    (h1 : δ * (r * q) < 1) :
    HasDerivAt (fun x : ℝ => HStep δ (x * q)) (δ * KStepFun (δ * (r * q)) / r) r := by
  have hrq : (0:ℝ) < r * q := mul_pos hr0 hq0
  have hz0 : (0:ℝ) < δ * (r * q) := by positivity
  have hzn : (-1:ℝ) < δ * (r * q) := by linarith
  have hw := hasDerivAt_wFun_slice hδ0 hq0 hr0 h1
  have hP := hasDerivAt_fe_mul_slice (δ := δ) (q := q) (r := r) hzn h1
  have hphi : HasDerivAt (fun x : ℝ => phiOdd δ (x * q))
      (-((artanh (δ * (r * q)) - δ * (r * q)) / (r * q) ^ 2 * q)) r := by
    have hfun : (fun x : ℝ => phiOdd δ (x * q)) = fun x : ℝ => δ - wFun δ (x * q) := by
      funext x; rw [phiOdd, wFun]; ring
    rw [hfun]
    simpa using hw.const_sub δ
  have h := hphi.fun_add (hP.const_mul δ)
  have hne : δ * (r * q) ≠ 0 := ne_of_gt hz0
  have heq : -((artanh (δ * (r * q)) - δ * (r * q)) / (r * q) ^ 2 * q)
      + δ * (artanh (δ * (r * q)) * (δ * q))
      = δ * KStepFun (δ * (r * q)) / r := by
    rw [KStepFun]
    field_simp
    ring
  rw [heq] at h
  have hfun2 : (fun x : ℝ => phiOdd δ (x * q) + δ * fe (δ * (x * q)))
      = fun x : ℝ => HStep δ (x * q) := by funext x; rw [HStep]
  rwa [hfun2] at h

/-- The slice `r ↦ H(rd) − H(rc)` is strictly increasing for `c < d`. -/
theorem HStep_slice_strictMonoOn {δ c d : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hc0 : 0 < c) (hcd : c < d) (hd1 : d ≤ 1) :
    StrictMonoOn (fun r : ℝ => HStep δ (r * d) - HStep δ (r * c)) (Ioc (0:ℝ) 1) := by
  have hd0 : 0 < d := hc0.trans hcd
  have hrange : ∀ {r q : ℝ}, 0 < r → r ≤ 1 → 0 < q → q ≤ 1 → δ * (r * q) < 1 := by
    intro r q hr0 hr1 hqq0 hqq1
    have hle : r * q ≤ 1 := by nlinarith
    nlinarith [mul_pos hr0 hqq0]
  refine strictMonoOn_Ioc_of_deriv_pos _
    (fun r => δ * KStepFun (δ * (r * d)) / r - δ * KStepFun (δ * (r * c)) / r) ?_ ?_
  · intro r hr
    exact (hasDerivAt_HStep_slice hδ0 hd0 hr.1 (hrange hr.1 hr.2 hd0 hd1)).sub
      (hasDerivAt_HStep_slice hδ0 hc0 hr.1 (hrange hr.1 hr.2 hc0 (le_of_lt (hcd.trans_le hd1))))
  · intro r hr
    have hr0 : 0 < r := hr.1
    have hr1' : r ≤ 1 := le_of_lt hr.2
    have hmc : δ * (r * c) ∈ Ioo (0:ℝ) 1 :=
      ⟨by positivity, hrange hr.1 hr1' hc0 (le_of_lt (hcd.trans_le hd1))⟩
    have hmd : δ * (r * d) ∈ Ioo (0:ℝ) 1 := ⟨by positivity, hrange hr.1 hr1' hd0 hd1⟩
    have hlt : δ * (r * c) < δ * (r * d) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hcd hr0) hδ0
    have hK := KStepFun_strictMonoOn hmc hmd hlt
    have : 0 < δ * KStepFun (δ * (r * d)) - δ * KStepFun (δ * (r * c)) := by
      have := mul_lt_mul_of_pos_left hK hδ0
      linarith
    have heq : δ * KStepFun (δ * (r * d)) / r - δ * KStepFun (δ * (r * c)) / r
        = (δ * KStepFun (δ * (r * d)) - δ * KStepFun (δ * (r * c))) / r := by ring
    rw [heq]
    exact div_pos this hr0

/-- **STEP 1.**  The mixed difference of `H` is negative: `Δ_φ + δ·Δ_g < 0`. -/
theorem HStep_mixed_diff_neg {δ a b c d : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hb0 : 0 < b) (hba : b < a) (ha1 : a ≤ 1)
    (hc0 : 0 < c) (hcd : c < d) (hd1 : d ≤ 1) :
    HStep δ (a * c) - HStep δ (a * d) - HStep δ (b * c) + HStep δ (b * d) < 0 := by
  have h := HStep_slice_strictMonoOn hδ0 hδ1 hc0 hcd hd1
    (Set.mem_Ioc.mpr ⟨hb0, le_of_lt (hba.trans_le ha1)⟩)
    (Set.mem_Ioc.mpr ⟨hb0.trans hba, ha1⟩) hba
  simp only at h
  linarith

/-! ## **(S4), PROVED** -/

/-- **(S4).**  For opposite skews (`b < a`, `c < d`), the odd gain `Ω` is at most
the spread of the four corner values of `g`.

```
Ω ≤ λκδ·|Δ_g|            STEP 1  (HStep_mixed_diff_neg, from z < (1+z²)artanh z)
  ≤ min(w_ac,w_bd)·|Δ_g| STEP 3  (a·c·δ ≤ 1 and b·d·δ ≤ 1)
  ≤ gMax4 − gSum         STEP 2  (2×2 algebra)
```
-/
theorem omegaTwoPoint_le_spread {δ μ ν a b c d : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hb0 : 0 < b) (hba : b < a) (ha1 : a ≤ 1)
    (hc0 : 0 < c) (hcd : c < d) (hd1 : d ≤ 1) :
    OmegaTwoPoint δ a b c d ≤ gMax4 δ μ ν a b c d - gSum δ μ ν a b c d := by
  have ha0 : 0 < a := hb0.trans hba
  have hd0 : 0 < d := hc0.trans hcd
  have hab : (0:ℝ) < a + b := by linarith
  have hcd' : (0:ℝ) < c + d := by linarith
  set Δfe : ℝ := fe (δ * (a * c)) - fe (δ * (a * d)) - fe (δ * (b * c)) + fe (δ * (b * d))
    with hΔfe
  -- STEP 1 : Δ_φ + δ·Δfe < 0
  have hH := HStep_mixed_diff_neg hδ0 hδ1 hb0 hba ha1 hc0 hcd hd1
  have hsplit : HStep δ (a * c) - HStep δ (a * d) - HStep δ (b * c) + HStep δ (b * d)
      = (phiOdd δ (a * c) - phiOdd δ (a * d) - phiOdd δ (b * c) + phiOdd δ (b * d))
        + δ * Δfe := by
    simp only [HStep, hΔfe]; ring
  rw [hsplit] at hH
  -- Ω = λκ·Δ_φ
  have hΩ := omegaTwoPoint_eq_phiOdd (δ := δ) ha0 hb0 hc0 hd0
  have hlk : (0:ℝ) < (a * b / (a + b)) * (c * d / (c + d)) := by positivity
  have hstep1 : OmegaTwoPoint δ a b c d
      ≤ (a * b / (a + b)) * (c * d / (c + d)) * δ * (-Δfe) := by
    rw [hΩ]
    nlinarith [hlk, hH]
  -- Δfe < 0
  have hΔneg : Δfe < 0 := by
    rw [hΔfe]
    have := fe_mul_supermodular (δ := δ) (p₁ := b) (p₂ := a) (q₁ := c) (q₂ := d)
      hδ0 hδ1 hb0 hba ha1 hc0 hcd hd1
    linarith
  -- STEP 3 : λκδ ≤ min weight
  have hstep3 := lam_kap_mul_le_min_weight (δ := δ) ha0 ha1 hb0
    (le_of_lt (hba.trans_le ha1)) hc0 (le_of_lt (hcd.trans_le hd1)) hd0 hd1 hδ0
    (le_of_lt hδ1)
  have hmid : (a * b / (a + b)) * (c * d / (c + d)) * δ * (-Δfe)
      ≤ min (b * d / ((a + b) * (c + d))) (a * c / ((a + b) * (c + d))) * (-Δfe) :=
    mul_le_mul_of_nonneg_right hstep3 (by linarith)
  -- STEP 2 : spread bound
  have hstep2 := spread_ge_min_weight_mul (δ := δ) (μ := μ) (ν := ν) ha0 hb0 hc0 hd0
  have hmix : gSym δ μ ν a d + gSym δ μ ν b c - gSym δ μ ν a c - gSym δ μ ν b d = -Δfe := by
    have := gSym_mixed_diff_eq δ μ ν a b c d
    rw [hΔfe]; linarith
  rw [hmix] at hstep2
  linarith

/-- **The opposite-skew half of the conjecture.**  Combined with
`lagrTwoPoint_lt_of_same_skew`, every two-point configuration satisfies
`F ≤ J_sym`. -/
theorem lagrTwoPoint_le_of_opposite_skew {δ μ ν a b c d M : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hb0 : 0 < b) (hba : b < a) (ha1 : a ≤ 1)
    (hc0 : 0 < c) (hcd : c < d) (hd1 : d ≤ 1)
    (h1 : gSym δ μ ν a c ≤ M) (h2 : gSym δ μ ν a d ≤ M)
    (h3 : gSym δ μ ν b c ≤ M) (h4 : gSym δ μ ν b d ≤ M) :
    lagrTwoPoint δ μ ν a b c d ≤ M := by
  have ha0 : 0 < a := hb0.trans hba
  have hd0 : 0 < d := hc0.trans hcd
  have hab : a + b ≠ 0 := by positivity
  have hcd' : c + d ≠ 0 := by positivity
  exact lagrTwoPoint_le_of_omega_le_spread hab hcd' h1 h2 h3 h4
    (omegaTwoPoint_le_spread hδ0 hδ1 hb0 hba ha1 hc0 hcd hd1)

/-! ## The complete two-point result

`lagrTwoPoint`, `gSum` and `gMax4` are invariant under the simultaneous swap
`(a↔b, c↔d)`, so the four skew orderings reduce to two, and `a = b` or `c = d`
gives `Ω = 0`.  Hence **every** two-point configuration satisfies `F ≤ M` for any
bound `M` on the four corner values of `g` — in particular `M = J_sym`. -/

lemma lagrTwoPoint_swap (δ μ ν a b c d : ℝ) :
    lagrTwoPoint δ μ ν b a d c = lagrTwoPoint δ μ ν a b c d := by
  rw [lagrTwoPoint, lagrTwoPoint]; ring

/-- **Every two-point configuration satisfies `F ≤ M`.**  With `M = J_sym` this is
the two-point case of the conjecture. -/
theorem lagrTwoPoint_le_of_corner_bounds {δ μ ν a b c d M : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (h1 : gSym δ μ ν a c ≤ M) (h2 : gSym δ μ ν a d ≤ M)
    (h3 : gSym δ μ ν b c ≤ M) (h4 : gSym δ μ ν b d ≤ M) :
    lagrTwoPoint δ μ ν a b c d ≤ M := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · rcases lt_trichotomy c d with hcl | hce | hcg
    · rw [← lagrTwoPoint_swap]
      exact le_of_lt (lagrTwoPoint_lt_of_same_skew hδ0 hδ1 ha0 hlt hb1
        hc0 hcl hd1 h4 h3 h2 h1)
    · subst hce
      exact lagrTwoPoint_le_of_omega_nonpos (le_of_lt ha0) (le_of_lt hb0) (le_of_lt hc0)
        (le_of_lt hc0) (by linarith) (by linarith) h1 h2 h3 h4
        (le_of_eq (omegaTwoPoint_zero_of_snd_eq δ a b c))
    · rw [← lagrTwoPoint_swap]
      exact lagrTwoPoint_le_of_opposite_skew hδ0 hδ1 ha0 hlt hb1
        hd0 hcg hc1 h4 h3 h2 h1
  · subst heq
    exact lagrTwoPoint_le_of_omega_nonpos (le_of_lt ha0) (le_of_lt ha0) (le_of_lt hc0)
      (le_of_lt hd0) (by linarith) (by linarith) h1 h2 h3 h4
      (le_of_eq (omegaTwoPoint_zero_of_fst_eq δ a c d))
  · rcases lt_trichotomy c d with hcl | hce | hcg
    · exact lagrTwoPoint_le_of_opposite_skew hδ0 hδ1 hb0 hgt ha1
        hc0 hcl hd1 h1 h2 h3 h4
    · subst hce
      exact lagrTwoPoint_le_of_omega_nonpos (le_of_lt ha0) (le_of_lt hb0) (le_of_lt hc0)
        (le_of_lt hc0) (by linarith) (by linarith) h1 h2 h3 h4
        (le_of_eq (omegaTwoPoint_zero_of_snd_eq δ a b c))
    · exact le_of_lt (lagrTwoPoint_lt_of_same_skew hδ0 hδ1 hb0 hgt ha1
        hd0 hcg hc1 h1 h2 h3 h4)

/-! ## Boundary atoms: the closed box

An atom at `0` makes the corresponding two-point law degenerate (`U ⊥ X` or
`V ⊥ Y`) and kills the odd gain, so those faces reduce to `Ω = 0`.  Atoms at `1`
are already covered.  Together this gives the theorem on the **closed** box
`a,b,c,d ∈ [0,1]` (with the two-point laws non-degenerate, `a+b > 0`,
`c+d > 0`), for every `δ ∈ (0,1)`.  The endpoints `δ ∈ {0,1}` are the separately
settled cases `p = 1/2` and `p = 0`. -/

@[simp] theorem omegaTwoPoint_zero_fst_atom (δ b c d : ℝ) : OmegaTwoPoint δ 0 b c d = 0 := by
  rw [OmegaTwoPoint]; simp

@[simp] theorem omegaTwoPoint_zero_snd_atom (δ a c d : ℝ) : OmegaTwoPoint δ a 0 c d = 0 := by
  rw [OmegaTwoPoint]; simp

@[simp] theorem omegaTwoPoint_zero_thd_atom (δ a b d : ℝ) : OmegaTwoPoint δ a b 0 d = 0 := by
  rw [OmegaTwoPoint]; simp

@[simp] theorem omegaTwoPoint_zero_fth_atom (δ a b c : ℝ) : OmegaTwoPoint δ a b c 0 = 0 := by
  rw [OmegaTwoPoint]; simp

/-- **`F ≤ M` on the closed box.**  Atoms may sit at `0` or `1`; only
non-degeneracy of the two point laws (`a+b > 0`, `c+d > 0`) is required. -/
theorem lagrTwoPoint_le_of_corner_bounds_closed {δ μ ν a b c d M : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hab : 0 < a + b) (hcd : 0 < c + d)
    (h1 : gSym δ μ ν a c ≤ M) (h2 : gSym δ μ ν a d ≤ M)
    (h3 : gSym δ μ ν b c ≤ M) (h4 : gSym δ μ ν b d ≤ M) :
    lagrTwoPoint δ μ ν a b c d ≤ M := by
  rcases eq_or_lt_of_le ha0 with ha | ha0'
  · exact lagrTwoPoint_le_of_omega_nonpos ha0 hb0 hc0 hd0 hab hcd h1 h2 h3 h4
      (le_of_eq (by rw [← ha]; exact omegaTwoPoint_zero_fst_atom δ b c d))
  rcases eq_or_lt_of_le hb0 with hb | hb0'
  · exact lagrTwoPoint_le_of_omega_nonpos ha0 hb0 hc0 hd0 hab hcd h1 h2 h3 h4
      (le_of_eq (by rw [← hb]; exact omegaTwoPoint_zero_snd_atom δ a c d))
  rcases eq_or_lt_of_le hc0 with hc | hc0'
  · exact lagrTwoPoint_le_of_omega_nonpos ha0 hb0 hc0 hd0 hab hcd h1 h2 h3 h4
      (le_of_eq (by rw [← hc]; exact omegaTwoPoint_zero_thd_atom δ a b d))
  rcases eq_or_lt_of_le hd0 with hd | hd0'
  · exact lagrTwoPoint_le_of_omega_nonpos ha0 hb0 hc0 hd0 hab hcd h1 h2 h3 h4
      (le_of_eq (by rw [← hd]; exact omegaTwoPoint_zero_fth_atom δ a b c))
  exact lagrTwoPoint_le_of_corner_bounds hδ0 hδ1 ha0' ha1 hb0' hb1 hc0' hc1 hd0' hd1 h1 h2 h3 h4

end BSCAveraging
