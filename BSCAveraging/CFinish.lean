import BSCAveraging.BFinishV
import BSCAveraging.TwoAtom

/-! # `(C)`: the saddle argument, structurally

`NOTES.md` §7e′–§7e″.  `hessian_indefinite` already says the constrained Hessian
at the symmetric point is indefinite.  Turning that into "the BSC pair is not a
maximiser" needs a feasible curve along which the value strictly increases, and
the obstacle has always been that the rate-constant curve is defined implicitly.

**It can be avoided.**  Three observations, formalised here.

*1. Bilinearity splits the comparison.*  `V(μ,ν) − V(μ*,ν*) = A_U + A_V + Q` is
an exact identity, `A_U`, `A_V` one-sided and `Q` the bilinear cross term.

*2. Bitangency turns `A_U` into one-variable Taylor at fixed points.*  With
`H(x) = φ(x) − λf_e(x) − ℓ₁x − ℓ₀` — the slack, which vanishes to second order at
both atoms — mass one and mean zero give the exact decomposition

```
⟨φ, μ⟩ = ⟨H, μ⟩ + λ·R(μ) + ℓ₀                       (twoAtomL_decomp)
```

so `A_U = ⟨H,μ'⟩ + λ(R(μ') − Cu)`.  Since `H(x_u) = H′(x_u) = 0`, the first term
is `½ Σ w_u H″(x_u) δ_u² + o(δ²)` — **Taylor for a one-variable function at a
fixed point**, no curve differentiation.

*3. Feasibility needs no implicit function.*  Take the explicit polynomial curve
`x(ε) = x* + εd + ε²(e − ηg)` with `d` tangent (`∇R·d = 0`), `e` killing the
second-order rate drift, and `∇R·g > 0`.  Then `R(ε) − Cu = −η(∇R·g)ε² + o(ε²)`,
strictly feasible for small `ε > 0`, and the induced value loss `λ(R−Cu)` is
`O(η ε²)` — which the strict margin of `hessian_indefinite` absorbs once `η` is
small.  Only `∇R ≠ 0` is needed, and that is `Dfst_fe_pos` / `Dsnd_fe_neg`.

What is formalised below: the rate gradient's second component, the exact
decomposition, and the second-order positivity test. -/

namespace BSCAveraging

open BSCAveraging.KKT



/-- **The second-order test.**  `g(0) = g′(0) = 0` with `g″(0) > 0` forces `g`
strictly positive just to the right of `0`. -/
theorem pos_of_second_deriv_pos {g g' : ℝ → ℝ} {c : ℝ}
    (hg : ∀ᶠ x in nhds (0:ℝ), HasDerivAt g (g' x) x) (hg0 : g 0 = 0) (hg'0 : g' 0 = 0)
    (hg' : HasDerivAt g' c 0) (hc : 0 < c) :
    ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < g ε := by
  have hpos : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < g' ε := by
    have h := KKT.eventually_gt_of_deriv_pos hg' hc
    rw [hg'0] at h; exact h
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hpos
  obtain ⟨δ, hδ0, hδ⟩ := hpos
  rw [Metric.eventually_nhds_iff] at hg
  obtain ⟨δ', hδ'0, hδ'⟩ := hg
  have hmem : Set.Ioo (0:ℝ) (min δ δ') ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
    Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hmem, self_mem_nhdsWithin] with ε hε hε0
  have hd : ∀ x ∈ Set.Icc (0:ℝ) ε, HasDerivAt g (g' x) x := by
    intro x hx
    refine hδ' ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    exact lt_of_le_of_lt hx.2 (lt_of_lt_of_le hε.2 (min_le_right _ _))
  have hmono : StrictMonoOn g (Set.Icc 0 ε) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 ε)
      (fun x hx => ((hd x hx).continuousAt).continuousWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).deriv]
    refine hδ ?_ hx.1
    rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]
    exact lt_trans hx.2 (lt_of_lt_of_le hε.2 (min_le_left _ _))
  have := hmono (Set.left_mem_Icc.mpr (le_of_lt hε0)) (Set.right_mem_Icc.mpr (le_of_lt hε0)) hε0
  rw [hg0] at this
  exact this


/-! ### The diagonal half of the identification -/





/-! ### The slack Hessian *is* the Hessian entry -/





/-! ### The cross-term principle

`Q(ε) = ⟨Δφ_ε, δμ(ε)⟩` pairs two objects that both vanish at `ε = 0`, so `Q`
vanishes to second order and its second derivative is *twice the product of the
two first-order data*.  Splitting the pairing as

```
Q = (a₁−½)·Δφ_ε(x₁(ε)) + (a₂−½)·Δφ_ε(x₂(ε))
      + ½(Δφ_ε(x₁(ε)) − Δφ_ε(s)) + ½(Δφ_ε(x₂(ε)) − Δφ_ε(−s))
```

exhibits the first two summands as literal products of vanishing functions,
which `second_deriv_of_mul_vanishing` handles. -/


/-- Mirror of `pos_of_second_deriv_pos`, for feasibility: `g(0) = g′(0) = 0` with
`g″(0) < 0` forces `g < 0` just to the right of `0`. -/
theorem neg_of_second_deriv_neg {g g' : ℝ → ℝ} {c : ℝ}
    (hg : ∀ᶠ x in nhds (0:ℝ), HasDerivAt g (g' x) x) (hg0 : g 0 = 0) (hg'0 : g' 0 = 0)
    (hg' : HasDerivAt g' c 0) (hc : c < 0) :
    ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), g ε < 0 := by
  have hneg : ∀ᶠ x in nhds (0:ℝ), HasDerivAt (fun y => -g y) (-g' x) x := by
    filter_upwards [hg] with x hx using hx.neg
  have h := pos_of_second_deriv_pos hneg (by rw [hg0]; ring) (by rw [hg'0]; ring)
    (hg'.neg) (by linarith)
  filter_upwards [h] with ε hε
  linarith

/-! ### The assembly

With the value gain and the feasibility margin both vanishing to second order,
the strict signs of their second derivatives close the argument: there is a
feasible point with strictly larger value, contradicting maximality.  This is
the shape `(C)` finishes in. -/


/-- The quadratic form of the constrained Hessian is positive in the saddle
direction — the input `not_max_of_second_order` needs. -/
theorem hessian_form_pos {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t)
    (ht1 : t < 1) :
    0 < Core.Fpp s t * 1 ^ 2
      + 2 * Core.Fpq s t * (1 * (-(Core.Fpq s t) / Core.Fqq s t))
      + Core.Fqq s t * (-(Core.Fpq s t) / Core.Fqq s t) ^ 2 := by
  have h := Core.saddle_direction hs0 hs1 ht0 ht1
  have he : Core.Fpp s t * 1 ^ 2
      + 2 * Core.Fpq s t * (1 * (-(Core.Fpq s t) / Core.Fqq s t))
      + Core.Fqq s t * (-(Core.Fpq s t) / Core.Fqq s t) ^ 2
      = Core.Fpp s t + 2 * (-(Core.Fpq s t) / Core.Fqq s t) * Core.Fpq s t
        + (-(Core.Fpq s t) / Core.Fqq s t) ^ 2 * Core.Fqq s t := by ring
  rw [he]
  exact h

/-! ### The mixed-partial engine

Every summand of the cross term has the *same* shape: the weights `aᵢ(ε)bⱼ(ε)`
are a product of two affine functions, hence quadratic, and the atom product
`xᵢ(ε)yⱼ(ε)` is quadratic too.  So each of the sixteen terms is

```
(c₀ + c₁ε + c₂ε²) · f(g₀ + g₁ε + g₂ε²)
```

and one lemma differentiates all of them.  The second derivative at `0` is

```
2c₂·f(g₀) + 2c₁·f′(g₀)g₁ + c₀·(f″(g₀)g₁² + 2g₂·f′(g₀)) ,
```

whose `c₀ f″(g₀) g₁²` part is the genuinely mixed contribution. -/


lemma hasDerivAt_quad (a₀ a₁ a₂ ε : ℝ) :
    HasDerivAt (fun e : ℝ => a₀ + a₁ * e + a₂ * e ^ 2) (a₁ + 2 * a₂ * ε) ε := by
  have h := ((((hasDerivAt_id ε).const_mul a₁).const_add a₀).add
    ((hasDerivAt_pow 2 ε).const_mul a₂))
  refine KKT.hd_congr h ?_
  simp
  ring



/-! ### The instantiation

Applying `polyMul_second` to the four terms of the value and the two of each
rate, along the *linear* curve `xᵢ(ε) = ±s + εd₁`, `yⱼ(ε) = ±t + εd₂` with the
forced weights, gives (writing `x = st`)

```
V″(0)   = 2d₁d₂·F_pq + (t²d₁² + s²d₂²)·[1/(1−x²) − 2·artanh x/x]
R_U″(0) = d₁²·[1/(1−s²) − 2·artanh s/s] ,     R_V″(0) = d₂²·[…]
```

The ε²-correction of the curve contributes `2∇V·e = 2λ∇R·e` — because
`∇V = λ∇R` at a critical point — so the total second-order coefficient is
`V″ − λ_U R_U″ − λ_V R_V″`.  That is exactly the Hessian form: the `d₁²`
coefficients match because `λ_U·artanh(s)/s = t²·artanh(x)/x`, which is
`λ_U = t·artanh x/artanh s` with `x = st`. -/

/-- **The instantiation identity.**  The total second-order coefficient along the
corrected curve is the constrained Hessian form. -/
theorem total_second_order_eq {s t d₁ d₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1) (has : Real.artanh s ≠ 0) (hat : Real.artanh t ≠ 0) :
    (2 * d₁ * d₂ * Core.Fpq s t
        + (t ^ 2 * d₁ ^ 2 + s ^ 2 * d₂ ^ 2)
          * (1 / (1 - (s * t) ^ 2) - 2 * Real.artanh (s * t) / (s * t)))
      - (t * Real.artanh (s * t) / Real.artanh s)
        * (d₁ ^ 2 * (1 / (1 - s ^ 2) - 2 * Real.artanh s / s))
      - (s * Real.artanh (s * t) / Real.artanh t)
        * (d₂ ^ 2 * (1 / (1 - t ^ 2) - 2 * Real.artanh t / t))
      = Core.Fpp s t * d₁ ^ 2 + 2 * Core.Fpq s t * d₁ * d₂ + Core.Fqq s t * d₂ ^ 2 := by
  have hst : 0 < s * t := mul_pos hs0 ht0
  have hst1 : s * t < 1 := by nlinarith
  have h1 : (1:ℝ) - (s * t) ^ 2 ≠ 0 := by nlinarith
  have h2 : (1:ℝ) - s ^ 2 ≠ 0 := by nlinarith
  have h3 : (1:ℝ) - t ^ 2 ≠ 0 := by nlinarith
  rw [Core.Fpp, Core.Fqq, Core.Fpq]
  field_simp
  ring



/-! ### The general engine

The pure translation is **not** always feasible: the rate's second derivative
along it is `d₁²·[1/(1−s²) − 2·artanh s/s]`, which changes sign at bias
`s ≈ 0.7964` (`numerics`).  Above that the translation *increases* the rate, so
the `ε²`-correction of the curve is genuinely needed — and it makes the forced
weights a *ratio* of quadratics and the atom products quartic, so
`polyMul_second` no longer applies.

`genMul_second` is the same computation with no shape assumption at all: for
`T(ε) = c(ε)·f(g(ε))`,

```
T″(0) = c″(0)f(g₀) + 2c′(0)f′(g₀)g′(0) + c(0)·(f″(g₀)g′(0)² + f′(g₀)g″(0)) .
```
-/

/-- **The general product-composition engine.**  Second derivative of
`c(ε)·f(g(ε))` at `0`, with no shape assumption on `c` or `g`. -/
theorem genMul_second {f f' f'' c c' g g' : ℝ → ℝ} {c₂ g₂ : ℝ}
    (hf : HasDerivAt f (f' (g 0)) (g 0)) (hf' : HasDerivAt f' (f'' (g 0)) (g 0))
    (hc : HasDerivAt c (c' 0) 0) (hc' : HasDerivAt c' c₂ 0)
    (hg : HasDerivAt g (g' 0) 0) (hg' : HasDerivAt g' g₂ 0) :
    HasDerivAt (fun ε => c' ε * f (g ε) + c ε * (f' (g ε) * g' ε))
      (c₂ * f (g 0) + 2 * (c' 0 * (f' (g 0) * g' 0))
        + c 0 * (f'' (g 0) * g' 0 ^ 2 + f' (g 0) * g₂)) 0 := by
  have hfg : HasDerivAt (fun ε => f (g ε)) (f' (g 0) * g' 0) 0 := by
    have h := hf.comp 0 hg
    simpa [Function.comp_def] using h
  have hf'g : HasDerivAt (fun ε => f' (g ε)) (f'' (g 0) * g' 0) 0 := by
    have h := hf'.comp 0 hg
    simpa [Function.comp_def] using h
  have hT1 : HasDerivAt (fun ε => c' ε * f (g ε))
      (c₂ * f (g 0) + c' 0 * (f' (g 0) * g' 0)) 0 := hc'.mul hfg
  have hT2 : HasDerivAt (fun ε => c ε * (f' (g ε) * g' ε))
      (c' 0 * (f' (g 0) * g' 0) + c 0 * (f'' (g 0) * g' 0 * g' 0 + f' (g 0) * g₂)) 0 := by
    have hin := hf'g.mul hg'
    exact hc.mul hin
  refine KKT.hd_congr (hT1.add hT2) ?_
  ring

/-- The first derivative that `genMul_second` differentiates. -/
theorem hasDerivAt_genMul {f f' c c' g g' : ℝ → ℝ} {ε : ℝ}
    (hf : HasDerivAt f (f' (g ε)) (g ε)) (hc : HasDerivAt c (c' ε) ε)
    (hg : HasDerivAt g (g' ε) ε) :
    HasDerivAt (fun e => c e * f (g e)) (c' ε * f (g ε) + c ε * (f' (g ε) * g' ε)) ε := by
  have hfg : HasDerivAt (fun e => f (g e)) (f' (g ε) * g' ε) ε := by
    have h := hf.comp ε hg
    simpa [Function.comp_def] using h
  exact hc.mul hfg


/-! ### The corrected curve's weights

`§7e⁸`'s "two regimes" reading was wrong.  Below the crossover the translation
*is* feasible, but then `R″ < 0` and the gain's second derivative is
`V″ = form + λ_U R_U″ + λ_V R_V″ < form` — wasting rate budget costs value, and
the sign is indeterminate.  The `η`-corrected curve is needed in **both**
regimes and works uniformly:

```
gain″ = form − 2λη(∇R·g) > 0   for small η,
R − Cu = −η(∇R·g)ε² + o(ε²) < 0 .
```

On the corrected curve `xᵢ(ε) = ±s + εd₁ + ε²eᵢ` with `e₁ ≠ e₂`, the forced
weight `w₁ = −x₂/(x₁−x₂)` is a genuine quotient, so its Taylor data comes from
`quot_second`.  With `D = x₁−x₂ = 2s + ε²(e₁−e₂)` and `N = −x₂`:

```
w₁(0) = ½ ,   w₁′(0) = −d₁/(2s) ,   w₁″(0) = −(e₁+e₂)/(2s) .
```
-/

/-- **Second derivative of a quotient.**  `(N/D)″(0)`, via the derivative
function `(N′D − ND′)/D²`. -/
theorem quot_second {N D N' D' : ℝ → ℝ} {N₂ D₂ : ℝ} (hD0 : D 0 ≠ 0)
    (hN : HasDerivAt N (N' 0) 0) (hD : HasDerivAt D (D' 0) 0)
    (hN' : HasDerivAt N' N₂ 0) (hD' : HasDerivAt D' D₂ 0) :
    HasDerivAt (fun ε => (N' ε * D ε - N ε * D' ε) / (D ε) ^ 2)
      (((N₂ * D 0 - N 0 * D₂) * D 0 - 2 * D' 0 * (N' 0 * D 0 - N 0 * D' 0)) / (D 0) ^ 3)
      0 := by
  have hu : HasDerivAt (fun ε => N' ε * D ε - N ε * D' ε) (N₂ * D 0 - N 0 * D₂) 0 := by
    have h := (hN'.mul hD).sub (hN.mul hD')
    refine KKT.hd_congr h ?_
    ring
  have hd2 : HasDerivAt (fun ε => (D ε) ^ 2) (2 * D 0 * D' 0) 0 := by
    have h := hD.pow 2
    refine KKT.hd_congr h ?_
    ring
  have h := hu.div hd2 (pow_ne_zero 2 hD0)
  refine KKT.hd_congr h ?_
  field_simp


/-! ### The corrected curve's rate

Instantiating `genMul_second` twice with `c = wᵢ` (Taylor data from
`weight_taylor`), `g = xᵢ`, `f = f_e` gives the rate's second derivative along the
corrected curve.  The `f_e(±s)` terms cancel because `w₁″ = −w₂″` (mass is
preserved) and `f_e` is even, leaving

```
R_U″(0) = d²·[1/(1−s²) − 2·artanh s/s] + artanh(s)·(e₁ − e₂)
        = R″_lin + 2·(∇R·e) ,
```

since `∇R = (artanh s/2, −artanh s/2)` at the symmetric point
(`Dfst_fe_pos`/`Dsnd_fe_neg` evaluated there).  **This is what the correction
buys**: `e₁ − e₂` moves the rate's second derivative by an arbitrary amount, so
it can be driven to `−2η(∇R·g) < 0`. -/

lemma artanh_odd {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.artanh (-s) = -Real.artanh s := by
  rw [Real.artanh_eq_half_log ⟨by linarith, by linarith⟩,
    Real.artanh_eq_half_log ⟨by linarith, le_of_lt hs1⟩,
    show (1 + -s) / (1 - -s) = ((1 + s) / (1 - s))⁻¹ by
      rw [show (1:ℝ) + -s = 1 - s by ring, show (1:ℝ) - -s = 1 + s by ring, inv_div],
    Real.log_inv]
  ring

lemma fe_even (s : ℝ) : fe (-s) = fe s := by
  simp only [fe]
  rw [show (1:ℝ) + -s = 1 - s by ring, show (1:ℝ) - -s = 1 + s by ring]
  ring

/-- **The corrected curve's rate coefficient.**  The `f_e` terms cancel; the
correction enters only through `e₁ − e₂`. -/
theorem rate_corrected_coeff {s d e₁ e₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ((-(e₁ + e₂) / (2 * s)) * fe s + 2 * ((-d / (2 * s)) * (Real.artanh s * d))
        + (1 / 2 : ℝ) * ((1 / (1 - s ^ 2)) * d ^ 2 + Real.artanh s * (2 * e₁)))
      + (((e₁ + e₂) / (2 * s)) * fe (-s) + 2 * ((d / (2 * s)) * (Real.artanh (-s) * d))
        + (1 / 2 : ℝ) * ((1 / (1 - s ^ 2)) * d ^ 2 + Real.artanh (-s) * (2 * e₂)))
      = d ^ 2 * (1 / (1 - s ^ 2) - 2 * Real.artanh s / s)
        + Real.artanh s * (e₁ - e₂) := by
  have h2 : (1:ℝ) - s ^ 2 ≠ 0 := by nlinarith
  rw [artanh_odd hs0 hs1, fe_even]
  field_simp
  ring


/-- **The correction achieves any target.**  Given the rate gradient is nonzero
(here `artanh s ≠ 0`), the second-order rate drift can be set to any value. -/
theorem exists_correction {s target : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ e₁ e₂ : ℝ, Real.artanh s * (e₁ - e₂) = target := by
  have hpos : 0 < Real.artanh s := Real.artanh_pos ⟨hs0, hs1⟩
  exact ⟨target / Real.artanh s, 0, by field_simp; ring⟩

/-! ### The corrected curve's value

In `V″(0) = Σᵢⱼ [(wᵢρⱼ)″f(gᵢⱼ⁰) + 2(wᵢρⱼ)′f′(gᵢⱼ⁰)gᵢⱼ′ + (wᵢρⱼ)(f″gᵢⱼ′² + f′gᵢⱼ″)]`
the correction (the `e`, `f` data) enters in two places, and the first cancels:
`w₁″ = −w₂″` and `ρ₁″ = −ρ₂″` by mass preservation, so the `f(gᵢⱼ⁰)` terms sum to
zero.  What survives telescopes:

```
correction = ½·Σᵢⱼ f′(gᵢⱼ⁰)(eᵢyⱼ⁰ + fⱼxᵢ⁰)
           = ½·(f′(x) − f′(−x))·[t(e₁−e₂) + s(f₁−f₂)]
           = artanh(x)·[t(e₁−e₂) + s(f₁−f₂)] ,        x = st,
```

which is exactly `2λ_U(∇R_U·e) + 2λ_V(∇R_V·f)`, since `λ_U·artanh s = t·artanh x`
and `λ_V·artanh t = s·artanh x`.  So

```
V″(0) = V″_lin + λ_U·A + λ_V·B ,    A = artanh(s)(e₁−e₂), B = artanh(t)(f₁−f₂),
R_U″(0) = R″_lin,U + A ,            R_V″(0) = R″_lin,V + B .
```
-/



/-! ### Choosing the corrections -/

/-- **The corrections exist.**  With the Hessian form positive, the second-order
rate drift can be made strictly negative on both sides while the value gain stays
strictly positive. -/
theorem exists_good_corrections {Vlin RlinU RlinV lamU lamV form : ℝ}
    (hlamU : 0 ≤ lamU) (hlamV : 0 ≤ lamV)
    (hform : Vlin - lamU * RlinU - lamV * RlinV = form) (hpos : 0 < form) :
    ∃ A B : ℝ, RlinU + A < 0 ∧ RlinV + B < 0 ∧ 0 < Vlin + lamU * A + lamV * B := by
  set η := form / (2 * (lamU + lamV + 1)) with hη
  have hden : (0:ℝ) < 2 * (lamU + lamV + 1) := by linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  refine ⟨-RlinU - η, -RlinV - η, by linarith, by linarith, ?_⟩
  have hkey : Vlin + lamU * (-RlinU - η) + lamV * (-RlinV - η)
      = form - (lamU + lamV) * η := by rw [← hform]; ring
  rw [hkey]
  have hbound : (lamU + lamV) * η ≤ form / 2 := by
    rw [hη, mul_div_assoc']
    rw [div_le_div_iff₀ hden (by norm_num)]
    nlinarith [hpos, hlamU, hlamV]
  linarith

/-! ### The `Chan` layer

The second-order machinery talks about explicit functions of the four atom
parameters.  These two lemmas are the bridge: the rate and the value of a pair
of atom-built channels *are* those functions. -/

/-- The atom value of an atom-built `V`-side channel. -/
theorem atomValue_chanOfAtomsV {c d : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hd0 : d < 0)
    (hd1 : -1 < d) (z : ℝ) :
    atomValue (chanOfAtomsV hc0 hc1 hd0 hd1) z
      = (-d / (c - d)) * fFun (z * c) + (c / (c - d)) * fFun (z * d) := by
  obtain ⟨m0, m1⟩ := marg₂_chanOfAtomsV hc0 hc1 hd0 hd1
  obtain ⟨e0, e1⟩ := biasOfSnd_chanOfAtomsV hc0 hc1 hd0 hd1
  have hD : (0:ℝ) < c - d := by linarith
  rw [atomValue, m0, m1, e0, e1, wOf]
  have h1 : (1:ℝ) - -d / (c - d) = c / (c - d) := by field_simp; ring
  rw [h1]

/-- **The value of a pair of atom-built channels**, as the explicit four-term
function of the atoms. -/
theorem value_pair_atoms {a b c d : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0)
    (hb1 : -1 < b) (hc0 : 0 < c) (hc1 : c < 1) (hd0 : d < 0) (hd1 : -1 < d) :
    mutualInfo (jointUV 0 (chanOfAtoms ha0 ha1 hb0 hb1) (chanOfAtomsV hc0 hc1 hd0 hd1))
      = (-b / (a - b)) * ((-d / (c - d)) * fFun (a * c) + (c / (c - d)) * fFun (a * d))
        + (a / (a - b)) * ((-d / (c - d)) * fFun (b * c) + (c / (c - d)) * fFun (b * d)) := by
  obtain ⟨eU1, eU0⟩ := biasOf_chanOfAtoms ha0 ha1 hb0 hb1
  obtain ⟨eV0, eV1⟩ := biasOfSnd_chanOfAtomsV hc0 hc1 hd0 hd1
  have hker : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ))
      * biasOf (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) u
      * biasOfSnd (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) v := by
    intro u v
    have hs : |biasOf (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) u| ≤ 1 := by
      cases u
      · rw [eU0, abs_le]; constructor <;> linarith
      · rw [eU1, abs_le]; constructor <;> linarith
    have ht : |biasOfSnd (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) v| ≤ 1 := by
      cases v
      · rw [eV0, abs_le]; constructor <;> linarith
      · rw [eV1, abs_le]; constructor <;> linarith
    have hbnd : |(1 - 2 * (0:ℝ))
        * biasOf (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) u
        * biasOfSnd (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) v| ≤ 1 := by
      rw [abs_mul, abs_mul, show |(1 - 2 * (0:ℝ))| = 1 by norm_num, one_mul]
      calc |biasOf (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) u|
            * |biasOfSnd (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1)) v|
          ≤ 1 * 1 := mul_le_mul hs ht (abs_nonneg _) zero_le_one
        _ = 1 := by ring
    linarith [(abs_le.mp hbnd).1]
  have hne : biasOf (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) true
      ≠ biasOf (jointUX (chanOfAtoms ha0 ha1 hb0 hb1)) false := by
    rw [eU1, eU0]; intro h; linarith
  rw [mutualInfo_jointUV_eq_twoAtomL (marg₁_chanOfAtoms_pos ha0 ha1 hb0 hb1)
    (marg₂_chanOfAtomsV_pos hc0 hc1 hd0 hd1) hker hne, eU1, eU0, twoAtomL,
    atomValue_chanOfAtomsV hc0 hc1 hd0 hd1, atomValue_chanOfAtomsV hc0 hc1 hd0 hd1]

/-- **The rate of an atom-built channel**, as the explicit two-term function. -/
theorem rate_pair_atoms {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0) (hb1 : -1 < b) :
    mutualInfo (jointUX (chanOfAtoms ha0 ha1 hb0 hb1))
      = (-b / (a - b)) * fe a + (a / (a - b)) * fe b := by
  rw [rate_chanOfAtoms ha0 ha1 hb0 hb1, twoAtomL]

theorem rateV_pair_atoms {c d : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hd0 : d < 0) (hd1 : -1 < d) :
    mutualInfo (jointYV (chanOfAtomsV hc0 hc1 hd0 hd1))
      = (-d / (c - d)) * fe c + (c / (c - d)) * fe d := by
  rw [rateV_chanOfAtomsV hc0 hc1 hd0 hd1, twoAtomL]

/-- **Maximality, in the form the second-order principle consumes.**  If the two
atom-built rates are within budget, the atom-built value cannot beat the
maximiser's.  This is exactly the `hmax` hypothesis of
`not_max_of_second_order`, with `gain = value − V*` and `feas = rate − C`. -/
theorem curve_max_bound {Cu Cv : ℝ} {cL cR : Chan} (hmx : IsMaxPairC Cu Cv cL cR)
    {a b c d : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0) (hb1 : -1 < b)
    (hc0 : 0 < c) (hc1 : c < 1) (hd0 : d < 0) (hd1 : -1 < d)
    (hRU : (-b / (a - b)) * fe a + (a / (a - b)) * fe b ≤ Cu)
    (hRV : (-d / (c - d)) * fe c + (c / (c - d)) * fe d ≤ Cv) :
    (-b / (a - b)) * ((-d / (c - d)) * fFun (a * c) + (c / (c - d)) * fFun (a * d))
        + (a / (a - b)) * ((-d / (c - d)) * fFun (b * c) + (c / (c - d)) * fFun (b * d))
      ≤ mutualInfo (jointUV 0 cL cR) := by
  have hfeas : FeasibleC Cu Cv (chanOfAtoms ha0 ha1 hb0 hb1) (chanOfAtomsV hc0 hc1 hd0 hd1) := by
    constructor
    · rw [rate_pair_atoms ha0 ha1 hb0 hb1]; exact hRU
    · rw [rateV_pair_atoms hc0 hc1 hd0 hd1]; exact hRV
  have h := hmx.2 _ _ hfeas
  rwa [value_pair_atoms ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1] at h

/-! ### The curve, concretely

The bottom layer of the `HasDerivAt` chains: the corrected atoms and the forced
weights, as explicit functions of `ε`, with their first and second derivative
data. -/

/-- A corrected atom `p + εd + ε²e`. -/
noncomputable def atomC (p d e ε : ℝ) : ℝ := p + d * ε + e * ε ^ 2

/-- Its derivative. -/
noncomputable def atomC' (d e ε : ℝ) : ℝ := d + 2 * e * ε

lemma hasDerivAt_atomC (p d e ε : ℝ) :
    HasDerivAt (atomC p d e) (atomC' d e ε) ε := hasDerivAt_quad p d e ε

lemma hasDerivAt_atomC' (d e : ℝ) : HasDerivAt (atomC' d e) (2 * e) 0 := by
  have := ((hasDerivAt_id (0:ℝ)).const_mul (2 * e)).const_add d
  exact KKT.hd_congr this (by ring)

@[simp] lemma atomC_zero (p d e : ℝ) : atomC p d e 0 = p := by simp [atomC]

@[simp] lemma atomC'_zero (d e : ℝ) : atomC' d e 0 = d := by simp [atomC']



/-- The gap stays away from zero near `ε = 0`. -/
lemma gap_ne_zero_eventually {s d e₁ e₂ : ℝ} (hs : 0 < s) :
    ∀ᶠ ε in nhds (0:ℝ), atomC s d e₁ ε - atomC (-s) d e₂ ε ≠ 0 := by
  have hcont : Continuous (fun ε : ℝ => atomC s d e₁ ε - atomC (-s) d e₂ ε) := by
    unfold atomC; fun_prop
  have h0 : (fun ε : ℝ => atomC s d e₁ ε - atomC (-s) d e₂ ε) 0 = 2 * s := by
    simp [atomC]; ring
  have := (hcont.tendsto 0).eventually (eventually_gt_nhds (by rw [h0]; linarith :
    (0:ℝ) < (fun ε : ℝ => atomC s d e₁ ε - atomC (-s) d e₂ ε) 0))
  filter_upwards [this] with ε hε using ne_of_gt hε

/-- The forced weight of the positive atom along the corrected curve. -/
noncomputable def wC (s d e₁ e₂ ε : ℝ) : ℝ :=
  -(atomC (-s) d e₂ ε) / (atomC s d e₁ ε - atomC (-s) d e₂ ε)

/-- Its derivative. -/
noncomputable def wC' (s d e₁ e₂ ε : ℝ) : ℝ :=
  ((-(atomC' d e₂ ε)) * (atomC s d e₁ ε - atomC (-s) d e₂ ε)
      - (-(atomC (-s) d e₂ ε)) * (atomC' d e₁ ε - atomC' d e₂ ε))
    / (atomC s d e₁ ε - atomC (-s) d e₂ ε) ^ 2

lemma hasDerivAt_wC {s d e₁ e₂ ε : ℝ}
    (hne : atomC s d e₁ ε - atomC (-s) d e₂ ε ≠ 0) :
    HasDerivAt (wC s d e₁ e₂) (wC' s d e₁ e₂ ε) ε := by
  have hN : HasDerivAt (fun e => -(atomC (-s) d e₂ e)) (-(atomC' d e₂ ε)) ε :=
    (hasDerivAt_atomC (-s) d e₂ ε).neg
  have hD : HasDerivAt (fun e => atomC s d e₁ e - atomC (-s) d e₂ e)
      (atomC' d e₁ ε - atomC' d e₂ ε) ε :=
    (hasDerivAt_atomC s d e₁ ε).sub (hasDerivAt_atomC (-s) d e₂ ε)
  exact hN.div hD hne

/-- The weight's second derivative at `0`: `−(e₁+e₂)/(2s)`. -/
lemma hasDerivAt_wC' {s d e₁ e₂ : ℝ} (hs : 0 < s) :
    HasDerivAt (wC' s d e₁ e₂) (-(e₁ + e₂) / (2 * s)) 0 := by
  have hD0 : (fun e => atomC s d e₁ e - atomC (-s) d e₂ e) 0 = 2 * s := by
    simp [atomC]; ring
  have hDne : (fun e => atomC s d e₁ e - atomC (-s) d e₂ e) 0 ≠ 0 := by
    rw [hD0]; positivity
  have hN : HasDerivAt (fun e => -(atomC (-s) d e₂ e))
      ((fun e => -(atomC' d e₂ e)) 0) 0 := (hasDerivAt_atomC (-s) d e₂ 0).neg
  have hD : HasDerivAt (fun e => atomC s d e₁ e - atomC (-s) d e₂ e)
      ((fun e => atomC' d e₁ e - atomC' d e₂ e) 0) 0 :=
    (hasDerivAt_atomC s d e₁ 0).sub (hasDerivAt_atomC (-s) d e₂ 0)
  have hN' : HasDerivAt (fun e => -(atomC' d e₂ e)) (-(2 * e₂)) 0 :=
    (hasDerivAt_atomC' d e₂).neg
  have hD' : HasDerivAt (fun e => atomC' d e₁ e - atomC' d e₂ e) (2 * e₁ - 2 * e₂) 0 :=
    (hasDerivAt_atomC' d e₁).sub (hasDerivAt_atomC' d e₂)
  have h := quot_second hDne hN hD hN' hD'
  refine KKT.hd_congr h ?_
  simp only [atomC_zero, atomC'_zero]
  have h2s : (2:ℝ) * s ≠ 0 := by positivity
  field_simp
  ring

/-! ### The rate chain, composed

`R_U(ε) = w(ε)·f_e(xₐ(ε)) + (1−w(ε))·f_e(x_b(ε))`.  Two applications of
`hasDerivAt_genMul` give its derivative; two of `genMul_second` give the second
derivative at `0`, which `rate_corrected_coeff` identifies. -/

@[simp] lemma wC_zero {s d e₁ e₂ : ℝ} (hs : 0 < s) : wC s d e₁ e₂ 0 = 1 / 2 := by
  have h : (2:ℝ) * s ≠ 0 := by positivity
  simp only [wC, atomC]
  norm_num
  field_simp
  ring

@[simp] lemma wC'_zero {s d e₁ e₂ : ℝ} (hs : 0 < s) :
    wC' s d e₁ e₂ 0 = -d / (2 * s) := by
  have h : (2:ℝ) * s ≠ 0 := by positivity
  simp only [wC', atomC, atomC']
  norm_num
  field_simp
  ring

/-- The atoms stay inside `(−1,1)` near `ε = 0`. -/
lemma atom_mem_eventually {p d e : ℝ} (hp : |p| < 1) :
    ∀ᶠ ε in nhds (0:ℝ), |atomC p d e ε| < 1 := by
  have hcont : Continuous (fun ε : ℝ => |atomC p d e ε|) := by
    unfold atomC; fun_prop
  exact (hcont.tendsto 0).eventually (eventually_lt_nhds (by simpa [atomC] using hp))

/-- The rate along the corrected curve. -/
noncomputable def rateCurve (s d e₁ e₂ ε : ℝ) : ℝ :=
  wC s d e₁ e₂ ε * fe (atomC s d e₁ ε)
    + (1 - wC s d e₁ e₂ ε) * fe (atomC (-s) d e₂ ε)

/-- Its derivative. -/
noncomputable def rateCurve' (s d e₁ e₂ ε : ℝ) : ℝ :=
  (wC' s d e₁ e₂ ε * fe (atomC s d e₁ ε)
      + wC s d e₁ e₂ ε * (Real.artanh (atomC s d e₁ ε) * atomC' d e₁ ε))
    + ((-(wC' s d e₁ e₂ ε)) * fe (atomC (-s) d e₂ ε)
      + (1 - wC s d e₁ e₂ ε) * (Real.artanh (atomC (-s) d e₂ ε) * atomC' d e₂ ε))

theorem hasDerivAt_rateCurve {s d e₁ e₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ᶠ ε in nhds (0:ℝ), HasDerivAt (rateCurve s d e₁ e₂) (rateCurve' s d e₁ e₂ ε) ε := by
  have habs : |s| < 1 := by rw [abs_lt]; constructor <;> linarith
  have habs' : |(-s)| < 1 := by rw [abs_lt]; constructor <;> linarith
  filter_upwards [gap_ne_zero_eventually (d := d) (e₁ := e₁) (e₂ := e₂) hs0,
    atom_mem_eventually (p := s) (d := d) (e := e₁) habs,
    atom_mem_eventually (p := -s) (d := d) (e := e₂) habs'] with ε hgap h1 h2
  have hw := hasDerivAt_wC hgap
  have hPa : HasDerivAt fe (Real.artanh (atomC s d e₁ ε)) (atomC s d e₁ ε) :=
    hasDerivAt_fe' (by linarith [(abs_lt.mp h1).1]) (abs_lt.mp h1).2
  have hPb : HasDerivAt fe (Real.artanh (atomC (-s) d e₂ ε)) (atomC (-s) d e₂ ε) :=
    hasDerivAt_fe' (by linarith [(abs_lt.mp h2).1]) (abs_lt.mp h2).2
  have t1 := hasDerivAt_genMul (f' := Real.artanh) hPa hw (hasDerivAt_atomC s d e₁ ε)
  have t2 := hasDerivAt_genMul (f' := Real.artanh) hPb
    (c' := fun e => -(wC' s d e₁ e₂ e)) (hw.const_sub 1) (hasDerivAt_atomC (-s) d e₂ ε)
  exact t1.add t2

/-- **The rate's second derivative along the corrected curve.** -/
theorem hasDerivAt_rateCurve' {s d e₁ e₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt (rateCurve' s d e₁ e₂)
      (d ^ 2 * (1 / (1 - s ^ 2) - 2 * Real.artanh s / s) + Real.artanh s * (e₁ - e₂)) 0 := by
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hPa : HasDerivAt fe (Real.artanh ((atomC s d e₁) 0)) ((atomC s d e₁) 0) := by
    simpa using hasDerivAt_fe' (by linarith : (-1:ℝ) < s) hs1
  have hPb : HasDerivAt fe (Real.artanh ((atomC (-s) d e₂) 0)) ((atomC (-s) d e₂) 0) := by
    simpa using hasDerivAt_fe' (by linarith : (-1:ℝ) < -s) (by linarith : -s < 1)
  have hAa : HasDerivAt Real.artanh ((fun z => 1 / (1 - z ^ 2)) ((atomC s d e₁) 0))
      ((atomC s d e₁) 0) := by
    simpa using hasDerivAt_artanh (by linarith : (-1:ℝ) < s) hs1
  have hAb : HasDerivAt Real.artanh ((fun z => 1 / (1 - z ^ 2)) ((atomC (-s) d e₂) 0))
      ((atomC (-s) d e₂) 0) := by
    simpa using hasDerivAt_artanh (by linarith : (-1:ℝ) < -s) (by linarith : -s < 1)
  have hgap0 : atomC s d e₁ 0 - atomC (-s) d e₂ 0 ≠ 0 := by simp [atomC]; positivity
  have hw := hasDerivAt_wC (s := s) (d := d) (e₁ := e₁) (e₂ := e₂) hgap0
  have hw' := hasDerivAt_wC' (s := s) (d := d) (e₁ := e₁) (e₂ := e₂) hs0
  have c1 := genMul_second (f' := Real.artanh) (f'' := fun z => 1 / (1 - z ^ 2))
    hPa hAa hw hw' (hasDerivAt_atomC s d e₁ 0) (hasDerivAt_atomC' d e₁)
  have c2 := genMul_second (f' := Real.artanh) (f'' := fun z => 1 / (1 - z ^ 2))
    hPb hAb (c' := fun e => -(wC' s d e₁ e₂ e)) (hw.const_sub 1) (hw'.neg)
    (hasDerivAt_atomC (-s) d e₂ 0) (hasDerivAt_atomC' d e₂)
  have hsum := c1.add c2
  refine KKT.hd_congr hsum ?_
  simp only [atomC_zero, atomC'_zero, wC_zero hs0, wC'_zero hs0]
  rw [← rate_corrected_coeff (s := s) (d := d) (e₁ := e₁) (e₂ := e₂) hs0 hs1]
  have h2 : (1:ℝ) - s ^ 2 ≠ 0 := by nlinarith
  have h2s : (2:ℝ) * s ≠ 0 := by positivity
  field_simp
  ring

/-! ### The value chain

Each of the four value terms is `c·f(g)` with `c = wᵢρⱼ` and `g = xᵢyⱼ` both
*products*, so the data fed to `genMul_second` comes from product rules. -/

/-- Product rule, first derivative. -/
lemma hasDerivAt_mul2 {A A' B B' : ℝ → ℝ} {ε : ℝ}
    (hA : HasDerivAt A (A' ε) ε) (hB : HasDerivAt B (B' ε) ε) :
    HasDerivAt (fun e => A e * B e) (A' ε * B ε + A ε * B' ε) ε := hA.mul hB

/-- Product rule, second derivative at `0`. -/
lemma hasDerivAt_mul2' {A A' B B' : ℝ → ℝ} {A₂ B₂ : ℝ}
    (hA : HasDerivAt A (A' 0) 0) (hB : HasDerivAt B (B' 0) 0)
    (hA' : HasDerivAt A' A₂ 0) (hB' : HasDerivAt B' B₂ 0) :
    HasDerivAt (fun e => A' e * B e + A e * B' e)
      (A₂ * B 0 + 2 * (A' 0 * B' 0) + A 0 * B₂) 0 := by
  have h1 : HasDerivAt (fun e => A' e * B e) (A₂ * B 0 + A' 0 * B' 0) 0 := hA'.mul hB
  have h2 : HasDerivAt (fun e => A e * B' e) (A' 0 * B' 0 + A 0 * B₂) 0 := hA.mul hB'
  refine KKT.hd_congr (h1.add h2) ?_
  ring

/-- One value term. -/
noncomputable def valTerm (c g : ℝ → ℝ) (ε : ℝ) : ℝ := c ε * fFun (g ε)

/-- Its derivative. -/
noncomputable def valTerm' (c c' g g' : ℝ → ℝ) (ε : ℝ) : ℝ :=
  c' ε * fFun (g ε) + c ε * ((Real.log (1 + g ε) + 1) * g' ε)

theorem hasDerivAt_valTerm {c c' g g' : ℝ → ℝ} {ε : ℝ} (hg : 0 < 1 + g ε)
    (hc : HasDerivAt c (c' ε) ε) (hgd : HasDerivAt g (g' ε) ε) :
    HasDerivAt (valTerm c g) (valTerm' c c' g g' ε) ε :=
  hasDerivAt_genMul (f' := fun z => Real.log (1 + z) + 1) (hasDerivAt_fFun hg) hc hgd

/-- **One value term's second derivative at `0`.** -/
theorem hasDerivAt_valTerm' {c c' g g' : ℝ → ℝ} {c₂ g₂ : ℝ} (hg : 0 < 1 + g 0)
    (hc : HasDerivAt c (c' 0) 0) (hc' : HasDerivAt c' c₂ 0)
    (hgd : HasDerivAt g (g' 0) 0) (hg' : HasDerivAt g' g₂ 0) :
    HasDerivAt (valTerm' c c' g g')
      (c₂ * fFun (g 0) + 2 * (c' 0 * ((Real.log (1 + g 0) + 1) * g' 0))
        + c 0 * ((1 / (1 + g 0)) * g' 0 ^ 2 + (Real.log (1 + g 0) + 1) * g₂)) 0 := by
  have hf' : HasDerivAt (fun z => Real.log (1 + z) + 1)
      ((fun z => 1 / (1 + z)) (g 0)) (g 0) := by
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 (g 0) := by
      simpa using (hasDerivAt_id (g 0)).const_add 1
    have h2 : HasDerivAt (fun z : ℝ => Real.log (1 + z)) (1 / (1 + g 0)) (g 0) := by
      have := h1.log (ne_of_gt hg)
      simpa using this
    simpa using h2.add_const 1
  exact genMul_second (f' := fun z => Real.log (1 + z) + 1) (f'' := fun z => 1 / (1 + z))
    (hasDerivAt_fFun hg) hf' hc hc' hgd hg'

/-! ### The four terms' data

For the term `(i,j)` the weight is `wᵢρⱼ` and the argument is `xᵢyⱼ`, so at `ε=0`

```
c(0) = ¼ ,  c′(0) = ½(wᵢ′ + ρⱼ′) ,  c₂ = wᵢ″ρⱼ + 2wᵢ′ρⱼ′ + wᵢρⱼ″ ,
g(0) = xᵢ⁰yⱼ⁰ , g′(0) = d₁yⱼ⁰ + xᵢ⁰d₂ , g₂ = 2eᵢyⱼ⁰ + 2d₁d₂ + 2xᵢ⁰fⱼ ,
```

all supplied by `hasDerivAt_mul2` / `hasDerivAt_mul2'` from `hasDerivAt_wC`,
`hasDerivAt_wC'`, `hasDerivAt_atomC`, `hasDerivAt_atomC'`.  Summing the four
`hasDerivAt_valTerm'` coefficients and matching against
`value_four_term_sum` closes the value chain. -/

/-- The atom product's second derivative datum. -/
lemma hasDerivAt_atomProd' (p q d₁ d₂ e f : ℝ) :
    HasDerivAt (fun e' => atomC' d₁ e e' * atomC q d₂ f e'
        + atomC p d₁ e e' * atomC' d₂ f e')
      (2 * e * q + 2 * (d₁ * d₂) + p * (2 * f)) 0 := by
  have h := hasDerivAt_mul2' (A := atomC p d₁ e) (A' := atomC' d₁ e)
    (B := atomC q d₂ f) (B' := atomC' d₂ f)
    (hasDerivAt_atomC p d₁ e 0) (hasDerivAt_atomC q d₂ f 0)
    (hasDerivAt_atomC' d₁ e) (hasDerivAt_atomC' d₂ f)
  refine KKT.hd_congr h ?_
  simp only [atomC_zero, atomC'_zero]

/-! ### The four-term sum -/

lemma hasDerivAt_sum4 {F₁ F₂ F₃ F₄ G₁ G₂ G₃ G₄ : ℝ → ℝ} {ε : ℝ}
    (h₁ : HasDerivAt F₁ (G₁ ε) ε) (h₂ : HasDerivAt F₂ (G₂ ε) ε)
    (h₃ : HasDerivAt F₃ (G₃ ε) ε) (h₄ : HasDerivAt F₄ (G₄ ε) ε) :
    HasDerivAt (fun e => F₁ e + F₂ e + F₃ e + F₄ e)
      (G₁ ε + G₂ ε + G₃ ε + G₄ ε) ε := ((h₁.add h₂).add h₃).add h₄

lemma hasDerivAt_sum4' {G₁ G₂ G₃ G₄ : ℝ → ℝ} {c₁ c₂ c₃ c₄ : ℝ}
    (h₁ : HasDerivAt G₁ c₁ 0) (h₂ : HasDerivAt G₂ c₂ 0)
    (h₃ : HasDerivAt G₃ c₃ 0) (h₄ : HasDerivAt G₄ c₄ 0) :
    HasDerivAt (fun e => G₁ e + G₂ e + G₃ e + G₄ e) (c₁ + c₂ + c₃ + c₄) 0 :=
  ((h₁.add h₂).add h₃).add h₄

/-- **The four-term sum.**  Adding the four `hasDerivAt_valTerm'` coefficients
with the curve's data gives the value's second derivative in closed form: the
linear part plus the `artanh(st)` correction. -/
theorem value_four_term_sum {s t d₁ d₂ e₁ e₂ f₁ f₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1) :
    ((-(e₁+e₂)/(4*s) + d₁*d₂/(2*s*t) - (f₁+f₂)/(4*t)) * fFun (s*t) + 2 * ((-d₁/(4*s) - d₂/(4*t)) * ((Real.log (1 + s*t) + 1) * (d₁*t + s*d₂)))
        + (1/4 : ℝ) * ((1/(1 + s*t)) * (d₁*t + s*d₂)^2 + (Real.log (1 + s*t) + 1) * (2*e₁*t + 2*(d₁*d₂) + 2*(s*f₁))))
      + ((-(e₁+e₂)/(4*s) - d₁*d₂/(2*s*t) + (f₁+f₂)/(4*t)) * fFun (-(s*t)) + 2 * ((-d₁/(4*s) + d₂/(4*t)) * ((Real.log (1 - s*t) + 1) * (-(d₁*t) + s*d₂)))
        + (1/4 : ℝ) * ((1/(1 - s*t)) * (-(d₁*t) + s*d₂)^2 + (Real.log (1 - s*t) + 1) * (-(2*e₁*t) + 2*(d₁*d₂) + 2*(s*f₂))))
      + (((e₁+e₂)/(4*s) - d₁*d₂/(2*s*t) - (f₁+f₂)/(4*t)) * fFun (-(s*t)) + 2 * ((d₁/(4*s) - d₂/(4*t)) * ((Real.log (1 - s*t) + 1) * (d₁*t - s*d₂)))
        + (1/4 : ℝ) * ((1/(1 - s*t)) * (d₁*t - s*d₂)^2 + (Real.log (1 - s*t) + 1) * (2*e₂*t + 2*(d₁*d₂) - 2*(s*f₁))))
      + (((e₁+e₂)/(4*s) + d₁*d₂/(2*s*t) + (f₁+f₂)/(4*t)) * fFun (s*t) + 2 * ((d₁/(4*s) + d₂/(4*t)) * ((Real.log (1 + s*t) + 1) * (-(d₁*t) - s*d₂)))
        + (1/4 : ℝ) * ((1/(1 + s*t)) * (-(d₁*t) - s*d₂)^2 + (Real.log (1 + s*t) + 1) * (-(2*e₂*t) + 2*(d₁*d₂) - 2*(s*f₂))))
      = 2 * d₁ * d₂ * Core.Fpq s t
        + (t ^ 2 * d₁ ^ 2 + s ^ 2 * d₂ ^ 2)
          * (1 / (1 - (s * t) ^ 2) - 2 * Real.artanh (s * t) / (s * t))
        + Real.artanh (s * t) * (t * (e₁ - e₂) + s * (f₁ - f₂)) := by
  have hst : 0 < s * t := mul_pos hs0 ht0
  have hst1 : s * t < 1 := by nlinarith
  have hp : (0:ℝ) < 1 + s * t := by linarith
  have hm : (0:ℝ) < 1 - s * t := by linarith
  have hA : Real.artanh (s * t)
      = (Real.log (1 + s * t) - Real.log (1 - s * t)) / 2 := by
    rw [Real.artanh_eq_half_log ⟨by linarith, le_of_lt hst1⟩,
      Real.log_div (ne_of_gt hp) (ne_of_gt hm)]
    ring
  have h1 : (1:ℝ) - (s * t) ^ 2 ≠ 0 := by nlinarith
  have h1' : (1:ℝ) - s ^ 2 * t ^ 2 ≠ 0 := by nlinarith
  rw [Core.Fpq, hA, fFun, fFun]
  have hneg : (1:ℝ) + -(s * t) = 1 - s * t := by ring
  rw [hneg]
  field_simp
  ring

/-! ### The value curve, assembled -/

/-- `1 + xᵢyⱼ > 0` near `ε = 0`. -/
lemma one_add_prod_pos_eventually {p q d₁ d₂ e f : ℝ} (h : |p * q| < 1) :
    ∀ᶠ ε in nhds (0:ℝ), 0 < 1 + atomC p d₁ e ε * atomC q d₂ f ε := by
  have hcont : Continuous (fun ε : ℝ => 1 + atomC p d₁ e ε * atomC q d₂ f ε) := by
    unfold atomC; fun_prop
  refine (hcont.tendsto 0).eventually (eventually_gt_nhds ?_)
  simp only [atomC]
  norm_num
  linarith [(abs_lt.mp h).1]

/-- The value along the corrected curve. -/
noncomputable def valueCurve (s t d₁ d₂ e₁ e₂ f₁ f₂ ε : ℝ) : ℝ :=
  valTerm (fun e => wC s d₁ e₁ e₂ e * wC t d₂ f₁ f₂ e)
      (fun e => atomC s d₁ e₁ e * atomC t d₂ f₁ e) ε
    + valTerm (fun e => wC s d₁ e₁ e₂ e * (1 - wC t d₂ f₁ f₂ e))
      (fun e => atomC s d₁ e₁ e * atomC (-t) d₂ f₂ e) ε
    + valTerm (fun e => (1 - wC s d₁ e₁ e₂ e) * wC t d₂ f₁ f₂ e)
      (fun e => atomC (-s) d₁ e₂ e * atomC t d₂ f₁ e) ε
    + valTerm (fun e => (1 - wC s d₁ e₁ e₂ e) * (1 - wC t d₂ f₁ f₂ e))
      (fun e => atomC (-s) d₁ e₂ e * atomC (-t) d₂ f₂ e) ε

/-- Its derivative. -/
noncomputable def valueCurve' (s t d₁ d₂ e₁ e₂ f₁ f₂ ε : ℝ) : ℝ :=
  valTerm' (fun e => wC s d₁ e₁ e₂ e * wC t d₂ f₁ f₂ e)
      (fun e => wC' s d₁ e₁ e₂ e * wC t d₂ f₁ f₂ e + wC s d₁ e₁ e₂ e * wC' t d₂ f₁ f₂ e)
      (fun e => atomC s d₁ e₁ e * atomC t d₂ f₁ e)
      (fun e => atomC' d₁ e₁ e * atomC t d₂ f₁ e + atomC s d₁ e₁ e * atomC' d₂ f₁ e) ε
    + valTerm' (fun e => wC s d₁ e₁ e₂ e * (1 - wC t d₂ f₁ f₂ e))
      (fun e => wC' s d₁ e₁ e₂ e * (1 - wC t d₂ f₁ f₂ e)
        + wC s d₁ e₁ e₂ e * (-(wC' t d₂ f₁ f₂ e)))
      (fun e => atomC s d₁ e₁ e * atomC (-t) d₂ f₂ e)
      (fun e => atomC' d₁ e₁ e * atomC (-t) d₂ f₂ e + atomC s d₁ e₁ e * atomC' d₂ f₂ e) ε
    + valTerm' (fun e => (1 - wC s d₁ e₁ e₂ e) * wC t d₂ f₁ f₂ e)
      (fun e => (-(wC' s d₁ e₁ e₂ e)) * wC t d₂ f₁ f₂ e
        + (1 - wC s d₁ e₁ e₂ e) * wC' t d₂ f₁ f₂ e)
      (fun e => atomC (-s) d₁ e₂ e * atomC t d₂ f₁ e)
      (fun e => atomC' d₁ e₂ e * atomC t d₂ f₁ e + atomC (-s) d₁ e₂ e * atomC' d₂ f₁ e) ε
    + valTerm' (fun e => (1 - wC s d₁ e₁ e₂ e) * (1 - wC t d₂ f₁ f₂ e))
      (fun e => (-(wC' s d₁ e₁ e₂ e)) * (1 - wC t d₂ f₁ f₂ e)
        + (1 - wC s d₁ e₁ e₂ e) * (-(wC' t d₂ f₁ f₂ e)))
      (fun e => atomC (-s) d₁ e₂ e * atomC (-t) d₂ f₂ e)
      (fun e => atomC' d₁ e₂ e * atomC (-t) d₂ f₂ e
        + atomC (-s) d₁ e₂ e * atomC' d₂ f₂ e) ε

theorem hasDerivAt_valueCurve {s t d₁ d₂ e₁ e₂ f₁ f₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ᶠ ε in nhds (0:ℝ),
      HasDerivAt (valueCurve s t d₁ d₂ e₁ e₂ f₁ f₂)
        (valueCurve' s t d₁ d₂ e₁ e₂ f₁ f₂ ε) ε := by
  have hA : |s * t| < 1 := by rw [abs_lt]; constructor <;> nlinarith
  have hB : |s * (-t)| < 1 := by rw [abs_lt]; constructor <;> nlinarith
  have hCc : |(-s) * t| < 1 := by rw [abs_lt]; constructor <;> nlinarith
  have hD : |(-s) * (-t)| < 1 := by rw [abs_lt]; constructor <;> nlinarith
  filter_upwards [gap_ne_zero_eventually (d := d₁) (e₁ := e₁) (e₂ := e₂) hs0,
    gap_ne_zero_eventually (d := d₂) (e₁ := f₁) (e₂ := f₂) ht0,
    one_add_prod_pos_eventually (p := s) (q := t) (d₁ := d₁) (d₂ := d₂) (e := e₁) (f := f₁) hA,
    one_add_prod_pos_eventually (p := s) (q := -t) (d₁ := d₁) (d₂ := d₂) (e := e₁) (f := f₂) hB,
    one_add_prod_pos_eventually (p := -s) (q := t) (d₁ := d₁) (d₂ := d₂) (e := e₂) (f := f₁) hCc,
    one_add_prod_pos_eventually (p := -s) (q := -t) (d₁ := d₁) (d₂ := d₂) (e := e₂) (f := f₂) hD]
    with ε hgU hgV h11 h12 h21 h22
  have hwU := hasDerivAt_wC hgU
  have hwV := hasDerivAt_wC hgV
  refine hasDerivAt_sum4 ?_ ?_ ?_ ?_
  · exact hasDerivAt_valTerm h11 (hasDerivAt_mul2 hwU hwV)
      (hasDerivAt_mul2 (hasDerivAt_atomC s d₁ e₁ ε) (hasDerivAt_atomC t d₂ f₁ ε))
  · exact hasDerivAt_valTerm h12
      (hasDerivAt_mul2 (B' := fun e => -(wC' t d₂ f₁ f₂ e)) hwU (hwV.const_sub 1))
      (hasDerivAt_mul2 (hasDerivAt_atomC s d₁ e₁ ε) (hasDerivAt_atomC (-t) d₂ f₂ ε))
  · exact hasDerivAt_valTerm h21
      (hasDerivAt_mul2 (A' := fun e => -(wC' s d₁ e₁ e₂ e)) (hwU.const_sub 1) hwV)
      (hasDerivAt_mul2 (hasDerivAt_atomC (-s) d₁ e₂ ε) (hasDerivAt_atomC t d₂ f₁ ε))
  · exact hasDerivAt_valTerm h22
      (hasDerivAt_mul2 (A' := fun e => -(wC' s d₁ e₁ e₂ e))
        (B' := fun e => -(wC' t d₂ f₁ f₂ e)) (hwU.const_sub 1) (hwV.const_sub 1))
      (hasDerivAt_mul2 (hasDerivAt_atomC (-s) d₁ e₂ ε) (hasDerivAt_atomC (-t) d₂ f₂ ε))

/-! ### The final chaining -/

/-- **The two-constraint non-maximality principle.** -/
theorem not_max_of_second_order2 {gain gain' fU fU' fV fV' : ℝ → ℝ} {c cU cV : ℝ}
    (hg : ∀ᶠ x in nhds (0:ℝ), HasDerivAt gain (gain' x) x) (hg0 : gain 0 = 0)
    (hg'0 : gain' 0 = 0) (hg' : HasDerivAt gain' c 0) (hc : 0 < c)
    (hU : ∀ᶠ x in nhds (0:ℝ), HasDerivAt fU (fU' x) x) (hU0 : fU 0 = 0)
    (hU'0 : fU' 0 = 0) (hU' : HasDerivAt fU' cU 0) (hcU : cU < 0)
    (hV : ∀ᶠ x in nhds (0:ℝ), HasDerivAt fV (fV' x) x) (hV0 : fV 0 = 0)
    (hV'0 : fV' 0 = 0) (hV' : HasDerivAt fV' cV 0) (hcV : cV < 0)
    (hmax : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), fU ε ≤ 0 → fV ε ≤ 0 → gain ε ≤ 0) :
    False := by
  have h1 := pos_of_second_deriv_pos hg hg0 hg'0 hg' hc
  have h2 := neg_of_second_deriv_neg hU hU0 hU'0 hU' hcU
  have h3 := neg_of_second_deriv_neg hV hV0 hV'0 hV' hcV
  obtain ⟨ε, ⟨⟨hε1, hε2⟩, hε3⟩, hε4⟩ := (((h1.and h2).and h3).and hmax).exists
  exact absurd (hε4 (le_of_lt hε2) (le_of_lt hε3)) (not_le.mpr hε1)

/-- The rate is stationary at the symmetric point. -/
theorem rateCurve'_zero {s d e₁ e₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    rateCurve' s d e₁ e₂ 0 = 0 := by
  have h2s : (2:ℝ) * s ≠ 0 := by positivity
  simp only [rateCurve', atomC_zero, atomC'_zero, wC_zero hs0, wC'_zero hs0]
  rw [fe_even, artanh_odd hs0 hs1]
  field_simp
  ring

/-- The value is stationary at the symmetric point. -/
theorem valueCurve'_zero {s t d₁ d₂ e₁ e₂ f₁ f₂ : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) :
    valueCurve' s t d₁ d₂ e₁ e₂ f₁ f₂ 0 = 0 := by
  have h2s : (2:ℝ) * s ≠ 0 := by positivity
  have h2t : (2:ℝ) * t ≠ 0 := by positivity
  simp only [valueCurve', valTerm', atomC_zero, atomC'_zero, wC_zero hs0, wC_zero ht0,
    wC'_zero hs0, wC'_zero ht0]
  rw [show s * -t = -(s * t) by ring, show -s * t = -(s * t) by ring,
    show -s * -t = s * t by ring]
  field_simp
  ring

/-- The rate at the symmetric point is the BSC rate. -/
theorem rateCurve_zero {s d e₁ e₂ : ℝ} (hs0 : 0 < s) :
    rateCurve s d e₁ e₂ 0 = fe s := by
  simp only [rateCurve, atomC_zero, wC_zero hs0]
  rw [fe_even]
  ring

/-- The value at the symmetric point is the BSC value. -/
theorem valueCurve_zero {s t d₁ d₂ e₁ e₂ f₁ f₂ : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) :
    valueCurve s t d₁ d₂ e₁ e₂ f₁ f₂ 0
      = (1 / 2 : ℝ) * (fFun (s * t) + fFun (-(s * t))) := by
  simp only [valueCurve, valTerm, atomC_zero, wC_zero hs0, wC_zero ht0]
  rw [show s * -t = -(s * t) by ring, show -s * t = -(s * t) by ring,
    show -s * -t = s * t by ring]
  ring

/-! ### Identifying the curves with the `pair_atoms` expressions -/

theorem rateCurve_eq {s d e₁ e₂ ε : ℝ}
    (hgap : atomC s d e₁ ε - atomC (-s) d e₂ ε ≠ 0) :
    rateCurve s d e₁ e₂ ε
      = (-(atomC (-s) d e₂ ε) / (atomC s d e₁ ε - atomC (-s) d e₂ ε))
          * fe (atomC s d e₁ ε)
        + (atomC s d e₁ ε / (atomC s d e₁ ε - atomC (-s) d e₂ ε))
          * fe (atomC (-s) d e₂ ε) := by
  simp only [rateCurve, wC]
  field_simp
  ring

theorem valueCurve_eq {s t d₁ d₂ e₁ e₂ f₁ f₂ ε : ℝ}
    (hgU : atomC s d₁ e₁ ε - atomC (-s) d₁ e₂ ε ≠ 0)
    (hgV : atomC t d₂ f₁ ε - atomC (-t) d₂ f₂ ε ≠ 0) :
    valueCurve s t d₁ d₂ e₁ e₂ f₁ f₂ ε
      = (-(atomC (-s) d₁ e₂ ε) / (atomC s d₁ e₁ ε - atomC (-s) d₁ e₂ ε))
          * ((-(atomC (-t) d₂ f₂ ε) / (atomC t d₂ f₁ ε - atomC (-t) d₂ f₂ ε))
              * fFun (atomC s d₁ e₁ ε * atomC t d₂ f₁ ε)
            + (atomC t d₂ f₁ ε / (atomC t d₂ f₁ ε - atomC (-t) d₂ f₂ ε))
              * fFun (atomC s d₁ e₁ ε * atomC (-t) d₂ f₂ ε))
        + (atomC s d₁ e₁ ε / (atomC s d₁ e₁ ε - atomC (-s) d₁ e₂ ε))
          * ((-(atomC (-t) d₂ f₂ ε) / (atomC t d₂ f₁ ε - atomC (-t) d₂ f₂ ε))
              * fFun (atomC (-s) d₁ e₂ ε * atomC t d₂ f₁ ε)
            + (atomC t d₂ f₁ ε / (atomC t d₂ f₁ ε - atomC (-t) d₂ f₂ ε))
              * fFun (atomC (-s) d₁ e₂ ε * atomC (-t) d₂ f₂ ε)) := by
  simp only [valueCurve, valTerm, wC]
  field_simp
  ring

/-! ### The value curve's second derivative -/

theorem hasDerivAt_valueCurve' {s t d₁ d₂ e₁ e₂ f₁ f₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (valueCurve' s t d₁ d₂ e₁ e₂ f₁ f₂)
      (2 * d₁ * d₂ * Core.Fpq s t
        + (t ^ 2 * d₁ ^ 2 + s ^ 2 * d₂ ^ 2)
          * (1 / (1 - (s * t) ^ 2) - 2 * Real.artanh (s * t) / (s * t))
        + Real.artanh (s * t) * (t * (e₁ - e₂) + s * (f₁ - f₂))) 0 := by
  have hst : 0 < s * t := mul_pos hs0 ht0
  have hst1 : s * t < 1 := by nlinarith
  have hgU : atomC s d₁ e₁ 0 - atomC (-s) d₁ e₂ 0 ≠ 0 := by simp [atomC]; positivity
  have hgV : atomC t d₂ f₁ 0 - atomC (-t) d₂ f₂ 0 ≠ 0 := by simp [atomC]; positivity
  have hwU := hasDerivAt_wC hgU
  have hwV := hasDerivAt_wC hgV
  have hwU2 := hasDerivAt_wC' (s := s) (d := d₁) (e₁ := e₁) (e₂ := e₂) hs0
  have hwV2 := hasDerivAt_wC' (s := t) (d := d₂) (e₁ := f₁) (e₂ := f₂) ht0
  have hp11 : (0:ℝ) < 1 + (fun e => atomC s d₁ e₁ e * atomC t d₂ f₁ e) 0 := by
    simp [atomC]; linarith
  have hp12 : (0:ℝ) < 1 + (fun e => atomC s d₁ e₁ e * atomC (-t) d₂ f₂ e) 0 := by
    simp [atomC]; nlinarith
  have hp21 : (0:ℝ) < 1 + (fun e => atomC (-s) d₁ e₂ e * atomC t d₂ f₁ e) 0 := by
    simp [atomC]; nlinarith
  have hp22 : (0:ℝ) < 1 + (fun e => atomC (-s) d₁ e₂ e * atomC (-t) d₂ f₂ e) 0 := by
    simp [atomC]; nlinarith
  have T1 := hasDerivAt_valTerm' hp11 (hasDerivAt_mul2 hwU hwV)
    (hasDerivAt_mul2' hwU hwV hwU2 hwV2)
    (hasDerivAt_mul2 (hasDerivAt_atomC s d₁ e₁ 0) (hasDerivAt_atomC t d₂ f₁ 0))
    (hasDerivAt_atomProd' s t d₁ d₂ e₁ f₁)
  have T2 := hasDerivAt_valTerm' hp12
    (hasDerivAt_mul2 (B' := fun e => -(wC' t d₂ f₁ f₂ e)) hwU (hwV.const_sub 1))
    (hasDerivAt_mul2' (B' := fun e => -(wC' t d₂ f₁ f₂ e)) hwU (hwV.const_sub 1) hwU2 hwV2.neg)
    (hasDerivAt_mul2 (hasDerivAt_atomC s d₁ e₁ 0) (hasDerivAt_atomC (-t) d₂ f₂ 0))
    (hasDerivAt_atomProd' s (-t) d₁ d₂ e₁ f₂)
  have T3 := hasDerivAt_valTerm' hp21
    (hasDerivAt_mul2 (A' := fun e => -(wC' s d₁ e₁ e₂ e)) (hwU.const_sub 1) hwV)
    (hasDerivAt_mul2' (A' := fun e => -(wC' s d₁ e₁ e₂ e)) (hwU.const_sub 1) hwV hwU2.neg hwV2)
    (hasDerivAt_mul2 (hasDerivAt_atomC (-s) d₁ e₂ 0) (hasDerivAt_atomC t d₂ f₁ 0))
    (hasDerivAt_atomProd' (-s) t d₁ d₂ e₂ f₁)
  have T4 := hasDerivAt_valTerm' hp22
    (hasDerivAt_mul2 (A' := fun e => -(wC' s d₁ e₁ e₂ e))
      (B' := fun e => -(wC' t d₂ f₁ f₂ e)) (hwU.const_sub 1) (hwV.const_sub 1))
    (hasDerivAt_mul2' (A' := fun e => -(wC' s d₁ e₁ e₂ e))
      (B' := fun e => -(wC' t d₂ f₁ f₂ e)) (hwU.const_sub 1) (hwV.const_sub 1)
      hwU2.neg hwV2.neg)
    (hasDerivAt_mul2 (hasDerivAt_atomC (-s) d₁ e₂ 0) (hasDerivAt_atomC (-t) d₂ f₂ 0))
    (hasDerivAt_atomProd' (-s) (-t) d₁ d₂ e₂ f₂)
  refine KKT.hd_congr (hasDerivAt_sum4' T1 T2 T3 T4) ?_
  simp only [atomC_zero, atomC'_zero, wC_zero hs0, wC_zero ht0, wC'_zero hs0, wC'_zero ht0]
  rw [show s * -t = -(s * t) by ring, show -s * t = -(s * t) by ring,
    show -s * -t = s * t by ring, show (1:ℝ) + -(s * t) = 1 - s * t by ring]
  linear_combination value_four_term_sum (s := s) (t := t) (d₁ := d₁) (d₂ := d₂)
    (e₁ := e₁) (e₂ := e₂) (f₁ := f₁) (f₂ := f₂) hs0 hs1 ht0 ht1

/-! ### The contradiction, chained

`gain ε = V(ε) − V*` and `feas ε = R(ε) − R(0)` on each side.  Both vanish at
`0` with vanishing first derivative (§7e¹⁷), their second derivatives are the
closed forms of §7e¹³ and §7e¹⁶, and `curve_max_bound` supplies maximality.  So
`not_max_of_second_order2` applies as soon as the second-derivative signs are
right — which `exists_good_corrections` arranges. -/

/-- **The contradiction.**  A symmetric pair with the stated second-order signs
cannot be a maximiser. -/
theorem curve_contradiction {s t d₁ d₂ e₁ e₂ f₁ f₂ Vstar : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hV0 : Vstar = (1 / 2 : ℝ) * (fFun (s * t) + fFun (-(s * t))))
    (hgainpos : 0 < 2 * d₁ * d₂ * Core.Fpq s t
        + (t ^ 2 * d₁ ^ 2 + s ^ 2 * d₂ ^ 2)
          * (1 / (1 - (s * t) ^ 2) - 2 * Real.artanh (s * t) / (s * t))
        + Real.artanh (s * t) * (t * (e₁ - e₂) + s * (f₁ - f₂)))
    (hUneg : d₁ ^ 2 * (1 / (1 - s ^ 2) - 2 * Real.artanh s / s)
        + Real.artanh s * (e₁ - e₂) < 0)
    (hVneg : d₂ ^ 2 * (1 / (1 - t ^ 2) - 2 * Real.artanh t / t)
        + Real.artanh t * (f₁ - f₂) < 0)
    (hmax : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      rateCurve s d₁ e₁ e₂ ε - rateCurve s d₁ e₁ e₂ 0 ≤ 0 →
      rateCurve t d₂ f₁ f₂ ε - rateCurve t d₂ f₁ f₂ 0 ≤ 0 →
      valueCurve s t d₁ d₂ e₁ e₂ f₁ f₂ ε - Vstar ≤ 0) : False := by
  refine not_max_of_second_order2
    (gain := fun ε => valueCurve s t d₁ d₂ e₁ e₂ f₁ f₂ ε - Vstar)
    (gain' := valueCurve' s t d₁ d₂ e₁ e₂ f₁ f₂)
    (fU := fun ε => rateCurve s d₁ e₁ e₂ ε - rateCurve s d₁ e₁ e₂ 0)
    (fU' := rateCurve' s d₁ e₁ e₂)
    (fV := fun ε => rateCurve t d₂ f₁ f₂ ε - rateCurve t d₂ f₁ f₂ 0)
    (fV' := rateCurve' t d₂ f₁ f₂)
    ?_ ?_ (valueCurve'_zero hs0 ht0) (hasDerivAt_valueCurve' hs0 hs1 ht0 ht1) hgainpos
    ?_ (by ring) (rateCurve'_zero hs0 hs1) (hasDerivAt_rateCurve' hs0 hs1) hUneg
    ?_ (by ring) (rateCurve'_zero ht0 ht1) (hasDerivAt_rateCurve' ht0 ht1) hVneg hmax
  · filter_upwards [hasDerivAt_valueCurve hs0 hs1 ht0 ht1] with ε hε using hε.sub_const Vstar
  · rw [hV0, valueCurve_zero hs0 ht0]; ring
  · filter_upwards [hasDerivAt_rateCurve (e₁ := e₁) (e₂ := e₂) hs0 hs1] with ε hε
      using hε.sub_const _
  · filter_upwards [hasDerivAt_rateCurve (e₁ := f₁) (e₂ := f₂) ht0 ht1] with ε hε
      using hε.sub_const _

/-! ### Producing the corrections -/

/-- **The corrections exist for the curve.**  With the Hessian form positive,
there are `e₁,e₂,f₁,f₂` making both rate drifts strictly negative and the value
gain strictly positive. -/
theorem exists_curve_corrections {s t d₁ d₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hform : 0 < Core.Fpp s t * d₁ ^ 2 + 2 * Core.Fpq s t * d₁ * d₂
      + Core.Fqq s t * d₂ ^ 2) :
    ∃ e₁ e₂ f₁ f₂ : ℝ,
      (d₁ ^ 2 * (1 / (1 - s ^ 2) - 2 * Real.artanh s / s)
          + Real.artanh s * (e₁ - e₂) < 0)
        ∧ (d₂ ^ 2 * (1 / (1 - t ^ 2) - 2 * Real.artanh t / t)
          + Real.artanh t * (f₁ - f₂) < 0)
        ∧ (0 < 2 * d₁ * d₂ * Core.Fpq s t
          + (t ^ 2 * d₁ ^ 2 + s ^ 2 * d₂ ^ 2)
            * (1 / (1 - (s * t) ^ 2) - 2 * Real.artanh (s * t) / (s * t))
          + Real.artanh (s * t) * (t * (e₁ - e₂) + s * (f₁ - f₂))) := by
  have hst : 0 < s * t := mul_pos hs0 ht0
  have hst1 : s * t < 1 := by nlinarith
  have has : 0 < Real.artanh s := Real.artanh_pos ⟨hs0, hs1⟩
  have hat : 0 < Real.artanh t := Real.artanh_pos ⟨ht0, ht1⟩
  have hax : 0 < Real.artanh (s * t) := Real.artanh_pos ⟨hst, hst1⟩
  have hlamU : (0:ℝ) ≤ t * Real.artanh (s * t) / Real.artanh s := by positivity
  have hlamV : (0:ℝ) ≤ s * Real.artanh (s * t) / Real.artanh t := by positivity
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_good_corrections hlamU hlamV
    (Vlin := 2 * d₁ * d₂ * Core.Fpq s t
      + (t ^ 2 * d₁ ^ 2 + s ^ 2 * d₂ ^ 2)
        * (1 / (1 - (s * t) ^ 2) - 2 * Real.artanh (s * t) / (s * t)))
    (RlinU := d₁ ^ 2 * (1 / (1 - s ^ 2) - 2 * Real.artanh s / s))
    (RlinV := d₂ ^ 2 * (1 / (1 - t ^ 2) - 2 * Real.artanh t / t))
    (total_second_order_eq hs0 hs1 ht0 ht1 (ne_of_gt has) (ne_of_gt hat)) hform
  obtain ⟨e₁, e₂, he⟩ := exists_correction (s := s) (target := A) hs0 hs1
  obtain ⟨f₁, f₂, hf⟩ := exists_correction (s := t) (target := B) ht0 ht1
  refine ⟨e₁, e₂, f₁, f₂, by rw [he]; exact hA, by rw [hf]; exact hB, ?_⟩
  have hkey : Real.artanh (s * t) * (t * (e₁ - e₂) + s * (f₁ - f₂))
      = (t * Real.artanh (s * t) / Real.artanh s) * A
        + (s * Real.artanh (s * t) / Real.artanh t) * B := by
    rw [← he, ← hf]
    field_simp
  rw [hkey]
  linarith [hAB]

/-! ### Discharging the maximality hypothesis -/

lemma atom_pos_eventually {p d e : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᶠ ε in nhds (0:ℝ), 0 < atomC p d e ε ∧ atomC p d e ε < 1 := by
  have hcont : Continuous (atomC p d e) := by unfold atomC; fun_prop
  have h1 := (hcont.tendsto 0).eventually (eventually_gt_nhds (by simpa [atomC] using hp0))
  have h2 := (hcont.tendsto 0).eventually (eventually_lt_nhds (by simpa [atomC] using hp1))
  filter_upwards [h1, h2] with ε ha hb using ⟨ha, hb⟩

lemma atom_neg_eventually {p d e : ℝ} (hp0 : p < 0) (hp1 : -1 < p) :
    ∀ᶠ ε in nhds (0:ℝ), atomC p d e ε < 0 ∧ -1 < atomC p d e ε := by
  have hcont : Continuous (atomC p d e) := by unfold atomC; fun_prop
  have h1 := (hcont.tendsto 0).eventually (eventually_lt_nhds (by simpa [atomC] using hp0))
  have h2 := (hcont.tendsto 0).eventually (eventually_gt_nhds (by simpa [atomC] using hp1))
  filter_upwards [h1, h2] with ε ha hb using ⟨ha, hb⟩

/-- **The maximality hypothesis, discharged.**  Near `ε = 0` the curve is a pair
of genuine channels, so `curve_max_bound` applies. -/
theorem hmax_discharge {Cu Cv : ℝ} {cL cR : Chan} {s t d₁ d₂ e₁ e₂ f₁ f₂ : ℝ}
    (hmx : IsMaxPairC Cu Cv cL cR) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hRU : rateCurve s d₁ e₁ e₂ 0 ≤ Cu) (hRV : rateCurve t d₂ f₁ f₂ 0 ≤ Cv) :
    ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      rateCurve s d₁ e₁ e₂ ε - rateCurve s d₁ e₁ e₂ 0 ≤ 0 →
      rateCurve t d₂ f₁ f₂ ε - rateCurve t d₂ f₁ f₂ 0 ≤ 0 →
      valueCurve s t d₁ d₂ e₁ e₂ f₁ f₂ ε - mutualInfo (jointUV 0 cL cR) ≤ 0 := by
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
  have hRU' : (-(atomC (-s) d₁ e₂ ε) / (atomC s d₁ e₁ ε - atomC (-s) d₁ e₂ ε))
        * fe (atomC s d₁ e₁ ε)
      + (atomC s d₁ e₁ ε / (atomC s d₁ e₁ ε - atomC (-s) d₁ e₂ ε))
        * fe (atomC (-s) d₁ e₂ ε) ≤ Cu := by
    rw [← rateCurve_eq hgU]; linarith
  have hRV' : (-(atomC (-t) d₂ f₂ ε) / (atomC t d₂ f₁ ε - atomC (-t) d₂ f₂ ε))
        * fe (atomC t d₂ f₁ ε)
      + (atomC t d₂ f₁ ε / (atomC t d₂ f₁ ε - atomC (-t) d₂ f₂ ε))
        * fe (atomC (-t) d₂ f₂ ε) ≤ Cv := by
    rw [← rateCurve_eq hgV]; linarith
  have h := curve_max_bound hmx pa0 pa1 pb0 pb1 pc0 pc1 pd0 pd1 hRU' hRV'
  rw [← valueCurve_eq hgU hgV] at h
  linarith

/-! ### The symmetric pair is not a maximiser -/

/-- **(C), at the level of biases.**  A pair whose bias magnitudes are `s` and
`t` in `(0,1)`, with the BSC value, cannot be a maximiser. -/
theorem symmetric_not_max {Cu Cv : ℝ} {cL cR : Chan} {s t : ℝ}
    (hmx : IsMaxPairC Cu Cv cL cR) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hRU : fe s ≤ Cu) (hRV : fe t ≤ Cv)
    (hV0 : mutualInfo (jointUV 0 cL cR)
      = (1 / 2 : ℝ) * (fFun (s * t) + fFun (-(s * t)))) : False := by
  have hform : 0 < Core.Fpp s t * (1:ℝ) ^ 2
      + 2 * Core.Fpq s t * (1:ℝ) * (-(Core.Fpq s t) / Core.Fqq s t)
      + Core.Fqq s t * (-(Core.Fpq s t) / Core.Fqq s t) ^ 2 := by
    have h := hessian_form_pos hs0 hs1 ht0 ht1
    linarith [h]
  obtain ⟨e₁, e₂, f₁, f₂, hU, hV, hG⟩ :=
    exists_curve_corrections (d₁ := 1) (d₂ := -(Core.Fpq s t) / Core.Fqq s t)
      hs0 hs1 ht0 ht1 hform
  refine curve_contradiction hs0 hs1 ht0 ht1 hV0 hG hU hV ?_
  refine hmax_discharge hmx hs0 hs1 ht0 ht1 ?_ ?_
  · rw [rateCurve_zero hs0]; exact hRU
  · rw [rateCurve_zero ht0]; exact hRV

/-! ### `BSCNotMax`: reducing `BothBSC` to the bias data -/

theorem fe_eq_half_fFun (z : ℝ) : fe z = (1 / 2 : ℝ) * (fFun z + fFun (-z)) := by
  simp only [fe, fFun]
  rw [show (1:ℝ) + -z = 1 - z by ring]
  ring

theorem fe_abs (z : ℝ) : fe |z| = fe z := by
  rcases abs_choice z with h | h
  · rw [h]
  · rw [h, fe_even]

/-- The biases of a BSC. -/
theorem biasOf_bsc {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    biasOf (jointUX (bsc α h0 h1)) true = 2 * α - 1
      ∧ biasOf (jointUX (bsc α h0 h1)) false = 1 - 2 * α := by
  have hm : ∀ u, marg₁ (jointUX (bsc α h0 h1)) u = 1 / 2 := by
    intro u; cases u <;>
      · simp only [marg₁, jointUX, bsc_tr, bscTr]
        norm_num
        ring
  constructor <;>
    · rw [biasOf, hm]
      simp only [jointUX, bsc_tr, bscTr]
      norm_num
      ring

theorem biasOfSnd_bsc {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    biasOfSnd (jointYV (bsc β h0 h1)) false = 1 - 2 * β
      ∧ biasOfSnd (jointYV (bsc β h0 h1)) true = 2 * β - 1 := by
  have hm : ∀ v, marg₂ (jointYV (bsc β h0 h1)) v = 1 / 2 := by
    intro v; cases v <;>
      · simp only [marg₂, jointYV, bsc_tr, bscTr]
        norm_num
        ring
  constructor <;>
    · rw [biasOfSnd, hm]
      simp only [jointYV, bsc_tr, bscTr]
      norm_num
      ring

/-- **`(C)` as the `BSCNotMax` `Prop`.** -/
theorem bscNotMax_holds : BSCNotMax := by
  intro a d ha0 ha1 hd0 hd1 cL cR hmx hbsc
  obtain ⟨⟨α, hα0, hα1, rfl⟩, β, hβ0, hβ1, rfl⟩ := hbsc
  -- rates and value of the BSC pair
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
  -- the Z/S pair, for the degenerate cases
  have hfeasZS : FeasibleC (zsRate a) (zsRate d) (zChan a ha0 ha1) (sChan d hd0 hd1) :=
    ⟨le_of_eq (zChan_rate ha0 ha1), le_of_eq (sChan_rate hd0 hd1)⟩
  have hZS := hmx.2 _ _ hfeasZS
  rw [zChan_sChan_value ha0 ha1 hd0 hd1, hval] at hZS
  -- corners are infeasible
  have hcorner : ∀ γ : ℝ, |1 - 2 * γ| = 1 → fe (1 - 2 * γ) = Real.log 2 := by
    intro γ hγ
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hγ with h | h
    · rw [h, fe_one]
    · rw [h, ← fe_even, neg_neg, fe_one]
  have hUlt : fe (1 - 2 * α) ≤ zsRate a := by rw [← hrU]; exact hmx.1.1
  have hVlt : fe (1 - 2 * β) ≤ zsRate d := by rw [← hrV]; exact hmx.1.2
  have hs1 : |1 - 2 * α| < 1 := by
    rcases lt_or_eq_of_le ((abs_le.mpr ⟨by linarith, by linarith⟩ : |1 - 2*α| ≤ 1)) with h | h
    · exact h
    · exfalso
      have := hcorner α h
      linarith [zsRate_lt_log_two ha0 ha1, hUlt, this]
  have ht1 : |1 - 2 * β| < 1 := by
    rcases lt_or_eq_of_le ((abs_le.mpr ⟨by linarith, by linarith⟩ : |1 - 2*β| ≤ 1)) with h | h
    · exact h
    · exfalso
      have := hcorner β h
      linarith [zsRate_lt_log_two hd0 hd1, hVlt, this]
  -- degenerate: a zero bias makes the value zero
  rcases eq_or_lt_of_le (abs_nonneg (1 - 2 * α)) with hs0 | hs0
  · exfalso
    have : (1 : ℝ) - 2 * α = 0 := by
      have := abs_eq_zero.mp hs0.symm; exact this
    rw [this, zero_mul, fe_zero] at hZS
    linarith [zsValue_pos ha0 ha1 hd0 hd1]
  rcases eq_or_lt_of_le (abs_nonneg (1 - 2 * β)) with ht0 | ht0
  · exfalso
    have : (1 : ℝ) - 2 * β = 0 := by
      have := abs_eq_zero.mp ht0.symm; exact this
    rw [this, mul_zero, fe_zero] at hZS
    linarith [zsValue_pos ha0 ha1 hd0 hd1]
  -- main case
  refine symmetric_not_max (s := |1 - 2 * α|) (t := |1 - 2 * β|) hmx hs0 hs1 ht0 ht1 ?_ ?_ ?_
  · rw [fe_abs]; exact hUlt
  · rw [fe_abs]; exact hVlt
  · rw [hval, ← fe_eq_half_fFun, ← abs_mul, fe_abs]

/-! ### The assembly

`(A)`, `(B)`, `(C)`, `(D)` are all theorems, so Conjecture 1 at `p = 0` reduces
to a single remaining case: a maximiser with a `U`-side corner and no `V`-side
corner.  Note the case is not vacuous and is not covered by `cornerBound`: the
value is symmetric in the two sides, but the *rates* are not — swapping would
need `cR`'s rate against `zsRate a` rather than `zsRate d`. -/

/-- A degenerate `U`-side makes the value zero. -/
theorem value_zero_of_bias_zero {cL cR : Chan} (hpi : ∀ u, 0 < marg₁ (jointUX cL) u)
    (hrho : ∀ v, 0 < marg₂ (jointYV cR) v) (hb : ∀ u, biasOf (jointUX cL) u = 0) :
    mutualInfo (jointUV 0 cL cR) = 0 := by
  have hker : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u
      * biasOfSnd (jointYV cR) v := by
    intro u v; rw [hb]; norm_num
  rw [mutualInfo_jointUV_eq_kernel_sum_of_nonneg 0 cL cR hpi hrho hker]
  simp [hb, fFun]

/-- If one `U`-bias vanishes, both do. -/
theorem bias_all_zero {cL : Chan} (hpi : ∀ u, 0 < marg₁ (jointUX cL) u)
    (h : biasOf (jointUX cL) true = 0) : ∀ u, biasOf (jointUX cL) u = 0 := by
  have hmz := pi_bias_sum_zero cL (hpi false) (hpi true)
  rw [h, mul_zero, add_zero] at hmz
  intro u
  cases u
  · exact (mul_eq_zero.mp hmz).resolve_left (ne_of_gt (hpi false))
  · exact h

/-- **Conjecture 1 at `p = 0`, modulo the one-corner case.**  Everything else —
existence `(A)`, classification `(B)`, the saddle `(C)`, the corner bound `(D)`,
and the degenerate branches — is discharged here. -/
theorem conjecture1_p0_of_Ucorner
    (hUc : ∀ (a d : ℝ), 0 < a → a < 1 → 0 < d → d < 1 → ∀ cL cR : Chan,
      IsMaxPairC (zsRate a) (zsRate d) cL cR →
      (∀ u, 0 < marg₁ (jointUX cL) u) → (∀ v, 0 < marg₂ (jointYV cR) v) →
      USideCorner cL → ¬ VSideCorner cR →
      mutualInfo (jointUV 0 cL cR) ≤ zsValue a d) :
    Conjecture1_p0 := by
  intro a d ha0 ha1 hd0 hd1 cL cR hCu hCv
  have hCv' : mutualInfo (jointYV cR) ≤ zsRate d := by
    rw [← sChan_rate hd0 hd1]; exact hCv
  have hfeas : FeasibleC (zsRate a) (zsRate d) cL cR := ⟨hCu, hCv'⟩
  obtain ⟨cL', cR', hmax⟩ := maxExistsC _ _ ⟨cL, cR, hfeas⟩
  have h1 := hmax.2 cL cR hfeas
  have hpv := zsValue_pos ha0 ha1 hd0 hd1
  by_cases hL : ∀ u, 0 < marg₁ (jointUX cL') u
  · by_cases hR : ∀ v, 0 < marg₂ (jointYV cR') v
    · by_cases hVc : VSideCorner cR'
      · have := cornerBound ha0 ha1 hd0 hd1 hL hR hVc hmax.1.1 hmax.1.2
        linarith
      · by_cases hUc' : USideCorner cL'
        · have := hUc a d ha0 ha1 hd0 hd1 cL' cR' hmax hL hR hUc' hVc
          linarith
        · by_cases hdeg : biasOf (jointUX cL') true = 0
          · have := value_zero_of_bias_zero hL hR (bias_all_zero hL hdeg)
            linarith
          · by_cases hdegV : biasOfSnd (jointYV cR') false = 0
            · -- a degenerate `V`-side also kills the value
              have hker : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX cL') u
                  * biasOfSnd (jointYV cR') v := by
                intro u v
                have hmz := rho_bias_sum_zero cR' (hR false) (hR true)
                rw [hdegV, mul_zero, zero_add] at hmz
                have hv1 : biasOfSnd (jointYV cR') true = 0 :=
                  (mul_eq_zero.mp hmz).resolve_left (ne_of_gt (hR true))
                cases v
                · rw [hdegV]; norm_num
                · rw [hv1]; norm_num
              have hmz := rho_bias_sum_zero cR' (hR false) (hR true)
              rw [hdegV, mul_zero, zero_add] at hmz
              have hv1 : biasOfSnd (jointYV cR') true = 0 :=
                (mul_eq_zero.mp hmz).resolve_left (ne_of_gt (hR true))
              have hz : mutualInfo (jointUV 0 cL' cR') = 0 := by
                rw [mutualInfo_jointUV_eq_kernel_sum_of_nonneg 0 cL' cR' hL hR hker]
                simp [hdegV, hv1, fFun]
              linarith
            · exact absurd (interiorIsBSC_of_noCorner (Or.inl hmax) hL hR hUc' hVc hdeg hdegV)
                (bscNotMax_holds a d ha0 ha1 hd0 hd1 cL' cR' hmax)
    · push_neg at hR
      obtain ⟨v₀, hv₀⟩ := hR
      have hnn : 0 ≤ marg₂ (jointYV cR') v₀ := by
        simp only [marg₂, jointYV]
        have := cR'.nonneg false v₀
        have := cR'.nonneg true v₀
        linarith
      have hz : marg₂ (jointYV cR') v₀ = 0 := le_antisymm hv₀ hnn
      have := mutualInfo_jointUV_eq_zero_of_degR (p := 0) (cL := cL') hz
      linarith
  · push_neg at hL
    obtain ⟨u₀, hu₀⟩ := hL
    have hnn : 0 ≤ marg₁ (jointUX cL') u₀ := by
      simp only [marg₁, jointUX]
      have := cL'.nonneg false u₀
      have := cL'.nonneg true u₀
      linarith
    have hz : marg₁ (jointUX cL') u₀ = 0 := le_antisymm hu₀ hnn
    have := mutualInfo_jointUV_eq_zero_of_degL (p := 0) (cR := cR') hz
    linarith

/-! ### The mirror of `(D)`

The remaining case is not separate after all.  `zsValue` **is symmetric**,

```
zsValue a d = d/(1+d)·log(1+a) + (1−ad)/((1+a)(1+d))·log(1−ad) + a/(1+a)·log(1+d)
```

— exchanging `a` and `d` permutes its three terms — and `mutualInfo` is
invariant under transposing a joint law.  So swapping the two sides turns a
`U`-corner into a `V`-corner *and* swaps the budgets, and `cornerBound` applies
verbatim. -/

theorem zsValue_symm (a d : ℝ) : zsValue a d = zsValue d a := by
  simp only [zsValue]
  rw [show (1:ℝ) - d * a = 1 - a * d by ring]
  ring

theorem jointUX_eq_transpose_jointYV (c : Chan) :
    jointUX c = fun u x => jointYV c x u := rfl

theorem mutualInfo_jointUX_eq_jointYV (c : Chan) :
    mutualInfo (jointUX c) = mutualInfo (jointYV c) := by
  rw [jointUX_eq_transpose_jointYV]
  exact mutualInfo_transpose _

theorem jointUV_swap (cL cR : Chan) (u v : Bool) :
    jointUV 0 cR cL u v = jointUV 0 cL cR v u := by
  simp only [jointUV, dsbs]
  cases u <;> cases v <;> norm_num <;> ring

theorem mutualInfo_jointUV_symm (cL cR : Chan) :
    mutualInfo (jointUV 0 cR cL) = mutualInfo (jointUV 0 cL cR) := by
  rw [show jointUV 0 cR cL = fun u v => jointUV 0 cL cR v u from
    funext fun u => funext fun v => jointUV_swap cL cR u v]
  exact mutualInfo_transpose _

/-- **The mirror of `(D)`.**  A `U`-side corner is bounded by the same
`zsValue`, by swapping the two sides. -/
theorem cornerBoundU {cL cR : Chan} {a d : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hd0 : 0 < d) (hd1 : d < 1) (hpi : ∀ u, 0 < marg₁ (jointUX cL) u)
    (hrho : ∀ v, 0 < marg₂ (jointYV cR) v) (hc : USideCorner cL)
    (hCu : mutualInfo (jointUX cL) ≤ zsRate a)
    (hCv : mutualInfo (jointYV cR) ≤ zsRate d) :
    mutualInfo (jointUV 0 cL cR) ≤ zsValue a d := by
  have hpi' : ∀ u, 0 < marg₁ (jointUX cR) u := hrho
  have hrho' : ∀ v, 0 < marg₂ (jointYV cL) v := hpi
  have hc' : VSideCorner cL := hc
  have hCu' : mutualInfo (jointUX cR) ≤ zsRate d := by
    rw [mutualInfo_jointUX_eq_jointYV]; exact hCv
  have hCv' : mutualInfo (jointYV cL) ≤ zsRate a := by
    rw [← mutualInfo_jointUX_eq_jointYV]; exact hCu
  have h := cornerBound hd0 hd1 ha0 ha1 hpi' hrho' hc' hCu' hCv'
  rw [mutualInfo_jointUV_symm, zsValue_symm] at h
  exact h

/-- **Conjecture 1 at `p = 0`.** -/
theorem conjecture1_p0_holds : Conjecture1_p0 := by
  refine conjecture1_p0_of_Ucorner ?_
  intro a d ha0 ha1 hd0 hd1 cL cR hmx hL hR hUc _
  exact cornerBoundU ha0 ha1 hd0 hd1 hL hR hUc hmx.1.1 hmx.1.2

end BSCAveraging
