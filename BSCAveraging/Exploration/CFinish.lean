import BSCAveraging.CFinish
import BSCAveraging.Exploration.TwoAtom

/-! # `CFinish` — exploration companion

The declarations of `BSCAveraging.CFinish` that are **not** used by any of the
three theorems of `BSCAveraging.Basic`.  Section headers are copied from the
main file so the two read in parallel. -/

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

/-- **The rate gradient's second component is negative.**  Mirror of
`Dfst_fe_pos`; together they give `∇R ≠ 0`, and each gives strict monotonicity
of the rate in one atom. -/
theorem Dsnd_fe_neg {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : b < 0) (hb1 : -1 < b) :
    Dsnd fe Real.artanh a b < 0 := by
  have hab : b < a := by linarith
  have hD : (0:ℝ) < a - b := by linarith
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope fe Real.artanh hab
    (fun x hx => ((hasDerivAt_fe' (by linarith [hx.1]) (by linarith [hx.2])).continuousAt
      ).continuousWithinAt)
    (fun x hx => hasDerivAt_fe' (by linarith [hx.1]) (by linarith [hx.2]))
  have hlt : Real.artanh b < Real.artanh ξ :=
    Real.artanh_lt_artanh (by linarith) (by linarith [hξ.2]) hξ.1
  have hkey : fe b - fe a - (b - a) * Real.artanh b < 0 := by
    rw [eq_comm, div_eq_iff (by linarith : a - b ≠ 0)] at hslope
    nlinarith [hslope, hlt, hD]
  rw [Dsnd]
  have heq : (a / (a - b) ^ 2) * (fe b - fe a) + (a / (a - b)) * Real.artanh b
      = (a / (a - b) ^ 2) * ((fe b - fe a) - (b - a) * Real.artanh b) := by
    field_simp
    ring
  rw [heq]
  exact mul_neg_of_pos_of_neg (by positivity) hkey

/-- **The exact one-sided decomposition.**  For a two-atom mean-zero law, any
linear functional splits as slack plus multiplier times rate.  This is what
turns `A_U` into one-variable Taylor at the (fixed) atoms. -/
theorem twoAtomL_decomp (φ : ℝ → ℝ) (lam l₀ l₁ a b : ℝ) (hab : b ≠ a) :
    twoAtomL φ b a
      = twoAtomL (fun x => φ x - lam * fe x - l₁ * x - l₀) b a
        + lam * twoAtomL fe b a + l₀ := by
  have hD : a - b ≠ 0 := sub_ne_zero_of_ne (Ne.symm hab)
  simp only [twoAtomL]
  field_simp
  ring


/-! ### The diagonal half of the identification -/

/-- The slack paired against the translating two-atom law. -/
noncomputable def slackPath (H : ℝ → ℝ) (s d ε : ℝ) : ℝ :=
  ((s - ε * d) / (2 * s)) * H (s + ε * d) + ((s + ε * d) / (2 * s)) * H (-s + ε * d)

/-- Its derivative. -/
noncomputable def slackPath' (H H' : ℝ → ℝ) (s d ε : ℝ) : ℝ :=
  (-d / (2 * s)) * H (s + ε * d) + ((s - ε * d) / (2 * s)) * (H' (s + ε * d) * d)
    + (d / (2 * s)) * H (-s + ε * d) + ((s + ε * d) / (2 * s)) * (H' (-s + ε * d) * d)

lemma hasDerivAt_slackPath {H H' : ℝ → ℝ} {s d : ℝ} (hs : s ≠ 0)
    (hd : ∀ x, HasDerivAt H (H' x) x) (ε : ℝ) :
    HasDerivAt (slackPath H s d) (slackPath' H H' s d ε) ε := by
  have hu : HasDerivAt (fun e : ℝ => s + e * d) d ε := by
    simpa using ((hasDerivAt_id ε).mul_const d).const_add s
  have hv : HasDerivAt (fun e : ℝ => -s + e * d) d ε := by
    simpa using ((hasDerivAt_id ε).mul_const d).const_add (-s)
  have hA : HasDerivAt (fun e : ℝ => (s - e * d) / (2 * s)) (-d / (2 * s)) ε := by
    have h := (((hasDerivAt_id ε).mul_const d).const_sub s).div_const (2 * s)
    exact KKT.hd_congr h (by ring)
  have hB : HasDerivAt (fun e : ℝ => (s + e * d) / (2 * s)) (d / (2 * s)) ε := by
    have h := (((hasDerivAt_id ε).mul_const d).const_add s).div_const (2 * s)
    exact KKT.hd_congr h (by ring)
  have hHu : HasDerivAt (fun e : ℝ => H (s + e * d)) (H' (s + ε * d) * d) ε := by
    have hH' : HasDerivAt H (H' (s + ε * d)) ((fun e : ℝ => s + e * d) ε) := by
      simpa using hd (s + ε * d)
    have h := hH'.comp ε hu
    simpa [Function.comp_def] using h
  have hHv : HasDerivAt (fun e : ℝ => H (-s + e * d)) (H' (-s + ε * d) * d) ε := by
    have hH' : HasDerivAt H (H' (-s + ε * d)) ((fun e : ℝ => -s + e * d) ε) := by
      simpa using hd (-s + ε * d)
    have h := hH'.comp ε hv
    simpa [Function.comp_def] using h
  have := (hA.mul hHu).add (hB.mul hHv)
  refine KKT.hd_congr this ?_
  rw [slackPath']
  ring

/-- **The diagonal identification.** -/
theorem slackPath_second_deriv {H H' H'' : ℝ → ℝ} {s d : ℝ} (hs : s ≠ 0)
    (hd : ∀ x, HasDerivAt H (H' x) x) (hd' : ∀ x, HasDerivAt H' (H'' x) x)
    (hHs : H s = 0) (hHms : H (-s) = 0) (hH's : H' s = 0) (hH'ms : H' (-s) = 0) :
    slackPath H s d 0 = 0 ∧ slackPath' H H' s d 0 = 0 ∧
      HasDerivAt (slackPath' H H' s d) (d ^ 2 * (H'' s + H'' (-s)) / 2) 0 := by
  have h2s : (2:ℝ) * s ≠ 0 := by simpa using hs
  refine ⟨?_, ?_, ?_⟩
  · simp only [slackPath, zero_mul, add_zero]
    rw [hHs, hHms]
    ring
  · simp only [slackPath', zero_mul, add_zero]
    rw [hHs, hHms, hH's, hH'ms]
    ring
  · have hu : HasDerivAt (fun e : ℝ => s + e * d) d 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const d).const_add s
    have hv : HasDerivAt (fun e : ℝ => -s + e * d) d 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const d).const_add (-s)
    have hA : HasDerivAt (fun e : ℝ => (s - e * d) / (2 * s)) (-d / (2 * s)) 0 := by
      have h := (((hasDerivAt_id (0:ℝ)).mul_const d).const_sub s).div_const (2 * s)
      exact KKT.hd_congr h (by ring)
    have hB : HasDerivAt (fun e : ℝ => (s + e * d) / (2 * s)) (d / (2 * s)) 0 := by
      have h := (((hasDerivAt_id (0:ℝ)).mul_const d).const_add s).div_const (2 * s)
      exact KKT.hd_congr h (by ring)
    have hHu : HasDerivAt (fun e : ℝ => H (s + e * d)) (H' s * d) 0 := by
      have hH' : HasDerivAt H (H' s) ((fun e : ℝ => s + e * d) 0) := by simpa using hd s
      have h := hH'.comp 0 hu
      simpa [Function.comp_def] using h
    have hHv : HasDerivAt (fun e : ℝ => H (-s + e * d)) (H' (-s) * d) 0 := by
      have hH' : HasDerivAt H (H' (-s)) ((fun e : ℝ => -s + e * d) 0) := by
        simpa using hd (-s)
      have h := hH'.comp 0 hv
      simpa [Function.comp_def] using h
    have hGu : HasDerivAt (fun e : ℝ => H' (s + e * d) * d) (H'' s * d * d) 0 := by
      have hH'' : HasDerivAt H' (H'' s) ((fun e : ℝ => s + e * d) 0) := by simpa using hd' s
      have h := (hH''.comp 0 hu).mul_const d
      simpa [Function.comp_def] using h
    have hGv : HasDerivAt (fun e : ℝ => H' (-s + e * d) * d) (H'' (-s) * d * d) 0 := by
      have hH'' : HasDerivAt H' (H'' (-s)) ((fun e : ℝ => -s + e * d) 0) := by
        simpa using hd' (-s)
      have h := (hH''.comp 0 hv).mul_const d
      simpa [Function.comp_def] using h
    have hT1 := hHu.const_mul (-d / (2 * s))
    have hT2 := hA.mul hGu
    have hT3 := hHv.const_mul (d / (2 * s))
    have hT4 := hB.mul hGv
    have hsum := (((hT1.add hT2).add hT3).add hT4)
    refine KKT.hd_congr hsum ?_
    simp only [add_zero, zero_mul, sub_zero]
    field_simp
    rw [hH's, hH'ms]
    ring

/-! ### The slack Hessian *is* the Hessian entry -/

theorem slackHess_eq_Fpp {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (has : Real.artanh s ≠ 0) :
    t ^ 2 / (1 - (s * t) ^ 2)
        - (t * Real.artanh (s * t) / Real.artanh s) / (1 - s ^ 2)
      = Core.Fpp s t := by
  have hst : 0 < s * t := mul_pos hs0 ht0
  have hst1 : s * t < 1 := by nlinarith
  have h1 : (1:ℝ) - (s * t) ^ 2 ≠ 0 := by nlinarith
  have h2 : (1:ℝ) - s ^ 2 ≠ 0 := by nlinarith
  rw [Core.Fpp]
  field_simp

theorem slackHess_eq_Fqq {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hat : Real.artanh t ≠ 0) :
    s ^ 2 / (1 - (s * t) ^ 2)
        - (s * Real.artanh (s * t) / Real.artanh t) / (1 - t ^ 2)
      = Core.Fqq s t := by
  have hst : 0 < s * t := mul_pos hs0 ht0
  have hst1 : s * t < 1 := by nlinarith
  have h1 : (1:ℝ) - (s * t) ^ 2 ≠ 0 := by nlinarith
  have h2 : (1:ℝ) - t ^ 2 ≠ 0 := by nlinarith
  rw [Core.Fqq]
  field_simp

theorem slackHess_even (t lam x : ℝ) :
    t ^ 2 / (1 - (x * t) ^ 2) - lam / (1 - x ^ 2)
      = t ^ 2 / (1 - (-x * t) ^ 2) - lam / (1 - (-x) ^ 2) := by
  ring_nf

theorem slackPath_second_deriv_Fpp {H H' H'' : ℝ → ℝ} {s d t : ℝ} (hs : s ≠ 0)
    (hd : ∀ x, HasDerivAt H (H' x) x) (hd' : ∀ x, HasDerivAt H' (H'' x) x)
    (hHs : H s = 0) (hHms : H (-s) = 0) (hH's : H' s = 0) (hH'ms : H' (-s) = 0)
    (hFs : H'' s = Core.Fpp s t) (hFms : H'' (-s) = Core.Fpp s t) :
    HasDerivAt (slackPath' H H' s d) (d ^ 2 * Core.Fpp s t) 0 := by
  have h := (slackPath_second_deriv (d := d) hs hd hd' hHs hHms hH's hH'ms).2.2
  rw [hFs, hFms] at h
  refine KKT.hd_congr h ?_
  ring

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

/-- **The cross-term principle.**  A product of two functions vanishing at `0`
vanishes to second order there, with second derivative `2·G′(0)·K′(0)`. -/
theorem second_deriv_of_mul_vanishing {G K G' K' : ℝ → ℝ} {g k : ℝ}
    (hG : ∀ x, HasDerivAt G (G' x) x) (hK : ∀ x, HasDerivAt K (K' x) x)
    (hG0 : G 0 = 0) (hK0 : K 0 = 0)
    (hG' : HasDerivAt G' g 0) (hK' : HasDerivAt K' k 0) :
    (G 0 * K 0 = 0) ∧ (G' 0 * K 0 + G 0 * K' 0 = 0) ∧
      HasDerivAt (fun ε => G' ε * K ε + G ε * K' ε) (2 * (G' 0 * K' 0)) 0 := by
  refine ⟨by rw [hG0]; ring, by rw [hG0, hK0]; ring, ?_⟩
  have h1 : HasDerivAt (fun ε => G' ε * K ε) (g * K 0 + G' 0 * K' 0) 0 :=
    hG'.mul (hK 0)
  have h2 : HasDerivAt (fun ε => G ε * K' ε) (G' 0 * K' 0 + G 0 * k) 0 :=
    (hG 0).mul hK'
  refine KKT.hd_congr (h1.add h2) ?_
  rw [hG0, hK0]
  ring


/-! ### The assembly

With the value gain and the feasibility margin both vanishing to second order,
the strict signs of their second derivatives close the argument: there is a
feasible point with strictly larger value, contradicting maximality.  This is
the shape `(C)` finishes in. -/

/-- **The second-order non-maximality principle.**  If along a one-parameter
family the feasibility margin has strictly negative second derivative (so the
family is strictly feasible just to the right of `0`) while the value gain has
strictly positive second derivative, no maximality can hold. -/
theorem not_max_of_second_order {gain gain' feas feas' : ℝ → ℝ} {c cf : ℝ}
    (hg : ∀ᶠ x in nhds (0:ℝ), HasDerivAt gain (gain' x) x) (hg0 : gain 0 = 0)
    (hg'0 : gain' 0 = 0)
    (hg' : HasDerivAt gain' c 0) (hc : 0 < c)
    (hf : ∀ᶠ x in nhds (0:ℝ), HasDerivAt feas (feas' x) x) (hf0 : feas 0 = 0)
    (hf'0 : feas' 0 = 0)
    (hf' : HasDerivAt feas' cf 0) (hcf : cf < 0)
    (hmax : ∀ ε : ℝ, feas ε ≤ 0 → gain ε ≤ 0) : False := by
  have h1 := pos_of_second_deriv_pos hg hg0 hg'0 hg' hc
  have h2 := neg_of_second_deriv_neg hf hf0 hf'0 hf' hcf
  obtain ⟨ε, hε1, hε2⟩ := (h1.and h2).exists
  exact absurd (hmax ε (le_of_lt hε2)) (not_le.mpr hε1)


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

/-- The derivative of `(quadratic)·f(quadratic)`. -/
noncomputable def polyMulComp (f f' : ℝ → ℝ) (c₀ c₁ c₂ g₀ g₁ g₂ ε : ℝ) : ℝ :=
  (c₁ + 2 * c₂ * ε) * f (g₀ + g₁ * ε + g₂ * ε ^ 2)
    + (c₀ + c₁ * ε + c₂ * ε ^ 2)
      * (f' (g₀ + g₁ * ε + g₂ * ε ^ 2) * (g₁ + 2 * g₂ * ε))


theorem hasDerivAt_polyMul {f f' : ℝ → ℝ} (hf : ∀ z, HasDerivAt f (f' z) z)
    (c₀ c₁ c₂ g₀ g₁ g₂ ε : ℝ) :
    HasDerivAt (fun e : ℝ => (c₀ + c₁ * e + c₂ * e ^ 2) * f (g₀ + g₁ * e + g₂ * e ^ 2))
      (polyMulComp f f' c₀ c₁ c₂ g₀ g₁ g₂ ε) ε := by
  have hc := hasDerivAt_quad c₀ c₁ c₂ ε
  have hg := hasDerivAt_quad g₀ g₁ g₂ ε
  have hfg : HasDerivAt (fun e : ℝ => f (g₀ + g₁ * e + g₂ * e ^ 2))
      (f' (g₀ + g₁ * ε + g₂ * ε ^ 2) * (g₁ + 2 * g₂ * ε)) ε := by
    have hz : HasDerivAt f (f' (g₀ + g₁ * ε + g₂ * ε ^ 2))
        ((fun e : ℝ => g₀ + g₁ * e + g₂ * e ^ 2) ε) := by
      simpa using hf (g₀ + g₁ * ε + g₂ * ε ^ 2)
    have h := hz.comp ε hg
    simpa [Function.comp_def] using h
  exact KKT.hd_congr (hc.mul hfg) rfl

/-- **The mixed-partial engine.**  Second derivative at `0` of
`(quadratic)·f(quadratic)`. -/
theorem polyMul_second {f f' f'' : ℝ → ℝ} {g₀ : ℝ} (hf : HasDerivAt f (f' g₀) g₀)
    (hf' : HasDerivAt f' (f'' g₀) g₀) (c₀ c₁ c₂ g₁ g₂ : ℝ) :
    HasDerivAt (polyMulComp f f' c₀ c₁ c₂ g₀ g₁ g₂)
      (2 * c₂ * f g₀ + 2 * c₁ * (f' g₀ * g₁)
        + c₀ * (f'' g₀ * g₁ ^ 2 + 2 * g₂ * f' g₀)) 0 := by
  have hc := hasDerivAt_quad c₀ c₁ c₂ (0:ℝ)
  have hg := hasDerivAt_quad g₀ g₁ g₂ (0:ℝ)
  have hg0 : g₀ + g₁ * (0:ℝ) + g₂ * (0:ℝ) ^ 2 = g₀ := by ring
  have hfg : HasDerivAt (fun e : ℝ => f (g₀ + g₁ * e + g₂ * e ^ 2)) (f' g₀ * g₁) 0 := by
    have hz : HasDerivAt f (f' g₀) ((fun e : ℝ => g₀ + g₁ * e + g₂ * e ^ 2) 0) := by
      simpa using hf
    have h := hz.comp 0 hg
    have := (by simpa [Function.comp_def] using h :
      HasDerivAt (fun e : ℝ => f (g₀ + g₁ * e + g₂ * e ^ 2)) (f' g₀ * (g₁ + 2 * g₂ * 0)) 0)
    exact KKT.hd_congr this (by ring)
  have hf'g : HasDerivAt (fun e : ℝ => f' (g₀ + g₁ * e + g₂ * e ^ 2)) (f'' g₀ * g₁) 0 := by
    have hz : HasDerivAt f' (f'' g₀) ((fun e : ℝ => g₀ + g₁ * e + g₂ * e ^ 2) 0) := by
      simpa using hf'
    have h := hz.comp 0 hg
    have := (by simpa [Function.comp_def] using h :
      HasDerivAt (fun e : ℝ => f' (g₀ + g₁ * e + g₂ * e ^ 2)) (f'' g₀ * (g₁ + 2 * g₂ * 0)) 0)
    exact KKT.hd_congr this (by ring)
  have hlin : HasDerivAt (fun e : ℝ => c₁ + 2 * c₂ * e) (2 * c₂) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).const_mul (2 * c₂)).const_add c₁
    exact KKT.hd_congr this (by ring)
  have hglin : HasDerivAt (fun e : ℝ => g₁ + 2 * g₂ * e) (2 * g₂) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).const_mul (2 * g₂)).const_add g₁
    exact KKT.hd_congr this (by ring)
  have hT1 : HasDerivAt (fun e : ℝ => (c₁ + 2 * c₂ * e) * f (g₀ + g₁ * e + g₂ * e ^ 2))
      (2 * c₂ * f g₀ + c₁ * (f' g₀ * g₁)) 0 := by
    have h := hlin.mul hfg
    refine KKT.hd_congr h ?_
    simp only [hg0]
    ring
  have hT2 : HasDerivAt (fun e : ℝ => (c₀ + c₁ * e + c₂ * e ^ 2)
        * (f' (g₀ + g₁ * e + g₂ * e ^ 2) * (g₁ + 2 * g₂ * e)))
      (c₁ * (f' g₀ * g₁) + c₀ * (f'' g₀ * g₁ * g₁ + f' g₀ * (2 * g₂))) 0 := by
    have hin := hf'g.mul hglin
    have h := hc.mul hin
    refine KKT.hd_congr h ?_
    norm_num
    try ring
  have := hT1.add hT2
  refine KKT.hd_congr this ?_
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


/-- **The rate coefficient.**  Summing the two `polyMul_second` coefficients for
`R_U` along the linear curve. -/
theorem rate_second_coeff {s d : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (2 * 0 * fe s + 2 * (-d / (2 * s)) * (Real.artanh s * d)
        + (1 / 2 : ℝ) * ((1 / (1 - s ^ 2)) * d ^ 2 + 2 * 0 * Real.artanh s))
      + (2 * 0 * fe (-s) + 2 * (d / (2 * s)) * (Real.artanh (-s) * d)
        + (1 / 2 : ℝ) * ((1 / (1 - (-s) ^ 2)) * d ^ 2 + 2 * 0 * Real.artanh (-s)))
      = d ^ 2 * (1 / (1 - s ^ 2) - 2 * Real.artanh s / s) := by
  have h2 : (1:ℝ) - s ^ 2 ≠ 0 := by nlinarith
  have hodd : Real.artanh (-s) = -Real.artanh s := by
    rw [Real.artanh_eq_half_log ⟨by linarith, by linarith⟩,
      Real.artanh_eq_half_log ⟨by linarith, le_of_lt hs1⟩,
      show (1 + -s) / (1 - -s) = ((1 + s) / (1 - s))⁻¹ by
        rw [show (1:ℝ) + -s = 1 - s by ring, show (1:ℝ) - -s = 1 + s by ring, inv_div],
      Real.log_inv]
    ring
  rw [hodd]
  field_simp
  ring

/-- **The value coefficient.**  Summing the four `polyMul_second` coefficients
for the value along the linear curve; `P = sd₂+td₁`, `M = td₁−sd₂`. -/
theorem value_second_coeff {s t d₁ d₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t)
    (ht1 : t < 1) :
    (d₁ * d₂ / (s * t)) * (fFun (s * t) - fFun (-(s * t)))
        - ((s * d₂ + t * d₁) ^ 2 / (s * t)) * (Real.log (1 + s * t) + 1)
        + ((t * d₁ - s * d₂) ^ 2 / (s * t)) * (Real.log (1 - s * t) + 1)
        + (1 / 2 : ℝ) * ((1 / (1 + s * t)) * (s * d₂ + t * d₁) ^ 2
            + (1 / (1 - s * t)) * (t * d₁ - s * d₂) ^ 2)
        + d₁ * d₂ * ((Real.log (1 + s * t) + 1) + (Real.log (1 - s * t) + 1))
      = 2 * d₁ * d₂ * Core.Fpq s t
        + (t ^ 2 * d₁ ^ 2 + s ^ 2 * d₂ ^ 2)
          * (1 / (1 - (s * t) ^ 2) - 2 * Real.artanh (s * t) / (s * t)) := by
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


/-- The rate's second derivative along the pure translation, as an explicit
sign-changing expression: the reason the corrected curve is needed. -/
theorem rate_translation_second (s d : ℝ) :
    d ^ 2 * (1 / (1 - s ^ 2) - 2 * Real.artanh s / s)
      = d ^ 2 / (1 - s ^ 2) - 2 * d ^ 2 * Real.artanh s / s := by
  ring

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


/-- The corrected curve's forced weight, and its Taylor data at `0`. -/
theorem weight_taylor {s d e₁ e₂ : ℝ} (hs : s ≠ 0) :
    (fun ε : ℝ => -(-s + ε * d + ε ^ 2 * e₂)) 0 / (fun ε : ℝ =>
        (s + ε * d + ε ^ 2 * e₁) - (-s + ε * d + ε ^ 2 * e₂)) 0 = 1 / 2
      ∧ (-d * (2 * s) - s * 0) / (2 * s) ^ 2 = -d / (2 * s)
      ∧ (((-2 * e₂) * (2 * s) - s * (2 * (e₁ - e₂))) * (2 * s)
          - 2 * 0 * ((-d) * (2 * s) - s * 0)) / (2 * s) ^ 3
        = -(e₁ + e₂) / (2 * s) := by
  have h2s : (2:ℝ) * s ≠ 0 := by simpa using hs
  refine ⟨?_, ?_, ?_⟩
  · norm_num
    field_simp
    norm_num
  · field_simp
    ring
  · field_simp
    ring

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


/-- The rate gradient at the symmetric point: `∇R = (artanh s/2, −artanh s/2)`. -/
theorem rate_grad_symmetric {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Dfst fe Real.artanh s (-s) = Real.artanh s / 2
      ∧ Dsnd fe Real.artanh s (-s) = -(Real.artanh s / 2) := by
  have hs : s ≠ 0 := ne_of_gt hs0
  constructor
  · rw [Dfst, fe_even]
    field_simp
    ring
  · rw [Dsnd, fe_even, artanh_odd hs0 hs1]
    field_simp
    ring


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

/-- The weight-correction terms cancel. -/
theorem value_weightcorr_cancel (E x : ℝ) :
    (1 / 2 : ℝ) * ((-E) * (fFun x + fFun (-x)) + E * (fFun (-x) + fFun x)) = 0 := by
  ring

/-- **The value correction.**  The surviving `f′` terms telescope to
`artanh(x)·[t(e₁−e₂) + s(f₁−f₂)]`. -/
theorem value_correction_coeff {s t e₁ e₂ f₁ f₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1) :
    (1 / 2 : ℝ) * ((Real.log (1 + s * t) + 1) * (e₁ * t + f₁ * s)
        + (Real.log (1 - s * t) + 1) * (-(e₁ * t) + f₂ * s)
        + (Real.log (1 - s * t) + 1) * (e₂ * t - f₁ * s)
        + (Real.log (1 + s * t) + 1) * (-(e₂ * t) - f₂ * s))
      = Real.artanh (s * t) * (t * (e₁ - e₂) + s * (f₁ - f₂)) := by
  have hst : 0 < s * t := mul_pos hs0 ht0
  have hst1 : s * t < 1 := by nlinarith
  have hp : (0:ℝ) < 1 + s * t := by linarith
  have hm : (0:ℝ) < 1 - s * t := by linarith
  have hA : Real.artanh (s * t)
      = (Real.log (1 + s * t) - Real.log (1 - s * t)) / 2 := by
    rw [Real.artanh_eq_half_log ⟨by linarith, le_of_lt hst1⟩,
      Real.log_div (ne_of_gt hp) (ne_of_gt hm)]
    ring
  rw [hA]
  ring

/-! ### Choosing the corrections -/


/-! ### The `Chan` layer

The second-order machinery talks about explicit functions of the four atom
parameters.  These two lemmas are the bridge: the rate and the value of a pair
of atom-built channels *are* those functions. -/


/-! ### The curve, concretely

The bottom layer of the `HasDerivAt` chains: the corrected atoms and the forced
weights, as explicit functions of `ε`, with their first and second derivative
data. -/


/-- The gap between the two corrected atoms: `2s + ε²(e₁−e₂)`. -/
noncomputable def gapC (s e₁ e₂ ε : ℝ) : ℝ := atomC s 0 e₁ ε - atomC (-s) 0 e₂ ε

lemma gapC_eq (s e₁ e₂ ε : ℝ) : gapC s e₁ e₂ ε = 2 * s + ε ^ 2 * (e₁ - e₂) := by
  simp only [gapC, atomC]; ring


/-! ### The rate chain, composed

`R_U(ε) = w(ε)·f_e(xₐ(ε)) + (1−w(ε))·f_e(x_b(ε))`.  Two applications of
`hasDerivAt_genMul` give its derivative; two of `genMul_second` give the second
derivative at `0`, which `rate_corrected_coeff` identifies. -/


/-! ### The value chain

Each of the four value terms is `c·f(g)` with `c = wᵢρⱼ` and `g = xᵢyⱼ` both
*products*, so the data fed to `genMul_second` comes from product rules. -/


/-! ### The four terms' data

For the term `(i,j)` the weight is `wᵢρⱼ` and the argument is `xᵢyⱼ`, so at `ε=0`

```
c(0) = ¼ ,  c′(0) = ½(wᵢ′ + ρⱼ′) ,  c₂ = wᵢ″ρⱼ + 2wᵢ′ρⱼ′ + wᵢρⱼ″ ,
g(0) = xᵢ⁰yⱼ⁰ , g′(0) = d₁yⱼ⁰ + xᵢ⁰d₂ , g₂ = 2eᵢyⱼ⁰ + 2d₁d₂ + 2xᵢ⁰fⱼ ,
```

all supplied by `hasDerivAt_mul2` / `hasDerivAt_mul2'` from `hasDerivAt_wC`,
`hasDerivAt_wC'`, `hasDerivAt_atomC`, `hasDerivAt_atomC'`.  Summing the four
`hasDerivAt_valTerm'` coefficients and matching against
`value_second_coeff` + `value_correction_coeff` closes the value chain. -/


/-! ### The four-term sum -/


/-! ### The value curve, assembled -/


/-! ### The final chaining -/


/-! ### Identifying the curves with the `pair_atoms` expressions -/


/-! ### The value curve's second derivative -/


/-! ### The contradiction, chained

`gain ε = V(ε) − V*` and `feas ε = R(ε) − R(0)` on each side.  Both vanish at
`0` with vanishing first derivative (§7e¹⁷), their second derivatives are the
closed forms of §7e¹³ and §7e¹⁶, and `curve_max_bound` supplies maximality.  So
`not_max_of_second_order2` applies as soon as the second-derivative signs are
right — which `exists_good_corrections` arranges. -/


/-! ### Producing the corrections -/


/-! ### Discharging the maximality hypothesis -/


/-! ### The symmetric pair is not a maximiser -/


/-! ### `BSCNotMax`: reducing `BothBSC` to the bias data -/


/-! ### The assembly

`(A)`, `(B)`, `(C)`, `(D)` are all theorems, so Conjecture 1 at `p = 0` reduces
to a single remaining case: a maximiser with a `U`-side corner and no `V`-side
corner.  Note the case is not vacuous and is not covered by `cornerBound`: the
value is symmetric in the two sides, but the *rates* are not — swapping would
need `cR`'s rate against `zsRate a` rather than `zsRate d`. -/


/-! ### The mirror of `(D)`

The remaining case is not separate after all.  `zsValue` **is symmetric**,

```
zsValue a d = d/(1+d)·log(1+a) + (1−ad)/((1+a)(1+d))·log(1−ad) + a/(1+a)·log(1+d)
```

— exchanging `a` and `d` permutes its three terms — and `mutualInfo` is
invariant under transposing a joint law.  So swapping the two sides turns a
`U`-corner into a `V`-corner *and* swaps the budgets, and `cornerBound` applies
verbatim. -/


end BSCAveraging
