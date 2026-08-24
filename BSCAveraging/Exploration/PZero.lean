import BSCAveraging.PZero
import BSCAveraging.Exploration.BestResponse

/-! # `PZero` — exploration companion

The declarations of `BSCAveraging.PZero` that are **not** used by any of the
three theorems of `BSCAveraging.Basic`.  Section headers are copied from the
main file so the two read in parallel. -/

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


/-! ## The key inequality: log-sum -/


/-! ## Elementary facts about `λ₂` -/

section Lam2

variable {a d : ℝ}


end Lam2

/-! ## The contact conditions `D(−1) = 0`, `D(a) = 0`, and `N(a) ≥ 0` -/

section Contacts

variable {a d : ℝ}


end Contacts


/-! ## Continuity and derivatives (generic in the multipliers) -/

section Calculus

variable {l0 l1 l2 d : ℝ}


end Calculus

/-! ## The two shapes -/

section Shapes

variable {l0 l1 l2 d : ℝ}


end Shapes

/-! ## Conjecture 1: the Z-channel is a global best response to the S-channel -/

section ConjOne

variable {a d : ℝ}


end ConjOne

/-! ## Conjecture 2: the mirror certificate

Conjecture 2 asks for the *minimum* of `I(U;V)`, attained (conjecturally) by two
Z-channels.  Against the same `T = (+1,−d)` the conjectured best response is
`S = (+1,−a)`, so the contacts move to `s = −a` (tangency) and `s = +1`
(endpoint), and the certificate flips sign: `G ≤ 0`, i.e. `φ_d` lies *above* the
affine function.  Shape B does the work. -/

section ConjTwo

variable {a d : ℝ}


end ConjTwo

/-! ## The S-channel, and the certificate as a statement about channels

`DFun_nonneg` is about one real variable.  This section turns it into a bound on
`I(U;V)` for *arbitrary* binary `cL`, by exhibiting the S-channel as a `Chan`
and computing its marginals and biases: with `x = (1−d)/(1+d)` the transition
matrix below has `ρ_false = d/(1+d)`, `ρ_true = 1/(1+d)` and bias atoms
`t_false = +1`, `t_true = −d`, which is exactly the `T` that `phiZ` encodes. -/

section SChannel

variable {d : ℝ}


/-- **The certificate, as a bound on `I(U;V)`.**  At `p = 0`, against the
S-channel with parameter `d`, *every* binary channel `cL` with `I(U;X) ≤ Cu`
satisfies `I(U;V) ≤ λ₀ + λ₂·Cu`, the multipliers being the closed forms of this
file.  Since the Z-channel `(a,−1)` attains the bound, it is a **global best
response** — over all binary `cL`, not merely a local or stationary one. -/
theorem mutualInfo_le_of_sChan {a Cu : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hd0 : 0 < d) (hd1 : d < 1) {cL : Chan}
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u)
    (hCu : mutualInfo (jointUX cL) ≤ Cu) :
    mutualInfo (jointUV 0 cL (sChan d hd0 hd1)) ≤ lam0 a d + lam2 a d * Cu := by
  obtain ⟨hm1, hm2⟩ := marg₂_sChan hd0 hd1
  obtain ⟨hb1, hb2⟩ := biasOfSnd_sChan hd0 hd1
  have hrho : ∀ v, 0 < marg₂ (jointYV (sChan d hd0 hd1)) v := by
    intro v; cases v
    · rw [hm1]; positivity
    · rw [hm2]; positivity
  have hnn : ∀ u x, 0 ≤ jointUX cL u x := by
    intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
  have hker : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u
      * biasOfSnd (jointYV (sChan d hd0 hd1)) v := by
    intro u v
    obtain ⟨hs0, hs1⟩ := biasOf_mem_Icc hnn (hpi u)
    cases v
    · rw [hb1]; nlinarith
    · rw [hb2]; nlinarith
  refine bestResponse_le_of_certificate (p := 0) (l₁ := lam1 a d) hpi hrho hker
    (le_of_lt (lam2_pos ha0 ha1 hd0 hd1)) ?_ hCu
  intro s hs0 hs1
  have hcert := DFun_nonneg ha0 ha1 hd0 hd1 hs0 hs1
  rw [DFun, GFun] at hcert
  rw [hm1, hm2, hb1, hb2]
  have hphi : d / (1 + d) * fFun ((1 - 2 * (0:ℝ)) * s * 1)
      + 1 / (1 + d) * fFun ((1 - 2 * (0:ℝ)) * s * -d) = phiZ d s := by
    have e1 : (1 - 2 * (0:ℝ)) * s * 1 = s := by ring
    have e2 : (1 - 2 * (0:ℝ)) * s * -d = -(d * s) := by ring
    rw [e1, e2, phiZ]
  rw [hphi]
  linarith


/-- **The mirror certificate, as a lower bound on `I(U;V)`.**  At `p = 0`,
against the S-channel with parameter `d`, every binary `cL` with
`I(U;X) ≥ Cu` satisfies `I(U;V) ≥ μ₀ + μ₂·Cu`.  This is the Conjecture 2
counterpart of `mutualInfo_le_of_sChan`. -/
theorem mutualInfo_ge_of_sChan {a Cu : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hd0 : 0 < d) (hd1 : d < 1) {cL : Chan}
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u)
    (hCu : Cu ≤ mutualInfo (jointUX cL)) :
    mlam0 a d + mlam2 a d * Cu ≤ mutualInfo (jointUV 0 cL (sChan d hd0 hd1)) := by
  obtain ⟨hm1, hm2⟩ := marg₂_sChan hd0 hd1
  obtain ⟨hb1, hb2⟩ := biasOfSnd_sChan hd0 hd1
  have hrho : ∀ v, 0 < marg₂ (jointYV (sChan d hd0 hd1)) v := by
    intro v; cases v
    · rw [hm1]; positivity
    · rw [hm2]; positivity
  have hnn : ∀ u x, 0 ≤ jointUX cL u x := by
    intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
  have hker : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u
      * biasOfSnd (jointYV (sChan d hd0 hd1)) v := by
    intro u v
    obtain ⟨hs0, hs1⟩ := biasOf_mem_Icc hnn (hpi u)
    cases v
    · rw [hb1]; nlinarith
    · rw [hb2]; nlinarith
  refine bestResponse_ge_of_certificate (p := 0) (l₁ := mlam1 a d) hpi hrho hker
    (le_of_lt (mlam2_pos ha0 ha1 hd0 hd1)) ?_ hCu
  intro s hs0 hs1
  have hcert := MDFun_nonpos ha0 ha1 hd0 hd1 hs0 hs1
  rw [MDFun, GFun] at hcert
  rw [hm1, hm2, hb1, hb2]
  have hphi : d / (1 + d) * fFun ((1 - 2 * (0:ℝ)) * s * 1)
      + 1 / (1 + d) * fFun ((1 - 2 * (0:ℝ)) * s * -d) = phiZ d s := by
    have e1 : (1 - 2 * (0:ℝ)) * s * 1 = s := by ring
    have e2 : (1 - 2 * (0:ℝ)) * s * -d = -(d * s) := by ring
    rw [e1, e2, phiZ]
  rw [hphi]
  linarith

end SChannel

end BSCAveraging
