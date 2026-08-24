import BSCAveraging.Main
/-! # Best-response bounds from a dual certificate

The *constrained* problem — Conjectures 1–3 of Dikshtein–Ordentlich–Shamai
(Entropy **24**(9):1321, 2022) — is not reachable from the hull theorem
(`Envelope.lean` explains why: the hull only sees the concave envelope).  This
file starts the machinery that is reachable: the **one-sided** problem.

Fix the `V`-side channel `cR`, so the bias law `T` and the weights `ρ_v` are
fixed, and write

```
φ_T(s) = ρ_false · f(δ·s·t_false) + ρ_true · f(δ·s·t_true),   f(z) = (1+z)log(1+z)
```

for the value of a `U`-atom of bias `s`.  Then `I(U;V) = E_π[φ_T(S)]` and
`I(U;X) = E_π[f_e(S)]`, both **linear in the law of `S`**, and the law is
constrained only by `E[S] = 0` (`X` uniform) and `E[f_e(S)] ≤ C_u`.  Maximizing
`I(U;V)` over the `U`-side is therefore a *linear program over measures* with
three linear constraints, whose dual is an envelope condition: any `(λ₀,λ₁,λ₂)`
with `λ₂ ≥ 0` and

```
φ_T(s)  ≤  λ₀ + λ₁·s + λ₂·f_e(s)      for all s ∈ [−1,1]                      (★)
```

certifies `I(U;V) ≤ λ₀ + λ₂·C_u` for **every** channel `cL` meeting the
constraint.  The kernel hypothesis is `0 ≤ 1 + δ·s·t`, not `0 <`, so the bound
covers the degenerate "impossible cell" `s·t = −1` that the `p = 0` Z/S pair
creates — exactly the configuration the certificates are about.  That is `bestResponse_le_of_certificate` below, and its `V`-side
mirror.  The `λ₁·s` term drops out for free: `E[S] = 0` because `X` is uniform.

Sharpness — and the shape of a proof of Conjecture 1 — is the content of
`NOTES.md` §7: at `p = 0` with `T` the conjectured S-channel `(1, −d)`, the
certificate `(★)` holds with contact exactly at the two atoms `s = a` and
`s = −1` of the conjectured Z-channel, its slack function
`D = λ₀ + λ₁ s + λ₂ f_e(s) − φ_T(s)` satisfies `D ≥ 0` with a double zero at `a`
and a simple zero at `−1`, and `D''` changes sign exactly once because

```
D''(s)·(1−s²)(1+s·t_false)(1+s·t_true)  is a quadratic in s.
```

So `D ≥ 0` reduces to root counting.  What this does *not* give is joint
optimality: the BSC pair is also an alternating-maximization fixed point, and
no affine certificate can separate the two (at `p = 0` the best affine bound is
the trivial `min(C_u,C_v)`).  That gap is the open part.

See `BSCAveraging.Main`. -/

open Real

namespace BSCAveraging

variable {p : ℝ}

/-- **The `U`-side best-response bound.**  If `(λ₀,λ₁,λ₂)` with `λ₂ ≥ 0`
dominates the atom value `φ_T` in the sense of `(★)`, then every binary channel
`cL` obeying the rate constraint `I(U;X) ≤ Cu` has `I(U;V) ≤ λ₀ + λ₂·Cu`.

The certificate is a statement about a *single real variable* `s`; the channel
`cL` is arbitrary. -/
theorem bestResponse_le_of_certificate {l₀ l₁ l₂ Cu : ℝ} {cL cR : Chan}
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hker : ∀ u v, 0 ≤ 1 + (1 - 2 * p) * biasOf (jointUX cL) u * biasOfSnd (jointYV cR) v)
    (hl₂ : 0 ≤ l₂)
    (hcert : ∀ s : ℝ, -1 ≤ s → s ≤ 1 →
      marg₂ (jointYV cR) false * fFun ((1 - 2 * p) * s * biasOfSnd (jointYV cR) false)
        + marg₂ (jointYV cR) true * fFun ((1 - 2 * p) * s * biasOfSnd (jointYV cR) true)
        ≤ l₀ + l₁ * s + l₂ * fe s)
    (hCu : mutualInfo (jointUX cL) ≤ Cu) :
    mutualInfo (jointUV p cL cR) ≤ l₀ + l₂ * Cu := by
  have hnn : ∀ u x, 0 ≤ jointUX cL u x := by
    intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
  obtain ⟨hsf0, hsf1⟩ := biasOf_mem_Icc hnn (hpi false)
  obtain ⟨hst0, hst1⟩ := biasOf_mem_Icc hnn (hpi true)
  -- `I(U;V) = π_false·φ_T(s_false) + π_true·φ_T(s_true)`
  have hUV := mutualInfo_jointUV_eq_kernel_sum_of_nonneg p cL cR hpi hrho hker
  -- the certificate at the two atoms, weighted by the atom probabilities
  have hwf := mul_le_mul_of_nonneg_left (hcert _ hsf0 hsf1) (le_of_lt (hpi false))
  have hwt := mul_le_mul_of_nonneg_left (hcert _ hst0 hst1) (le_of_lt (hpi true))
  -- `Σ π = 1`, `Σ π·s = 0`, `Σ π·f_e(s) = I(U;X)`
  have hsum := marg₁_jointUX_sum cL
  have hzero := pi_bias_sum_zero cL (hpi false) (hpi true)
  have hUX := mutualInfo_jointUX_eq_bias_closed hpi
  have hmul : l₂ * (marg₁ (jointUX cL) false * fe (biasOf (jointUX cL) false)
      + marg₁ (jointUX cL) true * fe (biasOf (jointUX cL) true)) ≤ l₂ * Cu := by
    rw [← hUX]; exact mul_le_mul_of_nonneg_left hCu hl₂
  -- the `λ₁` term drops out by `E[S] = 0`, the `λ₀` term by `Σ π = 1`
  have key : marg₁ (jointUX cL) false * (l₀ + l₁ * biasOf (jointUX cL) false
        + l₂ * fe (biasOf (jointUX cL) false))
      + marg₁ (jointUX cL) true * (l₀ + l₁ * biasOf (jointUX cL) true
        + l₂ * fe (biasOf (jointUX cL) true))
      = l₀ + l₂ * (marg₁ (jointUX cL) false * fe (biasOf (jointUX cL) false)
        + marg₁ (jointUX cL) true * fe (biasOf (jointUX cL) true)) := by
    linear_combination l₀ * hsum + l₁ * hzero
  rw [hUV]
  ring_nf at hwf hwt key hmul ⊢
  linarith


/-- **The `U`-side best-response *lower* bound**, the mirror of
`bestResponse_le_of_certificate` used by Conjecture 2.  A certificate that lies
*below* the atom value `φ_T`, with `λ₂ ≥ 0`, turns the *lower* rate constraint
`Cu ≤ I(U;X)` into `λ₀ + λ₂·Cu ≤ I(U;V)`.

The direction of the rate constraint flips with the direction of the bound: for
the minimisation problem an unconstrained `U` would give `I(U;V) = 0`, so it is
`I(U;X) ≥ Cu` that is binding. -/
theorem bestResponse_ge_of_certificate {l₀ l₁ l₂ Cu : ℝ} {cL cR : Chan}
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hker : ∀ u v, 0 ≤ 1 + (1 - 2 * p) * biasOf (jointUX cL) u * biasOfSnd (jointYV cR) v)
    (hl₂ : 0 ≤ l₂)
    (hcert : ∀ s : ℝ, -1 ≤ s → s ≤ 1 →
      l₀ + l₁ * s + l₂ * fe s ≤
        marg₂ (jointYV cR) false * fFun ((1 - 2 * p) * s * biasOfSnd (jointYV cR) false)
          + marg₂ (jointYV cR) true * fFun ((1 - 2 * p) * s * biasOfSnd (jointYV cR) true))
    (hCu : Cu ≤ mutualInfo (jointUX cL)) :
    l₀ + l₂ * Cu ≤ mutualInfo (jointUV p cL cR) := by
  have hnn : ∀ u x, 0 ≤ jointUX cL u x := by
    intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
  obtain ⟨hsf0, hsf1⟩ := biasOf_mem_Icc hnn (hpi false)
  obtain ⟨hst0, hst1⟩ := biasOf_mem_Icc hnn (hpi true)
  have hUV := mutualInfo_jointUV_eq_kernel_sum_of_nonneg p cL cR hpi hrho hker
  have hwf := mul_le_mul_of_nonneg_left (hcert _ hsf0 hsf1) (le_of_lt (hpi false))
  have hwt := mul_le_mul_of_nonneg_left (hcert _ hst0 hst1) (le_of_lt (hpi true))
  have hsum := marg₁_jointUX_sum cL
  have hzero := pi_bias_sum_zero cL (hpi false) (hpi true)
  have hUX := mutualInfo_jointUX_eq_bias_closed hpi
  have hmul : l₂ * Cu ≤ l₂ * (marg₁ (jointUX cL) false * fe (biasOf (jointUX cL) false)
      + marg₁ (jointUX cL) true * fe (biasOf (jointUX cL) true)) := by
    rw [← hUX]; exact mul_le_mul_of_nonneg_left hCu hl₂
  have key : marg₁ (jointUX cL) false * (l₀ + l₁ * biasOf (jointUX cL) false
        + l₂ * fe (biasOf (jointUX cL) false))
      + marg₁ (jointUX cL) true * (l₀ + l₁ * biasOf (jointUX cL) true
        + l₂ * fe (biasOf (jointUX cL) true))
      = l₀ + l₂ * (marg₁ (jointUX cL) false * fe (biasOf (jointUX cL) false)
        + marg₁ (jointUX cL) true * fe (biasOf (jointUX cL) true)) := by
    linear_combination l₀ * hsum + l₁ * hzero
  rw [hUV]
  ring_nf at hwf hwt key hmul ⊢
  linarith

end BSCAveraging
