import BSCAveraging.BestResponse
import BSCAveraging.Exploration.Envelope

/-! # `BestResponse` — exploration companion

The declarations of `BSCAveraging.BestResponse` that are **not** used by any of the
three theorems of `BSCAveraging.Basic`.  Section headers are copied from the
main file so the two read in parallel. -/

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


/-- The `V`-side mirror of `bestResponse_le_of_certificate`: with the `U`-side
channel `cL` fixed, a certificate in the variable `t` bounds `I(U;V)` for every
`cR` obeying `I(Y;V) ≤ Cv`. -/
theorem bestResponse_le_of_certificate' {l₀ l₁ l₂ Cv : ℝ} {cL cR : Chan}
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hker : ∀ u v, 0 ≤ 1 + (1 - 2 * p) * biasOf (jointUX cL) u * biasOfSnd (jointYV cR) v)
    (hl₂ : 0 ≤ l₂)
    (hcert : ∀ t : ℝ, -1 ≤ t → t ≤ 1 →
      marg₁ (jointUX cL) false * fFun ((1 - 2 * p) * biasOf (jointUX cL) false * t)
        + marg₁ (jointUX cL) true * fFun ((1 - 2 * p) * biasOf (jointUX cL) true * t)
        ≤ l₀ + l₁ * t + l₂ * fe t)
    (hCv : mutualInfo (jointYV cR) ≤ Cv) :
    mutualInfo (jointUV p cL cR) ≤ l₀ + l₂ * Cv := by
  have hnn : ∀ v y, 0 ≤ (fun v y => jointYV cR y v) v y := by
    intro v y; simp only [jointYV]; have := cR.nonneg y v; linarith
  have hbias : ∀ v, -1 ≤ biasOfSnd (jointYV cR) v ∧ biasOfSnd (jointYV cR) v ≤ 1 := by
    intro v
    have h := biasOf_mem_Icc (q := fun v y => jointYV cR y v) hnn (u := v) (by
      simpa [marg₁, marg₂] using hrho v)
    simpa [biasOf, biasOfSnd, marg₁, marg₂] using h
  obtain ⟨htf0, htf1⟩ := hbias false
  obtain ⟨htt0, htt1⟩ := hbias true
  have hUV := mutualInfo_jointUV_eq_kernel_sum_of_nonneg p cL cR hpi hrho hker
  have hwf := mul_le_mul_of_nonneg_left (hcert _ htf0 htf1) (le_of_lt (hrho false))
  have hwt := mul_le_mul_of_nonneg_left (hcert _ htt0 htt1) (le_of_lt (hrho true))
  have hsum := marg₂_jointYV_sum cR
  have hzero := rho_bias_sum_zero cR (hrho false) (hrho true)
  have hYV := mutualInfo_jointYV_eq_bias_closed hrho
  have hmul : l₂ * (marg₂ (jointYV cR) false * fe (biasOfSnd (jointYV cR) false)
      + marg₂ (jointYV cR) true * fe (biasOfSnd (jointYV cR) true)) ≤ l₂ * Cv := by
    rw [← hYV]; exact mul_le_mul_of_nonneg_left hCv hl₂
  have key : marg₂ (jointYV cR) false * (l₀ + l₁ * biasOfSnd (jointYV cR) false
        + l₂ * fe (biasOfSnd (jointYV cR) false))
      + marg₂ (jointYV cR) true * (l₀ + l₁ * biasOfSnd (jointYV cR) true
        + l₂ * fe (biasOfSnd (jointYV cR) true))
      = l₀ + l₂ * (marg₂ (jointYV cR) false * fe (biasOfSnd (jointYV cR) false)
        + marg₂ (jointYV cR) true * fe (biasOfSnd (jointYV cR) true)) := by
    linear_combination l₀ * hsum + l₁ * hzero
  rw [hUV]
  ring_nf at hwf hwt key hmul ⊢
  linarith


end BSCAveraging
