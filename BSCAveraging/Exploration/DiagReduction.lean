import BSCAveraging.DiagReduction
import BSCAveraging.Exploration.KernelBridge

/-! # `DiagReduction` — exploration companion

The declarations of `BSCAveraging.DiagReduction` that are **not** used by any of the
three theorems of `BSCAveraging.Basic`.  Section headers are copied from the
main file so the two read in parallel. -/

/-! # The diagonal reduction

`NOTES.md` §7f, step (iii).  With `A, B, C` the three linear functionals of the
mixture representation (`MixtureRep.lean`),

```
N(α,β) := A(β)·B(α)·C(α) − A(α)·B(β)·C(β) ,
```

and the diagonal reduction is `N ≥ 0` for `β ≤ α`.  Each factor is a
one-dimensional integral over the mixing variable `s ∈ [0,1]` (`θ = s²`), so
each of the two products is an *iterated* triple integral — no Fubini is needed,
because a product of one-dimensional integrals factors out of an iterated
integral by `integral_const_mul` alone.

Summing over the six permutations of the three dummy variables leaves the value
unchanged, `Σ_σ ∭ P∘σ = 6N`, while the *integrand* becomes symmetric and is a
positive multiple of the kernel sum of `KernelBridge.lean`.  Hence `6N ≥ 0`. -/

namespace BSCAveraging.Core

open MeasureTheory


/-- The symmetrised integrand, in abstract letters: the sum over the six
permutations of the three dummy variables is a positive multiple of the kernel
sum. -/
lemma sym_letters (A₁ A₂ A₃ a₁ a₂ a₃ b₁ b₂ b₃ w₁ w₂ w₃ u v : ℝ)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hb₃ : b₃ ≠ 0)
    (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) (hw₃ : w₃ ≠ 0) :
    (v * A₁ / b₁ ^ 2 * ((1 - u) / a₂ * (A₃ * (u * (1 - v)) / (a₃ * w₃)))
        + v * A₁ / b₁ ^ 2 * ((1 - u) / a₃ * (A₂ * (u * (1 - v)) / (a₂ * w₂)))
        + v * A₂ / b₂ ^ 2 * ((1 - u) / a₁ * (A₃ * (u * (1 - v)) / (a₃ * w₃)))
        + v * A₂ / b₂ ^ 2 * ((1 - u) / a₃ * (A₁ * (u * (1 - v)) / (a₁ * w₁)))
        + v * A₃ / b₃ ^ 2 * ((1 - u) / a₁ * (A₂ * (u * (1 - v)) / (a₂ * w₂)))
        + v * A₃ / b₃ ^ 2 * ((1 - u) / a₂ * (A₁ * (u * (1 - v)) / (a₁ * w₁))))
      - (u * A₁ / a₁ ^ 2 * ((1 - v) / b₂ * (A₃ * (v * (1 - u)) / (b₃ * w₃)))
        + u * A₁ / a₁ ^ 2 * ((1 - v) / b₃ * (A₂ * (v * (1 - u)) / (b₂ * w₂)))
        + u * A₂ / a₂ ^ 2 * ((1 - v) / b₁ * (A₃ * (v * (1 - u)) / (b₃ * w₃)))
        + u * A₂ / a₂ ^ 2 * ((1 - v) / b₃ * (A₁ * (v * (1 - u)) / (b₁ * w₁)))
        + u * A₃ / a₃ ^ 2 * ((1 - v) / b₁ * (A₂ * (v * (1 - u)) / (b₂ * w₂)))
        + u * A₃ / a₃ ^ 2 * ((1 - v) / b₂ * (A₁ * (v * (1 - u)) / (b₁ * w₁))))
      = u * v * (1 - u) * (1 - v) / (a₁ * a₂ * a₃)
        * (A₁ / a₁ * (A₂ / w₂ + A₃ / w₃) * ((a₁ / b₁) ^ 2 - a₂ / b₂ * (a₃ / b₃))
          + A₂ / a₂ * (A₁ / w₁ + A₃ / w₃) * ((a₂ / b₂) ^ 2 - a₁ / b₁ * (a₃ / b₃))
          + A₃ / a₃ * (A₁ / w₁ + A₂ / w₂) * ((a₃ / b₃) ^ 2 - a₁ / b₁ * (a₂ / b₂))) := by
  field_simp
  ring

/-! ### The three integrands -/


/-! ### The diagonal reduction -/


end BSCAveraging.Core
