import BSCAveraging.KernelBridge
import BSCAveraging.Exploration.KernelAlgebra

/-! # `KernelBridge` — exploration companion

The declarations of `BSCAveraging.KernelBridge` that are **not** used by any of the
three theorems of `BSCAveraging.Basic`.  Section headers are copied from the
main file so the two read in parallel. -/

/-! # From the cleared certificate to the kernel lemma

`KernelCertFast.lean` proves `0 ≤ kerQR θ₁ θ₂ θ₃ u v`, the *cleared* kernel in
ordered bi-simplex coordinates.  Here we

* identify `kerQR` with `kernelSum · kernelDen`, the denominator being a product
  of manifestly positive factors (`kerQR_eq`);
* drop the ordering hypothesis, the sum being symmetric in the `θᵢ`;

turning `KernelLemma` from a `Prop` into a theorem (`kernelLemma_holds`).

The clearing identity is proved in **abstract letters** (`kernel_clear_abstract`,
twelve opaque variables): expanding it in `θ₁,θ₂,θ₃,u,v` would be a degree-21
polynomial identity, which `ring` cannot do in reasonable time, whereas in the
letters `Aᵢ,aᵢ,bᵢ,wᵢ` it is a few dozen monomials. -/

namespace BSCAveraging

open Reflect


/-- **`KernelLemma` is a theorem.** -/
theorem kernelLemma_holds : KernelLemma := by
  intro θ₁ θ₂ θ₃ u v h₁ h₁' h₂ h₂' h₃ h₃' hv0 hvu hu1
  simpa [kernelSum] using
    kernelSum_nonneg (le_of_lt h₁) (le_of_lt h₁') (le_of_lt h₂) (le_of_lt h₂')
      (le_of_lt h₃) (le_of_lt h₃')
      (le_of_lt hv0) hvu hu1

end BSCAveraging
