import BSCAveraging.Reflect

/-! # `Reflect` — exploration companion

The declarations of `BSCAveraging.Reflect` that are **not** used by any of the
three theorems of `BSCAveraging.Basic`.  Section headers are copied from the
main file so the two read in parallel. -/

/-! # A reflection layer for nonnegative-coefficient certificates

The kernel lemma can also be proved by handing `ring` an 11385-term identity.
That was tried and abandoned (`NOTES.md` §7f⁴: killed after 476 min at 30 GB
without finishing).  It is expensive twice over: Lean must *parse and
elaborate* a 900 KB arithmetic term (every numeral an `OfNat ℝ`, every `*` an
`HMul` application), and then `ring` must build a proof term for the whole
normalisation.

This file removes both costs.  Polynomials become **data** — a list of
(exponent record, integer coefficient) pairs — with

* `M7`, a seven-slot exponent record (fixed arity, so no length side conditions);
* `Poly := List (M7 × ℤ)`, *not* assumed sorted or collected;
* `PE`, a syntax tree for polynomial expressions, and `PE.norm : PE → Poly`;
* `PE.eval : PE → (ℕ → ℝ) → ℝ`, and the soundness theorem
  `Poly.eval (e.norm) ρ = e.eval ρ`.

All the arithmetic happens in `ℤ` and `ℕ`, where Lean's kernel has GMP fast
paths; only the final soundness step touches `ℝ`, through what is essentially an
evaluation ring hom.  A certificate then never appears in the source: the small
product form is written as a `PE`, `norm` computes its expansion inside Lean,
and positivity is a decidable check on the resulting coefficient list.

See `NOTES.md` §7f‴. -/

namespace BSCAveraging.Reflect

open List

/-! ## Monomials -/


/-! ## Polynomials as data

No sortedness or collectedness is assumed: `Poly.eval` is just the sum of the
terms, so `+` is list append and `*` is the pairwise product. -/


theorem Poly.eval_pow (p : Poly) (n : ℕ) (ρ : Fin 7 → ℝ) :
    Poly.eval (Poly.pow p n) ρ = (Poly.eval p ρ) ^ n := by
  induction n with
  | zero => simp [Poly.pow, Poly.eval]
  | succ n ih => simp [Poly.pow, Poly.eval_mul, ih, pow_succ]; ring


/-! ## Collection

`Poly.mul` multiplies out pairwise, so without collection the term count is the
*product* of the input counts and the expansion explodes.  `Poly.collect` sorts
by a packed key and merges adjacent equal monomials.  Soundness needs nothing
about the sort order — permutation invariance of a list sum plus soundness of
adjacent merging — so the key need not be injective, and the fuel version below
is safe even if the fuel runs out (it just returns the list unchanged). -/


/-! ## Expressions and their normal form -/


/-! ## Positivity from a nonnegative coefficient list -/


end BSCAveraging.Reflect
