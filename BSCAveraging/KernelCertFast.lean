import BSCAveraging.Reflect
import BSCAveraging.KernelKron
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith

/-! # The kernel lemma by reflection — the certificate is *computed*, not shipped

The same fact can be stated by handing `ring` an 11385-term identity; that file
is ~900 KB and was abandoned after 476 min at 30 GB without finishing, most of
the cost being the parse and elaboration of a giant arithmetic term and then the
proof term for its normalisation.

Here nothing large is written down.  The cleared kernel is given as a small
syntax tree `kerQPE` over the seven nonnegative bi-simplex coordinates, Lean
*computes* its expansion with `PE.norm`, and positivity is the decidable check
`allNonneg` on the resulting coefficient list — 24129 monomials, every
coefficient a positive integer.  `PE.eval_nonneg_of_norm` (proved in
`Reflect.lean`, by induction, once and for all) turns that check into the real
inequality.

**The check runs in the kernel, and it never expands anything.**  Expanding
`kerQPE` in the kernel is hopeless — `6.8·10⁶` monomial products, tens of
gigabytes of retained intermediates (`NOTES.md` §7i–§7j′) — and for a long time
the coefficient check lived under `native_decide`, the one auxiliary axiom of
the development.  `KernelKron.lean` replaces it by **Kronecker substitution**:
the tree is evaluated at a single big-integer point, which the kernel does by
GMP arithmetic on `Nat` literals, and the 24129 coefficients are read off the
base-`2^64` digits of the result; non-negativity of all of them is one `land`
against a mask.  The four `decide +kernel` facts below are that computation
(about a second); `PE.eval_nonneg_of_kron` is the reflection principle that
turns them into the inequality.  This file, and with it Conjecture 1, is at
`[propext, Classical.choice, Quot.sound]`.

See `NOTES.md` §7f‴ and §7k. -/

namespace BSCAveraging.Reflect

open PE

private def v (i : Fin 7) : PE := .var i
private def T : PE := .add (.add (v 0) (v 1)) (.add (v 2) (v 3))
private def S : PE := .add (v 4) (.add (v 5) (v 6))
private def U : PE := .add (v 4) (v 5)
private def V : PE := v 4
private def TH : Fin 3 → PE
  | 0 => v 0
  | 1 => .add (v 0) (v 1)
  | _ => .add (.add (v 0) (v 1)) (v 2)
private def AA (i : Fin 3) : PE := .sub T (TH i)
private def aa (i : Fin 3) : PE := .sub (.mul T S) (.mul (TH i) U)
private def bb (i : Fin 3) : PE := .sub (.mul T S) (.mul (TH i) V)
private def ww (i : Fin 3) : PE := .sub (.mul T (.pow S 2)) (.mul (TH i) (.mul U V))

private def term (i j k : Fin 3) : PE :=
  .mul (.mul (.mul (AA i) (.mul (aa j) (aa k)))
             (.add (.mul (AA j) (.mul (ww i) (ww k))) (.mul (AA k) (.mul (ww i) (ww j)))))
       (.sub (.mul (.pow (aa i) 2) (.mul (.pow (bb j) 2) (.pow (bb k) 2)))
             (.mul (.mul (aa j) (aa k)) (.mul (.pow (bb i) 2) (.mul (bb j) (bb k)))))

/-- The cleared kernel `(kernel)·∏a_i·∏w_i·∏b_i²`, bihomogenised, as a syntax
tree over the bi-simplex coordinates `t₁,t₂,t₃,t₄,s₁,s₂,s₃`.  With
`T = Σtᵢ`, `S = Σsⱼ`, `Θ₁ = t₁`, `Θ₂ = t₁+t₂`, `Θ₃ = t₁+t₂+t₃`, `U = s₁+s₂`,
`V = s₁`, the factors are `Aᵢ = T−Θᵢ`, `aᵢ = TS−ΘᵢU`, `bᵢ = TS−ΘᵢV`,
`wᵢ = TS²−ΘᵢUV`. -/
def kerQPE : PE := .add (.add (term 0 1 2) (term 1 2 0)) (term 2 0 1)

/-- **The certificate, checked by the kernel in one big integer** (`KernelKron.lean`).
The four facts below are the whole computation: the tree is bihomogeneous of
bidegree `(12,12)` and has L1 bound below `2^63` (both structural, `decide`); its
value at the Kronecker point is a non-negative integer (a few dozen GMP
operations); and that integer has the top bit of every 64-bit digit clear — one
`land` against the mask `2^63·(B^371293−1)/(B−1)`.  Together, by
`PE.eval_nonneg_of_kron`, every one of the 24129 coefficients of the expansion is
non-negative, without the expansion ever being formed. -/
theorem kerQPE_bideg : kerQPE.bideg = some (12, 12) := by decide +kernel

theorem kerQPE_l1b : kerQPE.l1b < 2 ^ 63 := by decide +kernel

theorem kerQPE_kron_nonneg : 0 ≤ kerQPE.evalZ kron := by decide +kernel

theorem kerQPE_kron_mask :
    (kerQPE.evalZ kron).toNat &&& (2 ^ 63 * ((B ^ 371293 - 1) / (B - 1))) = 0 := by
  decide +kernel

/-- **The kernel lemma, cleared and ordered** — the reflection proof.  For
nonnegative bi-simplex coordinates the cleared kernel is nonnegative. -/
theorem kerQ_nonneg_reflect {t₁ t₂ t₃ t₄ s₁ s₂ s₃ : ℝ}
    (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) (h₃ : 0 ≤ t₃) (h₄ : 0 ≤ t₄)
    (k₁ : 0 ≤ s₁) (k₂ : 0 ≤ s₂) (k₃ : 0 ≤ s₃) :
    0 ≤ PE.eval ![t₁, t₂, t₃, t₄, s₁, s₂, s₃] kerQPE := by
  refine PE.eval_nonneg_of_kron kerQPE kerQPE_bideg kerQPE_l1b kerQPE_kron_nonneg kerQPE_kron_mask ?_
  intro i
  fin_cases i <;> simpa using ‹_›

/-- The syntax tree unfolds **definitionally** to the product form it encodes —
no `ring`, no expansion.  This is what makes the reflection cheap: the
24129-monomial expansion is never formed at all — its coefficients are read off
one big integer (`KernelKron.lean`) — and nothing is normalised by a tactic. -/
theorem eval_kerQPE (ρ : Fin 7 → ℝ) :
    PE.eval ρ kerQPE =
    ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) - ρ 0) * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1) * (ρ 4 + ρ 5)) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1 + ρ 2) * (ρ 4 + ρ 5)))
      * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) - (ρ 0 + ρ 1)) * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) ^ 2 - ρ 0 * ((ρ 4 + ρ 5) * ρ 4)) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) ^ 2 - (ρ 0 + ρ 1 + ρ 2) * ((ρ 4 + ρ 5) * ρ 4))) + ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) - (ρ 0 + ρ 1 + ρ 2)) * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) ^ 2 - ρ 0 * ((ρ 4 + ρ 5) * ρ 4)) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) ^ 2 - (ρ 0 + ρ 1) * ((ρ 4 + ρ 5) * ρ 4))))
      * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - ρ 0 * (ρ 4 + ρ 5)) ^ 2 * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1) * ρ 4) ^ 2 * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1 + ρ 2) * ρ 4) ^ 2)
          - ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1) * (ρ 4 + ρ 5)) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1 + ρ 2) * (ρ 4 + ρ 5)) * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - ρ 0 * ρ 4) ^ 2 * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1) * ρ 4) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1 + ρ 2) * ρ 4))))
  +
    ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) - (ρ 0 + ρ 1)) * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1 + ρ 2) * (ρ 4 + ρ 5)) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - ρ 0 * (ρ 4 + ρ 5)))
      * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) - (ρ 0 + ρ 1 + ρ 2)) * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) ^ 2 - (ρ 0 + ρ 1) * ((ρ 4 + ρ 5) * ρ 4)) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) ^ 2 - ρ 0 * ((ρ 4 + ρ 5) * ρ 4))) + ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) - ρ 0) * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) ^ 2 - (ρ 0 + ρ 1) * ((ρ 4 + ρ 5) * ρ 4)) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) ^ 2 - (ρ 0 + ρ 1 + ρ 2) * ((ρ 4 + ρ 5) * ρ 4))))
      * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1) * (ρ 4 + ρ 5)) ^ 2 * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1 + ρ 2) * ρ 4) ^ 2 * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - ρ 0 * ρ 4) ^ 2)
          - ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1 + ρ 2) * (ρ 4 + ρ 5)) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - ρ 0 * (ρ 4 + ρ 5)) * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1) * ρ 4) ^ 2 * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1 + ρ 2) * ρ 4) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - ρ 0 * ρ 4))))
  +
    ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) - (ρ 0 + ρ 1 + ρ 2)) * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - ρ 0 * (ρ 4 + ρ 5)) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1) * (ρ 4 + ρ 5)))
      * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) - ρ 0) * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) ^ 2 - (ρ 0 + ρ 1 + ρ 2) * ((ρ 4 + ρ 5) * ρ 4)) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) ^ 2 - (ρ 0 + ρ 1) * ((ρ 4 + ρ 5) * ρ 4))) + ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) - (ρ 0 + ρ 1)) * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) ^ 2 - (ρ 0 + ρ 1 + ρ 2) * ((ρ 4 + ρ 5) * ρ 4)) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) ^ 2 - ρ 0 * ((ρ 4 + ρ 5) * ρ 4))))
      * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1 + ρ 2) * (ρ 4 + ρ 5)) ^ 2 * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - ρ 0 * ρ 4) ^ 2 * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1) * ρ 4) ^ 2)
          - ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - ρ 0 * (ρ 4 + ρ 5)) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1) * (ρ 4 + ρ 5)) * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1 + ρ 2) * ρ 4) ^ 2 * (((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - ρ 0 * ρ 4) * ((ρ 0 + ρ 1 + (ρ 2 + ρ 3)) * (ρ 4 + (ρ 5 + ρ 6)) - (ρ 0 + ρ 1) * ρ 4)))) := rfl

/-- The cleared kernel in ordered bi-simplex coordinates.  Unfolding
`eval_kerQPE` shows this is `(kernel)·∏aᵢ·∏wᵢ·∏bᵢ²` with `T = Σtᵢ = 1`,
`S = Σsⱼ = 1`, `Θ₁ = θ₁`, `Θ₂ = θ₂`, `Θ₃ = θ₃`, `U = u`, `V = v`. -/
noncomputable def kerQR (θ₁ θ₂ θ₃ u v : ℝ) : ℝ :=
  PE.eval ![θ₁, θ₂ - θ₁, θ₃ - θ₂, 1 - θ₃, v, u - v, 1 - u] kerQPE

/-- **The kernel lemma, cleared and ordered — by reflection.**  For
`0 ≤ θ₁ ≤ θ₂ ≤ θ₃ ≤ 1` and `0 ≤ v ≤ u ≤ 1` the cleared kernel is nonnegative.
The `θᵢ` are ordered without loss of generality (the kernel is symmetric in
them), and that ordering is exactly what makes the certificate exist. -/
theorem kerQR_nonneg {θ₁ θ₂ θ₃ u v : ℝ} (h0 : 0 ≤ θ₁) (h12 : θ₁ ≤ θ₂) (h23 : θ₂ ≤ θ₃)
    (h31 : θ₃ ≤ 1) (hv0 : 0 ≤ v) (hvu : v ≤ u) (hu1 : u ≤ 1) :
    0 ≤ kerQR θ₁ θ₂ θ₃ u v :=
  kerQ_nonneg_reflect h0 (by linarith) (by linarith) (by linarith) hv0 (by linarith)
    (by linarith)

end BSCAveraging.Reflect
