import BSCAveraging.Reflect
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

Cost of the check: one `native_decide`, i.e. compiled integer arithmetic.  That
adds one axiom to this file — on Lean v4.32.0 `native_decide` mints a
per-declaration auxiliary axiom, here
`kerQPE_allNonneg._native.native_decide.ax_1_1`, rather than citing
`Lean.ofReduceBool`.  The rest of the development
stays at `[propext, Classical.choice, Quot.sound]`.  There is no axiom-clean
alternative in the repository: the direct `ring` route described in the first
paragraph was abandoned unfinished, so this `native_decide` is the only proof of
`kerQPE_allNonneg` that exists here.

See `NOTES.md` §7f‴. -/

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

/-- **The Pólya certificate, computed.**  Every coefficient of the expansion of
`kerQPE` is nonnegative.  24129 monomials; checked by compiled integer
arithmetic. -/
theorem kerQPE_allNonneg : kerQPE.norm.allNonneg = true := by native_decide

/-- **The kernel lemma, cleared and ordered** — the reflection proof.  For
nonnegative bi-simplex coordinates the cleared kernel is nonnegative. -/
theorem kerQ_nonneg_reflect {t₁ t₂ t₃ t₄ s₁ s₂ s₃ : ℝ}
    (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) (h₃ : 0 ≤ t₃) (h₄ : 0 ≤ t₄)
    (k₁ : 0 ≤ s₁) (k₂ : 0 ≤ s₂) (k₃ : 0 ≤ s₃) :
    0 ≤ PE.eval ![t₁, t₂, t₃, t₄, s₁, s₂, s₃] kerQPE := by
  refine PE.eval_nonneg_of_norm ?_ kerQPE kerQPE_allNonneg
  intro i
  fin_cases i <;> simpa using ‹_›

/-- The syntax tree unfolds **definitionally** to the product form it encodes —
no `ring`, no expansion.  This is what makes the reflection cheap: the only
expensive object, the 24129-monomial expansion, is computed by `PE.norm` inside
the kernel-checked `native_decide`, never written down or normalised by a
tactic. -/
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
