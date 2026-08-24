import BSCAveraging.Conj12
import BSCAveraging.Exploration.PZero
import BSCAveraging.Exploration.KernelAlgebra

/-! # `Conj12` — exploration companion

The declarations of `BSCAveraging.Conj12` that are **not** used by any of the
three theorems of `BSCAveraging.Basic`.  Section headers are copied from the
main file so the two read in parallel. -/

/-! # Conjectures 1 and 2 of Entropy 24(9):1321, at `p = 0`

`NOTES.md` §7d′ assembles the two conjectures out of four steps:

1. a maximiser exists and is a best response on each side, hence an
   alternating-maximisation fixed point (binary `U,V` suffice, Pichler Prop 4.3);
2. fixed points are the symmetric BSC pair, or have an atom at `±1`
   (`interior_response_symmetric` plus the Λ-symmetry argument of §7c⁗);
3. the BSC pair is a **saddle**, not a maximum — inequality (iii), proved in
   §7f (one-variable core) and §7f‴ (diagonal reduction via the kernel lemma);
4. at the corner the Z/S pair is optimal — `mutualInfo_le_of_sChan`, with the
   tangency of the certificate at the Z-channel's atoms.

Steps 1–3 say: *every admissible pair is dominated by one whose `V`-side is an
S-channel*.  That composite is `CornerDomination` below — the single statement
carrying all the formalisation debt of this file (steps 1 and 2 are paper
arguments; step 3 is proved but partly by certified computation).  Step 4 is
already a Lean theorem, and this file supplies the missing arithmetic link
between it and the conjecture as stated: `certificate_tight`, saying the
certificate's bound at the Z-channel's own rate is *exactly* the Z/S value.

`Conjecture1_p0` and `Conjecture2_p0` are `Prop`s, never assumed. -/

open Real

namespace BSCAveraging

variable {a d : ℝ}

/-! ## The certificate is tight at the Z-channel -/


/-! ## Towards (D): the S-channel family

Two facts every version of `(D)` needs: the S-channel's own rate is exactly
`zsRate`, and `zsRate` is strictly increasing — so the rate hypothesis of `(D)`
pins down `d' ≤ d`. -/


/-! ## Towards (A): continuity and compactness

`Feasible` as first written carries the *open* conditions `0 < marg₁ …` and
`0 < marg₂ …`, so the feasible set is not closed and no compactness argument can
give a maximiser.  The fix is to maximise over the closed set and handle
degeneracy downstream: a null letter makes one of the variables deterministic,
the value is then `0`, and `zsValue_pos` says that is below the target.  The
analytic input is continuity of `mutualInfo`, proved here. -/


/-! ### The optimisation in parameter space -/


/-! ### Degenerate pairs have value zero

A maximiser over the closed feasible set may have a null letter.  Then one of
the variables is deterministic and the value is `0`, which `zsValue_pos` puts
strictly below the target — so the degenerate case is harmless. -/


/-! ## Vocabulary for the decomposition -/


/-! ## (D) is a theorem

A corner `V`-side *is* an S-channel in law: mean-zero plus total mass force the
other bias to `∓d'` and the masses to `(d'/(1+d'), 1/(1+d'))`, with `d' ≤ 1`
because biases lie in `[−1,1]`.  Its atom-value function is then `phiZ d'` up to
the reflection `s ↦ σs`, and the reflection is free: `f_e` is even, so the
certificate transfers with `λ₁` replaced by `σ·λ₁`.

So the corner step needs neither a channel identity nor a degradation argument —
`bestResponse_le_of_certificate` takes an arbitrary `cR`, needing only its
marginals and biases.  `cornerBound` below is `(D)`'s role in the chain, proved
outright, which is why `conjecture1_p0_of_three` needs only (A), (B), (C). -/

section CornerProved


end CornerProved


/-! ## The two conjectures -/


/-- The minimisation counterpart of `CornerDomination`. -/
def CornerDominationMin : Prop :=
  ∀ (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (cL cR : Chan),
    (∀ u, 0 < marg₁ (jointUX cL) u) →
    mutualInfo (jointYV (sChan d hd0 hd1)) ≤ mutualInfo (jointYV cR) →
    mutualInfo (jointUV 0 cL (sChan d hd0 hd1)) ≤ mutualInfo (jointUV 0 cL cR)


/-! ## The four ingredients

`CornerDomination` above bundles steps 1–3 of `NOTES.md` §7d′ into one
statement, and as stated it quantifies over *every* `cR` — which is too strong
to be true: against a fixed BSC `cL` the best `cR` is a BSC, and it beats the
S-channel by Mrs. Gerber's Lemma (`mgl_jensen`).  That is the two-sidedness of
§7e.  The implication `conjecture1_p0_of_cornerDomination` is still valid, but
its hypothesis cannot be proved.

The decomposition below is the honest one: it speaks about **maximisers**, and
splits the debt into four independently attackable statements, each matching one
line of the §7d′ table.  `conjecture1_p0_of_parts` proves the chain. -/

section Parts


/-- **(B) Classification** (§7d′ step 2).  A maximiser is either the symmetric
BSC pair or has an atom at `±1` on the `V`-side.  `interior_response_symmetric`
is the symmetric half; the interior uniqueness is the Λ-symmetry argument of
§7c⁗. -/
def MaxIsBSCorCorner : Prop :=
  ∀ Cu Cv cL cR, IsMaxPairC Cu Cv cL cR →
    (∀ u, 0 < marg₁ (jointUX cL) u) → (∀ v, 0 < marg₂ (jointYV cR) v) →
    BothBSC cL cR ∨ VSideCorner cR


/-! ### Towards (B): best responses and the bitangency bridge

`(B)` says a maximiser is the BSC pair or has a corner `V`-side.  It factors
into two very different pieces.

*The variational bridge.*  A maximiser is a best response on each side
(`IsMaxPairC.bestResponseU` / `…V` below, immediate from the definition).  The
one-sided problem is a linear program over laws of the bias `S`, constrained by
`E[S] = 0` and `E[f_e(S)] ≤ C`, so at an optimum there are multipliers
`(λ₀,λ₁,λ₂)`, `λ₂ ≥ 0`, whose affine function dominates the atom value `φ_T` and
*touches it at both atoms* — value and tangency.  That is `Bitangency` below,
and it is the missing formal step: it needs Lagrange multipliers for the
parametrised family, not just the definition of a maximum.

*The analytic core.*  Given bitangency, `interior_response_symmetric`
(`PZeroSymm.lean`) already proves that against a **symmetric** `T` an interior
bitangent response is symmetric.  What remains on paper is §7c⁗: the
doubly-asymmetric case, via the Λ symmetry and the Green's-function fold. -/

/-- A maximiser is a best response on the `U`-side. -/
theorem IsMaxPairC.bestResponseU {Cu Cv : ℝ} {cL cR : Chan}
    (h : IsMaxPairC Cu Cv cL cR) (cL' : Chan) (h' : mutualInfo (jointUX cL') ≤ Cu) :
    mutualInfo (jointUV 0 cL' cR) ≤ mutualInfo (jointUV 0 cL cR) :=
  h.2 cL' cR ⟨h', h.1.2⟩

/-- A maximiser is a best response on the `V`-side. -/
theorem IsMaxPairC.bestResponseV {Cu Cv : ℝ} {cL cR : Chan}
    (h : IsMaxPairC Cu Cv cL cR) (cR' : Chan) (h' : mutualInfo (jointYV cR') ≤ Cv) :
    mutualInfo (jointUV 0 cL cR') ≤ mutualInfo (jointUV 0 cL cR) :=
  h.2 cL cR' ⟨h.1.1, h'⟩


/-- **The bitangency bridge** (the missing formal step of `(B)`).  At a
maximiser the `U`-side admits multipliers whose affine function dominates the
atom value on `[−1,1]` and touches it at both atoms.  This is the Lagrange
condition for the one-sided linear program; `bestResponseU` is its hypothesis,
and everything after it in §7c‴/§7c⁗ is analysis of the touching points. -/
def Bitangency : Prop :=
  ∀ (Cu Cv : ℝ) (cL cR : Chan), IsMaxPairC Cu Cv cL cR →
    (∀ u, 0 < marg₁ (jointUX cL) u) → (∀ v, 0 < marg₂ (jointYV cR) v) →
    ∃ l₀ l₁ l₂ : ℝ, 0 ≤ l₂ ∧
      (∀ s : ℝ, -1 ≤ s → s ≤ 1 → atomValue cR s ≤ l₀ + l₁ * s + l₂ * fe s) ∧
      (∀ u : Bool, atomValue cR (biasOf (jointUX cL) u)
        = l₀ + l₁ * biasOf (jointUX cL) u + l₂ * fe (biasOf (jointUX cL) u))

/-- **The remaining analytic step of `(B)`**: a bitangent interior pair is the
BSC pair.  For a symmetric `T` this is `interior_response_symmetric`; the
doubly-asymmetric case is §7c⁗, on paper. -/
def InteriorIsBSC : Prop :=
  ∀ (Cu Cv : ℝ) (cL cR : Chan), IsMaxPairC Cu Cv cL cR →
    (∀ u, 0 < marg₁ (jointUX cL) u) → (∀ v, 0 < marg₂ (jointYV cR) v) →
    ¬ VSideCorner cR → BothBSC cL cR

/-- `(B)` **is** `InteriorIsBSC`: the corner case is the other disjunct, and the
degenerate cases are handled separately in `conjecture1_p0_of_two`. -/
theorem maxIsBSCorCorner_of_interior (H : InteriorIsBSC) : MaxIsBSCorCorner := by
  intro Cu Cv cL cR hmax hL hR
  by_cases hc : VSideCorner cR
  · exact Or.inr hc
  · exact Or.inl (H Cu Cv cL cR hmax hL hR hc)


/-! ### Towards (C): the Z-channel and the branch gap

`(C)` says the BSC pair is not a maximiser.  The witness is the Z/S pair at the
same rates, so `(C)` follows from a single inequality between explicit
elementary functions — no inverse functions, no second-order analysis:

```
f_e(s·t) < zsValue a d      whenever  f_e(s) ≤ zsRate a  and  f_e(t) ≤ zsRate d.
```

That is `BranchGap`.  The reduction is `bscNotMax_of_branchGap`, proved here; it
needs the Z-channel as a `Chan`, its rate, and its value against the S-channel. -/


/-- **The branch gap** — the single inequality `(C)` reduces to.  No inverse
functions and no second-order analysis: `f_e` and `zsValue` are explicit. -/
def BranchGap : Prop :=
  ∀ a d s t : ℝ, 0 < a → a < 1 → 0 < d → d < 1 → -1 ≤ s → s ≤ 1 → -1 ≤ t → t ≤ 1 →
    fe s ≤ zsRate a → fe t ≤ zsRate d → fe (s * t) < zsValue a d

/-- **`(C)` reduces to the branch gap.**  If a maximiser were the BSC pair, the
Z/S pair — feasible at exactly those rates, with value `zsValue a d` — would beat
it, contradicting maximality. -/
theorem bscNotMax_of_branchGap (H : BranchGap) : BSCNotMax := by
  intro a d ha0 ha1 hd0 hd1 cL cR hmax hbsc
  obtain ⟨⟨α, hα0, hα1, rfl⟩, β, hβ0, hβ1, rfl⟩ := hbsc
  -- the BSC pair's rate and value, in bias coordinates
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
  -- the Z/S pair is feasible at these rates
  have hfeas : FeasibleC (zsRate a) (zsRate d) (zChan a ha0 ha1) (sChan d hd0 hd1) :=
    ⟨le_of_eq (zChan_rate ha0 ha1), le_of_eq (sChan_rate hd0 hd1)⟩
  have hle := hmax.2 _ _ hfeas
  rw [zChan_sChan_value ha0 ha1 hd0 hd1, hval] at hle
  -- but the branch gap says the opposite
  have h1 : fe (1 - 2 * α) ≤ zsRate a := by rw [← hrU]; exact hmax.1.1
  have h2 : fe (1 - 2 * β) ≤ zsRate d := by rw [← hrV]; exact hmax.1.2
  have := H a d (1 - 2 * α) (1 - 2 * β) ha0 ha1 hd0 hd1 (by linarith) (by linarith)
    (by linarith) (by linarith) h1 h2
  linarith

/-- **Conjecture 1 at `p = 0` from two ingredients.**  `(A)` and `(D)` are
theorems (`maxExistsC`, `cornerBound`); only the classification `(B)` and the
saddle `(C)` remain.  A maximiser exists over the closed feasible set; if it has
a null letter the value is `0`, below `zsValue` by `zsValue_pos`; otherwise it is
not the BSC pair by `(C)`, so by `(B)` its `V`-side is a corner, and
`cornerBound` finishes. -/
theorem conjecture1_p0_of_two (hB : MaxIsBSCorCorner) (hC : BSCNotMax) :
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
    · rcases hB _ _ _ _ hmax hL hR with hbsc | hcorner
      · exact absurd hbsc (hC a d ha0 ha1 hd0 hd1 cL' cR' hmax)
      · have := cornerBound ha0 ha1 hd0 hd1 hL hR hcorner hmax.1.1 hmax.1.2
        linarith
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

end Parts


/-- **Conjecture 2 at `p = 0` follows from `CornerDominationMin`**, by the same
two-step argument as Conjecture 1 with the mirror certificate: the corner
reduction puts an S-channel on the `V`-side, `mutualInfo_ge_of_sChan` bounds
`I(U;V)` from below by `μ₀ + μ₂·Cu`, and `certificate_tight_mirror` identifies
that bound with `mzsValue a d` at `Cu = zsRate a`. -/
theorem conjecture2_p0_of_cornerDominationMin (H : CornerDominationMin) :
    Conjecture2_p0 := by
  intro a d ha0 ha1 hd0 hd1 cL cR hpi hCu hCv
  have hcorner := H d hd0 hd1 cL cR hpi hCv
  have hcert := mutualInfo_ge_of_sChan ha0 ha1 hd0 hd1 hpi hCu
  have htight := certificate_tight_mirror ha0 ha1 hd0 hd1
  linarith

end BSCAveraging
