import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Conjecture 2 of Dikshtein–Ordentlich–Shamai, at `p = 0`

This module states, self-contained over Mathlib, Conjecture 2 of

> M. Dikshtein, O. Ordentlich and S. Shamai (Shitz), *The Double-Sided
> Information Bottleneck Function*, Entropy **24**(9):1321 (2022),
> [doi:10.3390/e24091321](https://doi.org/10.3390/e24091321).

## The conjecture, and the form stated here

The paper's setting is a bivariate source `(X, Y)` and the Markov chain
`U — X — Y — V`, with `U` produced from `X` and `V` produced from `Y` by two
independent test channels.  Here `(X, Y)` is a doubly symmetric binary source
with parameter `p`, and `p = 0`, i.e. `X = Y`.  The paper states:

> **Conjecture 2 (Dikshtein–Ordentlich–Shamai).**  The test channels `P_{U|X}`
> and `P_{V|X}` that maximize `I(X;U,V)` are both Z channels.

The paper's own Remark 5 supplies the translation.  Because `U — X — Y — V` is
a Markov chain,

```
I(U;V) = I(U;X) + I(V;X) − I(X; U, V)
```

so at fixed rates `I(X;U) = Cu` and `I(X;V) = Cv` maximizing `I(X;U,V)` is the
same as **minimizing** `I(U;V)`.  The statement below is that minimization
form, and it identifies the minimizing pair as the Z/Z pair, which is the
content of the conjecture.

**The identity itself is not formalized here.**  It is the authors' own
reduction, stated in Remark 5 of the paper and not an inference of this
development, but the module states the minimization problem directly rather
than deriving it; a reader who wants the conjecture in the paper's `I(X;U,V)`
form must supply the identity.  This is the one gap between the paper's wording
and the Lean statement, and it is recorded here deliberately.

## How the statement is phrased

The conjectured optimum is exhibited as an actual pair of channels rather than
as a closed-form number.  `zChan a` is the Z-channel with parameter `a`: a
`2 × 2` transition matrix whose input `false` is transmitted without error, so
that one output letter determines `X`.  The statement then says, of the two
Z-channels `zChan a` and `zChan d` themselves:

* their rates are the constraint — `cL` is admissible when `I(U;X)` is at least
  `I` of `zChan a`, and `cR` when `I(Y;V)` is at least that of `zChan d`;
* their value is the bound — no admissible pair achieves a smaller `I(U;V)`
  than the pair `(zChan a, zChan d)` does.

Nothing in the statement is a closed form, and nothing is specific to this
development: it mentions only `Chan`, the source `dsbs`, the three joint laws,
`mutualInfo`, and the Z-channel's transition matrix.

The Z-channel's rate `I(X;U)` is continuous and strictly increasing in
`a`, running from `0` at `a = 0` to `log 2` at `a = 1`, so as `(a, d)` ranges
over `(0,1)²` the constraint pair ranges over exactly the nondegenerate rate
pairs in `(0, log 2)²`.  Parametrising the constraints by `(a, d)` is therefore
no loss of generality.

A remark on Z versus S.  A Z-channel and an S-channel are the same channel up
to relabelling the *input* alphabet, so what distinguishes a pair is only the
*relative* orientation of its two sides, both of which here see the same `X`.
Conjecture 1's maximiser is the anti-aligned pair (a Z against an S) and
Conjecture 2's minimiser is the aligned one, which may be written as Z against
Z — the form the paper states, and the form used below — or equally as S
against S, flipping both inputs being a symmetry of all three informations.

## Scope, and what is *not* claimed

1. **`p = 0` only** — the case the paper's conjecture states.
2. **Binary `U` and `V`.**  `Chan` is a `2 × 2` row-stochastic matrix.  That
   binary test channels suffice for a binary source is Proposition 3 of the
   same paper (and Proposition 4.3 of Pichler–Piantanida–Matz, IMAIAI **11**
   (2022)); it is *cited, not formalized here*.
3. **Value, not uniqueness.**  The theorem says the Z/Z value is not
   undercut.  It does not claim the Z/Z pair is the *only* minimizer.
4. **The objective translation** described above.

## Conventions

Everything is in **nats** (natural logarithm), so the source's "1 bit" is
`Real.log 2`.
-/

open Real

namespace BSCAveraging

/-! ## Binary channels -/

/-- A binary channel: a `2 × 2` row-stochastic matrix.  `tr i j` is the
probability of output `j` given input `i`. -/
structure Chan where
  /-- Transition probabilities: `tr i j = P(output = j | input = i)`. -/
  tr : Bool → Bool → ℝ
  nonneg : ∀ i j, 0 ≤ tr i j
  sum_one : ∀ i, tr i false + tr i true = 1

/-! ## The doubly symmetric binary source -/

/-- Joint pmf of a doubly symmetric binary source with parameter `p`:
`X, Y ~ Bernoulli(1/2)` and `P(X ≠ Y) = p`. -/
noncomputable def dsbs (p : ℝ) (x y : Bool) : ℝ := if x = y then (1 - p) / 2 else p / 2

/-! ## Entropy and mutual information (nats) -/

/-- Shannon entropy of a distribution on `Bool`, in nats. -/
noncomputable def entropy1 (m : Bool → ℝ) : ℝ := negMulLog (m false) + negMulLog (m true)

/-- Shannon entropy of a distribution on `Bool × Bool`, in nats. -/
noncomputable def entropy2 (q : Bool → Bool → ℝ) : ℝ :=
  negMulLog (q false false) + negMulLog (q false true)
    + negMulLog (q true false) + negMulLog (q true true)

/-- First marginal of a joint distribution on `Bool × Bool`. -/
noncomputable def marg₁ (q : Bool → Bool → ℝ) (u : Bool) : ℝ := q u false + q u true

/-- Second marginal of a joint distribution on `Bool × Bool`. -/
noncomputable def marg₂ (q : Bool → Bool → ℝ) (v : Bool) : ℝ := q false v + q true v

/-- Mutual information of a joint distribution on `Bool × Bool`, in nats:
`I = H(marg₁) + H(marg₂) - H(joint)`. -/
noncomputable def mutualInfo (q : Bool → Bool → ℝ) : ℝ :=
  entropy1 (marg₁ q) + entropy1 (marg₂ q) - entropy2 q

/-! ## The three joint laws of the Markov chain `U — X — Y — V` -/

/-- Joint law of `(U, X)`, where `X ~ Bernoulli(1/2)` and `U` is the output of
`cL` on input `X`. -/
noncomputable def jointUX (cL : Chan) (u x : Bool) : ℝ := cL.tr x u / 2

/-- Joint law of `(Y, V)`, where `Y ~ Bernoulli(1/2)` and `V` is the output of
`cR` on input `Y`. -/
noncomputable def jointYV (cR : Chan) (y v : Bool) : ℝ := cR.tr y v / 2

/-- Joint law of `(U, V)` for the Markov chain `U — X — Y — V`: `(X, Y)` is a
DSBS with parameter `p`, `U` is the output of `cL` on `X`, and `V` is the
output of `cR` on `Y`.  At `p = 0` this is the chain `U — X — V` of the
conjecture. -/
noncomputable def jointUV (p : ℝ) (cL cR : Chan) (u v : Bool) : ℝ :=
  dsbs p false false * cL.tr false u * cR.tr false v
    + dsbs p false true * cL.tr false u * cR.tr true v
    + dsbs p true false * cL.tr true u * cR.tr false v
    + dsbs p true true * cL.tr true u * cR.tr true v

/-! ## The Z-channel -/

/-- The Z-channel with interior atom `a`: input `false` never produces `true`. -/
noncomputable def zChanTr (a : ℝ) (x u : Bool) : ℝ :=
  bif u then (bif x then 2 * a / (1 + a) else 0)
        else (bif x then (1 - a) / (1 + a) else 1)

/-- The Z-channel with parameter `a ∈ (0,1)`. -/
noncomputable def zChan (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) : Chan where
  tr := zChanTr a
  nonneg i j := by
    have h : (0:ℝ) < 1 + a := by linarith
    have h1 : (0:ℝ) ≤ (1 - a) / (1 + a) := by positivity
    have h2 : (0:ℝ) ≤ 2 * a / (1 + a) := by positivity
    cases i <;> cases j <;> simp only [zChanTr, cond_true, cond_false] <;> linarith
  sum_one i := by
    have h : (0:ℝ) < 1 + a := by linarith
    cases i
    · simp only [zChanTr, cond_true, cond_false]; norm_num
    · simp only [zChanTr, cond_true, cond_false]; field_simp; ring

namespace DSIB

/-- **Conjecture 2 of Dikshtein–Ordentlich–Shamai at `p = 0`.**

For a doubly symmetric binary source with `p = 0` (that is, `X = Y`): among all
pairs of binary test channels `cL : X → U` and `cR : Y → V` whose rates are at
least those of the two Z-channels `zChan a` and `zChan d`, none achieves a
smaller `I(U;V)` than the pair `(zChan a, zChan d)` itself.  That is Conjecture
2's assertion that the optimal test channels are both Z channels.

By the paper's Remark 5, `I(U;V) = I(U;X) + I(V;X) − I(X;U,V)`, so at fixed
rates this minimization is the paper's maximization of `I(X;U,V)`; see the
module documentation for that translation and for the other scope
limitations. -/
theorem conjecture2_p0 (a d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (cL cR : Chan)
    (hU : mutualInfo (jointUX (zChan a ha0 ha1)) ≤ mutualInfo (jointUX cL))
    (hV : mutualInfo (jointYV (zChan d hd0 hd1)) ≤ mutualInfo (jointYV cR)) :
    mutualInfo (jointUV 0 (zChan a ha0 ha1) (zChan d hd0 hd1))
      ≤ mutualInfo (jointUV 0 cL cR) := by
  sorry

end DSIB

end BSCAveraging
