import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Conjecture 1 of Dikshtein–Ordentlich–Shamai, at `p = 0`

This module states, self-contained over Mathlib, Conjecture 1 of

> M. Dikshtein, O. Ordentlich and S. Shamai (Shitz), *The Double-Sided
> Information Bottleneck Function*, Entropy **24**(9):1321 (2022),
> [doi:10.3390/e24091321](https://doi.org/10.3390/e24091321).

## The double-sided information bottleneck function

For a bivariate source `(X, Y)` the paper studies

```
R(Cu, Cv) = max { I(U;V) : U — X — Y — V,  I(X;U) ≤ Cu,  I(Y;V) ≤ Cv }.
```

Here `(X, Y)` is a doubly symmetric binary source with parameter `p`: two
`Bernoulli(1/2)` bits with `P(X ≠ Y) = p`.  Conjecture 1 concerns the extreme
case `p = 0`, i.e. `X = Y`:

> **Conjecture 1 (Dikshtein–Ordentlich–Shamai).**  Let `X = Y`, i.e. `p = 0`.
> The optimal test channels `P_{U|X}` and `P_{V|X}` that achieve `R(Cu, Cv, 0)`
> are a Z-channel and an S-channel respectively.

A **Z-channel** with parameter `a` and the **S-channel** with parameter `d` are
the two binary channels with one deterministic row; they are the corner
channels of the binary channel polytope at a given rate.

## What is stated here

The conjectured optimum is exhibited as an actual pair of channels rather than
as a closed-form number.  `zChan a` and `sChan d` are the two transition
matrices themselves: `zChan a` has `P(U=1 | X=0) = 0` and `sChan d` has
`P(V=0 | Y=1) = 0`, one vanishing crossover each, and opposite ones.  The
statement then says, of that pair:

* their rates are the constraint — `cL` is admissible when `I(U;X)` does not
  exceed `I` of `zChan a`, and `cR` when `I(Y;V)` does not exceed that of
  `sChan d`;
* their value is the bound — no admissible pair achieves a larger `I(U;V)`
  than the pair `(zChan a, sChan d)` does.

Nothing in the statement is a closed form, and nothing is specific to this
development: it mentions only `Chan`, the source `dsbs`, the three joint laws,
`mutualInfo`, and the two transition matrices.

The two channels share one rate function, continuous and strictly increasing in
the parameter, running from `0` at `0` to `log 2` at `1`, so as `(a, d)` ranges
over `(0,1)²` the constraint pair ranges over exactly the nondegenerate rate
pairs in `(0, log 2)²`.  Parametrising the rate constraints by `(a, d)` is
therefore no loss of generality.

A remark on Z versus S.  The two are the same channel up to relabelling the
*input* alphabet, so what distinguishes a pair is only the *relative*
orientation of its two sides, both of which here see the same `X`.  Writing the
maximiser as a Z against an S is exactly the statement that the two sides are
anti-aligned: `cL` has `P(U=1 | X=0) = 0` while `cR` has `P(V=0 | Y=1) = 0`, so
it is opposite crossovers that vanish on the two sides.

## Scope, and what is *not* claimed

Three limitations, all deliberate:

1. **`p = 0` only.**  This is the only case the paper's Conjecture 1 states.
   Conjecture 3 of the same paper, which concerns `p` above a threshold, is not
   addressed here.
2. **Binary `U` and `V`.**  `Chan` is a `2 × 2` row-stochastic matrix, so the
   maximisation is over binary test channels.  Conjecture 1 is a statement
   about `R(Cu, Cv, 0)`, whose maximisation ranges over test channels with
   unrestricted alphabets; that binary `U` and `V` suffice for a DSBS is
   Proposition 3 of the same paper, *cited, not formalized here*.  Read as a
   statement about `R(Cu, Cv, 0)`, the theorem below is therefore conditional
   on that published cardinality reduction.
3. **Value, not uniqueness.**  The theorem says that the Z/S value is not
   exceeded.  It does not claim that the Z/S pair is the *only* maximiser.

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

/-! ## The two corner channels -/

/-- The Z-channel with interior atom `a`: the crossover `P(U=1 | X=0)` vanishes,
`tr false true = 0`. -/
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

/-- Transition matrix of the S-channel with parameter `d`: the *other*
crossover vanishes, `P(V=0 | Y=1) = 0`, i.e. `tr true false = 0`. -/
noncomputable def sChanTr (d : ℝ) (y v : Bool) : ℝ :=
  bif y then (bif v then 1 else 0) else (bif v then (1 - d) / (1 + d) else 1 - (1 - d) / (1 + d))

/-- The S-channel with parameter `d ∈ (0,1)`. -/
noncomputable def sChan (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) : Chan where
  tr := sChanTr d
  nonneg i j := by
    have h : (0:ℝ) < 1 + d := by linarith
    have h1 : (1 - d) / (1 + d) ≤ 1 := by rw [div_le_one h]; linarith
    have h2 : (0:ℝ) ≤ (1 - d) / (1 + d) := by positivity
    cases i <;> cases j <;> simp only [sChanTr, cond_true, cond_false] <;> linarith
  sum_one i := by
    have h : (1:ℝ) + d ≠ 0 := by positivity
    cases i <;> simp only [sChanTr, cond_true, cond_false] <;> ring

namespace DSIB

/-- **Conjecture 1 of Dikshtein–Ordentlich–Shamai at `p = 0`.**

For a doubly symmetric binary source with `p = 0` (that is, `X = Y`): among all
pairs of binary test channels `cL : X → U` and `cR : Y → V` whose rates do not
exceed those of the Z-channel `zChan a` and the S-channel `sChan d`, none
achieves a larger `I(U;V)` than the pair `(zChan a, sChan d)` itself.  That is
Conjecture 1's assertion that the optimal test channels are a Z-channel and an
S-channel.

See the module documentation for the three scope limitations: `p = 0`, binary
alphabets (the cardinality reduction is cited, not formalized), and value
rather than uniqueness of the maximiser. -/
theorem conjecture1_p0 (a d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (cL cR : Chan)
    (hU : mutualInfo (jointUX cL) ≤ mutualInfo (jointUX (zChan a ha0 ha1)))
    (hV : mutualInfo (jointYV cR) ≤ mutualInfo (jointYV (sChan d hd0 hd1))) :
    mutualInfo (jointUV 0 cL cR)
      ≤ mutualInfo (jointUV 0 (zChan a ha0 ha1) (sChan d hd0 hd1)) := by
  sorry

end DSIB

end BSCAveraging
