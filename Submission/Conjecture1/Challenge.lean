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

`conjecture1_p0` is the value form of that conjecture: at the rate pair
realised by the Z/S pair with parameters `(a, d)`, no admissible pair of binary
channels achieves more than the Z/S value.

* `zsRate a` is the rate `I(X;U)` of the Z-channel with parameter `a`, in closed
  form `(f_e(a) + a·log 2)/(1 + a)`, and it is also the rate `I(Y;V)` of the
  S-channel with parameter `a`.  It is continuous and strictly increasing on
  `[0,1]` with `zsRate 0 = 0` and `zsRate 1 = log 2`, so as `(a, d)` ranges over
  `(0,1)²` the constraint pair `(zsRate a, zsRate d)` ranges over exactly the
  nondegenerate rate pairs in `(0, log 2)²`.  Parametrising the rate constraints
  by `(a, d)` is therefore no loss of generality; it is what makes the
  right-hand side a closed form.
* `zsValue a d` is `I(U;V)` for the Z/S pair with those parameters.

So the statement reads: for all `a, d ∈ (0,1)` and all binary channels `cL, cR`
with `I(U;X) ≤ zsRate a` and `I(Y;V) ≤ zsRate d`, one has
`I(U;V) ≤ zsValue a d`.

## Scope, and what is *not* claimed

Three limitations, all deliberate:

1. **`p = 0` only.**  This is the only case the paper's Conjecture 1 states.
   Conjecture 3 of the same paper, which concerns `p` above a threshold, is not
   addressed here.
2. **Binary `U` and `V`.**  `Chan` is a `2 × 2` row-stochastic matrix, so the
   maximisation is over binary test channels.  That this is no loss of
   generality for a binary source is Proposition 3 of the same paper (and
   Proposition 4.3 of Pichler–Piantanida–Matz, IMAIAI **11** (2022)); it is
   *cited, not formalized here*.  Read as a statement about `R(Cu, Cv, 0)` with
   unrestricted alphabets, the theorem below is therefore conditional on that
   published cardinality reduction.
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

/-! ## The rate and the value of the conjectured optimum -/

/-- `f_e(y) = ∫₀^y artanh`. -/
noncomputable def fe (y : ℝ) : ℝ := ((1 + y) * log (1 + y) + (1 - y) * log (1 - y)) / 2

/-- The rate of a Z-channel with interior atom `a`: `(f_e(a) + a·log 2)/(1+a)`.
It is also the rate of the S-channel with parameter `a`. -/
noncomputable def zsRate (a : ℝ) : ℝ := (fe a + a * log 2) / (1 + a)

/-- The Z/S branch value at `p = 0`, as a function of the two Z-parameters:
`I(U;V)` when the `U`-side is the Z-channel with parameter `a` and the `V`-side
is the S-channel with parameter `d`. -/
noncomputable def zsValue (a d : ℝ) : ℝ :=
  d / (1 + d) * log (1 + a) + (1 - a * d) / ((1 + a) * (1 + d)) * log (1 - a * d)
    + a / (1 + a) * log (1 + d)

namespace DSIB

/-- **Conjecture 1 of Dikshtein–Ordentlich–Shamai at `p = 0`, in value form.**

For a doubly symmetric binary source with `p = 0` (that is, `X = Y`), and for
every pair of binary test channels `cL : X → U` and `cR : Y → V` obeying the
rate constraints `I(U;X) ≤ zsRate a` and `I(Y;V) ≤ zsRate d`, the mutual
information `I(U;V)` does not exceed `zsValue a d`, the value attained by the
Z-channel/S-channel pair with those parameters.

Since `zsRate` is a continuous strictly increasing bijection of `[0,1]` onto
`[0, log 2]`, this covers every nondegenerate rate pair.  See the module
documentation for the three scope limitations: `p = 0`, binary alphabets (the
cardinality reduction is cited, not formalized), and value rather than
uniqueness of the maximiser. -/
theorem conjecture1_p0 (a d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (cL cR : Chan)
    (hU : mutualInfo (jointUX cL) ≤ zsRate a)
    (hV : mutualInfo (jointYV cR) ≤ zsRate d) :
    mutualInfo (jointUV 0 cL cR) ≤ zsValue a d := by
  sorry

end DSIB

end BSCAveraging
