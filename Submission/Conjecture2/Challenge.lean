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

## What the constants mean

* `zsRate a` is the rate `I(X;U)` of a Z-channel with parameter `a`, in closed
  form `(f_e(a) + a·log 2)/(1 + a)`.  It is continuous and strictly increasing
  on `[0,1]` with `zsRate 0 = 0` and `zsRate 1 = log 2`, so as `(a, d)` ranges
  over `(0,1)²` the rate pair `(zsRate a, zsRate d)` ranges over exactly the
  nondegenerate pairs in `(0, log 2)²`.  Parametrising the constraints by
  `(a, d)` is therefore no loss of generality.
* `mzsValue a d` is `I(U;V)` for the conjectured minimizing Z/Z pair: the
  `U`-side has atoms at `−a` with mass `1/(1+a)` and at `+1` with mass
  `a/(1+a)`, and `phiZ d` is the corresponding atom value against the `V`-side
  Z-channel with parameter `d`.

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

/-! ## The rate and the value of the conjectured optimum -/

/-- `f_e(y) = ∫₀^y artanh`. -/
noncomputable def fe (y : ℝ) : ℝ := ((1 + y) * log (1 + y) + (1 - y) * log (1 - y)) / 2

/-- The rate of a Z-channel with interior atom `a`: `(f_e(a) + a·log 2)/(1+a)`. -/
noncomputable def zsRate (a : ℝ) : ℝ := (fe a + a * log 2) / (1 + a)

/-- `f(z) = (1+z)·log(1+z)`, the mutual-information kernel: at `p = 0` one has
`I(U;V) = E f(S·T)` in the bias coordinates `S`, `T` of the two sides. -/
noncomputable def fFun (z : ℝ) : ℝ := (1 + z) * log (1 + z)

/-- The atom value at `p = 0` against the `V`-side Z-channel `T = (+1, −d)`:
the contribution of a `U`-side atom at bias `s`. -/
noncomputable def phiZ (d s : ℝ) : ℝ :=
  (d / (1 + d)) * fFun s + (1 / (1 + d)) * fFun (-(d * s))

/-- The value of the conjectured optimal pair for the **minimization** problem:
the `U`-side has atoms at `−a` (mass `1/(1+a)`) and `+1` (mass `a/(1+a)`), the
two contacts of the mirror certificate. -/
noncomputable def mzsValue (a d : ℝ) : ℝ :=
  (1 / (1 + a)) * phiZ d (-a) + (a / (1 + a)) * phiZ d 1

namespace DSIB

/-- **Conjecture 2 of Dikshtein–Ordentlich–Shamai at `p = 0`, in value form.**

For a doubly symmetric binary source with `p = 0` (that is, `X = Y`), and for
every pair of binary test channels `cL : X → U` and `cR : Y → V` meeting the
rates `zsRate a ≤ I(U;X)` and `zsRate d ≤ I(Y;V)`, the mutual information
`I(U;V)` is at least `mzsValue a d`, the value attained by the Z/Z pair with
those parameters.

By the paper's Remark 5, `I(U;V) = I(U;X) + I(V;X) − I(X;U,V)`, so at fixed
rates this minimization is the paper's maximization of `I(X;U,V)`; see the
module documentation for that translation and for the other scope
limitations. -/
theorem conjecture2_p0 (a d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (cL cR : Chan)
    (hU : zsRate a ≤ mutualInfo (jointUX cL))
    (hV : zsRate d ≤ mutualInfo (jointYV cR)) :
    mzsValue a d ≤ mutualInfo (jointUV 0 cL cR) := by
  sorry

end DSIB

end BSCAveraging
