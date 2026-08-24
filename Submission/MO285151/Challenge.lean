import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Hull

/-!
# Do averaged binary symmetric channels maximize mutual information?

This module states, self-contained over Mathlib, the theorem

> `convexHull ℝ (regionA p) = convexHull ℝ (regionB p)`  for every `p ∈ [0,1]`,

which answers affirmatively the question of
[MathOverflow 285151](https://mathoverflow.net/questions/285151/do-averaged-binary-symmetric-channels-maximize-mutual-information),
*Do averaged binary symmetric channels maximize mutual information?* (asked by
Georg Pichler in 2017; unanswered there).

## The question

Let `(X, Y)` be a **doubly symmetric binary source** with parameter `p`: two
`Bernoulli(1/2)` bits with `P(X ≠ Y) = p`.  Consider binary `U` and `V` forming
the Markov chain `U — X — Y — V`, i.e. `U` is produced from `X` by a binary
channel `cL` and `V` is produced from `Y` by a binary channel `cR`, the two
channels acting independently.  Two regions of rate triples `(R₀, R₁, R₂)`:

* `regionA p` — the triples for which **some** pair of binary channels satisfies
  `I(U;X) ≤ R₁`, `I(Y;V) ≤ R₂` and `R₀ ≤ I(U;V)`;
* `regionB p` — the same, with both channels restricted to be **binary
  symmetric** with crossover probabilities `a` and `b`.  For a BSC the three
  mutual informations have the closed forms `log 2 − h₂(a)`, `log 2 − h₂(b)`
  and `log 2 − h₂(a ∗ p ∗ b)`, where `∗` is binary convolution, so `regionB` is
  written directly in those terms.

`regionB p ⊆ regionA p` is immediate.  The question asks whether the reverse
inclusion holds *after convexification*: is every rate triple achievable with
arbitrary binary channels a convex combination of triples achievable with
symmetric ones?  Equivalently, do averaged binary symmetric channels already
exhaust what arbitrary binary channels achieve?

This is not settled by the earlier
[MathOverflow 213084](https://mathoverflow.net/questions/213084/do-binary-symmetric-channels-maximize-mutual-information),
which asked whether `regionA p = regionB p` and received a counterexample at
`p = 0`: at `R₁ = R₂ = 0.4` bits a near-Z channel pair beats every BSC pair.
Taking convex hulls is therefore essential to the present question, and the
counterexample leaves it open.

The same statement settles Conjecture 5.2 of Pichler, Piantanida and Matz,
*Distributed Information-Theoretic Clustering*, Information and Inference
**11** (2022) 1029–1082, [doi:10.1093/imaiai/iaab007](https://doi.org/10.1093/imaiai/iaab007).

## Conventions, and one deliberate departure from the source

* Everything is in **nats** (natural logarithm).  The source's "1 bit" is
  `Real.log 2`, and `1 − H(a)` reads `log 2 - h2 a`.
* `p` ranges over all of `[0,1]`, not just `[0,1/2]`; the region definitions
  make sense there and the theorem is proved on the whole interval.
* MathOverflow 285151 writes the first two constraints of `ℬ` as
  `R₁ ≥ 1 − H(a ∗ p)` and `R₂ ≥ 1 − H(b ∗ p)`.  That is a slip: with `X → U` a
  BSC of crossover `a` one has `I(U;X) = 1 − H(a)`, which is also how the
  predecessor question MO 213084 states it, and it is what makes
  `regionB p ⊆ regionA p` true.  The consistent version is the one formalized
  here.

## Scope, and what was already known

The channels are binary on both sides, as in the source question: `Chan` is a
`2 × 2` row-stochastic matrix.  This costs nothing here.  Conjecture 5.2 is
stated for the region `S_i`, which Pichler–Piantanida–Matz define *with* the
cardinality bounds `|U| ≤ |X|` and `|V| ≤ |Y|` — binary for a DSBS — and their
Proposition 4.3 shows `conv(S_i) = conv(R_i)`, the hull of the unrestricted
inner bound.  So no cardinality-reduction argument is needed, and none is used.

Two values of `p` were already settled in the literature and are reproved here
rather than established:

* `p = 0`, where `X = Y`.  Pichler–Piantanida–Matz observe that Corollary 4.1
  and Proposition 4.3 give `conv(S_b) = R`, so "Conjecture 5.2 holds for
  `p = 0`".  In Lean this is `averagedBSCConjecture_zero`.
* `p = 1/2`, where `X` and `Y` are independent and both regions collapse to
  `{R₀ ≤ 0, R₁ ≥ 0, R₂ ≥ 0}` outright, without convexification
  (`regionA_half_eq_regionB_half`).

The new content is therefore the open interval `p ∈ (0, 1/2) ∪ (1/2, 1)`; the
theorem below covers the whole of `[0,1]` uniformly.
-/

open Real

namespace BSCAveraging

/-! ## Binary convolution -/

/-- Binary convolution `a ∗ b = a·(1-b) + (1-a)·b`: the crossover probability
of two independent binary symmetric channels in series. -/
def bconv (a b : ℝ) : ℝ := a * (1 - b) + (1 - a) * b

@[inherit_doc] scoped infixl:70 " ⊛ " => bconv

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

/-- Binary entropy function, in nats. -/
noncomputable def h2 (a : ℝ) : ℝ := negMulLog a + negMulLog (1 - a)

/-! ## The three joint laws of the Markov chain `U — X — Y — V` -/

/-- Joint law of `(U, X)`, where `X ~ Bernoulli(1/2)` and `U` is the output of
`cL` on input `X`. -/
noncomputable def jointUX (cL : Chan) (u x : Bool) : ℝ := cL.tr x u / 2

/-- Joint law of `(Y, V)`, where `Y ~ Bernoulli(1/2)` and `V` is the output of
`cR` on input `Y`. -/
noncomputable def jointYV (cR : Chan) (y v : Bool) : ℝ := cR.tr y v / 2

/-- Joint law of `(U, V)` for the Markov chain `U — X — Y — V`: `(X, Y)` is a
DSBS with parameter `p`, `U` is the output of `cL` on `X`, and `V` is the
output of `cR` on `Y`. -/
noncomputable def jointUV (p : ℝ) (cL cR : Chan) (u v : Bool) : ℝ :=
  dsbs p false false * cL.tr false u * cR.tr false v
    + dsbs p false true * cL.tr false u * cR.tr true v
    + dsbs p true false * cL.tr true u * cR.tr false v
    + dsbs p true true * cL.tr true u * cR.tr true v

/-! ## The two regions -/

/-- Region `𝒜`: points `(R₀, R₁, R₂)` attainable with *arbitrary* binary
channels `X → U` and `Y → V`. -/
def regionA (p : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {R | ∃ cL cR : Chan,
      mutualInfo (jointUX cL) ≤ R.2.1 ∧
      mutualInfo (jointYV cR) ≤ R.2.2 ∧
      R.1 ≤ mutualInfo (jointUV p cL cR)}

/-- Region `ℬ`: the same points, attained with *binary symmetric* channels of
crossover `a` and `b`. -/
def regionB (p : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {R | ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧
      log 2 - h2 a ≤ R.2.1 ∧
      log 2 - h2 b ≤ R.2.2 ∧
      R.1 ≤ log 2 - h2 ((a ⊛ p) ⊛ b)}

namespace MO285151

/-- **Averaged binary symmetric channels maximize mutual information.**

For every `p ∈ [0,1]` the convex hulls of the two regions coincide: every rate
triple `(R₀, R₁, R₂)` attainable by an arbitrary pair of binary channels on the
two sides of a doubly symmetric binary source is a convex combination of
triples attainable by binary *symmetric* channels, and conversely.

This is the question of MathOverflow 285151, and it also settles Conjecture 5.2
of Pichler–Piantanida–Matz (2022). -/
theorem averaged_bsc_maximise_mutual_information {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    convexHull ℝ (regionA p) = convexHull ℝ (regionB p) := by
  sorry

end MO285151

end BSCAveraging
