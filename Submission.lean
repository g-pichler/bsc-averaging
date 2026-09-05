import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Hull

/-!
# Three problems about binary channels on a doubly symmetric binary source

This module states, self-contained over Mathlib, the three theorems the
development proves.  Let `(X, Y)` be a **doubly symmetric binary source** with
parameter `p`: two `Bernoulli(1/2)` bits with `P(X ≠ Y) = p`.  Let `U` and `V`
be binary and form the Markov chain `U — X — Y — V`, so that `U` is the output
of a binary channel `cL` on `X` and `V` the output of a binary channel `cR` on
`Y`, the two acting independently.  Everything is in **nats**: the sources'
"1 bit" is `Real.log 2`.

## The three statements

`MO285151.averaged_bsc_maximise_mutual_information` — `conv 𝒜 = conv ℬ` for
every `p ∈ [0,1]`, where `regionA p` is the set of rate triples `(R₀, R₁, R₂)`
with `I(U;X) ≤ R₁`, `I(Y;V) ≤ R₂` and `R₀ ≤ I(U;V)` attainable by *arbitrary*
binary channels, and `regionB p` the same set with both channels *symmetric*.
`regionB p ⊆ regionA p` is immediate; the content is the reverse inclusion
after convexification.  This answers
[MathOverflow 285151](https://mathoverflow.net/questions/285151/do-averaged-binary-symmetric-channels-maximize-mutual-information)
(Georg Pichler, 2017; unanswered there), which the counterexample to the
predecessor question
[MathOverflow 213084](https://mathoverflow.net/questions/213084/do-binary-symmetric-channels-maximize-mutual-information)
leaves open, and it settles Conjecture 5.2 of Pichler, Piantanida and Matz,
*Distributed Information-Theoretic Clustering*, Information and Inference
**11** (2022) 1029–1082.

`DSIB.conjecture1_p0` and `DSIB.conjecture2_p0` — Conjectures 1 and 2 of
Dikshtein, Ordentlich and Shamai (Shitz), *The Double-Sided Information
Bottleneck Function*, Entropy **24**(9):1321 (2022), at `p = 0`, that is
`X = Y`.  Both are stated in optimality form against the conjectured pair,
exhibited here as `Chan` values: no admissible pair exceeds the `I(U;V)` of the
Z/S pair `(zChan a, sChan d)`, and none undercuts that of the Z/Z pair
`(zChan a, zChan d)`.  A Z-channel and an S-channel are the same transition
matrix up to relabelling the input, so what the two conjectures distinguish is
the relative orientation of the two sides: anti-aligned for the maximum,
aligned for the minimum.

## Scope, for all three

The channels are binary on both sides.  For MathOverflow 285151 this is the
setting of the source question, and it costs nothing: Conjecture 5.2 is stated
for a region defined *with* the cardinality bounds `|U| ≤ |X|`, `|V| ≤ |Y|`,
and Proposition 4.3 of the same paper identifies its hull with that of the
unrestricted inner bound.  For the two conjectures it is a genuine
restriction: they are stated for `R(Cu, Cv, 0)`, whose maximisation ranges over
test channels with unrestricted alphabets, and that binary `U` and `V` suffice
for a doubly symmetric binary source is Proposition 3 of the
Dikshtein–Ordentlich–Shamai paper, cited and not formalized here.  Read as
statements about `R(Cu, Cv, 0)`, the two conjecture theorems are conditional on
that published cardinality bound.

Conjecture 2 is stated in its minimisation form, `min I(U;V)` at fixed rates;
the identity `I(U;V) = I(U;X) + I(V;X) − I(X;U,V)` that turns the paper's
maximisation of `I(X;U,V)` into it is the authors' own, Remark 5 of the same
paper, and is likewise not formalized.  Both conjecture theorems are value
statements: the conjectured optimum is not beaten, which is weaker than
uniqueness of the optimiser.  `p = 0` is the only case Conjectures 1 and 2
state; Conjecture 3, which concerns `p` above a threshold, is not addressed.

For `p ∈ {0, 1/2}` the first theorem reproves what is already in the
literature — `p = 0` follows from Corollary 4.1 and Proposition 4.3 of
Pichler–Piantanida–Matz, and at `p = 1/2` the two regions coincide without
convexification.  The new content there is `p ∈ (0, 1/2) ∪ (1/2, 1)`; the
theorem covers `[0,1]` uniformly.

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
