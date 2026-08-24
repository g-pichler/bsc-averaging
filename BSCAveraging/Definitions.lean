import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Hull

/-! # Definitions: binary channels, the DSBS, entropy and mutual information

The basic objects of the *averaged BSC* problem (MathOverflow 285151):

* `bconv a b = a * (1 - b) + (1 - a) * b`, binary convolution `a ∗ b`;
* `Chan`, a binary channel (a `2 × 2` row-stochastic matrix);
* `bsc a`, the binary symmetric channel with crossover probability `a`;
* `dsbs p`, the joint pmf of a doubly symmetric binary source with parameter
  `p` (both marginals `Bernoulli(1/2)`, `P(X ≠ Y) = p`);
* `entropy1`, `entropy2`, `mutualInfo` for distributions on `Bool` and
  `Bool × Bool`, all in **nats** (natural logarithm);
* the three joint laws `jointUX`, `jointYV`, `jointUV` induced by the Markov
  chain `U — X — Y — V`.

Everything is in nats, so the source's "1 bit" is `Real.log 2` and the region
constraints read `log 2 - h₂ a` rather than `1 - H(a)`.  See
`BSCAveraging.Basic` for the overview.
-/

open Real

namespace BSCAveraging

/-! ## Binary convolution -/

/-- Binary convolution `a ∗ b = a·(1-b) + (1-a)·b`: the crossover probability
of two independent binary symmetric channels in series. -/
def bconv (a b : ℝ) : ℝ := a * (1 - b) + (1 - a) * b

@[inherit_doc] scoped infixl:70 " ⊛ " => bconv

lemma bconv_nonneg {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ a ⊛ b := by
  have h1 : 0 ≤ a * (1 - b) := mul_nonneg ha0 (by linarith)
  have h2 : 0 ≤ (1 - a) * b := mul_nonneg (by linarith) hb0
  unfold bconv; linarith

lemma bconv_le_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    a ⊛ b ≤ 1 := by
  have h : 0 ≤ (1 - a) * (1 - b) + a * b :=
    add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg ha0 hb0)
  unfold bconv; nlinarith

/-! ## Binary channels -/

/-- A binary channel: a `2 × 2` row-stochastic matrix.  `tr i j` is the
probability of output `j` given input `i`. -/
structure Chan where
  /-- Transition probabilities: `tr i j = P(output = j | input = i)`. -/
  tr : Bool → Bool → ℝ
  nonneg : ∀ i j, 0 ≤ tr i j
  sum_one : ∀ i, tr i false + tr i true = 1

/-- Transition matrix of the binary symmetric channel with crossover `a`. -/
noncomputable def bscTr (a : ℝ) (i j : Bool) : ℝ := if i = j then 1 - a else a

/-- The binary symmetric channel with crossover probability `a ∈ [0,1]`. -/
noncomputable def bsc (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : Chan where
  tr := bscTr a
  nonneg i j := by unfold bscTr; split <;> linarith
  sum_one i := by cases i <;> simp [bscTr]

@[simp] lemma bsc_tr (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : (bsc a ha0 ha1).tr = bscTr a := rfl

/-- The completely useless channel (crossover `1/2`). -/
noncomputable def uselessChan : Chan := bsc (1 / 2) (by norm_num) (by norm_num)

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

@[simp] lemma h2_zero : h2 0 = 0 := by simp [h2]

@[simp] lemma h2_one : h2 1 = 0 := by simp [h2]

@[simp] lemma h2_half : h2 (1 / 2 : ℝ) = log 2 := by
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  simp only [h2, negMulLog, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hlog]
  ring

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

@[simp] lemma bconv_zero_right (a : ℝ) : a ⊛ (0 : ℝ) = a := by unfold bconv; ring

/-- A channel with crossover `1/2` destroys everything: `a ∗ (1/2) = 1/2`. -/
@[simp] lemma bconv_half_right (a : ℝ) : a ⊛ (1 / 2 : ℝ) = 1 / 2 := by unfold bconv; ring
@[simp] lemma bconv_half_left (b : ℝ) : (1 / 2 : ℝ) ⊛ b = 1 / 2 := by unfold bconv; ring

end BSCAveraging
