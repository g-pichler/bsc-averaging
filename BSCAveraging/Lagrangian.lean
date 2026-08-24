import BSCAveraging.SignFlip
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! # The Lagrangian in bias coordinates, and the region `μ ≥ 1`

`NOTES.md` §5h rewrites the Lagrangian using `I(U;V) = I(U;X) − I(U;X|V)`
(valid because `U — X — (Y,V)` is Markov):

```
F = (1−μ)·I(U;X) − I(U;X|V) − ν·I(Y;V) .
```

All three terms are `≤ 0` as soon as `μ ≥ 1`, so `F ≤ 0`, while the symmetric
optimum is always `≥ g(0,0) = 0`.  Hence `J = J_sym` for every `μ ≥ 1` — and,
by the symmetry of the problem, for every `ν ≥ 1`.  So `μ, ν ∈ [0,1)` is WLOG.

This file proves that in **bias coordinates**, where the same statement needs
only the data-processing inequality `E f(δST) ≤ E f_e(S)`, and where that in turn
has a two-line proof:

* `f(z) = (1+z)·log(1+z)` is convex, so on `[−a, a]` it lies below its chord,
  which is `f_e(a) + z·fo(a)/a` (`fFun_le_chord`);
* `δ·s·T` has mean `0` and stays in `[−|s|, |s|]`, so averaging the chord bound
  over `T` gives `E_T f(δsT) ≤ f_e(s)` (`dpi_row`);
* averaging over `S` gives `E f(δST) ≤ E f_e(S)` (`lagrKernel_le`), which is
  exactly `I(U;V) ≤ I(U;X)`.

Everything is stated for two-point laws, which is no loss: `F` is bilinear in
the pair of laws and the extreme points of the mean-zero measures on `[−1,1]`
are the two-point ones (`NOTES.md` §2, §5e).

See `BSCAveraging.Basic`. -/

open Real Set

namespace BSCAveraging

/-! ## `f_e` is even and non-negative -/

lemma fe_neg (y : ℝ) : fe (-y) = fe y := by
  simp only [fe]
  rw [show (1 : ℝ) + -y = 1 - y by ring, show (1 : ℝ) - -y = 1 + y by ring]
  ring

/-- `f(z) = (1+z)·log(1+z)`, so that `I(U;V) = E f(δST)`. -/
noncomputable def fFun (z : ℝ) : ℝ := (1 + z) * log (1 + z)

lemma fFun_eq_fe_add_fo (z : ℝ) : fFun z = fe z + fo z := by
  simp only [fFun, fe, fo]; ring

@[simp] lemma fFun_zero : fFun 0 = 0 := by simp [fFun]

end BSCAveraging
