import BSCAveraging.SignFlip
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! # `f(z) = (1+z)·log(1+z)`, and the parity of `f_e`

`NOTES.md` §5h rewrites the Lagrangian using `I(U;V) = I(U;X) − I(U;X|V)`
(valid because `U — X — (Y,V)` is Markov):

```
F = (1−μ)·I(U;X) − I(U;X|V) − ν·I(Y;V) .
```

In bias coordinates `I(U;V) = E f(δST)` for `f(z) = (1+z)·log(1+z)`, and what the
proof needs of `f` is its splitting into the even part `f_e` and the odd part
`fo` of `SignFlip.lean`.  This file is that small piece:

* `fe_neg` — `f_e` is even;
* `fFun` — the definition of `f`;
* `fFun_eq_fe_add_fo`, `fFun_zero` — the decomposition `f = f_e + fo`, and `f(0) = 0`.

The Lagrangian itself is bounded in `FixedPoint.lean`, through the two-point form
and its four corner values, with no hypothesis on `μ` or `ν`; the region `μ ≥ 1`
therefore needs no separate treatment and none is carried out here.  The earlier
route — the chord bound on `f` and the row-wise data-processing inequality
(`fFun_le_chord`, `dpi_row`, `lagrKernel_le`) — is proved in
`Exploration/Misc.lean` and is used by none of the three theorems.

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
