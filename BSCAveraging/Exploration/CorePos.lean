import BSCAveraging.CorePos

/-! # `CorePos` — exploration companion

The declarations of `BSCAveraging.CorePos` that are **not** used by any of the
three theorems of `BSCAveraging.Basic`.  Section headers are copied from the
main file so the two read in parallel. -/

/-! # The one-variable core of (iii), on all of `(0, ∞)`

`NOTES.md` §7f–§7f¹².  The three regimes:

* `(0, 0.45]` — `core_pos_regime1`, by the log-free reduction plus a polynomial
  certificate (`Regime1.lean`);
* `[0.45, 3]` — `core_pos_regime2`, by the centred interval sweep over 650 cells
  (`CoreSweep.lean`);
* `[3, ∞)` — `core_pos_regime3`, by elementary exponential bounds
  (`CoreDeriv.lean`).

Together they give the core of the saddle inequality (iii) on the whole
half-line. -/

namespace BSCAveraging.Core


/-- The same, in the `tanh` form of `NOTES.md` §7f. -/
theorem core_pos' {θ : ℝ} (hθ : 0 < θ) :
    Real.tanh θ / (2 * θ)
      < 1 / Real.log (Real.cosh (2 * θ)) - 1 / (Real.cosh (2 * θ) - 1) := by
  have h := core_pos hθ
  rw [F_eq hθ] at h
  linarith

end BSCAveraging.Core
