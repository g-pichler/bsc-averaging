import BSCAveraging.Regime1
import BSCAveraging.CoreSweep

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

/-- **The one-variable core of (iii)**: for every `θ > 0`,

```
1/log(cosh 2θ) − 1/(cosh 2θ − 1) − tanh θ/(2θ)  >  0 .
```
-/
theorem core_pos {θ : ℝ} (hθ : 0 < θ) : 0 < F θ := by
  rcases le_or_gt θ (45/100) with h | h
  · exact core_pos_regime1 hθ h
  · rcases le_or_gt θ 3 with h3 | h3
    · refine core_pos_regime2 θ ?_ ?_
      · push_cast; linarith
      · push_cast; linarith
    · exact core_pos_regime3 (le_of_lt h3)


end BSCAveraging.Core
