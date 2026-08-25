import BSCAveraging.Main

/-!
# Solution: MathOverflow 285151

The Challenge statement, discharged by `BSCAveraging.averaged_bsc_maximise_mutual_information`
from `BSCAveraging/Main.lean`.  Every definition occurring in the statement is
the one defined in `BSCAveraging/Definitions.lean` and `BSCAveraging/Regions.lean`,
which the Challenge reproduces verbatim.

The proof is the whole `BSCAveraging` development; `BSCAveraging/Main.lean` is
its road map.
-/

namespace BSCAveraging.MO285151

/-- **Averaged binary symmetric channels maximize mutual information.** -/
theorem averaged_bsc_maximise_mutual_information {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    convexHull ℝ (regionA p) = convexHull ℝ (regionB p) :=
  BSCAveraging.averaged_bsc_maximise_mutual_information hp0 hp1

end BSCAveraging.MO285151
