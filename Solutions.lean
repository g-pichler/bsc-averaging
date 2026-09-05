import BSCAveraging.Main
import BSCAveraging.CFinish
import BSCAveraging.Conj2

/-!
# Solution: the three Challenge statements of `Submission.lean`

Each statement is discharged from the library, whose definitions the Challenge
reproduces verbatim:

* `MO285151.averaged_bsc_maximise_mutual_information` by
  `BSCAveraging.averaged_bsc_maximise_mutual_information` (`BSCAveraging/Main.lean`);
* `DSIB.conjecture1_p0` by `conjecture1_p0_holds` (`BSCAveraging/CFinish.lean`);
* `DSIB.conjecture2_p0` by `conjecture2_p0_holds` (`BSCAveraging/Conj2.lean`).

The two conjecture Challenges phrase both the constraints and the bound in
terms of the channels themselves, where the library works with the closed forms
`zsRate`, `zsValue` and `mzsValue`.  The bridging identities are in
`BSCAveraging/Conj12.lean`: `zChan_rate` and `zChan_rate_snd` for the rates,
`zChan_sChan_value` and `zChan_zChan_value` for the two values, and
`sChan_rate`, the S-channel of parameter `d` having the same rate as the
Z-channel of parameter `d`.  The library's Conjecture 2 carries a
non-degeneracy hypothesis on the `U`-side marginal; it is redundant — a
degenerate marginal forces `I(U;X) = 0` (`mutualInfo_jointUX_eq_zero_of_deg`),
contradicting `zsRate a ≤ I(U;X)` with `zsRate a > 0` (`zsRate_pos`) — and is
discharged below, so the Challenge states the conjecture without it.

## Proof architecture

MathOverflow 285151 turns on the two-point Lagrangian bound
(`lagrTwoPoint_le_of_corner_bounds_closed`) and the convex geometry that lifts
it to an inclusion of hulls.  Both conjectures follow the same four steps over
binary `U, V`: a maximiser or minimiser exists (`maxExistsC`, `minExistsC`); an
interior optimiser is a BSC pair (`interiorIsBSC_of_noCorner`); that pair is
not the optimum (`saddle_iii` for the maximum, `symmetric_not_min` for the
minimum); and at a corner the conjectured pair is optimal (`cornerBound`,
`cornerBoundMin`).

## Computational content

Only the maximum needs computation, in the saddle step, and both checks run in
the Lean **kernel**: an 88-cell interval sweep of the middle regime of the
one-variable core (`decide +kernel`, `BSCAveraging/CoreSweep.lean`), and the
24129-coefficient Pólya certificate of the kernel lemma, checked without being
expanded by evaluating its syntax tree at one big-integer Kronecker point and
reading the coefficients off its base-`2^64` digits
(`BSCAveraging/KernelKron.lean`, `KernelCertFast.lean`).  All three theorems
report exactly `[propext, Classical.choice, Quot.sound]`.

-/

namespace BSCAveraging.MO285151

/-- **Averaged binary symmetric channels maximize mutual information.** -/
theorem averaged_bsc_maximise_mutual_information {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    convexHull ℝ (regionA p) = convexHull ℝ (regionB p) :=
  BSCAveraging.averaged_bsc_maximise_mutual_information hp0 hp1

end BSCAveraging.MO285151

namespace BSCAveraging.DSIB

/-- **Conjecture 1 of Dikshtein–Ordentlich–Shamai at `p = 0`, in value form.** -/
theorem conjecture1_p0 (a d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (cL cR : Chan)
    (hU : mutualInfo (jointUX cL) ≤ mutualInfo (jointUX (zChan a ha0 ha1)))
    (hV : mutualInfo (jointYV cR) ≤ mutualInfo (jointYV (sChan d hd0 hd1))) :
    mutualInfo (jointUV 0 cL cR)
      ≤ mutualInfo (jointUV 0 (zChan a ha0 ha1) (sChan d hd0 hd1)) := by
  rw [zChan_rate ha0 ha1] at hU
  rw [zChan_sChan_value ha0 ha1 hd0 hd1]
  exact conjecture1_p0_holds a d ha0 ha1 hd0 hd1 cL cR hU hV

/-- **Conjecture 2 of Dikshtein–Ordentlich–Shamai at `p = 0`.** -/
theorem conjecture2_p0 (a d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (cL cR : Chan)
    (hU : mutualInfo (jointUX (zChan a ha0 ha1)) ≤ mutualInfo (jointUX cL))
    (hV : mutualInfo (jointYV (zChan d hd0 hd1)) ≤ mutualInfo (jointYV cR)) :
    mutualInfo (jointUV 0 (zChan a ha0 ha1) (zChan d hd0 hd1))
      ≤ mutualInfo (jointUV 0 cL cR) := by
  rw [zChan_rate ha0 ha1] at hU
  rw [zChan_rate_snd hd0 hd1] at hV
  rw [zChan_zChan_value ha0 ha1 hd0 hd1]
  have hpi : ∀ u, 0 < marg₁ (jointUX cL) u := by
    intro u
    rcases lt_or_eq_of_le (show (0:ℝ) ≤ marg₁ (jointUX cL) u by
      simp only [marg₁, jointUX]
      have := cL.nonneg false u; have := cL.nonneg true u; linarith) with h | h
    · exact h
    · exact absurd (mutualInfo_jointUX_eq_zero_of_deg h.symm)
        (by linarith [zsRate_pos ha0 ha1])
  exact conjecture2_p0_holds a d ha0 ha1 hd0 hd1 cL cR hpi hU
    (by rw [sChan_rate hd0 hd1]; exact hV)

end BSCAveraging.DSIB
