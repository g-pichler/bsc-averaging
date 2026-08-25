import BSCAveraging.Conj2

/-!
# Solution: Dikshtein–Ordentlich–Shamai, Conjecture 2 at `p = 0`

The Challenge statement, discharged by `BSCAveraging.conjecture2_p0_holds`
(`BSCAveraging/Conj2.lean`).

Two differences between the library's `BSCAveraging.Conjecture2_p0` and the
Challenge statement, both eliminated here:

* the library writes the `V`-side rate constraint against the S-channel of
  parameter `d`; `BSCAveraging.sChan_rate` identifies that rate with `zsRate d`;
* the library carries a non-degeneracy hypothesis `∀ u, 0 < marg₁ (jointUX cL) u`
  on the `U`-side marginal.  It is redundant: a degenerate marginal forces
  `I(U;X) = 0` (`mutualInfo_jointUX_eq_zero_of_deg`), which contradicts
  `zsRate a ≤ I(U;X)` since `zsRate a > 0` for `a ∈ (0,1)` (`zsRate_pos`).  It is
  discharged below, so the Challenge states the conjecture without it.

## Proof architecture

The same four steps as Conjecture 1, with the mirror certificate: existence
(`minExistsC`), classification (`interiorIsBSC_of_noCorner`), the BSC pair is
not a minimum (`symmetric_not_min`, for which `F_pp < 0` alone suffices), and
the corner bound `MDFun_nonpos` / `cornerBoundMin`, tight at the Z-channel's
atoms.

This theorem uses **no** computed step: its axioms are exactly `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace BSCAveraging.DSIB

/-- **Conjecture 2 of Dikshtein–Ordentlich–Shamai at `p = 0`, in value form.** -/
theorem conjecture2_p0 (a d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (cL cR : Chan)
    (hU : zsRate a ≤ mutualInfo (jointUX cL))
    (hV : zsRate d ≤ mutualInfo (jointYV cR)) :
    mzsValue a d ≤ mutualInfo (jointUV 0 cL cR) := by
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
