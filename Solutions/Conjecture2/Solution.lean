import BSCAveraging.Conj2

/-!
# Solution: Dikshtein–Ordentlich–Shamai, Conjecture 2 at `p = 0`

The Challenge statement, discharged by `BSCAveraging.conjecture2_p0_holds`
(`BSCAveraging/Conj2.lean`).

The Challenge phrases both the constraints and the bound in terms of the
Z-channels themselves; the library works with the closed forms `zsRate` and
`mzsValue`.  Three identities bridge the two, all in `BSCAveraging/Conj12.lean`:

* `zChan_rate` — the Z-channel's rate on the `U`-side is `zsRate a`;
* `zChan_rate_snd` — its rate on the `V`-side is `zsRate d`;
* `zChan_zChan_value` — the Z/Z pair's `I(U;V)` is `mzsValue a d`.

The library's `V`-side constraint is written against the S-channel of parameter
`d`, whose rate is the same `zsRate d` (`sChan_rate`); that is the fourth
rewrite below.  Finally the library carries a non-degeneracy hypothesis
`∀ u, 0 < marg₁ (jointUX cL) u` on the `U`-side marginal.  It is redundant: a
degenerate marginal forces `I(U;X) = 0` (`mutualInfo_jointUX_eq_zero_of_deg`),
which contradicts `zsRate a ≤ I(U;X)` since `zsRate a > 0` for `a ∈ (0,1)`
(`zsRate_pos`).  It is discharged below, so the Challenge states the conjecture
without it.

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
