import BSCAveraging.CFinish

/-!
# Solution: Dikshtein–Ordentlich–Shamai, Conjecture 1 at `p = 0`

The Challenge statement, discharged by `BSCAveraging.conjecture1_p0_holds`
(`BSCAveraging/CFinish.lean`).

The Challenge phrases both the constraints and the bound in terms of the two
channels themselves; the library works with the closed forms `zsRate` and
`zsValue`.  Two identities in `BSCAveraging/Conj12.lean` bridge them:
`zChan_rate`, identifying the Z-channel's rate with `zsRate a`, and
`zChan_sChan_value`, identifying the Z/S pair's `I(U;V)` with `zsValue a d`.
The `V`-side constraint needs no bridge: the library's `Conjecture1_p0` already
states it against the S-channel of parameter `d`.

## Proof architecture

Four steps, over binary `U, V`:

* **(A)** a maximiser exists — compactness of the parameter box cut by the two
  rate constraints (`maxExistsC`);
* **(B)** an interior optimiser is a BSC pair (`interiorIsBSC_of_noCorner`);
* **(C)** the BSC pair is a saddle, not a maximum (`saddle_iii`, from the
  one-variable core `core_pos`, the kernel lemma and the diagonal reduction);
* **(D)** at a corner the Z/S pair is optimal — the certificate `DFun_nonneg`,
  tight at the Z-channel's atoms (`cornerBound`, `cornerBoundU`).

## Computational content

Step (C) uses two computed checks, both run by the Lean **kernel**.  The
650-cell interval sweep of regime 2 of the core is `decide +kernel`
(`BSCAveraging/CoreSweep.lean`).  The 24129-coefficient Pólya certificate of the
kernel lemma is checked without being expanded: the syntax tree is evaluated at
one big-integer Kronecker point and the coefficients are read off its base-`2^64`
digits (`BSCAveraging/KernelKron.lean`, `KernelCertFast.lean`).  This theorem's
axiom report reads `[propext, Classical.choice, Quot.sound]`.
-/

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

end BSCAveraging.DSIB
