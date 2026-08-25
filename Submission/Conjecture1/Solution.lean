import BSCAveraging.CFinish

/-!
# Solution: Dikshtein–Ordentlich–Shamai, Conjecture 1 at `p = 0`

The Challenge statement, discharged by `BSCAveraging.conjecture1_p0_holds`
(`BSCAveraging/CFinish.lean`).

The library states the conjecture as the `Prop` `BSCAveraging.Conjecture1_p0`
(`BSCAveraging/Conj12.lean`), whose `V`-side rate constraint is written against
the S-channel of parameter `d`.  `BSCAveraging.sChan_rate` identifies that rate
with `zsRate d`, which is the form the Challenge uses; the two statements are
therefore the same up to that rewrite.

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

Step (C) uses two computed checks.  The 650-cell interval sweep of regime 2 of
the core is checked by the Lean **kernel** (`BSCAveraging/CoreSweep.lean`).  The
24129-monomial Pólya expansion of the kernel lemma is checked by
`native_decide` (`BSCAveraging/KernelCertFast.lean`).  On Lean v4.32.2 that
mints a per-declaration auxiliary axiom, so this theorem's axiom report reads
`[propext, Classical.choice, Quot.sound,
BSCAveraging.Reflect.kerQPE_allNonneg._native.native_decide.ax_1_1]`.  Comparator
rejects that as a custom axiom, so this Challenge/Solution pair does not yet meet
Palomar's permitted-axiom rule.
-/

namespace BSCAveraging.DSIB

/-- **Conjecture 1 of Dikshtein–Ordentlich–Shamai at `p = 0`, in value form.** -/
theorem conjecture1_p0 (a d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (cL cR : Chan)
    (hU : mutualInfo (jointUX cL) ≤ zsRate a)
    (hV : mutualInfo (jointYV cR) ≤ zsRate d) :
    mutualInfo (jointUV 0 cL cR) ≤ zsValue a d :=
  conjecture1_p0_holds a d ha0 ha1 hd0 hd1 cL cR hU
    (by rw [sChan_rate hd0 hd1]; exact hV)

end BSCAveraging.DSIB
