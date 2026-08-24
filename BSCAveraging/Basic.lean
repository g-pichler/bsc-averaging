import BSCAveraging.Zero
import BSCAveraging.Rigidity
import BSCAveraging.SignFlip
import BSCAveraging.Lagrangian
import BSCAveraging.BiasCoords
import BSCAveraging.FixedPoint
import BSCAveraging.Closedness
import BSCAveraging.Bridge
import BSCAveraging.Assembly
import BSCAveraging.Main
import BSCAveraging.BestResponse
import BSCAveraging.PZero
import BSCAveraging.KernelAlgebra
import BSCAveraging.Conj12
import BSCAveraging.Interval
import BSCAveraging.CoreDeriv
import BSCAveraging.CoreSweep
import BSCAveraging.CorePos
import BSCAveraging.Diagonal
import BSCAveraging.MixtureRep
import BSCAveraging.KernelBridge
import BSCAveraging.DiagReduction
import BSCAveraging.SaddleIII
import BSCAveraging.LogCosh
import BSCAveraging.TwoAtom
import BSCAveraging.BitangencyBridge
import BSCAveraging.KKT
import BSCAveraging.TwoAtomChan
import BSCAveraging.BFinish
import BSCAveraging.BFinishV
import BSCAveraging.CFinish
import BSCAveraging.Conj2

/-! # `BSCAveraging`: the proof

A Lean 4 / Mathlib formalization built around

> [MathOverflow 285151](https://mathoverflow.net/questions/285151),
> *Do averaged binary symmetric channels maximize mutual information?*
> (Georg Pichler, 2017)

and the two conjectures of

> Dikshtein, Ordentlich, Shamai, *The Double-Sided Information Bottleneck
> Function*, Entropy **24**(9):1321 (2022).

## The three theorems

```lean
averaged_bsc_maximise_mutual_information :        -- MO 285151, every p ∈ [0,1]
  convexHull ℝ (regionA p) = convexHull ℝ (regionB p)
conjecture1_p0_holds : Conjecture1_p0             -- Entropy 24(9):1321, Conj. 1, p = 0
conjecture2_p0_holds : Conjecture2_p0             -- Entropy 24(9):1321, Conj. 2, p = 0
```

The first also settles Conjecture 5.2 of Pichler–Piantanida–Matz, *Distributed
Information-Theoretic Clustering*, IMAIAI **11** (2022).  `Main.lean` is the
road map for it.

The two Entropy conjectures are proved by the same four steps, over binary
`U, V` (Pichler Prop 4.3):

* **(A)** an optimiser exists — compactness of the parameter box cut by the two
  rate constraints (`maxExistsC`, `minExistsC`);
* **(B)** an interior optimiser is a BSC pair — the Green identity, the fold,
  `(♦)`, bitangency and 2-D KKT of `NOTES.md` §7c⁗.  KKT for a maximiser under
  `R ≤ C` and a minimiser under `R ≥ C` have the same form `∇V = λ∇R`, `λ ≥ 0`,
  so the step is stated once, for `OptPairC` (`interiorIsBSC_of_noCorner`);
* **(C)** the BSC pair is a saddle, not an optimum.  For the maximisation this
  is the indefinite Hessian direction, i.e. the saddle inequality `(iii)` —
  `saddle_iii`, from the one-variable core `core_pos`, the kernel lemma and the
  diagonal reduction.  For the minimisation `F_pp < 0` alone suffices
  (`symmetric_not_max`, `symmetric_not_min`);
* **(D)** at a corner the Z/S resp. Z/Z pair is optimal — the certificates
  `DFun_nonneg` and `MDFun_nonpos`, tight at the Z-channel's atoms
  (`cornerBound`, `cornerBoundMin`).  The `U`-side mirrors are the side-swap,
  since `zsValue` and `mzsValue` are symmetric.

## Axioms

Everything here is `sorry`-free.  `averaged_bsc_maximise_mutual_information`,
`conjecture2_p0_holds` and all of `(A)`, `(B)`, `(D)` depend only on `propext`,
`Classical.choice`, `Quot.sound`.  `conjecture1_p0_holds` additionally depends
on exactly one further axiom, reached through `saddle_iii`: the 24129-monomial
Pólya expansion of the kernel lemma, whose coefficient check runs under
`native_decide`.  On Lean v4.32.2 `native_decide` mints a *per-declaration
auxiliary axiom* rather than citing `Lean.ofReduceBool`, so the axiom report
names it `BSCAveraging.Reflect.kerQPE_allNonneg._native.native_decide.ax_1_1`.  The other computed step, the 650-cell interval sweep of
regime 2 of the core, is checked by the **kernel** (`CoreSweep.lean`).

## Layout

This module imports exactly the transitive dependency closure of the three
theorems.  Everything else that was proved along the way — the calibration
dumps, the concave-envelope and best-response variants, the alternative
certificates, and the unused parts of each proof file — lives in
`BSCAveraging.Exploration`, and is `sorry`-free too. -/

namespace BSCAveraging

-- Entropy and mutual information
#print axioms mutualInfo_nonneg
#print axioms h2_le_log_two
#print axioms mutualInfo_dsbs
#print axioms mutualInfo_jointUX_nonneg
#print axioms mutualInfo_jointYV_nonneg
-- Binary symmetric channels in series
#print axioms jointUV_bsc
#print axioms mutualInfo_jointUX_bsc
#print axioms mutualInfo_jointYV_bsc
#print axioms mutualInfo_jointUV_bsc
-- The regions
#print axioms regionB_mono
#print axioms regionB_subset_regionA
#print axioms convexHull_regionB_subset
#print axioms averagedBSCConjecture_iff
-- Data processing
#print axioms log_sum_two
#print axioms mutualInfo_compose_le
#print axioms mutualInfo_transpose
#print axioms mutualInfo_jointUV_le_jointUX
#print axioms mutualInfo_jointUV_le_jointYV
#print axioms regionA_fst_le_snd_fst
#print axioms regionA_fst_le_snd_snd
-- Mirror symmetry (the S -> -S flip; see NOTES.md sec.3b)
#print axioms mutualInfo_flip₂
#print axioms mutualInfo_jointUX_mirror
#print axioms mutualInfo_jointUV_mirror
-- The outer bound
#print axioms mutualInfo_jointUV_le_source
-- The degenerate case p = 0
#print axioms regionA_zero_subset_convexHull
#print axioms averagedBSCConjecture_zero
-- The degenerate case p = 1/2
#print axioms mutualInfo_jointUV_half
#print axioms regionA_half
#print axioms regionB_half
#print axioms regionA_half_eq_regionB_half
#print axioms averagedBSCConjecture_half
-- Local rigidity at symmetric fixed points (see NOTES.md sec.5d)
#print axioms self_lt_artanh
#print axioms hasDerivAt_artanh
-- The global sign flip (see NOTES.md sec.5e)
#print axioms artanh_div_strictMonoOn
#print axioms fo_sub_mul_deriv
#print axioms MFun_strictMonoOn
#print axioms wFun_mixed_diff_pos
#print axioms omegaTwoPoint_eq
#print axioms omegaTwoPoint_neg
-- The bias parametrization bridge (NOTES.md sec.6, route 6)
#print axioms negMulLog_row
#print axioms jointUV_eq_kernel
#print axioms rho_bias_sum_zero
#print axioms pi_bias_sum_zero
#print axioms marg₁_jointUV
#print axioms marg₂_jointUV
#print axioms mutualInfo_jointUV_eq_kernel_sum


/-! ## `FixedPoint`: closed forms, the route-2 identity, and (E4) -/

#print axioms hasDerivAt_fe_affine
#print axioms lagrTwoPoint_eq_gSum_add_Omega
#print axioms gSum_le_of_le
#print axioms lagrTwoPoint_le_of_omega_nonpos
#print axioms lagrTwoPoint_lt_of_same_skew
#print axioms omegaTwoPoint_zero_of_fst_eq
#print axioms omegaTwoPoint_zero_of_snd_eq
#print axioms mulArtanh_strictMonoOn
#print axioms hasDerivAt_fe_mul_slice
#print axioms fe_mul_slice_strictMonoOn
#print axioms fe_mul_supermodular
#print axioms gMax4_le
#print axioms lagrTwoPoint_le_gMax4_of_omega_le_spread
#print axioms lagrTwoPoint_le_of_omega_le_spread
#print axioms gSym_mixed_diff_eq
#print axioms wFun_eq_sub_phiOdd
#print axioms omegaTwoPoint_eq_phiOdd
#print axioms spread_ge_min_weight_mul
#print axioms lam_kap_mul_le_min_weight
#print axioms lt_one_add_sq_mul_artanh
#print axioms hasDerivAt_KStepFun
#print axioms KStepFun_strictMonoOn
#print axioms hasDerivAt_HStep_slice
#print axioms HStep_slice_strictMonoOn
#print axioms HStep_mixed_diff_neg
#print axioms omegaTwoPoint_le_spread
#print axioms lagrTwoPoint_le_of_opposite_skew
#print axioms lagrTwoPoint_swap
#print axioms lagrTwoPoint_le_of_corner_bounds
#print axioms omegaTwoPoint_zero_fst_atom
#print axioms omegaTwoPoint_zero_snd_atom
#print axioms omegaTwoPoint_zero_thd_atom
#print axioms omegaTwoPoint_zero_fth_atom
#print axioms lagrTwoPoint_le_of_corner_bounds_closed

/-! ## `Closedness`: both regions are closed -/

#print axioms isClosed_coneC
#print axioms convex_coneC
#print axioms continuous_valB
#print axioms isCompact_valBSet
#print axioms regionB_eq_add_cone
#print axioms continuous_combMap
#print axioms combMap_mem_convexHull
#print axioms exists_comb_of_mem_convexHull
#print axioms convexHull_eq_combMap_image
#print axioms isCompact_convexHull
#print axioms isClosed_convexHull_regionB
#print axioms orthant_subset_regionB
#print axioms regionA_subset_convexHull_regionB

/-! ## `Bridge`: `mutualInfo` Lagrangian = `lagrTwoPoint` -/

#print axioms pi_false_eq
#print axioms pi_true_eq
#print axioms rho_false_eq
#print axioms rho_true_eq

/-! ## `Assembly`: biases ↔ crossovers, and domination by `ℬ` -/

#print axioms one_sub_two_mul_bconv
#print axioms fe_one_sub_two_mul
#print axioms fe_bconv_bconv
#print axioms exists_regionB_point
#print axioms lagrTwoPoint_neg_swap
#print axioms lagrTwoPoint_neg_swap_snd
#print axioms bias_sign_cases
#print axioms gMax4_eq_corner
#print axioms exists_regionB_dominating_normalised
#print axioms exists_regionB_dominating
#print axioms fe_one
#print axioms fe_neg_one
#print axioms negMulLog_row_closed
#print axioms mutualInfo_eq_sum_fe_bias_closed
#print axioms mutualInfo_eq_zero_of_row_zero
#print axioms biasOf_mem_Icc
#print axioms mutualInfo_jointUX_eq_bias_closed
#print axioms mutualInfo_jointYV_eq_bias_closed
#print axioms lagrangian_eq_lagrTwoPoint_closed
#print axioms exists_regionB_dominating_all
#print axioms averagedBSCConjecture_of_lt_half
#print axioms averagedBSCConjecture_of_mem
#print axioms h2_one_sub
#print axioms regionB_one_sub
#print axioms regionA_one_sub
#print axioms averagedBSCConjecture_one_sub
#print axioms averagedBSCConjecture_all

#print axioms averaged_bsc_maximise_mutual_information

/-! ### One-sided certificates (`BestResponse.lean`) -/

#print axioms bestResponse_le_of_certificate

/-! ### The `p = 0` certificate (`PZero.lean`) -/

#print axioms key_log_sum
#print axioms lam2_pos
#print axioms lam2_lt_one
#print axioms DFun_neg_one
#print axioms DFun_at_a
#print axioms N_at_a_nonneg
#print axioms GFun''_eq
#print axioms GFun_nonneg_of_contacts
#print axioms GFun_nonpos_of_contacts
#print axioms DFun_nonneg
#print axioms key_mirror
#print axioms mlam2_lt_one
#print axioms MDFun_one
#print axioms MDFun_at_neg_a
#print axioms mN_at_neg_a_nonpos
#print axioms MDFun_nonpos
#print axioms mutualInfo_jointUV_eq_kernel_sum_of_nonneg
#print axioms sChan
#print axioms marg₂_sChan
#print axioms biasOfSnd_sChan

/-! ### The diagonal reduction: the parts that are theorems (`KernelAlgebra.lean`) -/

#print axioms certificate_tight
#print axioms bestResponse_ge_of_certificate
#print axioms mlam2_pos
#print axioms certificate_tight_mirror
#print axioms fe_lt_log_two
#print axioms sChan_rate
#print axioms zsRate_strictMonoOn
#print axioms le_of_zsRate_le
#print axioms zsValue_strictMonoOn_snd
#print axioms zsValue_mono_snd
#print axioms corner_phiZ
#print axioms cornerBound
#print axioms zsValue_pos
#print axioms continuous_mutualInfo
#print axioms chan_eq_chanOf
#print axioms continuous_chanTr
#print axioms isCompact_paramFeasible
#print axioms maxExistsC
#print axioms mutualInfo_jointUV_eq_zero_of_degL
#print axioms mutualInfo_jointUV_eq_zero_of_degR
#print axioms zChan_rate
#print axioms zChan_sChan_value
#print axioms kerQR_eq
#print axioms kernelSum_nonneg
#print axioms fe_tanh
#print axioms weights_of_mean_zero
#print axioms atomValue_eq_Gval
#print axioms Dsl_eq_slack
#print axioms weights_of_mass_mean
#print axioms mutualInfo_jointUX_eq_twoAtomL
#print axioms mutualInfo_jointUV_eq_twoAtomL
#print axioms biasOf_chanOfAtoms
#print axioms rate_chanOfAtoms
#print axioms value_chanOfAtoms
#print axioms hasDerivAt_twoAtomL_line
#print axioms stationary_of_max
#print axioms hasDerivAt_atomValue
#print axioms Dfst_fe_pos
#print axioms stationary_of_maximiser
#print axioms atomValue'_eq
#print axioms residual_zero_of_maximiser
#print axioms mutualInfo_jointUV_eq_twoAtomLV
#print axioms stationary_of_maximiserV
#print axioms residual_zero_of_maximiserV
#print axioms skews_vanish_of_maximiser
#print axioms bsc_of_balanced
#print axioms bothBSC_of_maximiser
#print axioms mutualInfo_jointUX_swapU
#print axioms mutualInfo_jointUV_swapU
#print axioms bothBSC_of_swapU
#print axioms bothBSC_of_maximiser_any
#print axioms mutualInfo_jointYV_swapU
#print axioms bothBSC_of_maximiser_free
#print axioms exists_theta_U
#print axioms bothBSC_of_interior
#print axioms interiorIsBSC_of_noCorner
#print axioms pos_of_second_deriv_pos
#print axioms neg_of_second_deriv_neg
#print axioms hessian_form_pos
#print axioms hasDerivAt_quad
#print axioms total_second_order_eq
#print axioms hasDerivAt_genMul
#print axioms genMul_second
#print axioms quot_second
#print axioms artanh_odd
#print axioms fe_even
#print axioms rate_corrected_coeff
#print axioms exists_correction
#print axioms exists_good_corrections
#print axioms atomValue_chanOfAtomsV
#print axioms value_pair_atoms
#print axioms rate_pair_atoms
#print axioms curve_max_bound
#print axioms hasDerivAt_atomC
#print axioms gap_ne_zero_eventually
#print axioms hasDerivAt_wC
#print axioms hasDerivAt_wC'
#print axioms wC_zero
#print axioms atom_mem_eventually
#print axioms hasDerivAt_rateCurve
#print axioms hasDerivAt_rateCurve'
#print axioms hasDerivAt_mul2'
#print axioms hasDerivAt_valTerm
#print axioms hasDerivAt_valTerm'
#print axioms hasDerivAt_atomProd'
#print axioms hasDerivAt_sum4
#print axioms value_four_term_sum
#print axioms one_add_prod_pos_eventually
#print axioms hasDerivAt_valueCurve
#print axioms not_max_of_second_order2
#print axioms rateCurve'_zero
#print axioms valueCurve'_zero
#print axioms rateCurve_zero
#print axioms valueCurve_zero
#print axioms rateCurve_eq
#print axioms valueCurve_eq
#print axioms hasDerivAt_valueCurve'
#print axioms curve_contradiction
#print axioms exists_curve_corrections
#print axioms hmax_discharge
#print axioms symmetric_not_max
#print axioms fe_eq_half_fFun
#print axioms biasOf_bsc
#print axioms bscNotMax_holds
#print axioms value_zero_of_bias_zero
#print axioms conjecture1_p0_of_Ucorner
#print axioms zsValue_symm
#print axioms cornerBoundU
#print axioms conjecture1_p0_holds
#print axioms cornerBoundMin
#print axioms cornerBoundMinU
#print axioms minExistsC
#print axioms symmetric_not_min
#print axioms bscNotMin
#print axioms conjecture2_p0_holds

end BSCAveraging
