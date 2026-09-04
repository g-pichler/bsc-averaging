/-
# The `Exploration` space

Everything under `BSCAveraging/Exploration/` is proved and `sorry`-free but is
**not** used by any of the three theorems of `BSCAveraging.Basic`
(`averaged_bsc_maximise_mutual_information`, `conjecture1_p0_holds`,
`conjecture2_p0_holds`).  It is kept because it records the search.

The split is mechanical: a declaration lives here iff it is outside the
transitive dependency closure of the three theorems and is not referenced by
anything inside it.

`Exploration/Cal0.lean`, `Cal1.lean` and `Calib.lean` are the CAS calibration
dumps — single `example ... := by ring` goals with `maxHeartbeats 0`.  They are
deliberately **not** imported here, and so are not part of any build.
-/

import BSCAveraging.Exploration.BestResponse
import BSCAveraging.Exploration.CFinish
import BSCAveraging.Exploration.Conj12
import BSCAveraging.Exploration.CorePos
import BSCAveraging.Exploration.DiagReduction
import BSCAveraging.Exploration.Envelope
import BSCAveraging.Exploration.Interval
import BSCAveraging.Exploration.KKT
import BSCAveraging.Exploration.KernelAlgebra
import BSCAveraging.Exploration.KernelBridge
import BSCAveraging.Exploration.KernelCertBern
import BSCAveraging.Exploration.KernelBridgeB
import BSCAveraging.Exploration.KernelCertKron
import BSCAveraging.Exploration.LogCosh
import BSCAveraging.Exploration.PZero
import BSCAveraging.Exploration.PZeroSymm
import BSCAveraging.Exploration.Reflect
import BSCAveraging.Exploration.TwoAtom
import BSCAveraging.Exploration.Misc

namespace BSCAveraging

#print axioms mem_convexHull_regionB_of_chan
#print axioms convexHull_linear_le
#print axioms lagrangian_le_of_bsc_bound
#print axioms mutualInfo_le_of_bsc_bound
#print axioms bddAbove_concEnvSet
#print axioms nonempty_concEnvSet
#print axioms mutualInfo_le_concEnvBSC
#print axioms bsc_le_concEnvBSC
#print axioms concEnvBSC_le_of_bsc_bound
#print axioms bestResponse_le_of_certificate'
#print axioms mutualInfo_le_of_sChan
#print axioms lam1_eq_zero
#print axioms DSym''_eq_zero_unique
#print axioms no_two_positive_contacts
#print axioms interior_response_symmetric
#print axioms artanh_edge
#print axioms schur_decomposition
#print axioms kernel_nonneg_of_comonotone
#print axioms comonotone_of_decreasing
#print axioms mul_comonotone
#print axioms kernel_split
#print axioms kerSum_f_nonneg
#print axioms kerSum_fg_nonneg
#print axioms kernel_vanishes_on_face
#print axioms faceX_nonneg
#print axioms faceY_nonneg
#print axioms mutualInfo_ge_of_sChan
#print axioms conjecture2_p0_of_cornerDominationMin
#print axioms conjecture1_p0_of_two
#print axioms IsMaxPairC.bestResponseU
#print axioms IsMaxPairC.bestResponseV
#print axioms maxIsBSCorCorner_of_interior
#print axioms bscNotMax_of_branchGap
#print axioms Iv.mem_add
#print axioms Iv.mem_mul
#print axioms Iv.pos_of_isPos
#print axioms Iv.mem_div
#print axioms Iv.mem_expIv
#print axioms Iv.mem_coshI
#print axioms Iv.mem_tanhI
#print axioms Iv.mem_logIv
#print axioms Iv.mem_outward
#print axioms Iv.mem_FI2
#print axioms Iv.pos_of_cellOk2
#print axioms Iv.sweep_sound
#print axioms Core.hasDerivAt_F
#print axioms Core.F_eq
#print axioms Core.F_pos_of_center
#print axioms Core.mem_FpI
#print axioms Core.abs_le_absBound
#print axioms Core.pos_of_cellOkC
#print axioms Core.sweepC_sound
#print axioms Reflect.kerBPE_allNonneg
#print axioms Reflect.kernelSum_nonneg_B'
#print axioms Reflect.Kron.digits_mask
#print axioms Core.core_pos_regime2
#print axioms Core.log_cosh_eq
#print axioms Core.exp_dominates
#print axioms Core.core_pos_regime3
#print axioms Core.core_pos_regime1
#print axioms Core.core_pos
#print axioms Core.core_pos'
#print axioms Core.gFun_tanh
#print axioms Core.artanh_tanh_sq
#print axioms Core.Ncore_pos
#print axioms Core.diag_pos
#print axioms Core.gFun_eq_integral
#print axioms Core.one_sub_gFun_eq_integral
#print axioms Core.Aval_eq_integral
#print axioms kernelLemma_holds
#print axioms Core.integral3_sum
#print axioms Core.sym_pointwise
#print axioms Core.Nfun_nonneg
#print axioms Core.hasDerivAt_gFun
#print axioms Core.gFun_strictAntiOn
#print axioms Core.hasDerivAt_Rat
#print axioms Core.Rat_antitoneOn
#print axioms Core.saddle_iii
#print axioms LC.LC_tangent_le
#print axioms LC.MG_div_strictAntiOn
#print axioms LC.phi_antitoneOn
#print axioms LC.diamond
#print axioms LC.green_identity
#print axioms LC.Kfun_nonpos
#print axioms LC.residual_green
#print axioms LC.residual_pos
#print axioms LC.RS_odd
#print axioms LC.skews_vanish
#print axioms LC.hasDerivAt_Gval
#print axioms LC.bitangent_residual_zero
#print axioms LC.bitangent_pair_symmetric
#print axioms Core.criterion_den_pos
#print axioms Core.saddleRatio_gt_one
#print axioms Core.Fpq_eq
#print axioms Core.Fpp_eq
#print axioms Core.Fpp_neg
#print axioms Core.hessian_indefinite
#print axioms Core.saddle_direction
#print axioms LC.tangency_of_contact
#print axioms KKT.le_zero_of_deriv_of_max
#print axioms KKT.kkt_of_directional
#print axioms KKT.bitangency_of_stationary
#print axioms KKT.cleared_of_grad
#print axioms KKT.hasDerivAt_twoAtomL_fst
#print axioms KKT.hasDerivAt_twoAtomR_snd
#print axioms Dsnd_fe_neg
#print axioms twoAtomL_decomp
#print axioms slackPath_second_deriv
#print axioms slackHess_eq_Fpp
#print axioms slackHess_eq_Fqq
#print axioms slackPath_second_deriv_Fpp
#print axioms second_deriv_of_mul_vanishing
#print axioms not_max_of_second_order
#print axioms hasDerivAt_polyMul
#print axioms polyMul_second
#print axioms rate_second_coeff
#print axioms value_second_coeff
#print axioms weight_taylor
#print axioms rate_grad_symmetric
#print axioms value_weightcorr_cancel
#print axioms value_correction_coeff
#print axioms cube_sum_ge_three_mul
#print axioms rFun_sub
#print axioms fFun'_sub
#print axioms fg_cross
#print axioms geometric_kernel_zero
#print axioms kernel_false_for_general_law
#print axioms two_mul_log_two_sq_lt_one

end BSCAveraging
