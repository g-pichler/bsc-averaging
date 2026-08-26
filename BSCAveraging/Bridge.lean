import BSCAveraging.BiasCoords
import BSCAveraging.FixedPoint
import BSCAveraging.DataProcessing

/-! # The two-point weights, from the mean-zero relations

The two-point theorem of `FixedPoint.lean` is stated about the algebraic
expression `lagrTwoPoint`, whose weights are not free: they are determined by the
bias vectors.  Writing `s_u = biasOf (jointUX cL) u` and
`t_v = biasOfSnd (jointYV cR) v`, and

```
a = s_false,  b = −s_true,   c = t_false,  d = −t_true
```

the mean-zero relations `Σ π_u s_u = 0` and `Σ ρ_v t_v = 0` (which hold because
`X` and `Y` are uniform) force

```
π_false = b/(a+b),  π_true = a/(a+b),   ρ_false = d/(c+d),  ρ_true = c/(c+d)
```

— exactly the weights built into `lagrTwoPoint`.  Those four identities,
`pi_false_eq`, `pi_true_eq`, `rho_false_eq` and `rho_true_eq`, are this file.

The identification of `lagrTwoPoint` with the Lagrangian itself is assembled from
them in `Assembly.lean` (`mutualInfo_jointUX_eq_bias_closed` and
`lagrangian_eq_lagrTwoPoint_closed`), against
`mutualInfo_jointUV_eq_kernel_sum` of `BiasCoords.lean`.

See `BSCAveraging.Basic`. -/

open Real

namespace BSCAveraging
lemma pi_false_eq {cL : Chan}
    (hf : 0 < marg₁ (jointUX cL) false) (ht : 0 < marg₁ (jointUX cL) true)
    (hne : biasOf (jointUX cL) false - biasOf (jointUX cL) true ≠ 0) :
    marg₁ (jointUX cL) false
      = -biasOf (jointUX cL) true
        / (biasOf (jointUX cL) false - biasOf (jointUX cL) true) := by
  have hz := pi_bias_sum_zero cL hf ht
  have hs := marg₁_jointUX_sum cL
  field_simp
  linear_combination hz - biasOf (jointUX cL) true * hs

lemma pi_true_eq {cL : Chan}
    (hf : 0 < marg₁ (jointUX cL) false) (ht : 0 < marg₁ (jointUX cL) true)
    (hne : biasOf (jointUX cL) false - biasOf (jointUX cL) true ≠ 0) :
    marg₁ (jointUX cL) true
      = biasOf (jointUX cL) false
        / (biasOf (jointUX cL) false - biasOf (jointUX cL) true) := by
  have hz := pi_bias_sum_zero cL hf ht
  have hs := marg₁_jointUX_sum cL
  field_simp
  linear_combination -hz + biasOf (jointUX cL) false * hs

lemma rho_false_eq {cR : Chan}
    (hf : 0 < marg₂ (jointYV cR) false) (ht : 0 < marg₂ (jointYV cR) true)
    (hne : biasOfSnd (jointYV cR) false - biasOfSnd (jointYV cR) true ≠ 0) :
    marg₂ (jointYV cR) false
      = -biasOfSnd (jointYV cR) true
        / (biasOfSnd (jointYV cR) false - biasOfSnd (jointYV cR) true) := by
  have hz := rho_bias_sum_zero cR hf ht
  have hs := marg₂_jointYV_sum cR
  field_simp
  linear_combination hz - biasOfSnd (jointYV cR) true * hs

lemma rho_true_eq {cR : Chan}
    (hf : 0 < marg₂ (jointYV cR) false) (ht : 0 < marg₂ (jointYV cR) true)
    (hne : biasOfSnd (jointYV cR) false - biasOfSnd (jointYV cR) true ≠ 0) :
    marg₂ (jointYV cR) true
      = biasOfSnd (jointYV cR) false
        / (biasOfSnd (jointYV cR) false - biasOfSnd (jointYV cR) true) := by
  have hz := rho_bias_sum_zero cR hf ht
  have hs := marg₂_jointYV_sum cR
  field_simp
  linear_combination -hz + biasOfSnd (jointYV cR) false * hs

/-! ## The bridge -/

end BSCAveraging
