import BSCAveraging.Rigidity
import BSCAveraging.Definitions
import BSCAveraging.Nonneg
import BSCAveraging.Lagrangian
import BSCAveraging.Regions

/-! # The bias parametrization, as a bridge to the region definitions

`NOTES.md` §2 works in **bias coordinates**: for a joint law of `(U,X)` with `X`
uniform, writing `π_u = P(U=u)` and `s_u = 1 − 2·P(X=1|U=u)` for the conditional
bias,

> `I(U;X) = Σ_u π_u · f_e(s_u)` ,   `f_e(y) = ½[(1+y)log(1+y) + (1−y)log(1−y)]` .

Every analytic result in this development — local rigidity, the global sign
flip, Mrs. Gerber's Lemma, `μ ≥ 1`, supermodularity of `f_e`, and the sharp bound
`ρ ≤ 2 − 1/log 2` — is stated in those coordinates, while `regionA`/`regionB`
and `AveragedBSCConjecture` are stated in terms of `mutualInfo`.  Nothing
connected the two.  This file supplies the first half of that bridge
(`NOTES.md` §6, route 6).

See `BSCAveraging.Basic`. -/

open Real

namespace BSCAveraging

/-- The conditional bias `s_u = 1 − 2·P(X = true | U = u)` of a joint law. -/
noncomputable def biasOf (q : Bool → Bool → ℝ) (u : Bool) : ℝ :=
  (q u false - q u true) / marg₁ q u

lemma q_false_eq {q : Bool → Bool → ℝ} {u : Bool} (h : 0 < marg₁ q u) :
    q u false = marg₁ q u * ((1 + biasOf q u) / 2) := by
  have hne : q u false + q u true ≠ 0 := by unfold marg₁ at h; exact ne_of_gt h
  unfold biasOf marg₁
  field_simp
  ring

lemma q_true_eq {q : Bool → Bool → ℝ} {u : Bool} (h : 0 < marg₁ q u) :
    q u true = marg₁ q u * ((1 - biasOf q u) / 2) := by
  have hne : q u false + q u true ≠ 0 := by unfold marg₁ at h; exact ne_of_gt h
  unfold biasOf marg₁
  field_simp
  ring

/-- **The key splitting.**  Writing a row of the joint law as
`π·(1±s)/2`, its contribution to the joint entropy splits into the row weight's
own entropy plus `π·(log 2 − f_e(s))`, the conditional entropy of that row. -/
lemma negMulLog_row {w s : ℝ} (hw : 0 < w) (hs0 : -1 < s) (hs1 : s < 1) :
    negMulLog (w * ((1 + s) / 2)) + negMulLog (w * ((1 - s) / 2))
      = negMulLog w + w * (Real.log 2 - fe s) := by
  have h1 : (0:ℝ) < (1 + s) / 2 := by linarith
  have h2 : (0:ℝ) < (1 - s) / 2 := by linarith
  have e1 : Real.log (w * ((1 + s) / 2)) = Real.log w + (Real.log (1 + s) - Real.log 2) := by
    rw [Real.log_mul (ne_of_gt hw) (ne_of_gt h1), Real.log_div (by linarith) two_ne_zero]
  have e2 : Real.log (w * ((1 - s) / 2)) = Real.log w + (Real.log (1 - s) - Real.log 2) := by
    rw [Real.log_mul (ne_of_gt hw) (ne_of_gt h2), Real.log_div (by linarith) two_ne_zero]
  simp only [Real.negMulLog, e1, e2, fe]
  ring

/-- The bias of the *second* coordinate given the first, for laws such as
`jointYV` whose uniform marginal is the first one. -/
noncomputable def biasOfSnd (q : Bool → Bool → ℝ) (v : Bool) : ℝ :=
  (q false v - q true v) / marg₂ q v

/-! ## The joint laws of the problem -/

lemma marg₂_jointUX (cL : Chan) (x : Bool) : marg₂ (jointUX cL) x = 1 / 2 := by
  simp only [marg₂, jointUX]
  rw [show cL.tr x false / 2 + cL.tr x true / 2 = (cL.tr x false + cL.tr x true) / 2 by ring,
    cL.sum_one x]

lemma marg₁_jointUX_sum (cL : Chan) :
    marg₁ (jointUX cL) false + marg₁ (jointUX cL) true = 1 := by
  simp only [marg₁, jointUX]
  have h1 := cL.sum_one false
  have h2 := cL.sum_one true
  linarith

/-- **The kernel identity of `NOTES.md` §2.**  With `π_u = P(U=u)`,
`ρ_v = P(V=v)`, `s_u`, `t_v` the conditional biases and `δ = 1 − 2p`,

> `P(u,v) = π_u · ρ_v · (1 + δ · s_u · t_v)` .

This is what makes the whole bias parametrization work, and what
`numerics/check_kernel.py` checks numerically. -/
theorem jointUV_eq_kernel (p : ℝ) (cL cR : Chan) (u v : Bool)
    (hL : 0 < cL.tr false u + cL.tr true u) (hR : 0 < cR.tr false v + cR.tr true v) :
    jointUV p cL cR u v
      = marg₁ (jointUX cL) u * marg₂ (jointYV cR) v
        * (1 + (1 - 2 * p) * biasOf (jointUX cL) u * biasOfSnd (jointYV cR) v) := by
  have hLne : cL.tr false u + cL.tr true u ≠ 0 := ne_of_gt hL
  have hRne : cR.tr false v + cR.tr true v ≠ 0 := ne_of_gt hR
  simp only [jointUV, dsbs, marg₁, marg₂, jointUX, jointYV, biasOf, biasOfSnd]
  norm_num
  field_simp
  ring

/-! ## Marginals of the `(U,V)` law, and `I(U;V)` in bias coordinates -/

lemma marg₁_jointYV (cR : Chan) (y : Bool) : marg₁ (jointYV cR) y = 1 / 2 := by
  simp only [marg₁, jointYV]
  rw [show cR.tr y false / 2 + cR.tr y true / 2 = (cR.tr y false + cR.tr y true) / 2 by ring,
    cR.sum_one y]

/-- `E[T] = 0`: the `V`-side biases have mean zero, because `Y` is uniform. -/
lemma rho_bias_sum_zero (cR : Chan)
    (hf : 0 < marg₂ (jointYV cR) false) (ht : 0 < marg₂ (jointYV cR) true) :
    marg₂ (jointYV cR) false * biasOfSnd (jointYV cR) false
      + marg₂ (jointYV cR) true * biasOfSnd (jointYV cR) true = 0 := by
  have e : ∀ v, marg₂ (jointYV cR) v * biasOfSnd (jointYV cR) v
      = jointYV cR false v - jointYV cR true v := by
    intro v
    have hv : marg₂ (jointYV cR) v ≠ 0 := by
      rcases v with _ | _
      · exact ne_of_gt hf
      · exact ne_of_gt ht
    unfold biasOfSnd
    field_simp
  rw [e false, e true]
  have h1 := marg₁_jointYV cR false
  have h2 := marg₁_jointYV cR true
  simp only [marg₁] at h1 h2
  linarith

lemma marg₂_jointYV_sum (cR : Chan) :
    marg₂ (jointYV cR) false + marg₂ (jointYV cR) true = 1 := by
  simp only [marg₂, jointYV]
  have h1 := cR.sum_one false
  have h2 := cR.sum_one true
  linarith

/-- `E[S] = 0`: the `U`-side biases have mean zero, because `X` is uniform. -/
lemma pi_bias_sum_zero (cL : Chan)
    (hf : 0 < marg₁ (jointUX cL) false) (ht : 0 < marg₁ (jointUX cL) true) :
    marg₁ (jointUX cL) false * biasOf (jointUX cL) false
      + marg₁ (jointUX cL) true * biasOf (jointUX cL) true = 0 := by
  have e : ∀ u, marg₁ (jointUX cL) u * biasOf (jointUX cL) u
      = jointUX cL u false - jointUX cL u true := by
    intro u
    have hu : marg₁ (jointUX cL) u ≠ 0 := by
      rcases u with _ | _
      · exact ne_of_gt hf
      · exact ne_of_gt ht
    unfold biasOf
    field_simp
  rw [e false, e true]
  have h1 := marg₂_jointUX cL false
  have h2 := marg₂_jointUX cL true
  simp only [marg₂] at h1 h2
  linarith

/-- The `(U,V)` law has the right first marginal: `Σ_v P(u,v) = π_u`.  Uses the
kernel identity together with `E[T] = 0`. -/
lemma marg₁_jointUV (p : ℝ) (cL cR : Chan)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v) (u : Bool) :
    marg₁ (jointUV p cL cR) u = marg₁ (jointUX cL) u := by
  have hL : ∀ w, 0 < cL.tr false w + cL.tr true w := by
    intro w; have := hpi w; simp only [marg₁, jointUX] at this; linarith
  have hR : ∀ w, 0 < cR.tr false w + cR.tr true w := by
    intro w; have := hrho w; simp only [marg₂, jointYV] at this; linarith
  have k0 := jointUV_eq_kernel p cL cR u false (hL u) (hR false)
  have k1 := jointUV_eq_kernel p cL cR u true (hL u) (hR true)
  have hz := rho_bias_sum_zero cR (hrho false) (hrho true)
  have hs := marg₂_jointYV_sum cR
  show jointUV p cL cR u false + jointUV p cL cR u true = marg₁ (jointUX cL) u
  rw [k0, k1]
  linear_combination marg₁ (jointUX cL) u * hs
    + marg₁ (jointUX cL) u * (1 - 2 * p) * biasOf (jointUX cL) u * hz

/-- The `(U,V)` law has the right second marginal: `Σ_u P(u,v) = ρ_v`. -/
lemma marg₂_jointUV (p : ℝ) (cL cR : Chan)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v) (v : Bool) :
    marg₂ (jointUV p cL cR) v = marg₂ (jointYV cR) v := by
  have hL : ∀ w, 0 < cL.tr false w + cL.tr true w := by
    intro w; have := hpi w; simp only [marg₁, jointUX] at this; linarith
  have hR : ∀ w, 0 < cR.tr false w + cR.tr true w := by
    intro w; have := hrho w; simp only [marg₂, jointYV] at this; linarith
  have k0 := jointUV_eq_kernel p cL cR false v (hL false) (hR v)
  have k1 := jointUV_eq_kernel p cL cR true v (hL true) (hR v)
  have hz := pi_bias_sum_zero cL (hpi false) (hpi true)
  have hs := marg₁_jointUX_sum cL
  show jointUV p cL cR false v + jointUV p cL cR true v = marg₂ (jointYV cR) v
  rw [k0, k1]
  linear_combination marg₂ (jointYV cR) v * hs
    + marg₂ (jointYV cR) v * (1 - 2 * p) * biasOfSnd (jointYV cR) v * hz

/-- **`I(U;V) = Σ_{u,v} π_u ρ_v · f(δ s_u t_v)`**, `f(z) = (1+z)log(1+z)`: the
second half of the bias parametrization of `NOTES.md` §2, now for the joint law
`regionA` is stated with. -/
theorem mutualInfo_jointUV_eq_kernel_sum (p : ℝ) (cL cR : Chan)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hker : ∀ u v, 0 < 1 + (1 - 2 * p) * biasOf (jointUX cL) u * biasOfSnd (jointYV cR) v) :
    mutualInfo (jointUV p cL cR)
      = marg₁ (jointUX cL) false * marg₂ (jointYV cR) false
          * fFun ((1 - 2 * p) * biasOf (jointUX cL) false * biasOfSnd (jointYV cR) false)
        + marg₁ (jointUX cL) false * marg₂ (jointYV cR) true
          * fFun ((1 - 2 * p) * biasOf (jointUX cL) false * biasOfSnd (jointYV cR) true)
        + marg₁ (jointUX cL) true * marg₂ (jointYV cR) false
          * fFun ((1 - 2 * p) * biasOf (jointUX cL) true * biasOfSnd (jointYV cR) false)
        + marg₁ (jointUX cL) true * marg₂ (jointYV cR) true
          * fFun ((1 - 2 * p) * biasOf (jointUX cL) true * biasOfSnd (jointYV cR) true) := by
  set wU := fun u => marg₁ (jointUX cL) u with hwU
  set wV := fun v => marg₂ (jointYV cR) v with hwV
  set zz := fun u v => (1 - 2 * p) * biasOf (jointUX cL) u * biasOfSnd (jointYV cR) v with hzz
  have hL : ∀ u, 0 < cL.tr false u + cL.tr true u := by
    intro u; have := hpi u; simp only [marg₁, jointUX] at this; linarith
  have hR : ∀ v, 0 < cR.tr false v + cR.tr true v := by
    intro v; have := hrho v; simp only [marg₂, jointYV] at this; linarith
  have hm1 : ∀ u, marg₁ (jointUV p cL cR) u = marg₁ (jointUX cL) u :=
    fun u => marg₁_jointUV p cL cR hpi hrho u
  have hm2 : ∀ v, marg₂ (jointUV p cL cR) v = marg₂ (jointYV cR) v :=
    fun v => marg₂_jointUV p cL cR hpi hrho v
  have hq : ∀ u v, jointUV p cL cR u v = wU u * wV v * (1 + zz u v) := by
    intro u v; exact jointUV_eq_kernel p cL cR u v (hL u) (hR v)
  have hcell : ∀ u v, jointUV p cL cR u v * Real.log (jointUV p cL cR u v)
      - jointUV p cL cR u v * (Real.log (marg₁ (jointUV p cL cR) u)
        + Real.log (marg₂ (jointUV p cL cR) v))
      = wU u * wV v * fFun (zz u v) := by
    intro u v
    rw [hq u v, hm1 u, hm2 v, fFun]
    rw [Real.log_mul (ne_of_gt (mul_pos (hpi u) (hrho v))) (ne_of_gt (hker u v)),
      Real.log_mul (ne_of_gt (hpi u)) (ne_of_gt (hrho v))]
    ring
  rw [mutualInfo_eq_sum]
  rw [hcell false false, hcell false true, hcell true false, hcell true true]

/-- **The kernel identity with degenerate cells allowed.**  Weakening `hker` from
`0 <` to `0 ≤` costs nothing: when `1 + δ·s_u·t_v = 0` — the "impossible cell"
that the `p = 0` Z/S pair creates — that cell has probability `0` and
`f(−1) = 0·log 0 = 0`, so it contributes `0` to both sides.  This is what lets
the `p = 0` certificates apply to the very configurations they are about. -/
theorem mutualInfo_jointUV_eq_kernel_sum_of_nonneg (p : ℝ) (cL cR : Chan)
    (hpi : ∀ u, 0 < marg₁ (jointUX cL) u) (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hker : ∀ u v, 0 ≤ 1 + (1 - 2 * p) * biasOf (jointUX cL) u * biasOfSnd (jointYV cR) v) :
    mutualInfo (jointUV p cL cR)
      = marg₁ (jointUX cL) false * marg₂ (jointYV cR) false
          * fFun ((1 - 2 * p) * biasOf (jointUX cL) false * biasOfSnd (jointYV cR) false)
        + marg₁ (jointUX cL) false * marg₂ (jointYV cR) true
          * fFun ((1 - 2 * p) * biasOf (jointUX cL) false * biasOfSnd (jointYV cR) true)
        + marg₁ (jointUX cL) true * marg₂ (jointYV cR) false
          * fFun ((1 - 2 * p) * biasOf (jointUX cL) true * biasOfSnd (jointYV cR) false)
        + marg₁ (jointUX cL) true * marg₂ (jointYV cR) true
          * fFun ((1 - 2 * p) * biasOf (jointUX cL) true * biasOfSnd (jointYV cR) true) := by
  set wU := fun u => marg₁ (jointUX cL) u with hwU
  set wV := fun v => marg₂ (jointYV cR) v with hwV
  set zz := fun u v => (1 - 2 * p) * biasOf (jointUX cL) u * biasOfSnd (jointYV cR) v with hzz
  have hL : ∀ u, 0 < cL.tr false u + cL.tr true u := by
    intro u; have := hpi u; simp only [marg₁, jointUX] at this; linarith
  have hR : ∀ v, 0 < cR.tr false v + cR.tr true v := by
    intro v; have := hrho v; simp only [marg₂, jointYV] at this; linarith
  have hm1 : ∀ u, marg₁ (jointUV p cL cR) u = marg₁ (jointUX cL) u :=
    fun u => marg₁_jointUV p cL cR hpi hrho u
  have hm2 : ∀ v, marg₂ (jointUV p cL cR) v = marg₂ (jointYV cR) v :=
    fun v => marg₂_jointUV p cL cR hpi hrho v
  have hq : ∀ u v, jointUV p cL cR u v = wU u * wV v * (1 + zz u v) := by
    intro u v; exact jointUV_eq_kernel p cL cR u v (hL u) (hR v)
  have hcell : ∀ u v, jointUV p cL cR u v * Real.log (jointUV p cL cR u v)
      - jointUV p cL cR u v * (Real.log (marg₁ (jointUV p cL cR) u)
        + Real.log (marg₂ (jointUV p cL cR) v))
      = wU u * wV v * fFun (zz u v) := by
    intro u v
    rcases eq_or_lt_of_le (hker u v) with hz | hz
    · have hz1 : zz u v = -1 := by linarith
      have hq0 : jointUV p cL cR u v = 0 := by rw [hq u v, ← hz]; ring
      rw [hq0, hz1]
      simp [fFun]
    · rw [hq u v, hm1 u, hm2 v, fFun]
      rw [Real.log_mul (ne_of_gt (mul_pos (hpi u) (hrho v))) (ne_of_gt hz),
        Real.log_mul (ne_of_gt (hpi u)) (ne_of_gt (hrho v))]
      ring
  rw [mutualInfo_eq_sum]
  rw [hcell false false, hcell false true, hcell true false, hcell true true]

end BSCAveraging
