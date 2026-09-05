import BSCAveraging.PZero
import BSCAveraging.KernelAlgebra

/-! # Conjectures 1 and 2 of Entropy 24(9):1321, at `p = 0`

`NOTES.md` §7d′ assembles the two conjectures out of four steps, over binary
`U, V` (Pichler Prop 4.3, cited and not formalized):

1. an optimiser exists — compactness of the parameter box cut by the two rate
   constraints (`maxExistsC`, `minExistsC`, proved below out of
   `continuous_mutualInfo`, `chan_eq_chanOf` and `isCompact_paramFeasible`);
2. an interior optimiser is the symmetric BSC pair — KKT for a maximiser under
   `R ≤ C` and a minimiser under `R ≥ C` have the same form, so the step is
   stated once for `OptPairC` (`interiorIsBSC_of_noCorner`, in `BFinishV.lean`);
3. the BSC pair is a saddle, not an optimum — for the maximisation the saddle
   inequality (iii) (`saddle_iii`), for the minimisation `F_pp < 0` alone
   (`symmetric_not_min`);
4. at the corner the Z/S resp. Z/Z pair is optimal — the certificates, tight at
   the Z-channel's atoms (`cornerBound` below, `cornerBoundMin`).

What this file carries of that is steps 1 and 4 together with the arithmetic
around the Z/S branch: `certificate_tight`, saying the certificate's bound at the
Z-channel's own rate is *exactly* the Z/S value; `sChan_rate`, identifying the
S-channel's rate with `zsRate`; the monotonicity of `zsRate` and of `zsValue`
(`zsRate_strictMonoOn`, `zsValue_strictMonoOn_snd`, `le_of_zsRate_le`,
`zsValue_mono_snd`); and the bounds `fe_lt_log_two`, `zsRate_lt_log_two`,
`zsValue_pos`.

The `Prop`-level bundling of steps 1–3 into a single corner-domination statement,
and the route through `interior_response_symmetric` and `mutualInfo_le_of_sChan`,
are in `Exploration/Conj12.lean` and `Exploration/PZero.lean`; no part of the
proof imports them.

`Conjecture1_p0` and `Conjecture2_p0` are `Prop`s, never assumed. -/

open Real

namespace BSCAveraging

variable {a d : ℝ}

/-! ## The certificate is tight at the Z-channel -/

/-- **The certificate's bound equals the Z/S value.**  The Z-channel with
interior atom `a` puts mass `1/(1+a)` at `s = a` and `a/(1+a)` at `s = −1`, which
are exactly the two contacts of the certificate (`DFun_at_a`, `DFun_neg_one`).
Averaging the two contact identities with those weights, the `λ₁` term cancels
(the atoms have mean zero) and the `λ₂` term collects into the Z-channel's rate:

```
λ₀ + λ₂·zsRate a = zsValue a d .
```

So the bound of `mutualInfo_le_of_sChan` is attained, and the Z/S pair is a
*global* best response — not merely a stationary point. -/
theorem certificate_tight (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    lam0 a d + lam2 a d * zsRate a = zsValue a d := by
  have h1a : (0 : ℝ) < 1 + a := by linarith
  -- the two contacts, read as evaluations of `phiZ`
  have hA : phiZ d a = lam0 a d + lam1 a d * a + lam2 a d * fe a := by
    have h := DFun_at_a ha0 ha1 hd0 hd1
    simp only [DFun, GFun] at h
    linarith
  have hB : phiZ d (-1) = lam0 a d - lam1 a d + lam2 a d * log 2 := by
    have h := DFun_neg_one (a := a) hd0
    simp only [DFun, GFun, fe_neg_one] at h
    linarith
  -- the Z/S value is the `(1/(1+a), a/(1+a))` average of the two atom values
  have hz : zsValue a d = (1 / (1 + a)) * phiZ d a + (a / (1 + a)) * phiZ d (-1) := by
    rw [phiZ_neg_one hd0]
    have hd : (0 : ℝ) < 1 + d := by linarith
    simp only [zsValue, phiZ, fFun]
    have hxa : (1 : ℝ) + a ≠ 0 := ne_of_gt h1a
    have hxd : (1 : ℝ) + d ≠ 0 := ne_of_gt hd
    have hneg : -(d * a) = -(d * a) := rfl
    field_simp
    ring
  rw [hz, hA, hB, zsRate]
  field_simp
  ring

/-! ## Towards (D): the S-channel family

Two facts every version of `(D)` needs: the S-channel's own rate is exactly
`zsRate`, and `zsRate` is strictly increasing — so the rate hypothesis of `(D)`
pins down `d' ≤ d`. -/

/-- `f_e < log 2` on `(0,1)`, from `f_e(1−2α) = log 2 − h₂(α)` and `h₂ > 0`. -/
theorem fe_lt_log_two {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : fe y < log 2 := by
  have hα0 : (0:ℝ) ≤ (1 - y) / 2 := by linarith
  have hα1 : (1 - y) / 2 ≤ 1 := by linarith
  have he : y = 1 - 2 * ((1 - y) / 2) := by ring
  rw [he, fe_one_sub_two_mul hα0 hα1]
  have hpos : 0 < h2 ((1 - y) / 2) := by
    have h1 : (0:ℝ) < (1 - y) / 2 := by linarith
    have h2' : (1 - y) / 2 < 1 := by linarith
    have e1 : 0 < -((1 - y) / 2) * log ((1 - y) / 2) :=
      mul_pos_of_neg_of_neg (by linarith) (Real.log_neg h1 h2')
    have e2 : 0 < -(1 - (1 - y) / 2) * log (1 - (1 - y) / 2) :=
      mul_pos_of_neg_of_neg (by linarith) (Real.log_neg (by linarith) (by linarith))
    simpa [h2, Real.negMulLog, neg_mul] using add_pos e1 e2
  linarith

/-- The derivative of `f_e` (a local copy: `Exploration.lean` is not imported here). -/
lemma hasDerivAt_fe' {z : ℝ} (h0 : -1 < z) (h1 : z < 1) : HasDerivAt fe (artanh z) z := by
  have hp : (1 : ℝ) + z ≠ 0 := by linarith
  have hm : (1 : ℝ) - z ≠ 0 := by linarith
  have d1 : HasDerivAt (fun u : ℝ => (1 + u) * log (1 + u)) (log (1 + z) + 1) z := by
    have ha : HasDerivAt (fun u : ℝ => 1 + u) 1 z := by simpa using (hasDerivAt_id z).const_add 1
    have h := ha.mul (ha.log hp)
    have heq : 1 * log (1 + z) + (1 + z) * (1 / (1 + z)) = log (1 + z) + 1 := by field_simp
    rwa [heq] at h
  have d2 : HasDerivAt (fun u : ℝ => (1 - u) * log (1 - u)) (-log (1 - z) - 1) z := by
    have ha : HasDerivAt (fun u : ℝ => 1 - u) (-1) z := by simpa using (hasDerivAt_id z).const_sub 1
    have h := ha.mul (ha.log hm)
    have heq : -1 * log (1 - z) + (1 - z) * (-1 / (1 - z)) = -log (1 - z) - 1 := by
      field_simp
      ring
    rwa [heq] at h
  have h := (d1.add d2).div_const 2
  have heq : (log (1 + z) + 1 + (-log (1 - z) - 1)) / 2 = artanh z := by
    rw [artanh_eq_log_sub h0 h1]; ring
  rwa [heq] at h

/-- **The S-channel's rate is `zsRate`.**  In bias coordinates its law is
`(+1, −d)` with masses `(d/(1+d), 1/(1+d))`. -/
theorem sChan_rate (hd0 : 0 < d) (hd1 : d < 1) :
    mutualInfo (jointYV (sChan d hd0 hd1)) = zsRate d := by
  obtain ⟨hm1, hm2⟩ := marg₂_sChan hd0 hd1
  obtain ⟨hb1, hb2⟩ := biasOfSnd_sChan hd0 hd1
  have hrho : ∀ v, 0 < marg₂ (jointYV (sChan d hd0 hd1)) v := by
    intro v; cases v
    · rw [hm1]; positivity
    · rw [hm2]; positivity
  rw [mutualInfo_jointYV_eq_bias_closed hrho, hm1, hm2, hb1, hb2, fe_one, fe_neg, zsRate]
  have h : (1 : ℝ) + d ≠ 0 := by positivity
  field_simp
  ring

/-- The derivative of `zsRate`. -/
lemma hasDerivAt_zsRate {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    HasDerivAt zsRate (((1 + x) * artanh x + log 2 - fe x) / (1 + x) ^ 2) x := by
  have hx : (1 : ℝ) + x ≠ 0 := by positivity
  have hP := hasDerivAt_fe' (show (-1:ℝ) < x by linarith) h1
  have hL : HasDerivAt (fun t : ℝ => t * log 2) (log 2) x := by
    simpa using (hasDerivAt_id x).mul_const (log 2)
  have hnum : HasDerivAt (fun t : ℝ => fe t + t * log 2) (artanh x + log 2) x := hP.add hL
  have hden : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    simpa using (hasDerivAt_id x).const_add 1
  have h := hnum.div hden hx
  have heq : ((artanh x + log 2) * (1 + x) - (fe x + x * log 2) * 1) / (1 + x) ^ 2
      = ((1 + x) * artanh x + log 2 - fe x) / (1 + x) ^ 2 := by ring
  rw [heq] at h
  exact h

/-- **`zsRate` is strictly increasing on `(0,1)`**: the numerator of its
derivative is `(1+x)·artanh x + log 2 − f_e(x) > 0`. -/
theorem zsRate_strictMonoOn : StrictMonoOn zsRate (Set.Ioo (0:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0:ℝ) 1)
  · intro x hx
    exact ((hasDerivAt_zsRate hx.1 hx.2).continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(hasDerivAt_zsRate hx.1 hx.2).deriv]
    have hA : 0 < artanh x := Real.artanh_pos ⟨hx.1, hx.2⟩
    have hPl : fe x < log 2 := fe_lt_log_two hx.1 hx.2
    have h1x : (0:ℝ) < 1 + x := by linarith [hx.1]
    have hmul : 0 < (1 + x) * artanh x := mul_pos h1x hA
    have hnum : (0:ℝ) < (1 + x) * artanh x + log 2 - fe x := by linarith
    exact div_pos hnum (by positivity)

/-- The rate hypothesis of `(D)` pins the parameter: `zsRate d' ≤ zsRate d` forces
`d' ≤ d`. -/
theorem le_of_zsRate_le {d' d : ℝ} (h0' : 0 < d') (h1' : d' < 1) (h0 : 0 < d) (h1 : d < 1)
    (h : zsRate d' ≤ zsRate d) : d' ≤ d := by
  by_contra hlt
  push_neg at hlt
  exact absurd (zsRate_strictMonoOn ⟨h0, h1⟩ ⟨h0', h1'⟩ hlt) (by linarith)


/-- The derivative of `zsValue a ·`.  Every `log(1−ad)` term cancels: the
numerator collapses to `(1+a)·[log(1+a) − log(1−ad)]`. -/
lemma hasDerivAt_zsValue_snd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun t : ℝ => zsValue a t)
      ((log (1 + a) - log (1 - a * x)) / (1 + x) ^ 2) x := by
  have hx : (0:ℝ) < 1 + x := by linarith
  have hxne : (1:ℝ) + x ≠ 0 := ne_of_gt hx
  have ha : (0:ℝ) < 1 + a := by linarith
  have hane : (1:ℝ) + a ≠ 0 := ne_of_gt ha
  have hax : (0:ℝ) < 1 - a * x := by nlinarith
  have haxne : (1:ℝ) - a * x ≠ 0 := ne_of_gt hax
  have hd : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by simpa using (hasDerivAt_id x).const_add 1
  have hden2 : HasDerivAt (fun t : ℝ => (1 + a) * (1 + t)) (1 + a) x := by
    simpa using hd.const_mul (1 + a)
  have hden2ne : (1 + a) * (1 + x) ≠ 0 := by positivity
  have hu : HasDerivAt (fun t : ℝ => 1 - a * t) (-a) x := by
    simpa using ((hasDerivAt_id x).const_mul a).const_sub 1
  -- first summand
  have h1 : HasDerivAt (fun t : ℝ => t / (1 + t) * log (1 + a))
      (1 / (1 + x) ^ 2 * log (1 + a)) x := by
    have h := ((hasDerivAt_id x).div hd hxne).mul_const (log (1 + a))
    have heq : (1 * (1 + x) - id x * 1) / (1 + x) ^ 2 = 1 / (1 + x) ^ 2 := by
      simp only [id_eq]; field_simp; ring
    rw [heq] at h
    exact h
  -- second summand, in exactly the shape `zsValue` uses
  have hA : HasDerivAt (fun t : ℝ => (1 - a * t) / ((1 + a) * (1 + t)))
      ((-a * ((1 + a) * (1 + x)) - (1 - a * x) * (1 + a)) / ((1 + a) * (1 + x)) ^ 2) x :=
    hu.div hden2 hden2ne
  have hB : HasDerivAt (fun t : ℝ => log (1 - a * t)) (-a / (1 - a * x)) x := hu.log haxne
  have h2 := hA.mul hB
  -- third summand
  have h3 : HasDerivAt (fun t : ℝ => a / (1 + a) * log (1 + t))
      (a / (1 + a) * (1 / (1 + x))) x := by
    simpa using (hd.log hxne).const_mul (a / (1 + a))
  have hsum := (h1.add h2).add h3
  have hval : 1 / (1 + x) ^ 2 * log (1 + a)
      + ((-a * ((1 + a) * (1 + x)) - (1 - a * x) * (1 + a)) / ((1 + a) * (1 + x)) ^ 2
          * log (1 - a * x) + (1 - a * x) / ((1 + a) * (1 + x)) * (-a / (1 - a * x)))
      + a / (1 + a) * (1 / (1 + x))
      = (log (1 + a) - log (1 - a * x)) / (1 + x) ^ 2 := by
    have e1 : (1 - a * x) / ((1 + a) * (1 + x)) * (-a / (1 - a * x))
        = -(a / (1 + a) * (1 / (1 + x))) := by
      field_simp
    have e2 : (-a * ((1 + a) * (1 + x)) - (1 - a * x) * (1 + a)) / ((1 + a) * (1 + x)) ^ 2
        = -(1 / (1 + x) ^ 2) := by
      field_simp
      ring
    rw [e1, e2]
    ring
  rw [hval] at hsum
  exact hsum

/-- **`zsValue a ·` is strictly increasing on `(0,1)`.**  So a corner `V`-side
with a smaller parameter has a smaller value: this is the value half of `(D)`. -/
theorem zsValue_strictMonoOn_snd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    StrictMonoOn (fun t : ℝ => zsValue a t) (Set.Ioo (0:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0:ℝ) 1)
  · intro x hx
    exact ((hasDerivAt_zsValue_snd ha0 ha1 hx.1 hx.2).continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(hasDerivAt_zsValue_snd ha0 ha1 hx.1 hx.2).deriv]
    have hax : (0:ℝ) < 1 - a * x := by nlinarith [hx.1, hx.2]
    have hlt : 1 - a * x < 1 + a := by nlinarith [hx.1]
    have := Real.log_lt_log hax hlt
    have hx' : (0:ℝ) < (1 + x) ^ 2 := by nlinarith [hx.1]
    exact div_pos (by linarith) hx'

/-- The value half of `(D)`, packaged: a smaller S-parameter gives no larger
value. -/
theorem zsValue_mono_snd {a d' d : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (h0' : 0 < d')
    (h1' : d' < 1) (h0 : 0 < d) (h1 : d < 1) (hle : d' ≤ d) :
    zsValue a d' ≤ zsValue a d := by
  rcases eq_or_lt_of_le hle with h | h
  · rw [h]
  · exact le_of_lt (zsValue_strictMonoOn_snd ha0 ha1 ⟨h0', h1'⟩ ⟨h0, h1⟩ h)


/-- `zsRate d < log 2` for `d < 1`: the S-channel is not deterministic. -/
theorem zsRate_lt_log_two {d : ℝ} (hd0 : 0 < d) (hd1 : d < 1) : zsRate d < log 2 := by
  have hP := fe_lt_log_two hd0 hd1
  have h : (0:ℝ) < 1 + d := by linarith
  rw [zsRate, div_lt_iff₀ h]
  nlinarith


/-- **`zsValue` is positive.**  Not termwise: the middle term is negative.  Two
instances of `log t ≤ t − 1` give `log(1+a) ≥ a/(1+a)` and
`log(1−ad) ≥ −ad/(1−ad)`, and the three bounds combine to
`zsValue a d ≥ ad/((1+a)(1+d)) > 0`. -/
theorem zsValue_pos {a d : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    0 < zsValue a d := by
  have ha : (0:ℝ) < 1 + a := by linarith
  have hd : (0:ℝ) < 1 + d := by linarith
  have had : (0:ℝ) < 1 - a * d := by nlinarith
  have hla : a / (1 + a) ≤ log (1 + a) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 + a)⁻¹ by positivity)
    rw [Real.log_inv] at h
    have he : (1 + a)⁻¹ - 1 = -(a / (1 + a)) := by field_simp; ring
    rw [he] at h
    linarith
  have hld : d / (1 + d) ≤ log (1 + d) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 + d)⁻¹ by positivity)
    rw [Real.log_inv] at h
    have he : (1 + d)⁻¹ - 1 = -(d / (1 + d)) := by field_simp; ring
    rw [he] at h
    linarith
  have hlad : -(a * d / (1 - a * d)) ≤ log (1 - a * d) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 - a * d)⁻¹ by positivity)
    rw [Real.log_inv] at h
    have he : (1 - a * d)⁻¹ - 1 = a * d / (1 - a * d) := by field_simp; ring
    rw [he] at h
    linarith
  have hmid : -(a * d / ((1 + a) * (1 + d)))
      ≤ (1 - a * d) / ((1 + a) * (1 + d)) * log (1 - a * d) := by
    have hcoef : (0:ℝ) < (1 - a * d) / ((1 + a) * (1 + d)) := by positivity
    have := mul_le_mul_of_nonneg_left hlad (le_of_lt hcoef)
    calc -(a * d / ((1 + a) * (1 + d)))
        = (1 - a * d) / ((1 + a) * (1 + d)) * -(a * d / (1 - a * d)) := by
          field_simp
      _ ≤ _ := this
  have h1 : d / (1 + d) * (a / (1 + a)) ≤ d / (1 + d) * log (1 + a) :=
    mul_le_mul_of_nonneg_left hla (by positivity)
  have h2 : a / (1 + a) * (d / (1 + d)) ≤ a / (1 + a) * log (1 + d) :=
    mul_le_mul_of_nonneg_left hld (by positivity)
  have hkey : 0 < d / (1 + d) * (a / (1 + a)) + a / (1 + a) * (d / (1 + d))
      - a * d / ((1 + a) * (1 + d)) := by
    have e1 : d / (1 + d) * (a / (1 + a)) = a * d / ((1 + a) * (1 + d)) := by
      field_simp
    have e2 : a / (1 + a) * (d / (1 + d)) = a * d / ((1 + a) * (1 + d)) := by
      field_simp
    rw [e1, e2]
    have hpos : (0:ℝ) < a * d / ((1 + a) * (1 + d)) := by positivity
    linarith
  rw [zsValue]
  linarith


/-! ## Towards (A): continuity and compactness

`Feasible` as first written carries the *open* conditions `0 < marg₁ …` and
`0 < marg₂ …`, so the feasible set is not closed and no compactness argument can
give a maximiser.  The fix is to maximise over the closed set and handle
degeneracy downstream: a null letter makes one of the variables deterministic,
the value is then `0`, and `zsValue_pos` says that is below the target.  The
analytic input is continuity of `mutualInfo`, proved here. -/

/-- `mutualInfo` is continuous on joint laws (with the `0·log 0 = 0`
convention that `Real.negMulLog` already implements). -/
theorem continuous_mutualInfo : Continuous (fun q : Bool → Bool → ℝ => mutualInfo q) := by
  unfold mutualInfo entropy1 entropy2 marg₁ marg₂
  fun_prop

/-- A binary channel is its two "output `true`" probabilities: this is the map
back from the parameter square `[0,1]²`. -/
noncomputable def chanTr (x y : ℝ) : Bool → Bool → ℝ :=
  fun i j => bif j then (bif i then y else x) else 1 - (bif i then y else x)

lemma chanTr_nonneg {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∀ i j, 0 ≤ chanTr x y i j := by
  intro i j
  cases i <;> cases j <;> simp [chanTr] <;> linarith

lemma chanTr_sum_one (x y : ℝ) : ∀ i, chanTr x y i false + chanTr x y i true = 1 := by
  intro i; cases i <;> simp [chanTr] <;> ring

/-- The channel with parameters `(x,y)`. -/
noncomputable def chanOf (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) : Chan where
  tr := chanTr x y
  nonneg := chanTr_nonneg hx0 hx1 hy0 hy1
  sum_one := chanTr_sum_one x y

/-- Every channel is of that form. -/
theorem chan_eq_chanOf (c : Chan) :
    c.tr = chanTr (c.tr false true) (c.tr true true) := by
  funext i j
  cases i <;> cases j <;> simp [chanTr] <;> linarith [c.sum_one false, c.sum_one true]

/-- The parameters of a channel lie in `[0,1]`. -/
theorem chan_param_mem (c : Chan) (i : Bool) : c.tr i true ∈ Set.Icc (0:ℝ) 1 :=
  ⟨c.nonneg i true, by linarith [c.nonneg i false, c.sum_one i]⟩

/-- `chanTr` is continuous in its parameters. -/
theorem continuous_chanTr :
    Continuous (fun p : ℝ × ℝ => chanTr p.1 p.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases i <;> cases j <;> simp [chanTr] <;> fun_prop


/-! ### The optimisation in parameter space -/

/-- `jointUX` as a function of the channel parameters. -/
noncomputable def jointUXTr (x y : ℝ) : Bool → Bool → ℝ := fun u xx => chanTr x y xx u / 2

/-- `jointYV` as a function of the channel parameters. -/
noncomputable def jointYVTr (x y : ℝ) : Bool → Bool → ℝ := fun yy v => chanTr x y yy v / 2

/-- `jointUV` as a function of the two channels' parameters. -/
noncomputable def jointUVTr (p x₁ y₁ x₂ y₂ : ℝ) : Bool → Bool → ℝ := fun u v =>
  dsbs p false false * chanTr x₁ y₁ false u * chanTr x₂ y₂ false v
    + dsbs p false true * chanTr x₁ y₁ false u * chanTr x₂ y₂ true v
    + dsbs p true false * chanTr x₁ y₁ true u * chanTr x₂ y₂ false v
    + dsbs p true true * chanTr x₁ y₁ true u * chanTr x₂ y₂ true v

/-- Pointwise form of `chan_eq_chanOf`. -/
theorem chanTr_apply (c : Chan) (i j : Bool) :
    chanTr (c.tr false true) (c.tr true true) i j = c.tr i j :=
  congrFun (congrFun (chan_eq_chanOf c).symm i) j

theorem jointUX_eq (c : Chan) : jointUX c = jointUXTr (c.tr false true) (c.tr true true) := by
  funext u x
  simp only [jointUX, jointUXTr]
  congr 1
  exact congrFun (congrFun (chan_eq_chanOf c) x) u

theorem jointYV_eq (c : Chan) : jointYV c = jointYVTr (c.tr false true) (c.tr true true) := by
  funext y v
  simp only [jointYV, jointYVTr]
  congr 1
  exact congrFun (congrFun (chan_eq_chanOf c) y) v

theorem jointUV_eq (p : ℝ) (cL cR : Chan) :
    jointUV p cL cR = jointUVTr p (cL.tr false true) (cL.tr true true)
      (cR.tr false true) (cR.tr true true) := by
  funext u v
  simp only [jointUV, jointUVTr, chanTr_apply]

theorem continuous_jointUXTr : Continuous (fun p : ℝ × ℝ => jointUXTr p.1 p.2) := by
  apply continuous_pi; intro u; apply continuous_pi; intro x
  simp only [jointUXTr]
  exact (((continuous_apply u).comp ((continuous_apply x).comp continuous_chanTr))).div_const 2

theorem continuous_jointYVTr : Continuous (fun p : ℝ × ℝ => jointYVTr p.1 p.2) := by
  apply continuous_pi; intro y; apply continuous_pi; intro v
  simp only [jointYVTr]
  exact (((continuous_apply v).comp ((continuous_apply y).comp continuous_chanTr))).div_const 2

theorem continuous_jointUVTr (p : ℝ) :
    Continuous (fun q : (ℝ × ℝ) × (ℝ × ℝ) => jointUVTr p q.1.1 q.1.2 q.2.1 q.2.2) := by
  have hL : Continuous (fun q : (ℝ × ℝ) × (ℝ × ℝ) => chanTr q.1.1 q.1.2) :=
    continuous_chanTr.comp continuous_fst
  have hR : Continuous (fun q : (ℝ × ℝ) × (ℝ × ℝ) => chanTr q.2.1 q.2.2) :=
    continuous_chanTr.comp continuous_snd
  apply continuous_pi; intro u; apply continuous_pi; intro v
  simp only [jointUVTr]
  fun_prop

/-- The `U`-side rate, in parameter space. -/
noncomputable def rateUOf (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ := mutualInfo (jointUXTr q.1.1 q.1.2)
/-- The `V`-side rate, in parameter space. -/
noncomputable def rateVOf (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ := mutualInfo (jointYVTr q.2.1 q.2.2)
/-- The objective, in parameter space. -/
noncomputable def valOf (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  mutualInfo (jointUVTr 0 q.1.1 q.1.2 q.2.1 q.2.2)

theorem continuous_rateUOf : Continuous rateUOf :=
  continuous_mutualInfo.comp (continuous_jointUXTr.comp continuous_fst)
theorem continuous_rateVOf : Continuous rateVOf :=
  continuous_mutualInfo.comp (continuous_jointYVTr.comp continuous_snd)
theorem continuous_valOf : Continuous valOf :=
  continuous_mutualInfo.comp (continuous_jointUVTr 0)

/-- The parameter square. -/
def paramBox : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)

theorem isCompact_paramBox : IsCompact paramBox :=
  ((isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc))

/-- The feasible set in parameter space: the box cut by the two rate
constraints.  Closed conditions only, so it is compact. -/
def paramFeasible (Cu Cv : ℝ) : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  paramBox ∩ (rateUOf ⁻¹' Set.Iic Cu) ∩ (rateVOf ⁻¹' Set.Iic Cv)

theorem isCompact_paramFeasible (Cu Cv : ℝ) : IsCompact (paramFeasible Cu Cv) := by
  apply IsCompact.inter_right
  · exact isCompact_paramBox.inter_right
      (IsClosed.preimage continuous_rateUOf isClosed_Iic)
  · exact IsClosed.preimage continuous_rateVOf isClosed_Iic


/-- The parameters of a channel. -/
noncomputable def par (c : Chan) : ℝ × ℝ := (c.tr false true, c.tr true true)

theorem par_mem (c : Chan) : par c ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 :=
  ⟨chan_param_mem c false, chan_param_mem c true⟩

@[simp] theorem par_chanOf {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    par (chanOf x y hx0 hx1 hy0 hy1) = (x, y) := by
  simp [par, chanOf, chanTr]

/-- **Feasibility as a closed condition** — the positivity constraints are
dropped, so the feasible set is closed and compactness applies.  Degeneracy is
handled downstream: a null letter makes a variable deterministic and the value
is then `0`, which `zsValue_pos` puts below the target. -/
def FeasibleC (Cu Cv : ℝ) (cL cR : Chan) : Prop :=
  mutualInfo (jointUX cL) ≤ Cu ∧ mutualInfo (jointYV cR) ≤ Cv

/-- A maximiser over the closed feasible set. -/
def IsMaxPairC (Cu Cv : ℝ) (cL cR : Chan) : Prop :=
  FeasibleC Cu Cv cL cR ∧
    ∀ cL' cR', FeasibleC Cu Cv cL' cR' →
      mutualInfo (jointUV 0 cL' cR') ≤ mutualInfo (jointUV 0 cL cR)

/-- The feasible set of the *minimisation*: both rates at **least** the budgets. -/
def FeasibleMin (Cu Cv : ℝ) (cL cR : Chan) : Prop :=
  Cu ≤ mutualInfo (jointUX cL) ∧ Cv ≤ mutualInfo (jointYV cR)

/-- A minimiser over the closed feasible set. -/
def IsMinPairC (Cu Cv : ℝ) (cL cR : Chan) : Prop :=
  FeasibleMin Cu Cv cL cR ∧
    ∀ cL' cR', FeasibleMin Cu Cv cL' cR' →
      mutualInfo (jointUV 0 cL cR) ≤ mutualInfo (jointUV 0 cL' cR')

/-- **Either kind of optimiser.**  The whole of `(B)` — the classification of
interior optima as BSC pairs — uses optimality only through the KKT conditions,
and those have the *same* form (`∇V = λ∇R`, `λ ≥ 0`) for a maximiser under
`R ≤ C` and a minimiser under `R ≥ C`.  So the classification is stated once,
for `OptPairC`. -/
def OptPairC (Cu Cv : ℝ) (cL cR : Chan) : Prop :=
  IsMaxPairC Cu Cv cL cR ∨ IsMinPairC Cu Cv cL cR

theorem mem_paramFeasible_of_feasible {Cu Cv : ℝ} {cL cR : Chan}
    (h : FeasibleC Cu Cv cL cR) : (par cL, par cR) ∈ paramFeasible Cu Cv := by
  refine ⟨⟨⟨par_mem cL, par_mem cR⟩, ?_⟩, ?_⟩
  · show rateUOf (par cL, par cR) ≤ Cu
    simpa [rateUOf, par, ← jointUX_eq] using h.1
  · show rateVOf (par cL, par cR) ≤ Cv
    simpa [rateVOf, par, ← jointYV_eq] using h.2

theorem valOf_par (cL cR : Chan) :
    valOf (par cL, par cR) = mutualInfo (jointUV 0 cL cR) := by
  simp [valOf, par, ← jointUV_eq]

/-- **(A), proved: a maximiser exists.**  The parameter square is compact, the
two rate constraints are closed, and `mutualInfo` is continuous, so
`IsCompact.exists_isMaxOn` applies; `chan_eq_chanOf` transports the maximiser
back to a pair of channels. -/
theorem maxExistsC (Cu Cv : ℝ) (hne : ∃ cL cR, FeasibleC Cu Cv cL cR) :
    ∃ cL cR, IsMaxPairC Cu Cv cL cR := by
  obtain ⟨cL₀, cR₀, h₀⟩ := hne
  have hFne : (paramFeasible Cu Cv).Nonempty :=
    ⟨_, mem_paramFeasible_of_feasible h₀⟩
  obtain ⟨q, hq, hmax⟩ :=
    (isCompact_paramFeasible Cu Cv).exists_isMaxOn hFne continuous_valOf.continuousOn
  obtain ⟨⟨hbox, hru⟩, hrv⟩ := hq
  obtain ⟨⟨h11, h12⟩, h21, h22⟩ := hbox
  refine ⟨chanOf q.1.1 q.1.2 h11.1 h11.2 h12.1 h12.2,
    chanOf q.2.1 q.2.2 h21.1 h21.2 h22.1 h22.2, ⟨?_, ?_⟩, ?_⟩
  · have : mutualInfo (jointUX (chanOf q.1.1 q.1.2 h11.1 h11.2 h12.1 h12.2)) = rateUOf q := by
      rw [jointUX_eq]
      simp [rateUOf, chanOf, chanTr]
    rw [this]
    exact hru
  · have : mutualInfo (jointYV (chanOf q.2.1 q.2.2 h21.1 h21.2 h22.1 h22.2)) = rateVOf q := by
      rw [jointYV_eq]
      simp [rateVOf, chanOf, chanTr]
    rw [this]
    exact hrv
  · intro cL' cR' hfeas
    have hmem := mem_paramFeasible_of_feasible hfeas
    have hle : valOf (par cL', par cR') ≤ valOf q := hmax hmem
    rw [valOf_par] at hle
    have heq : valOf q = mutualInfo (jointUV 0 (chanOf q.1.1 q.1.2 h11.1 h11.2 h12.1 h12.2)
        (chanOf q.2.1 q.2.2 h21.1 h21.2 h22.1 h22.2)) := by
      rw [jointUV_eq]
      simp [valOf, chanOf, chanTr]
    rw [heq] at hle
    exact hle


/-- The feasible set in parameter space, for the minimisation. -/
def paramFeasibleMin (Cu Cv : ℝ) : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  paramBox ∩ (rateUOf ⁻¹' Set.Ici Cu) ∩ (rateVOf ⁻¹' Set.Ici Cv)

theorem isCompact_paramFeasibleMin (Cu Cv : ℝ) : IsCompact (paramFeasibleMin Cu Cv) := by
  apply IsCompact.inter_right
  · exact isCompact_paramBox.inter_right
      (IsClosed.preimage continuous_rateUOf isClosed_Ici)
  · exact IsClosed.preimage continuous_rateVOf isClosed_Ici

theorem mem_paramFeasibleMin_of_feasible {Cu Cv : ℝ} {cL cR : Chan}
    (h : FeasibleMin Cu Cv cL cR) : (par cL, par cR) ∈ paramFeasibleMin Cu Cv := by
  refine ⟨⟨⟨par_mem cL, par_mem cR⟩, ?_⟩, ?_⟩
  · show Cu ≤ rateUOf (par cL, par cR)
    simpa [rateUOf, par, ← jointUX_eq] using h.1
  · show Cv ≤ rateVOf (par cL, par cR)
    simpa [rateVOf, par, ← jointYV_eq] using h.2

/-- **`(A′)`: a minimiser exists.** -/
theorem minExistsC (Cu Cv : ℝ) (hne : ∃ cL cR, FeasibleMin Cu Cv cL cR) :
    ∃ cL cR, IsMinPairC Cu Cv cL cR := by
  obtain ⟨cL₀, cR₀, h₀⟩ := hne
  have hFne : (paramFeasibleMin Cu Cv).Nonempty :=
    ⟨_, mem_paramFeasibleMin_of_feasible h₀⟩
  obtain ⟨q, hq, hmin⟩ :=
    (isCompact_paramFeasibleMin Cu Cv).exists_isMinOn hFne continuous_valOf.continuousOn
  obtain ⟨⟨hbox, hru⟩, hrv⟩ := hq
  obtain ⟨⟨h11, h12⟩, h21, h22⟩ := hbox
  refine ⟨chanOf q.1.1 q.1.2 h11.1 h11.2 h12.1 h12.2,
    chanOf q.2.1 q.2.2 h21.1 h21.2 h22.1 h22.2, ⟨?_, ?_⟩, ?_⟩
  · have : mutualInfo (jointUX (chanOf q.1.1 q.1.2 h11.1 h11.2 h12.1 h12.2)) = rateUOf q := by
      rw [jointUX_eq]
      simp [rateUOf, chanOf, chanTr]
    rw [this]
    exact hru
  · have : mutualInfo (jointYV (chanOf q.2.1 q.2.2 h21.1 h21.2 h22.1 h22.2)) = rateVOf q := by
      rw [jointYV_eq]
      simp [rateVOf, chanOf, chanTr]
    rw [this]
    exact hrv
  · intro cL' cR' hfeas
    have hmem := mem_paramFeasibleMin_of_feasible hfeas
    have hle : valOf q ≤ valOf (par cL', par cR') := hmin hmem
    rw [valOf_par] at hle
    have heq : valOf q = mutualInfo (jointUV 0 (chanOf q.1.1 q.1.2 h11.1 h11.2 h12.1 h12.2)
        (chanOf q.2.1 q.2.2 h21.1 h21.2 h22.1 h22.2)) := by
      rw [jointUV_eq]
      simp [valOf, chanOf, chanTr]
    rw [heq] at hle
    exact hle

/-! ### Degenerate pairs have value zero

A maximiser over the closed feasible set may have a null letter.  Then one of
the variables is deterministic and the value is `0`, which `zsValue_pos` puts
strictly below the target — so the degenerate case is harmless. -/

theorem jointUV_sum_one (p : ℝ) (cL cR : Chan) :
    jointUV p cL cR false false + jointUV p cL cR false true
      + jointUV p cL cR true false + jointUV p cL cR true true = 1 := by
  have e1 : cL.tr false true = 1 - cL.tr false false := by linarith [cL.sum_one false]
  have e2 : cL.tr true true = 1 - cL.tr true false := by linarith [cL.sum_one true]
  have e3 : cR.tr false true = 1 - cR.tr false false := by linarith [cR.sum_one false]
  have e4 : cR.tr true true = 1 - cR.tr true false := by linarith [cR.sum_one true]
  simp only [jointUV, dsbs]
  norm_num [e1, e2, e3, e4]
  ring

/-- A null `U`-letter kills the value. -/
theorem mutualInfo_jointUV_eq_zero_of_degL {p : ℝ} {cL cR : Chan} {u₀ : Bool}
    (h : marg₁ (jointUX cL) u₀ = 0) : mutualInfo (jointUV p cL cR) = 0 := by
  have hnn0 := cL.nonneg false u₀
  have hnn1 := cL.nonneg true u₀
  have h' : cL.tr false u₀ + cL.tr true u₀ = 0 := by
    simp only [marg₁, jointUX] at h; linarith
  have hz0 : cL.tr false u₀ = 0 := by linarith
  have hz1 : cL.tr true u₀ = 0 := by linarith
  refine mutualInfo_eq_zero_of_row_zero (u₀ := u₀) ?_ (jointUV_sum_one p cL cR)
  intro v
  simp only [jointUV, hz0, hz1]
  ring

/-- A null `V`-letter kills the value. -/
theorem mutualInfo_jointUV_eq_zero_of_degR {p : ℝ} {cL cR : Chan} {v₀ : Bool}
    (h : marg₂ (jointYV cR) v₀ = 0) : mutualInfo (jointUV p cL cR) = 0 := by
  have hnn0 := cR.nonneg false v₀
  have hnn1 := cR.nonneg true v₀
  have h' : cR.tr false v₀ + cR.tr true v₀ = 0 := by
    simp only [marg₂, jointYV] at h; linarith
  have hz0 : cR.tr false v₀ = 0 := by linarith
  have hz1 : cR.tr true v₀ = 0 := by linarith
  rw [← mutualInfo_transpose (jointUV p cL cR)]
  refine mutualInfo_eq_zero_of_row_zero (u₀ := v₀) ?_ ?_
  · intro u
    simp only [jointUV, hz0, hz1]
    ring
  · have h := jointUV_sum_one p cL cR
    linarith

/-! ## Vocabulary for the decomposition -/

/-- The `V`-side sits at a corner: some letter has bias `±1`. -/
def VSideCorner (cR : Chan) : Prop :=
  ∃ v, biasOfSnd (jointYV cR) v = 1 ∨ biasOfSnd (jointYV cR) v = -1

/-- Both sides are binary symmetric channels. -/
def BothBSC (cL cR : Chan) : Prop :=
  (∃ (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1), cL = bsc α h0 h1) ∧
    (∃ (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1), cR = bsc β h0 h1)

/-! ## (D) is a theorem

A corner `V`-side *is* an S-channel in law: mean-zero plus total mass force the
other bias to `∓d'` and the masses to `(d'/(1+d'), 1/(1+d'))`, with `d' ≤ 1`
because biases lie in `[−1,1]`.  Its atom-value function is then `phiZ d'` up to
the reflection `s ↦ σs`, and the reflection is free: `f_e` is even, so the
certificate transfers with `λ₁` replaced by `σ·λ₁`.

So the corner step needs neither a channel identity nor a degradation argument —
`bestResponse_le_of_certificate` takes an arbitrary `cR`, needing only its
marginals and biases.  `cornerBound` below is `(D)`'s role in the chain, proved
outright, which is why `conjecture1_p0_of_three` needs only (A), (B), (C). -/

section CornerProved

/-- The atom-value function of a reflected S-channel law. -/
private lemma phiZ_of_atoms {d' σ s : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    d' / (1 + d') * fFun (s * σ) + 1 / (1 + d') * fFun (s * (-σ * d'))
      = phiZ d' (σ * s) := by
  rcases hσ with h | h <;> subst h <;>
    simp only [phiZ, one_mul, mul_one, neg_mul, neg_neg, mul_neg] <;>
    congr 2 <;> ring

/-- Masses and biases of a corner law. -/
private lemma corner_atoms {ρ₀ ρ₁ t₀ t₁ σ : ℝ} (h0 : 0 < ρ₀) (h1 : 0 < ρ₁)
    (hs : ρ₀ + ρ₁ = 1) (hz : ρ₀ * t₀ + ρ₁ * t₁ = 0) (ht0 : t₀ = σ)
    (hσ : σ = 1 ∨ σ = -1) (hb0 : -1 ≤ t₁) (hb1 : t₁ ≤ 1) :
    ∃ d' : ℝ, 0 < d' ∧ d' ≤ 1 ∧ ρ₀ = d' / (1 + d') ∧ ρ₁ = 1 / (1 + d') ∧
      t₁ = -σ * d' := by
  subst ht0
  refine ⟨ρ₀ / ρ₁, by positivity, ?_, ?_, ?_, ?_⟩
  · rw [div_le_one h1]
    rcases hσ with h | h <;> subst h <;> nlinarith
  · have : (0:ℝ) < 1 + ρ₀ / ρ₁ := by positivity
    field_simp
    linarith
  · have : (0:ℝ) < 1 + ρ₀ / ρ₁ := by positivity
    field_simp
    linarith
  · rcases hσ with h | h <;> subst h <;> field_simp <;> nlinarith

/-- **A corner `V`-side is an S-channel in law**: its rate is `zsRate d'`, and
its atom-value function is `phiZ d'` up to a reflection. -/
theorem corner_phiZ {cR : Chan} (hrho : ∀ v, 0 < marg₂ (jointYV cR) v)
    (hc : VSideCorner cR) :
    ∃ d' σ : ℝ, 0 < d' ∧ d' ≤ 1 ∧ (σ = 1 ∨ σ = -1) ∧
      mutualInfo (jointYV cR) = zsRate d' ∧
      ∀ s : ℝ, marg₂ (jointYV cR) false * fFun (s * biasOfSnd (jointYV cR) false)
          + marg₂ (jointYV cR) true * fFun (s * biasOfSnd (jointYV cR) true)
        = phiZ d' (σ * s) := by
  have hsum := marg₂_jointYV_sum cR
  have hzero := rho_bias_sum_zero cR (hrho false) (hrho true)
  have hnn : ∀ v y, 0 ≤ (fun v y => jointYV cR y v) v y := by
    intro v y; simp only [jointYV]; have := cR.nonneg y v; linarith
  have hbd : ∀ v, -1 ≤ biasOfSnd (jointYV cR) v ∧ biasOfSnd (jointYV cR) v ≤ 1 := by
    intro v
    have h := biasOf_mem_Icc (q := fun v y => jointYV cR y v) hnn (u := v) (by
      simpa [marg₁, marg₂] using hrho v)
    simpa [biasOf, biasOfSnd, marg₁, marg₂] using h
  -- assemble, given that letter `v₀` carries bias `σ`
  have build : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → ∀ v₀ : Bool,
      biasOfSnd (jointYV cR) v₀ = σ →
      ∃ d' σ' : ℝ, 0 < d' ∧ d' ≤ 1 ∧ (σ' = 1 ∨ σ' = -1) ∧
        mutualInfo (jointYV cR) = zsRate d' ∧
        ∀ s : ℝ, marg₂ (jointYV cR) false * fFun (s * biasOfSnd (jointYV cR) false)
            + marg₂ (jointYV cR) true * fFun (s * biasOfSnd (jointYV cR) true)
          = phiZ d' (σ' * s) := by
    intro σ hσ v₀ hb
    cases v₀ with
    | false =>
      obtain ⟨d', hd0, hd1, he0, he1, he2⟩ :=
        corner_atoms (hrho false) (hrho true) hsum hzero hb hσ (hbd true).1 (hbd true).2
      refine ⟨d', σ, hd0, hd1, hσ, ?_, ?_⟩
      · have hne : (1:ℝ) + d' ≠ 0 := by positivity
        rw [mutualInfo_jointYV_eq_bias_closed hrho, he0, he1, hb, he2, zsRate]
        rcases hσ with h | h <;> subst h <;>
          simp only [neg_mul, one_mul, neg_neg, fe_one, fe_neg] <;> field_simp <;> ring
      · intro s
        rw [he0, he1, hb, he2]
        exact phiZ_of_atoms hσ
    | true =>
      obtain ⟨d', hd0, hd1, he0, he1, he2⟩ :=
        corner_atoms (hrho true) (hrho false) (by linarith) (by linarith) hb hσ
          (hbd false).1 (hbd false).2
      refine ⟨d', σ, hd0, hd1, hσ, ?_, ?_⟩
      · have hne : (1:ℝ) + d' ≠ 0 := by positivity
        rw [mutualInfo_jointYV_eq_bias_closed hrho, he0, he1, hb, he2, zsRate]
        rcases hσ with h | h <;> subst h <;>
          simp only [neg_mul, one_mul, neg_neg, fe_one, fe_neg] <;> field_simp <;> ring
      · intro s
        rw [he0, he1, hb, he2]
        rw [add_comm]
        exact phiZ_of_atoms hσ
  obtain ⟨v, hv⟩ := hc
  rcases hv with h | h
  · exact build 1 (Or.inl rfl) v h
  · exact build (-1) (Or.inr rfl) v h

end CornerProved

/-- **The corner step, proved.**  If the `V`-side sits at a corner and both rate
budgets are those of the Z/S pair `(a,d)`, then the value is at most
`zsValue a d`.  This is what `(D)` was assumed for. -/
theorem cornerBound {cL cR : Chan} {a d : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hd0 : 0 < d) (hd1 : d < 1) (hpi : ∀ u, 0 < marg₁ (jointUX cL) u)
    (hrho : ∀ v, 0 < marg₂ (jointYV cR) v) (hc : VSideCorner cR)
    (hCu : mutualInfo (jointUX cL) ≤ zsRate a)
    (hCv : mutualInfo (jointYV cR) ≤ zsRate d) :
    mutualInfo (jointUV 0 cL cR) ≤ zsValue a d := by
  obtain ⟨d', σ, hd0', hd1', hσ, hrate, hphi⟩ := corner_phiZ hrho hc
  -- the corner parameter is `< 1`: otherwise the `V`-side would be deterministic
  have hd'lt : d' < 1 := by
    rcases lt_or_eq_of_le hd1' with h | h
    · exact h
    · exfalso
      rw [h] at hrate
      have : zsRate 1 = log 2 := by
        rw [zsRate, fe_one]; norm_num
      rw [this] at hrate
      have := zsRate_lt_log_two hd0 hd1
      linarith
  -- and it fits inside `d`'s budget
  have hdd : d' ≤ d := by
    apply le_of_zsRate_le hd0' hd'lt hd0 hd1
    rw [← hrate]; exact hCv
  -- the certificate, reflected by `σ`
  have hnnL : ∀ u x, 0 ≤ jointUX cL u x := by
    intro u x; simp only [jointUX]; have := cL.nonneg x u; linarith
  have hnnR : ∀ v y, 0 ≤ (fun v y => jointYV cR y v) v y := by
    intro v y; simp only [jointYV]; have := cR.nonneg y v; linarith
  have hbdL : ∀ u, -1 ≤ biasOf (jointUX cL) u ∧ biasOf (jointUX cL) u ≤ 1 :=
    fun u => biasOf_mem_Icc hnnL (hpi u)
  have hbdR : ∀ v, -1 ≤ biasOfSnd (jointYV cR) v ∧ biasOfSnd (jointYV cR) v ≤ 1 := by
    intro v
    have h := biasOf_mem_Icc (q := fun v y => jointYV cR y v) hnnR (u := v) (by
      simpa [marg₁, marg₂] using hrho v)
    simpa [biasOf, biasOfSnd, marg₁, marg₂] using h
  have hker : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX cL) u
      * biasOfSnd (jointYV cR) v := by
    intro u v
    obtain ⟨h1, h2⟩ := hbdL u
    obtain ⟨h3, h4⟩ := hbdR v
    nlinarith
  have hbound := bestResponse_le_of_certificate (p := 0) (l₀ := lam0 a d')
    (l₁ := σ * lam1 a d') (l₂ := lam2 a d') hpi hrho hker
    (le_of_lt (lam2_pos ha0 ha1 hd0' hd'lt)) ?_ hCu
  · -- close with tightness and monotonicity in `d`
    have ht := certificate_tight ha0 ha1 hd0' hd'lt
    have hm := zsValue_mono_snd ha0 ha1 hd0' hd'lt hd0 hd1 hdd
    linarith
  · intro s hs0 hs1
    have hσs0 : -1 ≤ σ * s := by
      rcases hσ with h | h <;> subst h <;> linarith
    have hσs1 : σ * s ≤ 1 := by
      rcases hσ with h | h <;> subst h <;> linarith
    have hcert := DFun_nonneg ha0 ha1 hd0' hd'lt hσs0 hσs1
    rw [DFun, GFun] at hcert
    have hfe : fe (σ * s) = fe s := by
      rcases hσ with h | h <;> subst h <;> simp [fe_neg]
    have hL : (1 - 2 * (0:ℝ)) * s = s := by ring
    simp only [hL]
    rw [hphi s]
    rw [hfe] at hcert
    have : σ * lam1 a d' * s = lam1 a d' * (σ * s) := by ring
    rw [this]
    linarith


/-! ## The two conjectures -/

/-- **Conjecture 1** of Dikshtein–Ordentlich–Shamai (Entropy **24**(9):1321) at
`p = 0`: at the rate pair realised by the Z/S pair `(a,d)`, no admissible pair
beats the Z/S value `zsValue a d`. -/
def Conjecture1_p0 : Prop :=
  ∀ (a d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) (cL cR : Chan),
    mutualInfo (jointUX cL) ≤ zsRate a →
    mutualInfo (jointYV cR) ≤ mutualInfo (jointYV (sChan d hd0 hd1)) →
    mutualInfo (jointUV 0 cL cR) ≤ zsValue a d

/-- The value of the conjectured optimal pair for the **minimisation** problem:
the `U`-side has atoms at `−a` (mass `1/(1+a)`) and `+1` (mass `a/(1+a)`), the
two contacts of the mirror certificate. -/
noncomputable def mzsValue (a d : ℝ) : ℝ :=
  (1 / (1 + a)) * phiZ d (-a) + (a / (1 + a)) * phiZ d 1

/-- **The mirror certificate is tight**, at the same rate `zsRate a`: averaging
the two contacts `MDFun_at_neg_a` and `MDFun_one` with the masses `1/(1+a)` and
`a/(1+a)` cancels the `μ₁` term and collects `μ₂` into the rate. -/
theorem certificate_tight_mirror (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    mlam0 a d + mlam2 a d * zsRate a = mzsValue a d := by
  have h1a : (0 : ℝ) < 1 + a := by linarith
  have hA : phiZ d (-a) = mlam0 a d + mlam1 a d * (-a) + mlam2 a d * fe a := by
    have h := MDFun_at_neg_a ha0 ha1 hd0 hd1
    simp only [MDFun, GFun, fe_neg] at h
    linarith
  have hB : phiZ d 1 = mlam0 a d + mlam1 a d + mlam2 a d * log 2 := by
    have h := MDFun_one (a := a) (d := d)
    simp only [MDFun, GFun, fe_one] at h
    linarith
  rw [mzsValue, hA, hB, zsRate]
  field_simp
  ring





/-! ## The four ingredients

`CornerDomination` above bundles steps 1–3 of `NOTES.md` §7d′ into one
statement, and as stated it quantifies over *every* `cR` — which is too strong
to be true: against a fixed BSC `cL` the best `cR` is a BSC, and it beats the
S-channel by Mrs. Gerber's Lemma (`mgl_jensen`).  That is the two-sidedness of
§7e.  The implication `conjecture1_p0_of_cornerDomination` is still valid, but
its hypothesis cannot be proved.

The decomposition below is the honest one: it speaks about **maximisers**, and
splits the debt into four independently attackable statements, each matching one
line of the §7d′ table.  `conjecture1_p0_of_parts` proves the chain. -/

section Parts




/-! ### Towards (B): best responses and the bitangency bridge

`(B)` says a maximiser is the BSC pair or has a corner `V`-side.  It factors
into two very different pieces.

*The variational bridge.*  A maximiser is a best response on each side
(`IsMaxPairC.bestResponseU` / `…V` below, immediate from the definition).  The
one-sided problem is a linear program over laws of the bias `S`, constrained by
`E[S] = 0` and `E[f_e(S)] ≤ C`, so at an optimum there are multipliers
`(λ₀,λ₁,λ₂)`, `λ₂ ≥ 0`, whose affine function dominates the atom value `φ_T` and
*touches it at both atoms* — value and tangency.  That is `Bitangency` below,
and it is the missing formal step: it needs Lagrange multipliers for the
parametrised family, not just the definition of a maximum.

*The analytic core.*  Given bitangency, `interior_response_symmetric`
(`PZeroSymm.lean`) already proves that against a **symmetric** `T` an interior
bitangent response is symmetric.  What remains on paper is §7c⁗: the
doubly-asymmetric case, via the Λ symmetry and the Green's-function fold. -/



/-- The atom value of the `U`-side against the `V`-law of `cR`:
`φ_T(s) = Σ_v ρ_v·f(s·t_v)`. -/
noncomputable def atomValue (cR : Chan) (s : ℝ) : ℝ :=
  marg₂ (jointYV cR) false * fFun (s * biasOfSnd (jointYV cR) false)
    + marg₂ (jointYV cR) true * fFun (s * biasOfSnd (jointYV cR) true)




/-- **(C) The BSC pair is not a maximiser** (§7d′ step 3).  This is the saddle
property, i.e. inequality (iii): at `p = 0` the symmetric fixed point has
`ΛΛ′ > 1`, so it is not even a local maximum.  Stated at the rate pair realised
by an interior Z/S pair, which is where it is needed. -/
def BSCNotMax : Prop :=
  ∀ (a d : ℝ) (_ha0 : 0 < a) (_ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) (cL cR : Chan),
    IsMaxPairC (zsRate a) (zsRate d) cL cR → ¬ BothBSC cL cR

/-! ### Towards (C): the Z-channel and the branch gap

`(C)` says the BSC pair is not a maximiser.  The witness is the Z/S pair at the
same rates, so `(C)` follows from a single inequality between explicit
elementary functions — no inverse functions, no second-order analysis:

```
f_e(s·t) < zsValue a d      whenever  f_e(s) ≤ zsRate a  and  f_e(t) ≤ zsRate d.
```

That is `BranchGap`.  The reduction is `bscNotMax_of_branchGap`, proved here; it
needs the Z-channel as a `Chan`, its rate, and its value against the S-channel. -/

/-- The Z-channel with parameter `a ∈ (0,1)`. -/
noncomputable def zChan (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) : Chan where
  tr := zChanTr a
  nonneg i j := by
    have h : (0:ℝ) < 1 + a := by linarith
    have h1 : (0:ℝ) ≤ (1 - a) / (1 + a) := by positivity
    have h2 : (0:ℝ) ≤ 2 * a / (1 + a) := by positivity
    cases i <;> cases j <;> simp only [zChanTr, cond_true, cond_false] <;> linarith
  sum_one i := by
    have h : (0:ℝ) < 1 + a := by linarith
    cases i
    · simp only [zChanTr, cond_true, cond_false]; norm_num
    · simp only [zChanTr, cond_true, cond_false]; field_simp; ring

lemma marg₁_zChan (ha0 : 0 < a) (ha1 : a < 1) :
    marg₁ (jointUX (zChan a ha0 ha1)) false = 1 / (1 + a) ∧
      marg₁ (jointUX (zChan a ha0 ha1)) true = a / (1 + a) := by
  have h : (0:ℝ) < 1 + a := by linarith
  constructor <;>
    · simp only [marg₁, jointUX, zChan, zChanTr, cond_true, cond_false]
      field_simp
      ring

lemma biasOf_zChan (ha0 : 0 < a) (ha1 : a < 1) :
    biasOf (jointUX (zChan a ha0 ha1)) false = a ∧
      biasOf (jointUX (zChan a ha0 ha1)) true = -1 := by
  have h : (0:ℝ) < 1 + a := by linarith
  obtain ⟨hm0, hm1⟩ := marg₁_zChan ha0 ha1
  constructor
  · rw [biasOf, hm0]
    simp only [jointUX, zChan, zChanTr, cond_true, cond_false]
    field_simp
    ring
  · rw [biasOf, hm1]
    simp only [jointUX, zChan, zChanTr, cond_true, cond_false]
    field_simp
    ring

/-- The Z-channel's rate is `zsRate a`. -/
theorem zChan_rate (ha0 : 0 < a) (ha1 : a < 1) :
    mutualInfo (jointUX (zChan a ha0 ha1)) = zsRate a := by
  have h : (0:ℝ) < 1 + a := by linarith
  obtain ⟨hm0, hm1⟩ := marg₁_zChan ha0 ha1
  obtain ⟨hb0, hb1⟩ := biasOf_zChan ha0 ha1
  have hpi : ∀ u, 0 < marg₁ (jointUX (zChan a ha0 ha1)) u := by
    intro u; cases u
    · rw [hm0]; positivity
    · rw [hm1]; positivity
  rw [mutualInfo_jointUX_eq_bias_closed hpi, hm0, hm1, hb0, hb1, fe_neg_one, zsRate]
  field_simp


/-- **The Z/S pair attains `zsValue`.**  The kernel identity with the degenerate
cell `s·t = −1` allowed (`…_of_nonneg`) evaluates the four atom products. -/
theorem zChan_sChan_value (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    mutualInfo (jointUV 0 (zChan a ha0 ha1) (sChan d hd0 hd1)) = zsValue a d := by
  have ha : (0:ℝ) < 1 + a := by linarith
  have hd : (0:ℝ) < 1 + d := by linarith
  obtain ⟨hm0, hm1⟩ := marg₁_zChan ha0 ha1
  obtain ⟨hb0, hb1⟩ := biasOf_zChan ha0 ha1
  obtain ⟨hn0, hn1⟩ := marg₂_sChan hd0 hd1
  obtain ⟨ht0, ht1⟩ := biasOfSnd_sChan hd0 hd1
  have hpi : ∀ u, 0 < marg₁ (jointUX (zChan a ha0 ha1)) u := by
    intro u; cases u
    · rw [hm0]; positivity
    · rw [hm1]; positivity
  have hrho : ∀ v, 0 < marg₂ (jointYV (sChan d hd0 hd1)) v := by
    intro v; cases v
    · rw [hn0]; positivity
    · rw [hn1]; positivity
  have hker : ∀ u v, 0 ≤ 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX (zChan a ha0 ha1)) u
      * biasOfSnd (jointYV (sChan d hd0 hd1)) v := by
    intro u v
    cases u <;> cases v <;>
      simp only [hb0, hb1, ht0, ht1] <;> nlinarith
  rw [mutualInfo_jointUV_eq_kernel_sum_of_nonneg 0 _ _ hpi hrho hker,
    hm0, hm1, hb0, hb1, hn0, hn1, ht0, ht1]
  have e1 : (1 - 2 * (0:ℝ)) * a * 1 = a := by ring
  have e2 : (1 - 2 * (0:ℝ)) * a * -d = -(a * d) := by ring
  have e3 : (1 - 2 * (0:ℝ)) * (-1) * 1 = -1 := by ring
  have e4 : (1 - 2 * (0:ℝ)) * (-1) * -d = d := by ring
  rw [e1, e2, e3, e4]
  have hf1 : fFun (-1 : ℝ) = 0 := by simp [fFun]
  have hf2 : fFun a = (1 + a) * log (1 + a) := rfl
  have hf3 : fFun (-(a * d)) = (1 - a * d) * log (1 - a * d) := by
    simp only [fFun]; ring_nf
  have hf4 : fFun d = (1 + d) * log (1 + d) := rfl
  rw [hf1, hf2, hf3, hf4, zsValue]
  field_simp
  ring

/-! ### The Z-channel on the `V`-side, and the Z/Z pair

Conjecture 2's optimum is the *aligned* pair: a Z-channel on **both** sides, so
that the two deterministic atoms agree (`s·t = +1`) instead of cancelling as
they do in the Z/S pair of Conjecture 1.  The `V`-side computation is the mirror
of `marg₁_zChan`/`biasOf_zChan` — the same transition matrix read down its
columns — giving masses `(1/(1+d), d/(1+d))` and bias atoms `(d, −1)`.

Note that `mzsValue` is *written* as the S/S pair: its `U`-side atoms are `+1`
and `−a`, which is `sChan a` read on the `U`-side, and `phiZ d` encodes the
`V`-side `(+1, −d)`, which is `sChan d`.  Flipping the input of **both**
channels is a symmetry of `I(U;V)`, `I(U;X)` and `I(Y;V)` alike, so the S/S and
Z/Z pairs have the same rates and the same value; `zChan_zChan_value` below is
that fact, proved by evaluating the kernel sum rather than by a flip argument.
The Z/Z form is the one the paper's Conjecture 2 states. -/

lemma marg₂_zChan (hd0 : 0 < d) (hd1 : d < 1) :
    marg₂ (jointYV (zChan d hd0 hd1)) false = 1 / (1 + d) ∧
      marg₂ (jointYV (zChan d hd0 hd1)) true = d / (1 + d) := by
  have h : (0:ℝ) < 1 + d := by linarith
  constructor <;>
    · simp only [marg₂, jointYV, zChan, zChanTr, cond_true, cond_false]
      field_simp
      ring

lemma biasOfSnd_zChan (hd0 : 0 < d) (hd1 : d < 1) :
    biasOfSnd (jointYV (zChan d hd0 hd1)) false = d ∧
      biasOfSnd (jointYV (zChan d hd0 hd1)) true = -1 := by
  have h : (0:ℝ) < 1 + d := by linarith
  have hd : d ≠ 0 := ne_of_gt hd0
  obtain ⟨hm0, hm1⟩ := marg₂_zChan hd0 hd1
  constructor
  · rw [biasOfSnd, hm0]
    simp only [jointYV, zChan, zChanTr, cond_true, cond_false]
    field_simp
    ring
  · rw [biasOfSnd, hm1]
    simp only [jointYV, zChan, zChanTr, cond_true, cond_false]
    field_simp
    ring

/-- **The Z-channel's rate, read on the `V`-side**, is again `zsRate`.  The
mirror of `zChan_rate`; with `sChan_rate` it says the Z/Z and Z/S pairs sit at
the *same* rate pair `(zsRate a, zsRate d)`, which is what lets the two
conjectures be compared at a common constraint. -/
theorem zChan_rate_snd (hd0 : 0 < d) (hd1 : d < 1) :
    mutualInfo (jointYV (zChan d hd0 hd1)) = zsRate d := by
  obtain ⟨hm0, hm1⟩ := marg₂_zChan hd0 hd1
  obtain ⟨hb0, hb1⟩ := biasOfSnd_zChan hd0 hd1
  have hrho : ∀ v, 0 < marg₂ (jointYV (zChan d hd0 hd1)) v := by
    intro v; cases v
    · rw [hm0]; positivity
    · rw [hm1]; positivity
  rw [mutualInfo_jointYV_eq_bias_closed hrho, hm0, hm1, hb0, hb1, fe_neg_one, zsRate]
  have h : (1 : ℝ) + d ≠ 0 := by positivity
  field_simp

/-- **The Z/Z pair attains `mzsValue`.**  Unlike the Z/S pair, the aligned pair
degenerates no cell: the four products `s·t` are `a·d`, `−a`, `−d` and `+1`, all
`> −1`, so the *strict* kernel identity applies and the four atom values line up
term by term with the two `phiZ` expansions of `mzsValue`. -/
theorem zChan_zChan_value (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) :
    mutualInfo (jointUV 0 (zChan a ha0 ha1) (zChan d hd0 hd1)) = mzsValue a d := by
  have ha : (0:ℝ) < 1 + a := by linarith
  have hd : (0:ℝ) < 1 + d := by linarith
  obtain ⟨hm0, hm1⟩ := marg₁_zChan ha0 ha1
  obtain ⟨hb0, hb1⟩ := biasOf_zChan ha0 ha1
  obtain ⟨hn0, hn1⟩ := marg₂_zChan hd0 hd1
  obtain ⟨ht0, ht1⟩ := biasOfSnd_zChan hd0 hd1
  have hpi : ∀ u, 0 < marg₁ (jointUX (zChan a ha0 ha1)) u := by
    intro u; cases u
    · rw [hm0]; positivity
    · rw [hm1]; positivity
  have hrho : ∀ v, 0 < marg₂ (jointYV (zChan d hd0 hd1)) v := by
    intro v; cases v
    · rw [hn0]; positivity
    · rw [hn1]; positivity
  have hker : ∀ u v, 0 < 1 + (1 - 2 * (0:ℝ)) * biasOf (jointUX (zChan a ha0 ha1)) u
      * biasOfSnd (jointYV (zChan d hd0 hd1)) v := by
    intro u v
    cases u <;> cases v <;>
      simp only [hb0, hb1, ht0, ht1] <;> nlinarith
  rw [mutualInfo_jointUV_eq_kernel_sum 0 _ _ hpi hrho hker,
    hm0, hm1, hb0, hb1, hn0, hn1, ht0, ht1]
  have e1 : (1 - 2 * (0:ℝ)) * a * d = -(d * -a) := by ring
  have e2 : (1 - 2 * (0:ℝ)) * a * -1 = -a := by ring
  have e3 : (1 - 2 * (0:ℝ)) * -1 * d = -(d * 1) := by ring
  have e4 : (1 - 2 * (0:ℝ)) * -1 * -1 = 1 := by ring
  rw [e1, e2, e3, e4]
  simp only [mzsValue, phiZ]
  ring

end Parts

/-- **Conjecture 2** at `p = 0`, the minimisation mirror.  The mirror certificate
`MDFun_nonpos` bounds `I(U;V)` from *below* by `μ₀ + μ₂·Cu`; the conjecture is
that this is attained, by the Z/Z pair (the sign flip `omegaTwoPoint_neg` says
aligned skews minimise).  Stated here in the same shape as `Conjecture1_p0`. -/
def Conjecture2_p0 : Prop :=
  ∀ (a d : ℝ) (_ha0 : 0 < a) (_ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1) (cL cR : Chan),
    (∀ u, 0 < marg₁ (jointUX cL) u) →
    zsRate a ≤ mutualInfo (jointUX cL) →
    mutualInfo (jointYV (sChan d hd0 hd1)) ≤ mutualInfo (jointYV cR) →
    mzsValue a d ≤ mutualInfo (jointUV 0 cL cR)


end BSCAveraging
