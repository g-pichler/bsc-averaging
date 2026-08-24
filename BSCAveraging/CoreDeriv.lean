import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import BSCAveraging.Interval
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The derivative of (iii)'s one-variable core

`NOTES.md` §7f⁸: the naive interval extension of

```
F(θ) = 1/log Z − 1/(Z−1) − tanh θ/(2θ),      Z = cosh 2θ
```

cannot certify positivity at the hard end, because `F` is a difference of large
nearly-equal terms and interval arithmetic cannot see the cancellation.  The
cure is the mean-value form `F(θ) ∈ F(c) ± L·(b−a)/2` with `L` a bound on `|F′|`
over the cell — and `F′` is *small and non-cancelling*, so a naive enclosure of
it is perfectly adequate.

This file supplies the derivative.  `tanh` is written as `sinh/cosh` so that
only `Real.hasDerivAt_sinh`, `Real.hasDerivAt_cosh` and the quotient rule are
needed. -/

namespace BSCAveraging.Core

open Real

/-- The core function of (iii), with `tanh` spelled out and reciprocals written
as `⁻¹` so that the derivative rules apply without reshaping. -/
noncomputable def F (t : ℝ) : ℝ :=
  (Real.log (Real.cosh (2 * t)))⁻¹ - (Real.cosh (2 * t) - 1)⁻¹
    - Real.sinh t / (Real.cosh t * (2 * t))

/-- Its derivative, in exactly the shape the composition rules produce. -/
noncomputable def F' (t : ℝ) : ℝ :=
  -(2 * Real.sinh (2 * t) / Real.cosh (2 * t)) / Real.log (Real.cosh (2 * t)) ^ 2
    - -(2 * Real.sinh (2 * t)) / (Real.cosh (2 * t) - 1) ^ 2
    - (Real.cosh t * (Real.cosh t * (2 * t))
        - Real.sinh t * (Real.sinh t * (2 * t) + Real.cosh t * 2))
      / (Real.cosh t * (2 * t)) ^ 2

/-- `cosh 2t > 1` for `t > 0`. -/
theorem one_lt_cosh {t : ℝ} (ht : 0 < t) : 1 < Real.cosh (2 * t) := by
  have h : (0:ℝ) < 2 * t := by linarith
  exact Real.one_lt_cosh.mpr (ne_of_gt h)

theorem log_cosh_pos {t : ℝ} (ht : 0 < t) : 0 < Real.log (Real.cosh (2 * t)) :=
  Real.log_pos (one_lt_cosh ht)

/-- **The derivative of the core.** -/
theorem hasDerivAt_F {t : ℝ} (ht : 0 < t) : HasDerivAt F (F' t) t := by
  have hZ1 : 1 < Real.cosh (2 * t) := one_lt_cosh ht
  have hZpos : (0:ℝ) < Real.cosh (2 * t) := lt_trans one_pos hZ1
  have hZne : Real.cosh (2 * t) ≠ 0 := ne_of_gt hZpos
  have hZm1 : Real.cosh (2 * t) - 1 ≠ 0 := by
    have : (0:ℝ) < Real.cosh (2 * t) - 1 := by linarith
    exact ne_of_gt this
  have hlog : Real.log (Real.cosh (2 * t)) ≠ 0 := ne_of_gt (log_cosh_pos ht)
  have hct : (0:ℝ) < Real.cosh t := Real.cosh_pos t
  have hden : Real.cosh t * (2 * t) ≠ 0 := by positivity
  have h2t : HasDerivAt (fun x : ℝ => 2 * x) 2 t := by
    simpa using (hasDerivAt_id t).const_mul (2:ℝ)
  have hcosh2 : HasDerivAt (fun x : ℝ => Real.cosh (2 * x))
      (Real.sinh (2 * t) * 2) t := h2t.cosh
  have hcosh2' : HasDerivAt (fun x : ℝ => Real.cosh (2 * x))
      (2 * Real.sinh (2 * t)) t := by
    have e : Real.sinh (2 * t) * 2 = 2 * Real.sinh (2 * t) := by ring
    rwa [e] at hcosh2
  have hlogc : HasDerivAt (fun x : ℝ => Real.log (Real.cosh (2 * x)))
      (2 * Real.sinh (2 * t) / Real.cosh (2 * t)) t := hcosh2'.log hZne
  have h1 : HasDerivAt (fun x : ℝ => (Real.log (Real.cosh (2 * x)))⁻¹)
      (-(2 * Real.sinh (2 * t) / Real.cosh (2 * t))
        / Real.log (Real.cosh (2 * t)) ^ 2) t := hlogc.inv hlog
  have hsub : HasDerivAt (fun x : ℝ => Real.cosh (2 * x) - 1)
      (2 * Real.sinh (2 * t)) t := hcosh2'.sub_const 1
  have h2 : HasDerivAt (fun x : ℝ => (Real.cosh (2 * x) - 1)⁻¹)
      (-(2 * Real.sinh (2 * t)) / (Real.cosh (2 * t) - 1) ^ 2) t := hsub.inv hZm1
  have hnum : HasDerivAt Real.sinh (Real.cosh t) t := Real.hasDerivAt_sinh t
  have hd : HasDerivAt (fun x : ℝ => Real.cosh x * (2 * x))
      (Real.sinh t * (2 * t) + Real.cosh t * 2) t := (Real.hasDerivAt_cosh t).mul h2t
  have h3 : HasDerivAt (fun x : ℝ => Real.sinh x / (Real.cosh x * (2 * x)))
      ((Real.cosh t * (Real.cosh t * (2 * t))
          - Real.sinh t * (Real.sinh t * (2 * t) + Real.cosh t * 2))
        / (Real.cosh t * (2 * t)) ^ 2) t := hnum.div hd hden
  exact (h1.sub h2).sub h3

/-- `F` is the core of (iii), in the `tanh` form the sweep uses. -/
theorem F_eq {t : ℝ} (ht : 0 < t) :
    F t = 1 / Real.log (Real.cosh (2 * t)) - 1 / (Real.cosh (2 * t) - 1)
      - Real.tanh t / (2 * t) := by
  have hct : (0:ℝ) < Real.cosh t := Real.cosh_pos t
  have h2t : (2:ℝ) * t ≠ 0 := by positivity
  simp only [F, Real.tanh_eq_sinh_div_cosh, one_div]
  field_simp

/-- **The mean-value step.**  On a cell where `|F′| ≤ L`, the value at any point
is within `L·(b−a)` of the value at any other, so a single point evaluation with
enough margin certifies positivity on the whole cell.  This is what the naive
interval extension could not do: it loses the cancellation that makes `F`
slowly varying, while `F′` is genuinely small. -/
theorem F_pos_of_center {a b c L : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : c ∈ Set.Icc a b) (hL : ∀ x ∈ Set.Icc a b, |F' x| ≤ L)
    (hmargin : L * (b - a) < F c) :
    ∀ θ ∈ Set.Icc a b, 0 < F θ := by
  intro θ hθ
  have hderiv : ∀ x ∈ Set.Icc a b, HasDerivWithinAt F (F' x) (Set.Icc a b) x := by
    intro x hx
    exact (hasDerivAt_F (lt_of_lt_of_le ha hx.1)).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Icc a b, ‖F' x‖ ≤ L := by
    intro x hx
    simpa [Real.norm_eq_abs] using hL x hx
  have key := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound hc hθ
  have hdist : ‖θ - c‖ ≤ b - a := by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [hθ.1, hc.2]
    · linarith [hθ.2, hc.1]
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hL c hc)
  have h1 : ‖F θ - F c‖ ≤ L * (b - a) :=
    le_trans key (mul_le_mul_of_nonneg_left hdist hL0)
  have h2 : F c - F θ ≤ L * (b - a) := by
    have := abs_le.mp (by simpa [Real.norm_eq_abs] using h1)
    linarith [this.1]
  linarith

/-! ## Interval extension of `F′`

`F′` does not suffer the cancellation that defeats the naive extension of `F`:
its terms are `O(1)` and their combination is `O(10⁻²)`, so a straightforward
enclosure is adequate.  Everything is built from the pieces of `Interval.lean`;
the `log` enclosure again rides in as the pair of witnesses. -/

open BSCAveraging.Iv

/-- Interval extension of `F′` on a cell, given witnesses `lp ≤ log Z ≤ lq`. -/
def FpI (Ith : Iv) (lp lq : ℚ) (k n m : ℕ) : Iv :=
  let I2 := scale 2 Ith
  let Z := coshI I2 k n m
  let S2 := sinhI I2 k n m
  let L : Iv := ⟨lp, lq⟩
  let C := coshI Ith k n m
  let S := sinhI Ith k n m
  let t1 := outward m (div (neg (outward m (div (scale 2 S2) Z))) (outward m (mul L L)))
  let t2 := outward m (div (neg (scale 2 S2))
    (outward m (mul (outward m (sub Z (const 1))) (outward m (sub Z (const 1))))))
  let den := outward m (mul C I2)
  let num := outward m (sub (outward m (mul C den))
    (outward m (mul S (outward m (add (outward m (mul S I2)) (scale 2 C))))))
  let t3 := outward m (div num (outward m (mul den den)))
  outward m (sub (outward m (sub t1 t2)) t3)

theorem mem_FpI {Ith : Iv} {θ : ℝ} {lp lq : ℚ} {k n m : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hx : mem Ith θ) (hlog : mem ⟨lp, lq⟩ (Real.log (Real.cosh (2 * θ))))
    (hZne : 0 < (coshI (scale 2 Ith) k n m).lo)
    (hLsq : 0 < (outward m (mul ⟨lp, lq⟩ ⟨lp, lq⟩)).lo)
    (hZ1sq : 0 < (outward m (mul (outward m (sub (coshI (scale 2 Ith) k n m) (const 1)))
      (outward m (sub (coshI (scale 2 Ith) k n m) (const 1))))).lo)
    (hdensq : 0 < (outward m (mul (outward m (mul (coshI Ith k n m) (scale 2 Ith)))
      (outward m (mul (coshI Ith k n m) (scale 2 Ith))))).lo)
    (hcosh : 0 < (coshI Ith k n m).lo)
    (e1 : |(scale 2 Ith).lo / 2 ^ k| ≤ 1) (e2 : |(scale 2 Ith).hi / 2 ^ k| ≤ 1)
    (e3 : |(neg (scale 2 Ith)).lo / 2 ^ k| ≤ 1)
    (e4 : |(neg (scale 2 Ith)).hi / 2 ^ k| ≤ 1)
    (f1 : |Ith.lo / 2 ^ k| ≤ 1) (f2 : |Ith.hi / 2 ^ k| ≤ 1)
    (f3 : |(neg Ith).lo / 2 ^ k| ≤ 1) (f4 : |(neg Ith).hi / 2 ^ k| ≤ 1) :
    mem (FpI Ith lp lq k n m) (F' θ) := by
  have h2 : mem (scale 2 Ith) (2 * θ) := by
    have := mem_scale (2 : ℚ) hx
    simpa using this
  have hZ := mem_coshI hm e1 e2 e3 e4 hn h2
  have hS2 := mem_sinhI hm e1 e2 e3 e4 hn h2
  have hC := mem_coshI hm f1 f2 f3 f4 hn hx
  have hS := mem_sinhI hm f1 f2 f3 f4 hn hx
  have hone : mem (const 1) (1 : ℝ) := by
    have := mem_const (1 : ℚ)
    simpa using this
  -- first term
  have hq1 : mem (outward m (div (scale 2 (sinhI (scale 2 Ith) k n m))
      (coshI (scale 2 Ith) k n m)))
      (2 * Real.sinh (2 * θ) / Real.cosh (2 * θ)) := by
    have hnum : mem (scale 2 (sinhI (scale 2 Ith) k n m)) (2 * Real.sinh (2 * θ)) := by
      have := mem_scale (2 : ℚ) hS2
      simpa using this
    exact mem_outward hm (mem_div hZne hnum hZ)
  have ht1 := mem_outward hm (mem_div hLsq (mem_neg hq1) (mem_outward hm (mem_mul hlog hlog)))
  -- second term
  have hZm1 := mem_outward hm (mem_sub hZ hone)
  have hnum2 : mem (neg (scale 2 (sinhI (scale 2 Ith) k n m))) (-(2 * Real.sinh (2 * θ))) := by
    have : mem (scale 2 (sinhI (scale 2 Ith) k n m)) (2 * Real.sinh (2 * θ)) := by
      have := mem_scale (2 : ℚ) hS2
      simpa using this
    exact mem_neg this
  have ht2 := mem_outward hm (mem_div hZ1sq hnum2 (mem_outward hm (mem_mul hZm1 hZm1)))
  -- third term
  have hden := mem_outward hm (mem_mul hC h2)
  have hinner : mem (outward m (add (outward m (mul (sinhI Ith k n m) (scale 2 Ith)))
      (scale 2 (coshI Ith k n m))))
      (Real.sinh θ * (2 * θ) + Real.cosh θ * 2) := by
    have hA := mem_outward hm (mem_mul hS h2)
    have hB : mem (scale 2 (coshI Ith k n m)) (Real.cosh θ * 2) := by
      have := mem_scale (2 : ℚ) hC
      have e : ((2:ℚ) : ℝ) * Real.cosh θ = Real.cosh θ * 2 := by push_cast; ring
      rwa [e] at this
    exact mem_outward hm (mem_add hA hB)
  have hnum3 := mem_outward hm (mem_sub (mem_outward hm (mem_mul hC hden))
    (mem_outward hm (mem_mul hS hinner)))
  have ht3 := mem_outward hm (mem_div hdensq hnum3 (mem_outward hm (mem_mul hden hden)))
  have e : F' θ = -(2 * Real.sinh (2 * θ) / Real.cosh (2 * θ))
        / (Real.log (Real.cosh (2 * θ)) * Real.log (Real.cosh (2 * θ)))
      - -(2 * Real.sinh (2 * θ)) / ((Real.cosh (2 * θ) - 1) * (Real.cosh (2 * θ) - 1))
      - (Real.cosh θ * (Real.cosh θ * (2 * θ))
          - Real.sinh θ * (Real.sinh θ * (2 * θ) + Real.cosh θ * 2))
        / ((Real.cosh θ * (2 * θ)) * (Real.cosh θ * (2 * θ))) := by
    simp only [F']
    ring
  rw [e]
  exact mem_outward hm (mem_sub (mem_outward hm (mem_sub ht1 ht2)) ht3)

/-- The absolute bound read off an enclosure. -/
def absBound (I : Iv) : ℚ := max |I.lo| |I.hi|

theorem abs_le_absBound {I : Iv} {x : ℝ} (h : mem I x) : |x| ≤ (absBound I : ℝ) := by
  obtain ⟨h1, h2⟩ := h
  rw [abs_le]
  constructor
  · have : -(|I.lo| : ℝ) ≤ (I.lo : ℝ) := neg_abs_le _
    have hle : (-(absBound I : ℝ)) ≤ (I.lo : ℝ) := by
      refine le_trans ?_ this
      simp only [absBound, Rat.cast_max, Rat.cast_abs]
      exact neg_le_neg (le_max_left _ _)
    linarith
  · have : (I.hi : ℝ) ≤ |(I.hi : ℝ)| := le_abs_self _
    have hle : (I.hi : ℝ) ≤ (absBound I : ℝ) := by
      refine le_trans this ?_
      simp only [absBound, Rat.cast_max, Rat.cast_abs]
      exact le_max_right _ _
    linarith

/-! ## The centred cell test

Two helpers: `fpOk` certifies a Lipschitz bound for `F′` over the cell, `fOk`
certifies a point enclosure of `F`.  `cellOkC` combines them with the margin
check, and `pos_of_cellOkC` is `F_pos_of_center` fed by the two. -/

/-- Side conditions making `FpI` a valid enclosure of `F′` on `I`. -/
def fpOk (I : Iv) (lp lq : ℚ) (k n m : ℕ) : Bool :=
  let I2 := scale 2 I
  let Z := coshI I2 k n m
  let Zm1 := outward m (sub Z (const 1))
  let den := outward m (mul (coshI I k n m) I2)
  decide (|lp / 2 ^ k| ≤ 1) && (decide (|lq / 2 ^ k| ≤ 1) &&
  (decide ((expIv lp k n m).hi ≤ Z.lo) && (decide (Z.hi ≤ (expIv lq k n m).lo) &&
  (decide (0 < Z.lo) && (decide (0 < (outward m (mul ⟨lp, lq⟩ ⟨lp, lq⟩)).lo) &&
  (decide (0 < (outward m (mul Zm1 Zm1)).lo) &&
  (decide (0 < (outward m (mul den den)).lo) &&
  (decide (0 < (coshI I k n m).lo) &&
  (decide (|I2.lo / 2 ^ k| ≤ 1) && (decide (|I2.hi / 2 ^ k| ≤ 1) &&
  (decide (|(neg I2).lo / 2 ^ k| ≤ 1) && (decide (|(neg I2).hi / 2 ^ k| ≤ 1) &&
  (decide (|I.lo / 2 ^ k| ≤ 1) && (decide (|I.hi / 2 ^ k| ≤ 1) &&
  (decide (|(neg I).lo / 2 ^ k| ≤ 1) && decide (|(neg I).hi / 2 ^ k| ≤ 1))))))))))))))))

theorem fp_sound {I : Iv} {lp lq : ℚ} {k n m : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hok : fpOk I lp lq k n m = true) {x : ℝ} (hx : mem I x) :
    |F' x| ≤ (absBound (FpI I lp lq k n m) : ℝ) := by
  simp only [fpOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hp, hq, hw1, hw2, hZpos, hLsq, hZ1sq, hdensq, hcosh, e1, e2, e3, e4,
    f1, f2, f3, f4⟩ := hok
  have h2 : mem (scale 2 I) (2 * x) := by
    have := mem_scale (2 : ℚ) hx
    simpa using this
  have hZ := mem_coshI hm e1 e2 e3 e4 hn h2
  have hZr : (0:ℝ) < Real.cosh (2 * x) := Real.cosh_pos _
  have hle1 : (((expIv lp k n m).hi : ℚ) : ℝ) ≤ Real.cosh (2 * x) :=
    le_trans (by exact_mod_cast hw1) hZ.1
  have hle2 : Real.cosh (2 * x) ≤ (((expIv lq k n m).lo : ℚ) : ℝ) :=
    le_trans hZ.2 (by exact_mod_cast hw2)
  have hlog := mem_logIv hm hp hq hn hZr hle1 hle2
  exact abs_le_absBound
    (mem_FpI hm hn hx hlog hZpos hLsq hZ1sq hdensq hcosh e1 e2 e3 e4 f1 f2 f3 f4)

/-- Side conditions making `FI2` a valid enclosure of `F` on `I`. -/
def fOk (I : Iv) (p q : ℚ) (k n m : ℕ) : Bool :=
  let I2 := scale 2 I
  let Z := coshI I2 k n m
  let Zm1 := outward m (sub Z (const 1))
  decide (0 < I.lo) && (decide (|p / 2 ^ k| ≤ 1) && (decide (|q / 2 ^ k| ≤ 1) &&
  (decide (0 < p) && (decide ((expIv p k n m).hi ≤ Z.lo) &&
  (decide (Z.hi ≤ (expIv q k n m).lo) && (decide (0 < Zm1.lo) &&
  (decide (0 < (outward m (mul ⟨p, q⟩ Zm1)).lo) &&
  (decide (0 < I2.lo) && (decide (0 < (coshI I k n m).lo) &&
  (decide (|I2.lo / 2 ^ k| ≤ 1) && (decide (|I2.hi / 2 ^ k| ≤ 1) &&
  (decide (|(neg I2).lo / 2 ^ k| ≤ 1) && (decide (|(neg I2).hi / 2 ^ k| ≤ 1) &&
  (decide (|I.lo / 2 ^ k| ≤ 1) && (decide (|I.hi / 2 ^ k| ≤ 1) &&
  (decide (|(neg I).lo / 2 ^ k| ≤ 1) && decide (|(neg I).hi / 2 ^ k| ≤ 1)))))))))))))))))

theorem f_sound {I : Iv} {p q : ℚ} {k n m : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hok : fOk I p q k n m = true) {x : ℝ} (hx : mem I x) :
    mem (FI2 I p q k n m) (F x) := by
  simp only [fOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hIlo, hp, hq, hppos, hw1, hw2, hZ1, hprod, h2θ, hcosh, e1, e2, e3, e4,
    f1, f2, f3, f4⟩ := hok
  have hxpos : (0:ℝ) < x := by
    have : (0:ℝ) < (I.lo : ℝ) := by exact_mod_cast hIlo
    linarith [hx.1]
  have h2 : mem (scale 2 I) (2 * x) := by
    have := mem_scale (2 : ℚ) hx
    simpa using this
  have hZ := mem_coshI hm e1 e2 e3 e4 hn h2
  have hZr : (0:ℝ) < Real.cosh (2 * x) := Real.cosh_pos _
  have hle1 : (((expIv p k n m).hi : ℚ) : ℝ) ≤ Real.cosh (2 * x) :=
    le_trans (by exact_mod_cast hw1) hZ.1
  have hle2 : Real.cosh (2 * x) ≤ (((expIv q k n m).lo : ℚ) : ℝ) :=
    le_trans hZ.2 (by exact_mod_cast hw2)
  have hlog := mem_logIv hm hp hq hn hZr hle1 hle2
  have := mem_FI2 hm hx hlog hppos hZ1 hprod h2θ hcosh e1 e2 e3 e4 f1 f2 f3 f4 hn
  rwa [← F_eq hxpos] at this

/-- A cell for the centred sweep: its range, the cell-wide `log` witnesses (for
`F′`), and the centre's witnesses (for the point evaluation). -/
structure CellC where
  lo : ℚ
  hi : ℚ
  lp : ℚ
  lq : ℚ
  cp : ℚ
  cq : ℚ
deriving Repr, Inhabited

/-- Midpoint of a cell. -/
def CellC.mid (c : CellC) : ℚ := (c.lo + c.hi) / 2

/-- **The centred cell test.** -/
def cellOkC (c : CellC) (k n m : ℕ) : Bool :=
  decide (0 < c.lo) && (decide (c.lo ≤ c.hi) &&
  (fpOk ⟨c.lo, c.hi⟩ c.lp c.lq k n m &&
  (fOk ⟨c.mid, c.mid⟩ c.cp c.cq k n m &&
  decide (absBound (FpI ⟨c.lo, c.hi⟩ c.lp c.lq k n m) * (c.hi - c.lo)
    < (FI2 ⟨c.mid, c.mid⟩ c.cp c.cq k n m).lo))))

/-- **`F > 0` on a cell that passes the centred test.** -/
theorem pos_of_cellOkC {c : CellC} {k n m : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hok : cellOkC c k n m = true) :
    ∀ θ ∈ Set.Icc (c.lo : ℝ) (c.hi : ℝ), 0 < F θ := by
  simp only [cellOkC, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hlo, hab, hfp, hf, hmargin⟩ := hok
  have hlopos : (0:ℝ) < (c.lo : ℝ) := by exact_mod_cast hlo
  have habr : (c.lo : ℝ) ≤ (c.hi : ℝ) := by exact_mod_cast hab
  have hmidlo : (c.lo : ℝ) ≤ (c.mid : ℝ) := by
    have : c.lo ≤ c.mid := by simp only [CellC.mid]; linarith
    exact_mod_cast this
  have hmidhi : (c.mid : ℝ) ≤ (c.hi : ℝ) := by
    have : c.mid ≤ c.hi := by simp only [CellC.mid]; linarith
    exact_mod_cast this
  refine F_pos_of_center (L := ((absBound (FpI ⟨c.lo, c.hi⟩ c.lp c.lq k n m) : ℚ) : ℝ))
    hlopos habr ⟨hmidlo, hmidhi⟩ ?_ ?_
  · intro x hx
    exact fp_sound hm hn hfp ⟨hx.1, hx.2⟩
  · have hFmid : mem (FI2 ⟨c.mid, c.mid⟩ c.cp c.cq k n m) (F (c.mid : ℝ)) :=
      f_sound hm hn hf ⟨le_rfl, le_rfl⟩
    have hcast : ((absBound (FpI ⟨c.lo, c.hi⟩ c.lp c.lq k n m) : ℚ) : ℝ)
        * ((c.hi : ℝ) - (c.lo : ℝ))
        < (((FI2 ⟨c.mid, c.mid⟩ c.cp c.cq k n m).lo : ℚ) : ℝ) := by
      have := (Rat.cast_lt (K := ℝ)).mpr hmargin
      push_cast at this ⊢
      linarith
    linarith [hFmid.1]

/-- The centred cells tile `[A,B]` from left to right. -/
def tilesC (B : ℚ) : ℚ → List CellC → Bool
  | _, [] => false
  | A, [c] => decide (c.lo ≤ A) && decide (B ≤ c.hi)
  | A, c :: cs => decide (c.lo ≤ A) && tilesC B c.hi cs

/-- **The centred sweep is sound**: cells that tile `[A,B]` and pass the centred
test give `F > 0` on `[A,B]`. -/
theorem sweepC_sound {k n m : ℕ} (hm : 0 < m) (hn : 0 < n) {B : ℚ} :
    ∀ (cs : List CellC) (A : ℚ), tilesC B A cs = true →
      (∀ c ∈ cs, cellOkC c k n m = true) →
      ∀ θ : ℝ, (A : ℝ) ≤ θ → θ ≤ (B : ℝ) → 0 < F θ
  | [], A, ht, _, _, _, _ => by simp [tilesC] at ht
  | [c], A, ht, hall, θ, hA, hB => by
    simp only [tilesC, Bool.and_eq_true, decide_eq_true_eq] at ht
    refine pos_of_cellOkC hm hn (hall c (by simp)) θ ⟨?_, ?_⟩
    · exact le_trans (by exact_mod_cast ht.1) hA
    · exact le_trans hB (by exact_mod_cast ht.2)
  | c :: d :: cs, A, ht, hall, θ, hA, hB => by
    simp only [tilesC, Bool.and_eq_true, decide_eq_true_eq] at ht
    by_cases hcase : θ ≤ (c.hi : ℝ)
    · refine pos_of_cellOkC hm hn (hall c (by simp)) θ ⟨?_, hcase⟩
      exact le_trans (by exact_mod_cast ht.1) hA
    · push_neg at hcase
      exact sweepC_sound hm hn (d :: cs) c.hi ht.2
        (fun x hx => hall x (by simp [hx])) θ (le_of_lt hcase) hB

/-! ## Regime 3: `θ ≥ 3`

Elementary.  `log cosh 2θ = 2θ − log 2 + log(1+e^{−4θ})`, so `1/log Z` beats
`1/(2θ)` by about `log 2/(4θ²)`, while `1/(Z−1)` is exponentially small. -/

/-- `cosh u = e^u (1 + e^{−2u})/2`. -/
theorem cosh_eq_exp_mul (u : ℝ) :
    Real.cosh u = Real.exp u * (1 + Real.exp (-(2 * u))) / 2 := by
  have h : Real.exp u * (1 + Real.exp (-(2 * u))) = Real.exp u + Real.exp (-u) := by
    rw [mul_add, mul_one, ← Real.exp_add]
    ring_nf
  rw [Real.cosh_eq, h]

/-- `log cosh u = u − log 2 + log(1 + e^{−2u})`. -/
theorem log_cosh_eq (u : ℝ) :
    Real.log (Real.cosh u) = u - Real.log 2 + Real.log (1 + Real.exp (-(2 * u))) := by
  rw [cosh_eq_exp_mul u]
  have h1 : (0:ℝ) < Real.exp u := Real.exp_pos u
  have h2 : (0:ℝ) < 1 + Real.exp (-(2 * u)) := by positivity
  rw [Real.log_div (by positivity) (by norm_num),
    Real.log_mul (ne_of_gt h1) (ne_of_gt h2), Real.log_exp]
  ring

/-- `e⁶ > 250`, via `e^{1/8} ≥ 9/8` raised to the 48th power. -/
theorem exp_six_gt : (250:ℝ) < Real.exp 6 := by
  have h1 : (9:ℝ)/8 ≤ Real.exp (1/8) := by
    have := Real.add_one_le_exp ((1:ℝ)/8); linarith
  have h2 : ((9:ℝ)/8) ^ (48:ℕ) ≤ (Real.exp (1/8)) ^ (48:ℕ) :=
    pow_le_pow_left₀ (by norm_num) h1 48
  have h3 : (Real.exp (1/8)) ^ (48:ℕ) = Real.exp 6 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h4 : (250:ℝ) < ((9:ℝ)/8) ^ (48:ℕ) := by norm_num
  linarith [h3 ▸ h2]

theorem exp_neg_six_lt : Real.exp (-6) < 1/250 := by
  have h := exp_six_gt
  have hp : (0:ℝ) < Real.exp 6 := Real.exp_pos 6
  rw [Real.exp_neg, inv_lt_comm₀ hp (by norm_num)]
  linarith

/-- `θ² ≤ 9e^{θ−3}` for `θ ≥ 3`, from `e^{s/2} ≥ 1 + s/2`. -/
theorem sq_le_exp {θ : ℝ} (hθ : 3 ≤ θ) : θ ^ 2 ≤ 9 * Real.exp (θ - 3) := by
  have hs : (0:ℝ) ≤ θ - 3 := by linarith
  have h1 : 1 + (θ - 3)/2 ≤ Real.exp ((θ - 3)/2) := by
    have := Real.add_one_le_exp ((θ - 3)/2); linarith
  have h2 : Real.exp (θ - 3) = Real.exp ((θ - 3)/2) * Real.exp ((θ - 3)/2) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : (0:ℝ) ≤ 1 + (θ - 3)/2 := by linarith
  nlinarith [Real.exp_pos ((θ - 3)/2)]

/-- `16 θ² e^{−2θ} < 0.69` for `θ ≥ 3`. -/
theorem exp_dominates {θ : ℝ} (hθ : 3 ≤ θ) :
    16 * θ ^ 2 * Real.exp (-(2 * θ)) < 0.69 := by
  have hE : (0:ℝ) < Real.exp (θ - 3) := Real.exp_pos _
  have hE1 : (1:ℝ) ≤ Real.exp (θ - 3) := Real.one_le_exp (by linarith)
  have he : Real.exp (-(2 * θ)) = Real.exp (-6) / (Real.exp (θ - 3) * Real.exp (θ - 3)) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  have hq := sq_le_exp hθ
  have h6 := exp_neg_six_lt
  have h6p : (0:ℝ) < Real.exp (-6) := Real.exp_pos _
  rw [he]
  have hstep : 16 * θ ^ 2 * (Real.exp (-6) / (Real.exp (θ - 3) * Real.exp (θ - 3)))
      ≤ 16 * (9 * Real.exp (θ - 3)) * (Real.exp (-6)
        / (Real.exp (θ - 3) * Real.exp (θ - 3))) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith
  have hval : 16 * (9 * Real.exp (θ - 3)) * (Real.exp (-6)
      / (Real.exp (θ - 3) * Real.exp (θ - 3))) = 144 * Real.exp (-6) / Real.exp (θ - 3) := by
    field_simp
    ring
  have hle : 144 * Real.exp (-6) / Real.exp (θ - 3) ≤ 144 * Real.exp (-6) := by
    rw [div_le_iff₀ hE]
    nlinarith
  have : 144 * Real.exp (-6) < 0.69 := by
    have := exp_neg_six_lt; nlinarith
  linarith [hstep, hval ▸ hstep]

/-- `1/(cosh 2θ − 1) ≤ 4e^{−2θ}` for `θ ≥ 3`. -/
theorem inv_cosh_sub_one_le {θ : ℝ} (hθ : 3 ≤ θ) :
    1 / (Real.cosh (2 * θ) - 1) ≤ 4 * Real.exp (-(2 * θ)) := by
  have hep : (0:ℝ) < Real.exp (2 * θ) := Real.exp_pos _
  have h400 : (250:ℝ) < Real.exp (2 * θ) := by
    have : Real.exp (6:ℝ) ≤ Real.exp (2 * θ) := Real.exp_le_exp.mpr (by linarith)
    linarith [exp_six_gt]
  have hlow : Real.exp (2 * θ) / 4 ≤ Real.cosh (2 * θ) - 1 := by
    rw [cosh_eq_exp_mul (2 * θ)]
    have hq : (0:ℝ) < Real.exp (-(2 * (2 * θ))) := Real.exp_pos _
    nlinarith
  have hpos : (0:ℝ) < Real.cosh (2 * θ) - 1 := by
    have : (0:ℝ) < Real.exp (2 * θ) / 4 := by positivity
    linarith
  have hinv : 1 / (Real.cosh (2 * θ) - 1) ≤ 1 / (Real.exp (2 * θ) / 4) :=
    one_div_le_one_div_of_le (by positivity) hlow
  have heq : 1 / (Real.exp (2 * θ) / 4) = 4 * Real.exp (-(2 * θ)) := by
    rw [Real.exp_neg]
    field_simp
  linarith [heq ▸ hinv]

/-- **Regime 3 of (iii)'s core.** -/
theorem core_pos_regime3 {θ : ℝ} (hθ : 3 ≤ θ) : 0 < F θ := by
  have hθ0 : (0:ℝ) < θ := by linarith
  have h2θ : (0:ℝ) < 2 * θ := by linarith
  have hZ1 : 1 < Real.cosh (2 * θ) := one_lt_cosh hθ0
  have hLpos : 0 < Real.log (Real.cosh (2 * θ)) := log_cosh_pos hθ0
  have hl2lo : (0.6931:ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2hi : Real.log 2 < 0.6932 := by have := Real.log_two_lt_d9; linarith
  have hq : Real.exp (-(2 * (2 * θ))) ≤ Real.exp (-12) :=
    Real.exp_le_exp.mpr (by linarith)
  have h12 : Real.exp (-12) < 1/1000 := by
    have h6 := exp_neg_six_lt
    have h : Real.exp (-12) = Real.exp (-6) * Real.exp (-6) := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-6:ℝ)]
  have hsmallq : Real.exp (-(2 * (2 * θ))) < 1/1000 := lt_of_le_of_lt hq h12
  -- upper bound on log Z
  have hlogub : Real.log (Real.cosh (2 * θ))
      ≤ 2 * θ - Real.log 2 + Real.exp (-(2 * (2 * θ))) := by
    rw [log_cosh_eq (2 * θ)]
    have := Real.log_le_sub_one_of_pos
      (show (0:ℝ) < 1 + Real.exp (-(2 * (2 * θ))) by positivity)
    linarith
  have hD : (0:ℝ) < 2 * θ - Real.log 2 + Real.exp (-(2 * (2 * θ))) := by
    have := Real.exp_pos (-(2 * (2 * θ))); linarith
  have hDne : (2 * θ - Real.log 2 + Real.exp (-(2 * (2 * θ)))) ≠ 0 := ne_of_gt hD
  have h2θne : (2 * θ : ℝ) ≠ 0 := ne_of_gt h2θ
  -- the gap
  have hgap : (Real.log 2 - Real.exp (-(2 * (2 * θ)))) / ((2 * θ) * (2 * θ))
      ≤ 1 / Real.log (Real.cosh (2 * θ)) - 1 / (2 * θ) := by
    have h1 : 1 / (2 * θ - Real.log 2 + Real.exp (-(2 * (2 * θ))))
        ≤ 1 / Real.log (Real.cosh (2 * θ)) := one_div_le_one_div_of_le hLpos hlogub
    have h2 : 1 / (2 * θ - Real.log 2 + Real.exp (-(2 * (2 * θ)))) - 1 / (2 * θ)
        = (Real.log 2 - Real.exp (-(2 * (2 * θ))))
          / ((2 * θ - Real.log 2 + Real.exp (-(2 * (2 * θ)))) * (2 * θ)) := by
      rw [div_sub_div _ _ hDne h2θne]
      congr 1
      ring
    have h3 : (Real.log 2 - Real.exp (-(2 * (2 * θ))))
          / ((2 * θ) * (2 * θ))
        ≤ (Real.log 2 - Real.exp (-(2 * (2 * θ))))
          / ((2 * θ - Real.log 2 + Real.exp (-(2 * (2 * θ)))) * (2 * θ)) := by
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      nlinarith [Real.exp_pos (-(2 * (2 * θ)))]
    linarith
  -- the exponential remainder loses
  have hrem : 4 * Real.exp (-(2 * θ))
      < (Real.log 2 - Real.exp (-(2 * (2 * θ)))) / ((2 * θ) * (2 * θ)) := by
    rw [lt_div_iff₀ (by positivity)]
    have hdom := exp_dominates hθ
    have he : 4 * Real.exp (-(2 * θ)) * ((2 * θ) * (2 * θ))
        = 16 * θ ^ 2 * Real.exp (-(2 * θ)) := by ring
    rw [he]
    linarith
  have htan : Real.tanh θ / (2 * θ) ≤ 1 / (2 * θ) := by
    gcongr
    exact le_of_lt (Real.tanh_lt_one θ)
  have hZm1 := inv_cosh_sub_one_le hθ
  rw [F_eq hθ0]
  linarith

/-! ## Regime 1: the log-free reduction

Clearing denominators, `F = N / (log Z · (Z−1) · 2θ)` with

```
N(θ) = 2θ(Z−1) − log Z · W ,        W = 2θ + tanh θ · (Z−1),
```

all three factors of the denominator positive, so `F > 0 ⟺ N > 0`.  Writing
`y = 2θ(Z−1)/W` gives `N = W·(y − log Z)`, hence

```
N > 0  ⟺  log Z < y  ⟺  Z < exp y ,
```

and `exp y` dominates each of its partial sums.  So regime 1 reduces to the
**log-free** inequality `Z < 1 + y + y²/2 + y³/6 + y⁴/24`, which numerically
holds on all of `(0, 0.45]` — the fourth-order partial sum already suffices.

`N` vanishes to ninth order at `0`:
`N = (16/45)θ⁹ − (16/21)θ¹¹ + (2032/1575)θ¹³ − …`, which is why no bound of
lower order can work, and why the remaining step needs series arithmetic to
order ≥ 9. -/

/-- `W = 2θ + tanh θ·(Z−1)`, the denominator of `y`. -/
noncomputable def W (θ : ℝ) : ℝ := 2 * θ + Real.tanh θ * (Real.cosh (2 * θ) - 1)

/-- `y = 2θ(Z−1)/W`. -/
noncomputable def yOf (θ : ℝ) : ℝ :=
  2 * θ * (Real.cosh (2 * θ) - 1) / W θ

theorem W_pos {θ : ℝ} (hθ : 0 < θ) : 0 < W θ := by
  have h1 : 0 < Real.cosh (2 * θ) - 1 := by
    have := one_lt_cosh hθ; linarith
  have h2 : 0 < Real.tanh θ := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hθ) (Real.cosh_pos θ)
  have : 0 < Real.tanh θ * (Real.cosh (2 * θ) - 1) := mul_pos h2 h1
  simp only [W]
  linarith

theorem yOf_pos {θ : ℝ} (hθ : 0 < θ) : 0 < yOf θ := by
  have h1 : 0 < Real.cosh (2 * θ) - 1 := by
    have := one_lt_cosh hθ; linarith
  have := W_pos hθ
  simp only [yOf]
  positivity

/-- **The log-free reduction.**  If `cosh 2θ` is below the fourth partial sum of
`exp y`, then `F θ > 0`. -/
theorem F_pos_of_exp_bound {θ : ℝ} (hθ : 0 < θ)
    (h : Real.cosh (2 * θ)
      < 1 + yOf θ + yOf θ ^ 2 / 2 + yOf θ ^ 3 / 6 + yOf θ ^ 4 / 24) :
    0 < F θ := by
  have hZ1 : 1 < Real.cosh (2 * θ) := one_lt_cosh hθ
  have hZm1 : 0 < Real.cosh (2 * θ) - 1 := by linarith
  have hZpos : (0:ℝ) < Real.cosh (2 * θ) := by linarith
  have hL : 0 < Real.log (Real.cosh (2 * θ)) := log_cosh_pos hθ
  have hW := W_pos hθ
  have hy := yOf_pos hθ
  -- the partial sum is below `exp y`
  have hpart : 1 + yOf θ + yOf θ ^ 2 / 2 + yOf θ ^ 3 / 6 + yOf θ ^ 4 / 24
      ≤ Real.exp (yOf θ) := by
    have h4 := Real.sum_le_exp_of_nonneg (le_of_lt hy) 5
    simpa [Finset.sum_range_succ, pow_zero, pow_one, Nat.factorial] using h4
  -- hence `log Z < y`
  have hlogy : Real.log (Real.cosh (2 * θ)) < yOf θ := by
    have hZexp : Real.cosh (2 * θ) < Real.exp (yOf θ) := lt_of_lt_of_le h hpart
    have := Real.log_lt_log hZpos hZexp
    rwa [Real.log_exp] at this
  -- `N = W (y − log Z) > 0`, and `F = N / (log Z · (Z−1) · 2θ)`
  have hN : 0 < 2 * θ * (Real.cosh (2 * θ) - 1) - Real.log (Real.cosh (2 * θ)) * W θ := by
    have hy' : yOf θ * W θ = 2 * θ * (Real.cosh (2 * θ) - 1) := by
      simp only [yOf]
      field_simp
    nlinarith [mul_lt_mul_of_pos_right hlogy hW]
  rw [F_eq hθ]
  have hkey : 1 / Real.log (Real.cosh (2 * θ)) - 1 / (Real.cosh (2 * θ) - 1)
      - Real.tanh θ / (2 * θ)
      = (2 * θ * (Real.cosh (2 * θ) - 1) - Real.log (Real.cosh (2 * θ)) * W θ)
        / (Real.log (Real.cosh (2 * θ)) * (Real.cosh (2 * θ) - 1) * (2 * θ)) := by
    simp only [W]
    field_simp
    ring
  rw [hkey]
  apply div_pos hN
  positivity

end BSCAveraging.Core
