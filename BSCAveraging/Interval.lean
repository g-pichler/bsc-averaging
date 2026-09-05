import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Verified rational interval arithmetic

`NOTES.md` §7f⁷: the last computational ingredient of `(C)` is inequality
(iii)'s one-variable core, `1/log Z − 1/(Z−1) > tanh θ/(2θ)` with `Z = cosh 2θ`,
which on the middle regime is established by a sweep over 88 cells
(`CoreSweep.lean`).  Doing
that in Lean by writing the cells out as terms is hopeless — the same lesson as
the kernel certificate (`Reflect.lean`): encode the computation as **data** and
prove one soundness lemma.

This file is the foundation: intervals with rational endpoints, arithmetic, and
soundness of each operation.  The point of an *interval extension* is that
soundness composes — if every operation maps enclosures to enclosures, then the
computed enclosure of a whole expression contains its true value on the cell, so
a positive lower endpoint proves positivity on that cell with no Lipschitz
constant and no derivative bound anywhere.

See `NOTES.md` §7f⁷. -/

namespace BSCAveraging.Iv

/-- An interval with rational endpoints. -/
structure Iv where
  lo : ℚ
  hi : ℚ
deriving Repr, DecidableEq, Inhabited

/-- `x` lies in the interval. -/
def mem (I : Iv) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- The degenerate interval at a rational point. -/
def const (q : ℚ) : Iv := ⟨q, q⟩

theorem mem_const (q : ℚ) : mem (const q) (q : ℝ) := ⟨le_rfl, le_rfl⟩

/-- Sum of intervals. -/
def add (I J : Iv) : Iv := ⟨I.lo + J.lo, I.hi + J.hi⟩

theorem mem_add {I J : Iv} {x y : ℝ} (hx : mem I x) (hy : mem J y) :
    mem (add I J) (x + y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  constructor <;> · simp only [add, Rat.cast_add]; linarith

/-- Negation. -/
def neg (I : Iv) : Iv := ⟨-I.hi, -I.lo⟩

theorem mem_neg {I : Iv} {x : ℝ} (hx : mem I x) : mem (neg I) (-x) := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> · simp only [neg, Rat.cast_neg]; linarith

/-- Difference. -/
def sub (I J : Iv) : Iv := add I (neg J)

theorem mem_sub {I J : Iv} {x y : ℝ} (hx : mem I x) (hy : mem J y) :
    mem (sub I J) (x - y) := by
  have := mem_add hx (mem_neg hy)
  simpa [sub, sub_eq_add_neg] using this

/-- Product: the extremes of a bilinear function on a rectangle sit at its
corners. -/
def mul (I J : Iv) : Iv :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
    max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

/-- For fixed `y`, `x ↦ xy` is affine, so it is bounded by its values at the
endpoints of `x`'s interval; then the same in `y`. -/
private theorem mul_le_max {a b c d x y : ℝ} (hxa : a ≤ x) (hxb : x ≤ b)
    (hyc : c ≤ y) (hyd : y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have step1 : x * y ≤ max (a * y) (b * y) := by
    rcases le_total 0 y with hy | hy
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_right hxb hy)
    · exact le_max_of_le_left (by nlinarith [mul_nonneg (sub_nonneg.mpr hxa) (neg_nonneg.mpr hy)])
  have step2 : a * y ≤ max (a * c) (a * d) := by
    rcases le_total 0 a with ha | ha
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_left hyd ha)
    · exact le_max_of_le_left (by nlinarith [mul_nonneg (neg_nonneg.mpr ha) (sub_nonneg.mpr hyc)])
  have step3 : b * y ≤ max (b * c) (b * d) := by
    rcases le_total 0 b with hb | hb
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_left hyd hb)
    · exact le_max_of_le_left (by nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hyc)])
  refine le_trans step1 (max_le ?_ ?_)
  · exact le_trans step2 (le_max_left _ _)
  · exact le_trans step3 (le_max_right _ _)

/-- The mirror bound. -/
private theorem min_le_mul {a b c d x y : ℝ} (hxa : a ≤ x) (hxb : x ≤ b)
    (hyc : c ≤ y) (hyd : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  have step1 : min (a * y) (b * y) ≤ x * y := by
    rcases le_total 0 y with hy | hy
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right hxa hy)
    · refine le_trans (min_le_right _ _) ?_
      nlinarith [mul_nonneg (sub_nonneg.mpr hxb) (neg_nonneg.mpr hy)]
  have step2 : min (a * c) (a * d) ≤ a * y := by
    rcases le_total 0 a with ha | ha
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hyc ha)
    · refine le_trans (min_le_right _ _) ?_
      nlinarith [mul_nonneg (neg_nonneg.mpr ha) (sub_nonneg.mpr hyd)]
  have step3 : min (b * c) (b * d) ≤ b * y := by
    rcases le_total 0 b with hb | hb
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hyc hb)
    · refine le_trans (min_le_right _ _) ?_
      nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hyd)]
  refine le_trans (le_min ?_ ?_) step1
  · exact le_trans (min_le_left _ _) step2
  · exact le_trans (min_le_right _ _) step3

theorem mem_mul {I J : Iv} {x y : ℝ} (hx : mem I x) (hy : mem J y) :
    mem (mul I J) (x * y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  constructor
  · simp only [mul, Rat.cast_min, Rat.cast_mul]
    exact min_le_mul h1 h2 h3 h4
  · simp only [mul, Rat.cast_max, Rat.cast_mul]
    exact mul_le_max h1 h2 h3 h4


/-! ## Enclosing `exp`

`Real.exp_bound` gives a Taylor remainder only for `|x| ≤ 1`, so the enclosure
is: reduce the argument by `2^k`, Taylor there, then square `k` times.  Squaring
is just `mul` against itself, so its soundness is already available. -/

/-- Truncated Taylor sum of `exp`, over `ℚ` (recursive, so the cast lemma is an
easy induction). -/
def expSum (q : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => expSum q n + q ^ n / (Nat.factorial n)

open Finset in
theorem cast_expSum (q : ℚ) :
    ∀ n, ((expSum q n : ℚ) : ℝ) = ∑ m ∈ range n, (q : ℝ) ^ m / (Nat.factorial m)
  | 0 => by simp [expSum]
  | n + 1 => by
    rw [expSum, Finset.sum_range_succ, ← cast_expSum q n]
    push_cast
    ring

/-- Enclosure of `exp q` for `|q| ≤ 1`, from `Real.exp_bound`. -/
def expIv1 (q : ℚ) (n : ℕ) : Iv :=
  let s := expSum q n
  let e := |q| ^ n * ((n + 1) / (Nat.factorial n * n))
  ⟨s - e, s + e⟩

open Finset in
theorem mem_expIv1 {q : ℚ} (hq : |q| ≤ 1) {n : ℕ} (hn : 0 < n) :
    mem (expIv1 q n) (Real.exp q) := by
  have hqr : |(q : ℝ)| ≤ 1 := by rw [← Rat.cast_abs]; exact_mod_cast hq
  have h := Real.exp_bound hqr hn
  have hsum := cast_expSum q n
  have herr : ((|q| ^ n * ((n + 1) / (Nat.factorial n * n)) : ℚ) : ℝ)
      = |(q : ℝ)| ^ n * ((n.succ : ℝ) / (Nat.factorial n * n)) := by
    push_cast [Rat.cast_abs]
    ring
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · simp only [expIv1, Rat.cast_sub, hsum, herr]
    linarith
  · simp only [expIv1, Rat.cast_add, hsum, herr]
    linarith

/-! ## Outward rounding

Exact `ℚ` arithmetic makes denominators grow explosively along a long
computation — each squaring squares the denominator.  Rounding the endpoints
outward to a fixed grid keeps them bounded, and widening an enclosure is
trivially sound. -/

/-- Round the endpoints outward to multiples of `1/m`. -/
def outward (m : ℕ) (I : Iv) : Iv :=
  ⟨((⌊I.lo * m⌋ : ℤ) : ℚ) / (m : ℚ), ((⌈I.hi * m⌉ : ℤ) : ℚ) / (m : ℚ)⟩

theorem mem_outward {I : Iv} {x : ℝ} {m : ℕ} (hm : 0 < m) (hx : mem I x) :
    mem (outward m I) x := by
  have hmq : (0:ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hlo : ((⌊I.lo * m⌋ : ℤ) : ℚ) / (m : ℚ) ≤ I.lo := by
    rw [div_le_iff₀ hmq]; exact Int.floor_le _
  have hhi : I.hi ≤ ((⌈I.hi * m⌉ : ℤ) : ℚ) / (m : ℚ) := by
    rw [le_div_iff₀ hmq]; exact Int.le_ceil _
  refine ⟨le_trans ?_ hx.1, le_trans hx.2 ?_⟩
  · show ((outward m I).lo : ℝ) ≤ (I.lo : ℝ)
    simp only [outward]; exact_mod_cast hlo
  · show ((I.hi : ℝ)) ≤ ((outward m I).hi : ℝ)
    simp only [outward]; exact_mod_cast hhi

/-- Squaring an interval. -/
def sq (I : Iv) : Iv := mul I I

theorem mem_sq {I : Iv} {x : ℝ} (h : mem I x) : mem (sq I) (x ^ 2) := by
  have := mem_mul h h
  simpa [sq, pow_two] using this

/-- Square `k` times: encloses `x ^ (2 ^ k)`.  Rounding after every squaring is
essential — without it each step squares the denominator. -/
def sqIter (m : ℕ) : ℕ → Iv → Iv
  | 0, I => I
  | k + 1, I => outward m (sq (sqIter m k I))

theorem mem_sqIter {I : Iv} {x : ℝ} {m : ℕ} (hm : 0 < m) (h : mem I x) :
    ∀ k, mem (sqIter m k I) (x ^ (2 ^ k))
  | 0 => by simpa [sqIter] using h
  | k + 1 => by
    have hk := mem_sqIter hm h k
    have h2 := mem_sq hk
    have he : (x ^ (2 ^ k)) ^ 2 = x ^ (2 ^ (k + 1)) := by
      rw [← pow_mul, pow_succ]
    rw [he] at h2
    exact mem_outward hm h2

/-- **Enclosure of `exp q`**: Taylor at the reduced argument `q/2^k`, then `k`
squarings. -/
def expIv (q : ℚ) (k n m : ℕ) : Iv := sqIter m k (outward m (expIv1 (q / 2 ^ k) n))

theorem mem_expIv {q : ℚ} {k n m : ℕ} (hm : 0 < m) (hq : |q / 2 ^ k| ≤ 1) (hn : 0 < n) :
    mem (expIv q k n m) (Real.exp q) := by
  have h1 := mem_outward hm (mem_expIv1 hq hn)
  have h2 := mem_sqIter hm h1 k
  have hpow : (Real.exp ((q / 2 ^ k : ℚ) : ℝ)) ^ (2 ^ k) = Real.exp q := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rwa [hpow] at h2


/-! ## Division, and the hyperbolic functions

For the sweep every denominator (`log Z`, `Z−1`, `2θ`, `cosh`) is positive, so
only the positive-denominator inverse is needed; positivity of the enclosure is
a decidable side condition, discharged by computation at the call site. -/

/-- Reciprocal of an interval that lies strictly right of `0`. -/
def inv (J : Iv) : Iv := ⟨1 / J.hi, 1 / J.lo⟩

theorem mem_inv {J : Iv} {y : ℝ} (hJ : 0 < J.lo) (hy : mem J y) : mem (inv J) (1 / y) := by
  obtain ⟨h1, h2⟩ := hy
  have hlo : (0:ℝ) < (J.lo : ℝ) := by exact_mod_cast hJ
  have hy0 : 0 < y := lt_of_lt_of_le hlo h1
  have hhi : (0:ℝ) < (J.hi : ℝ) := lt_of_lt_of_le hy0 h2
  constructor
  · simp only [inv, Rat.cast_div, Rat.cast_one]
    exact one_div_le_one_div_of_le hy0 h2
  · simp only [inv, Rat.cast_div, Rat.cast_one]
    exact one_div_le_one_div_of_le hlo h1

/-- Quotient, for a denominator interval strictly right of `0`. -/
def div (I J : Iv) : Iv := mul I (inv J)

theorem mem_div {I J : Iv} {x y : ℝ} (hJ : 0 < J.lo) (hx : mem I x) (hy : mem J y) :
    mem (div I J) (x / y) := by
  have h := mem_mul hx (mem_inv hJ hy)
  have e : x * (1 / y) = x / y := by ring
  rwa [e] at h

/-- Scaling by a rational. -/
def scale (c : ℚ) (I : Iv) : Iv := mul (const c) I

theorem mem_scale {I : Iv} {x : ℝ} (c : ℚ) (hx : mem I x) : mem (scale c I) ((c : ℝ) * x) :=
  mem_mul (mem_const c) hx

/-- **Interval extension of `exp`**, by monotonicity of the endpoints. -/
def expI (I : Iv) (k n m : ℕ) : Iv := ⟨(expIv I.lo k n m).lo, (expIv I.hi k n m).hi⟩

theorem mem_expI {I : Iv} {x : ℝ} {k n m : ℕ} (hm : 0 < m) (hlo : |I.lo / 2 ^ k| ≤ 1)
    (hhi : |I.hi / 2 ^ k| ≤ 1) (hn : 0 < n) (hx : mem I x) :
    mem (expI I k n m) (Real.exp x) := by
  obtain ⟨h1, h2⟩ := hx
  have e1 := mem_expIv (q := I.lo) hm hlo hn
  have e2 := mem_expIv (q := I.hi) hm hhi hn
  exact ⟨le_trans e1.1 (Real.exp_le_exp.mpr h1), le_trans (Real.exp_le_exp.mpr h2) e2.2⟩

/-- `cosh` as `(eˣ + e⁻ˣ)/2`, rounded. -/
def coshI (I : Iv) (k n m : ℕ) : Iv :=
  outward m (scale (1 / 2) (add (expI I k n m) (expI (neg I) k n m)))

/-- `sinh` as `(eˣ − e⁻ˣ)/2`, rounded. -/
def sinhI (I : Iv) (k n m : ℕ) : Iv :=
  outward m (scale (1 / 2) (sub (expI I k n m) (expI (neg I) k n m)))

theorem mem_coshI {I : Iv} {x : ℝ} {k n m : ℕ} (hm : 0 < m) (hlo : |I.lo / 2 ^ k| ≤ 1)
    (hhi : |I.hi / 2 ^ k| ≤ 1) (hnlo : |(neg I).lo / 2 ^ k| ≤ 1)
    (hnhi : |(neg I).hi / 2 ^ k| ≤ 1) (hn : 0 < n) (hx : mem I x) :
    mem (coshI I k n m) (Real.cosh x) := by
  have h1 := mem_expI hm hlo hhi hn hx
  have h2 := mem_expI hm hnlo hnhi hn (mem_neg hx)
  have h := mem_scale (1/2 : ℚ) (mem_add h1 h2)
  have e : ((1/2 : ℚ) : ℝ) * (Real.exp x + Real.exp (-x))
      = (Real.exp x + Real.exp (-x)) / 2 := by push_cast; ring
  rw [e] at h
  rw [Real.cosh_eq]
  exact mem_outward hm h

theorem mem_sinhI {I : Iv} {x : ℝ} {k n m : ℕ} (hm : 0 < m) (hlo : |I.lo / 2 ^ k| ≤ 1)
    (hhi : |I.hi / 2 ^ k| ≤ 1) (hnlo : |(neg I).lo / 2 ^ k| ≤ 1)
    (hnhi : |(neg I).hi / 2 ^ k| ≤ 1) (hn : 0 < n) (hx : mem I x) :
    mem (sinhI I k n m) (Real.sinh x) := by
  have h1 := mem_expI hm hlo hhi hn hx
  have h2 := mem_expI hm hnlo hnhi hn (mem_neg hx)
  have h := mem_scale (1/2 : ℚ) (mem_sub h1 h2)
  have e : ((1/2 : ℚ) : ℝ) * (Real.exp x - Real.exp (-x))
      = (Real.exp x - Real.exp (-x)) / 2 := by push_cast; ring
  rw [e] at h
  rw [Real.sinh_eq]
  exact mem_outward hm h

/-- `tanh = sinh / cosh`. -/
def tanhI (I : Iv) (k n m : ℕ) : Iv := outward m (div (sinhI I k n m) (coshI I k n m))

theorem mem_tanhI {I : Iv} {x : ℝ} {k n m : ℕ} (hm : 0 < m) (hlo : |I.lo / 2 ^ k| ≤ 1)
    (hhi : |I.hi / 2 ^ k| ≤ 1) (hnlo : |(neg I).lo / 2 ^ k| ≤ 1)
    (hnhi : |(neg I).hi / 2 ^ k| ≤ 1) (hn : 0 < n)
    (hpos : 0 < (coshI I k n m).lo) (hx : mem I x) :
    mem (tanhI I k n m) (Real.tanh x) := by
  have hs := mem_sinhI hm hlo hhi hnlo hnhi hn hx
  have hc := mem_coshI hm hlo hhi hnlo hnhi hn hx
  have h := mem_div hpos hs hc
  rw [← Real.tanh_eq_sinh_div_cosh] at h
  exact mem_outward hm h

/-! ## Enclosing `log`, by inversion

`log` needs no series: to bound `log z` it is enough to exhibit rationals with
`exp p ≤ z ≤ exp q`, and `exp` we have.  The check is decidable, so the cell
data carries `p` and `q` and the arithmetic verifies them. -/

theorem mem_logIv {p q : ℚ} {z : ℝ} {k n m : ℕ} (hm : 0 < m) (hp : |p / 2 ^ k| ≤ 1)
    (hq : |q / 2 ^ k| ≤ 1) (hn : 0 < n) (hz : 0 < z)
    (hlo : ((expIv p k n m).hi : ℝ) ≤ z) (hhi : z ≤ ((expIv q k n m).lo : ℝ)) :
    mem ⟨p, q⟩ (Real.log z) := by
  have ep := mem_expIv hm hp hn
  have eq' := mem_expIv hm hq hn
  constructor
  · have h : Real.exp (p : ℝ) ≤ z := le_trans ep.2 hlo
    have := Real.log_le_log (Real.exp_pos _) h
    rwa [Real.log_exp] at this
  · have h : z ≤ Real.exp (q : ℝ) := le_trans hhi eq'.1
    have := Real.log_le_log hz h
    rwa [Real.log_exp] at this

/-! ## The target function of (iii)'s core

`F(θ) = 1/log Z − 1/(Z−1) − tanh θ/(2θ)` with `Z = cosh 2θ`. -/





/-! ## The sweep -/





/-! ### A cancellation-free form

`F` is a difference of large nearly-equal terms — at `θ = 0.45` it is
`2.779 − 2.309 − 0.469 = 0.0013` — and interval arithmetic cannot see the
cancellation, so the naive extension's width is the *sum* of the term
variations.  Combining the first two terms into one fraction,

```
1/log Z − 1/(Z−1) = ((Z−1) − log Z) / (log Z · (Z−1)),
```

removes one cancellation and shrinks the enclosure by about a factor five. -/

/-- Cancellation-free interval extension of `F`. -/
def FI2 (Ith : Iv) (lp lq : ℚ) (k n m : ℕ) : Iv :=
  let Z := coshI (scale 2 Ith) k n m
  let Zm1 := outward m (sub Z (const 1))
  let L : Iv := ⟨lp, lq⟩
  outward m (sub (outward m (div (sub Zm1 L) (outward m (mul L Zm1))))
    (outward m (div (tanhI Ith k n m) (scale 2 Ith))))

theorem mem_FI2 {Ith : Iv} {θ : ℝ} {lp lq : ℚ} {k n m : ℕ} (hm : 0 < m) (hx : mem Ith θ)
    (hlog : mem ⟨lp, lq⟩ (Real.log (Real.cosh (2 * θ))))
    (hlp : 0 < lp)
    (hZ1 : 0 < (outward m (sub (coshI (scale 2 Ith) k n m) (const 1))).lo)
    (hprod : 0 < (outward m (mul ⟨lp, lq⟩
      (outward m (sub (coshI (scale 2 Ith) k n m) (const 1))))).lo)
    (h2θ : 0 < (scale 2 Ith).lo)
    (hcosh : 0 < (coshI Ith k n m).lo)
    (e1 : |(scale 2 Ith).lo / 2 ^ k| ≤ 1) (e2 : |(scale 2 Ith).hi / 2 ^ k| ≤ 1)
    (e3 : |(neg (scale 2 Ith)).lo / 2 ^ k| ≤ 1)
    (e4 : |(neg (scale 2 Ith)).hi / 2 ^ k| ≤ 1)
    (f1 : |Ith.lo / 2 ^ k| ≤ 1) (f2 : |Ith.hi / 2 ^ k| ≤ 1)
    (f3 : |(neg Ith).lo / 2 ^ k| ≤ 1) (f4 : |(neg Ith).hi / 2 ^ k| ≤ 1)
    (hn : 0 < n) :
    mem (FI2 Ith lp lq k n m)
      (1 / Real.log (Real.cosh (2 * θ)) - 1 / (Real.cosh (2 * θ) - 1)
        - Real.tanh θ / (2 * θ)) := by
  have h2 : mem (scale 2 Ith) (2 * θ) := by
    have := mem_scale (2 : ℚ) hx
    simpa using this
  have hZ := mem_coshI hm e1 e2 e3 e4 hn h2
  have hone : mem (const 1) (1 : ℝ) := by
    have := mem_const (1 : ℚ)
    simpa using this
  have hZm1 := mem_outward hm (mem_sub hZ hone)
  -- positivity of the two denominators, transported to `ℝ`
  have hZ1r : (0:ℝ) < Real.cosh (2 * θ) - 1 := by
    have : (0:ℝ) < ((outward m (sub (coshI (scale 2 Ith) k n m) (const 1))).lo : ℝ) := by
      exact_mod_cast hZ1
    linarith [hZm1.1]
  have hLr : (0:ℝ) < Real.log (Real.cosh (2 * θ)) := by
    have : (0:ℝ) < (lp : ℝ) := by exact_mod_cast hlp
    linarith [hlog.1]
  -- the algebraic identity
  have hid : 1 / Real.log (Real.cosh (2 * θ)) - 1 / (Real.cosh (2 * θ) - 1)
      = ((Real.cosh (2 * θ) - 1) - Real.log (Real.cosh (2 * θ)))
        / (Real.log (Real.cosh (2 * θ)) * (Real.cosh (2 * θ) - 1)) := by
    field_simp
  have hnum := mem_sub hZm1 hlog
  have hden := mem_outward hm (mem_mul hlog hZm1)
  have hfrac := mem_outward hm (mem_div hprod hnum hden)
  have t3 := mem_outward hm (mem_div h2θ (mem_tanhI hm f1 f2 f3 f4 hn hcosh hx) h2)
  have h := mem_outward hm (mem_sub hfrac t3)
  rw [hid]
  exact h





end BSCAveraging.Iv
