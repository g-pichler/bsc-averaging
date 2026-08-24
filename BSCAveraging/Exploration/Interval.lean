import BSCAveraging.Interval

/-! # `Interval` — exploration companion

The declarations of `BSCAveraging.Interval` that are **not** used by any of the
three theorems of `BSCAveraging.Basic`.  Section headers are copied from the
main file so the two read in parallel. -/

/-! # Verified rational interval arithmetic

`NOTES.md` §7f⁷: the last computational ingredient of `(C)` is inequality
(iii)'s one-variable core, `1/log Z − 1/(Z−1) > tanh θ/(2θ)` with `Z = cosh 2θ`,
which on the middle regime is established by a sweep over 650 cells
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


/-! ## Enclosing `exp`

`Real.exp_bound` gives a Taylor remainder only for `|x| ≤ 1`, so the enclosure
is: reduce the argument by `2^k`, Taylor there, then square `k` times.  Squaring
is just `mul` against itself, so its soundness is already available. -/


/-! ## Outward rounding

Exact `ℚ` arithmetic makes denominators grow explosively along a long
computation — each squaring squares the denominator.  Rounding the endpoints
outward to a fixed grid keeps them bounded, and widening an enclosure is
trivially sound. -/


/-! ## Division, and the hyperbolic functions

For the sweep every denominator (`log Z`, `Z−1`, `2θ`, `cosh`) is positive, so
only the positive-denominator inverse is needed; positivity of the enclosure is
a decidable side condition, discharged by computation at the call site. -/


/-! ## Enclosing `log`, by inversion

`log` needs no series: to bound `log z` it is enough to exhibit rationals with
`exp p ≤ z ≤ exp q`, and `exp` we have.  The check is decidable, so the cell
data carries `p` and `q` and the arithmetic verifies them. -/


/-! ## The target function of (iii)'s core

`F(θ) = 1/log Z − 1/(Z−1) − tanh θ/(2θ)` with `Z = cosh 2θ`. -/

/-- Interval extension of `F`, given witnesses `lp ≤ log Z ≤ lq`. -/
def FI (Ith : Iv) (lp lq : ℚ) (k n m : ℕ) : Iv :=
  outward m (sub (sub (inv ⟨lp, lq⟩)
      (inv (outward m (sub (coshI (scale 2 Ith) k n m) (const 1)))))
    (outward m (div (tanhI Ith k n m) (scale 2 Ith))))

theorem mem_FI {Ith : Iv} {θ : ℝ} {lp lq : ℚ} {k n m : ℕ} (hm : 0 < m) (hx : mem Ith θ)
    (hlog : mem ⟨lp, lq⟩ (Real.log (Real.cosh (2 * θ))))
    (hlp : 0 < lp)
    (hZ1 : 0 < (outward m (sub (coshI (scale 2 Ith) k n m) (const 1))).lo)
    (h2θ : 0 < (scale 2 Ith).lo)
    (hcosh : 0 < (coshI Ith k n m).lo)
    (e1 : |(scale 2 Ith).lo / 2 ^ k| ≤ 1) (e2 : |(scale 2 Ith).hi / 2 ^ k| ≤ 1)
    (e3 : |(neg (scale 2 Ith)).lo / 2 ^ k| ≤ 1)
    (e4 : |(neg (scale 2 Ith)).hi / 2 ^ k| ≤ 1)
    (f1 : |Ith.lo / 2 ^ k| ≤ 1) (f2 : |Ith.hi / 2 ^ k| ≤ 1)
    (f3 : |(neg Ith).lo / 2 ^ k| ≤ 1) (f4 : |(neg Ith).hi / 2 ^ k| ≤ 1)
    (hn : 0 < n) :
    mem (FI Ith lp lq k n m)
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
  have t1 := mem_inv (J := ⟨lp, lq⟩) hlp hlog
  have t2 := mem_inv hZ1 hZm1
  have t3 := mem_outward hm (mem_div h2θ (mem_tanhI hm f1 f2 f3 f4 hn hcosh hx) h2)
  exact mem_outward hm (mem_sub (mem_sub t1 t2) t3)

/-- Positivity of an interval is decidable and implies positivity of every
member — this is how a cell is discharged. -/
def isPos (I : Iv) : Bool := 0 < I.lo

theorem pos_of_isPos {I : Iv} {x : ℝ} (hI : isPos I = true) (hx : mem I x) : 0 < x := by
  have h : (0 : ℚ) < I.lo := by simpa [isPos] using hI
  have : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast h
  linarith [hx.1]

/-! ## The sweep -/

/-- One cell: its `θ`-range and the two rational witnesses for `log(cosh 2θ)`. -/
structure Cell where
  lo : ℚ
  hi : ℚ
  lp : ℚ
  lq : ℚ
deriving Repr, Inhabited

/-- Everything checked for a single cell, as one decidable right-nested
conjunction. -/
def cellOk (c : Cell) (k n m : ℕ) : Bool :=
  let Ith : Iv := ⟨c.lo, c.hi⟩
  let I2 := scale 2 Ith
  let Z := coshI I2 k n m
  decide (|c.lp / 2 ^ k| ≤ 1) && (decide (|c.lq / 2 ^ k| ≤ 1) &&
  (decide (0 < c.lp) && (decide ((expIv c.lp k n m).hi ≤ Z.lo) &&
  (decide (Z.hi ≤ (expIv c.lq k n m).lo) &&
  (decide (0 < (outward m (sub Z (const 1))).lo) &&
  (decide (0 < I2.lo) && (decide (0 < (coshI Ith k n m).lo) &&
  (decide (|I2.lo / 2 ^ k| ≤ 1) && (decide (|I2.hi / 2 ^ k| ≤ 1) &&
  (decide (|(neg I2).lo / 2 ^ k| ≤ 1) && (decide (|(neg I2).hi / 2 ^ k| ≤ 1) &&
  (decide (|Ith.lo / 2 ^ k| ≤ 1) && (decide (|Ith.hi / 2 ^ k| ≤ 1) &&
  (decide (|(neg Ith).lo / 2 ^ k| ≤ 1) && (decide (|(neg Ith).hi / 2 ^ k| ≤ 1) &&
  isPos (FI Ith c.lp c.lq k n m))))))))))))))))

/-- `F` is positive on a cell that passes the test. -/
theorem pos_of_cellOk {c : Cell} {θ : ℝ} {k n m : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hok : cellOk c k n m = true) (hlo : (c.lo : ℝ) ≤ θ) (hhi : θ ≤ (c.hi : ℝ)) :
    0 < 1 / Real.log (Real.cosh (2 * θ)) - 1 / (Real.cosh (2 * θ) - 1)
      - Real.tanh θ / (2 * θ) := by
  simp only [cellOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hp, hq, hlp, hw1, hw2, hZ1, h2θ, hcosh, e1, e2, e3, e4, f1, f2, f3, f4, hpos⟩ := hok
  have hx : mem ⟨c.lo, c.hi⟩ θ := ⟨hlo, hhi⟩
  have h2 : mem (scale 2 ⟨c.lo, c.hi⟩) (2 * θ) := by
    have := mem_scale (2 : ℚ) hx
    simpa using this
  have hZ := mem_coshI hm e1 e2 e3 e4 hn h2
  have hZpos : (0:ℝ) < Real.cosh (2 * θ) := Real.cosh_pos _
  have hle1 : (((expIv c.lp k n m).hi : ℚ) : ℝ) ≤ Real.cosh (2 * θ) :=
    le_trans (by exact_mod_cast hw1) hZ.1
  have hle2 : Real.cosh (2 * θ) ≤ (((expIv c.lq k n m).lo : ℚ) : ℝ) :=
    le_trans hZ.2 (by exact_mod_cast hw2)
  have hlog := mem_logIv hm hp hq hn hZpos hle1 hle2
  exact pos_of_isPos hpos
    (mem_FI hm hx hlog hlp hZ1 h2θ hcosh e1 e2 e3 e4 f1 f2 f3 f4 hn)


/-! ### A cancellation-free form

`F` is a difference of large nearly-equal terms — at `θ = 0.45` it is
`2.779 − 2.309 − 0.469 = 0.0013` — and interval arithmetic cannot see the
cancellation, so the naive extension's width is the *sum* of the term
variations.  Combining the first two terms into one fraction,

```
1/log Z − 1/(Z−1) = ((Z−1) − log Z) / (log Z · (Z−1)),
```

removes one cancellation and shrinks the enclosure by about a factor five. -/


/-- The cell test, in the cancellation-free form. -/
def cellOk2 (c : Cell) (k n m : ℕ) : Bool :=
  let Ith : Iv := ⟨c.lo, c.hi⟩
  let I2 := scale 2 Ith
  let Z := coshI I2 k n m
  let Zm1 := outward m (sub Z (const 1))
  decide (|c.lp / 2 ^ k| ≤ 1) && (decide (|c.lq / 2 ^ k| ≤ 1) &&
  (decide (0 < c.lp) && (decide ((expIv c.lp k n m).hi ≤ Z.lo) &&
  (decide (Z.hi ≤ (expIv c.lq k n m).lo) && (decide (0 < Zm1.lo) &&
  (decide (0 < (outward m (mul ⟨c.lp, c.lq⟩ Zm1)).lo) &&
  (decide (0 < I2.lo) && (decide (0 < (coshI Ith k n m).lo) &&
  (decide (|I2.lo / 2 ^ k| ≤ 1) && (decide (|I2.hi / 2 ^ k| ≤ 1) &&
  (decide (|(neg I2).lo / 2 ^ k| ≤ 1) && (decide (|(neg I2).hi / 2 ^ k| ≤ 1) &&
  (decide (|Ith.lo / 2 ^ k| ≤ 1) && (decide (|Ith.hi / 2 ^ k| ≤ 1) &&
  (decide (|(neg Ith).lo / 2 ^ k| ≤ 1) && (decide (|(neg Ith).hi / 2 ^ k| ≤ 1) &&
  isPos (FI2 Ith c.lp c.lq k n m)))))))))))))))))

theorem pos_of_cellOk2 {c : Cell} {θ : ℝ} {k n m : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hok : cellOk2 c k n m = true) (hlo : (c.lo : ℝ) ≤ θ) (hhi : θ ≤ (c.hi : ℝ)) :
    0 < 1 / Real.log (Real.cosh (2 * θ)) - 1 / (Real.cosh (2 * θ) - 1)
      - Real.tanh θ / (2 * θ) := by
  simp only [cellOk2, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hp, hq, hlp, hw1, hw2, hZ1, hprod, h2θ, hcosh, e1, e2, e3, e4, f1, f2, f3, f4,
    hpos⟩ := hok
  have hx : mem ⟨c.lo, c.hi⟩ θ := ⟨hlo, hhi⟩
  have h2 : mem (scale 2 ⟨c.lo, c.hi⟩) (2 * θ) := by
    have := mem_scale (2 : ℚ) hx
    simpa using this
  have hZ := mem_coshI hm e1 e2 e3 e4 hn h2
  have hZpos : (0:ℝ) < Real.cosh (2 * θ) := Real.cosh_pos _
  have hle1 : (((expIv c.lp k n m).hi : ℚ) : ℝ) ≤ Real.cosh (2 * θ) :=
    le_trans (by exact_mod_cast hw1) hZ.1
  have hle2 : Real.cosh (2 * θ) ≤ (((expIv c.lq k n m).lo : ℚ) : ℝ) :=
    le_trans hZ.2 (by exact_mod_cast hw2)
  have hlog := mem_logIv hm hp hq hn hZpos hle1 hle2
  exact pos_of_isPos hpos
    (mem_FI2 hm hx hlog hlp hZ1 hprod h2θ hcosh e1 e2 e3 e4 f1 f2 f3 f4 hn)

/-- The cells tile `[A,B]` from left to right. -/
def tiles (B : ℚ) : ℚ → List Cell → Bool
  | _, [] => false
  | A, [c] => decide (c.lo ≤ A) && decide (B ≤ c.hi)
  | A, c :: cs => decide (c.lo ≤ A) && tiles B c.hi cs

/-- **The sweep is sound.** -/
theorem sweep_sound {k n m : ℕ} (hm : 0 < m) (hn : 0 < n) {B : ℚ} :
    ∀ (cs : List Cell) (A : ℚ), tiles B A cs = true →
      (∀ c ∈ cs, cellOk c k n m = true) →
      ∀ θ : ℝ, (A : ℝ) ≤ θ → θ ≤ (B : ℝ) →
        0 < 1 / Real.log (Real.cosh (2 * θ)) - 1 / (Real.cosh (2 * θ) - 1)
          - Real.tanh θ / (2 * θ)
  | [], A, ht, _, _, _, _ => by simp [tiles] at ht
  | [c], A, ht, hall, θ, hA, hB => by
    simp only [tiles, Bool.and_eq_true, decide_eq_true_eq] at ht
    refine pos_of_cellOk hm hn (hall c (by simp)) ?_ ?_
    · exact le_trans (by exact_mod_cast ht.1) hA
    · exact le_trans hB (by exact_mod_cast ht.2)
  | c :: d :: cs, A, ht, hall, θ, hA, hB => by
    simp only [tiles, Bool.and_eq_true, decide_eq_true_eq] at ht
    by_cases hcase : θ ≤ (c.hi : ℝ)
    · refine pos_of_cellOk hm hn (hall c (by simp)) ?_ hcase
      exact le_trans (by exact_mod_cast ht.1) hA
    · push_neg at hcase
      exact sweep_sound hm hn (d :: cs) c.hi ht.2
        (fun x hx => hall x (by simp [hx])) θ (le_of_lt hcase) hB

end BSCAveraging.Iv
