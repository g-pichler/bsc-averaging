import BSCAveraging.Reflect
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Non-negativity of a syntax tree from one big-integer evaluation

Stage 1: the tree as a multivariate polynomial, its bidegree, and an L1 bound
on its coefficients — all structural, nothing expanded. -/

namespace BSCAveraging.Reflect

open MvPolynomial

/-! ### The syntax tree as a polynomial -/

/-- The polynomial a syntax tree denotes. -/
noncomputable def PE.toMv : PE → MvPolynomial (Fin 7) ℤ
  | .var i => X i
  | .int n => C n
  | .add a b => a.toMv + b.toMv
  | .sub a b => a.toMv - b.toMv
  | .mul a b => a.toMv * b.toMv
  | .pow a n => a.toMv ^ n

theorem PE.eval_eq_aeval (ρ : Fin 7 → ℝ) : ∀ e : PE, PE.eval ρ e = aeval ρ e.toMv
  | .var i => by simp [PE.eval, PE.toMv]
  | .int n => by simp [PE.eval, PE.toMv]
  | .add a b => by simp [PE.eval, PE.toMv, PE.eval_eq_aeval ρ a, PE.eval_eq_aeval ρ b]
  | .sub a b => by simp [PE.eval, PE.toMv, PE.eval_eq_aeval ρ a, PE.eval_eq_aeval ρ b]
  | .mul a b => by simp [PE.eval, PE.toMv, PE.eval_eq_aeval ρ a, PE.eval_eq_aeval ρ b]
  | .pow a n => by simp [PE.eval, PE.toMv, PE.eval_eq_aeval ρ a]

/-- Integer evaluation of a syntax tree — the recursion of `PE.eval`, over `ℤ`. -/
def PE.evalZ (ρ : Fin 7 → ℤ) : PE → ℤ
  | .var i => ρ i
  | .int n => n
  | .add a b => a.evalZ ρ + b.evalZ ρ
  | .sub a b => a.evalZ ρ - b.evalZ ρ
  | .mul a b => a.evalZ ρ * b.evalZ ρ
  | .pow a n => (a.evalZ ρ) ^ n

theorem PE.evalZ_eq_eval (ρ : Fin 7 → ℤ) : ∀ e : PE, PE.evalZ ρ e = MvPolynomial.eval ρ e.toMv
  | .var i => by simp [PE.evalZ, PE.toMv]
  | .int n => by simp [PE.evalZ, PE.toMv]
  | .add a b => by simp [PE.evalZ, PE.toMv, PE.evalZ_eq_eval ρ a, PE.evalZ_eq_eval ρ b]
  | .sub a b => by simp [PE.evalZ, PE.toMv, PE.evalZ_eq_eval ρ a, PE.evalZ_eq_eval ρ b]
  | .mul a b => by simp [PE.evalZ, PE.toMv, PE.evalZ_eq_eval ρ a, PE.evalZ_eq_eval ρ b]
  | .pow a n => by simp [PE.evalZ, PE.toMv, PE.evalZ_eq_eval ρ a]

/-! ### Bidegree -/

/-- Weight of the variables: the first four count towards the `t`-degree, the
last three towards the `s`-degree. -/
def wt : Fin 7 → ℕ × ℕ := fun i => if i.val < 4 then (1, 0) else (0, 1)

/-- The bidegree of a tree, if it is bihomogeneous; computed structurally. -/
def PE.bideg : PE → Option (ℕ × ℕ)
  | .var i => some (wt i)
  | .int _ => some (0, 0)
  | .add a b =>
      match a.bideg, b.bideg with
      | some d, some d' => if d = d' then some d else none
      | _, _ => none
  | .sub a b =>
      match a.bideg, b.bideg with
      | some d, some d' => if d = d' then some d else none
      | _, _ => none
  | .mul a b =>
      match a.bideg, b.bideg with
      | some d, some d' => some (d.1 + d'.1, d.2 + d'.2)
      | _, _ => none
  | .pow a n =>
      match a.bideg with
      | some d => some (n * d.1, n * d.2)
      | none => none

theorem isWH_neg {σ M R : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M}
    {φ : MvPolynomial σ R} {n : M} (h : IsWeightedHomogeneous w φ n) :
    IsWeightedHomogeneous w (-φ) n := fun d hd => h (by rwa [coeff_neg, neg_ne_zero] at hd)

theorem PE.isWeightedHomogeneous_of_bideg :
    ∀ (e : PE) (d : ℕ × ℕ), e.bideg = some d → IsWeightedHomogeneous wt e.toMv d
  | .var i, d, h => by
      simp only [PE.bideg, Option.some.injEq] at h
      subst h; exact isWeightedHomogeneous_X ℤ wt i
  | .int n, d, h => by
      simp only [PE.bideg, Option.some.injEq] at h
      subst h; exact isWeightedHomogeneous_C wt n
  | .add a b, d, h => by
      rcases ha : a.bideg with _ | da <;> rcases hb : b.bideg with _ | db <;>
        simp only [PE.bideg, ha, hb, reduceCtorEq] at h
      split_ifs at h with hd
      · simp only [Option.some.injEq] at h; subst h; subst hd
        exact (PE.isWeightedHomogeneous_of_bideg a _ ha).add (PE.isWeightedHomogeneous_of_bideg b _ hb)
  | .sub a b, d, h => by
      rcases ha : a.bideg with _ | da <;> rcases hb : b.bideg with _ | db <;>
        simp only [PE.bideg, ha, hb, reduceCtorEq] at h
      split_ifs at h with hd
      · simp only [Option.some.injEq] at h; subst h; subst hd
        exact (PE.isWeightedHomogeneous_of_bideg a _ ha).add
          (isWH_neg (PE.isWeightedHomogeneous_of_bideg b _ hb))
  | .mul a b, d, h => by
      rcases ha : a.bideg with _ | da <;> rcases hb : b.bideg with _ | db <;>
        simp only [PE.bideg, ha, hb, reduceCtorEq, Option.some.injEq] at h
      subst h
      exact (PE.isWeightedHomogeneous_of_bideg a _ ha).mul (PE.isWeightedHomogeneous_of_bideg b _ hb)
  | .pow a n, d, h => by
      rcases ha : a.bideg with _ | da <;>
        simp only [PE.bideg, ha, reduceCtorEq, Option.some.injEq] at h
      subst h
      have h1 := (PE.isWeightedHomogeneous_of_bideg a _ ha).pow n
      have h2 : (n * da.1, n * da.2) = n • da := by ext <;> simp
      rw [h2]; exact h1

/-! ### An L1 bound on the coefficients -/

/-- Structural bound on the sum of absolute coefficients. -/
def PE.l1b : PE → ℕ
  | .var _ => 1
  | .int n => n.natAbs
  | .add a b => a.l1b + b.l1b
  | .sub a b => a.l1b + b.l1b
  | .mul a b => a.l1b * b.l1b
  | .pow a n => a.l1b ^ n

/-- The tree with every subtraction replaced by addition and every constant by
its absolute value: a polynomial with non-negative coefficients dominating the
coefficients of `toMv`. -/
noncomputable def PE.absMv : PE → MvPolynomial (Fin 7) ℤ
  | .var i => X i
  | .int n => C (|n|)
  | .add a b => a.absMv + b.absMv
  | .sub a b => a.absMv + b.absMv
  | .mul a b => a.absMv * b.absMv
  | .pow a n => a.absMv ^ n

theorem coeff_mul_nonneg {p q : MvPolynomial (Fin 7) ℤ} (hp : ∀ m, 0 ≤ coeff m p)
    (hq : ∀ m, 0 ≤ coeff m q) (m : Fin 7 →₀ ℕ) : 0 ≤ coeff m (p * q) := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

theorem coeff_pow_nonneg {p : MvPolynomial (Fin 7) ℤ} (hp : ∀ m, 0 ≤ coeff m p) :
    ∀ (n : ℕ) (m : Fin 7 →₀ ℕ), 0 ≤ coeff m (p ^ n)
  | 0, m => by rw [pow_zero, coeff_one]; split_ifs <;> simp
  | n + 1, m => by rw [pow_succ]; exact coeff_mul_nonneg (coeff_pow_nonneg hp n) hp m

theorem PE.absMv_nonneg : ∀ (e : PE) (m : Fin 7 →₀ ℕ), 0 ≤ coeff m e.absMv
  | .var i, m => by simp only [PE.absMv, coeff_X]; split_ifs <;> simp
  | .int n, m => by simp only [PE.absMv, coeff_C]; split_ifs <;> simp
  | .add a b, m => by
      simp only [PE.absMv, coeff_add]; exact add_nonneg (PE.absMv_nonneg a m) (PE.absMv_nonneg b m)
  | .sub a b, m => by
      simp only [PE.absMv, coeff_add]; exact add_nonneg (PE.absMv_nonneg a m) (PE.absMv_nonneg b m)
  | .mul a b, m => coeff_mul_nonneg (PE.absMv_nonneg a) (PE.absMv_nonneg b) m
  | .pow a n, m => coeff_pow_nonneg (PE.absMv_nonneg a) n m

theorem abs_coeff_mul_le {p q p' q' : MvPolynomial (Fin 7) ℤ}
    (hp : ∀ m, |coeff m p| ≤ coeff m p') (hq : ∀ m, |coeff m q| ≤ coeff m q') (m : Fin 7 →₀ ℕ) :
    |coeff m (p * q)| ≤ coeff m (p' * q') := by
  rw [coeff_mul, coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (hp _) (hq _) (abs_nonneg _) ((abs_nonneg _).trans (hp _))

theorem abs_coeff_pow_le {p p' : MvPolynomial (Fin 7) ℤ} (hp : ∀ m, |coeff m p| ≤ coeff m p') :
    ∀ (n : ℕ) (m : Fin 7 →₀ ℕ), |coeff m (p ^ n)| ≤ coeff m (p' ^ n)
  | 0, m => by rw [pow_zero, pow_zero, coeff_one]; split_ifs <;> simp
  | n + 1, m => by
      rw [pow_succ, pow_succ]; exact abs_coeff_mul_le (abs_coeff_pow_le hp n) hp m

theorem PE.abs_coeff_le_absMv : ∀ (e : PE) (m : Fin 7 →₀ ℕ), |coeff m e.toMv| ≤ coeff m e.absMv
  | .var i, m => by simp only [PE.toMv, PE.absMv, coeff_X]; split_ifs <;> simp
  | .int n, m => by simp only [PE.toMv, PE.absMv, coeff_C]; split_ifs <;> simp
  | .add a b, m => by
      simp only [PE.toMv, PE.absMv, coeff_add]
      exact (abs_add_le _ _).trans (add_le_add (PE.abs_coeff_le_absMv a m) (PE.abs_coeff_le_absMv b m))
  | .sub a b, m => by
      simp only [PE.toMv, PE.absMv, coeff_sub, coeff_add]
      exact (abs_sub _ _).trans (add_le_add (PE.abs_coeff_le_absMv a m) (PE.abs_coeff_le_absMv b m))
  | .mul a b, m => abs_coeff_mul_le (PE.abs_coeff_le_absMv a) (PE.abs_coeff_le_absMv b) m
  | .pow a n, m => abs_coeff_pow_le (PE.abs_coeff_le_absMv a) n m

theorem PE.eval_one_absMv : ∀ e : PE, MvPolynomial.eval (fun _ => (1 : ℤ)) e.absMv = (e.l1b : ℤ)
  | .var i => by simp [PE.absMv, PE.l1b]
  | .int n => by simp [PE.absMv, PE.l1b]
  | .add a b => by simp [PE.absMv, PE.l1b, PE.eval_one_absMv a, PE.eval_one_absMv b]
  | .sub a b => by simp [PE.absMv, PE.l1b, PE.eval_one_absMv a, PE.eval_one_absMv b]
  | .mul a b => by simp [PE.absMv, PE.l1b, PE.eval_one_absMv a, PE.eval_one_absMv b]
  | .pow a n => by simp [PE.absMv, PE.l1b, PE.eval_one_absMv a]

/-- A coefficient of a polynomial with non-negative coefficients is at most its
value at `(1, …, 1)`. -/
theorem coeff_le_eval_one {p : MvPolynomial (Fin 7) ℤ} (hp : ∀ m, 0 ≤ coeff m p) (m : Fin 7 →₀ ℕ) :
    coeff m p ≤ MvPolynomial.eval (fun _ => (1 : ℤ)) p := by
  rw [eval_eq']
  simp only [one_pow, Finset.prod_const_one, mul_one]
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (fun d _ => hp d) hm
  · rw [MvPolynomial.notMem_support_iff.mp hm]; exact Finset.sum_nonneg fun d _ => hp d

/-- **The L1 bound**: every coefficient of `toMv e` is at most `l1b e` in absolute value. -/
theorem PE.abs_coeff_le_l1b (e : PE) (m : Fin 7 →₀ ℕ) : |coeff m e.toMv| ≤ (e.l1b : ℤ) :=
  (PE.abs_coeff_le_absMv e m).trans
    ((coeff_le_eval_one (PE.absMv_nonneg e) m).trans_eq (PE.eval_one_absMv e))

/-! ### The Kronecker point -/

def B : ℕ := 2 ^ 64

/-- The slot of a monomial: its exponents in `t₁,t₂,t₃,s₁,s₂` read as base-13 digits
(`t₄` and `s₃` are set to `1` at the Kronecker point). -/
def slot (m : Fin 7 →₀ ℕ) : ℕ := m 0 + 13 * m 1 + 169 * m 2 + 2197 * m 4 + 28561 * m 5

/-- The Kronecker point.  The powers are `ℕ`-powers cast to `ℤ`, so that the kernel
computes them by GMP. -/
def kron : Fin 7 → ℤ :=
  ![((B : ℕ) : ℤ), ((B ^ 13 : ℕ) : ℤ), ((B ^ 169 : ℕ) : ℤ), 1,
    ((B ^ 2197 : ℕ) : ℤ), ((B ^ 28561 : ℕ) : ℤ), 1]

theorem prod_kron_pow (m : Fin 7 →₀ ℕ) : ∏ i, kron i ^ m i = ((B : ℕ) : ℤ) ^ slot m := by
  rw [Fin.prod_univ_seven]
  show ((B : ℕ) : ℤ) ^ m 0 * ((B ^ 13 : ℕ) : ℤ) ^ m 1 * ((B ^ 169 : ℕ) : ℤ) ^ m 2 * (1 : ℤ) ^ m 3
      * ((B ^ 2197 : ℕ) : ℤ) ^ m 4 * ((B ^ 28561 : ℕ) : ℤ) ^ m 5 * (1 : ℤ) ^ m 6 = _
  simp only [Nat.cast_pow, one_pow, mul_one, ← pow_mul, ← pow_add, slot]

theorem eval_kron (P : MvPolynomial (Fin 7) ℤ) :
    MvPolynomial.eval kron P = ∑ d ∈ P.support, coeff d P * ((B : ℕ) : ℤ) ^ slot d := by
  rw [eval_eq']
  exact Finset.sum_congr rfl fun d _ => by rw [prod_kron_pow]

/-- The weight of a monomial, explicitly. -/
theorem weight_wt (d : Fin 7 →₀ ℕ) :
    Finsupp.weight wt d = (d 0 + d 1 + d 2 + d 3, d 4 + d 5 + d 6) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fin.sum_univ_seven]
  simp [wt]

/-- Slots are injective on monomials of bidegree `(12,12)`. -/
theorem slot_injOn {d d' : Fin 7 →₀ ℕ} (hd : Finsupp.weight wt d = (12, 12))
    (hd' : Finsupp.weight wt d' = (12, 12)) (h : slot d = slot d') : d = d' := by
  rw [weight_wt, Prod.mk.injEq] at hd hd'
  obtain ⟨hd1, hd2⟩ := hd
  obtain ⟨hd1', hd2'⟩ := hd'
  simp only [slot] at h
  have e5 : d 5 = d' 5 := by omega
  have e4 : d 4 = d' 4 := by omega
  have e2 : d 2 = d' 2 := by omega
  have e1 : d 1 = d' 1 := by omega
  have e0 : d 0 = d' 0 := by omega
  have e3 : d 3 = d' 3 := by omega
  have e6 : d 6 = d' 6 := by omega
  ext i
  fin_cases i <;> assumption

/-! ### Balanced digits -/

/-- If `N = Σ_{k<L} D k · B^k` with `|D k| < B/2`, `N ≥ 0`, and every base-`B` digit of
`N` is `< B/2`, then every `D k` is non-negative: uniqueness of the balanced
representation, peeled one digit at a time. -/
theorem digits_nonneg : ∀ (L : ℕ) (D : ℕ → ℤ), (∀ k, |D k| < 2 ^ 63) →
    0 ≤ ∑ k ∈ Finset.range L, D k * ((B : ℕ) : ℤ) ^ k →
    (∀ k < L, ((∑ k ∈ Finset.range L, D k * ((B : ℕ) : ℤ) ^ k) / ((B : ℕ) : ℤ) ^ k) % (B : ℕ) < 2 ^ 63) →
    ∀ k < L, 0 ≤ D k
  | 0, _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | L + 1, D, hb, hN, hdig, k, hk => by
      have hB : ((B : ℕ) : ℤ) = 2 ^ 64 := by simp [B]
      have hBpos : (0 : ℤ) < ((B : ℕ) : ℤ) := by rw [hB]; positivity
      set N' : ℤ := ∑ k ∈ Finset.range L, D (k + 1) * ((B : ℕ) : ℤ) ^ k with hN'
      have hsplit : ∑ k ∈ Finset.range (L + 1), D k * ((B : ℕ) : ℤ) ^ k = D 0 + ((B : ℕ) : ℤ) * N' := by
        rw [Finset.sum_range_succ', hN', Finset.mul_sum]
        simp only [pow_zero, mul_one]
        rw [add_comm]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hsplit] at hN hdig
      -- the lowest digit
      have h0 := hdig 0 (Nat.succ_pos L)
      simp only [pow_zero, Int.ediv_one, Int.add_mul_emod_self_left] at h0
      have hD0 : 0 ≤ D 0 := by
        by_contra hneg
        rw [not_le] at hneg
        have h1 : D 0 % ((B : ℕ) : ℤ) = D 0 + ((B : ℕ) : ℤ) := by
          have h2 := Int.add_mul_emod_self_left (D 0) ((B : ℕ) : ℤ) 1
          rw [mul_one, Int.emod_eq_of_lt (by rw [hB]; linarith [(abs_lt.mp (hb 0)).1])
            (by linarith)] at h2
          exact h2.symm
        rw [h1, hB] at h0
        have := (abs_lt.mp (hb 0)).1
        linarith
      have hD0' : D 0 % ((B : ℕ) : ℤ) = D 0 :=
        Int.emod_eq_of_lt hD0 (by rw [hB]; linarith [(abs_lt.mp (hb 0)).2])
      -- the quotient carries the remaining digits
      have hq : (D 0 + ((B : ℕ) : ℤ) * N') / ((B : ℕ) : ℤ) = N' := by
        rw [Int.add_mul_ediv_left _ _ hBpos.ne', Int.ediv_eq_zero_of_lt hD0 (by rw [hB]; linarith [(abs_lt.mp (hb 0)).2]), zero_add]
      have hN'0 : 0 ≤ N' := by
        rw [← hq]; exact Int.ediv_nonneg hN hBpos.le
      have hdig' : ∀ k < L, (N' / ((B : ℕ) : ℤ) ^ k) % (B : ℕ) < 2 ^ 63 := by
        intro k hk
        have := hdig (k + 1) (Nat.succ_lt_succ hk)
        rwa [pow_succ', ← Int.ediv_ediv_of_nonneg hBpos.le, hq] at this
      have ih := digits_nonneg L (fun k => D (k + 1)) (fun k => hb (k + 1)) hN'0 hdig'
      rcases k with _ | k
      · exact hD0
      · exact ih k (Nat.lt_of_succ_lt_succ hk)

/-! ### The mask -/

/-- `Σ_{k<L} 2^63 · B^k`: a `1` in the top bit of each of the first `L` digits. -/
def maskS : ℕ → ℕ
  | 0 => 0
  | L + 1 => maskS L + 2 ^ 63 * B ^ L

theorem B_eq : B = 2 ^ 64 := rfl

theorem B_pow (L : ℕ) : B ^ L = 2 ^ (64 * L) := by rw [B_eq, ← pow_mul]

theorem maskS_lt (L : ℕ) : maskS L < 2 ^ (64 * L) := by
  induction L with
  | zero => simp [maskS]
  | succ L ih =>
      rw [maskS, B_pow, show 64 * (L + 1) = 64 * L + 64 by ring, pow_add]
      have : 2 ^ 63 * 2 ^ (64 * L) + 2 ^ (64 * L) ≤ 2 ^ (64 * L) * 2 ^ 64 := by
        rw [show (2:ℕ) ^ 64 = 2 ^ 63 + 2 ^ 63 by norm_num]; nlinarith
      omega

theorem testBit_maskS (L : ℕ) : ∀ k < L, (maskS L).testBit (64 * k + 63) = true := by
  induction L with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ L ih =>
      intro k hk
      have hm : maskS (L + 1) = 2 ^ (64 * L + 63) + maskS L := by
        rw [maskS, B_pow, pow_add]; ring
      rw [hm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [Nat.testBit_two_pow_add_gt (by omega)]; exact ih k hk
      · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (lt_of_lt_of_le (maskS_lt k)
          (Nat.pow_le_pow_right (by norm_num) (show 64 * k ≤ 64 * k + 63 by omega)))]
        rfl

/-- Geometric sum without division: `(B−1)·S + 1 = B^L`. -/
theorem geomB : ∀ L : ℕ, (B - 1) * (∑ k ∈ Finset.range L, B ^ k) + 1 = B ^ L
  | 0 => by simp
  | L + 1 => by
      rw [Finset.sum_range_succ, mul_add, pow_succ]
      have h := geomB L
      have hB : 1 ≤ B := by rw [B_eq]; exact Nat.one_le_two_pow
      zify [hB, Nat.one_le_pow L B hB] at h ⊢
      nlinarith [h]

theorem maskS_eq_sum (L : ℕ) : maskS L = 2 ^ 63 * ∑ k ∈ Finset.range L, B ^ k := by
  induction L with
  | zero => simp [maskS]
  | succ L ih => rw [maskS, ih, Finset.sum_range_succ, mul_add]

/-- The closed form the kernel evaluates. -/
theorem maskS_eq (L : ℕ) : maskS L = 2 ^ 63 * ((B ^ L - 1) / (B - 1)) := by
  rw [maskS_eq_sum]
  congr 1
  have h := geomB L
  have hB : 0 < B - 1 := by rw [B_eq]; norm_num
  symm
  apply Nat.div_eq_of_eq_mul_left hB
  rw [mul_comm]; omega

/-- From the mask to the digits. -/
theorem digit_lt_of_land (N L : ℕ) (h : N &&& maskS L = 0) :
    ∀ k < L, (N / B ^ k) % B < 2 ^ 63 := by
  intro k hk
  have hbit : N.testBit (64 * k + 63) = false := by
    have := congrArg (fun x => Nat.testBit x (64 * k + 63)) h
    simp only [Nat.testBit_and, Nat.zero_testBit, testBit_maskS L k hk, Bool.and_true] at this
    exact this
  rw [B_pow, B_eq]
  by_contra hge
  push_neg at hge
  set y := N / 2 ^ (64 * k) % 2 ^ 64 with hy
  have hy1 : y < 2 ^ 64 := Nat.mod_lt _ (by positivity)
  have hbit' : y.testBit 63 = false := by
    rw [hy, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simpa [show 63 + 64 * k = 64 * k + 63 by ring] using hbit
  have hsplit : y = 2 ^ 63 + (y - 2 ^ 63) := by omega
  rw [hsplit, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by omega)] at hbit'
  simp at hbit'

/-! ### Assembly -/

/-- Every coefficient of a bihomogeneous tree of bidegree `(12,12)` with L1 bound below
`2^63` is non-negative, provided its value at the Kronecker point is non-negative and
has all top digit-bits clear. -/
theorem PE.coeff_nonneg_of_kron (e : PE) (hdeg : e.bideg = some (12, 12)) (hl1 : e.l1b < 2 ^ 63)
    (hN : 0 ≤ e.evalZ kron) (hmask : (e.evalZ kron).toNat &&& maskS 371293 = 0) :
    ∀ m, 0 ≤ coeff m e.toMv := by
  set P := e.toMv with hP
  have hhom := PE.isWeightedHomogeneous_of_bideg e _ hdeg
  have hslot : ∀ d ∈ P.support, slot d < 371293 := by
    intro d hd
    have hw := hhom (mem_support_iff.mp hd)
    rw [weight_wt, Prod.mk.injEq] at hw
    simp only [slot]; omega
  -- digits from the mask
  have hdigN : ∀ k < 371293, ((e.evalZ kron) / ((B : ℕ) : ℤ) ^ k) % (B : ℕ) < 2 ^ 63 := by
    intro k hk
    have h := digit_lt_of_land _ _ hmask k hk
    have hcast : ((e.evalZ kron).toNat : ℤ) = e.evalZ kron := Int.toNat_of_nonneg hN
    have : ((((e.evalZ kron).toNat / B ^ k) % B : ℕ) : ℤ) < 2 ^ 63 := by exact_mod_cast h
    rwa [Int.natCast_emod, Int.natCast_ediv, Nat.cast_pow, hcast] at this
  -- the value as a digit sum
  set D : ℕ → ℤ := fun k => ∑ d ∈ P.support.filter (fun d => slot d = k), coeff d P with hD
  have hval : e.evalZ kron = ∑ k ∈ Finset.range 371293, D k * ((B : ℕ) : ℤ) ^ k := by
    rw [PE.evalZ_eq_eval, eval_kron, ← Finset.sum_fiberwise_of_maps_to (t := Finset.range 371293)
      (g := slot) (fun d hd => Finset.mem_range.mpr (hslot d hd))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hD, Finset.sum_mul]
    exact Finset.sum_congr rfl fun d hd => by rw [(Finset.mem_filter.mp hd).2]
  -- each fiber has at most one monomial
  have hfib : ∀ k, ∀ d ∈ P.support.filter (fun d => slot d = k), ∀ d' ∈ P.support.filter (fun d => slot d = k), d = d' := by
    intro k d hd d' hd'
    rw [Finset.mem_filter] at hd hd'
    exact slot_injOn (hhom (mem_support_iff.mp hd.1)) (hhom (mem_support_iff.mp hd'.1)) (hd.2.trans hd'.2.symm)
  have hDb : ∀ k, |D k| < 2 ^ 63 := by
    intro k
    rcases (P.support.filter (fun d => slot d = k)).eq_empty_or_nonempty with he | ⟨d, hd⟩
    · simp [hD, he]
    · have hs : P.support.filter (fun d => slot d = k) = {d} :=
        Finset.eq_singleton_iff_unique_mem.mpr ⟨hd, fun d' hd' => hfib k d' hd' d hd⟩
      simp only [hD, hs, Finset.sum_singleton]
      exact lt_of_le_of_lt (PE.abs_coeff_le_l1b e d) (by exact_mod_cast hl1)
  rw [hval] at hN hdigN
  have hDnn := digits_nonneg 371293 D hDb hN hdigN
  intro m
  by_cases hm : m ∈ P.support
  · have hs : P.support.filter (fun d => slot d = slot m) = {m} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨Finset.mem_filter.mpr ⟨hm, rfl⟩, fun d' hd' => hfib _ d' hd' m (Finset.mem_filter.mpr ⟨hm, rfl⟩)⟩
    have := hDnn (slot m) (hslot m hm)
    simpa [hD, hs] using this
  · rw [MvPolynomial.notMem_support_iff.mp hm]

/-- **The reflection principle by Kronecker substitution.**  The hypotheses are four
computations, all of which the kernel does by GMP arithmetic. -/
theorem PE.eval_nonneg_of_kron (e : PE) (hdeg : e.bideg = some (12, 12)) (hl1 : e.l1b < 2 ^ 63)
    (hN : 0 ≤ e.evalZ kron) (hmask : (e.evalZ kron).toNat &&& (2 ^ 63 * ((B ^ 371293 - 1) / (B - 1))) = 0)
    {ρ : Fin 7 → ℝ} (hρ : ∀ i, 0 ≤ ρ i) : 0 ≤ PE.eval ρ e := by
  have hc := PE.coeff_nonneg_of_kron e hdeg hl1 hN (by rwa [maskS_eq])
  rw [PE.eval_eq_aeval, aeval_def, eval₂_eq']
  refine Finset.sum_nonneg fun d _ => mul_nonneg ?_ (Finset.prod_nonneg fun i _ => pow_nonneg (hρ i) _)
  simpa using hc d

end BSCAveraging.Reflect
