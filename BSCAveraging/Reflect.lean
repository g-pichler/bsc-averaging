import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # A reflection layer for nonnegative-coefficient certificates

The kernel lemma can also be proved by handing `ring` an 11385-term identity.
That was tried and abandoned (`NOTES.md` §7f⁴: killed after 476 min at 30 GB
without finishing).  It is expensive twice over: Lean must *parse and
elaborate* a 900 KB arithmetic term (every numeral an `OfNat ℝ`, every `*` an
`HMul` application), and then `ring` must build a proof term for the whole
normalisation.

This file removes both costs.  Polynomials become **data** — a list of
(exponent record, integer coefficient) pairs — with

* `M7`, a seven-slot exponent record (fixed arity, so no length side conditions);
* `Poly := List (M7 × ℤ)`, *not* assumed sorted or collected;
* `PE`, a syntax tree for polynomial expressions, and `PE.norm : PE → Poly`;
* `PE.eval : PE → (ℕ → ℝ) → ℝ`, and the soundness theorem
  `Poly.eval (e.norm) ρ = e.eval ρ`.

All the arithmetic happens in `ℤ` and `ℕ`, where Lean's kernel has GMP fast
paths; only the final soundness step touches `ℝ`, through what is essentially an
evaluation ring hom.  A certificate then never appears in the source: the small
product form is written as a `PE`, `norm` computes its expansion inside Lean,
and positivity is a decidable check on the resulting coefficient list.

See `NOTES.md` §7f‴. -/

namespace BSCAveraging.Reflect

open List

/-! ## Monomials -/

/-- A monomial in seven variables: the exponent of each. -/
structure M7 where
  e0 : ℕ
  e1 : ℕ
  e2 : ℕ
  e3 : ℕ
  e4 : ℕ
  e5 : ℕ
  e6 : ℕ
deriving DecidableEq, Repr, Inhabited

/-- The unit monomial. -/
def M7.one : M7 := ⟨0, 0, 0, 0, 0, 0, 0⟩

/-- Monomials multiply by adding exponents. -/
def M7.mul (x y : M7) : M7 :=
  ⟨x.e0 + y.e0, x.e1 + y.e1, x.e2 + y.e2, x.e3 + y.e3, x.e4 + y.e4, x.e5 + y.e5,
    x.e6 + y.e6⟩

/-- The variable `xᵢ`. -/
def M7.var (i : Fin 7) : M7 :=
  ⟨if i = 0 then 1 else 0, if i = 1 then 1 else 0, if i = 2 then 1 else 0,
    if i = 3 then 1 else 0, if i = 4 then 1 else 0, if i = 5 then 1 else 0,
    if i = 6 then 1 else 0⟩

/-- Value of a monomial at an assignment. -/
def M7.eval (x : M7) (ρ : Fin 7 → ℝ) : ℝ :=
  ρ 0 ^ x.e0 * (ρ 1 ^ x.e1 * (ρ 2 ^ x.e2 * (ρ 3 ^ x.e3 * (ρ 4 ^ x.e4 *
    (ρ 5 ^ x.e5 * ρ 6 ^ x.e6)))))

@[simp] theorem M7.eval_var (i : Fin 7) (ρ : Fin 7 → ℝ) : (M7.var i).eval ρ = ρ i := by
  fin_cases i <;> simp [M7.var, M7.eval]

@[simp] theorem M7.eval_one (ρ : Fin 7 → ℝ) : M7.one.eval ρ = 1 := by
  simp [M7.eval, M7.one]

theorem M7.eval_mul (x y : M7) (ρ : Fin 7 → ℝ) :
    (x.mul y).eval ρ = x.eval ρ * y.eval ρ := by
  simp only [M7.eval, M7.mul, pow_add]
  ring

/-- A monomial is nonnegative when every variable is. -/
theorem M7.eval_nonneg {ρ : Fin 7 → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (x : M7) : 0 ≤ x.eval ρ := by
  simp only [M7.eval]
  exact mul_nonneg (pow_nonneg (hρ 0) _) (mul_nonneg (pow_nonneg (hρ 1) _)
    (mul_nonneg (pow_nonneg (hρ 2) _) (mul_nonneg (pow_nonneg (hρ 3) _)
      (mul_nonneg (pow_nonneg (hρ 4) _) (mul_nonneg (pow_nonneg (hρ 5) _)
        (pow_nonneg (hρ 6) _))))))

/-! ## Polynomials as data

No sortedness or collectedness is assumed: `Poly.eval` is just the sum of the
terms, so `+` is list append and `*` is the pairwise product. -/

/-- A polynomial: a list of terms, each an exponent record with an integer
coefficient.  Duplicated monomials are allowed. -/
abbrev Poly := List (M7 × ℤ)

/-- Value of a polynomial at an assignment. -/
def Poly.eval (p : Poly) (ρ : Fin 7 → ℝ) : ℝ :=
  (p.map (fun t => (t.2 : ℝ) * t.1.eval ρ)).sum

@[simp] theorem Poly.eval_nil (ρ : Fin 7 → ℝ) : Poly.eval [] ρ = 0 := rfl

@[simp] theorem Poly.eval_cons (t : M7 × ℤ) (p : Poly) (ρ : Fin 7 → ℝ) :
    Poly.eval (t :: p) ρ = (t.2 : ℝ) * t.1.eval ρ + Poly.eval p ρ := rfl

theorem Poly.eval_append (p q : Poly) (ρ : Fin 7 → ℝ) :
    Poly.eval (p ++ q) ρ = Poly.eval p ρ + Poly.eval q ρ := by
  induction p with
  | nil => simp
  | cons t p ih => simp [Poly.eval_cons, ih]; ring

/-- Scale a polynomial by a single term. -/
def Poly.scale (m : M7) (c : ℤ) (p : Poly) : Poly :=
  p.map (fun t => (m.mul t.1, c * t.2))

theorem Poly.eval_scale (m : M7) (c : ℤ) (p : Poly) (ρ : Fin 7 → ℝ) :
    Poly.eval (Poly.scale m c p) ρ = (c : ℝ) * m.eval ρ * Poly.eval p ρ := by
  induction p with
  | nil => simp [Poly.scale]
  | cons t p ih =>
    simp only [Poly.scale, List.map_cons, Poly.eval_cons, M7.eval_mul, Int.cast_mul] at *
    rw [ih]
    ring

/-- Product of polynomials: all pairwise products of terms. -/
def Poly.mul (p q : Poly) : Poly :=
  p.flatMap (fun t => Poly.scale t.1 t.2 q)

theorem Poly.eval_mul (p q : Poly) (ρ : Fin 7 → ℝ) :
    Poly.eval (Poly.mul p q) ρ = Poly.eval p ρ * Poly.eval q ρ := by
  induction p with
  | nil => simp [Poly.mul]
  | cons t p ih =>
    simp only [Poly.mul, List.flatMap_cons] at *
    rw [Poly.eval_append, Poly.eval_scale, ih, Poly.eval_cons]
    ring

/-- Powers, by iteration. -/
def Poly.pow (p : Poly) : ℕ → Poly
  | 0 => [(M7.one, 1)]
  | n + 1 => Poly.mul p (Poly.pow p n)


/-- Negation. -/
def Poly.neg (p : Poly) : Poly := p.map (fun t => (t.1, -t.2))

theorem Poly.eval_neg (p : Poly) (ρ : Fin 7 → ℝ) :
    Poly.eval (Poly.neg p) ρ = -Poly.eval p ρ := by
  induction p with
  | nil => simp [Poly.neg]
  | cons t p ih => simp only [Poly.neg, List.map_cons, Poly.eval_cons] at *; rw [ih]; push_cast; ring


/-! ## Collection

`Poly.mul` multiplies out pairwise, so without collection the term count is the
*product* of the input counts and the expansion explodes.  `Poly.collect` sorts
by a packed key and merges adjacent equal monomials.  Soundness needs nothing
about the sort order — permutation invariance of a list sum plus soundness of
adjacent merging — so the key need not be injective, and the fuel version below
is safe even if the fuel runs out (it just returns the list unchanged). -/

/-- A packing of the exponents, used only to sort. -/
def M7.key (m : M7) : ℕ :=
  m.e0 + 64 * (m.e1 + 64 * (m.e2 + 64 * (m.e3 + 64 * (m.e4 + 64 * (m.e5 + 64 * m.e6)))))

/-- Merge adjacent equal monomials, dropping zero coefficients. -/
def Poly.mergeAdj : ℕ → Poly → Poly
  | 0, p => p
  | _ + 1, [] => []
  | _ + 1, [t] => if t.2 = 0 then [] else [t]
  | n + 1, t :: u :: rest =>
      if t.1 = u.1 then Poly.mergeAdj n ((t.1, t.2 + u.2) :: rest)
      else if t.2 = 0 then Poly.mergeAdj n (u :: rest)
      else t :: Poly.mergeAdj n (u :: rest)

theorem Poly.eval_mergeAdj (ρ : Fin 7 → ℝ) :
    ∀ (n : ℕ) (p : Poly), Poly.eval (Poly.mergeAdj n p) ρ = Poly.eval p ρ
  | 0, p => rfl
  | _ + 1, [] => rfl
  | _ + 1, [t] => by
      by_cases h : t.2 = 0 <;> simp [Poly.mergeAdj, h, Poly.eval]
  | n + 1, t :: u :: rest => by
      by_cases h : t.1 = u.1
      · simp only [Poly.mergeAdj, h, if_pos]
        rw [Poly.eval_mergeAdj ρ n]
        simp only [Poly.eval_cons, h]
        push_cast
        ring
      · by_cases h2 : t.2 = 0
        · simp only [Poly.mergeAdj, h, if_neg, h2, if_pos, not_false_iff]
          rw [Poly.eval_mergeAdj ρ n]
          simp [Poly.eval_cons, h2]
        · simp only [Poly.mergeAdj, h, h2, if_neg, not_false_iff]
          rw [Poly.eval_cons, Poly.eval_mergeAdj ρ n]
          rfl

theorem Poly.eval_perm {p q : Poly} (h : p.Perm q) (ρ : Fin 7 → ℝ) :
    Poly.eval p ρ = Poly.eval q ρ := by
  unfold Poly.eval
  exact (h.map _).sum_eq

/-! ### A structural merge sort

`List.mergeSort` is defined by well-founded recursion and therefore does **not
reduce in the Lean kernel** — with it, even a two-monomial product gets stuck
under `decide`.  The sort below is structural, driven by an explicit fuel
argument, and its soundness is proved directly on the value rather than through
a permutation: `Poly.eval` is a sum, so all that is needed is that merging adds
and splitting splits. -/

/-- Merge two key-sorted polynomials, tail-recursively: the output is
accumulated in reverse and flushed with `List.reverseAux`.  A non-tail-recursive
merge overflows the compiled stack on the `68544`-entry intermediates of
`KernelCertFast.lean`.  `n` is fuel; `p.length + q.length` suffices. -/
def Poly.mergeAux : ℕ → Poly → Poly → Poly → Poly
  | 0, acc, p, q => acc.reverseAux (p ++ q)
  | _ + 1, acc, [], q => acc.reverseAux q
  | _ + 1, acc, p, [] => acc.reverseAux p
  | n + 1, acc, x :: p, y :: q =>
      if x.1.key ≤ y.1.key then Poly.mergeAux n (x :: acc) p (y :: q)
      else Poly.mergeAux n (y :: acc) (x :: p) q

def Poly.merge (n : ℕ) (p q : Poly) : Poly := Poly.mergeAux n [] p q

theorem Poly.eval_reverse (p : Poly) (ρ : Fin 7 → ℝ) :
    Poly.eval p.reverse ρ = Poly.eval p ρ :=
  Poly.eval_perm (List.reverse_perm p) ρ

theorem Poly.eval_reverseAux (acc p : Poly) (ρ : Fin 7 → ℝ) :
    Poly.eval (acc.reverseAux p) ρ = Poly.eval acc ρ + Poly.eval p ρ := by
  rw [List.reverseAux_eq, Poly.eval_append, Poly.eval_reverse]

theorem Poly.eval_mergeAux (ρ : Fin 7 → ℝ) :
    ∀ (n : ℕ) (acc p q : Poly),
      Poly.eval (Poly.mergeAux n acc p q) ρ
        = Poly.eval acc ρ + (Poly.eval p ρ + Poly.eval q ρ)
  | 0, acc, p, q => by
      show Poly.eval (acc.reverseAux (p ++ q)) ρ = _
      rw [Poly.eval_reverseAux, Poly.eval_append]
  | _ + 1, acc, [], q => by
      show Poly.eval (acc.reverseAux q) ρ = _
      rw [Poly.eval_reverseAux]; simp
  | _ + 1, acc, x :: p, [] => by
      show Poly.eval (acc.reverseAux (x :: p)) ρ = _
      rw [Poly.eval_reverseAux]; simp
  | n + 1, acc, x :: p, y :: q => by
      simp only [Poly.mergeAux]
      split
      · rw [Poly.eval_mergeAux ρ n (x :: acc) p (y :: q)]
        simp only [Poly.eval_cons]; ring
      · rw [Poly.eval_mergeAux ρ n (y :: acc) (x :: p) q]
        simp only [Poly.eval_cons]; ring

theorem Poly.eval_merge (ρ : Fin 7 → ℝ) (n : ℕ) (p q : Poly) :
    Poly.eval (Poly.merge n p q) ρ = Poly.eval p ρ + Poly.eval q ρ := by
  rw [Poly.merge, Poly.eval_mergeAux]
  simp

/-- Merge sort by key, structural in the fuel `n`. -/
def Poly.msort : ℕ → Poly → Poly
  | 0, p => p
  | n + 1, p =>
      match p with
      | [] => []
      | [x] => [x]
      | p =>
        let k := p.length / 2
        Poly.merge p.length (Poly.msort n (p.take k)) (Poly.msort n (p.drop k))

theorem Poly.eval_msort (ρ : Fin 7 → ℝ) :
    ∀ (n : ℕ) (p : Poly), Poly.eval (Poly.msort n p) ρ = Poly.eval p ρ
  | 0, p => rfl
  | n + 1, p => by
      match p with
      | [] => rfl
      | [x] => rfl
      | a :: b :: cs =>
        show Poly.eval (Poly.merge _ (Poly.msort n (List.take _ (a :: b :: cs)))
          (Poly.msort n (List.drop _ (a :: b :: cs)))) ρ = _
        rw [Poly.eval_merge, Poly.eval_msort ρ n, Poly.eval_msort ρ n,
          ← Poly.eval_append, List.take_append_drop]

/-- Sort by key, then merge adjacent equal monomials.

The sort is `Poly.msort`, not `List.mergeSort`: the latter is defined by
well-founded recursion and does not reduce in the Lean kernel at all, so with it
`PE.norm` is opaque to `decide`.  `Poly.msort` is structural, and its merge is
tail-recursive — on the `68544`-entry intermediate lists of
`KernelCertFast.lean` a non-tail-recursive merge overflows the *compiled*
stack. -/
def Poly.collect (p : Poly) : Poly :=
  Poly.mergeAdj p.length (Poly.msort p.length p)

theorem Poly.eval_collect (p : Poly) (ρ : Fin 7 → ℝ) :
    Poly.eval (Poly.collect p) ρ = Poly.eval p ρ := by
  rw [Poly.collect, Poly.eval_mergeAdj, Poly.eval_msort]

/-- Merge two collected polynomials, collecting again. -/
def Poly.addC (p q : Poly) : Poly :=
  Poly.mergeAdj (p.length + q.length) (Poly.merge (p.length + q.length) p q)

theorem Poly.eval_addC (p q : Poly) (ρ : Fin 7 → ℝ) :
    Poly.eval (Poly.addC p q) ρ = Poly.eval p ρ + Poly.eval q ρ := by
  rw [Poly.addC, Poly.eval_mergeAdj, Poly.eval_merge]

/-- **Collecting product.**  Each scaled copy of `q` is merged into an already
collected accumulator, so no list larger than the output is ever built.  The
obvious alternative, `Poly.collect (Poly.mul p q)`, materialises the whole
unsorted product first — `68544` entries at the worst step of
`KernelCertFast.lean` — and the kernel retains every one of them. -/
def Poly.cmul : Poly → Poly → Poly
  | [], _ => []
  | t :: p, q => Poly.addC (Poly.scale t.1 t.2 q) (Poly.cmul p q)

theorem Poly.eval_cmul (p q : Poly) (ρ : Fin 7 → ℝ) :
    Poly.eval (Poly.cmul p q) ρ = Poly.eval p ρ * Poly.eval q ρ := by
  induction p with
  | nil => simp [Poly.cmul]
  | cons t p ih =>
    rw [Poly.cmul, Poly.eval_addC, Poly.eval_scale, ih, Poly.eval_cons]
    ring

/-- Collecting power. -/
def Poly.cpow (p : Poly) : ℕ → Poly
  | 0 => [(M7.one, 1)]
  | n + 1 => Poly.cmul p (Poly.cpow p n)

theorem Poly.eval_cpow (p : Poly) (n : ℕ) (ρ : Fin 7 → ℝ) :
    Poly.eval (Poly.cpow p n) ρ = (Poly.eval p ρ) ^ n := by
  induction n with
  | zero => simp [Poly.cpow, Poly.eval]
  | succ n ih => rw [Poly.cpow, Poly.eval_cmul, ih, pow_succ]; ring

/-! ## Expressions and their normal form -/

/-- A polynomial expression over seven variables. -/
inductive PE where
  | var : Fin 7 → PE
  | int : ℤ → PE
  | add : PE → PE → PE
  | sub : PE → PE → PE
  | mul : PE → PE → PE
  | pow : PE → ℕ → PE
deriving Repr, Inhabited

/-- Value of an expression. -/
def PE.eval (ρ : Fin 7 → ℝ) : PE → ℝ
  | .var i => ρ i
  | .int n => (n : ℝ)
  | .add a b => a.eval ρ + b.eval ρ
  | .sub a b => a.eval ρ - b.eval ρ
  | .mul a b => a.eval ρ * b.eval ρ
  | .pow a n => (a.eval ρ) ^ n

/-- Expansion of an expression into a term list. -/
def PE.norm : PE → Poly
  | .var i => [(M7.var i, 1)]
  | .int n => if n = 0 then [] else [(M7.one, n)]
  | .add a b => Poly.collect (a.norm ++ b.norm)
  | .sub a b => Poly.collect (a.norm ++ Poly.neg b.norm)
  | .mul a b => Poly.cmul a.norm b.norm
  | .pow a n => Poly.cpow a.norm n

/-- **Soundness**: expansion preserves the value.  This is the only step that
touches `ℝ`; everything else is `ℕ`/`ℤ` arithmetic on data. -/
theorem PE.eval_norm (ρ : Fin 7 → ℝ) : ∀ e : PE, Poly.eval e.norm ρ = e.eval ρ
  | .var i => by simp [PE.norm, PE.eval, Poly.eval]
  | .int n => by
      by_cases h : n = 0 <;> simp [PE.norm, PE.eval, Poly.eval, h]
  | .add a b => by
      simp only [PE.norm, PE.eval, Poly.eval_collect, Poly.eval_append, PE.eval_norm ρ a,
        PE.eval_norm ρ b]
  | .sub a b => by
      simp only [PE.norm, PE.eval, Poly.eval_collect, Poly.eval_append, Poly.eval_neg,
        PE.eval_norm ρ a, PE.eval_norm ρ b]
      ring
  | .mul a b => by
      simp only [PE.norm, PE.eval, Poly.eval_cmul, PE.eval_norm ρ a, PE.eval_norm ρ b]
  | .pow a n => by
      simp only [PE.norm, PE.eval, Poly.eval_cpow, PE.eval_norm ρ a]

/-! ## Positivity from a nonnegative coefficient list -/

/-- A polynomial with nonnegative coefficients is nonnegative on the
nonnegative orthant. -/
theorem Poly.eval_nonneg {ρ : Fin 7 → ℝ} (hρ : ∀ i, 0 ≤ ρ i) :
    ∀ p : Poly, (∀ t ∈ p, 0 ≤ t.2) → 0 ≤ Poly.eval p ρ
  | [], _ => by simp
  | t :: p, h => by
    rw [Poly.eval_cons]
    have h1 : 0 ≤ (t.2 : ℝ) := by exact_mod_cast h t (by simp)
    exact add_nonneg (mul_nonneg h1 (M7.eval_nonneg hρ _))
      (Poly.eval_nonneg hρ p (fun s hs => h s (by simp [hs])))

/-- The decidable check that a term list has only nonnegative coefficients. -/
def Poly.allNonneg (p : Poly) : Bool := p.all (fun t => 0 ≤ t.2)

theorem Poly.allNonneg_iff (p : Poly) : p.allNonneg = true ↔ ∀ t ∈ p, 0 ≤ t.2 := by
  simp [Poly.allNonneg, List.all_eq_true]

/-- **The reflection principle used by the certificate.**  If the expansion of
`e` has only nonnegative coefficients, then `e` is nonnegative wherever all the
variables are.  The hypothesis is a computation on `ℤ` data — no `ring`, and no
large term in the source. -/
theorem PE.eval_nonneg_of_norm {ρ : Fin 7 → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (e : PE)
    (h : e.norm.allNonneg = true) : 0 ≤ e.eval ρ := by
  rw [← PE.eval_norm ρ e]
  exact Poly.eval_nonneg hρ _ ((Poly.allNonneg_iff _).mp h)

end BSCAveraging.Reflect
