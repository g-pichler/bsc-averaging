import BSCAveraging.KernelCertFast

/-! # The kernel lemma's certificate, checked by the kernel in one big integer

`KernelCertFast.lean` proves `kerQPE_allNonneg` — every one of the 24129
coefficients of the cleared, ordered kernel is a positive integer — by
`native_decide`, the only axiom beyond `propext`, `Classical.choice`,
`Quot.sound` in the chain for Conjecture 1.  Every attempt to move that check
into the kernel (`NOTES.md` §7i, §7j, §7j′) did *symbolic* polynomial
arithmetic there and died of retained intermediates: 30–89 GB for the
expansion, >43 GB for `ring`, and the cyclic sum cannot be split.

This file does no expansion.  It evaluates the syntax tree `kerQPE` at **one
integer point** and reads the coefficients off the digits — **Kronecker
substitution** — using the one thing the kernel does fast: GMP arithmetic on
`Nat` literals (`Nat.pow`, `mul`, `sub`, `div`, `mod`, `land`, `ble` are all
accelerated; `pow` needs the exponent below `2^24`).

**The point.**  Dehomogenise, `t₄ = s₃ = 1`, and put

```
(t₁,t₂,t₃,t₄,s₁,s₂,s₃) = (B, B^13, B^169, 1, B^2197, B^28561, 1),   B = 2^64.
```

`kerQPE` is bihomogeneous of bidegree `(12,12)`, so every monomial has
exponents `≤ 12` in each of `t₁,t₂,t₃,s₁,s₂`, and the exponent vector maps
injectively to the slot `e₁ + 13e₂ + 169e₃ + 2197e₅ + 28561e₆ < 371293`.  The
value `N` is therefore the coefficient vector written in base `B`, one
coefficient per 64-bit digit — *provided* no digit overflows or borrows.  The
structural L1 bound of the tree (sum of absolute coefficients, bounded by
products and sums of the factors' L1 norms without expanding) is
`1.67·10¹⁵ < 2^51 < B/2`, so every true coefficient lies in `(−B/2, B/2)`, and
by uniqueness of the balanced base-`B` representation

> all coefficients `≥ 0`  ⟺  every 64-bit digit of `N` has top bit `0`
> ⟺  `N.land mask = 0`,  `mask = 2^63 · (B^371293 − 1)/(B − 1)`.

**Measured** (v4.32.0, `lake env lean` on this file): the three `decide +kernel`
below take **3.3 s wall including the 2.7 s import, +230 MB** over the import's
1.66 GB — against 138 s for the `native_decide` of `KernelCertFast.lean`.  A
divide-and-conquer digit scan (`blocksOk` below, check not included in the
build) does the same job in 72 s and 14 GB, the kernel retaining the recursion's
intermediates.  Negative control: lowering the leaf threshold to `2^26` — below
the largest coefficient, `74 216 288` — makes the check fail, so the digits are
really being read.

**What this file does not do.**  The three theorems are the *computation*; the
connection to `kerQPE.norm.allNonneg` is not written.  It needs, none of it
research (`NOTES.md` §7k):

* `evalZ` agrees with `PE.eval` under the cast `ℤ → ℝ`, hence with
  `Poly.eval ∘ PE.norm` by `PE.eval_norm`;
* structural `PE.l1bound` and `PE.bideg`, with lemmas bounding the monomials
  and coefficients of `PE.norm` through `collect`, `cmul`, `cpow` — for
  `kerQPE` they compute to `1667733694599168` and `(12,12)`;
* the number theory: balanced base-`B` uniqueness, and
  `N.land mask = 0 → ∀ e, (N / B^e) % B < 2^63` (`Nat.testBit_land`,
  `Nat.geomSum_eq` for the closed form of `mask`).

With those, `kerQPE_allNonneg` follows from `digits_mask` and the last
`native_decide` leaves the development. -/

namespace BSCAveraging.Reflect.Kron

open BSCAveraging.Reflect

def B : ℕ := 2^64

/-- The Kronecker point, dehomogenised (`t₄ = s₃ = 1`): 13 slots per variable. -/
def kron : Fin 7 → ℤ :=
  ![((B : ℕ) : ℤ), ((B^13 : ℕ) : ℤ), ((B^169 : ℕ) : ℤ), 1,
    ((B^2197 : ℕ) : ℤ), ((B^28561 : ℕ) : ℤ), 1]

/-- Integer evaluation of a syntax tree — the recursion of `PE.eval`, over `ℤ`. -/
def evalZ (ρ : Fin 7 → ℤ) : PE → ℤ
  | .var i => ρ i
  | .int n => n
  | .add a b => evalZ ρ a + evalZ ρ b
  | .sub a b => evalZ ρ a - evalZ ρ b
  | .mul a b => evalZ ρ a * evalZ ρ b
  | .pow a n => (evalZ ρ a) ^ n

/-- The cleared kernel at the Kronecker point: the coefficient vector in base `B`. -/
def N : ℤ := evalZ kron kerQPE
def NNat : ℕ := N.toNat

/-- One `1` in the top bit of each of the `371293` 64-bit digits. -/
def mask : ℕ := 2^63 * ((B^371293 - 1) / (B - 1))

/-- The product form evaluates to a non-negative integer … -/
theorem N_nonneg : 0 ≤ N := by decide +kernel
/-- … with no more than `371293` digits … -/
theorem N_lt : NNat < B ^ 371293 := by decide +kernel
/-- … every one of which is `< 2^63`.  **This is the certificate**, one `land`. -/
theorem digits_mask : NNat.land mask = 0 := by decide +kernel

/-- The same digit condition by divide and conquer on `div`/`mod` — elementary
to prove correct, but 72 s and 14 GB in the kernel; its instance on `NNat` is
therefore not part of the build. -/
def blocksOk : ℕ → ℕ → ℕ → Bool
  | 0, n, L => L ≤ 1 && n < 2^63
  | d+1, n, L =>
      if L ≤ 1 then n < 2^63 else
        let h := L / 2
        let p := B ^ h
        blocksOk d (n / p) (L - h) && blocksOk d (n % p) h

end BSCAveraging.Reflect.Kron
