import BSCAveraging.Reflect
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! # The kernel lemma, kernel-checked

`KernelCertFast.lean` proves the same positivity through `native_decide`: it
expands the cleared kernel in the ordered bi-simplex coordinates, 24129
monomials, at a cost of `6.8·10⁶` monomial products — far beyond kernel
reduction.  This file replaces that certificate with one a hundred times
cheaper, checked by the **kernel** (`NOTES.md` §7j).

Three changes produce it.  With `y = θ/(1−θ)`, `A = 1−u`, `B = 1−v` and
`C = 1−uv = A+B−AB`, the three profiles linearise,

```
f_i = 1/F_i ,  g_i = 1/G_i ,  r_i = F_i/H_i ,
F_i = 1+y_iA ,  G_i = 1+y_iC ,  H_i = 1+y_iB ,
```

and the cleared kernel — the kernel sum times `∏F_i∏G_i∏H_i²` — collapses to

```
Σ_i F_jF_k · G_i(G_j+G_k) · H_jH_k · (F_i²H_jH_k − F_jF_kH_i²) .
```

Ordering `y₁ ≤ y₂ ≤ y₃` as `z₁, z₁+z₂, z₁+z₂+z₃` costs three variables instead
of four.  For the `u,v` part, `a = 1−u` and `b = u−v` give a triangle on which
the expansion still has negative coefficients; blowing up its corner
`a = b = 0` (that is `u = v = 1`, where `r ≡ 1`) by

```
a = s·w' ,   b = s·w ,      s = 1−v ,  w = u−v ,  w' = 1−u ,  s' = v
```

turns the triangle into a product of two segments, and there the expansion is
coefficient-nonnegative outright — no Pólya elevation.  Writing the constants
of `F, G, H` as the corresponding powers of `s+s'` and `w+w'` makes the tree
below bihomogeneous, and its expansion has **4000 monomials, every coefficient
a positive integer**, at `2.1·10⁵` products. -/

set_option maxRecDepth 400000
set_option maxHeartbeats 2000000

namespace BSCAveraging.Reflect


open PE

/-- `s + s'`, the first unit. -/
def bS1 : PE := .add (.var 3) (.var 4)
/-- `w + w'`, the second unit. -/
def bW1 : PE := .add (.var 5) (.var 6)

/-- The ordered `y`s. -/
def bY : Fin 3 → PE
  | 0 => .var 0
  | 1 => .add (.var 0) (.var 1)
  | _ => .add (.add (.var 0) (.var 1)) (.var 2)

/-- `A = 1−u = s·w'`. -/
def bA : PE := .mul (.var 3) (.var 6)
/-- `B = 1−v = s`. -/
def bB : PE := .var 3
/-- `C = 1−uv = A + B − AB`, homogenised to bidegree `(2,1)`. -/
def bC : PE :=
  .sub (.add (.mul bS1 bA) (.mul (.mul bS1 bW1) bB)) (.mul bA bB)

def bF (i : Fin 3) : PE := .add (.mul bS1 bW1) (.mul (bY i) bA)
def bH (i : Fin 3) : PE := .add bS1 (.mul (bY i) bB)
def bG (i : Fin 3) : PE := .add (.mul (.mul bS1 bS1) bW1) (.mul (bY i) bC)

def bterm (i j k : Fin 3) : PE :=
  .mul (.mul (.mul (bF j) (bF k)) (.mul (bG i) (.add (bG j) (bG k))))
       (.mul (.mul (bH j) (bH k))
             (.sub (.mul (.mul (.pow (bF i) 2) (bH j)) (bH k))
                   (.mul (.mul (bF j) (bF k)) (.pow (bH i) 2))))

/-- The cleared kernel over `(z₁,z₂,z₃,s,s',w,w')`. -/
def kerBPE : PE := .add (.add (bterm 0 1 2) (bterm 1 2 0)) (bterm 2 0 1)

/-- **The certificate.**  Every coefficient of the expansion of `kerBPE` is
nonnegative: 4000 monomials, `2.1·10⁵` monomial products — a hundredfold less
work than the `24129`-monomial expansion of `KernelCertFast.lean`.

It is still checked here by `native_decide`, and that is the honest state of
this file: the reduction in *work* did not turn out to be enough to move the
check into the kernel.  Measured, with the structural sort of `Reflect.lean` in
place (`List.mergeSort` is well-founded and does not reduce in the kernel at
all, so that replacement was a prerequisite):

* kernel throughput on this kind of symbolic list arithmetic is `~10⁴`
  elementary steps per second — a degree-12 trinomial power, 91 monomials,
  takes about a second;
* the expansion needs `2.1·10⁵` products and, with the generic
  `Poly.mul`-then-sort, about `3·10⁶` further sort steps;
* worse, the kernel *retains every intermediate*: `Poly.mul` builds the whole
  unsorted product list before collecting, and the largest here is `68544`
  entries.  A `decide +kernel` run peaked at **89 GB** and timed out at ten
  minutes.

**The merge-based route was since implemented, and it does not fix this.**
`Poly.cmul` (`Reflect.lean`) is exactly the multiplication described above — it
merges each scaled copy into an already collected accumulator, so no list larger
than the output is ever built — and `PE.norm` uses it.  The `89 GB` figure above
predates it and no longer describes the code.  Re-measured with `cmul` in place,
on a 94 GB machine: resident memory grows **linearly at about 80 MB/s with no
plateau**, reaching `46.5 GB` after some nine minutes without finishing.
Extrapolating the `2.4·10⁷`-step estimate at that rate puts completion near
`200 GB`.

So the retention is not the intermediate product list; it is the kernel's own
reduction cache, which holds every step of a long computation.  No change to the
`Poly` representation addresses that, and this route is closed.

One route remains, untried: drop reflection for this step.  With only 4000 terms
the `ring` route that was hopeless at 24129 terms (>3 h, 21 GB) may now fit,
since elaboration cost scales with the term count.

Note also that even a kernel-checked `kerBPE_allNonneg` would not by itself make
`conjecture1_p0_holds` axiom-clean: this file stops at `FB_pos`/`GB_pos`/`HB_pos`
and never derives an analogue of `kerQR_nonneg`, so `saddle_iii` still reaches
the `native_decide` of `KernelCertFast.lean`. -/
theorem kerBPE_allNonneg : kerBPE.norm.allNonneg = true := by native_decide

/-! ### The substitution -/

/-- `F̂ = 1 + y(1−u)`. -/
def FB (y u : ℝ) : ℝ := 1 + y * (1 - u)
/-- `Ĝ = 1 + y(1−uv)`. -/
def GB (y u v : ℝ) : ℝ := 1 + y * (1 - u * v)
/-- `Ĥ = 1 + y(1−v)`. -/
def HB (y v : ℝ) : ℝ := 1 + y * (1 - v)

/-- One cyclic term of the cleared kernel, in the hatted letters. -/
def termB (y₁ y₂ y₃ u v : ℝ) : ℝ :=
  (FB y₂ u * FB y₃ u) * (GB y₁ u v * (GB y₂ u v + GB y₃ u v))
    * ((HB y₂ v * HB y₃ v)
        * ((FB y₁ u ^ 2 * HB y₂ v) * HB y₃ v - (FB y₂ u * FB y₃ u) * HB y₁ v ^ 2))

/-- **The tree, at the substituted point.**  Both units evaluate to `1`, so no
scaling factor survives and the value is exactly the cleared kernel in the
hatted letters. -/
theorem eval_kerBPE_subst (y₁ y₂ y₃ u v : ℝ) (hv : (1 : ℝ) - v ≠ 0) :
    PE.eval ![y₁, y₂ - y₁, y₃ - y₂, 1 - v, v, (u - v) / (1 - v), (1 - u) / (1 - v)] kerBPE
      = termB y₁ y₂ y₃ u v + termB y₂ y₃ y₁ u v + termB y₃ y₁ y₂ u v := by
  have hS : (1 - v) + v = 1 := by ring
  have hW : (u - v) / (1 - v) + (1 - u) / (1 - v) = 1 := by
    rw [← add_div, show u - v + (1 - u) = 1 - v by ring]
    exact div_self hv
  have hA : (1 - v) * ((1 - u) / (1 - v)) = 1 - u := by
    rw [mul_comm, div_mul_cancel₀ _ hv]
  have hy2 : y₁ + (y₂ - y₁) = y₂ := by ring
  have hy3 : y₂ + (y₃ - y₂) = y₃ := by ring
  simp only [kerBPE, bterm, bF, bG, bH, bA, bB, bC, bS1, bW1, bY, PE.eval,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    hS, hW, hA, hy2, hy3, one_mul, mul_one]
  simp only [termB, FB, GB, HB]
  ring_nf

/-! ### From the hatted letters to `kernelSum` -/

/-- `y = θ/(1−θ)`. -/
noncomputable def yOf (θ : ℝ) : ℝ := θ / (1 - θ)

lemma yOf_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) : 0 ≤ yOf θ := by
  rw [yOf]; apply div_nonneg h0; linarith

lemma yOf_mono {θ₁ θ₂ : ℝ} (h0 : 0 ≤ θ₁) (h12 : θ₁ ≤ θ₂) (h1 : θ₂ < 1) :
    yOf θ₁ ≤ yOf θ₂ := by
  have d₂ : (0:ℝ) < 1 - θ₂ := by linarith
  have d₁ : (0:ℝ) < 1 - θ₁ := by linarith
  rw [yOf, yOf, div_le_div_iff₀ d₁ d₂]
  nlinarith

lemma FB_yOf {θ u : ℝ} (hθ : (1:ℝ) - θ ≠ 0) : FB (yOf θ) u = (1 - θ * u) / (1 - θ) := by
  rw [FB, yOf]; field_simp; ring

lemma GB_yOf {θ u v : ℝ} (hθ : (1:ℝ) - θ ≠ 0) :
    GB (yOf θ) u v = (1 - θ * (u * v)) / (1 - θ) := by
  rw [GB, yOf]; field_simp; ring

lemma HB_yOf {θ v : ℝ} (hθ : (1:ℝ) - θ ≠ 0) : HB (yOf θ) v = (1 - θ * v) / (1 - θ) := by
  rw [HB, yOf]; field_simp; ring

lemma one_div_FB {θ u : ℝ} (hθ : (1:ℝ) - θ ≠ 0) (hu : (1:ℝ) - θ * u ≠ 0) :
    1 / FB (yOf θ) u = (1 - θ) / (1 - θ * u) := by
  rw [FB_yOf hθ, one_div_div]

lemma one_div_GB {θ u v : ℝ} (hθ : (1:ℝ) - θ ≠ 0) (hu : (1:ℝ) - θ * (u * v) ≠ 0) :
    1 / GB (yOf θ) u v = (1 - θ) / (1 - θ * (u * v)) := by
  rw [GB_yOf hθ, one_div_div]

lemma FB_div_HB {θ u v : ℝ} (hθ : (1:ℝ) - θ ≠ 0) (hv : (1:ℝ) - θ * v ≠ 0) :
    FB (yOf θ) u / HB (yOf θ) v = (1 - θ * u) / (1 - θ * v) := by
  rw [FB_yOf hθ, HB_yOf hθ]
  rw [div_div_div_eq]
  field_simp

lemma FB_pos {θ u : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    0 < FB (yOf θ) u := by
  have h : (1:ℝ) - θ ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  rw [FB_yOf h]
  apply div_pos (by nlinarith) (by linarith)

lemma GB_pos {θ u v : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (huv0 : 0 ≤ u * v) (huv1 : u * v < 1) :
    0 < GB (yOf θ) u v := by
  have h : (1:ℝ) - θ ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  rw [GB_yOf h]
  apply div_pos (by nlinarith) (by linarith)

lemma HB_pos {θ v : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    0 < HB (yOf θ) v := by
  have h : (1:ℝ) - θ ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  rw [HB_yOf h]
  apply div_pos (by nlinarith) (by linarith)

end BSCAveraging.Reflect
