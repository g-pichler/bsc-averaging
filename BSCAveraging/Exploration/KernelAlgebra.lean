import BSCAveraging.KernelAlgebra
import BSCAveraging.Exploration.PZeroSymm

/-! # `KernelAlgebra` — exploration companion

The declarations of `BSCAveraging.KernelAlgebra` that are **not** used by any of the
three theorems of `BSCAveraging.Basic`.  Section headers are copied from the
main file so the two read in parallel. -/

/-! # The `p = 0` diagonal reduction: the parts that are theorems

`NOTES.md` §7f reduces Conjecture 1 at `p = 0` to the *kernel lemma*, an explicit
rational inequality in five variables.  This file collects the pieces of that
analysis which are proofs rather than numerics.

* `artanh_edge` — the **boundary case of (iii)**: `β < artanh β·(1 − β²/3)` on
  `(0,1)`.  This is exactly what makes the leading coefficient of `Q̃` positive
  as `α → 0` with `β` fixed, so the boundary behaviour of (iii) is settled.  The
  difference vanishes at `0` and has derivative
  `(2β/3)·[β/(1−β²) − artanh β] > 0`, the bracket being `artanh_mul_lt`.
* `schur_decomposition` — the identity splitting the kernel lemma into a
  Chebyshev term and a manifestly nonnegative one.
* `cube_sum_ge_three_mul` — `r₁³+r₂³+r₃³ ≥ 3r₁r₂r₃`, which is the equal-weight
  case of the kernel lemma.
* `rFun_sub`, `fFun'_sub`, `fg_cross` — the difference identities showing every
  difference in the kernel lemma carries an explicit factor `(θ_l − θ_i)`.  They
  are why the kernel is divisible by `(θ_i−θ_l)²`, hence the shape of the
  certificate ansatz.

`KernelLemma` states the one inequality still open.  `NOTES.md` §7f records that
every diagonal-Handelman LP relaxation of it is infeasible — `Q` is negative off
the box `A ≤ 1` — so a genuine SOS with cross terms is needed.

See `NOTES.md` §7f. -/

open Real Set

namespace BSCAveraging

/-! ## The boundary case of (iii) -/

/-- The derivative of `z ↦ artanh z·(1 − z²/3) − z`, on `(−1,1)`. -/
lemma hasDerivAt_artanhEdge {z : ℝ} (hz0 : -1 < z) (hz1 : z < 1) :
    HasDerivAt (fun t : ℝ => artanh t * (1 - t ^ 2 / 3) - t)
      (2 * z / 3 * (z / (1 - z ^ 2) - artanh z)) z := by
  have hne : (1 : ℝ) - z ^ 2 ≠ 0 := by nlinarith
  have h1 : HasDerivAt artanh (1 / (1 - z ^ 2)) z := hasDerivAt_artanh hz0 hz1
  have h2 : HasDerivAt (fun t : ℝ => 1 - t ^ 2 / 3) (-(2 * z / 3)) z := by
    have := ((hasDerivAt_pow 2 z).div_const 3).const_sub 1
    simpa using this
  have h := (h1.mul h2).sub (hasDerivAt_id z)
  have heq : 1 / (1 - z ^ 2) * (1 - z ^ 2 / 3) + artanh z * -(2 * z / 3) - 1
      = 2 * z / 3 * (z / (1 - z ^ 2) - artanh z) := by
    field_simp
    ring
  rw [heq] at h
  exact h

/-- **The boundary case of the saddle inequality (iii)**:
`β < artanh β·(1 − β²/3)` for `β ∈ (0,1)`. -/
theorem artanh_edge {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    y < artanh y * (1 - y ^ 2 / 3) := by
  have key : 0 < artanh y * (1 - y ^ 2 / 3) - y := by
    refine pos_of_hasDerivAt_pos (fun t : ℝ => artanh t * (1 - t ^ 2 / 3) - t)
      (fun t : ℝ => 2 * t / 3 * (t / (1 - t ^ 2) - artanh t)) (by simp) ?_ ?_ ?_ hy0 hy1
    · exact fun z hz => hasDerivAt_artanhEdge (by linarith [hz.1]) hz.2
    · exact ((hasDerivAt_artanhEdge (by norm_num) (by norm_num)).continuousAt).continuousWithinAt
    · intro z hz
      have hpos : (0 : ℝ) < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
      have hbr : 0 < z / (1 - z ^ 2) - artanh z := by
        rw [sub_pos, lt_div_iff₀ hpos]
        have := artanh_mul_lt hz.1 hz.2
        linarith
      have hz0 : 0 < z := hz.1
      positivity
  linarith

/-! ## The Schur-type decomposition -/

/-- **The decomposition behind the kernel lemma.**  The Chebyshev part is the
first sum; the second is manifestly nonnegative when the `λ` are, and it is the
slack that pure association arguments lack. -/
theorem schur_decomposition (l₁ l₂ l₃ r₁ r₂ r₃ : ℝ) :
    l₁ * (r₁ ^ 2 - r₂ * r₃) + l₂ * (r₂ ^ 2 - r₁ * r₃) + l₃ * (r₃ ^ 2 - r₁ * r₂)
      = ((l₁ - l₂) * (r₁ ^ 2 - r₂ ^ 2) + (l₁ - l₃) * (r₁ ^ 2 - r₃ ^ 2)
          + (l₂ - l₃) * (r₂ ^ 2 - r₃ ^ 2)) / 2
        + (l₃ * (r₁ - r₂) ^ 2 + l₂ * (r₁ - r₃) ^ 2 + l₁ * (r₂ - r₃) ^ 2) / 2 := by
  ring

/-- The equal-weight case of the kernel lemma is AM–GM. -/
theorem cube_sum_ge_three_mul {r₁ r₂ r₃ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (h₃ : 0 ≤ r₃) :
    3 * (r₁ * r₂ * r₃) ≤ r₁ ^ 3 + r₂ ^ 3 + r₃ ^ 3 := by
  nlinarith [sq_nonneg (r₁ - r₂), sq_nonneg (r₂ - r₃), sq_nonneg (r₁ - r₃),
    sq_nonneg (r₁ + r₂ + r₃), add_nonneg (add_nonneg h₁ h₂) h₃,
    mul_nonneg h₁ h₂, mul_nonneg h₂ h₃, mul_nonneg h₁ h₃]

/-! ## The difference identities

Every difference appearing in the kernel lemma carries an explicit factor
`(θ_l − θ_i)`; this is why the kernel is divisible by `(θ_i − θ_l)²`. -/

section Differences

variable {θ₁ θ₂ u v : ℝ}

/-- `r(θ) = (1−θu)/(1−θv)`: the difference carries `(θ₂−θ₁)(u−v)`. -/
theorem rFun_sub (h₁ : 1 - θ₁ * v ≠ 0) (h₂ : 1 - θ₂ * v ≠ 0) :
    (1 - θ₁ * u) / (1 - θ₁ * v) - (1 - θ₂ * u) / (1 - θ₂ * v)
      = (θ₂ - θ₁) * (u - v) / ((1 - θ₁ * v) * (1 - θ₂ * v)) := by
  have h₁' : 1 - v * θ₁ ≠ 0 := by rw [mul_comm]; exact h₁
  have h₂' : 1 - v * θ₂ ≠ 0 := by rw [mul_comm]; exact h₂
  field_simp
  ring

/-- `f(θ) = (1−θ)/(1−θu)`: the difference carries `(θ₂−θ₁)(1−u)`. -/
theorem fFun'_sub (h₁ : 1 - θ₁ * u ≠ 0) (h₂ : 1 - θ₂ * u ≠ 0) :
    (1 - θ₁) / (1 - θ₁ * u) - (1 - θ₂) / (1 - θ₂ * u)
      = (θ₂ - θ₁) * (1 - u) / ((1 - θ₁ * u) * (1 - θ₂ * u)) := by
  have h₁' : 1 - u * θ₁ ≠ 0 := by rw [mul_comm]; exact h₁
  have h₂' : 1 - u * θ₂ ≠ 0 := by rw [mul_comm]; exact h₂
  field_simp
  ring

/-- The cross term `f₁g₂ − f₂g₁` with `g(θ) = (1−θ)/(1−θt)`: it carries
`(θ₁−θ₂)(u−t)`, and is the *negative* contribution in the kernel. -/
theorem fg_cross {t : ℝ} (ha₁ : 1 - θ₁ * u ≠ 0) (ha₂ : 1 - θ₂ * u ≠ 0)
    (hw₁ : 1 - θ₁ * t ≠ 0) (hw₂ : 1 - θ₂ * t ≠ 0) :
    (1 - θ₁) / (1 - θ₁ * u) * ((1 - θ₂) / (1 - θ₂ * t))
        - (1 - θ₂) / (1 - θ₂ * u) * ((1 - θ₁) / (1 - θ₁ * t))
      = (1 - θ₁) * (1 - θ₂) * ((θ₁ - θ₂) * (u - t))
          / ((1 - θ₁ * u) * (1 - θ₂ * u) * (1 - θ₁ * t) * (1 - θ₂ * t)) := by
  have ha₁' : 1 - u * θ₁ ≠ 0 := by rw [mul_comm]; exact ha₁
  have ha₂' : 1 - u * θ₂ ≠ 0 := by rw [mul_comm]; exact ha₂
  have hw₁' : 1 - t * θ₁ ≠ 0 := by rw [mul_comm]; exact hw₁
  have hw₂' : 1 - t * θ₂ ≠ 0 := by rw [mul_comm]; exact hw₂
  field_simp
  ring

end Differences


/-! ## Why the mixture route, and why no general argument can work -/

section GeometricDegeneracy

variable {θ u v : ℝ}

/-- **The kernel form annihilates every geometric law.**  For
`Ĝ_θ(z) = (1−θ)z/(1−θz)` the two products coincide term by term — this is the
degeneracy that makes the geometric-mixture representation the right one: the
cubic form has a vanishing diagonal, so only the off-diagonal kernel matters. -/
theorem geometric_kernel_zero (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) :
    (v * (1 - θ) / (1 - θ * v) ^ 2) * ((1 - u) / (1 - θ * u))
        * ((1 - θ) * (u - u * v) / ((1 - θ * u) * (1 - θ * (u * v))))
      - (u * (1 - θ) / (1 - θ * u) ^ 2) * ((1 - v) / (1 - θ * v))
        * ((1 - θ) * (v - u * v) / ((1 - θ * v) * (1 - θ * (u * v)))) = 0 := by
  have huv1 : u * v < 1 := by nlinarith
  have hbu : θ * u ≤ θ := by nlinarith [mul_nonneg hθ0 (sub_pos.mpr hu1).le]
  have hbv : θ * v ≤ θ := by nlinarith [mul_nonneg hθ0 (sub_pos.mpr hv1).le]
  have hbt : θ * (u * v) ≤ θ := by nlinarith [mul_nonneg hθ0 (sub_pos.mpr huv1).le]
  have hu : 1 - θ * u ≠ 0 := ne_of_gt (by linarith)
  have hv : 1 - θ * v ≠ 0 := ne_of_gt (by linarith)
  have ht : 1 - θ * (u * v) ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

end GeometricDegeneracy

/-- **No weight-blind argument can prove the kernel lemma.**  For the two-atom
law `c = {1 ↦ 1/10, 2 ↦ 9/10}` — with `Ĝ(z) = z/10 + 9z²/10`, `A = zĜ′`,
`B = 1−Ĝ`, `C(z) = Ĝ(z) − Ĝ(uv)` — the quantity `A(v)B(u)C(u) − A(u)B(v)C(v)`
is **negative** at `u = 9/10`, `v = 3/10`.  Since the corresponding statement
*is* true for `Ĝ(z) = 2Σ z^k/(4k²−1)`, any proof must use the actual weights. -/
theorem kernel_false_for_general_law :
    (fun z : ℝ => z / 10 + 2 * (9 / 10) * z ^ 2) (3 / 10)
        * (1 - ((9 : ℝ) / 10 / 10 + 9 / 10 * (9 / 10) ^ 2))
        * (((9 : ℝ) / 10 / 10 + 9 / 10 * (9 / 10) ^ 2)
            - ((27 : ℝ) / 100 / 10 + 9 / 10 * (27 / 100) ^ 2))
      - (fun z : ℝ => z / 10 + 2 * (9 / 10) * z ^ 2) (9 / 10)
        * (1 - ((3 : ℝ) / 10 / 10 + 9 / 10 * (3 / 10) ^ 2))
        * (((3 : ℝ) / 10 / 10 + 9 / 10 * (3 / 10) ^ 2)
            - ((27 : ℝ) / 100 / 10 + 9 / 10 * (27 / 100) ^ 2)) < 0 := by
  norm_num


/-! ## The other route: the branch comparison at `p = 0`

Conjecture 1 can also be closed by comparing the two branches directly:
`V_Z(C_u,C_v) > V_B(C_u,C_v)`, where `V_B = f_e(αβ)` is the BSC value and

```
V_Z(a,d) = (d/(1+d))·log(1+a) + ((1−ad)/((1+a)(1+d)))·log(1−ad) + (a/(1+a))·log(1+d)
```

is the Z/S value, the rates being `f_e(α) = C_u` and `(f_e(a) + a·log 2)/(1+a) = C_u`.
Unlike (iii) this comparison has a **uniform** relative margin (≈ 4 % at small
rates, measured), but it is irreducibly two-sided: against a fixed BSC the
S-channel *loses* to the BSC, by Mrs. Gerber's Lemma (`mgl_jensen`), so no
one-side-at-a-time chain reaches it.

Its small-rate limit is the constant below: `α ≈ √(2C)` gives `V_B ≈ 2C_uC_v`
while `a ≈ C/log 2` gives `V_Z ≈ C_uC_v/log²2`, so the ratio tends to
`1/(2log²2) = 1.0407… > 1`. -/


/-- **The extremal constant of the branch comparison**: `2·log²2 < 1`, i.e.
`1/(2log²2) > 1`.  This is exactly the small-rate limit of `V_Z/V_B`, so the
Z/S branch beats the BSC branch as the rates vanish. -/
theorem two_mul_log_two_sq_lt_one : 2 * (log 2) ^ 2 < 1 := by
  have h := Real.log_two_lt_d9
  have h0 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
  nlinarith [h, h0]

/-- **The branch comparison** (open): at `p = 0` the Z/S pair beats the BSC pair
at every matched rate pair.  Together with the fixed-point classification this
is an alternative route to Conjecture 1, independent of the saddle inequality
(iii); see `NOTES.md` §7e. -/
def BranchComparison : Prop :=
  ∀ a d α β : ℝ, 0 < a → a < 1 → 0 < d → d < 1 → 0 < α → α < 1 → 0 < β → β < 1 →
    fe α = zsRate a → fe β = zsRate d → fe (α * β) < zsValue a d

/-! ## Comonotone Schur: the two halves of the kernel lemma that *are* theorems

Write `S φ = Σ_i φ(θ_i)·(r_i² − r_j r_k)` and `G = g θ₁ + g θ₂ + g θ₃`.  Since
the kernel weight is `λ_i = f(θ_i)·(G − g(θ_i))`,

```
Σ_i λ_i (r_i² − r_j r_k)  =  G · S f  −  S (f·g) .
```

Both halves are nonnegative, and for a *structural* reason: `f`, `g`, hence
`f·g`, and `r` are all **decreasing** in `θ`, and a Schur sum whose weights are
comonotone with `r` is nonnegative (`kernel_nonneg_of_comonotone`, from
`schur_decomposition`: the Chebyshev bracket is then termwise nonnegative).

So the kernel lemma is exactly the *ratio* bound `S (f·g) ≤ G · S f` between two
quantities already known to be nonnegative.  Equivalently, by

```
λ_i − λ_l = g_m·(f_i − f_l)  +  f_i f_l·(φ_l − φ_i),     φ = g/f = (1−θu)/(1−θuv)
```

(`lambda_sub`), the only obstruction to comonotonicity of `λ` itself — and hence
the only negative contribution anywhere — is the second term, `φ` being
decreasing.  Numerically all three summands of `G` are needed: `S (f·g) ≤ g_max·S f`
fails on 97% of samples and `(g_max+g_mid)·S f` still fails on 31%. -/

section Comonotone

variable {θ₁ θ₂ θ₃ u v : ℝ}

/-- **Comonotone Schur.**  A Schur sum with nonnegative weights that are
comonotone with `r` is nonnegative.  In `schur_decomposition` the second bracket
is nonnegative from `l_i ≥ 0` alone, and comonotonicity makes each term of the
Chebyshev bracket nonnegative. -/
theorem kernel_nonneg_of_comonotone {l₁ l₂ l₃ r₁ r₂ r₃ : ℝ}
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hl₃ : 0 ≤ l₃)
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hr₃ : 0 ≤ r₃)
    (h₁₂ : 0 ≤ (l₁ - l₂) * (r₁ - r₂)) (h₁₃ : 0 ≤ (l₁ - l₃) * (r₁ - r₃))
    (h₂₃ : 0 ≤ (l₂ - l₃) * (r₂ - r₃)) :
    0 ≤ l₁ * (r₁ ^ 2 - r₂ * r₃) + l₂ * (r₂ ^ 2 - r₁ * r₃) + l₃ * (r₃ ^ 2 - r₁ * r₂) := by
  have k₁₂ : 0 ≤ (l₁ - l₂) * (r₁ ^ 2 - r₂ ^ 2) := by
    have h : (l₁ - l₂) * (r₁ ^ 2 - r₂ ^ 2) = ((l₁ - l₂) * (r₁ - r₂)) * (r₁ + r₂) := by ring
    rw [h]; exact mul_nonneg h₁₂ (by linarith)
  have k₁₃ : 0 ≤ (l₁ - l₃) * (r₁ ^ 2 - r₃ ^ 2) := by
    have h : (l₁ - l₃) * (r₁ ^ 2 - r₃ ^ 2) = ((l₁ - l₃) * (r₁ - r₃)) * (r₁ + r₃) := by ring
    rw [h]; exact mul_nonneg h₁₃ (by linarith)
  have k₂₃ : 0 ≤ (l₂ - l₃) * (r₂ ^ 2 - r₃ ^ 2) := by
    have h : (l₂ - l₃) * (r₂ ^ 2 - r₃ ^ 2) = ((l₂ - l₃) * (r₂ - r₃)) * (r₂ + r₃) := by ring
    rw [h]; exact mul_nonneg h₂₃ (by linarith)
  have hsq : 0 ≤ l₃ * (r₁ - r₂) ^ 2 + l₂ * (r₁ - r₃) ^ 2 + l₁ * (r₂ - r₃) ^ 2 :=
    add_nonneg (add_nonneg (mul_nonneg hl₃ (sq_nonneg _)) (mul_nonneg hl₂ (sq_nonneg _)))
      (mul_nonneg hl₁ (sq_nonneg _))
  rw [schur_decomposition l₁ l₂ l₃ r₁ r₂ r₃]
  linarith

/-- Every weight in the kernel lemma has the shape `θ ↦ (1−θ)/(1−θs)` with
`s < 1`, and each such function is comonotone with `r(θ) = (1−θu)/(1−θv)` when
`v ≤ u`: both are decreasing, and by `fFun'_sub`/`rFun_sub` the product of the
two differences is `(θ₂−θ₁)²·(1−s)(u−v)` over positive denominators. -/
theorem comonotone_of_decreasing {s : ℝ} (hs : s < 1) (hvu : v ≤ u)
    (ha₁ : 0 < 1 - θ₁ * s) (ha₂ : 0 < 1 - θ₂ * s)
    (hb₁ : 0 < 1 - θ₁ * v) (hb₂ : 0 < 1 - θ₂ * v) :
    0 ≤ ((1 - θ₁) / (1 - θ₁ * s) - (1 - θ₂) / (1 - θ₂ * s))
        * ((1 - θ₁ * u) / (1 - θ₁ * v) - (1 - θ₂ * u) / (1 - θ₂ * v)) := by
  rw [fFun'_sub ha₁.ne' ha₂.ne', rFun_sub hb₁.ne' hb₂.ne']
  rw [div_mul_div_comm]
  apply div_nonneg
  · have h : (θ₂ - θ₁) * (1 - s) * ((θ₂ - θ₁) * (u - v))
        = (θ₂ - θ₁) ^ 2 * ((1 - s) * (u - v)) := by ring
    rw [h]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))
  · exact mul_nonneg (mul_nonneg ha₁.le ha₂.le) (mul_nonneg hb₁.le hb₂.le)

/-- Comonotonicity is preserved by products of nonnegative comonotone factors —
this is what upgrades `f` and `g` to the weight `f·g`. -/
theorem mul_comonotone {A₁ A₂ B₁ B₂ R₁ R₂ : ℝ} (hA₂ : 0 ≤ A₂) (hB₁ : 0 ≤ B₁)
    (hA : 0 ≤ (A₁ - A₂) * (R₁ - R₂)) (hB : 0 ≤ (B₁ - B₂) * (R₁ - R₂)) :
    0 ≤ (A₁ * B₁ - A₂ * B₂) * (R₁ - R₂) := by
  have h : (A₁ * B₁ - A₂ * B₂) * (R₁ - R₂)
      = B₁ * ((A₁ - A₂) * (R₁ - R₂)) + A₂ * ((B₁ - B₂) * (R₁ - R₂)) := by ring
  rw [h]
  exact add_nonneg (mul_nonneg hB₁ hA) (mul_nonneg hA₂ hB)

/-- The kernel weight `λ_i = f(θ_i)·(g(θ_j)+g(θ_k))` splits the kernel sum into
`G·S f − S (f·g)`, with `G = Σ g(θ_i)`.  Pure algebra, valid for any `f, g, r`. -/
theorem kernel_split (f g r : ℝ → ℝ) (θ₁ θ₂ θ₃ : ℝ) :
    f θ₁ * (g θ₂ + g θ₃) * (r θ₁ ^ 2 - r θ₂ * r θ₃)
      + f θ₂ * (g θ₁ + g θ₃) * (r θ₂ ^ 2 - r θ₁ * r θ₃)
      + f θ₃ * (g θ₁ + g θ₂) * (r θ₃ ^ 2 - r θ₁ * r θ₂)
    = (g θ₁ + g θ₂ + g θ₃)
        * (f θ₁ * (r θ₁ ^ 2 - r θ₂ * r θ₃) + f θ₂ * (r θ₂ ^ 2 - r θ₁ * r θ₃)
            + f θ₃ * (r θ₃ ^ 2 - r θ₁ * r θ₂))
      - (f θ₁ * g θ₁ * (r θ₁ ^ 2 - r θ₂ * r θ₃) + f θ₂ * g θ₂ * (r θ₂ ^ 2 - r θ₁ * r θ₃)
          + f θ₃ * g θ₃ * (r θ₃ ^ 2 - r θ₁ * r θ₂)) := by
  ring

/-- The failure of comonotonicity of `λ` itself, isolated: the first term is
nonnegative (`f` decreasing), the second is the *only* negative contribution
anywhere in the kernel lemma, and `fg_cross` evaluates it. -/
theorem lambda_sub (f g : ℝ → ℝ) (θ₁ θ₂ θ₃ : ℝ) :
    f θ₁ * (g θ₂ + g θ₃) - f θ₂ * (g θ₁ + g θ₃)
      = g θ₃ * (f θ₁ - f θ₂) + (f θ₁ * g θ₂ - f θ₂ * g θ₁) := by
  ring

end Comonotone

/-! ### The two halves, for the actual `f`, `g`, `r` -/

section Halves

variable {θ₁ θ₂ θ₃ u v : ℝ}

/-- Positivity of the three denominators. -/
private lemma denom_pos {θ s : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (_hs0 : 0 ≤ s) (hs1 : s < 1) :
    0 < 1 - θ * s := by nlinarith

/-- `S f ≥ 0`: the kernel sum with the *unweighted* factor `f`, which is the
`G → ∞` limit of the kernel lemma. -/
theorem kerSum_f_nonneg (h₁ : 0 < θ₁) (h₁' : θ₁ < 1) (h₂ : 0 < θ₂) (h₂' : θ₂ < 1)
    (h₃ : 0 < θ₃) (h₃' : θ₃ < 1) (hv0 : 0 < v) (hvu : v ≤ u) (hu1 : u < 1) :
    0 ≤ (1 - θ₁) / (1 - θ₁ * u) * (((1 - θ₁ * u) / (1 - θ₁ * v)) ^ 2
          - (1 - θ₂ * u) / (1 - θ₂ * v) * ((1 - θ₃ * u) / (1 - θ₃ * v)))
      + (1 - θ₂) / (1 - θ₂ * u) * (((1 - θ₂ * u) / (1 - θ₂ * v)) ^ 2
          - (1 - θ₁ * u) / (1 - θ₁ * v) * ((1 - θ₃ * u) / (1 - θ₃ * v)))
      + (1 - θ₃) / (1 - θ₃ * u) * (((1 - θ₃ * u) / (1 - θ₃ * v)) ^ 2
          - (1 - θ₁ * u) / (1 - θ₁ * v) * ((1 - θ₂ * u) / (1 - θ₂ * v))) := by
  have hu0 : 0 ≤ u := le_trans hv0.le hvu
  have hv1 : v < 1 := lt_of_le_of_lt hvu hu1
  have ha₁ := denom_pos h₁ h₁' hu0 hu1; have ha₂ := denom_pos h₂ h₂' hu0 hu1
  have ha₃ := denom_pos h₃ h₃' hu0 hu1
  have hb₁ := denom_pos h₁ h₁' hv0.le hv1; have hb₂ := denom_pos h₂ h₂' hv0.le hv1
  have hb₃ := denom_pos h₃ h₃' hv0.le hv1
  exact kernel_nonneg_of_comonotone
    (div_nonneg (by linarith) ha₁.le) (div_nonneg (by linarith) ha₂.le)
    (div_nonneg (by linarith) ha₃.le)
    (div_nonneg ha₁.le hb₁.le) (div_nonneg ha₂.le hb₂.le) (div_nonneg ha₃.le hb₃.le)
    (comonotone_of_decreasing hu1 hvu ha₁ ha₂ hb₁ hb₂)
    (comonotone_of_decreasing hu1 hvu ha₁ ha₃ hb₁ hb₃)
    (comonotone_of_decreasing hu1 hvu ha₂ ha₃ hb₂ hb₃)

/-- `S (f·g) ≥ 0`: the same, with the weight `f·g`, which is decreasing as a
product of nonnegative decreasing functions (`mul_comonotone`). -/
theorem kerSum_fg_nonneg (h₁ : 0 < θ₁) (h₁' : θ₁ < 1) (h₂ : 0 < θ₂) (h₂' : θ₂ < 1)
    (h₃ : 0 < θ₃) (h₃' : θ₃ < 1) (hv0 : 0 < v) (hvu : v ≤ u) (hu1 : u < 1) :
    0 ≤ (1 - θ₁) / (1 - θ₁ * u) * ((1 - θ₁) / (1 - θ₁ * (u * v)))
          * (((1 - θ₁ * u) / (1 - θ₁ * v)) ^ 2
            - (1 - θ₂ * u) / (1 - θ₂ * v) * ((1 - θ₃ * u) / (1 - θ₃ * v)))
      + (1 - θ₂) / (1 - θ₂ * u) * ((1 - θ₂) / (1 - θ₂ * (u * v)))
          * (((1 - θ₂ * u) / (1 - θ₂ * v)) ^ 2
            - (1 - θ₁ * u) / (1 - θ₁ * v) * ((1 - θ₃ * u) / (1 - θ₃ * v)))
      + (1 - θ₃) / (1 - θ₃ * u) * ((1 - θ₃) / (1 - θ₃ * (u * v)))
          * (((1 - θ₃ * u) / (1 - θ₃ * v)) ^ 2
            - (1 - θ₁ * u) / (1 - θ₁ * v) * ((1 - θ₂ * u) / (1 - θ₂ * v))) := by
  have hu0 : 0 ≤ u := le_trans hv0.le hvu
  have hv1 : v < 1 := lt_of_le_of_lt hvu hu1
  have ht0 : 0 ≤ u * v := mul_nonneg hu0 hv0.le
  have ht1 : u * v < 1 := by nlinarith
  have ha₁ := denom_pos h₁ h₁' hu0 hu1; have ha₂ := denom_pos h₂ h₂' hu0 hu1
  have ha₃ := denom_pos h₃ h₃' hu0 hu1
  have hb₁ := denom_pos h₁ h₁' hv0.le hv1; have hb₂ := denom_pos h₂ h₂' hv0.le hv1
  have hb₃ := denom_pos h₃ h₃' hv0.le hv1
  have hw₁ := denom_pos h₁ h₁' ht0 ht1; have hw₂ := denom_pos h₂ h₂' ht0 ht1
  have hw₃ := denom_pos h₃ h₃' ht0 ht1
  -- the product weight is comonotone with `r`, pair by pair
  have hcm : ∀ {α β : ℝ}, 0 < α → α < 1 → 0 < β → β < 1 →
      ∀ (hα : 0 < 1 - α * u) (hβ : 0 < 1 - β * u) (hbα : 0 < 1 - α * v) (hbβ : 0 < 1 - β * v),
      0 < 1 - α * (u * v) → 0 < 1 - β * (u * v) →
      0 ≤ ((1 - α) / (1 - α * u) * ((1 - α) / (1 - α * (u * v)))
            - (1 - β) / (1 - β * u) * ((1 - β) / (1 - β * (u * v))))
          * ((1 - α * u) / (1 - α * v) - (1 - β * u) / (1 - β * v)) := by
    intro α β _ hα1 _ hβ1 hα hβ hbα hbβ hwα hwβ
    exact mul_comonotone (div_nonneg (by linarith) hβ.le) (div_nonneg (by linarith) hwα.le)
      (comonotone_of_decreasing hu1 hvu hα hβ hbα hbβ)
      (comonotone_of_decreasing ht1 hvu hwα hwβ hbα hbβ)
  exact kernel_nonneg_of_comonotone
    (mul_nonneg (div_nonneg (by linarith) ha₁.le) (div_nonneg (by linarith) hw₁.le))
    (mul_nonneg (div_nonneg (by linarith) ha₂.le) (div_nonneg (by linarith) hw₂.le))
    (mul_nonneg (div_nonneg (by linarith) ha₃.le) (div_nonneg (by linarith) hw₃.le))
    (div_nonneg ha₁.le hb₁.le) (div_nonneg ha₂.le hb₂.le) (div_nonneg ha₃.le hb₃.le)
    (hcm h₁ h₁' h₂ h₂' ha₁ ha₂ hb₁ hb₂ hw₁ hw₂)
    (hcm h₁ h₁' h₃ h₃' ha₁ ha₃ hb₁ hb₃ hw₁ hw₃)
    (hcm h₂ h₂' h₃ h₃' ha₂ ha₃ hb₂ hb₃ hw₂ hw₃)

end Halves


/-! ### The degenerate face `u = 1`

At `u = 1` one has `a_i = 1−θ_i = A_i`, hence `f ≡ 1`, `w_i = b_i`, `g_i = r_i`,
and the kernel **vanishes identically** (`kernel_vanishes_on_face`): the whole
face `u = 1` is a zero of the kernel lemma.  That is why every global
certificate attempt saw a vanishing margin, and why the corner analysis of §7f′
found an exact leading-order cancellation — the corner merely sits on this face.

So on the face the first non-trivial datum is the derivative in `c = 1 − u`.
Writing `s_i = θ_i/b_i`, the face relation is `r_i + (1−v)·s_i = 1` — the two
coordinates are affinely dependent — so `s_i = (1−r_i)/κ` with `κ = 1−v`, and a
CAS computation (`numerics/p0_kernel_face.py`) gives

```
κ·r₁r₂r₃ · ∂(kernel)/∂c  at  c = 0   =   κ · faceX(r)  +  faceY(r) ,   r_i ∈ (0,1).
```

Both coefficients are nonnegative on the cube — `faceX` outright, `faceY` after
ordering — so the kernel enters the region `u < 1` with a nonnegative slope
across the whole face.  `faceY` is negative off the cube (e.g. on `(0,3)³`), so
the box constraints are essential; the certificate is the Pólya one in the
ordered simplex coordinates `w = r₃`, `q = r₂−r₃`, `p = r₁−r₂`, `m = 1−r₁`,
where `faceY` has **53 monomials, all with positive integer coefficients** and
no degree elevation is needed.

The differentiation itself is done by CAS, not in Lean; what is formalised here
is the algebra it produces — the face identity and the two positivity
statements. -/

section Face

/-- The kernel lemma degenerates on the face `u = 1`: there `f ≡ 1` and `g = r`,
and the resulting symmetric sum vanishes identically. -/
theorem kernel_vanishes_on_face (r₁ r₂ r₃ : ℝ) :
    (r₂ + r₃) * (r₁ ^ 2 - r₂ * r₃) + (r₁ + r₃) * (r₂ ^ 2 - r₁ * r₃)
      + (r₁ + r₂) * (r₃ ^ 2 - r₁ * r₂) = 0 := by
  ring

/-- The `κ`-coefficient of the face derivative. -/
noncomputable def faceX (r₁ r₂ r₃ : ℝ) : ℝ :=
  r₁ * r₂ * r₃ * (r₁ * r₂ * (r₁ - r₂) ^ 2 + r₁ * r₃ * (r₁ - r₃) ^ 2
    + r₂ * r₃ * (r₂ - r₃) ^ 2)

/-- The `κ`-free coefficient of the face derivative. -/
noncomputable def faceY (r₁ r₂ r₃ : ℝ) : ℝ :=
  -r₁^4*r₂^2*r₃ - r₁^4*r₂*r₃^2 + 2*r₁^3*r₂^3*r₃ + r₁^3*r₂^2 + 2*r₁^3*r₂*r₃^3 - 2*r₁^3*r₂*r₃ + r₁^3*r₃^2 - r₁^2*r₂^4*r₃ + r₁^2*r₂^3 - r₁^2*r₂*r₃^4 + r₁^2*r₃^3 - r₁*r₂^4*r₃^2 + 2*r₁*r₂^3*r₃^3 - 2*r₁*r₂^3*r₃ - r₁*r₂^2*r₃^4 - 2*r₁*r₂*r₃^3 + r₂^3*r₃^2 + r₂^2*r₃^3

/-- `faceX ≥ 0` needs only nonnegativity. -/
theorem faceX_nonneg {r₁ r₂ r₃ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (h₃ : 0 ≤ r₃) :
    0 ≤ faceX r₁ r₂ r₃ := by
  unfold faceX
  positivity

/-- One monomial of the Pólya certificate. -/
private lemma monomial_nonneg {w q p M C : ℝ} (hw : 0 ≤ w) (hq : 0 ≤ q) (hp : 0 ≤ p)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (a b c d : ℕ) :
    0 ≤ C * (w ^ a * (q ^ b * (p ^ c * M ^ d))) :=
  mul_nonneg hC (mul_nonneg (pow_nonneg hw a)
    (mul_nonneg (pow_nonneg hq b) (mul_nonneg (pow_nonneg hp c) (pow_nonneg hM d))))

set_option maxHeartbeats 2000000 in
/-- **`faceY ≥ 0` on the ordered unit cube.**  The proof is the Pólya
certificate: in the simplex coordinates `r₃`, `r₂−r₃`, `r₁−r₂`, `1−r₁` — all
nonnegative and summing to `1` — `faceY` is a positive-integer combination of
monomials.  No degree elevation is needed. -/
theorem faceY_nonneg {r₁ r₂ r₃ : ℝ} (h₃ : 0 ≤ r₃) (h₃₂ : r₃ ≤ r₂) (h₂₁ : r₂ ≤ r₁)
    (h₁ : r₁ ≤ 1) : 0 ≤ faceY r₁ r₂ r₃ := by
  have hw : (0 : ℝ) ≤ r₃ := h₃
  have hq : (0 : ℝ) ≤ r₂ - r₃ := by linarith
  have hp : (0 : ℝ) ≤ r₁ - r₂ := by linarith
  have hM : (0 : ℝ) ≤ 1 - r₁ := by linarith
  have key : faceY r₁ r₂ r₃ =
      (1 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 2 * ((r₁ - r₂) ^ 3 * (1 - r₁) ^ 2)))
      + (2 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 2 * ((r₁ - r₂) ^ 4 * (1 - r₁) ^ 1)))
      + (1 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 2 * ((r₁ - r₂) ^ 5 * (1 - r₁) ^ 0)))
      + (4 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 3 * ((r₁ - r₂) ^ 2 * (1 - r₁) ^ 2)))
      + (10 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 3 * ((r₁ - r₂) ^ 3 * (1 - r₁) ^ 1)))
      + (6 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 3 * ((r₁ - r₂) ^ 4 * (1 - r₁) ^ 0)))
      + (5 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 4 * ((r₁ - r₂) ^ 1 * (1 - r₁) ^ 2)))
      + (18 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 4 * ((r₁ - r₂) ^ 2 * (1 - r₁) ^ 1)))
      + (14 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 4 * ((r₁ - r₂) ^ 3 * (1 - r₁) ^ 0)))
      + (2 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 5 * ((r₁ - r₂) ^ 0 * (1 - r₁) ^ 2)))
      + (14 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 5 * ((r₁ - r₂) ^ 1 * (1 - r₁) ^ 1)))
      + (16 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 5 * ((r₁ - r₂) ^ 2 * (1 - r₁) ^ 0)))
      + (4 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 6 * ((r₁ - r₂) ^ 0 * (1 - r₁) ^ 1)))
      + (9 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 6 * ((r₁ - r₂) ^ 1 * (1 - r₁) ^ 0)))
      + (2 : ℝ) * (r₃ ^ 0 * ((r₂ - r₃) ^ 7 * ((r₁ - r₂) ^ 0 * (1 - r₁) ^ 0)))
      + (6 : ℝ) * (r₃ ^ 1 * ((r₂ - r₃) ^ 2 * ((r₁ - r₂) ^ 2 * (1 - r₁) ^ 2)))
      + (14 : ℝ) * (r₃ ^ 1 * ((r₂ - r₃) ^ 2 * ((r₁ - r₂) ^ 3 * (1 - r₁) ^ 1)))
      + (7 : ℝ) * (r₃ ^ 1 * ((r₂ - r₃) ^ 2 * ((r₁ - r₂) ^ 4 * (1 - r₁) ^ 0)))
      + (12 : ℝ) * (r₃ ^ 1 * ((r₂ - r₃) ^ 3 * ((r₁ - r₂) ^ 1 * (1 - r₁) ^ 2)))
      + (44 : ℝ) * (r₃ ^ 1 * ((r₂ - r₃) ^ 3 * ((r₁ - r₂) ^ 2 * (1 - r₁) ^ 1)))
      + (32 : ℝ) * (r₃ ^ 1 * ((r₂ - r₃) ^ 3 * ((r₁ - r₂) ^ 3 * (1 - r₁) ^ 0)))
      + (6 : ℝ) * (r₃ ^ 1 * ((r₂ - r₃) ^ 4 * ((r₁ - r₂) ^ 0 * (1 - r₁) ^ 2)))
      + (46 : ℝ) * (r₃ ^ 1 * ((r₂ - r₃) ^ 4 * ((r₁ - r₂) ^ 1 * (1 - r₁) ^ 1)))
      + (53 : ℝ) * (r₃ ^ 1 * ((r₂ - r₃) ^ 4 * ((r₁ - r₂) ^ 2 * (1 - r₁) ^ 0)))
      + (16 : ℝ) * (r₃ ^ 1 * ((r₂ - r₃) ^ 5 * ((r₁ - r₂) ^ 0 * (1 - r₁) ^ 1)))
      + (38 : ℝ) * (r₃ ^ 1 * ((r₂ - r₃) ^ 5 * ((r₁ - r₂) ^ 1 * (1 - r₁) ^ 0)))
      + (10 : ℝ) * (r₃ ^ 1 * ((r₂ - r₃) ^ 6 * ((r₁ - r₂) ^ 0 * (1 - r₁) ^ 0)))
      + (3 : ℝ) * (r₃ ^ 2 * ((r₂ - r₃) ^ 1 * ((r₁ - r₂) ^ 2 * (1 - r₁) ^ 2)))
      + (6 : ℝ) * (r₃ ^ 2 * ((r₂ - r₃) ^ 1 * ((r₁ - r₂) ^ 3 * (1 - r₁) ^ 1)))
      + (9 : ℝ) * (r₃ ^ 2 * ((r₂ - r₃) ^ 2 * ((r₁ - r₂) ^ 1 * (1 - r₁) ^ 2)))
      + (36 : ℝ) * (r₃ ^ 2 * ((r₂ - r₃) ^ 2 * ((r₁ - r₂) ^ 2 * (1 - r₁) ^ 1)))
      + (18 : ℝ) * (r₃ ^ 2 * ((r₂ - r₃) ^ 2 * ((r₁ - r₂) ^ 3 * (1 - r₁) ^ 0)))
      + (6 : ℝ) * (r₃ ^ 2 * ((r₂ - r₃) ^ 3 * ((r₁ - r₂) ^ 0 * (1 - r₁) ^ 2)))
      + (54 : ℝ) * (r₃ ^ 2 * ((r₂ - r₃) ^ 3 * ((r₁ - r₂) ^ 1 * (1 - r₁) ^ 1)))
      + (57 : ℝ) * (r₃ ^ 2 * ((r₂ - r₃) ^ 3 * ((r₁ - r₂) ^ 2 * (1 - r₁) ^ 0)))
      + (24 : ℝ) * (r₃ ^ 2 * ((r₂ - r₃) ^ 4 * ((r₁ - r₂) ^ 0 * (1 - r₁) ^ 1)))
      + (57 : ℝ) * (r₃ ^ 2 * ((r₂ - r₃) ^ 4 * ((r₁ - r₂) ^ 1 * (1 - r₁) ^ 0)))
      + (18 : ℝ) * (r₃ ^ 2 * ((r₂ - r₃) ^ 5 * ((r₁ - r₂) ^ 0 * (1 - r₁) ^ 0)))
      + (2 : ℝ) * (r₃ ^ 3 * ((r₂ - r₃) ^ 0 * ((r₁ - r₂) ^ 2 * (1 - r₁) ^ 2)))
      + (4 : ℝ) * (r₃ ^ 3 * ((r₂ - r₃) ^ 0 * ((r₁ - r₂) ^ 3 * (1 - r₁) ^ 1)))
      + (2 : ℝ) * (r₃ ^ 3 * ((r₂ - r₃) ^ 1 * ((r₁ - r₂) ^ 1 * (1 - r₁) ^ 2)))
      + (14 : ℝ) * (r₃ ^ 3 * ((r₂ - r₃) ^ 1 * ((r₁ - r₂) ^ 2 * (1 - r₁) ^ 1)))
      + (2 : ℝ) * (r₃ ^ 3 * ((r₂ - r₃) ^ 2 * ((r₁ - r₂) ^ 0 * (1 - r₁) ^ 2)))
      + (26 : ℝ) * (r₃ ^ 3 * ((r₂ - r₃) ^ 2 * ((r₁ - r₂) ^ 1 * (1 - r₁) ^ 1)))
      + (20 : ℝ) * (r₃ ^ 3 * ((r₂ - r₃) ^ 2 * ((r₁ - r₂) ^ 2 * (1 - r₁) ^ 0)))
      + (16 : ℝ) * (r₃ ^ 3 * ((r₂ - r₃) ^ 3 * ((r₁ - r₂) ^ 0 * (1 - r₁) ^ 1)))
      + (36 : ℝ) * (r₃ ^ 3 * ((r₂ - r₃) ^ 3 * ((r₁ - r₂) ^ 1 * (1 - r₁) ^ 0)))
      + (14 : ℝ) * (r₃ ^ 3 * ((r₂ - r₃) ^ 4 * ((r₁ - r₂) ^ 0 * (1 - r₁) ^ 0)))
      + (4 : ℝ) * (r₃ ^ 4 * ((r₂ - r₃) ^ 0 * ((r₁ - r₂) ^ 2 * (1 - r₁) ^ 1)))
      + (4 : ℝ) * (r₃ ^ 4 * ((r₂ - r₃) ^ 1 * ((r₁ - r₂) ^ 1 * (1 - r₁) ^ 1)))
      + (4 : ℝ) * (r₃ ^ 4 * ((r₂ - r₃) ^ 2 * ((r₁ - r₂) ^ 0 * (1 - r₁) ^ 1)))
      + (8 : ℝ) * (r₃ ^ 4 * ((r₂ - r₃) ^ 2 * ((r₁ - r₂) ^ 1 * (1 - r₁) ^ 0)))
      + (4 : ℝ) * (r₃ ^ 4 * ((r₂ - r₃) ^ 3 * ((r₁ - r₂) ^ 0 * (1 - r₁) ^ 0)))
    := by unfold faceY; ring
  rw [key]
  repeat' refine add_nonneg ?_ ?_
  all_goals exact monomial_nonneg hw hq hp hM (by norm_num) _ _ _ _

end Face

/-! ## The remaining open inequality -/

/-- **The kernel lemma** (open; see `NOTES.md` §7f).  With
`r_i = (1−θ_i u)/(1−θ_i v)`, `f(θ) = (1−θ)/(1−θu)`, `g(θ) = (1−θ)/(1−θuv)` and
`λ_i = f(θ_i)·(g(θ_j) + g(θ_k))`, the diagonal reduction of (iii) is exactly

```
Σ_i λ_i · (r_i² − r_j r_k) ≥ 0 .
```

Numerically verified with no violations; every diagonal-Handelman LP relaxation
is infeasible, so a proof needs an SOS certificate with cross terms, or a new
idea. -/
def KernelLemma : Prop :=
  ∀ θ₁ θ₂ θ₃ u v : ℝ, 0 < θ₁ → θ₁ < 1 → 0 < θ₂ → θ₂ < 1 → 0 < θ₃ → θ₃ < 1 →
    0 < v → v ≤ u → u < 1 →
    let f : ℝ → ℝ := fun θ => (1 - θ) / (1 - θ * u)
    let g : ℝ → ℝ := fun θ => (1 - θ) / (1 - θ * (u * v))
    let r : ℝ → ℝ := fun θ => (1 - θ * u) / (1 - θ * v)
    0 ≤ f θ₁ * (g θ₂ + g θ₃) * (r θ₁ ^ 2 - r θ₂ * r θ₃)
      + f θ₂ * (g θ₁ + g θ₃) * (r θ₂ ^ 2 - r θ₁ * r θ₃)
      + f θ₃ * (g θ₁ + g θ₂) * (r θ₃ ^ 2 - r θ₁ * r θ₂)

end BSCAveraging
