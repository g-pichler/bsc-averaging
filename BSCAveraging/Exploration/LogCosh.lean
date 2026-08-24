import BSCAveraging.LogCosh

/-! # `LogCosh` — exploration companion

The declarations of `BSCAveraging.LogCosh` that are **not** used by any of the
three theorems of `BSCAveraging.Basic`.  Section headers are copied from the
main file so the two read in parallel. -/

/-! # `L = log cosh` and the odd kernels `M_g`

The elementary layer of `NOTES.md` §7c⁗ (interior uniqueness at `p = 0`).

`L(w) = log cosh w` is even, convex, with `L′ = tanh`, `L″ = 1 − tanh² = sech²`.
The kernels are `M_g(w) = L(w+g) − L(w−g)`, odd in `w` and in `g`, concave in
`w > 0` when `g > 0`.  The two facts §7c⁗ needs from this layer are

* `MG_div_antitoneOn` — `M_v(t)/t` is decreasing on `t > 0`;
* `phi_antitoneOn` — `ϕ(g) = (L(Y) − L(Y−2g))/g` is decreasing, which is exactly
  the tangent-line inequality for the convex `L`.

Together they give the inequality `(♦)` of §7c⁗ step 5. -/

namespace BSCAveraging.LC

open Real


lemma MG_zero (w : ℝ) : MG 0 w = 0 := by simp [MG]


/-! ### The Green identity

If `F` and `G` both vanish at the ends of the window, then `∫ F·G″ = ∫ F″·G`:
the Wronskian `F G′ − F′ G` is an antiderivative of `F G″ − F″ G` and vanishes
at both ends.  No integration-by-parts lemma is needed — one application of
`integral_eq_sub_of_hasDerivAt`. -/

/-! ### The window, the deficit, and the bitangency residual -/


/-! ### From bitangency to the residual

`NOTES.md` §7c⁗.  In `θ = artanh` coordinates the `U`-side slack is

```
D(σ) = l₀ + l₁·tanh σ + l₂·f_e(tanh σ) − G(σ) ,   f_e(tanh σ) = σ tanh σ − L(σ),
```

with `G` the atom value against the two-atom `V`-side `(tanh γ, −tanh δ)`.  The
key collapse is that the *mean-zero* weights make both mixed coefficients equal
to `k = sinh γ sinh δ / sinh(γ+δ)`, so

```
G′(σ)·cosh²σ = k·[ L(σ+γ) − L(σ−δ) − L(γ) + L(δ) ] = k·[ M_n(σ+v) − M_n(v) ],
```

`n = (γ+δ)/2`, `v = (γ−δ)/2`: the odd-kernel form.  The two tangency conditions
then say that the affine function `l₁ + l₂σ` matches `k·M_n` at the two window
ends, i.e. it *is* the chord, and the two value conditions say the integral of
the difference against `sech²` vanishes — which is exactly `R_S = 0`. -/


lemma continuous_LCshift (c : ℝ) : Continuous (fun σ : ℝ => LC (σ + c)) :=
  continuous_LC.comp (by fun_prop)


/-- **The analytic core of `(B)`**: a doubly-interior bitangent pair is
symmetric — both skews vanish. -/
theorem bitangent_pair_symmetric {m n u v l₀ l₁ l₂ p₀ p₁ p₂ : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hγ : 0 < n + v) (hδ : 0 < n - v)
    (hα : 0 < m + u) (hβ : 0 < m - u)
    (hDα : Dsl l₀ l₁ l₂ (n + v) (n - v) (m + u) = 0)
    (hDβ : Dsl l₀ l₁ l₂ (n + v) (n - v) (u - m) = 0)
    (hTα : l₁ + l₂ * (m + u) = kco (n + v) (n - v) * (MG n (u + v + m) - MG n v))
    (hTβ : l₁ + l₂ * (u - m) = kco (n + v) (n - v) * (MG n (u + v - m) - MG n v))
    (hEγ : Dsl p₀ p₁ p₂ (m + u) (m - u) (n + v) = 0)
    (hEδ : Dsl p₀ p₁ p₂ (m + u) (m - u) (v - n) = 0)
    (hUγ : p₁ + p₂ * (n + v) = kco (m + u) (m - u) * (MG m (v + u + n) - MG m u))
    (hUδ : p₁ + p₂ * (v - n) = kco (m + u) (m - u) * (MG m (v + u - n) - MG m u)) :
    u = 0 ∧ v = 0 := by
  have hS := bitangent_residual_zero hm hγ hδ hDα hDβ hTα hTβ
  have hT := bitangent_residual_zero hn hα hβ hEγ hEδ hUγ hUδ
  exact skews_vanish hm hn hS hT

/-- A contact point of a nonnegative slack is a tangency point: the derivative
condition comes free from the domination. -/
theorem tangency_of_contact {n v l₀ l₁ l₂ σ : ℝ} (hγ : 0 < n + v) (hδ : 0 < n - v)
    (hge : ∀ τ : ℝ, 0 ≤ Dsl l₀ l₁ l₂ (n + v) (n - v) τ)
    (heq : Dsl l₀ l₁ l₂ (n + v) (n - v) σ = 0) :
    l₁ + l₂ * σ = kco (n + v) (n - v) * (MG n (σ + v) - MG n v) := by
  have hmin : IsLocalMin (Dsl l₀ l₁ l₂ (n + v) (n - v)) σ :=
    Filter.Eventually.of_forall (fun x => by rw [heq]; exact hge x)
  have hd := hasDerivAt_Dsl hγ hδ l₀ l₁ l₂ σ
  have h0 := hmin.hasDerivAt_eq_zero hd
  have hc : Real.cosh σ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (Real.cosh_pos σ))
  field_simp at h0
  linarith

end BSCAveraging.LC
