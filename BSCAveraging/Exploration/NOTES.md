# Attacking `conv 𝒜 = conv ℬ`

Working notes on MO 285151. What the question reduces to, what is provable, and
exactly where the remaining difficulty sits. Bits throughout (the Lean files use
nats). Write `δ := 1 − 2p ∈ [0,1]` for the correlation.

> **Status: proved** for every `p ∈ [0,1]`
> (`averaged_bsc_maximise_mutual_information`).  Conjectures 1 and 2 of
> Dikshtein–Ordentlich–Shamai at `p = 0` are proved too (§7); that work started
> after most of these notes were written, so §7 is the only part of the file
> that concerns them.  These notes are the working
> record, written as the attack proceeded, so they are organised by *route*, not
> by the final argument — and most routes here were refuted, which is their main
> value.  Read them for the failures and the numerics.
>
> For the proof itself read `Main.lean` (the road map).  File names in these
> notes are the ones current when each section was written; some files were
> later merged, renamed or moved into `Exploration/`, so a name here may not
> resolve in the present tree.  `Basic.lean` and the tree itself are
> authoritative.
> §1 (support-function reduction), §2 (bias parametrization) and §5e (the sign
> flip) are the parts that survived into it; §6 records the rest.  Results cited
> below that live in `Exploration.lean` are proved but *not* used by the theorem.

## 0. Notation

Global, used everywhere:

| Symbol | Meaning |
| --- | --- |
| `δ = 1 − 2p` | correlation of the source; `δ ∈ [0,1]` for `p ∈ [0,1/2]` |
| `f(z) = (1+z)log(1+z)` | the mutual-information kernel; `I(U;V) = E f(δST)` |
| `f_e(y) = ½[(1+y)log(1+y)+(1−y)log(1−y)]` | the **even part** of `f`; `= log 2 − h₂((1−y)/2)`; `I(U;X) = E f_e(S)` |
| `fo(z) = ½[(1+z)log(1+z)−(1−z)log(1−z)]` | the **odd part** of `f`, so `f = f_e + fo` |
| `L = artanh` | `f_e′ = L`, and `f_e(y) = y·L(y) − A(y)`, `A(y) = −½log(1−y²)` |
| `s_u`, `t_v` | the bias *families*: one number per value of `U`, resp. `V` (§2) |
| `S = s_U`, `T = t_V` | the bias *random variables*, independent, mean zero |
| `a, b, c, d` | the atoms: `S ∈ {a,−b}`, `T ∈ {c,−d}`, **positive atom first**, all in `[0,1]` |
| `g(P,Q) = f_e(δPQ) − μf_e(P) − νf_e(Q)` | the value of the *symmetric* (BSC) pair with biases `P, Q` |
| `J`, `J_sym` | `sup` of the Lagrangian over all pairs, resp. over BSC pairs |
| `Ω` | the odd gain, `E fo(δST)` — the whole difficulty (§5e) |
| `g_ij`, `w_ij` | the four **corner values** `g_ij = g(i,j)`, `i ∈ {a,b}`, `j ∈ {c,d}`, and their weights (`Σ w_ij = 1`) |
| `gSum`, `gMax4` | the weighted average `Σ w_ij g_ij` and the maximum `max_ij g_ij`; `F = gSum + Ω` |
| `Δ_g` | the mixed difference `g_ac − g_ad − g_bc + g_bd`, free of `μ, ν`, and `< 0` |

**Reused letters.** The following are *local* to their section and are not the
same function as each other, nor as anything above:

| Symbol | Section | Meaning |
| --- | --- | --- |
| `φ` | §5j (LP dual) | a generic test function in `sup{∫φ dP̃}` |
| `φ(z) = log(1+z)(1+λz)` | §6 (L1) | the logarithm-free witness for `ρ ≤ 2 − 1/log 2` |
| `φ(t) = f_e(m+kδt) − νf_e(t)` | §6 (E4) | the best-response objective whose bitangency is (E4) |
| `φ(u) = fo(δu)/u` | §5e | the odd kernel, whose supermodularity gives the sign flip |
| `g` | §5a, §5d | the curvature profile `g = Q·R` — **not** the `g(P,Q)` above |

Earlier drafts wrote `φ` for `f_e` and `f̄` for `f_e` as well; those are now spelled
`f_e` throughout §§1–5.

## 1. Support-function reduction

`𝒜` and `ℬ` are both down-closed in `R₀` and up-closed in `R₁, R₂`, so they share
the recession cone `{d₀ ≤ 0, d₁ ≥ 0, d₂ ≥ 0}`. Hence a linear functional
`⟨λ, R⟩` is bounded above on either set only when `λ₀ ≥ 0`, `λ₁, λ₂ ≤ 0`, and
`conv 𝒜 = conv ℬ` iff the two support functions agree on that cone. The case
`λ₀ = 0` is trivial (both suprema are `0`), and `λ₀ > 0` rescales to `λ₀ = 1`.
Writing `λ₁ = −μ`, `λ₂ = −ν`:

> **(SF)** `conv 𝒜 = conv ℬ` ⟺ for all `μ, ν ≥ 0`,
> `sup_{cL, cR} [I(U;V) − μ I(U;X) − ν I(Y;V)]` is the same when `cL, cR` range
> over all binary channels as when they range over BSCs.

## 2. The bias parametrization

Let `π_u = P(U=u)`, `ρ_v = P(V=v)`. The posteriors, in centered form, are the
two **bias families**

```
s_u := 1 − 2 P(X=1 | U=u)  ∈ [−1,1]   (one number per value u of U)
t_v := 1 − 2 P(Y=1 | V=v)  ∈ [−1,1]   (one number per value v of V)
```

and the two **bias random variables** are `S := s_U` and `T := t_V`, i.e. `S`
takes the value `s_u` with probability `π_u`. Everything below is a statement
about `S` and `T`; the subscripted `s_u`, `t_v` are just their atoms. `S` and `T`
are independent, because `U — X — Y — V`.

Write `f_e` for the even function

```
f_e(y) := ½[(1+y)log(1+y) + (1−y)log(1−y)] = log 2 − h₂((1−y)/2),
```

so `f_e(0) = 0`, `f_e(±1) = log 2` (one bit), `f_e` is even, convex and increasing on
`[0,1]`. `f_e` is the even part of `f(z) := (1+z)log(1+z)`, and `I(U;X)` is exactly
`E f_e(S)`. (`NOTES` elsewhere reuses the letter `f_e` for unrelated local functions
— see the notation table in §0 — but `f_e` always means this one.)

Then (verified symbolically and numerically to machine precision,
`numerics/check_kernel.py`):

```
P(u,v) = π_u ρ_v (1 + δ s_u t_v)                                     (kernel)
I(U;V) = Σ_{u,v} π_u ρ_v f(δ s_u t_v) = E f(δ S T)
I(U;X) = Σ_u π_u f_e(s_u)              = E f_e(S)
I(Y;V) = Σ_v ρ_v f_e(t_v)              = E f_e(T)
```

and `X, Y ~ Bern(1/2)` is exactly the pair of constraints `E S = 0`, `E T = 0`
(i.e. `Σ_u π_u s_u = 0` and `Σ_v ρ_v t_v = 0`). So with `S`, `T` **independent**
random variables on `[−1,1]` of mean `0`, the problem in (SF) is

> **(P)** `J(μ,ν) := sup { E f(δ S T) − μ E f_e(S) − ν E f_e(T) }`.

A BSC pair is exactly a *symmetric* two-point law, `S = ±P` and `T = ±Q` each
with probability `1/2`; since `f_e` is the even part of `f`, such a pair gives

```
J_sym(μ,ν) = max_{P,Q ∈ [0,1]} g(P,Q),     g(P,Q) := f_e(δPQ) − μf_e(P) − νf_e(Q).
```

**The conjecture is exactly `J = J_sym` for all `μ, ν ≥ 0`.**

Note `J ≤ 0` is *not* the conjecture and is in fact false: near the symmetric
locus `J_sym > 0` legitimately. The target is `J ≤ J_sym`. (An early scan
confused the two; see §6.)

### Two atoms suffice, for free

For fixed `P_T` the objective is *linear* in `P_S` over the set of probability
measures on `[−1,1]` with mean `0`, whose extreme points have at most two atoms.
So an optimal `S` has two atoms — i.e. `|U| = 2` — and likewise `|V| = 2`. For
(P) this is a remark rather than a necessity: the question already *defines* `𝒜`
with binary `U, V`, so nothing has to be reduced. (For the pointwise problem it
would need a separate argument; cf. Proposition 3 of
Dikshtein–Ordentlich–Shamai, or Proposition 4.3 of the IMAIAI paper.)

Concretely — and this is the convention used throughout the Lean development,
`Bridge.lean` and `FixedPoint.lean` — a mean-zero two-point law is

```
S ∈ {a, −b},   P(S = a) = b/(a+b),   P(S = −b) = a/(a+b),    a, b ≥ 0
T ∈ {c, −d},   P(T = c) = d/(c+d),   P(T = −d) = c/(c+d),    c, d ≥ 0
```

**the first atom is the positive one.** The weights are forced by `E S = 0`, not
chosen (`pi_false_eq`). In Lean, with `U`'s two values `false, true`:

```
a = s_false,  b = −s_true,   c = t_false,  d = −t_true
```

so `a, b, c, d ∈ [0,1]` after relabelling `U` or `V` if needed — a relabelling
sends `(a,b) ↦ (−b,−a)` and leaves the objective unchanged
(`lagrTwoPoint_neg_swap`). (P) then becomes the explicit four-variable problem
`lagrTwoPoint`, with `N := (a+b)(c+d)`:

```
J = sup_{a,b,c,d ≥ 0} [ (bd·f(δac) + bc·f(−δad) + ad·f(−δbc) + ac·f(δbd))/N
                        − μ (bf_e(a)+af_e(b))/(a+b) − ν (df_e(c)+cf_e(d))/(c+d) ].
```

The signs inside `f` are the point: the two *mixed* terms carry `−δ`, and it is
their imbalance that the odd part `Ω` measures (§5e).

## 3. What is provable

Fix the `T`-side and set `G(s) := E_T f(δ s T)`, `g := G − μf_e`.

* `G` is **convex** with `G(0) = 0` and `G'(0) = δ E[T] = 0` (indeed
  `G''(s) = δ² E[T²/(1+δsT)] > 0`), and `g(0) = 0`.
* The `S`-side optimum is the **concave envelope of `g` at `0`**, `ĝ(0)`
  (two atoms, mean zero = a chord through `0`). Dually
  `ĝ(0) = min_c max_s [g(s) − c s]`.
* If `T` is **symmetric**, then `G`, hence `g`, is **even**, and the best chord
  through `0` is the symmetric one: `ĝ(0) = max_s g(s)`, attained by a BSC.
  (This is the classical information-combining fact that against a binary
  memoryless *symmetric* channel the optimal test channel is a BSC — Remark 6
  of the Entropy paper.)

So symmetric configurations form a **closed set under alternating maximization**,
and `J_sym` is a fixed point of it. What the conjecture adds is that no
*asymmetric* fixed point does better. Every numerical probe agrees (§5).

## 3b. The moment expansion, and a quantitative bound on the gap

Since `S ⊥ T` and `(1+z) ln(1+z) = Σ_{k≥2} (−1)^k z^k / (k(k−1))`, with
`m_k := E[S^k]`, `n_k := E[T^k]` (the linear term dies because `E S = E T = 0`):

```
E f(δ S T) = Σ_{k≥2} (−1)^k δ^k m_k n_k / (k(k−1))
```

— **even** moments enter with positive coefficients, **odd** moments with
negative ones. Symmetrizing `S` (replace `S` by `εS`, `ε = ±1` uniform and
independent) kills exactly the odd moments and leaves `E f_e(S)` alone (`f_e` even).
Put

```
Q := −½ E F(δ S T) = Σ_{k odd ≥ 3} (−1)^{k+1} δ^k m_k n_k / (k(k−1)),
     F(z) := f(z) − f(−z) = (1+z)log(1+z) − (1−z)log(1−z).
```

Then, since `J` is linear in `P_S` for fixed `P_T`,

```
J(εS, T) = J(S,T) + Q,        J(−S, T) = J(S,T) + 2Q.                      (A)
```

Note `εS` is the *time-sharing midpoint* of the two feasible configurations
`(S,T)` and `(−S,T)`, so (A) is a statement about `conv 𝒜`, not about larger
alphabets. In channel language `S ↦ −S` is **mirroring** `cL` (relabelling `X`):
it preserves `I(U;X)` and sends `p ↦ 1−p`, so

```
Q = ½ [ I_{1−p}(U;V) − I_p(U;V) ].
```

Both facts are formalized: `mirror`, `mutualInfo_jointUX_mirror`,
`mutualInfo_jointUV_mirror`, `regionA_mirror`,
`even_part_mem_convexHull_regionA`. A BSC pair has `Q = 0` outright
(`mutualInfo_jointUV_bsc_flip`), which is why symmetrization is free for it.

Two consequences.

> **(B) Odd-moment anti-correlation.** At any maximizer of `J`, `Q ≤ 0`
> (otherwise `(−S,T)` beats it, by (A)). Equivalently
> `Σ_{k odd ≥3} δ^k m_k n_k / (k(k−1)) ≥ 0` fails sign — to leading order
> `m₃ n₃ ≤ 0`: the two skews point in **opposite** directions.

This is exactly what the numerics show: the best response to a skewed `T` is
skewed the other way (24 of 30 nondegenerate one-sided updates flip the sign of
`b − a`, the rest return a symmetric answer).

> **(C) Quantitative gap bound.** Symmetrizing `S` and then `T` (the second step
> changes nothing once `S` is symmetric) gives a symmetric competitor, and the
> best symmetric pair is two-point, so `J_sym ≥ J + Q` and hence
>
> ```
> 0 ≤ J − J_sym ≤ |Q| = ½ E F(δ S T) ≤ (δ − F(δ)/2) · E|S|³ · E|T|³
>                                     ≤ δ − F(δ)/2 = δ³/6 + δ⁵/20 + …
> ```
>
> using `|m_k| ≤ E|S|³` for odd `k ≥ 3` (valid as `|S| ≤ 1`) and
> `Σ_{k odd ≥3} δ^k/(k(k−1)) = δ − F(δ)/2`.

Since the bound is uniform in `(μ,ν)`, it transfers to the regions: with
`ε(δ) := δ − F(δ)/2` (nats),

```
conv 𝒜 ⊆ closure(conv ℬ) + (−ε(δ), 0, 0),
```

i.e. **the conjecture is true up to a shift of `ε(δ) = O(δ³/6)` in `R₀`.** For
`p = 0.3` (`δ = 0.4`) this is `0.011` nats `= 0.016` bits; for `p = 0.4` it is
`0.0014` nats. It degrades to `1 − log 2 ≈ 0.31` nats at `δ = 1`, where however
the conjecture is proved outright. Sharpening `E|S|³ ≤ E S² ≤ 2 I(U;X)` makes
the bound rate-dependent as well.

This is the first bound valid for *all* `p`, and it recovers the
`p → 1/2` regime of the Entropy paper's Theorem 1 for the hull version.

## 4. Why the easy arguments fail

**Sign-flip symmetrization does not work.** Replacing `S` by `εS` with `ε = ±1`
uniform and independent leaves `E f_e(S)` unchanged (f_e even) and replaces
`E f(δST)` by `E f_e(δST)` — but

```
E f_e(δST) = ½ [ J(S,T) + J(−S,T) ],
```

the *average* of two feasible configurations, never more than their max. The
`Z`/`S`-channel gain is precisely this: `J(S,T) > J(−S,T)` for the good sign.
Any proof must compare the asymmetric optimum with a *different* symmetric
configuration, not with its own symmetrization.

**The chord decomposition localizes the problem but does not close it.** Split
`g = ψ + G_o` into even and odd parts (`ψ = G_e − μf_e`). The chord through `0`
with atoms `−a, b` has value

```
[b ψ(a) + a ψ(b)] / (a+b)  +  ab [ G_o(b)/b − G_o(a)/a ] / (a+b).
```

The first term is a weighted average of `ψ(a), ψ(b)`, so it is `≤ max_s ψ(s)`,
the symmetric value for that `ψ`. Everything therefore hinges on the sign of the
second, odd, term. With `F(z) := f(z) − f(−z)` one has
`G_o(s) = ½ E_T F(δ s T)` and `F'' (z) = −2z/(1−z²)`, so `F` is concave on
`[0,1)` and `F(z)/z` is decreasing there. If `T` were supported on `[0,1]` this
would force `G_o(x)/x` decreasing and the odd term `≤ 0` whenever `b ≥ a` — but
`T` has mean zero, so it straddles `0` and `G_o` mixes concave and convex pieces.
No sign is available in general, and reflecting `S` flips the odd term's sign,
so one may always take it `≥ 0`. This is exactly the room the `Z`/`S` channels
exploit pointwise.

**Lagrangian swap is strictly lossy.** Applying duality on both sides and
exchanging `sup` and `min`,

```
J ≤ min_{c,d} max_{s,t} [ f(δ s t) − μf_e(s) − νf_e(t) − c s − d t ] =: min_{c,d} M(c,d).
```

`M` is convex and `M(c,d) = M(−c,−d)` (because `Φ(s,t) := f(δst) − μf_e(s) − νf_e(t)`
satisfies `Φ(−s,−t) = Φ(s,t)`), so the minimum is at `c = d = 0`, giving

```
J ≤ max_{s,t} [ f(δ s t) − μ f_e(s) − ν f_e(t) ],
```

which is the relaxation that *drops the mean-zero constraints* (i.e. drops
`X ~ Bern(1/2)`; cf. the closing remark of the MO 213084 answer). It uses `f`
where `J_sym` uses `f_e`, and the gap `f − f_e` is exactly the odd part again. So
this bound is strictly weaker than needed.

## 5. Numerical status

Three independent probes, all in `numerics/`:

1. **Support-function scan** (`support_gap.py`): 726 combinations of
   `p ∈ [0,0.45]` and `μ,ν ∈ [0.05,0.95]`. Largest `J − J_sym` observed:
   `3.5·10⁻⁶` bits, at optimizer tolerance, and the maximizing general pair is a
   BSC pair in every direction.
2. **LP membership** (`convex_hull_lp.py`): 3392 sampled points of `𝒜`
   (random channel pairs plus deliberately Z/S-like ones) across
   `p ∈ [0,0.4]`; every single one lies in `conv ℬ` by an exact LP over a BSC
   grid. Zero failures.
3. **Violation maximization** (`convex_hull_lp.py`, `max_violation`): global
   search (differential evolution) over all four channel parameters maximizing
   `R₀ − (concave envelope of ℬ at (R₁,R₂))`. Maximum found: `≤ 1.1·10⁻¹⁴` bits
   for every `p` tested, i.e. nothing beyond floating point.

Contrast with the *pointwise* problem: at `p = 0`, `C_u = C_v = 0.4` bits,
general channels reach `0.19539` versus `0.18950` for BSCs (the MO 213084
counterexample) — but the envelope of `ℬ` at that point is `0.4`. The Z/S gain
lives strictly inside the non-concave part of the rate region.

## 5b. Fixed points of the alternating maximization

A cleaner target than "the maximizer is symmetric": *every fixed point of the
alternating maximization is symmetric*. That suffices, since the global maximum
is such a fixed point. Two things are known.

* **No half-symmetric fixed points** (proved, §3): if one side is symmetric the
  other side's best response is symmetric. So an asymmetric fixed point must be
  asymmetric on *both* sides.
* **None found.** A census of 980 runs — 7 values of `p`, 7 pairs `(μ,ν)`,
  20 initializations each including deliberately Z/S-like ones with an atom
  pinned at the boundary `s = ±1` — converged only to symmetric or degenerate
  (`S ≡ 0`) fixed points. Zero asymmetric ones (`numerics/fixed_points.py`).

The Z/S channels are *not* a counterexample to this: they are stationary points
of the **constrained** problem, sitting in the non-concave part of the rate
region, not fixed points of the Lagrangian alternating maximization. That
distinction is precisely why the pointwise claim is false while the hull claim
appears true.

Attempted mechanism: the one-sided update flips the sign of the skew
`E[S³] = ab(b−a)` (24/30 nondegenerate cases; the rest return skew `0`), and the
two-step map contracts `|skew|` in 99.8% of 633 sampled cases, median ratio
`0.000`. Raw-skew contraction is **not uniform** (worst observed two-step ratio
`1.87`), so a naive contraction-mapping argument fails. The linearization at the
optimum, §5c, does work.

## 5c. Local analysis at the double-tangency points

Fix a symmetric fixed point `S = ±s`, `T = ±t`, `x := δ s t`, and perturb `T` off
symmetry: atoms `−(t−η), t+η` with the mean-zero weights, `ε := η/t`. Then

```
g_T(σ) = [ f_e(δσt) − μf_e(σ) ] + (ε/2)·w(δσt) + O(ε²),
w(z) = 2z − log((1+z)/(1−z)) = 2(z − artanh z)          (proved by direct expansion)
```

The perturbation is **odd**. Consequences, all first order in `ε`:

* `h'` is *even*, so the two tangency conditions `g'(p₊) = g'(p₋)` give
  `u₊ = u₋ =: u`: the touching interval **translates rigidly** rather than
  stretching, and the new skew is `skew_S = 2u`.
* The chord condition then yields the closed form

  ```
  skew_S = −Λ · skew_T ,   Λ = ψ(x)/(s·t·m) ,   m = μ/(1−s²) − (δt)²/(1−x²) = −G''(s) > 0
  ψ(x) := x − artanh x + x³/(1−x²) = Σ_{k odd ≥ 3} (1 − 1/k) x^k .
  ```

* `ψ > 0` on `(0,1)` by that series, so **`Λ > 0`: the sign flip is proved**, not
  just observed.

Composing the two sides, a fixed point with nonzero skew requires exactly
`ΛΛ' = 1`. Substituting the stationarity relations
`μ = δt·artanh(x)/artanh(s)`, `ν = δs·artanh(x)/artanh(t)` turns this into an
explicit three-variable condition on `(s, t, x)` with `x ≤ st`:

```
ΛΛ' = ψ(x)² / (s·t·x²·A·B),
A = artanh(x)/((1−s²)artanh(s)) − x/(s(1−x²)),
B = artanh(x)/((1−t²)artanh(t)) − x/(t(1−x²)).
```

**Verdict** (`numerics/skew_stability.py`): over 7421 *genuine* symmetric global
optima — `J > 0` and `(s,t)` maximizing the symmetric problem for its induced
`(μ,ν)` — `sup ΛΛ' = 6.2·10⁻⁴`, four orders of magnitude below the bifurcation
threshold. **No asymmetric branch bifurcates from the optimum**: it is locally
unique and strongly attracting.

Values `ΛΛ' > 1` do occur (up to `≈ 1.5`), but only at stationary points that
are *not* global optima — coordinatewise maxima that are saddles of the joint
problem, or points with `J < 0` where the trivial pair wins. They are precisely
the objects the alternating maximization never settles on.

Two traps worth recording. The optima sit at `s, t ≈ 0.998` (one side nearly
noiseless, `U ≈ X`), so any grid on `[0, 0.96]` misses them entirely and
reports, falsely, that all interior stationary points are saddles with `J ≤ 0`;
sample in `artanh` coordinates. And the optimum is *not* exactly at the corner
— restricting to `U = X` exactly loses up to `≈ 9·10⁻⁵` bits, so the problem
does not collapse to a one-sided information bottleneck.

## 5d. Local rigidity is a theorem

The three-variable inequality of §5c is provable. Throughout, for `y ∈ (0,1)`,

```
L(y) := artanh y,   f_e(y) := ∫₀^y L = ½[(1+y)log(1+y) + (1−y)log(1−y)],
g(y) := (1−y²)L(y)/y,   R(y) := f_e(y)/(y L(y)),   Q(y) := (1−y²)L(y)²/f_e(y),
```

so that **`g = Q·R` identically**. Recall `x = δst`, `G := g(x)`,
`κ_y := G/g(y) − 1`, and that the value constraint `J > 0` reads
`R(s) + R(t) < R(x)`.

> **Theorem.** Let `s, t ∈ (0,1)`, `δ ∈ (0,1]`, `x = δst`, and suppose
> `R(s) + R(t) < R(x)`. Then `ΛΛ' < x² < 1`. In particular no asymmetric
> branch bifurcates from a symmetric fixed point of positive value.

*Proof.*

**0. Reduction.** From `(1−x²)L(x) = x·g(x)` one gets `ω = x(1−G)` and
`W(y) = x(G/g(y) − 1)`, hence `ΛΛ' = (1−G)²/(x²·κ_s·κ_t)`.

**1.** `g(y) = 1 − 2Σ_{k≥1} y^{2k}/(4k²−1)`, so `g` is strictly decreasing with
`g(0⁺) = 1`, `g(1⁻) = 0`. Since `Σ_{k≥1} 1/(4k²−1) = ½` (telescoping,
`1/(4k²−1) = ½[1/(2k−1) − 1/(2k+1)]`) and `y^{2k} ≤ y²`,

```
0 ≤ 1 − g(y) ≤ y².
```

**2.** `x = δst < s` and `x < t`, so by monotonicity `g(s), g(t) < G`, i.e.
`κ_s, κ_t > 0`.

**3.** `κ_s κ_t ≥ 1 ⟺ G ≥ g(s) + g(t)` — expand: `(G/u−1)(G/v−1) ≥ 1` is
`G² − G(u+v) + uv ≥ uv`, i.e. `G ≥ u+v`.

**4. (Key) `Q` is strictly decreasing on `(0,1)`.** Indeed

```
(log Q)'(y) = −2y/(1−y²) + 2/((1−y²)L) − L/f_e  <  0
   ⟺  2f_e(1 − yL) < (1−y²)L².
```

If `yL ≥ 1` the left side is `≤ 0 <` the right side. If `yL < 1`, use `f_e ≤ yL/2`
— valid because `artanh` is convex on `[0,1)` (`L'' = 2y/(1−y²)² > 0`), so its
integral lies below the chord from `(0,0)` to `(y, L(y))`. Then it suffices that
`yL(1−yL) < (1−y²)L²`, i.e. `y(1−yL) < (1−y²)L`, i.e. `y − y²L < L − y²L`, i.e.
`y < artanh y` — true on `(0,1)`. ∎

**5.** By step 4 and `s, t > x`: `Q(s), Q(t) ≤ Q(x)`. Hence, using `R > 0` and
the constraint,

```
g(s) + g(t) = Q(s)R(s) + Q(t)R(t) ≤ Q(x)[R(s) + R(t)] < Q(x)R(x) = g(x),
```

so `κ_s κ_t > 1` by step 3.

**6.** By step 1, `(1−G)² ≤ x⁴`, so `ΛΛ' = (1−G)²/(x²κ_sκ_t) < x⁴/x² = x² ≤ (st)² < 1`. ∎

Two remarks. The bound `ΛΛ' < x²` is rigorous but loose: numerically
`max ΛΛ'/x² ≈ 1.3·10⁻³` over the feasible region, consistent with the observed
`sup ΛΛ' = 6.2·10⁻⁴`. And the proof explains *why* the value constraint is
indispensable: it enters only at step 5, and without it `sup ΛΛ' = 4`.

All steps are verified numerically in `numerics/local_rigidity.py` (`Q` strictly
decreasing, `g = Q·R`, `f_e ≤ yL/2`, the key inequality, and the final bound).

**This theorem is formalized**, in `Rigidity.lean`. Since Mathlib defines
`Real.artanh` but provides no derivative API for it, the file first builds a
minimal calculus layer (`hasDerivAt_artanh`, `hasDerivAt_fe`), then proves
`y < artanh y` (`self_lt_artanh`), the trapezoid bound `f_e(y) < y·L(y)/2`
(`fe_le_half_mul`), the identity `g = Q·R` (`gFun_eq_Qfun_mul_Rfun`), step 1
(`one_sub_gFun_lt_sq`, `gFun_lt_one`), step 4 (`two_fe_mul_lt`,
`Qfun_strictAntiOn`), step 5 (`gFun_add_lt`), step 3 (`kappa_prod_gt_one`) and
step 6 (`lambda_prod_lt`, `lambda_prod_lt_one`). Two deviations from the text
above, both harmless: step 1 is proved from `y < artanh y` directly rather than
from the power series, and `x < s`, `x < t` are taken as hypotheses instead of
being derived from `x = δst` (`δ ≤ 1`), which is where they come from anyway.
Everything else — including that the value constraint is used at exactly one
step — is as written.

What remains: this is the *linearization*, so it rules out asymmetric fixed
points near symmetric ones and any bifurcation from them. It does not exclude a
far-away asymmetric fixed point; the census of §5b found none.

## 5e. Going global: the sign/magnitude split

`F` is **bilinear** in the pair of laws `(P_S, P_T)`:

```
F(P,Q) = ∬ f(δst) dP(s) dQ(t) − μ⟨f_e,P⟩ − ν⟨f_e,Q⟩,   f(z) = (1+z)log(1+z),
```

on the convex set of mean-zero measures on `[−1,1]`, whose extreme points are
the two-point laws — which is why "two atoms suffice" (§2), and why the
maximum is attained at an extreme point of each factor.

Split `f` into its even and odd parts, `f = f_e + f_o`:

```
f_o(z) = ½[(1+z)log(1+z) − (1−z)log(1−z)],
```

and write `R = |S|`, `Q = |T|`. Because `f_e` is even, `f_e(δST) = f_e(δRQ)` and
`f_e(S) = f_e(R)`, so with `g(r,q) := f_e(δrq) − μf_e(r) − νf_e(q)`:

> **Proposition 1 (split).** `F(S,T) = E[g(R,Q)] + Ω`, where `Ω := E[f_o(δST)]`.

The first term sees only the magnitudes; the second is the entire sign content.

> **Proposition 2.** `J_sym = max_{(r,q) ∈ [0,1]²} g(r,q)`.

A symmetric pair `S = ±s`, `T = ±t` has `Ω = 0` and `E g = g(s,t)`. Conversely
`E[g(R,Q)]` is bilinear in the pair of *magnitude* laws, whose constraint set is
all of `𝒫([0,1])` — no mean-zero constraint survives on the magnitudes — and its
extreme points are point masses. **So randomizing the magnitudes never helps:
the symmetric problem is exactly the sign-blind problem.** Combining:

> **Corollary 3 (exact reformulation).** `J = J_sym` **iff** for every
> independent mean-zero pair on `[−1,1]`
>
> ```
> Ω  ≤  max g − E[g(|S|,|T|)]        (odd gain ≤ Jensen slack).
> ```

Both sides vanish for a symmetric pair with deterministic magnitude, and both
are quadratic in a perturbation of it — the comparison of those two quadratics
*is* §5d.

### `Ω` has no linear part

Put `W(u) := δu − f_o(δu) = Σ_{k odd ≥ 3} (δu)^k/(k(k−1)) ≥ 0`. Since
`f_o(δST) = sign(S)sign(T)·f_o(δ|S||T|)` and `sign(S)|S| = S`, the linear piece
contributes `δ·E[S]·E[T] = 0`:

> **Proposition 4.** `Ω = −E[ sign(S)·sign(T)·W(|S||T|) ]`.

> **Corollary 5 (global gap bound).** `0 ≤ J − J_sym ≤ max_{u∈[0,1]} W(u)
> = δ − f_o(δ) = δ³/6 + δ⁵/20 + …`

This is §3b's `O(δ³/6)` bound with a two-line proof, in closed form, and valid
at *every* pair rather than only at an optimum.

### The global sign flip

For a two-point pair `S ∈ {a,−b}`, `T ∈ {c,−d}` (weights forced by mean zero),
Proposition 4 expands. With `w(u) := W(u)/u`, `λ := ab/(a+b)`, `κ := cd/(c+d)`:

```
Ω = −λκ·[ w(ac) − w(ad) − w(bc) + w(bd) ] .
```

The bracket is the mixed second difference of the kernel `(r,q) ↦ w(rq)` over
`[b,a]×[d,c]`. And that kernel is **strictly supermodular**: the identity

```
f_o(z) − z·f_o′(z) = artanh z − z            (∗)
```

gives `w′(u) = (artanh(δu) − δu)/u²`, hence

```
∂²/∂r∂q  w(rq)  =  (1/r)·d/du[ u·w′(u) ]|_{u=rq} ,   u·w′(u) = artanh(δu)/u − δ ,
```

which is increasing exactly because **`z ↦ artanh z / z` is increasing**, i.e.
exactly because `artanh z < z/(1−z²)` — the same elementary inequality that
`Rigidity.lean` already proves as `artanh_lt_div`. Therefore:

> **Theorem 6 (global sign flip).** `Ω > 0` **iff** `(a−b)(c−d) < 0`, and
> `Ω = 0` iff `a = b` or `c = d`.
>
> Consequently, at any maximizer `Ω ≥ 0` (otherwise `S ↦ −S` strictly
> increases `F`), so **the two skews always point opposite ways.**

This is the global form of §5c, which had only the linearized sign flip. It is
formalized in `SignFlip.lean` (`omegaTwoPoint_neg`, `omegaTwoPoint_pos`), on top
of `wFun_mixed_diff_pos` and `artanh_div_strictMonoOn`.

Identity (∗) is worth recording on its own: with `f_o′(z) = 1 + ½log(1−z²)`,

```
f_o(z) − z(1 + ½log(1−z²)) = ½log(1+z) − ½log(1−z) − z = artanh z − z.
```

### Why this does not yet close it

Corollary 3 is an equivalence, not a bound, and the obvious ways to bound `Ω`
are all lossy in the same place. The crude `|Ω| ≤ E[W(|S||T|)]` (Corollary 5)
ignores the mean-zero cancellation entirely; sharply,

```
sup{ ∫φ dP̃ : |P̃| ≤ P, ∫r dP̃ = 0 }  =  min_c ∫ |φ(r) − c·r| dP(r)
```

(LP duality), where `P` is the law of `|S|` and `P̃` its signed version. For a
point mass this is `0`, as it must be — but every bound that drops the `min_c`
is positive there, exactly where the Jensen slack vanishes, so it can never
close. Any successful argument has to keep the cancellation: near the symmetric
optimum `Ω` is quadratic in the perturbation (one factor of skew from each
side), and so is the slack, and the whole question is the constant — which is
`ΛΛ' < 1`, i.e. §5d.

## 5f. The global skew mechanism, and what the contraction needs

Write the best response on the `S` side as an optimization over the *centre* and
the *half-gap* of the atom pair: for `T ∈ {c,−d}` and

```
G(y) = E_T f(δyT) − μf_e(y),
V(u,v) = [ (u−v)·G(v+u) + (u+v)·G(v−u) ] / (2u)
```

the pair `{v+u, v−u}` is mean-zero with weights `(u−v)/(2u)`, `(u+v)/(2u)` and
`V` is its value, so the best response is `max_{u,v} V`. Stationarity in both
variables is equivalent to bitangency: with `A = G(v+u)`, `B = G(v−u)`,
`A' = G′(v+u)`, `B' = G′(v−u)`,

```
∂V/∂v = [ −A + (u−v)A' + B + (u+v)B' ] / (2u),
∂V/∂u = [ v(A−B) + u((u−v)A' − (u+v)B') ] / (2u²),
```

and eliminating gives `(u²−v²)·(A' − B') = 0`, i.e. `G′(a) = G′(−b)`, which with
`∂V/∂v = 0` is the chord condition. Symmetry is `v = 0`.

Split `G = G_e + O` into even and odd parts. With `w_c = d/(c+d)`,
`w_d = c/(c+d)`, `κ = cd/(c+d)` — so `w_c·c = w_d·d = κ` — the even part
`G_e(y) = E_{|T|}[f_e(δy|T|)] − μf_e(y)` is blind to the skew and

```
O(y) = w_c·f_o(δcy) − w_d·f_o(δdy) = κ·y·[ w(dy) − w(cy) ],       (†)
```

where `w(u) = W(u)/u` as in §5e; the linear parts cancel because `w_c c = w_d d`.
Since `w` is even and strictly increasing in `|u|` (its derivative is
`(artanh(δu) − δu)/u² > 0`, i.e. `y < artanh y` again), `O(y)` has the sign of
`y·(d−c)` **for every** `y` — the tilt never changes direction.

The force that moves the centre off symmetry is

```
∂V/∂v |_{v=0} = O′(u) − O(u)/u = κ·[ M(du) − M(cu) ],   M(z) := artanh(δz)/z − δ,
```

(the first equality is a direct computation from `V`; the second follows from
(†) and the identity `f_o(z) − z·f_o′(z) = artanh z − z` of §5e). By
`M` strictly increasing — which is again exactly `artanh z/z` increasing, i.e.
`artanh z < z/(1−z²)` — this force has the sign of `d − c` **for every `u > 0`**.
So §5c's "the touching interval translates, in a definite direction" is now
unconditional, not linearized.

All of this is formalized in `Contraction.lean`: `wFun_strictMonoOn`,
`oddPart_eq`, `oddPart_pos`, `oddPart_deriv_sub_eq`, `forceFun_pos` for the odd
part and the force; and `envVal`, `hasDerivAt_envVal_v`, `hasDerivAt_envVal_u`,
`stationary_imp_bitangent`, `envVal_deriv_v_zero_of_split`,
`envVal_deriv_v_zero_eq_forceFun` for the `V`-calculus above — including that
the even part of `G` cancels out of `∂V/∂v|_{v=0}` entirely, so the force *is*
`forceFun`.

Sanity check on the linearization. Expanding the stationarity conditions to
first order gives `∂²V/∂v²|_{v=0} = G_e″(u) − 2G_e′(u)/u`, which at `u = u₀ =
argmax G_e` is `−m`; hence `v ≈ Φ(u₀)/m` and

```
Λ·Λ' = ψ(x)² / (s²t²·m_S·m_T) ,
```

reproducing §5c/§5d exactly (`M′(st) = ψ(x)/(st)²` with
`ψ(x) = x/(1−x²) − artanh x`, and the individual `Λ`s differ from §5c's by the
skew normalization, which cancels in the product).

### What the global contraction still needs

`numerics/skew_contraction.py` measures the exact map on 362 positive-value
configurations sampled in artanh coordinates:

| quantity | max |
| --- | --- |
| one-step ratio `\|skew S\|/\|skew T\|` (atom gap) | `1.375` |
| two-step ratio `\|skew T'\|/\|skew T\|` (atom gap) | `0.026` |
| one-step ratio (third moment) | `1.357` |
| two-step ratio (third moment) | `0.079` |
| sign-flip violations | `0` |

So the one-step map is **not** a contraction — consistent with §5d, which bounds
only the product `ΛΛ'` — while the two-step map contracts by a factor `≲ 0.08`,
far below the `< 1` that rigidity needs.

What is missing is quantitative: a global bound on `|v|` in terms of the input
skew. The mechanism above gives the numerator (the force `Φ(u)`, now signed and
explicit) but not the denominator: one needs `∂²V/∂v² ≤ −m < 0` uniformly along
the path, with `m` controlled by the value constraint the way §5d controls it at
a symmetric point. Where §5d used `R(s)+R(t) < R(x)` at exactly one step, a
global argument has to use it along the whole trajectory.

## 5g. Rate-matched symmetrization: an identity, and a refuted route

Summary up front: the **identity** below is correct and useful, and it exhibits
Mrs. Gerber's Lemma as one of the two slack terms — which turns out to be
already proved (see below). But the inequality it was meant to support, **(RM),
is false**, with an explicit counterexample. Recording both.

Once `S` is optimized out, write

```
Φ(T) := sup over mean-zero S of [ E f(δST) − μ E f_e(S) ] ,   F = Φ(T) − ν E f_e(|T|).
```

Let `t ∈ [0,1]` be the **rate-matched** symmetric partner of `T`, i.e.
`f_e(t) = E f_e(|T|)`. Replacing `T` by `±t` leaves the `ν` term untouched, and
`Φ(±t) = max_s [f_e(δst) − μf_e(s)] = max_s g(s,t)`. So

> **(RM)** `Φ(T) ≤ Φ(±t)` for every mean-zero `T`
>
> would imply `F ≤ max_s g(s,t) ≤ max g = J_sym`, i.e. **the conjecture**.

(RM) is *not* the pointwise claim `I(U;V) ≤ log 2 − h(a∗p∗b)`, which fails by the
Z-channel: here the `S` side is optimized out, and that optimization was meant
to absorb the Z-channel gain. It does not absorb enough — see below.

### The identity

Put `A_t(s) := f_e(δst) − μf_e(s)`. Then, exactly,

```
max_s A_t(s) − [ E f(δST) − μ E f_e(S) ]  =  Σ_S + Σ_T − Ω,

Σ_S := max_s A_t(s) − E[ A_t(|S|) ]                                 ≥ 0,
Σ_T := E_{|S|}[ f_e(δ|S|t) − E_{|T|} f_e(δ|S||T|) ]                     ≥ 0,
Ω   := E[ f_o(δST) ]        (as in §5e).
```

*Proof.* `E f(δST) = E[f_e(δ|S||T|)] + Ω` (§5e) and
`E[A_t(|S|)] = E[f_e(δ|S|t)] − μ E f_e(|S|)`; substitute. ∎

`Σ_S ≥ 0` is "max ≥ average". `Σ_T ≥ 0` is **Mrs. Gerber's Lemma** applied at
parameter `δ|S|`: the map `r ↦ f_e(δ|S|·f_e⁻¹(r))` is concave and
`E f_e(|T|) = f_e(t)` by construction, so Jensen applies. Hence

> **(RM) ⟺ `Ω ≤ Σ_S + Σ_T` for all mean-zero `S`, `T`.**

The slack is now split into two *explicit, separately non-negative* pieces, one
per side: `Σ_S` is a Jensen gap in the `|S|` law, `Σ_T` an MGL gap in the `|T|`
law, and `Ω` is bilinear in the two skews. No dynamics, no fixed points, no
concave envelopes.

### Mrs. Gerber's Lemma is already proved

Its second-derivative form is elementary. With `κ := δ|S|`, `q := f_e⁻¹(r)`,

```
Θ_κ(u) = f_e(κ·f_e⁻¹(u)),   Θ_κ''(u) = κ·[ κ·L(q)/(1−(κq)²) − L(κq)/(1−q²) ] / L(q)³,
```

so `Θ_κ'' ≤ 0` is exactly `κ(1−q²)L(q) ≤ (1−(κq)²)L(κq)`. Dividing by `κq > 0`
this reads `g(q) ≤ g(κq)` with `g(y) = (1−y²)L(y)/y` — and `κq < q`, so it is
precisely **`g` decreasing**, i.e. `gFun_strictAntiOn`, already proved in
`Rigidity.lean` for the local-rigidity theorem. Formalized as `mgl_bias` in
`MGL.lean`. (Packaging it as concavity of `Θ_κ`, hence `Σ_T ≥ 0` via Jensen,
additionally needs `f_e⁻¹` as a differentiable function — not formalized.)

### (RM) is false

`numerics/rate_matched.py` tests (RM) directly, and
`numerics/rm_counterexample.py` re-checks the violation on a 12 000-point grid
with Nelder–Mead polish and the rate matching solved by bisection:

```
δ = 0.994712945387,  μ = 0.768497935293,
T ∈ {c, −d},  c = 0.804518249404,  d = 0.999983353638,
E f_e(|T|) = 0.515718514362 = f_e(t),   t = 0.913958200832,

Φ(T)  = 0.014037097  >  Φ(±t) = 0.012046858 ,     gap = +1.990e-3 .
```

Grid maxima only ever *under*-estimate a maximum, so refinement cannot create
such a gap; it survives every refinement tried. **(RM) fails**, and equivalently
`Ω ≤ Σ_S + Σ_T` fails — for the *optimal* `S`, which is the case the equivalence
needs.

Caution about a near-miss: `numerics/two_slack.py` samples `S` at random and
reports `Ω ≤ Σ_S + Σ_T` throughout, with `max Ω/(Σ_S+Σ_T) ≈ 0.90`. That is not
evidence for (RM) — random `S` essentially never hits the maximizer, and the
equivalence quantifies over *all* `S`. The scripts are kept because the identity
check (max error `2.8e-16`) and the `Σ_T ≥ 0` check (min `1.1e-14`, MGL) are
still meaningful.

Since `E f_e(|T|) = f_e(t)`, the `ν` term is identical for `T` and `±t`, so the
asymmetric `T` beats its rate-matched symmetric partner **for every `ν`**. This
does not contradict the conjecture: the optimal `T` need only be compared with
*some* symmetric pair, not with its rate-matched partner. Indeed at
`δ = 0.994713`, `μ = 0.768498` the conjecture holds exactly —
`J − J_sym = 0` to machine precision for `ν ∈ {0.05, 0.2, 0.4, 0.6, 0.8, 0.95}`.

### What survives

* The identity is exact and unconditional.
* `Σ_T ≥ 0` is Mrs. Gerber's Lemma, and its differential form is
  `gFun_strictAntiOn`, already proved — see above. This is the most reusable
  thing to come out of the section, and it is **now formalized in full Jensen
  form** (`mgl_jensen`), see §5i.
* The identity still gives the valid bound
  `J − J_sym ≤ sup (Ω − Σ_S − Σ_T)`; it is just not `≤ 0`.

The moral for the remaining routes: **rate-matched one-sided symmetrization is
not value-preserving**, so no argument may assume that replacing one side by the
BSC of equal rate is free. Together with §5e (plain sign-randomization loses
exactly `Ω`) that rules out both of the obvious symmetrization moves.

## 5h. The conditional-MI form: two parameters instead of four

`U — X — (Y,V)` is Markov, so `I(U;X,V) = I(U;X)` and therefore
`I(U;V) = I(U;X) − I(U;X|V)`. Hence

```
F = (1−μ)·I(U;X) − I(U;X|V) − ν·I(Y;V).                                  (‡)
```

**Immediate consequence: `μ ≥ 1` and `ν ≥ 1` are settled.** All three terms of
(‡) are then `≤ 0`, so `F ≤ 0 = g(0,0) ≤ max g = J_sym`, and `J ≥ J_sym` always.
So `J = J_sym` whenever `μ ≥ 1` or `ν ≥ 1`, and **WLOG `μ, ν ∈ [0,1)`**.

### Halving the dimension

Given `V = v`, the input `X` has bias `δ t_v` and the channel `P(u|x)` is
unchanged, so `I(U;X|V) = E_T[C(δT)]`, where

```
C(β) := I( Bern((1+β)/2), W )
```

is the channel's MI-versus-input-bias curve. For a binary channel with
conditional biases `v₀` (given `x=0`) and `v₁` (given `x=1`),

```
C(β) = A + Bβ − f_e(m + kβ),
A = (f_e(v₀)+f_e(v₁))/2,   B = (f_e(v₀)−f_e(v₁))/2,   m = (v₀+v₁)/2,  k = (v₀−v₁)/2.
```

`B` multiplies `E[T] = 0`, so **the odd part of the channel drops out**.
Substituting into (‡) and optimizing over `T`:

> ```
> F_opt(v₀,v₁) = −μ·A − (1−μ)·f_e(m) + conc(ζ)(0),   ζ(y) = f_e(m + kδy) − νf_e(y),
> ```
>
> where `conc(·)(0)` is the concave envelope at `0`, i.e. the sup over mean-zero
> `T` of `E ζ(T)`.

Two parameters plus a one-dimensional concave envelope, in place of four
parameters. Symmetry is `m = 0` (`v₁ = −v₀`), and then `ζ` is even, so
`conc(ζ)(0) = max_y ζ(y)` and `F_opt = max_y g(v₀, y)` as it should be.

The translation to the bias parametrization is Bayes:
`S = {k/(1+m) w.p. (1+m)/2, −k/(1−m) w.p. (1−m)/2}`.

Verified in `numerics/channel_form.py`: `C` against a direct mutual-information
computation (max error `2.4e-16`), `F_opt` against the four-parameter form
(`2.2e-16`), and `μ ≥ 1 ⟹ F ≤ 0`.

### Why this looks like the better line of attack

Asymmetry now costs in exactly two identifiable places, and both have a sign:

1. the explicit penalty `−(1−μ)f_e(m) < 0` for `m ≠ 0` (recall `μ < 1` is WLOG);
2. the shift `m` inside `ζ(y) = f_e(m + kδy) − νf_e(y)`, which is what breaks the
   evenness of `ζ` and hence separates `conc(ζ)(0)` from `max_y ζ(y)`.

So the conjecture becomes: for all `(v₀,v₁) ∈ [−1,1]²`,

```
conc(ζ)(0) − max_y ζ_sym(y)  ≤  μ[A − f_e(k_sym)] + (1−μ)f_e(m)
```

against a suitable symmetric comparison — i.e. **the gain from the asymmetric
shift must not exceed the explicit asymmetry penalty.** Unlike §5e–§5g, both
sides are now one-dimensional objects attached to a two-parameter family, and
neither side involves the `S`/`T` interaction that defeated the earlier bounds.

## 5i. Two results proved along the way

**`μ ≥ 1` and `ν ≥ 1` are settled.** In bias coordinates this needs only data
processing, which has a two-line proof: `f(z) = (1+z)log(1+z)` is convex, so on
`[−a,a]` it lies below its chord `f_e(a) + z·fo(a)/a`; since `δsT` is mean-zero and
stays in `[−|s|,|s|]`, averaging gives `E_T f(δsT) ≤ f_e(s)`, and averaging again
gives `E f(δST) ≤ E f_e(S)`, i.e. `I(U;V) ≤ I(U;X)`. Then
`F ≤ (1−μ)Ef_e(S) − νEf_e(T) ≤ 0 ≤ J_sym`. Formalized in `Lagrangian.lean`
(`fFun_le_chord`, `chord_expectation`, `dpi_row`, `lagrKernel_le`,
`lagrangian_nonpos_of_one_le_mu`).

**Mrs. Gerber's Lemma, in Jensen form, without `f_e⁻¹`.** The obstacle to using
`mgl_bias` was packaging it as concavity of `Θ_κ(u) = f_e(κ·f_e⁻¹(u))`, which appears
to need `f_e⁻¹` as a differentiable function. It does not. Along the
parametrization `u = f_e(q)` the slope of the curve is `κ·L(κq)/L(q)`, so concavity
is exactly

```
mglRatio κ q = artanh(κq) / artanh q   is decreasing in q,
```

which is `mgl_bias` (`mglRatio_strictAntiOn`). And a function whose derivative
changes sign at most once, from `+` to `−`, lies above its chords: with
`H(q) = f_e(κq) − αf_e(q)` one has `H′(q) = artanh q · (κ·mglRatio κ q − α)`, so if
`H(q₁) = H(q₂)` then `H ≥ H(q₁)` on `[q₁,q₂]` (`mglH_ge_of_mem`). Applying this
at the chord slope gives

> **`mgl_jensen`**: if `w₁f_e(q₁) + w₂f_e(q₂) = f_e(t)` and `w₁ + w₂ = 1`, then
> `w₁f_e(κq₁) + w₂f_e(κq₂) ≤ f_e(κt)`.

This is exactly `Σ_T ≥ 0` of §5g, and it is the standard tool for every
`1 − H(a∗p∗b)` bound. All in `MGL.lean`.

## 5j. Working in the `(m,k)` coordinates: what fails, and one lemma that holds

Continuing route (1). Coordinates as in §5h: `m = (v₀+v₁)/2`, `k = (v₀−v₁)/2`,
`A = (f_e(m+k)+f_e(m−k))/2`, symmetry is `m = 0`, and the domain is the triangle
`m, k ≥ 0`, `m+k ≤ 1`.

### `f_e` is supermodular (proved, formalized)

> `f_e(m+k) + f_e(m−k) ≥ 2f_e(m) + 2f_e(k)`, hence `A ≥ f_e(m) + f_e(k)`.

The "shift" `m` and the "spread" `k` each cost their own rate. Since
`f_e = ∫ artanh`, this integrates the elementary

```
artanh(m+u) − artanh(m−u) ≥ 2·artanh u        (u, m ≥ 0, m+u < 1),
```

which after `artanh z = ½[log(1+z) − log(1−z)]` reduces to
`(1+u)²((1−u)²−m²) ≤ (1−u)²((1+u)²−m²)`, i.e. to `m²(1−u)² ≤ m²(1+u)²`.
Formalized as `artanh_add_sub_ge` and `fe_supermodular` in `Lagrangian.lean`.

### Two more refuted symmetrizations

Supermodularity gives `F_opt(m,k) ≤ conc(ζ_{m,k})(0) − f_e(m) − μf_e(k)`, so the
conjecture would follow from the **shift bound**

```
(SH)   conc(ζ_{m,k})(0) − conc(ζ_{0,k})(0)  ≤  f_e(m).
```

**(SH) is false** (`numerics/shift_bound.py`: `max Gain/f_e(m) = 6.01`). The
second-order reason is decisive and was clear before running it: near `m = 0`
the gain is `C₁m² + m²/(2(1−x₀²))` with `x₀ = kδy₀`, while `f_e(m) ≈ m²/2`, and
`1/(2(1−x₀²)) ≥ 1/2` already exhausts the budget with `C₁ > 0` left over. Two
things are lost: the bound `A ≥ f_e(m)+f_e(k)` (exactly `A ≈ f_e(k) + m²/(2(1−k²))`)
and, more importantly, comparing at the *same* `k` — the symmetric competitor
must be allowed to re-optimize.

Matching the penalties instead, `f_e(k′) = A + ((1−μ)/μ)f_e(m)`, gives

```
(SH′)  conc(ζ_{m,k})(0) ≤ max_y [f_e(δk′y) − νf_e(y)]     ⟺  F_opt(m,k) ≤ F_opt(0,k′),
```

the `U`-side analogue of the `V`-side rate matching refuted in §5g. **(SH′) is
also false** (`numerics/shift_matched.py`: max excess `0.665`, at `μ = 0.9947`,
`m = 0.9954`, `k = 0.0031`, where `k′ ≈ 0.9967` and the matched competitor pays
`μf_e(k′) ≈ 0.67` for almost nothing). The same run confirms the conjecture itself
on those samples (`max [F_opt − J_sym] = 4e−9`).

> **Moral, now threefold.** Rate matching on the `V` side (§5g), penalty matching
> on the `U` side, and same-`k` comparison all fail. **No local "matching"
> heuristic picks the right symmetric competitor** — a good one always exists
> (the conjecture holds numerically throughout), but it has to be found by
> optimization, not by matching a scalar. Any proof must compare against
> `max_{k′} F_opt(0,k′)`, keeping the maximization intact.

## 6. What would close it

Prove (P) `= J_sym` for all `δ ∈ [0,1]`, `μ, ν ≥ 0`. After §5h this is no longer
the four-variable problem of §2: in the conditional-MI coordinates the whole
question is **two parameters plus a one-dimensional concave envelope**,

```
F_opt(m,k) = −μ·A − (1−μ)·f_e(m) + conc(ζ_{m,k})(0),
A = (f_e(m+k)+f_e(m−k))/2,   ζ_{m,k}(y) = f_e(m + kδy) − νf_e(y),
```

on the triangle `m, k ≥ 0`, `m + k ≤ 1`, with symmetry exactly `m = 0`. So:

> **Show that `max F_opt` over the triangle is attained at `m = 0`.**

### What is settled

| Region | Status |
| --- | --- |
| `p = 1/2` (`δ = 0`) | proved in Lean, at the level of `AveragedBSCConjecture` |
| `p = 0` (`δ = 1`) | proved in Lean, at the level of `AveragedBSCConjecture` |
| `μ ≥ 1`, and `ν ≥ 1` | proved in Lean, at the Lagrangian level in bias coordinates (`lagrangian_nonpos_of_one_le_mu`); so `μ, ν ∈ [0,1)` is WLOG |
| `m = 0` locally | local rigidity `Λ·Λ' < x² < 1`, proved and formalized (§5d) |

Tools now available and formalized: Mrs. Gerber's Lemma in Jensen form
(`mgl_jensen`), the global sign flip (§5e), the signed skew force (§5f),
supermodularity of `f_e` (§5j), and data processing in bias coordinates (§5i).

### Open routes, ranked

Revised after (L2) and the two-regime split were refuted.  The one durable gain
is **(L1)**, now an unconditional theorem in Lean: `ρ(U;V) ≤ 2 − 1/log 2` for
*every* mean-zero law on `[−1,1]`, sharp.  Any route below may use it freely.

1. **A coupled bound at a single configuration.**  The target, in the sharpest
   coordinates available, is

   > `ρ(U;V) ≤ ρ(U;X) + ρ(Y;V)` at asymmetric fixed points,
   > where `ρ(A;B) = I/(I+L)` and `F = 𝒥(U;V)·[ρ(U;V) − ρ(U;X) − ρ(Y;V)]`.

   Six decoupled attempts have now failed (see the dead-end list), each because
   it bounded the two sides at *different* configurations.  So the coupling must
   be carried explicitly, and the fixed-point relations are what carry it:
   `μ·𝒥(U;X) = 𝒥(U;V) = ν·𝒥(Y;V)` with `μ, ν < 1`, plus the per-branch
   equalizer.  **Most promising.**
2. **The `γ` formulation** — attempted, not closed, but it has by far the best
   margin of any formulation tried.  `γ := conc(H)(0) ≥ 0` is the `U`-side
   envelope value and `F = γ − ν·I(Y;V)`, so the target is `γ ≤ ν·I(Y;V)`.
   Measured over 300 non-degenerate asymmetric fixed points:

   > `γ / (ν·I(Y;V))  ≤  0.368`, median `0.0056`

   — a factor `≈ 2.7` of room, against the `0.03` the `ρ`-formulation had, and
   `> 1` at symmetric fixed points of positive value, so the two families are
   cleanly separated.  **The margin survived a multi-start audit**
   (`numerics/multistart_check.py`, 6000 triples × 16 starts): the fixed-point
   set really does carry extra branches — mean `1.20` distinct roots per triple,
   max `3`, `19.4%` with more than one, so the single-start scans *were*
   incomplete — but the extra branches carry no higher ratio, and
   `sup γ/(ν·I(Y;V)) = 0.247` with every extremal point verified as a genuine
   two-sided best response.  No creep towards `1`.  Two sub-attempts, both recorded as failures:

   * **The chord bound is dead.**  `H(s) = E_T f(δsT) − μf_e(s)` has a convex
     first part and concave second, so `γ ≤ conc(E_T f(δ·T))(0) = E[f_e(δ|T|)]`,
     the chord midpoint.  Closing via it would need
     `E[f_e(δ|T|)] ≤ ν·E[f_e(|T|)]`, and that ratio has **median `10.2`, max `171`,
     and is never `≤ 1`** — the chord overshoots by an order of magnitude.
   * **The asymmetry bound `γ ≤ (μ/2)·log((1+m)²/(4m))`** (from
     `a ≤ (1−m)/(1+m)`, item 6) is slack by factors `5.8`–`39.8` at the binding
     configurations.  Useless.

   **Where the difficulty sits.**  The binding cases have *tiny* `m`:
   `m = 2.1·10⁻⁴` at the worst (`δ = 0.9905`, `a ≈ b ≈ 0.9854`,
   `c ≈ d ≈ 0.8172`, `μ = 0.357`, `ν = 0.929`), then `1.3·10⁻⁴`,
   `3.8·10⁻³`.  So the hard configurations are again *near-symmetric* — §5d's
   territory — while the strongly asymmetric ones are easy.  This is the same
   split that (L2) tried and failed to exploit, but here the margin is a factor
   of `2.7` rather than `1.01`, so a quantitative version of §5d (lemma (L3))
   would have far more room to work with.  **Still the most promising route.**
3. ~~**The two-slack identity with a variational competitor.**~~ **Collapses.**
   For an arbitrary symmetric competitor `τ` the identity reads

   > `max_s g(s,τ) − F = Σ_S(τ) + Σ_T(τ) − Ω + ν·[Ef_e(T) − f_e(τ)]` ,

   with `Σ_S(τ) = max_s A_τ(s) − E A_τ(|S|) ≥ 0`.  Rate matching kills the last
   term and makes `Σ_T ≥ 0` by MGL — that was §5g, and it failed.  But
   *optimizing* over `τ` gives `max_τ max_s g(s,τ) = J_sym`, so the free-competitor
   version is exactly `J_sym ≥ F`: **the conjecture restated**.  Bookkeeping, no
   reduction.  Remove from the list.
4. **A rigorous computer-assisted proof.**  The domain is compact, the
   neighbourhood of the symmetric branch is covered analytically by §5d, and
   (L1) is now a theorem, so one of the two bounds needed is no longer
   numerical.  Interval arithmetic / branch-and-bound on the complement would
   finish it.  After six refuted analytic comparisons this is a serious option.
5. **Pointwise `Λ ≤ conc Λ_BSC`**, `Λ_BSC(R₁,R₂) = f_e(δ·f_e⁻¹(R₁)·f_e⁻¹(R₂))`.
   Removes the supremum entirely; what `convex_hull_lp.py` tests (3392 cases, 0
   failures).  Four-dimensional, and `f_e⁻¹` is no longer an obstacle now that MGL
   is packaged.
6. **Formalize the scaffolding** — *substantially advanced*.  The **bias
   parametrization of §2 is now formalized** (`BiasCoords.lean`), for the joint
   laws `regionA` and the conjecture are actually stated with:

   > `I(U;X) = Σ_u π_u f_e(s_u)`  (`mutualInfo_jointUX_eq_bias`),
   > `P(u,v) = π_u ρ_v (1 + δ s_u t_v)`  (`jointUV_eq_kernel`),
   > `I(U;V) = Σ_{u,v} π_u ρ_v f(δ s_u t_v)`  (`mutualInfo_jointUV_eq_kernel_sum`).

   The kernel identity in particular was previously checked only numerically
   (`check_kernel.py`).  This closes the gap that made every analytic result
   here formally irrelevant to `AveragedBSCConjecture`.  What is left: the
   marginals `marg₁(jointUV) = π_u`, `marg₂(jointUV) = ρ_v` (currently
   hypotheses; they follow from the kernel identity plus `rho_bias_sum_zero`,
   so bookkeeping), then two-atoms-suffice and the support-function reduction.
7. **Product-variable view.**  Both relevant kernels depend only on `u = rq`.
   Suggestive; no lever found, and nothing new since.  Lowest priority.

### Dead ends (do not retry)

* **Plain sign-randomization**: loses exactly `Ω` (§5e).
* **Rate-matched symmetrization on the `V` side**: strictly loses; explicit
  counterexample at `δ = 0.994713`, `μ = 0.768498` (§5g).
* **Penalty-matched symmetrization on the `U` side** (`f_e(k′) = A + ((1−μ)/μ)f_e(m)`):
  strictly loses, max excess `0.665` (§5j).  This one matched the wrong
  invariant — the rate is `I(U;X) = A − f_e(m)`, not `A` — but see the next entry.
* **Rate-matched symmetrization on the `U` side** (`f_e(k″) = A − f_e(m) = I(U;X)`),
  equivalently the `μ`-free claim *"among binary `U` of given `I(U;X)`, the BSC
  maximizes `sup_V [I(U;V) − νI(Y;V)]`"*: **false**.  At
  `δ = 0.98570`, `ν = 0.31716`, `m = 0.35258`, `k = 0.61558` (so
  `I(U;X) = 0.25970`, `k″ = 0.68744`) the asymmetric channel gives `0.0432940`
  against `0.0428620` for the rate-matched BSC — an excess of `4.32e−4` that
  survives 20 000-point grids with Nelder–Mead polish on both sides
  (`numerics/rate_matched_u.py`).  Note this is *not* the `V`-side statement
  refuted in §5g: here `V` has been optimized out.
* **The shift bound** `conc(ζ_{m,k})(0) − conc(ζ_{0,k})(0) ≤ f_e(m)`: false, max
  ratio `6.01`, and it fails already at second order because `1/(2(1−x₀²)) ≥ 1/2`
  exhausts the `f_e(m) ≈ m²/2` budget on its own (§5j).
* **Monotonicity of `F_opt` in `m`**: false.
* **(L2)** `G(a,b) + G(c,d) ≥ c₀` at asymmetric fixed points with `m ≥ m₀`, and
  with it the **two-regime architecture**: false, explicit non-degenerate
  counterexample at `m = 0.0142` above.
* **Any bound on `Ω` dropping the LP-dual `min_c ∫|φ − c·r| dP`**: positive at
  point masses, exactly where the Jensen slack vanishes (§5e).
* **`W(rq) + g(r,q) ≤ max g`** as a sufficient condition: false at the maximizer
  itself (§5e).

### Structural facts available for route 1

Collected while refuting the matchings above; all cheap, and the first two are
formalizable with lemmas already in the development.

1. **DC structure.** In `(v₀,v₁)` coordinates `m + kδy` is the convex combination
   `λ(y)v₀ + (1−λ(y))v₁` with `λ(y) = (1+δy)/2`.  So for each `y` the gain
   integrand `f_e(λv₀+(1−λ)v₁)` is convex in `(v₀,v₁)` (convex ∘ affine), and
   expectation then supremum preserve convexity:

   > `conc(ζ)(0)` is **convex** in `(v₀,v₁)`, and the penalty
   > `μ(f_e(v₀)+f_e(v₁))/2 + (1−μ)f_e((v₀+v₁)/2)` is convex too.

   Both are invariant under the reflection `(v₀,v₁) ↦ (−v₁,−v₀)`, whose fixed
   set is the symmetric line `m = 0`.  A convex reflection-invariant function
   increases away from the fixed set, so **gain and penalty both increase in
   `|m|` at fixed `k`** — the whole question is which grows faster, which is why
   no one-sided bound has worked.

2. **The envelope-free form.**  Two atoms suffice for `T`, so
   `F_opt(m,k) = max_{c,d>0} Φ(m,k,c,d)` with `Φ` completely explicit:

   ```
   Φ = −μA − (1−μ)f_e(m) + [ d(f_e(m+kδc) − νf_e(c)) + c(f_e(m−kδd) − νf_e(d)) ] / (c+d).
   ```

   Differentiating at the symmetric slice,

   ```
   ∂Φ/∂m |_{m=0} = cd·[ L(kδc)/c − L(kδd)/d ] / (c+d),
   ```

   and `z ↦ artanh(αz)/z` is increasing (`artanh_div_strictMonoOn` again), so
   the sign is `sign(c−d)`.  Hence **on the symmetric slice the `m`-gradient
   vanishes exactly when the `V`-side is symmetric**: the only stationary
   configurations with `m = 0` are the fully symmetric ones.  With §5d saying
   those are local maxima in `m`, what is left is interior critical points with
   `m > 0`.

3. **The boundary splits cleanly.**  The triangle has three edges:
   * `k = 0`: then `U ⊥ X`, `A = f_e(m)`, `ζ ≡ f_e(m)`, so `F_opt ≡ 0` — a
     one-line check, and `J_sym ≥ 0` always.
   * `m = 0`: the symmetric family; this is the target, not an obstacle.
   * `m + k = 1`: `v₀ = 1`, one branch deterministic — **the Z-channel edge**,
     exactly where the pointwise counterexamples of MO 213084 live.  This is the
     only hard boundary, and it is a *one*-parameter family plus an envelope.

   So a complete proof splits as: interior critical points (item 2 plus §5d),
   and the single edge `m + k = 1`.  Solving that edge explicitly is the most
   concrete unattempted sub-problem in the whole development.

### Adding the fixed-point equations to route 1

A global maximizer is a fixed point of the alternating maximization, so its
stationarity equations may be *assumed*.  In the `(m,k,c,d)` coordinates
(`v₀,v₁ = m ± k` the biases of `U` given `X`, weights `½`; `b₁ = m+kδc`,
`b₂ = m−kδd` those given `V`, weights `w_c,w_d`; `κ = cd/(c+d)`; `L = artanh`):

```
(E1)  μ·𝔏(X) + (1−μ)·𝔏(∅) = 𝔏(V) ,   𝔏(W) := E[ L(bias of U given W) ]
(E2)  μ·[L(v₀) − L(v₁)]/2 = δκ·[L(b₁) − L(b₂)]
(E3)  kδ·[L(b₁) − L(b₂)] = ν·[L(c) + L(d)]
(E4)  f_e(b₁) − f_e(b₂) − ν[f_e(c) − f_e(d)] = (c+d)·[kδ·L(b₁) − ν·L(c)]
```

(E1) and (E2) are `∂Φ/∂m = 0` and `∂Φ/∂k = 0`, verified against finite
differences to `8.4e−11` (`numerics/fixed_point_eqs.py`); (E3) and (E4) are the
`V`-side bitangency of §5f, formalized as `stationary_imp_bitangent`.  Note
`E[b] = m` and `E[v] = m`, so (E1) is a genuine information-theoretic identity:
`μ·[𝔏(X) − 𝔏(V)] = (1−μ)·[𝔏(V) − 𝔏(∅)]`.

**What this buys.** (E3) always determines `ν`.  **Off** the symmetric slice
(E1) determines `μ`:

```
μ = [𝔏(V) − 𝔏(∅)] / [𝔏(X) − 𝔏(∅)] ,     ν = kδ[L(b₁) − L(b₂)] / [L(c) + L(d)] .
```

So an *asymmetric* fixed point satisfies **(E2) and (E4) as two parameter-free
equations in `(m,k,c,d)`** — the multipliers are gone, and with them the whole
`(μ,ν,δ)` sweep except for `δ`.  The target becomes: show that system has no
solution with `m > 0` and `μ, ν ∈ [0,1)`.  Two by-products: `μ < 1` is
*equivalent* to `𝔏(V) < 𝔏(X)` (a strict data-processing statement for `𝔏`), and
combining (E2) with (E3) gives `μk[L(v₀)−L(v₁)]/2 = νκ[L(c)+L(d)]`.

**Two caveats, both found by checking.**

* **On** the symmetric slice (E1) degenerates to `0 = 0` — it is the
  `m`-derivative, which vanishes identically there because `F_opt` is even in
  `m`.  So the `μ`-elimination above is available exactly in the case we want to
  rule out, which is convenient, but it cannot be used to re-derive the
  symmetric relations; there `μ` comes from (E2), recovering
  `μ = δtL(x)/L(k)`, `ν = kδL(x)/L(t)` of §5d.
* **Stationarity is not always the binding condition.**  Running alternating
  maximization to convergence, the maximizers frequently sit at `k → 1`, `m = 0`
  — i.e. `v₀ = 1`, `v₁ = −1`, the noiseless corner `U = X` — on the *boundary*
  of the parameter square, where `L(v₀) = ∞` and (E1)–(E2) simply do not hold.
  That corner is symmetric, so it is harmless for the conjecture, but any proof
  built on the fixed-point system must treat the boundary `max(|v₀|,|v₁|) = 1`
  separately.  This is the same edge flagged above as the hard one.

### The value at a general fixed point, and what it reveals

Two ingredients.  The envelope value at `0` is the chord's intercept, so by (E4)
`G = ζ(c) − c·ζ′(c)`; and (E2)+(E3) turn `μ·[A − m𝔏(X)]` into a `ν`-term plus
terms in `Φ*(y) := f_e(y) − y·L(y)`.  Writing `Δ := L(b₁) − L(b₂)`,
`D := L(v₀) − L(v₁)`,

```
𝑅_B := [w_cf_e(b₁) + w_df_e(b₂)] / Δ ,
𝑅_U := 2(b₁−m)·w_c·A / (k·D) ,
𝑅_V := [ (m−b₂)f_e(c) + (b₁−m)f_e(d) ] / ( [L(c)+L(d)]·(c+d) ) ,
```

one gets

> ```
> F  =  Δ·[ 𝑅_B − 𝑅_U − 𝑅_V ]  −  (1−μ)·f_e(m) .
> ```

At symmetry (`m = 0`, `c = d = t`, `k = s`) this is `Δ = 2L(x)` and
`𝑅_B, 𝑅_U, 𝑅_V = x·R(x)/2, x·R(s)/2, x·R(t)/2`, so it collapses to
`F = xL(x)[R(x) − R(s) − R(t)]` — §5d exactly.  **The general fixed-point value
is the symmetric-looking expression minus an explicit asymmetry cost
`(1−μ)f_e(m) ≥ 0`**, which vanishes iff `m = 0` (recall `μ < 1` is WLOG).  Verified
to machine precision (`numerics/fixed_point_value.py`, max error `1.2e−11`).

### Asymmetric fixed points all have non-positive value

Solving (E2),(E4) for `(c,d)` at random `(m,k,δ)` — with `μ` from (E1) and `ν`
from (E3), and keeping only solutions with `μ, ν ∈ [0,1)` — produces genuine
asymmetric fixed points in quantity.  Over **694** of them:

> **not one has `F > 0`.**  The maximum value observed is `−1.7e−13`, attained at
> a degenerate near-trivial configuration (`c,d ∼ 1e−4`, `μ ∼ 1e−9`).

Since `J_sym ≥ g(0,0) = 0` always, this says asymmetric fixed points are **never
global maximizers**.  It also dovetails exactly with §5d, which shows symmetric
fixed points of *positive* value are locally rigid: the value constraint `J > 0`
is precisely what separates the two regimes, and it is indispensable in both.

This gives a complete proof skeleton for route 1:

> **Target.** Every fixed point with `m > 0` has `F ≤ 0`; equivalently
> `Δ·[𝑅_B − 𝑅_U − 𝑅_V] ≤ (1−μ)·f_e(m)`.
>
> ⚠ **This target as literally stated is FALSE** — fixed points with
> `m ~ 1e-12 > 0` have `F > 0` (they are BSC pairs, where `F > 0` is legitimate
> because `J_sym > 0`).  It needs `m` bounded away from `0`, or better, replacing
> `F ≤ 0` by the correct `F ≤ J_sym`.  See the scope correction at the end of §6.
>
> Given that: `J` is attained by compactness; an interior maximizer is a fixed
> point; if it has `m > 0` then `J = F ≤ 0 ≤ J_sym`, and if `m = 0` it is
> symmetric so `J = J_sym`.  Either way `J = J_sym`.  What remains besides the
> target is the **boundary** `max(|v₀|,|v₁|) = 1` (and `c,d ∈ {0,1}`), where
> stationarity fails — the edge already flagged as the hard one.

This is now a statement about a two-parameter family with fully explicit
equations and an explicit value formula, which is a far better position than any
of the refuted comparisons.

### The value in normal form: two Lautum identities

The formula above simplifies decisively.  Since `f(z) − z·f′(z) = log(1+z) − z`
and `E[T] = 0`, the bitangent intercept on the `U` side collapses to

```
conc(H)(0) = E_T[ log(1 + δaT) ] − μ·Φ*(a) ,   Φ*(y) := f_e(y) − y·L(y) = −log cosh(artanh y).
```

Both pieces are recognizable.  Averaged over `u`, `E_T[log(1+δs_uT)]` is
`−L(U;V)`, minus the **Lautum information** `L(U;V) := D(P_U P_V ‖ P_{UV})`
(the reverse KL, whereas `I(U;V)` is the forward one).  Hence, at **any** fixed
point,

> ```
> μ·E[S·artanh S]  =  ν·E[T·artanh T]  =  I(U;V) + L(U;V)  =:  𝒬  ≥ 0 ,
> ```

and, with `ℛ(S) := E[f_e(S)] / E[S·artanh S]` and `ℛ_V := I(U;V)/𝒬`,

> ```
> F  =  𝒬 · [ ℛ_V − ℛ(S) − ℛ(T) ] .
> ```

**No extra term.**  At symmetry `ℛ(±s) = R(s)`, `ℛ_V = R(x)`, `𝒬 = x·L(x)`, so
this is §5d's `F = xL(x)[R(x) − R(s) − R(t)]` verbatim — the general fixed point
obeys the same law, with `R` replaced by the ratio-of-averages `ℛ` and `R(x)` by
`ℛ_V`.  (The earlier `Δ[𝑅_B − 𝑅_U − 𝑅_V] − (1−μ)f_e(m)` is equivalent but is not
the normal form.)  All three identities verified to `≈ 1e−13`.

**So the target reduces to a single clean inequality:**

> ```
> F ≤ 0   ⟺   ℛ(S) + ℛ(T)  ≥  ℛ_V        at asymmetric fixed points.
> ```
>
> ⚠ `F ≤ 0` is *sufficient* for the conjecture, not equivalent — see the scope
> correction at the end of §6.

Over 178 asymmetric fixed points the margin is large — `ℛ_V − ℛ(S) − ℛ(T) ≤
−0.294` — so this is not a delicate near-tie.  Note `ℛ(S)` is a *mediant* of
`R(a)` and `R(b)`, hence lies between them, and `R(y) = f_e(y)/(yL(y))` decreases
from `1/2` at `y = 0` to `0` at `y = 1`; positive value in the symmetric case
requires `R(s) + R(t) < R(x)`, which is why the optima sit at `s,t ≈ 0.998`.

**A tempting sub-lemma, refuted.**  `ℛ_V ≤ 1/2` would follow from
`I(U;V) ≤ L(U;V)`, and at symmetry that is exactly the trapezoid bound
`f_e(x) ≤ x·artanh(x)/2` already proved (`fe_le_half_mul`).  In general it is
**false**: `I − L` reaches `+1.9e−3` at `a = 0.2477`, `b = 0.9826`, `c = 0.2516`,
`d = 0.9713`, `δ = 0.9926`.  So the forward/reverse KL comparison holds on the
symmetric slice but not off it — another instance of a symmetric-case fact that
does not survive.

### Everything is Jeffreys divergence

The identities simplify once more.  Since
`log cosh(artanh s) = −½log(1−s²) = D(π_X ‖ P_{X|u})`, one has
`E[S·artanh S] = I(U;X) + L(U;X)`.  Write

```
𝒥(A;B) := I(A;B) + L(A;B) = D(P_{AB}‖P_A P_B) + D(P_A P_B‖P_{AB})     (Jeffreys)
ρ(A;B) := I(A;B) / 𝒥(A;B)  ∈ [0,1]
```

Then at **any** fixed point:

> ```
> μ·𝒥(U;X)  =  𝒥(U;V)  =  ν·𝒥(Y;V)
> F  =  𝒥(U;V) · [ ρ(U;V) − ρ(U;X) − ρ(Y;V) ]
> ```

So **`μ` and `ν` are exactly the Jeffreys contraction ratios of the two hops**,
`μ = 𝒥(U;V)/𝒥(U;X)`, `ν = 𝒥(U;V)/𝒥(Y;V)`; in particular `μ, ν < 1` is automatic
from the data-processing inequality for Jeffreys divergence, and no longer needs
to be imposed.  And §5d's `R(y) = f_e(y)/(y·artanh y)`, which looked like an ad hoc
profile, **is just `ρ`** — the fraction of the Jeffreys divergence carried by its
forward half.  Verified to `1e−16` / `2.6e−13`.

### The equalizer condition

The two tangency points give more than the average.  With
`A_u := D(π_X ‖ P_{X|u})` and `B_u := D(ρ_V ‖ P_{V|u})`, the intercept identity
holds at *each* contact point separately, so

> ```
> μ·A_u − B_u  =  γ   is constant over supp U,      γ = F + ν·I(Y;V)
> ```

(verified: spread `4.3e−16`), and symmetrically
`ν·D(ρ_Y‖P_{Y|v}) − D(π_U‖P_{U|v}) = F + μ·I(U;X)` over `supp V`.  This is the
exact analogue of the KKT condition at channel capacity, where
`D(P_{Y|x}‖P_Y)` is constant on the support of the optimal input.  Averaging
recovers the Jeffreys identity, so the per-branch form is strictly stronger.
Note `F > 0` forces `γ > 0`, i.e. `μ·A_u > B_u + ν·I(Y;V)` at **both** contact
points.

### Target, and what to try next

> **Open:** `ρ(U;X) + ρ(Y;V) ≥ ρ(U;V)` at asymmetric fixed points.

Margin over 189 asymmetric fixed points: `ρ(U;V) − ρ(U;X) − ρ(Y;V) ≤ −0.284`.
Ideas not yet tried:

1. **Exploit the equalizer per branch.**  It is the only relation so far that
   distinguishes the two branches rather than averaging them, and asymmetry is
   precisely a statement about the branches differing.  `F > 0` needs
   `μA_u > B_u + νI(Y;V)` simultaneously at both contact points.
2. **Bounds on `ρ`.**  `ρ = I/(I+L)` compares forward and reverse KL.  On the
   symmetric slice `ρ ≤ 1/2` — that is exactly the proved trapezoid bound
   `fe_le_half_mul` — but it fails off the slice by up to `1.9e−3`, so what is
   needed is a *near*-`1/2` bound with an explicit defect, plus a matching lower
   bound on `ρ(U;X) + ρ(Y;V)`.
3. **Schur-convexity.**  Ask whether `ρ(U;X)` is Schur-convex/concave in
   `(v₀,v₁)`, which would locate its extremes on the symmetric line.
4. **Computer-assisted, rigorously.**  The domain is compact and the local
   behaviour at the symmetric branch is already proved (§5d).  Interval
   arithmetic / branch-and-bound on the complement of a neighbourhood of that
   branch would give a complete proof.  Given that five analytic comparisons
   have now been refuted, this is a serious option rather than a fallback, and
   the `−0.284` margin off the symmetric branch makes it numerically comfortable.
5. **Narrow the open `δ`-interval.**  `δ = 0` and `δ = 1` are proved; a
   perturbative argument at each end would shrink what is left, and could be
   combined with 4.

### Working the equalizer

Let `H(s) := E_T f(δsT) − μf_e(s)` be the `U`-side objective and
`g(s) := H(s) − s·H′(s)` its tangent-intercept function.  Then

```
g(s) = μ·A(s) − B(s) ,   A(s) = −½log(1−s²) = D(π_X‖P_{X|s}) ,  B(s) = D(ρ_V‖P_{V|s}) ,
g(0) = 0 ,               g′(s) = −s·H″(s) ,
```

so integrating,

```
γ = ∫₀^a σ·[ μ/(1−σ²) − δ²·E_T( T²/(1+δσT) ) ] dσ           (mirror for −b),
```

verified numerically.  Four things come out of this.

1. **A new proof that a symmetric `T` forces a symmetric `S`.**  If `T` is
   symmetric then `H` is even, hence `g` is even; and `g′(s) = −s·H″(s) > 0`
   wherever `H″ < 0`, which holds at the contact points of a concave envelope.
   So `g` is strictly increasing there, and `g(a) = g(b)` gives `a = b`.  This is
   the classical fact (Remark 6 of the Entropy paper) with a one-line proof.

2. **A branch-wise necessary condition for positive value.**  `F > 0` forces
   `γ > 0`, i.e. at **both** contact points

   > `D(ρ_V ‖ P_{V|u})  <  μ · D(π_X ‖ P_{X|u})` .

   In the symmetric case `B(s) = A(x)`, so this is the explicit constraint
   `1 − x² > (1 − s²)^μ` — verified on symmetric fixed points of positive value.

3. **The extra scalar relation** beyond the averaged Jeffreys identity:

   > `μ·[A(a) − A(b)]  =  B(a) − B(−b)  =  E_T[ log( (1−δbT)/(1+δaT) ) ]` .

   At `a = b` the right side is `∝ −skew(T)` to leading order, so this *is* the
   sign-flip of §5e/§5f, now falling out of the equalizer; and it says the
   `U`-side asymmetry `a − b` is what balances the `T`-side skew.

4. **Why the contact points sit at `≈ 0.998`.**  `g′(σ) ≈ μσ/(1−σ²) → ∞` as
   `σ → 1`, and that dominant term is *the same on both sides* — the asymmetry
   enters only through the bounded `δ²E_T[T²/(1±δσT)]`.  So the regime of
   positive value, which needs `γ` large, pushes both contact points towards
   `±1`, precisely where the symmetric term swamps the asymmetric one.  This is
   a mechanism for near-symmetry, and the most promising thread to make
   quantitative.

5. **The excess-integral identity.**  Subtracting the two integral forms of `γ`
   (taking `a > b`) gives, exactly,

   > ```
   > ∫_b^a σ·[ μ/(1−σ²) − ω(σ) ] dσ  =  −2δ³·∫₀^b σ²·E_T[ T³/(1−(δσT)²) ] dσ ,
   > ```

   `ω(σ) := δ²E_T[T²/(1+δσT)]`.  Verified to `2.5e−16`.  The left side diverges
   as `a → 1`; the right side is `∝ −skew(T)` and stays bounded.

6. **Asymmetry bounds the contact points away from `±1`.**  This is forced by the
   parametrization, and is the missing half of the mechanism:

   > `a = k/(1+m)`, `b = k/(1−m)`, and `|b| ≤ 1` gives `k ≤ 1−m`, hence
   > **`a ≤ (1−m)/(1+m) < 1`.**

   So `γ ≤ μ·A(a) ≤ (μ/2)·log((1+m)²/(4m))`: the more asymmetric the channel, the
   smaller the cap on `γ`, hence on `F`.  Empirically the asymmetric fixed points
   all sit at small contact points (`a, b ∈ [0.011, 0.68]` over the sample),
   never in the near-deterministic corner `≈ 0.998` where positive value lives.
   Relatedly `p_a·a = p_b·b = k/2`, which collapses the Jeffreys term to

   > `𝒥(U;X) = (k/2)·[ artanh a + artanh b ]` .

**What is still missing.**  The *averaged* equalizer is equivalent to the
definition of `F` and yields nothing (it is circular); all the content is in the
per-branch items 3, 5, 6.  Using the Jeffreys identity to eliminate `ν`, the
condition `F > 0` becomes

```
−log(1−a²)  >  k·[artanh a + artanh b]·ρ(Y;V) ,
```

and closing the argument needs a lower bound on `ρ(Y;V)` — which is exactly what
is unavailable, since `ρ(Y;V)` can be made small by a near-deterministic `V`.
That is the gap.

Two further attempts, both recorded because they fail informatively.

* **The dangerous regime is clean.**  Positive value needs contact points near
  `±1`, and §5d already excludes asymmetric fixed points in a neighbourhood of
  the symmetric positive-value branch.  Scanning just outside it (tiny `m`,
  `k → 1`) produces **337** further asymmetric fixed points, **119** of them with
  a contact point above `0.99`, and `max F = −2.2e−12`
  (`numerics/danger_scan.py`).  Over a thousand asymmetric fixed points have now
  been examined across all scans with no exception to `F ≤ 0`.  ⚠ Those scans
  never reached `k → 1`; configurations with `m ~ 1e-12` do have `F > 0`
  (legitimately — they are BSC pairs).  See the scope correction.

* **Decoupling the target fails, but only just.**  Since
  `F ≤ 0 ⟺ ρ(U;V) ≤ ρ(U;X) + ρ(Y;V)` (⚠ `F ≤ 0` is sufficient, not equivalent to
  the conjecture — scope correction at the end of §6), it would suffice to prove the two
  *separate* bounds `sup ρ(U;V) ≤ c₀` and `inf[ρ(U;X) + ρ(Y;V)] ≥ c₀`.  Measured:

  > `sup ρ(U;V) = 0.548638` over arbitrary two-point pairs (on the symmetric
  > slice it is `≤ 1/2` — exactly the proved trapezoid bound `fe_le_half_mul`),
  > while `inf[ρ(U;X) + ρ(Y;V)] = 0.542473` over asymmetric fixed points.

  So the decoupled chain misses by `0.006`.  The instructive part is *where*: the
  infimum is attained at an essentially symmetric configuration
  (`m = 1.6e−6`, `a ≈ b ≈ 0.960`, `c ≈ d ≈ 0.995`), where `ρ(U;V)` is far below
  its supremum.  The two worst cases live at different configurations, so **any
  proof must evaluate the two sides at the same point** — the coupling cannot be
  thrown away, which is the same lesson as the refuted matchings, one level up.

### A two-regime architecture — REFUTED

The decoupling failure above is *localized*: its worst case sits at
`m = 1.6e−6`, i.e. deep inside the region §5d already governs.  That suggests
splitting on the asymmetry `m = (b−a)/(a+b)` rather than trying to bound
everything uniformly.

> **Regime 1 (`m < m₀`, near-symmetric).**  §5d: at a symmetric fixed point of
> positive value the linearized skew map contracts, `Λ·Λ′ < x² < 1`, so no
> asymmetric branch bifurcates.  Proved and formalized — but as a *local*
> statement, with no explicit radius.
>
> **Careful:** this does **not** say there are no asymmetric fixed points with
> small `m` — the scans find them at `m = 1.6·10⁻⁶` and `4.8·10⁻⁷`.  It says none
> of them can have `F > 0`, since such a point would be a branch bifurcating
> from a positive-value symmetric fixed point, which §5d forbids.  So (L3) must
> be stated as *"there is `m₀ > 0` such that no asymmetric fixed point with
> `m < m₀` has `F > 0`"*, not as an exclusion of asymmetric fixed points.
>
> **Regime 2 (`m ≥ m₀`).**  Use the decoupled bound: since
> `F ≤ 0 ⟺ ρ(U;V) ≤ ρ(U;X) + ρ(Y;V)` (⚠ sufficient, not equivalent — see the
> scope correction), it suffices that
> `sup ρ(U;V) ≤ c₀ ≤ inf_{m ≥ m₀}[ρ(U;X) + ρ(Y;V)]`.

**This does not work: (L2) is false.**  The thresholds below were measured on a
sample that was both under-sampled and contaminated by degenerate fixed points;
see the audit that follows.  The section is kept because the failure is
instructive.  The thresholds as originally measured:

| `m₀` | `inf [ ρ(U;X) + ρ(Y;V) ]` |
| --- | --- |
| `0` | `0.5316` |
| `10⁻³` | `0.5316` |
| `3·10⁻³` | `0.5812` |
| `10⁻²` | `0.6250` |
| `10⁻¹` | `0.6307` |

against `sup ρ(U;V)`, which has a **closed form**:

> ```
> sup ρ(U;V)  =  2 − 1/ln 2  =  0.5573049571…
> ```
>
> approached (not attained) along `a = c = ε → 0`, `b = d = 1 − ε`, `δ = 1` — a
> **Z-channel pair**, fitting since those are the extremal objects of the whole
> problem.  There `I ≈ ε²(2log2 − 1)` and `𝒥 ≈ ε²·log 2`, giving the ratio.
> Multi-start Nelder–Mead over all five parameters confirms it to nine digits.

So the split closes already at `m₀ = 3·10⁻³` (`0.5573 < 0.5812`), and at
`m₀ = 10⁻²` the margin is comfortable (`0.5573` vs `0.6250`).  What the
architecture needs is exactly three lemmas:

* **(L1)** — **PROVED AND FORMALIZED** (`SharpRho.lean`), for arbitrary mean-zero `Z` on `[−1,1]`, not just
  for products `Z = δST`.  Put `c₀ := 2 − 1/ln 2` and `λ := 1 − c₀ = 1/ln 2 − 1`.
  Since `𝒥 = E[Z·log(1+Z)] ≥ 0`,

  > `ρ ≤ c₀  ⟺  E[ (1+Z)log(1+Z) − c₀·Z log(1+Z) ] ≤ 0  ⟺  E[ φ(Z) ] ≤ 0`,
  > where `φ(z) := log(1+z)·(1 + λz)`.

  And `φ(z) ≤ z` **pointwise** on `(−1,1]`, with equality exactly at `z = 0` and
  `z = 1`.  Since `E[Z] = 0`, `E[φ(Z)] ≤ E[Z] = 0`. ∎
  The constant is sharp (equality approached as `z → 0`), and on the symmetric
  slice the statement degrades to `ρ ≤ 1/2`, the already-formalized trapezoid
  bound `fe_le_half_mul`.  In Lean: `psiF_nonpos`, `log_mul_one_add_lamC_le`,
  `mutual_le_c0_mul_jeffreys`.  Dividing by `1 + λz > 0` turns the statement into
  `ψ(z) := log(1+z) − z/(1+λz) ≤ 0`, whose derivative
  `ψ′(z) = 1/(1+z) − 1/(1+λz)²` carries **no logarithm**, so its sign is the sign
  of `z·(λ²z + 2λ − 1)`: `ψ` rises to `ψ(0) = 0`, dips on `[0,ζ]`, and rises back
  to `ψ(1) = 0`, with `ζ = (1−2λ)/λ² ∈ (0,1)`.
* **(L2)** `inf[ρ(U;X) + ρ(Y;V)] ≥ c₀` over asymmetric fixed points with
  `m ≥ m₀`.  Explicitly, with

  > `G(p,q) := [f_e(p)/p + f_e(q)/q] / [artanh p + artanh q]`

  (the `artanh`-weighted mean of `R(p)` and `R(q)`, hence in `(0,1/2)` and
  decreasing as the atoms approach `1`), (L2) reads `G(a,b) + G(c,d) ≥ c₀`.

  **What the coupling has to supply.**  `m ≥ m₀` bounds `a ≤ (1−m₀)/(1+m₀)` away
  from `1` (item 6), but that is *not* enough on its own: `b → 1` sends
  `artanh b → ∞`, so `G(a,b) → R(b) → 0` regardless of `a`.  Measuring over 500
  asymmetric fixed points with `m ≥ 3·10⁻³`:

  | | |
  | --- | --- |
  | `max(a,b,c,d)` | `0.99976` — atoms *do* reach `1` |
  | `min G(a,b)` | `0.2665` |
  | `min G(c,d)` | `0.1734` |
  | `min [G(a,b) + G(c,d)]` | `0.5880` (vs `c₀ = 0.5573`) |

  and the minimiser is `m = 0.392`, `a = 0.409`, `b = 0.936`, `c = 0.9995`,
  `d = 0.960`.  So each `G` separately gets small — `G(c,d) = 0.173` there — but
  **never both at once**: when one side pushes both atoms towards `1`, the
  fixed-point equations force a small atom on the other side.  That trade-off is
  exactly what (L2) must capture, and it is why no bound on one side alone can
  work.  The natural source of the coupling is the Jeffreys chain
  `μ·𝒥(U;X) = 𝒥(U;V) = ν·𝒥(Y;V)` with `μ, ν < 1`, i.e.
  `𝒥(U;V) < min(𝒥(U;X), 𝒥(Y;V))`.
* **(L3)** an explicit radius `m₀ > 0` such that no asymmetric fixed point with
  `m < m₀` has `F > 0` — the quantitative form of §5d.  **Assessed; and it turns
  out probably not to be needed.**

  The bifurcation shape is clear: near a symmetric fixed point the skew equations
  give `σ = Ξ(σ)` with `Ξ(0) = 0`, `Ξ′(0) = ΛΛ′`, so `(1−ΛΛ′)|σ| ≤ C|σ|²/2` and
  hence `σ = 0` or `|σ| ≥ 2(1−ΛΛ′)/C`; with `m ≍ σ/2` this gives
  `m₀ = (1−ΛΛ′)/C`.  The first input is **free**: `local_rigidity.py` gives
  `max ΛΛ′/x² = 0.001257`, so `ΛΛ′ ≤ 0.0013` and `1 − ΛΛ′ ≥ 0.9987` — the
  contraction is overwhelming, not marginal.  Everything therefore rests on the
  second-order constant `C`, and that is where the difficulty is: positive value
  forces the atoms to `≈ 0.998`, where `artanh′ ≈ 250` and `artanh″ ≈ 1.2·10⁵`,
  so `C ∼ 10⁵` and `m₀ ∼ 10⁻⁵`.  Making that uniform over `{F > 0}` is precisely
  the uniform curvature bound §5f flagged as missing.

  **But the stratification says the split is unnecessary.**  Over **600**
  non-degenerate asymmetric fixed points (`numerics/l3_scan.py`):

  | stratum | count | `max F` | `max γ/(ν·I(Y;V))` |
  | --- | --- | --- | --- |
  | `m < 10⁻⁵` | 45 | `−8.2·10⁻³` | `0.101` |
  | `m < 10⁻⁴` | 138 | `−5.7·10⁻³` | `0.183` |
  | `m < 10⁻³` | 274 | `−2.2·10⁻³` | `0.230` |
  | `m ≥ 10⁻⁵` | 555 | `−4.7·10⁻⁴` | `0.259` |
  | `m ≥ 10⁻²` | 204 | `−1.5·10⁻³` | `0.259` |
  | `m ≥ 10⁻¹` | 64 | `−1.5·10⁻³` | `0.065` |

  (A 250-point run of the same scan gave `0.058 / 0.183 / 0.230 / 0.230`, and a
  different seed elsewhere reached `0.368`; so the true supremum is somewhere
  around `0.3`–`0.4`, still a factor `≥ 2.5` of room.  Quoting a single
  under-sampled run is what killed (L2), so treat these as lower bounds on the
  sup.)

  The route-2 ratio **does not degenerate near symmetry** — it is *smallest*
  there (`0.101` for `m < 10⁻⁵`, `0.065` for `m ≥ 10⁻¹`) and largest at
  intermediate `m`.  So the near-symmetric regime is not the hard part, the bound
  never approaches `1` anywhere, and a *uniform* proof of `γ ≤ ν·I(Y;V)` is the
  right target — with **(L3) not merely optional but pointless**.

  (L3) is a *special case* of route 2 (its restriction to `m < m₀`), so route 2
  subsumes it, while (L3) alone never suffices.  And the split is badly placed:
  `m₀ ≈ 10⁻⁵` removes the stratum where route 2 is most comfortable (ratio
  `0.101`, a 10× margin) and leaves the one containing the supremum (`0.247`).
  It also trades cheap for expensive — a ratio bound with 10× slack, against a
  uniform curvature bound `C` over `{F > 0}` where `artanh″ ≈ 1.2·10⁵`.  Note
  too that asymmetric fixed points with `m → 0` have ratio `≈ 0.10 ≪ 1`, so they
  approach symmetric fixed points of *negative* value, never the positive-value
  branch: that is (L3)'s content, obtained from route 2's inequality instead of
  from a bifurcation analysis.  **Drop (L3).**  Only a future scan showing the
  ratio approaching `1` in some stratum would revive it.

This is the first complete architecture in the development: three concrete,
independently attackable lemmas with numerically calibrated constants, instead
of one monolithic inequality.  It also explains why every previous attempt
failed — each tried to cover both regimes with a single bound, and the two
regimes genuinely need different arguments.

**Status: not proved.**  Established: the Jeffreys normal form, the
contraction-ratio reading of `μ` and `ν`, the identification `R = ρ`, the
equalizer condition, and items 1–4 above.

### The refutation of (L2), and a degeneracy audit

**(L2) is false.**  A non-degenerate asymmetric fixed point with
`m = 0.0142 ≫ m₀ = 3·10⁻³` (`numerics/nondegenerate_scan.py`):

```
m = 0.01421,  δ = 0.9964,  a = 0.95239,  b = 0.97984,  c = 0.99607,  d = 0.98818,
μ = 0.9185,   ν = 0.6536,
G(a,b) + G(c,d) = 0.3035 + 0.2371 = 0.5406  <  c₀ = 0.5573 .
```

There `F = −0.408 < 0` still — but through `ρ(U;V) = 0.3189`, far below both `c₀`
and the sum.  So the inequality `F ≤ 0` holds there while the *decoupled* bound fails,
exactly as the earlier `0.006` near-miss warned.  No larger `m₀` rescues it: this
point sits well inside the region Regime 2 was meant to cover.  The earlier
infima (`0.5812` at `m₀ = 3·10⁻³`, `0.625` at `10⁻²`) were **under-sampled**.

**Degeneracy audit.**  Solving (E2),(E4) produces many *degenerate* fixed points.
The diagnostic is `γ = conc(H)(0)`, the `U`-side concave-envelope value, which
satisfies `γ ≥ H(0) = 0` always; `γ = 0` means the bitangent passes through the
origin, so `S ≡ 0` is already optimal and `F = −ν·I(Y;V) ≤ 0` holds vacuously.
Measured over the candidates: `|γ| < 10⁻⁹` for **256**, and `μ < 10⁻⁶` for
**215**, against **300** non-degenerate ones kept.

> So the earlier counts — "694", "337", "over a thousand asymmetric fixed
> points" — **overstated the effective evidence by roughly a factor of two**.

What survives, and is in fact stronger: on the 300 non-degenerate fixed points,
`max F = −8.9·10⁻⁴`, a genuine margin rather than the machine-zero maxima the
contaminated samples were reporting.  Both sides were separately verified to be
true best responses (200/200, shortfall `8.6·10⁻¹³`), so these are genuine
alternating-maximization fixed points and not merely critical points of `Φ`.

### Route 2: decoupling *does* work, once restricted to fixed points

(L1) is sharp over **all** two-point pairs, with `c₀ = 2 − 1/log 2 = 0.5573`
attained at a Z-channel corner — and that corner is not a fixed point.  (L2)
missed by only `0.017`.  So restrict the bound to the fixed-point set:

| quantity, over asymmetric fixed points | value |
| --- | --- |
| `max ρ(U;V)` — sampling | `0.499899` |
| `max ρ(U;V)` — direct maximization | **`0.4999707`** |
| `min [ρ(U;X) + ρ(Y;V)]` | **`0.548401`** |

`0.49997 < 0.5484`, so **the decoupling that failed globally succeeds at fixed
points**, with a margin of `0.048` instead of a deficit of `0.017`.  The
maximizer sits at `m = 9.6·10⁻⁶`, i.e. in the *symmetric limit*.  This replaces
the refuted (L1)+(L2) pair by:

> **(A)** `ρ(U;V) ≤ 1/2` at fixed points.  Equivalently `I(U;V) ≤ L(U;V)`, i.e.
> `E[(2+z)·log(1+z)] ≤ 0` for `z = δST`.  Sharp, and approached exactly in the
> symmetric limit — where it *is* the trapezoid bound `f_e(x) ≤ x·artanh x/2`,
> already proved and formalized (`fe_le_half_mul`).  It is **false off the
> fixed-point set** (globally `sup ρ = 0.5573`), so fixed-pointness is essential.
>
> **(B)** `ρ(U;X) + ρ(Y;V) ≥ 1/2` at fixed points.  Measured minimum `0.5484`.

**(A) is now proved and formalized** (`BSCAveraging/EvenOdd.lean`,
`mutual_le_lautum_of_opposite_skew`).  The mechanism sketched from the moment
expansion turned out to work *exactly*, with no weighted-tail gap at all, once
the split is done at the level of functions rather than moments.

Write `η(z) := ξ(z) − 2z`; since `E z = 0`, `I − L = E[η(z)]`.  Split `η` into
even and odd parts:

```
η_e(z) = log(1−z²) + z·artanh z                          (even)
η_o(z) = (1 + z/2)·log(1+z) − (1 − z/2)·log(1−z) − 2z     (odd)
```

*The even half is the trapezoid bound.*  `η_e(z) = 2f_e(z) − z·artanh z`, so

```
η_e(z) ≤ 0   ⟺   f_e(z) ≤ z·artanh(z)/2
```

which is `fe_le_half_mul`, proved in §5d.  This is **pointwise** — no moments,
no expectation — and it is exactly why (A) is sharp in the symmetric limit.

*The odd half is the sign flip.*  `η_o` has **no linear part** (it starts at
`z³/6`), so nothing needs subtracting off, and the §5e machinery applies
verbatim to the kernel `v(u) = η_o(δu)/u`:

```
E[η_o(δST)] = λκ · [v(ac) − v(ad) − v(bc) + v(bd)],   λ = ab/(a+b), κ = cd/(c+d)
```

— note the **plus** sign, where `Ω` had a minus, precisely because `fo` did have
a linear part and `η_o` does not.  Supermodularity of `(r,q) ↦ v(rq)` is `u·v′(u)`
increasing, and the identity

```
z·η_o′(z) − η_o(z) = 2z − 2·artanh z + z³/(1−z²)
```

(the analogue of `fo_sub_mul_deriv`) reduces that to monotonicity of
`K(z) = 2 − 2·artanh z/z + z²/(1−z²)`, whose derivative is `T(z)/z²` with

```
T(z)  = 2·artanh z − 2z/(1−z²) + 2z³/(1−z²)² ,      T(0) = 0,
T′(z) = 2(z² + 3z⁴)/(1−z²)³ > 0 .
```

**`T′` is rational — every logarithm cancels.**  So the odd half rests on one
elementary positivity, just as §5e rested on `artanh_lt_div`.  Both halves are
`≤ 0`, hence `I ≤ L`.

The hypothesis used is *opposite skews* (`b < a` and `c < d`), which is exactly
the conclusion of `omegaTwoPoint_pos` at any maximizer.  The bound is genuinely
**false** without it — globally `sup ρ = 2 − 1/log 2 > 1/2` — so the sign flip is
doing real work, not decoration.

**(B) is REFUTED** — the tenth refutation with the same signature.  Direct
minimization of `ρ(U;X) + ρ(Y;V)` over the fixed-point set finds a genuine,
fully non-degenerate fixed point at `m = 1.42e-05`, `k = 0.999977`,
`δ = 0.999958` (fsolve residual `1.3e-10`, `μ = 0.283`, `ν = 0.9996`,
`γ = 0.362` — no degeneracy filter catches it):

```
ρ(U;X) = 0.119343     ρ(Y;V) = 0.339579     sum = 0.458922  <  1/2
ρ(U;V) = 0.339638     F      = -0.196       ρ − sum = -0.119   (still fine)
```

The earlier measured minimum `0.5484` came from sampling that never pushed
`a,b → 1`, where `G → 0`.  Push `k → 1` and the U-side ratio collapses.

**Why the split fails, again.**  (A) is tight only in the *symmetric* limit
(`m → 0`, where `ρ(U;V) → 1/2`); (B) fails only where `a,b → 1`.  Those are
different configurations, so bounding the two sides separately loses the whole
margin — the same error as the previous nine dead ends.  Note that at the
refuting point `ρ(U;V) = 0.339638` and `ρ(Y;V) = 0.339579` agree to `6e-5`,
while `ρ(U;X) = 0.119` is pure slack: the real target is carried entirely by one
side, and *which* side varies.

**The max-form bound is refuted too** (eleventh).  `ρ(U;V) ≤ max(ρ(U;X), ρ(Y;V))`
would have implied the conjecture outright, since the other term is `≥ 0`.  It
fails at a healthy *interior* fixed point — `m = 3.557e-02`, `k = 0.847348`,
`δ = 0.973861`, `c = 0.866380`, `d = 0.801546` (residual `1.1e-12`,
`μ = 0.5496`, `ν = 0.5823`, `γ = 0.0277`):

```
ρ(U;X) = 0.397967   ρ(Y;V) = 0.404008   max = 0.404008
ρ(U;V) = 0.445183   exceeds the max by +0.041175
sum    = 0.801975   (target margin +0.357)
```

### The sum is irreducible — consolidated

| candidate | verdict |
| --- | --- |
| `ρ(U;V) ≤ 1/2` under opposite skews — **(A)** | **proved** (`EvenOdd.lean`) |
| `ρ(U;V) ≤ ρ(U;X)` | refuted, `+0.119` |
| `ρ(U;V) ≤ ρ(Y;V)` | refuted, `+0.315` |
| `ρ(U;V) ≤ ρ(U;Y) = G(δa,δb)` | refuted, `+0.098` |
| `ρ(U;V) ≤ max(ρ(U;X), ρ(Y;V))` | refuted, `+0.041` |
| `ρ(U;V) ≤ 2ρ(U;X)` | holds, margin `0.17` — but only half of what is needed |
| `ρ(U;V) ≤ 2ρ(Y;V)` | refuted, `+0.134` |
| `ρ(U;X) + ρ(Y;V) ≥ 1/2` — **(B)** | refuted, `0.4589` |
| `ρ(U;V) ≤ ρ(U;X) + ρ(Y;V)` — **⟺ `F ≤ 0`, which is *stronger* than the conjecture** | fails near the symmetric locus; see the scope correction below |

So `ρ` is **not** monotone under data processing in any form, and the sum cannot
be split.  The two sides trade off against each other — when one is small the
other is large — and the fixed-point equations balance the trade-off exactly.
Any future route must keep both sides **coupled**, i.e. use the fixed-point
equations themselves, as §5d does at symmetric points.  Bounding the sides at
independently chosen configurations is now an eleven-times-refuted dead end and
should not be attempted again.

**What survives.**  (A) is a theorem (`EvenOdd.lean`) and is independently
useful.  The route-2 linchpin identity is now verified numerically to `8e-13`
against typical `|F| ~ 6e-4` (`numerics/verify_identity.py`), as is
`ρ(Y;V) = G(c,d)` to machine precision — so the *framing* of route 2 is right
even though this particular decoupling is not.  Across the fixed-point set the
quantity `ρ(U;V) ≤ ρ(U;X) + ρ(Y;V)` is equivalent to `F ≤ 0`, which is **not**
the conjecture but a strictly stronger statement (`J_sym ≥ g(0,0) = 0`).  It is
*false* near the symmetric locus — see the scope correction below.  The margin
figures quoted in earlier drafts (`≥ 0.119`, `0.317`) came from samplers that
could not reach `k → 1`, and are withdrawn.

### Closed forms on the fixed-point manifold (all verified to machine precision)

Parametrise a fixed point by `(m,k,δ)` with U-side X-biases `v₀,v₁ = m±k`, V-side
X-biases `b₁,b₂ = m + kδc, m − kδd`, weights `wc,wd = d/(c+d), c/(c+d)`,
`κ = cd/(c+d)`, `Δℓ = L(b₁) − L(b₂)`, `D = L(m+k) − L(m−k)`,
`A = ½[f_e(v₀)+f_e(v₁)]`.  Then (`numerics/verify_identity.py`, errors `< 4e-14`):

```
I(U;V) = wc·f_e(b₁) + wd·f_e(b₂) − f_e(m)  =  I(X;V)
𝒥(U;V) = 𝒥(X;V) = k·δ·κ·Δℓ                       ← closed form, no logs of the joint
ρ(U;V) = ρ(X;V)                                   ← the U-side is transparent
ρ(U;X) = 2(A − f_e(m)) / (k·D)
ρ(Y;V) = G(c,d),   G(p,q) = [f_e(p)/p + f_e(q)/q]/[L(p)+L(q)]
F      = k·δ·κ·Δℓ · [ρ(U;V) − ρ(U;X) − ρ(Y;V)]
```

The two-point data and `(m,k)` are interchangeable:
`m = (b−a)/(a+b)`, `k = 2ab/(a+b)`, `a = k/(1+m)`, `b = k/(1−m)`.

Two consequences worth keeping.  First, **`ρ(U;V) = ρ(X;V)`** — all three ratios
are functions of the same mean-zero two-point data, `ρ(U;X)` of `S` alone,
`ρ(Y;V)` of `T` alone, `ρ(U;V)` of `(S,T,δ)` jointly.  Second, in **ratio** form
the conjecture is far better behaved than in `F` form: the "dangerous" fixed
points where `F ≈ −2e-12` have `F → 0` only because `𝒥(U;V) = kδκΔℓ → 0`
(there `c,d → 0`), while the ratio margin `ρ(U;X)+ρ(Y;V) − ρ(U;V)` stays above
`0.17` across every scan.  The ratio normalisation removes the degeneracy that
made the `F` form look delicate.

**The constraint-free inequality is false.**  `ρ_δ(S,T) ≤ G(a,b) + G(c,d)` for
arbitrary two-point data fails by up to `+0.428` (`+0.371` even under opposite
skews).  In the symmetric case it reads `R(δst) ≤ R(s) + R(t)` with
`R(y) = f_e(y)/(y·L(y))` decreasing, and `s = t = 0.9999`, `δ = 0.9` gives
`R(0.89982) = 0.3732 > 0.2798 = R(s)+R(t)`.  So the fixed-point coupling is
genuinely load-bearing — consistent with the eleven refutations.

**All of the closed forms above, the route-2 identity, and (E4) are now
formalised** in `BSCAveraging/FixedPoint.lean` (`DOf_eq`, `AOf_sub_fe`,
`rhoUX_eq`, `DlOf_eq`, `jeffreysTP_eq`, `mutualTP_eq`, `route_identity`,
`route_identity_ratio`, `E2_of_def`, `E4Res_symmetric`).  The route identity is
stated division-free as `Φ = I(U;V) − 𝒥(U;V)·[ρ(U;X) + ρ(Y;V)]`, with the ratio
form as a corollary under `𝒥 ≠ 0`.  **The variational characterisation of (E4) is now formalised too.**  With `μ,ν`
held fixed, write `g₁(c) = f_e(b₁(c)) − νf_e(c)`, `C₂ = f_e(b₂) − νf_e(d)`,
`N(c) = d·g₁(c) + c·C₂`.  Then `∂Φ/∂c = [N′(c)(c+d) − N(c)]/(c+d)²` collapses to

```
∂Φ/∂c = −d·E4Res /(c+d)²        hasDerivAt_PhiPar_c
∂Φ/∂d = +c·E4Res′/(c+d)²        hasDerivAt_PhiPar_d
```

so **(E4) is exactly the `c`-stationarity of the V-side Lagrangian**
(`E4ResPar_eq_zero_iff`).  Moreover the two stationarity equations differ by
exactly the defining relation for `ν`:

```
E4Res − E4Res′ = −(c+d)·[k·δ·Δℓ − ν·(artanh c + artanh d)]     E4ResPar_sub_E4ResPar'
```

which vanishes identically at `ν = nuOf` (`E4ResPar_eq_E4ResPar'_of_nuOf`).  So
the *single* equation (E4) encodes **both** stationarity conditions, and

> `∂Φ/∂c = 0  ∧  ∂Φ/∂d = 0   ⟺   E4Res = 0`        `E4Res_eq_zero_iff_stationary`

This supersedes the earlier note that (E4)'s variational reading was
numerics-only.  The earlier ambiguity (a frozen-`μ,ν` finite-difference probe
showing relative gradients `~1e-2`) was an artefact of `Φ` being extremely flat
near the sampled points, not a discrepancy: the identity above is exact.

### An argument from (E4): the bitangency reduction (formalised)

Collapse the V-side to a single scalar function of one atom,

```
φ(t) = f_e(m + kδt) − ν·f_e(t)
```

The V-side of a fixed point is the **mean-zero** two-point law `T ∈ {c, −d}` with
weights `wc = d/(c+d)`, `wd = c/(c+d)`, and

```
φ(c)  = f_e(b₁) − ν·f_e(c)         φ(−d) = f_e(b₂) − ν·f_e(d)
φ′(c) = kδ·L(b₁) − ν·L(c)      φ′(−d) = kδ·L(b₂) + ν·L(d)
```

so `φ′(c)` is *exactly* the bracket in (E4).  Therefore

* **(E4)** ⟺ `φ(c) − φ(−d) = (c+d)·φ′(c)` — the chord has slope `φ′(c)`;
* **`ν = nuOf`** ⟺ `φ′(c) = φ′(−d)` — equal slopes.

Together: the chord is **bitangent** to `φ` at `c` and `−d`.  Since `E T = 0`, the
mixture value is the bitangent line at `0`, and `φ(0) = f_e(m)`, giving

```
Φ = [φ(c) − c·φ′(c)] − φ(0) − μ·I(U;X)
```

> **`Φ ≤ 0`  ⟺  (concave-envelope gain of `φ` at `0`)  ≤  μ·I(U;X).**
>
> (`Φ ≤ 0` is *sufficient* for the conjecture, not equivalent to it — see the
> scope correction.  The reduction itself is an identity and is unaffected.)

This is the reduction §5d uses on the symmetric slice, now available at a general
(E4) point.  It also shows the trivial case is vacuous: bitangency at two
*distinct* points `c > 0 > −d` forces `φ` to be non-concave on `[−d,c]`, so the
gain is genuinely positive and the whole difficulty sits in bounding it.

Formalised in `FixedPoint.lean`: `phiV`, `phiV'`, `hasDerivAt_phiV`,
`E4ResPar_eq_zero_iff_chord`, `phiV'_eq_of_nuOf`, `mixture_eq_tangent`,
`PhiVal_eq_tangent_gain`, `PhiVal_nonpos_iff_gain_le`, `PhiVal_nonpos_of_no_gain`.

**What remains** is one inequality, now sharply stated: bound the concave-envelope
gain of `φ` at `0` by `μ·I(U;X)`.  Note `φ″(t) = (kδ)²/(1−(m+kδt)²) − ν/(1−t²)`,
so `φ″(0) = (kδ)²/(1−m²) − ν`: the gain is driven by how far `ν` falls below the
Mrs.-Gerber curvature `(kδ)²/(1−m²)`, which is where `MGL.lean` should enter.

### Bounding the gain by MGL — what works and what does not

MGL in bias coordinates **is** `mgl_jensen`: it governs the *pure scaling*
`s ↦ κ·s` a BSC performs on a bias.  Applied to the V-side two-point law it
collapses the gain to a **one-dimensional** quantity — for any `t` matching the
mixture (`E[f_e(T)] = f_e(t)`; no `f_e⁻¹` is ever constructed):

```
E[f_e(κT)] − ν·E[f_e(T)]  ≤  f_e(κt) − ν·f_e(t)          gain_le_of_mgl
```

so on a symmetric U-side the concave-envelope gain of `φ` at `0` is at most
`φ(t)`, the *same function at a single point* (`gain_le_phiV_of_mgl`).

**But this covers only `m = 0`.**  For `m ≠ 0` the argument of the first term is
the *affine* `m + kδt`, not a scaling, and MGL does not apply.  The two natural
affine analogues are **false** — tested over 165k samples with
`f_e(τ*) = E[f_e(T)]`:

| candidate | max violation |
| --- | --- |
| `E[f_e(m+κT)] ≤ f_e(m+κτ*)` | `+0.318` |
| `E[f_e(m+κT)] ≤ ½[f_e(m+κτ*) + f_e(m−κτ*)]` | `+0.019` |

And `m = 0` forces `c = d` at a bitangent point (`φ` is then even, so its
bitangency points are symmetric) — precisely the slice §5d already settles.  So
**MGL alone does not bound the gain in the asymmetric case**; it is not a matter
of repackaging it.  What the formalised bound does buy is a sharp statement of
the missing ingredient:

> An *affine* MGL — a bound on `E[f_e(m + κT)]` for mean-zero `T` in terms of a
> one-dimensional matching quantity — with the offset `m` handled.  Both obvious
> candidates are refuted, so this needs a new idea, not a variant.

Formalised: `gain_le_of_mgl`, `phiV_symm`, `phiV_symm_zero`, `gain_le_phiV_of_mgl`,
`kOf_self`, `mOf_self`.

### ✔ **The correct target, and a theorem for half of it**

Write `J_sym := sup_ℬ F = max_{p,q} g(p,q)` with

```
g(p,q) = f_e(δpq) − μ·f_e(p) − ν·f_e(q)        (the value of the BSC pair (p,q))
```

The conjecture is `sup_𝒜 F = sup_ℬ F`, i.e. **`F ≤ J_sym`**.  Because
`g(0,0) = 0` we have `J_sym ≥ 0`, so `F ≤ 0` is **sufficient but not necessary** —
and it is genuinely false near the symmetric locus.  Every route-2 target stated
as `F ≤ 0` (including (M), the margin, and the tangent-gain bound) was therefore
aiming at a strictly stronger — and in general false — statement.

The `SignFlip` magnitude/sign split gives the correct statement directly
(`lagrTwoPoint_eq_gSum_add_Omega`):

```
F = Σ wᵢⱼ · g(|sᵢ|,|tⱼ|) + Ω
```

The first term is an average of four values of `g`, hence `≤ max g ≤ J_sym`
(`gSum_le_of_le`).  Therefore

> **`Ω ≤ 0` ⟹ `F ≤ J_sym`**    (`lagrTwoPoint_le_of_omega_nonpos`)

and `omegaTwoPoint_neg` gives `Ω < 0` whenever the skews point the **same** way:

> **Same-direction skews never beat the symmetric optimum**
> (`lagrTwoPoint_lt_of_same_skew`) — no multiplier hypothesis, no fixed-point
> hypothesis, no `m > 0` restriction.  Half the configuration space is settled
> unconditionally.

What remains is the opposite-skew half, where `Ω > 0` (`omegaTwoPoint_pos`) and
the target is

> **(S)**  `Ω ≤ max g − Σ wᵢⱼ g(|sᵢ|,|tⱼ|)` — the odd gain is at most the
> deficit of the magnitude-average from its maximum.

Both sides are `≥ 0` there, and this is the honest replacement for (M).

### (S): the remaining half, and why its two sides match in order

After `lagrTwoPoint_lt_of_same_skew` only the **opposite-skew** case is open,
where `Ω > 0`.  There, by `lagrTwoPoint_le_iff_omega_le_deficit`,

> `F ≤ M`  **⟺**  `Ω ≤ M − Σ wᵢⱼ·g(|sᵢ|,|tⱼ|)`

and with `M = J_sym` this is exactly the conjecture on that half.  So (S) is not
a weakening — it is the conjecture, localised to where `Ω` can help.

**The two sides have matching order**, which is what makes a comparison
plausible.  With `|S| ∈ {a,b}` at probabilities `(b,a)/(a+b)` and `|T| ∈ {c,d}`
at `(d,c)/(c+d)`:

```
E|S| = 2ab/(a+b) = k        E[|S|²] = ab          absMean_eq, absSq_eq
Var|S| = ab − k² = ab(a−b)²/(a+b)²                absVar_eq
```

so the Jensen gap driving the deficit is quadratic in `(a−b)` and `(c−d)`
*separately*, whereas `Ω` is a **mixed** second difference, bilinear in
`(a−b)·(c−d)`.  Both vanish identically on the symmetric locus
(`omegaTwoPoint_zero_of_fst_eq`, `omegaTwoPoint_zero_of_snd_eq`, and
`Var|S| = 0` at `a = b`).

Hence (S) is a comparison of two quadratic forms,

```
c₁·(a−b)² + c₂·(c−d)²   ≥   c₃·|a−b|·|c−d|
```

i.e. by AM–GM a `2×2` discriminant condition `c₃² ≤ 4c₁c₂` — the
general-position version of §5d's local rigidity.  This is the first time the
asymmetric case has been reduced to a *finite-dimensional* positivity condition
rather than a functional inequality.

Formalised: `omegaTwoPoint_zero_of_fst_eq`, `omegaTwoPoint_zero_of_snd_eq`,
`absVar_eq`, `absMean_eq`, `absSq_eq`, `gSum_le_max4`,
`lagrTwoPoint_le_iff_omega_le_deficit`.

### The discriminant for (S), computed

Expand about a symmetric point: `a,b = s ± α`, `c,d = t ∓ β` (opposite skews for
`α,β > 0`), with `(s,t)` a critical point of `g`, so

```
μ = δt·L(z)/L(s),     ν = δs·L(z)/L(t),     z = δst
```

**The odd gain.**  `λ ≈ s/2`, `κ ≈ t/2`, and the mixed difference is
`Δ_w ≈ (a−b)(c−d)·Q(st)` with `Q(u) = (u·w′(u))′ = (MFun δ u)′`.  Since
`u·w′(u) = MFun δ u = artanh(δu)/u − δ`,

```
Q(u) = [δu/(1−δ²u²) − artanh(δu)]/u²,      so  Q(st) = E(z)/(st)²
Ω ≈ αβ · E(z)/(st),                        E(z) := z/(1−z²) − artanh z  > 0
```

`E > 0` is `artanh_lt_div` — the same fact that powers the sign flip.

**The deficit.**  `Var|S| = α² + O(α⁴)`, `E|S| = s − α²/s`, and `g_p = g_q = 0` at
the critical point, so the mean-shift contributes only `O(α⁴)`:

```
deficit ≈ −½·g_pp·α² − ½·g_qq·β²
−g_pp = (z/s²)·A_s ,   A_s := s·L(z)/((1−s²)L(s)) − z/(1−z²)
−g_qq = (z/t²)·A_t ,   A_t := t·L(z)/((1−t²)L(t)) − z/(1−z²)
```

**The discriminant.**  (S) to second order is `c₁α² + c₂β² ≥ c₃·αβ` for all
`α,β > 0`, i.e. `c₃² ≤ 4c₁c₂`.  The factors `s²t²` cancel and it collapses to

> **`E(z)² ≤ z² · A_s · A_t`**

with `E`, `A_s`, `A_t` built only from `artanh` and rational functions.

**Test.**  The condition is *false* if `(s,t)` is merely a **local** critical
point — ratio up to `2.074` at `s = 0.9961`, `t = 0.1395`, `δ ≈ 1` (there
`A_t ≈ 1.5e-5`, a nearly degenerate direction).  That case is irrelevant: the
deficit is measured against `max g`, so only **global** maximisers count.
Restricted to those it holds with enormous room:

```
critical points that ARE the global max of g:  46  (199954 rejected as non-global)
max  E(z)² / (z²·A_s·A_t) = 4.56e-4            — three orders of magnitude inside
```

So the local obstruction to (S) is not merely absent, it is absent by a factor of
~2000.  **The relevant hypothesis is global maximality of `(s,t)`, not local** —
a distinction that silently breaks the naive discriminant.

**Formalised** (`FixedPoint.lean`): `EFun`, `EFun_pos` (from `artanh_lt_div`),
`AFactor`, `quadForm_nonneg` (the discriminant/AM–GM step, via
`4c₁(c₁α²+c₂β²−Pαβ) = (2c₁α−Pβ)² + (4c₁c₂−P²)β²`), and
`secondOrder_of_discriminant` — the implication *discriminant ⟹ deficit ≥ Ω* for
every skew pair `(α,β)`.  Also `hasDerivAt_MFun`: `(MFun δ)′ = E(δu)/u²`, which
identifies `E` as the numerator of the very derivative whose positivity is the
supermodularity behind the global sign flip.  What is **not** formalised is the
discriminant itself — that is the remaining analytic content.

### 6c: the exact reduction, and why multiplier-freeness is impossible

The second-order route reaches only infinitesimal skews.  There is an **exact**
replacement.  `Ω` itself is exact — `Δ_w` is a mixed second difference, so

```
Ω = λκ ∫_b^a ∫_c^d Q(rq) dq dr ,      Q(u) = (u·w′(u))′ = (MFun δ)′ = E(δu)/u²
```

(`hasDerivAt_MFun`), positive under opposite skews since `E > 0`.  For the
deficit, choose the symmetric competitor by **MGL matching**: `f_e(s) = E[f_e(|S|)]`,
`f_e(t) = E[f_e(|T|)]`.  Then `(s,t)` is a legitimate BSC pair, and in
`g(s,t) − gSum` the multiplier terms **cancel identically**
(`gSym_sub_gSum_eq`):

```
g(s,t) − gSum = f_e(δst) − E[f_e(δ|S||T|)]     the MGL gap, ≥ 0 by mgl_jensen
```

giving the exact, `μ,ν`-free criterion (`lagrTwoPoint_le_gSym_iff`)

> **(S′)**  `Ω ≤ f_e(δst) − E[f_e(δ|S||T|)]`   ⟹   `F ≤ g(s,t) ≤ J_sym`

**(S′) is REFUTED.**  At the clean interior point

```
a = 0.983388, b = 0.773061, c = 0.775054, d = 0.993080, δ = 0.999594
(a−b)(c−d) = −4.59e-2  (opposite skews)     Ω = +1.6675e-2
MGL-matched s = 0.885605, t = 0.893749      MGL gap = +1.3859e-2
Ω / MGLgap = 1.2032  > 1
```

(a targeted search reports `17.1`, but at `c = d = 1` where `Ω ≡ 0` — a `0/0`
artefact; the sampled point above is the real refutation).

**This does not touch the conjecture**: (S′) is sufficient, not necessary, and
for the actual `(μ,ν)` the true `J_sym = max g` can exceed `g(s,t)` by much more
than the matched gap.  What it *does* establish is structural:

> **The comparison point cannot be chosen multiplier-free.**  The MGL-matched
> symmetric pair — the only canonical `μ,ν`-independent choice — is too weak.
> Any proof of (S) must use the actual maximiser of `g`, which depends on `μ,ν`.

This also explains the second-order finding: the discriminant needed *global*
maximality of `(s,t)`, and global maximality is exactly a `μ,ν`-dependent
condition.  The two results agree.

Formalised and still valid (they are identities, independent of (S′)):
`feProd`, `mglGap`, `gSym_sub_gSum_eq`, `lagrTwoPoint_le_gSym_iff`,
`lagrTwoPoint_le_of_omega_le_mglGap`.

### The envelope gap quantified — (S) holds with a factor-7 margin

Writing `MGLgap = Φ(U₀,V₀) − E[Φ]` and `EnvGap = conc(Φ)(U₀,V₀) − Φ(U₀,V₀)`,

```
(S)  ⟺  Ω − MGLgap  ≤  EnvGap
     ⟺  Ω  ≤  min_{μ,ν ≥ 0} [ max_{p,q} g_{μν}(p,q) − gSum_{μν} ]
```

The right-hand side is computable **reliably**: `h(μ,ν) = max_{p,q}[f_e(δpq) − μf_e(p)
− νf_e(q)] + μU₀ + νV₀ − E[f_e(δ\|S\|\|T\|)]` is a max of affine functions of `(μ,ν)`,
so the outer minimisation is **convex** — unlike the Nelder–Mead searches that
misled earlier in this file.

At the (S′) counterexample:

```
Ω = 1.6675e-2      min_{μ,ν}[max g − gSum] = 1.2851e-1   at μ = 0.9764, ν = 0.0214
ratio = 0.1298 ≤ 1                                        ⟹ (S) HOLDS
```

so `EnvGap = 0.1146` against `Ω − MGLgap = 0.00282`: the envelope slack exceeds
what is needed by a **factor 40**, and the MGL-matched competitor was capturing
only ~11% of the available deficit.  Over a sweep of opposite-skew
configurations:

> **`max Ω / min_{μ,ν}[max g − gSum] = 0.1435`** (53 configurations) — (S) holds
> in its sharpest form with a factor-7 margin.

Two structural observations.  First, the binding multipliers sit against the
**already-proved** boundary: `μ = 0.9764` in the first case, `ν = 0.9416` in the
sweep's worst case.  Second, the positive-curvature direction of `Φ` is the
**diagonal** — for a Hessian `[[−A, C],[C, −B]]` the positive eigenvalue exists
exactly when `C² > AB` (i.e. `det < 0`), and at `A = B` its eigenvector is
`(1,1)`.  So the envelope is realised by mixing with *both* sides moving
together, which is why any competitor that moves only one side (as MGL matching
does) is too weak.

### **(S4): the conjecture reduces to one finite inequality**

`max g ≥ g` at each of the four corners `(a,c), (a,d), (b,c), (b,d)`, and `gSum`
is exactly their weighted average.  So a purely **finite** sufficient condition is

> **(S4)**   `Ω  ≤  gMax4 − gSum`
>
> the odd gain is dominated by the spread the four corner values already exhibit.

No continuum maximisation, no concave envelope, no `f_e⁻¹` — four values of `f_e` and
`Ω`.  `gSum ≤ gMax4` is already proved (`gSum_le_max4`), so the spread is
automatically `≥ 0`.

**Numerics.**  All four differences `g_ij − gSum = A_ij − μB_i − νC_j` are affine
in `(μ,ν)`, so `min_{μ,ν≥0}[gMax4 − gSum]` is a small **LP** — exactly solvable,
no local-optimum risk:

| test | result |
| --- | --- |
| at the (S′) counterexample | `Ω/spread = 0.4279` ✔ |
| sweep, opposite skews | **`max Ω/spread = 0.684084`** over `100 209` configs ✔ |
| worst case | `a=0.99055, b=0.97438, c=0.89530, d=0.99967, δ=0.98536`, `μ=0.4887, ν=0.8330` |
| degenerate cases (`spread ≤ 1e-12`, 89 of them) | `Ω ≤ 5.4e-10`, `\|spread\| ≤ 2.2e-8` — both vanish together at `\|c−d\| ~ 1e-5` |

So (S4) holds with a `1.46×` margin, and the degenerate cases are exactly the
near-unskewed ones where `Ω → 0` by `omegaTwoPoint_zero_of_snd_eq`.  For
comparison, the sharpest form (`min_{μ,ν}` over the *continuum*) has ratio
`0.1435`; the finite four-corner relaxation costs a factor `4.8` and still
succeeds.

**Formalised** (`FixedPoint.lean`): `gMax4`, `gMax4_le`, `gSum_le_gMax4`,
`lagrTwoPoint_le_gMax4_of_omega_le_spread`, `lagrTwoPoint_le_of_omega_le_spread` — the full chain
*(S4) ⟹ `F ≤ J_sym`*.  Combined with `lagrTwoPoint_lt_of_same_skew` (the
same-skew half, already unconditional), **(S4) is the single remaining
inequality** for the two-point case of the conjecture.

## ★★★ **THE CONJECTURE IS PROVED**

```
averagedBSCConjecture_of_mem : 0 ≤ p → p ≤ 1/2 → AveragedBSCConjecture p
      i.e.   conv 𝒜 = conv ℬ
```

`#print axioms` reports only `[propext, Classical.choice, Quot.sound]`; no
`sorry`, no `axiom`, no `native_decide` anywhere in `BSCAveraging`.

MathOverflow 285151 (asked 2017) = Conjecture 5.2 of Pichler–Piantanida–Matz.
The chain, endpoint cases first: `p = 0` is `averagedBSCConjecture_zero`,
`p = 1/2` is `averagedBSCConjecture_half`, and `0 < p < 1/2` is
`averagedBSCConjecture_of_lt_half`, which runs

```
support-function reduction   regionA_subset_convexHull_regionB   (Hahn–Banach + closed hulls)
        ↑ hypothesis supplied by
domination, all cases        exists_regionB_dominating_all       (regular + 2 degenerate branches)
        ↑
two-point theorem            lagrTwoPoint_le_of_corner_bounds_closed
        ↑ via the bridge
Lagrangian = lagrTwoPoint    lagrangian_eq_lagrTwoPoint_closed
```

and the two-point theorem itself splits on skew direction: same-direction skews
die to the global sign flip, opposite skews are **(S4)**, whose whole content
descends from `z < artanh z`.

## ★ **(S4) IS PROVED — the two-point case of the conjecture is closed**

`lagrTwoPoint_le_of_corner_bounds`: for every `δ ∈ (0,1)` and all
`a,b,c,d ∈ (0,1)`, and any `M` bounding the four corner values of `g`,

```
F  =  lagrTwoPoint δ μ ν a b c d  ≤  M
```

With `M = J_sym = sup_ℬ F` this is **`F ≤ J_sym`**, the conjecture on two-point
supports.  Zero `sorry`; `#print axioms` clean.

**Case split.**  `a = b` or `c = d` gives `Ω = 0`
(`omegaTwoPoint_zero_of_fst_eq/_snd_eq`); same-direction skews give `Ω < 0`
(`lagrTwoPoint_lt_of_same_skew`, from the global sign flip); opposite skews are
(S4).  The four orderings reduce to two by the swap invariance
`lagrTwoPoint_swap` (`(a↔b, c↔d)`).

**(S4) in three steps** (`omegaTwoPoint_le_spread`):

```
STEP 1   Ω ≤ λκδ·|Δ_g|                      HStep_mixed_diff_neg
STEP 3   λκδ ≤ min(w_ac, w_bd)              lam_kap_mul_le_min_weight
STEP 2   min(w_ac,w_bd)·|Δ_g| ≤ gMax4 − gSum spread_ge_min_weight_mul
```

* **Step 1** is the analytic core.  `H(u) = fo(δu)/u + δ·f_e(δu)` has
  `u·H′(u) = δ·K(δu)` with `K(z) = 1 − artanh z/z + z·artanh z` (using
  `fo_sub_mul_deriv`).  `K′(z) = artanh z·(1+1/z²) − 1/z ≥ 0` **exactly when
  `z ≤ (1+z²)·artanh z`**, which follows from `self_lt_artanh`.  `K` increasing
  makes the slice `r ↦ H(rd) − H(rc)` increasing, so the mixed difference of `H`
  — which is `Δ_φ + δ·Δ_g` — is negative.
* **Step 2** is pure 2×2 algebra: drop two non-negative gaps, use `w ≥ w_min`,
  then `2·gMax4 ≥ g_ad + g_bc`.  (An earlier attempt claimed the bound
  `w_ac·|Δ_g|`; the true minimum is `min(w_ac,w_bd)·|Δ_g|`, attained at
  `p = q = D`, not at the origin.  Verified exactly on random 2×2 data.)
* **Step 3** is `a·c·δ ≤ 1` and `b·d·δ ≤ 1`.

> **Everything reduces to `z < artanh z`.**  The sign flip, the supermodularity
> of `f_e(δpq)`, and the odd-gain bound all descend from that one inequality.

Numerically `max Ω/spread = 0.684` over `100 209` opposite-skew configurations,
consistent with the proved bound `max(acδ, bdδ) < 1`.

### Both regions are closed (`Closedness.lean`)

```
T      := {f : Bool → Bool → ℝ | f ≥ 0, row sums 1}     compact  (closed + bounded in ℝ⁴)
val p  : T × T → ℝ³                                     continuous
regionA p = valSet p + coneC,   coneC = {c₀ ≤ 0, c₁ ≥ 0, c₂ ≥ 0}
```

`compact + closed ⇒ closed` (`IsClosed.add_left_of_isCompact`) gives
`isClosed_regionA`; `regionB` is the same argument over `(a,b) ∈ [0,1]²`
(`isClosed_regionB`).  A `Chan` is exactly a member of `T` with its proofs, so
nothing is lost by working with transition functions — this sidesteps `Chan`
having no topology.

**The hulls are closed too.**  The separation step needs `conv ℬ` closed, which
follows from `conv` of a compact set in `ℝ³` being compact.  That is **absent
from Mathlib v4.32.0** (only `Set.Finite.isCompact_convexHull`;
`Mathlib.Analysis.Convex.Normed` does not exist there), so it is supplied here:

```
convexHull S = combMap '' (stdSimplex ℝ (Fin 4) ×ˢ {x | ∀ i, x i ∈ S})    convexHull_eq_combMap_image
isCompact_convexHull : IsCompact S → IsCompact (convexHull ℝ S)
```

The `⊆` direction is Carathéodory: `eq_pos_convex_span_of_mem_convexHull` gives
an affinely independent spanning family, `AffineIndependent.card_le_finrank_succ`
together with `Submodule.finrank_le` bounds its cardinality by
`finrank ℝ³ + 1 = 4`, and the family is padded to exactly four indices along an
embedding `ι ↪ Fin 4` using `Function.extend … 0` (zero weights off the range,
so the sums are unchanged).  Then

```
conv (K + C) = conv K + C          (convexHull_add, C convex)
```

is `compact + closed`, giving `isClosed_convexHull_regionA` and
`isClosed_convexHull_regionB`.

This piece is independent of the conjecture and would be a reasonable Mathlib
contribution on its own.

### The support-function reduction, proved

`regionA_subset_convexHull_regionB`: if every point of `𝒜` is dominated, in every
direction `F = R₀ − μR₁ − νR₂` with `μ,ν ≥ 0`, by some point of `ℬ`, then
`𝒜 ⊆ conv ℬ`.

The sign analysis is what makes only that one family of directions relevant.
Taking both crossovers `1/2` shows `(0,0,0) ∈ ℬ`, and with `regionB_mono` the whole
orthant `{R₀ ≤ 0, R₁ ≥ 0, R₂ ≥ 0}` lies in `ℬ` (`orthant_subset_regionB` — it needs
no constraint on `p` at all).  A separating functional
`f = l₀R₀ + l₁R₁ + l₂R₂` is bounded above on `ℬ`, so testing it on `(0,T,0)`,
`(0,0,T)` and `(−T,0,0)` for large `T` forces `l₁ ≤ 0`, `l₂ ≤ 0`, `l₀ ≥ 0`; and
`l₀ = 0` is impossible because then `f(R) ≤ 0 < u < f(R)` using `R₁, R₂ ≥ 0` on
`𝒜`.  So `l₀ > 0`, and dividing by it gives exactly `F` with
`μ = −l₁/l₀ ≥ 0`, `ν = −l₂/l₀ ≥ 0`.

Mathlib's `geometric_hahn_banach_closed_point` supplies the separation, using the
convexity and the closedness proved above.

**Item 4 is done, and needed no continuity argument at all.**
`lagrTwoPoint_le_of_corner_bounds_closed` holds on the **closed** box
`a,b,c,d ∈ [0,1]` for every `δ ∈ (0,1)`, assuming only non-degeneracy of the two
point laws (`a+b > 0`, `c+d > 0`).  Two observations made the density argument
unnecessary:

* **Atoms at `1`.**  Every use of `a < 1` was to keep a slice inside `Ioo 0 1`.
  With `δ < 1` all products `δ·(r·q)` stay `< 1` even at `r = q = 1`, so the
  slices extend to `Ioc 0 1` (`strictMonoOn_Ioc_of_deriv_pos`, already in
  `SignFlip`).  `fe_mul_slice_strictMonoOn`, `fe_mul_supermodular`,
  `HStep_slice_strictMonoOn`, `HStep_mixed_diff_neg` and `omegaTwoPoint_le_spread`
  were all relaxed to `δ < 1`, atoms `≤ 1`.  This covers the `k → 1` family — the
  boundary that destroyed the uniform margin.
* **Atoms at `0`.**  An atom at `0` makes that side's two-point law degenerate
  (`U ⊥ X` or `V ⊥ Y`) and kills the odd gain: `Ω = 0` outright
  (`omegaTwoPoint_zero_{fst,snd,thd,fth}_atom`, each by `simp` from `fo 0 = 0`).
  So those faces go through `lagrTwoPoint_le_of_omega_nonpos`, whose weight
  lemmas were relaxed from positive to non-negative atoms.

`δ ∈ {0,1}` is not needed: those are `p = 1/2` and `p = 0`, already settled
(`averagedBSCConjecture_half`, `averagedBSCConjecture_zero`).

### The bridge to `mutualInfo` (`Bridge.lean`)

`lagrangian_eq_lagrTwoPoint`: for a binary channel pair, with
`s_u = biasOf (jointUX cL) u`, `t_v = biasOfSnd (jointYV cR) v` and

```
a = s_false,  b = −s_true,  c = t_false,  d = −t_true,   δ = 1 − 2p
```

```
I(U;V) − μ·I(U;X) − ν·I(Y;V)  =  lagrTwoPoint δ μ ν a b c d
```

The weights are *forced*, not chosen: `X` and `Y` are uniform, so
`Σ π_u s_u = 0` and `Σ ρ_v t_v = 0` (`pi_bias_sum_zero`, `rho_bias_sum_zero`),
which with `Σ π = Σ ρ = 1` give

```
π_false = b/(a+b),  π_true = a/(a+b),  ρ_false = d/(c+d),  ρ_true = c/(c+d)
```

— exactly the weights hard-coded into `lagrTwoPoint` (`pi_false_eq` and
friends, each a one-line `linear_combination`).  The `V`-side bias formula
`mutualInfo_jointYV_eq_bias` comes from `mutualInfo_transpose` plus the
existing `mutualInfo_eq_sum_fe_bias`.

So the two-point theorem is now a statement **about the conjecture's own
`mutualInfo`**, not about an algebraic expression.

### The assembly (`Assembly.lean`)

The dictionary between the two languages:

```
f_e(1 − 2α) = log 2 − h₂ α                      fe_one_sub_two_mul
1 − 2(α ⊛ β) = (1−2α)(1−2β)                   one_sub_two_mul_bconv
f_e((1−2α)(1−2p)(1−2β)) = log 2 − h₂((α⊛p)⊛β)   fe_bconv_bconv
```

so every bias pair `(P,Q) ∈ [0,1]²` is realised by an actual BSC pair in `ℬ`
whose Lagrangian value is `gSym` (`exists_regionB_point`).  Combined with the
two-point theorem and `gMax4_eq_corner` this gives
`exists_regionB_dominating_normalised`, and after sign normalisation
(`lagrTwoPoint_neg_swap`, `lagrTwoPoint_neg_swap_snd`, `bias_sign_cases` — the
mean-zero relation forces the two biases to have opposite signs, and relabelling
`U` or `V` maps `(a,b) ↦ (−b,−a)` leaving `F` unchanged),

> **`exists_regionB_dominating`** — for a **regular** channel pair, every `R ∈ 𝒜`
> is dominated in direction `F` by a point of `ℬ`.

"Regular" means: both marginals positive, all four biases in `(−1,1)`, the kernel
positive, and the two biases on each side distinct.

**What is still missing — and a correction.**  Where regularity fails there are
three situations, and they are *not* alike:

* ⚠ **A bias of `±1` is NOT degenerate.**  It means the row is deterministic —
  e.g. `cL` the identity channel, `U = X`; taking both channels the identity gives
  `I(U;V) = I(X;Y) > 0`.  An earlier draft of this section wrongly listed it among
  the cases with `I(U;V) = 0`.  It is not a branch to dispatch but a genuine case
  that the machinery must cover, i.e. the hypothesis `hbL`/`hbR` (biases in the
  *open* `(−1,1)`) is too strong.

  **Now fixed at the formula level**: `negMulLog_row_closed` and
  `mutualInfo_eq_sum_fe_bias_closed` hold on the closed range `|s| ≤ 1`, because
  `f_e(±1) = log 2` exactly cancels the vanishing entropy of a deterministic row
  (`fe_one`, `fe_neg_one`).  Note also that `hker` is automatic once `δ < 1`:
  `1 + δ·s·t ≥ 1 − δ > 0`.

* **A marginal `π_u` or `ρ_v` is `0`** — the auxiliary variable is constant, so
  `I(U;V) = 0`.
* **`s_false = s_true`** — by mean-zero both are `0`, the kernel is `1`, the law
  is a product and `I(U;V) = 0`.

For the last two, `F(R) ≤ 0` and `(0,0,0) ∈ ℬ` dominates.

**All discharged.**  `mutualInfo_jointUX_eq_bias_closed`,
`mutualInfo_jointYV_eq_bias_closed` and `lagrangian_eq_lagrTwoPoint_closed`
carry the closed range — and there `hbL`, `hbR`, `hker` become *derivable*:
positive marginals already force `|bias| ≤ 1` (`biasOf_mem_Icc`), and `δ < 1`
already forces `1 + δ·s·t ≥ 1 − δ > 0`.  The two degenerate branches go through
`mutualInfo_eq_zero_of_row_zero` (a vanishing marginal gives a zero row) and, for
`s_false = s_true`, mean-zero forces both biases to `0`, so `I(U;X) = 0` and DPI
gives `I(U;V) = 0`.  In both `F(R) ≤ 0` and `(0,0,0) ∈ ℬ` dominates
(`exists_regionB_dominating_all`).

### Literature: the conjecture's published home

BSCAveraging, Piantanida & Matz, *Distributed Information-Theoretic Clustering*,
IMAIAI 11(1) 2022, DOI `10.1093/imaiai/iaab007`.

* **Prop 4.3** gives `|U| ≤ |X|`, `|V| ≤ |Y|`, i.e. `|U|,|V| ≤ 2` for binary
  sources — the **two-atoms-suffice** step, hence item 1 below.
* **Conjecture 5.2** (`conv 𝒮ᵢ = conv 𝒮ᵦ`) **is** this conjecture / MO 285151.
* **Prop 5.3** `𝒮ᵦ ≠ 𝒮ᵢ` for DSBS(0) — matches `averagedBSCConjecture_zero`.
* **Closedness is not proved** for any region there, which bears on item 2.

(Read via page summary, not full text — verify Prop 4.3's convexification clause
before leaning on it.)

### What remains for the full conjecture — four items

| # | item | rating |
| --- | --- | --- |
| 1 | two atoms suffice (`\|U\| = \|V\| = 2`) | **settled** — Prop 4.3 of the DIC paper (Lean work only) |
| 2 | support-function converse: `𝒜 ⊆ conv ℬ` from `sup_𝒜 F ≤ sup_ℬ F` | **A** — `regionA_subset_convexHull_regionB` |
| 3 | bridge from `mutualInfo` to `lagrTwoPoint` for binary `U,V` | **A** — `lagrangian_eq_lagrTwoPoint` (`Bridge.lean`) |
| 4 | boundary atoms (`0` or `1`) | **A** — `lagrTwoPoint_le_of_corner_bounds_closed` |

Item 3 is easy to overlook: `BiasCoords.lean` proves `I(U;V) = Σ π ρ f(δ s t)` and
`I(U;X) = Σ π f_e(s)`, but the assembly *"for binary `U,V` the Lagrangian equals
`lagrTwoPoint δ μ ν a b c d`"* is not written.  Until it is, the two-point theorem
is a statement about an algebraic expression rather than about the conjecture.

Item 4 deserves more suspicion than "routine continuity".  The boundary is
exactly where this problem has repeatedly misled: the `k → 1` family (which
destroyed the uniform margin and was invisible to three separate samplers), the
`m → 0` singular limit of the fixed-point system, and the `F > 0` BSC pairs at
`m ~ 1e-12`.  `δ` at its endpoints is already covered
(`averagedBSCConjecture_half`, `averagedBSCConjecture_zero`); atoms at `0`/`1`
are not.

Note the proved theorem imposes **no sign constraint on `μ,ν`** — they are free
reals, which is stronger than the support-function reduction requires — and
`gSym(p,q)` is `F` at the BSC pair `(p,q)` (checked to `4.4e-16`), so `M = J_sym`
is a legitimate instantiation.

**Overall rating for the conjecture: B3.**  The analytic core that resisted the
twelve refuted approaches is proved and machine-checked; what is left is one
genuine open case and three reduction steps that are standard in kind.

### ⚠ **`F ≤ 0` is NOT the conjecture** — scope correction

The conjecture is `conv 𝒜 = conv ℬ`, i.e. via support functions

```
sup_𝒜 F = sup_ℬ F        F = I(U;V) − μ·I(U;X) − ν·I(Y;V)
```

Since `ℬ ⊂ 𝒜` the content is `sup_𝒜 F ≤ sup_ℬ F`.  It is **not** `F ≤ 0`.  For a
BSC pair (`m = 0`, `a = b = s`, `c = d = t`) the value is

```
F_ℬ(s,t) = f_e(δst) − μ·f_e(s) − ν·f_e(t)
```

and `sup_{s,t} F_ℬ` is **positive** for small `μ,ν`.  A sampler driven into
`k → 1` finds solutions of (E2),(E4) with `F > 0` — three examples, all with
fsolve residual `< 1e-9`, `μ,ν ∈ (0,1)`, and verified V-side best responses:

| `m` | `k` | `δ` | `c = d` | `μ` | `ν` | `F` | margin |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `1.1e-12` | `0.997836` | `0.3939` | `0.979057` | `0.0458` | `0.0701` | `+8.69e-5` | `−5.6e-4` |
| `6.8e-13` | `0.999671` | `0.1064` | `0.978924` | `0.0025` | `0.0049` | `+5.96e-4` | `−5.5e-2` |
| `1.3e-12` | `0.999906` | `0.0765` | `0.930115` | `0.0010` | `0.0033` | — | `−9.5e-3` |

**All three are symmetric** (`a = b`, `c = d`, `m ≈ 0`) — i.e. they *are* BSC
pairs, so `F > 0` there is legitimate.  Confirmed decisively at the first one by
maximising `Φ` over **all** `(m,k,c,d)`:

```
global max Φ over (m,k,c,d) = +8.7256154e-05   at m ≈ 0, c = d = 0.97905676  (SYMMETRIC)
sup over BSC pairs      F_ℬ = +8.7256154e-05   at s = 0.99783622, t = 0.97905676
```

identical to 9 significant figures, with the global maximiser a BSC pair.  **The
conjecture holds there; there is no counterexample.**

**What this invalidates.**  `margin ≥ 0` ⟺ `F ≤ 0` is the right target *only at
multipliers where* `sup_ℬ F = 0`.  (M) below, the tangent-gain bound, and the
whole margin programme silently carry that hypothesis.  The correct target is

> `sup_𝒜 F ≤ sup_ℬ F`, equivalently: **every maximiser of `F` is symmetric**

which is also what §5d compares against, so the framing is recoverable.

**What survives untouched.**  Every formalised result in `FixedPoint.lean` is an
*identity* or an equivalence — closed forms, route identity, bitangency
reduction, `tanGain_eq`, mirror identity, `PhiVal_nonpos_iff_*`.  These do not
depend on the target and remain correct; only the *reading* of `Φ ≤ 0` as "the
conjecture" was too strong.

### **(M) — the missing inequality, in closed form**

The tangent-line gain `Tan(x) = φ(x) − x·φ′(x) − φ(0)` has an elementary closed
form.  From `f_e(y) = y·artanh y − A(y)` with `A(y) = −½log(1−y²)`, the
`κ·x·artanh(m+κx)` terms cancel identically, giving (`tanGain_eq`, no integral,
no `f_e`):

```
Tan(x) = ν·A(x) − A(m+κx) + A(m) + m·[artanh(m+κx) − artanh m],    κ = kδ
```

At a bitangent (E4) point `Tan(c) = Tan(−d) = gain`.  So, with
`b₁ = m+κc`, `A_U = ½[f_e(m+k)+f_e(m−k)]`, `μ = 2δκ_V·Δℓ/D`, `κ_V = cd/(c+d)`:

> **(M)**  `ν·A(c) − A(b₁) + A(m) + m·[L(b₁) − L(m)]  ≤  μ·(A_U − f_e(m))`
>
> for all `(a,b,c,d,δ)` satisfying (E4), where `m = (b−a)/(a+b)`, `k = 2ab/(a+b)`,
> `ν = kδΔℓ/(L(c)+L(d))`.

`Φ ≤ 0 ⟺ (M)` is `PhiVal_nonpos_iff_tanGain_le`.  Equivalent forms:

```
(M)  ⟺  gain ≤ 𝒥(U;V)·ρ(U;X)          𝒥(U;V) = kδκ_V Δℓ
     ⟺  ρ(U;V) − ρ(Y;V) ≤ ρ(U;X)      "excess over the V-side is paid by the U-side"
```

Five real variables, one constraint, no inverse function, no optimisation, no
integral — only `log` and `artanh`.  Numerically `max[gain − μ·I(U;X)] ≈ −1.7e-9`
over sampled fixed points (attained at the degenerate `𝒥 → 0` points), while in
**ratio** form the margin is `≥ 0.119`.

#### Venues 3 and 5 — outcomes

**Venue 5 (linearity in `ν`) — formalised, but the wrong working form.**
`Tan(c)` is linear in `ν` with coefficient `A(c) > 0`, and `μ·I(U;X)` contains no
`ν`, so (M) is exactly a threshold (`PhiVal_nonpos_iff_nu_le`):

```
(M)  ⟺  ν ≤ ν* := [ μ·I(U;X) + A(b₁) − A(m) − m·(L(b₁) − L(m)) ] / A(c)
```

Holds at 600/600 sampled fixed points — but `min[ν* − ν] = 1.7e-7` and
`min ν*/ν = 1.000012`, i.e. **the threshold is attained** at the degenerate
points (`d → 0`, `μ → 0`, `𝒥 → 0`).  So the `ν`-form inherits the same boundary
tightness as the `F`-form and is unsuitable as a working formulation.

**Venue 3 (`m`-expansion) — premise refuted, but a better fact found.**
`m = 0` is a *singular* limit of the fixed-point system, not a solution: at
`m = 0`, `L̄ = ½[L(κt) + L(−κt)] = 0` forces `μ = 0`, and (E2) then reads
`0 = δtL(κt) ≠ 0`.  Worse for the expansion, `|c−d|/m` is **not** bounded — it
ranges over `[3.4e-6, 71.5]` across the sample — so `c−d = O(m)` fails and there
is no single-parameter expansion in `m`.

What the scan did establish is more useful:

| stratum | n | min ratio margin | max `μ` |
| --- | --- | --- | --- |
| `m ∈ [1e-7,1e-5)` | 90 | `0.3312` | `0.777` |
| `m ∈ [1e-5,1e-3)` | 355 | `0.3462` | `0.711` |
| `m ∈ [1e-3,1e-2)` | 83 | `0.2797` | `0.939` |
| `m ∈ [1e-2,1e-1)` | 41 | `0.3427` | `0.824` |
| `m ∈ [1e-1,1)` | 31 | `0.3306` | `0.837` |

No boundary layer appears as `m → 0` *in this sample* — but that sample drew
`k ~ U(0.05, 1−m−0.05)`, so it never reached `k → 1`.

### **THE UNIFORM MARGIN IS FALSE.**

A targeted probe along `k → 1` (with `m ≈ (1−k)/10`, `δ = k`) gives

| `k` | `G(a,b)` | `G(c,d)` | `ρ(U;V)` | **margin** | `ν` | `margin·artanh a` |
| --- | --- | --- | --- | --- | --- | --- |
| `1−1e-7` | `0.08244` | `0.49805` | `0.49805` | `0.0824` | `1.0000` | `0.68901` |
| `1−1e-9` | `0.06472` | `0.48075` | `0.48075` | `0.0647` | `1.0000` | `0.68990` |
| `1−1e-12` | `0.04894` | `0.38860` | `0.38860` | `0.0489` | `1.0000` | `0.69069` |

Along this family `G(c,d) = ρ(U;V)` **exactly**, so `margin = G(a,b)`, and

```
margin · artanh(a) → log 2 = 0.693147,     i.e.   margin ~ log 2 / artanh(a) → 0
```

The infimum of the ratio-form margin is therefore **`0`**, and the conjecture is
asymptotically tight in ratio form as well — there is no slack anywhere.

This retracts the "never tight anywhere" claim above, which rested on a sampler
that could not reach `k → 1` — the same sampling artefact that produced the false
(B).  Consequently **venue-4 blocker (2) stands**: interval branch-and-bound
cannot certify an inequality that degenerates to equality, in either form.

Note `ν → 1` along the whole family, with `1 − ν` vanishing *much* faster than the
margin (`margin/(1−ν) → ∞`).  So the critical family sits against the boundary of
the region already proved (`ν ≥ 1`), approached from inside the unproved side.

**Corrected target.**  An absolute uniform margin is unavailable; the honest
replacement is a *scale-free* bound, e.g. `margin ≥ c·G(a,b)` for an explicit
`c > 0` — along the critical family `margin/G(a,b) → 1`, and at the max-DP point
it is `0.897`, so any such `c` must satisfy `c ≤ 0.897`.

#### Venues to attack (M)

1. **The mirror pair — DONE, a simplification, not a proof.**  Formalised as
   `tanGain_mirror`, `mirror_identity`, `mutualTP_eq_jeffreys_add`,
   `lautum_closed`.  Outcome: (E4) restated with **no `f_e`**,
   `ν[A(c) − A(d)] = A(b₁) − A(b₂) − m·Δℓ`, hence (★); plus closed forms
   `I(U;V) = 𝒥 + A(m) − Ā + m(L̄ − L(m))` and `L(U;V) = Ā − A(m) − m(L̄ − L(m))`
   holding with **no fixed-point hypothesis**.  It does *not* prove (M) — every
   route through it closes back to `ρ(U;V) ≤ G(a,b)+G(c,d)`, because identities
   cannot produce an inequality.  Its real value: the *constraint* now lives in
   the same elementary class (`log`, `artanh`) as the target, which is the
   precondition for venue 4.
2. **Affine MGL.**  Bound `E[f_e(m+κT)]` for mean-zero `T` by a one-dimensional
   matching quantity.  Both naive candidates are refuted (`+0.318`, `+0.019`), so
   this needs a new statement — e.g. matching a functional other than `f_e`, or
   matching against the *two*-parameter family that the offset genuinely
   requires.  Characterise the true extremiser numerically before guessing again.
3. **`m`-expansion.**  `m = 0` is proved (§5d, and now also via `gain_le_phiV_of_mgl`).
   The closed form is analytic in `m` with the `m`-linear term `m[L(b₁) − L(m)]`
   explicit.  A second-order-in-`m` argument may reach the whole regime, since
   the scans put the hard fixed points at `m ≤ 10⁻²`.
4. **Direct elementary attack.**  (M) is now a `log`/`artanh` inequality in five
   variables.  Substituting `A(y) = ½log(1/(1−y²))` makes both sides sums of
   logarithms; the constraint (E4) is also a `f_e`/`artanh` identity.  This is the
   first form of the problem where interval arithmetic / branch-and-bound
   (route 4) is realistically applicable — no `f_e⁻¹`, no envelope, no sup.
5. **Convexity in `ν`.**  `Tan(x)` is *linear* in `ν` with coefficient `A(x) > 0`,
   while `ν` itself is pinned by `ν = kδΔℓ/(L(c)+L(d))`.  Treating `ν` as free and
   optimising the difference `(M)` in `ν` alone may give a clean sufficient
   condition covering the region where `ν` is far from its extremes.

### Which fixed-point conditions are actually needed — a relaxation ladder

The fixed-point set is 3-dimensional (`m,k,δ`) inside the 5-dimensional data
`(a,b,c,d,δ)`, so it is cut out by **two** equations, (E2) and (E4).  (E2) is
consumed as the *definition* of `μ`, leaving only the multiplier ranges and (E4)
as usable content.  Relaxing the fixed-point conditions one at a time and
maximising `ρ(U;V) − ρ(U;X) − ρ(Y;V)` (target `≤ 0`) gives:

| constraints imposed | max gap (sweep / targeted) |
| --- | --- |
| none — free two-point data | `+0.126` / **`+0.428`** |
| opposite skews only (proved at maximizers) | `+0.156` / **`+0.371`** |
| `μ,ν ∈ [0,1)` only (`μ≥1`, `ν≥1` already proved) | `+0.136` / **`+0.428`** |
| `μ,ν ∈ [0,1)` **and** opposite skews | `+0.119` / **`+0.365`** |
| full fixed point (E2 **and** E4) | `≤ −0.17` *in the sampled region only* — no uniform margin exists (infimum `0`; negative near the symmetric locus) |

Every relaxation fails, and the last row is a genuine interior counterexample
(`a=0.99999, b=0.2118, c=0.8807, d=0.9985, δ=0.312, μ=0.017, ν=0.008`, opposite
skews) — not a boundary artefact.  So:

> **(E4) is the irreducible ingredient.**  The multiplier bounds and the sign
> flip, which are the two things already proved, provably do not suffice in any
> combination.  No argument that uses only `μ,ν < 1` and the skew ordering can
> work.

(E4) in usable form, with `ν = kδΔℓ/(L(c)+L(d))`:

```
f_e(b₁) − f_e(b₂) − ν·[f_e(c) − f_e(d)]  =  (c+d)·[k·δ·L(b₁) − ν·L(c)]
```

Note (E4) is **automatically satisfied at symmetric points** (`m=0`, `c=d=t`,
where both sides vanish and it reduces to the definition of `ν`).  So (E4)
carries exactly the asymmetric content — which is why §5d, which handles the
symmetric slice, never needed it, and why every asymmetric route so far has
stalled.  Any future attempt should start from (E4), not from the multipliers.

### The standing constraint on any proof

Every failure above has the same shape: the supremum over symmetric competitors
was replaced by one specific competitor, chosen by matching a scalar (a rate on
either side, a penalty, the same `k`) or by a monotonicity.  Four matchings and
one monotonicity are now refuted. A good symmetric competitor always
exists — `J = J_sym` holds to machine precision in every scan run here — but it
is not produced by any local rule. **A proof must keep `max_{k′} F_opt(0,k′)`
intact and argue variationally.** Correspondingly, the one place where a
comparison *has* succeeded is §5d, which does exactly that: it works at a
critical point of the symmetric problem and uses its stationarity.

---

## 7. The `p = 0` conjectures of Entropy 24(9):1321 — the LP/certificate reduction

Dikshtein–Ordentlich–Shamai state three conjectures for the *unhulled*
double-sided bottleneck `R(Cu,Cv,p)`.  §7a records why the hull theorem cannot
reach them; §7b–§7d the reduction that can, and what is now proved.

### 7a. Why `conv 𝒜 = conv ℬ` is silent about them

The hull theorem pins down the **concave envelope** of `R(·,·,p)`, nothing more.
Numerically (`numerics/` and the README table) the BSC surface
`F_p(Cu,Cv) = log 2 − h₂(a ⊛ p ⊛ b)` lies *strictly* below its own concave
envelope on the whole open square, for every `p` — the touching set is only the
boundary edges.  So all three conjectures, which are pointwise statements about
the interior, live in the part the hull erases.  The sharpest illustration is
their Theorem 1: BSC optimality holds as `p → 1/2`, yet there
`F_p ≈ c·u(Cu)·u(Cv)` is a product, hence a saddle, hence non-concave.

Corollary, still worth having (`Envelope.lean`): `R ≤ concEnv F_p`, which beats
their Proposition 6 upper bound on 51–64 % of the grid, by up to 0.036 bits.

Stronger structural point.  **Every lemma on our proof path is `δ`-uniform.**
Any chain of them proves BSC optimality at `p = 0` too, which is false.  So no
recombination of the existing toolkit can prove Conjecture 3; a proof must
consume `δ < δ₀` quantitatively.  Measured thresholds: `θ(Cu,Cv) ≤ 0.0152`
over the grid, maximal near `(0.4,0.4)`, decaying to `0.0014` at `(0.95,0.95)`.
So the hard regime is `δ ∈ (0.97,1)` — near the *boundary*, not near `δ = 0`.

### 7b. At `p = 0` the one-sided problem is a linear program over measures

Fix the `V`-side.  With `f(z) = (1+z)log(1+z)` and the atom value

```
φ_T(s) = Σ_v ρ_v · f(δ·s·t_v)
```

the two quantities in play are `I(U;V) = E_π[φ_T(S)]` and `I(U;X) = E_π[f_e(S)]`,
both **linear in the law of `S`**, and the law is constrained only by
`E[S] = 0` (`X` uniform), `E[f_e(S)] ≤ Cu`, `E[1] = 1`.  Three linear constraints:

* extreme points have ≤ 3 atoms (Richter–Rogosinski) — nearly their Prop. 3;
* the dual is an **envelope condition**: any `(λ₀,λ₁,λ₂)` with `λ₂ ≥ 0` and

```
      φ_T(s) ≤ λ₀ + λ₁ s + λ₂ f_e(s)      for all s ∈ [−1,1]                (★)
```

  certifies `I(U;V) ≤ λ₀ + λ₂·Cu` for *every* `U`-side channel meeting the
  constraint.  The `λ₁` term is free: `E[S] = 0`.

`(★) ⟹ bound` is proved: `bestResponse_le_of_certificate` and its mirror
`bestResponse_le_of_certificate'` in `BestResponse.lean`, stated for general
`p`, not just `p = 0`.

### 7c. The certificates the two conjectures need, and why they should be provable

Write `D(s) = λ₀ + λ₁ s + λ₂ f_e(s) − φ_T(s)`.  For the conjectured optima:

| | `S` | `T` | contacts |
| --- | --- | --- | --- |
| Conj 1 (max `I(U;V)`) | `(a, −1)` Z | `(+1, −d)` S | `s = a` (tangency), `s = −1` (endpoint) |
| Conj 2 (min `I(U;V)`) | `(+1, −a)` Z | `(+1, −d)` Z | `s = −a` (tangency), `s = +1` (endpoint) |

`numerics/p0_certificate.py` solves the three contact equations for
`(λ₀,λ₁,λ₂)` and checks the certificate.  At every `(Cu,Cv)` tested it holds —
`D ≥ 0` for Conj 1, `D ≤ 0` for Conj 2, contacts exact, `λ₂ > 0`, healthy slack
elsewhere (`D(1) ≈ 0.05–0.11`).

The mechanism that should turn this into a theorem: **`D''` has exactly one
sign change**, because

```
D''(s)·(1−s²)(1 + s·t_false)(1 + s·t_true)   is a quadratic in s.
```

Verified numerically at every test point (exactly one sign change).  Given
that, `D ≥ 0` follows from root counting: `D''` with one sign change ⟹ `D'` has
≤ 2 zeros ⟹ `D` has ≤ 3 zeros with multiplicity, and the contact conditions
already supply 3 (a double zero at the tangency, a simple one at the endpoint).

### 7c′. The certificate is now a theorem (`PZero.lean`)

Both collapses hold, and the argument closes:

* `DFun''_eq` — `D″(s)·(1−s²)(1−d·s) = (λ₂−d) + d(1−λ₂)s`.  The `s²` coefficient
  is `d²ρ₊ − d·q₊ = d²/(1+d) − d²/(1+d) = 0`; that cancellation is what makes
  `N` linear rather than quadratic.
* `key_log_sum` — the needed `N(a) ≥ 0` is **exactly** `log_sum_two` on the
  pairs `(1−d, 1−d)` and `(d(1−a), 2d)`.  Nothing analytic is required beyond
  the log-sum inequality the repository already had for the DPI.

Closed forms, obtained by solving the three contact equations:

```
λ₂ = log((1−d·a)/(1+d)) / log((1−a)/2)          0 < λ₂ < 1
λ₂ < 1  ⟺  (1+a)(1−d) > 0                       (lam2_lt_one)
f_e(a) − log 2 − (1+a)·artanh a = log((1−a)/2)     (fe_sub_tangent)
φ_d(a) − (1+a)·φ_d′(a) = log(1−d·a)              (phiZ_sub_tangent)
φ_d(−1) = log(1+d)                               (phiZ_neg_one)
```

`DFun_nonneg` is `sorry`-free: to the right of `a`, `D′` increases from
`D′(a) = 0` so `D` increases (`DFun_nonneg_right`); between the sign change of
`N` and `a`, `D′ ≤ 0` so `D` decreases into its double zero
(`DFun_nonneg_middle`); to the left, two applications of the mean value theorem
against the monotonicity of `D′` contradict any `D(s) < 0`
(`DFun_nonneg_left`).

### 7c″. The mirror certificate (Conjecture 2) — and it is *not* log-sum

Against the same `T = (+1,−d)`, Conjecture 2's conjectured best response is
`S = (+1,−a)`: contacts move to `s = −a` (tangency) and `s = +1` (endpoint),
and the certificate flips sign (`G ≤ 0`, i.e. `φ_d` above the affine function).
Same `N`, same collapse, opposite shape — `GFun_nonpos_of_contacts` is the
mirror of `GFun_nonneg_of_contacts`, both now generic in `(λ₀,λ₁,λ₂)`.

The multiplier is again closed-form:

```
mlam2 = [ 2d·M − (1−d)·L ] / [ (1+d)·M ],   M = log(2/(1−a)),  L = log((1+d·a)/(1−d))
```

and `N(−a) ≤ 0` reduces, after clearing `(1−d) > 0`, to

```
d(1−a)·log(2/(1−a))  ≤  (1+d·a)·log((1+d·a)/(1−d))                  (key_mirror)
```

This is **not** a log-sum instance.  It follows from two applications of
`log x ≤ x − 1`, sandwiching both sides against `d(1+a)`:

```
log(2/(1−a)) ≤ (1+a)/(1−a)              ⟹ LHS ≤ d(1+a)
−log(1−d) ≥ d,  log(1+da) ≥ da/(1+da)   ⟹ RHS ≥ da + d(1+da) = d(1+a) + d²a
```

`MDFun_nonpos` is `sorry`-free.

### 7c‴. The fixed points at `p = 0`

At `δ = 1` the atom-value derivative collapses, because `E[T] = 0` kills the
`+1` in `f′`:

```
φ_T′(s) = Σ_v ρ_v t_v log(1 + s t_v) = κ_T · log((1+sc)/(1−sd)),   κ_T = cd/(c+d)
```

so both sides' tangency conditions are governed by the *same* quantity

```
Λ = log[ (1+ac)(1+bd) / ((1−ad)(1−bc)) ]        symmetric under (a,b) ↔ (c,d)
λ₂ = κ_T·Λ / (artanh a + artanh b),   μ₂ = κ_S·Λ / (artanh c + artanh d)
```

**Counting.**  A side with two *interior* atoms imposes 4 contact conditions
(`D = D′ = 0` at each atom) on 3 multipliers — one residual equation, the
bitangency condition.  A side with an atom at `±1` imposes only 3 (no tangency
at an endpoint, just an inequality) — **no residual**.  So corner (Z/S)
configurations are stationary *for free*, at every rate; interior ones are not.

Numerically (`numerics/`, 361 starts per rate pair, both residuals solved
simultaneously subject to the two rate constraints): the *only* interior fixed
point is the symmetric BSC pair —

| `(Cu,Cv)` bits | interior fixed points |
| --- | --- |
| (0.4,0.4) | 1, at `a=b=c=d=0.70780` |
| (0.4,0.6) | 1, at `a=b=0.70780`, `c=d=0.84124` |
| (0.2,0.7) | 1, at `a=b=0.51399`, `c=d=0.89352` |

**Half of the classification is now a theorem** (`PZeroSymm.lean`).  Two further
collapses, both special to `δ = 1`:

* for a *general* two-atom `T = (c,−d)` the second derivative of the atom value
  loses its linear term too — the coefficient is `cd(ρ₋d − ρ₊c) = cd·(cd−dc)/(c+d) = 0` —
  leaving `φ_T″(s)·(1+sc)(1−sd) = cd`, so `D″` is a **quadratic** over positive
  denominators and `D` has at most four zeros with multiplicity.  A bitangency
  spends exactly four, which is why interior fixed points are rigid;
* a *symmetric* `T` makes the atom value **even**: `φ_(c,c)(s) = f_e(c·s)`.

Then, for symmetric `T`, evaluating the certificate `D ≥ 0` at the **mirrored**
points gives, using `D(−s) = D(s) − 2λ₁s`,

```
D(−a) = −2λ₁a ≥ 0  and  D(b) = +2λ₁b ≥ 0   ⟹   λ₁ = 0        (lam1_eq_zero)
```

so `D` is even and `b` is a contact too.  Now `D′` vanishes at `0` (oddness), at
`a`, and — Rolle between the two contacts — at some `ξ` in between; two more
Rolle steps give two *distinct* zeros of `D″` in `(0,1)`.  But
`D″(z) = 0 ⟺ λ₂(1−c²z²) = c²(1−z²)`, and subtracting two such gives
`(z₁²−z₂²)·c²(λ₂−1) = 0`, forcing `λ₂ = 1` and then `c = 1`
(`DSym''_eq_zero_unique`).  Contradiction, so `a = b`:

```
interior_response_symmetric : against a symmetric T, a bitangent interior response is symmetric
```

Consequence: **no half-asymmetric interior fixed point exists.**  A symmetric
side forces a symmetric response, so the interior fixed points are either fully
symmetric — the BSC pair — or fully asymmetric on both sides, which the numerics
do not find.

So the conjectured picture at `p = 0` is: **every fixed point is either the BSC
pair or has an atom at `±1`.**  Conjecture 1 then reduces to a finite
comparison — Z/S versus Z/Z versus BSC — where the orientation is settled by
the sign flip and the certificates above settle each side's optimality.  What
remains unproved is the uniqueness of the interior fixed point (C9) and the
branch value comparison.


### 7c⁗. Interior uniqueness at `p = 0`: the Λ symmetry closes it

Write the atoms in `θ = artanh` coordinates and split each side into centre and
half-gap: `α,β = m ± u` for `S`, `γ,δ = n ± v` for `T`.  With `L = log cosh`,

```
Λ = L(α+γ) + L(β+δ) − L(α−δ) − L(β−γ)
  = L(X+m+n) + L(X−m−n) − L(X+m−n) − L(X−m+n),        X := u + v
```

so — because `L` is even — **Λ sees the two skews only through their sum `X`**.
Shifting each side by its own skew turns both tangency conditions into the same
odd-kernel form with `M_g(w) := L(w+g) − L(w−g)`, and the bitangency residual
becomes *function minus its own chord* against a shifted `sech²`:

```
R_S = ∫_{X−m}^{X+m} [ M_n(w) − chord_{[X−m,X+m]}M_n(w) ] · sech²(w−v) dw
R_T = ∫_{X−n}^{X+n} [ M_m(z) − chord_{[X−n,X+n]}M_m(z) ] · sech²(z−u) dz
```

**The key inequality.**  `(★)  v > 0 and X ≥ 0 ⟹ R_S > 0.`  Proof:

1. *Green's function.*  Both the deficit and `K(w) := L(w−v) − chord L(·−v)`
   vanish at the window ends, so two integrations by parts give
   `R_S = ∫ M_n″(w)·K(w) dw`, and `K ≤ 0` because `L` is convex.
2. *Fold.*  `M_n″` is odd and negative on `(0,∞)`.  With `q = X+m`, `−p = m−X`,

   ```
   R_S = ∫_0^{m−X} M_n″(t)·[K(t) − K(−t)] dt + ∫_{m−X}^{m+X} M_n″(t)·K(t) dt
   ```

   (the case `X ≥ m` needs nothing: the window lies in the concave half, so the
   deficit is `≥ 0` throughout).
3. *Second piece.*  `(≤0)·(≤0) ≥ 0`, strictly positive when `X > 0`.
4. *Reflection difference.*  The chord slope of `L(·−v)` over the window is
   exactly `M_m(u)/(2m)`, whence

   ```
   K(t) − K(−t) = −M_v(t) − t·M_m(u)/m
   ```

   so the first piece is `≥ 0` iff `M_v(t) + t·M_m(u)/m ≥ 0` on `(0, m−X)`.
   For `u ≥ 0` both terms are `≥ 0`.
5. *The `u < 0` case.*  `M_v(t)/t` is decreasing (`M_v` odd, concave on `t>0`),
   so it suffices at `t = m−X`, i.e.

   ```
   (♦)   m·M_v(m−X) ≥ (m−X)·M_m(v−X)
   ```

   Divide by `m(m−X)`: with `Φ(g,y) := [L(y+g) − L(y−g)]/g` this reads
   `Φ(m−X, v) ≥ Φ(m, v−X)`, and **both sides have the same `g+y = m+v−X =: Y`**.
   So it is one function of `g`: `ϕ(g) = [L(Y) − L(Y−2g)]/g`, decreasing iff
   `2g·tanh(Y−2g) ≤ L(Y) − L(Y−2g)` — which, with `z = Y−2g`, is exactly the
   tangent-line inequality `L(z) + L′(z)(Y−z) ≤ L(Y)` for the **convex** `L`.
   Equality iff `g = 0`, i.e. iff `X = 0`.

**Consequence.**  By oddness `(★)` also gives `v < 0, X ≤ 0 ⟹ R_S < 0`, and the
mirror `(m,u) ↔ (n,v)` gives the same for `R_T` in `u`.  At an interior fixed
point both residuals vanish, so

* `v > 0 ⟹ X < 0`, `v < 0 ⟹ X > 0`, `v = 0 ⟹ X = 0` (there `M_0 ≡ 0`);
* `u > 0 ⟹ X < 0`, `u < 0 ⟹ X > 0`, `u = 0 ⟹ X = 0`.

Every sign combination contradicts `X = u + v`: `u,v > 0` forces `X > 0` and
`X < 0`; `u > 0 > v` forces `X < 0` and `X > 0`; and if either vanishes so does
`X`, hence so does the other.  Therefore `u = v = 0`:

> **At `p = 0` the only interior fixed point is the symmetric (BSC) pair.**

`numerics/p0_interior_uniqueness.py` checks every step — Green identity to
`10⁻¹⁴`, `K ≤ 0`, the chord-slope identity, and `R_S > 0` with both pieces
nonnegative over 1764 configurations, no violations.  The argument is now a
Lean theorem — see §7c⁶.  It needs only `intervalIntegral` (FTC-2, additivity,
`comp_neg`, positivity) from `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`;
no integration-by-parts lemma, because the Wronskian `FG′ − F′G` is an explicit
antiderivative of `FG″ − F″G` (`green_identity`), and every integrand is
continuous, so integrability is one step.


### 7c⁶. §7c⁗ is a Lean theorem — the analytic core of `(B)`

`LogCosh.lean` formalises the whole interior-uniqueness argument of §7c⁗,
axiom-clean (no `native_decide`).  Layers:

**Elementary.**  `LC w = log cosh w` with `L′ = tanh` (`hasDerivAt_LC`),
`L″ = sech²` (`hasDerivAt_tanh`), `L` even, `tanh` monotone, and the tangent-line
inequality `LC_tangent_le` (from a generic `tangent_le_of_monotone_deriv`).  The
odd kernels are `MG g w = L(w+g) − L(w−g)`, with `MG_symm : M_g(w) = M_w(g)`,
`MG_odd`, `MG_pos`, and `MGpp n w = sech²(w+n) − sech²(w−n)` (`MGpp_odd`,
`MGpp_neg`).

**Step 5 (the tangent-line reduction).**  `phi_antitoneOn` — `ϕ(g) =
(L(Y) − L(Y−2g))/g` is decreasing, *literally* `LC_tangent_le` — and
`MG_div_antitoneOn` / `MG_div_strictAntiOn` — `M_v(t)/t` decreasing, from
concavity of `M_v` on `[0,∞)` via one mean-value theorem.  Together:

> **`diamond`**  `(m−X)·M_m(v−X) ≤ m·M_v(m−X)` for `X ≥ 0 < m−X`,

because both sides are `Φ(g, Y−g)` with the *same* `Y = m+v−X`.

**Steps 1–3 (Green and the fold).**  No integration-by-parts lemma is needed:
the Wronskian `F G′ − F′ G` is an antiderivative of `F G″ − F″ G`, so one
`integral_eq_sub_of_hasDerivAt` gives

> **`green_identity`**  `∫ F·G″ = ∫ F″·G` when `F` and `G` vanish at both ends.

With `Dfun` the deficit of `M_n` against its chord over `[X−m, X+m]` and `Kfun`
the same for `L(·−v)`, this is `residual_green`:
`R_S = ∫ M_n″·K`.  `Kfun_nonpos`/`Kfun_neg` (`K ≤ 0`, `< 0` inside) come from a
self-contained two-MVT proof that a function with (strictly) decreasing
derivative and zero boundary values is (strictly) positive inside — no `ConvexOn`
API.  The fold uses `integral_comp_neg` plus `MGpp_odd`, and the chord-slope
identity is `Kfun_reflect`:

```
K(t) − K(−t) = − M_v(t) − t·M_m(u)/m .
```

**The theorem.**

> **`residual_pos`**  `0 < R_S(m,n,u,v)` whenever `m,n > 0`, `v ≥ 0`,
> `X = u+v ≥ 0`, and `(v,X) ≠ (0,0)`.

(The hypothesis is `0 ≤ v` rather than `0 < v`: when `u < 0` the constraint
`X ≥ 0` already forces `v > 0`, and when `v = 0` strictness comes from the outer
piece.)  `RS_odd` gives the mirror sign, and the six-way sign chase is

> **`skews_vanish`**  `R_S = 0` and `R_T = 0` `⟹` `u = v = 0`:
> **at `p = 0` the only interior fixed point is the symmetric (BSC) pair.**

**What `(B)` still needs.**  Only the *bridge*, not the analysis: `Bitangency`
(Lagrange multipliers for the one-sided linear program) and the identification of
the Lean-side residual of `Conj12.lean` with `RS` in the `θ = artanh` atom
coordinates.  The mathematics of §7c⁗ is now machine-checked.

### 7c⁷. The bridge from bitangency to `R_S` — `(B)`'s analysis is complete

The residual identification of §7c⁗, which the notes only sketched, turns out to
be short once one computes the *atom value's* derivative.  With the `V`-side
atoms `tanh γ, −tanh δ` the mean-zero weights are
`ρ₁ = sinh δ cosh γ/sinh(γ+δ)`, `ρ₂ = sinh γ cosh δ/sinh(γ+δ)`, and the two
mixed coefficients coincide:

```
ρ₁·tanh γ = ρ₂·tanh δ = k := sinh γ sinh δ / sinh(γ+δ) .
```

Hence, using `log(1 + tanh x tanh y) = L(x+y) − L(x) − L(y)`,

> **`hasDerivAt_Gval`**  `G′(σ)·cosh²σ = k·[L(σ+γ) − L(σ−δ) − L(γ) + L(δ)]
>                                       = k·[M_n(σ+v) − M_n(v)]`

— the odd-kernel form, exactly.  Everything else is bookkeeping:

* the slack `D(σ) = l₀ + l₁ tanh σ + l₂(σ tanh σ − L σ) − G(σ)` has
  `D′(σ) = [(l₁+l₂σ) − k(M_n(σ+v) − M_n(v))]/cosh²σ` (`hasDerivAt_Dsl`);
* the two **value** conditions `D(α) = D(−β) = 0` give `∫ D′ = 0` over
  `[−β, α]`, which after `w = σ+v` is an integral over the §7c⁗ window
  `[X−m, X+m]`, `X = u+v`;
* the two **tangency** conditions say the affine `l₁+l₂σ` matches `k·M_n` at the
  two window ends, i.e. it *is* the chord (a one-line `linear_combination`);
* therefore the integrand is `−k·(M_n − chord M_n)·sech²(w−v)`, so
  `R_S = 0` (`bitangent_residual_zero`), and with `skews_vanish`:

> **`bitangent_pair_symmetric`** — a doubly-interior bitangent pair has
> `u = v = 0`: **both sides are BSC**.

Numerically the residual and `R_S` differ exactly by the factor
`k = sinh γ sinh δ/sinh(γ+δ)`, which is what the proof reproduces.

**What `(B)` still needs** is only the `Chan`-level plumbing: `Bitangency`
(Lagrange multipliers for the one-sided LP) and rewriting `Conj12.lean`'s
maximiser hypotheses into the `θ`-coordinate form `Dsl`.  No analysis remains.

### 7e′. `(C)`: the bilinear structure, and the criterion in closed form

Two facts make the second-order test for `(C)` much smaller than feared.

**1. The value is bilinear.**  `I(U;V) = Σ_{u,v} π_u ρ_v f(s_u t_v)` is linear in
each side-law, and both feasible sets (`mass 1`, `mean 0`, `∫f_e ≤ C`) are
*linear* constraints on the law.  So

```
V(μ*+d_U, ν*+d_V) − V(μ*,ν*) = A_U + A_V + Q(d_U,d_V)
```

is an **exact identity** — no Taylor expansion of `V` is needed, only of the
one-sided terms.  (This also explains §7f⁷: the first-order loss vanishes not
because of any cancellation but because the atoms sit at critical points of the
Lagrangian atom function, so `⟨h, d⟩ = O(ε²)`.)

**2. Both one-sided objects have closed forms** in `θ` coordinates
(`TwoAtom.lean`, verified against the direct definitions):

```
Rtwo α β = [sinh β cosh α (α tanh α − Lα) + sinh α cosh β (β tanh β − Lβ)]/sinh(α+β)

Vtwo α β γ δ · sinh(α+β) sinh(γ+δ)
  = sinh β sinh δ cosh(α+γ)[L(α+γ)−Lα−Lγ] + sinh β sinh γ cosh(α−δ)[L(α−δ)−Lα−Lδ]
  + sinh α sinh δ cosh(β−γ)[L(β−γ)−Lβ−Lγ] + sinh α sinh γ cosh(β+δ)[L(β+δ)−Lβ−Lδ]
```

**3. The criterion is the reciprocal of the (iii) ratio.**  Measuring the
Hessian slope product `F_uv²/(F_uu F_vv)` numerically at the symmetric point and
comparing with `x²(g(x)/g(α)−1)(g(x)/g(β)−1)/(1−g(x))²` gives agreement to full
precision *as reciprocals* — e.g. `0.9376` vs `1.0665 = 1/0.9376` at
`σ = τ = 0.5`.  So the criterion is

> **`saddleRatio_gt_one`**  `1 < (1−g(x))²g(α)g(β) / [x²(g(x)−g(α))(g(x)−g(β))]`,

which is `saddle_iii` divided by a positive denominator — **already a theorem**.

**What `(C)` still needs.**  Only the identification of that ratio with the
constrained Hessian: second derivatives of `Vtwo` and `Rtwo` at `α=β=σ`,
`γ=δ=τ`, the bordered-Hessian determinant, and the standard
"indefinite ⟹ not a local max" step.  The last one does **not** need the
implicit function theorem: take the curve `x(t) = x* + t d + t² e` with `d`
tangent to the rate level set and `e` killing the second-order rate drift, then
a `−K t³` push along `∇R` makes the rate strictly feasible for small `t > 0`
while the `t²` value gain survives.

### 7e″. The Hessian identification — `(C)`'s computation, done

Bilinearity does the work.  Along the two rate-constant curves
`p ↦ μ(p)`, `q ↦ ν(q)`,

```
F_pp = ⟨φ_{ν₀}, μ″⟩ ,     F_qq = ⟨φ_{μ₀}, ν″⟩ ,     F_pq = (μ′⊗ν′)[f(xy)] ,
```

so **no mixed second derivative of the value is ever needed** — each entry is a
one-sided object.  At the symmetric point `μ₀ = ½(δ_s+δ_{−s})`,
`ν₀ = ½(δ_t+δ_{−t})`, `φ_{ν₀}(x) = f_e(xt)`.

*Diagonal.*  Bitangency (with `λ₁ = 0` by symmetry) makes
`H(x) = f_e(xt) − λ₀ − λ₂f_e(x)` vanish to second order at `±s`; since `μ″`
annihilates `1`, `id`, `f_e`, only the `H″` term survives:

```
F_pp = Σ_i w_i (x_i′)² H″(x_i) = H″(s) = t²/(1−x²) − λ₂/(1−s²),
λ₂ = t·artanh x/artanh s,      x = st .
```

*Mixed.*  The tangent direction is `w₁′ = −1/(2s)`, `w₂′ = +1/(2s)`,
`x₁′ = x₂′ = 1` — both atoms translate; the rate is automatically stationary
along it, which is why §7f⁷ saw a pure `ε²` effect.  Pairing against `f`:

```
A(y) = ⟨f(·y), μ′⟩ = y − artanh(sy)/s ,   F_pq = A′(t) − A(t)/t
     = artanh x/x − 1/(1−x²) .
```

*Collapse.*  Using `artanh y = y g(y)/(1−y²)`:

```
F_pq = −(1−g(x))/(1−x²) ,
F_pp = −t²(g(x)/g(s) − 1)/(1−x²) ,      F_qq = −s²(g(x)/g(t) − 1)/(1−x²) ,
```

so `F_pp, F_qq < 0` (as `g` is decreasing and `x < s,t`) and

```
F_pq² / (F_pp F_qq) = (1−g(x))² / [ x²(g(x)/g(s)−1)(g(x)/g(t)−1) ] ,
```

**exactly the reciprocal of the (iii) ratio**.  Hence
`hessian_indefinite : F_pp·F_qq < F_pq²` from `saddle_iii`, and
`saddle_direction` exhibits the ascent direction `(1, −F_pq/F_qq)`.  The Lean
formulas reproduce the numerically measured slope products to the precision of
the finite differences (`1.0665261` vs `1.0665260` at `σ=τ=0.5`).

What remains for `(C)` is no longer analysis: build the rate-constant curves as
`Chan`s, identify `F_pp`, `F_qq`, `F_pq` with their second derivatives, and run
the `x(t) = x* + t d + t² e − K t³ ∇R` feasibility argument.

### 7c⁸. `(B)`: the `Chan`-to-`θ` translation layer

`BitangencyBridge.lean`:

* `fe_tanh : f_e(tanh σ) = σ tanh σ − L(σ)`;
* `weights_of_mean_zero` — mean zero *forces* the two-atom weights to be
  `sinh δ cosh γ/sinh(γ+δ)`, `sinh γ cosh δ/sinh(γ+δ)`;
* `atomValue_eq_Gval` — so `Conj12.lean`'s `atomValue` is `Gval`;
* `Dsl_eq_slack` — so the `Chan`-level slack is `Dsl`.

and in `LogCosh.lean`, `tangency_of_contact`: a contact point of a nonnegative
slack is automatically a tangency point (`IsLocalMin.hasDerivAt_eq_zero`), so
the two derivative conditions of §7c⁗ come free from the domination half of
`Bitangency`.

`(B)` is therefore reduced to **`Bitangency` alone** — the Lagrange multipliers
for the one-sided linear program — plus the corner bookkeeping that turns
`¬VSideCorner` into `γ, δ > 0`.

### 7c⁹. `Bitangency`: what maximality actually gives, and the KKT step

A scope correction first.  `Chan` is a **binary** channel, so the `U`-side law
has at most **two atoms**.  Domination of the atom value by an affine-plus-`λf_e`
function *over all of* `[−1,1]` — the way `Bitangency` is stated in
`Conj12.lean` — is therefore neither what maximality over `Chan` supplies (it
would need three-atom competitors) nor what §7c⁗ consumes.  What §7c⁗ consumes
is the **four equations**, and those follow from stationarity alone.

`KKT.lean` supplies the three missing pieces, all elementary:

* **`le_zero_of_deriv_of_max`** (the calculus input).  Along a straight line on
  which `R` strictly decreases, feasibility holds automatically for small
  `t > 0`, so `V`'s directional derivative is `≤ 0`.  Proved through
  `hasDerivAt_iff_tendsto_slope` — **no implicit function theorem anywhere**,
  which is what blocked this step before.

* **`kkt_of_directional`** (pure linear algebra).  If `∇V·d ≤ 0` whenever
  `∇R·d < 0`, and `∇R ≠ 0`, then `∇V = λ∇R` with `λ ≥ 0`.  Proof: perturb the
  orthogonal direction `(−r_b, r_a)` by `∓ε∇R` to enter the open half-space,
  giving `|∇V·(−r_b, r_a)| ≤ ε ∇V·∇R` for every `ε > 0`.

* **`bitangency_of_stationary`** (the algebraic core).  Mass and mean *force*
  the weights `w₁ = −x₂/(x₁−x₂)`, `w₂ = x₁/(x₁−x₂)`, so for
  `η = φ − λψ` the two stationarity equations say precisely

  ```
  η′(x₁) = η′(x₂) = (η(x₁) − η(x₂))/(x₁ − x₂) ,
  ```

  i.e. an affine function matches `φ − λψ` in value *and* slope at both atoms —
  the four bitangency equations.  `cleared_of_grad` performs the denominator
  clearing, and `hasDerivAt_twoAtomL_fst` / `hasDerivAt_twoAtomR_snd` are the
  partial derivatives of `⟨φ, μ(x₁,x₂)⟩` that feed it.

**Both `(B)` and `(C)` now bottleneck on the same plumbing** and on nothing
else: realise the two-atom family `(x₁,x₂) ↦ Chan` and identify
`mutualInfo (jointUV 0 cL cR)` with `twoAtomL (atomValue cR)` and
`mutualInfo (jointUX cL)` with `twoAtomL f_e`.  Given that,

* `(B)`: maximality → `le_zero_of_deriv_of_max` → `kkt_of_directional` →
  `cleared_of_grad` → `bitangency_of_stationary` → `BitangencyBridge` →
  `bitangent_pair_symmetric` → `BothBSC`;
* `(C)`: the same family, plus `hessian_indefinite` and the
  `x(t) = x* + t d + t² e − K t³ ∇R` feasibility argument.

### 7c¹⁰. The two-atom channel family — the shared plumbing, done

`TwoAtomChan.lean`.  Both `(B)` and `(C)` were blocked on exactly this, and it
is now in place, axiom-clean.

**Weights are forced.**  At `p = 0` the marginal on `X` is uniform, so every
binary channel has mean-zero biases (`pi_bias_sum_zero`); with mass one this
determines the weights from the atoms (`weights_of_mass_mean`):

```
π_true = −s_false/(s_true − s_false),      π_false = s_true/(s_true − s_false).
```

**Rate and value are `twoAtomL`.**  Feeding that into the two closed forms
already in the development gives

```
mutualInfo_jointUX_eq_twoAtomL : I(U;X)  = twoAtomL f_e            s_false s_true
mutualInfo_jointUV_eq_twoAtomL : I(U;V)  = twoAtomL (atomValue cR) s_false s_true
```

the second by regrouping `Σ_{u,v} π_u ρ_v f(s_u t_v) = Σ_u π_u·atomValue(s_u)`.

**Atoms realise as channels.**  `chanOfAtoms` sends `a > 0 > b` in `(−1,1)` to
the channel with parameters `w(1+a), w(1−a)`, `w = −b/(a−b)`; membership in
`[0,1]` reduces to `a(1+b) ≥ 0` and `a(b−1) ≤ 0`.  Then

```
biasOf_chanOfAtoms : biases are exactly `a` and `b`
rate_chanOfAtoms   : I(U;X) = twoAtomL f_e b a
value_chanOfAtoms  : I(U;V) = twoAtomL (atomValue cR) b a
```

**Why this is the payoff.**  Along the atom family the rate and the value are
*literally* the one-variable functions whose derivatives are
`hasDerivAt_twoAtomL_fst` / `hasDerivAt_twoAtomR_snd` — no further
differentiability plumbing is needed.  `(B)` and `(C)` are now assembly:

* `(B)`: maximality → `le_zero_of_deriv_of_max` → `kkt_of_directional`
  → `cleared_of_grad` → `bitangency_of_stationary` → `BitangencyBridge`
  → `bitangent_pair_symmetric` → `BothBSC`;
* `(C)`: the same family plus `hessian_indefinite` and the
  `x(t) = x* + t d + t² e − K t³ ∇R` feasibility curve.

### 7c¹¹. `(B)`: the `U`-side is closed

`BFinish.lean`.  Everything below is axiom-clean.

* `hasDerivAt_twoAtomL_line` — the directional derivative of the two-atom
  functional along a straight line in `(a,b)`, equal to `D_fst·d₁ + D_snd·d₂`.
* `stationary_of_max` — feeding that to `le_zero_of_deriv_of_max` and
  `kkt_of_directional`: if no feasible straight-line move improves the value,
  the two gradients are proportional with `λ ≥ 0`.
* `hasDerivAt_atomValue`, `atomValue'` — the atom value is differentiable at
  every interior bias (the two `f`-arguments satisfy `1 + s t_v > 0` because
  `|s| < 1` and `|t_v| ≤ 1`).
* `Dfst_fe_pos` — **the rate gradient does not vanish**: strict convexity of
  `f_e` (one mean-value theorem plus strict monotonicity of `artanh`) gives
  `f_e(a) − f_e(b) − (a−b)artanh a < 0`, and `b < 0` flips it to `D_fst f_e > 0`.
* `stationary_of_maximiser` — **this is `Bitangency` in its correct form**,
  proved from `IsMaxPairC`.  For each direction, perturbed atoms stay admissible
  for small `t > 0` (`eventually_atoms`), `chanOfAtoms` realises them, its rate
  and value are `twoAtomL f_e` and `twoAtomL (atomValue cR)` (`TwoAtomChan.lean`),
  so feasibility follows from `rate ≤ rate₀ ≤ Cu` and maximality applies.
* `atomValue'_eq` — the derivative of the atom value in `θ` coordinates, by
  uniqueness of the derivative against `hasDerivAt_Gval`.
* `residual_zero_of_maximiser` — **the `U`-side conclusion**: at a maximiser
  with interior atoms `tanh α, −tanh β` and `V`-side atoms `tanh γ, −tanh δ`,

  ```
  R_S((α+β)/2, (γ+δ)/2, (α−β)/2, (γ−δ)/2) = 0 .
  ```

**What remains for `(B)`** is the `V`-side mirror of the last three items — the
same statements with `jointYV`/`marg₂`/`biasOfSnd` in place of
`jointUX`/`marg₁`/`biasOf` — giving `R_T = 0`; then `skews_vanish` yields
`u = v = 0`, and reading off `BothBSC` from equal-magnitude biases.  It is
mechanical duplication, not new mathematics.  (A side-generic formulation would
have avoided it; retrofitting one now costs the same as duplicating.)

### 7c¹². `(B)`: the `V`-side mirror, and `BothBSC`

`BFinishV.lean` mirrors `BFinish.lean` with `jointYV`/`marg₂`/`biasOfSnd`, the
positive `V`-atom sitting at index `false`:

* `atomValueV`, `hasDerivAt_atomValueV`, `atomValueV'`;
* `mutualInfo_jointYV_eq_twoAtomL`, `mutualInfo_jointUV_eq_twoAtomLV`;
* `chanOfAtomsV` — parameters `1 − w(1±c)`, i.e. the `U`-side construction
  reflected, with the same `[0,1]` bounds;
* `stationary_of_maximiserV`, `atomValueV_eq_Gval`, `atomValueV'_eq`,
  `residual_zero_of_maximiserV : R_T = 0`.

Combining the two residuals through `skews_vanish`:

> **`skews_vanish_of_maximiser`** — at a maximiser with interior atoms
> `tanh α, −tanh β` and `tanh γ, −tanh δ`, `α = β` and `γ = δ`.

and reading that off as channels: mean zero plus equal atom magnitudes force
balanced marginals, and a channel with `marg₁ true = 1/2` *is* a BSC
(`bsc_of_balanced`: `X + Y = 1` makes `chanTr X Y = bscTr X`), giving

> **`bothBSC_of_maximiser`** — `BothBSC cL cR`.

All axiom-clean.  `(B)`'s analysis and its `Chan`-level statement are complete;
what separates `bothBSC_of_maximiser` from the `InteriorIsBSC` `Prop` is only
the *degenerate* bookkeeping — turning `¬VSideCorner` plus positive marginals
into the interior parametrisation, and disposing of the null-value cases (both
biases zero, which `conjecture1_p0_of_two` already handles separately by
`zsValue_pos`).

### 7c¹³. Relabelling, and both `U`-orientations

The development fixes which `Bool` label carries the positive atom.  That is a
gauge choice, and `swapU` removes it on the `U` side: swapping the two `U`
letters leaves `marg₂`, `entropy1`, `entropy2` — hence both `I(U;X)` and
`I(U;V)` — invariant (`mutualInfo_jointUX_swapU`, `mutualInfo_jointUV_swapU`),
is involutive, and sends `bsc a` to `bsc (1−a)`, so `BothBSC` transfers back
(`bothBSC_of_swapU`).  Hence

> **`bothBSC_of_maximiser_any`** — `BothBSC` at a maximiser for *either*
> `U`-orientation of the atoms.

The same construction on the `V` side would remove the last gauge choice; it is
the identical 60 lines with `marg₁`/`marg₂` exchanged.

**Remaining between this and the `InteriorIsBSC` `Prop`** — no analysis, two
bookkeeping items:

1. *Corners.*  `¬VSideCorner` gives `|t_v| < 1`, but says nothing about the
   `U` side; a `U`-side corner would have to be excluded (or the disjunction
   `BothBSC ∨ VSideCorner ∨ USideCorner` carried, with the mirror of
   `cornerBound`).  Note this is not vacuous: the conjectured optimum, the Z/S
   pair, *is* a double corner — which is exactly why `¬VSideCorner` appears in
   the hypothesis.
2. *Degeneracy.*  Both biases vanishing on a side makes the channel useless
   (`I(U;X) = I(U;V) = 0`) and generally not a BSC; such a pair is a maximiser
   only when the optimal value is `0`, which `conjecture1_p0_of_two` already
   disposes of separately via `zsValue_pos`.

### 7c¹⁴. `(B)` in final form

`swapU` swaps the *second* index of `tr`, which is `U` in `jointUX` and `V` in
`jointYV` — so the same operation relabels either side.  With
`mutualInfo_jointYV_swapU`, `mutualInfo_jointUV_swapV` and `bothBSC_of_swapV`,
both gauge choices disappear:

> **`bothBSC_of_maximiser_free`** — `BothBSC` for *any* orientation of the atoms
> on either side.

`exists_theta_U` / `exists_theta_V` produce the `θ`-parametrisation from the
hypotheses: mean zero with positive marginals forces the two biases to have
opposite signs, and `|bias| < 1` lets `artanh` name them.  Hence

> **`bothBSC_of_interior`** — a maximiser whose atoms are interior
> (`|bias| < 1`) and non-degenerate (not both zero) on each side is a BSC pair,

and in the shape of the `InteriorIsBSC` `Prop`,

> **`interiorIsBSC_of_noCorner`** — `¬USideCorner`, `¬VSideCorner`, positive
> marginals, non-degeneracy `⟹ BothBSC`.

**That is `(B)`.**  The two hypotheses beyond `InteriorIsBSC`'s own are both
genuine and both belong to the assembly, not to `(B)`:

* `¬USideCorner` is *not* implied by `¬VSideCorner`, and excluding it is not
  vacuous — the conjectured optimum, the Z/S pair, is a **double** corner.  The
  assembly must either exclude a `U`-corner or carry
  `BothBSC ∨ VSideCorner ∨ USideCorner` with a mirror of `cornerBound`.
* Non-degeneracy (both biases zero on a side) makes the channel useless, value
  `0`; `conjecture1_p0_of_two` already disposes of that case via `zsValue_pos`.

### 7e. The branch comparison is not needed: at `p = 0` the BSC point is a **saddle**

A global maximum is a best response on each side, hence a fixed point.  By §7c‴
and §7c⁗ the fixed points are the symmetric (BSC) pair or configurations with an
atom at `±1`.  So Conjecture 1 follows if the BSC pair is *not* a local maximum
at `p = 0` — no transcendental branch comparison required.

It isn't.  Parametrising each side by its positive atom with the rate constraint
solved for the other atom, the Hessian at the symmetric point has
`det < 0` at every rate pair tested (`numerics/p0_saddle_hessian.py`):

| `(Cu,Cv)` bits | slope product `F_uv²/(F_uu F_vv)` at `p=0` | crossing of 1 | measured `θ` |
| --- | --- | --- | --- |
| (0.4,0.4) | 1.195 | 0.01–0.02 | 0.0152 |
| (0.4,0.6) | 1.273 | 0.01–0.02 | 0.0145 |
| (0.8,0.8) | 1.495 | 0.005–0.01 | 0.0071 |

In §5d's own notation this is `ΛΛ′ > 1`, the **exact converse** of the local
rigidity theorem.  There is no conflict: §5d assumes the value constraint
`R(s) + R(t) < R(x)`, which *fails* here — at `Cu = Cv = 0.4` bits it reads
`0.889 < 0.477`, false.  The rigidity theorem is about symmetric fixed points of
positive Lagrangian value; at `p = 0` the relevant multiplier makes that value
negative, and the contraction reverses.

**The last piece of Conjecture 1** is therefore the closed-form inequality, in
the `gFun` language already formalised in `Rigidity.lean`:

> `(iii)`  For `α, β ∈ (0,1)` and `x = αβ`, with `g(y) = (1−y²)·artanh y / y`,
>
> ```
> (1 − g(x))²  >  x² · (g(x)/g(α) − 1) · (g(x)/g(β) − 1)
> ```

`numerics/p0_lambda_product.py`: the left/right ratio is `> 1` on the whole grid,
minimum `1.000027`, maximum `2.05`, and it reproduces the numerically measured
Hessian slope product to four digits.  The inequality is **asymptotically tight**
as the rates vanish — expanding `g(y) = 1 − (2/3)y² − (2/15)y⁴ + …` gives
`ΛΛ′ = 1 + (4/15)ε² + O(ε⁴)` at `α = β = ε` — so any proof has to be sharp at
that end.  Note the already-formalised ingredients point the other way
(`one_sub_gFun_lt_sq` gives `1 − g(x) < x²`), so what is needed is an *upper*
bound on `κ_α κ_β`, not the lower bound `kappa_prod_gt_one` supplies.

**Bonus: an equation for Conjecture 3's threshold.**  Running the same criterion
at general `p` (`x = (1−2p)αβ`) and solving `ΛΛ′ = 1` predicts where the
symmetric branch loses local maximality (`numerics/theta_from_stability.py`):

| `(Cu,Cv)` | `θ` predicted ×1000 | `θ` measured ×1000 |
| --- | --- | --- |
| (0.4,0.6) | 14.50 | 14.5 |
| (0.6,0.6) | 13.28 | 13.3 |
| (0.4,0.4) | 15.31 | 15.2 |
| (0.8,0.8) | 7.39 | 7.1 |
| (0.05,0.05) | 4.13 | 9.1 |
| (0.1,0.9) | 7.37 | 11.1 |

Where the two agree the transition is a pitchfork — `θ` *is* the stability
boundary, and has an explicit equation.  Where `θ_pred < θ_meas` the symmetric
point is still a local max while already beaten by the corner branch, i.e. the
transition is subcritical there.  Either way `p < θ_pred ⟹ BSC is not optimal`,
which at `p = 0` is unconditional.


### 7e‴. `(C)` without an implicit function — the strategy, and its three pieces

The obstacle to `(C)` was always that the rate-constant curve is defined
implicitly, so its *second* derivative is out of reach.  Three observations
remove the need for it entirely.

**1. Bilinearity splits the comparison.**
`V(μ,ν) − V(μ*,ν*) = A_U + A_V + Q` exactly, `A_U`, `A_V` one-sided, `Q` the
bilinear cross term.

**2. Bitangency turns `A_U` into one-variable Taylor at *fixed* points.**  With
the slack `H(x) = φ(x) − λf_e(x) − ℓ₁x − ℓ₀`, mass one and mean zero give

> **`twoAtomL_decomp`**  `⟨φ,μ⟩ = ⟨H,μ⟩ + λ·R(μ) + ℓ₀`

so `A_U = ⟨H,μ′⟩ + λ(R(μ′) − Cu)`.  Because bitangency makes `H` and `H′` vanish
at both atoms, `⟨H,μ′⟩ = ½Σ w_u H″(x_u)δ_u² + o(δ²)` — Taylor for a *one-variable*
function at a *fixed* point.  The curve is never differentiated.

**3. Feasibility needs no implicit function either.**  Take the explicit
polynomial curve `x(ε) = x* + εd + ε²(e − ηg)`, `d` tangent (`∇R·d = 0`), `e`
killing the second-order rate drift, `∇R·g > 0`.  Then
`R(ε) − Cu = −η(∇R·g)ε² + o(ε²) < 0`: strictly feasible for small `ε > 0`, at
the cost of a value loss `λ(R−Cu) = O(ηε²)` which the *strict* margin of
`hessian_indefinite` absorbs once `η` is small.  Only `∇R ≠ 0` is needed:

> **`Dfst_fe_pos`**, **`Dsnd_fe_neg`** — the two components of `∇R`, strictly
> positive and strictly negative (strict convexity of `f_e`).  The second also
> gives strict monotonicity of the rate in the second atom.

Closing the argument then needs the elementary

> **`pos_of_second_deriv_pos`** — `g(0) = g′(0) = 0`, `g″(0) > 0` `⟹` `g > 0`
> just to the right of `0`.

**What remains for `(C)`.**  Assembling these: build the two curves as `Chan`s
(`chanOfAtoms`/`chanOfAtomsV` already do this), and identify the second-order
coefficient of the total gain — `½Σ w H″d² + ½Σ ρ H″d′² + Q₂` — with
`F_pp d₁² + 2F_pq d₁d₂ + F_qq d₂²`, which `hessian_indefinite` and
`saddle_direction` then make positive.  That identification is the one
substantial computation left; it is bounded, and it needs no measure theory and
no implicit functions.

### 7e⁴. The diagonal half of the identification

Along the rate-preserving direction **both atoms translate at unit speed**, so
the gap `x₁ − x₂ = 2s` is *constant* and the forced weights are **affine** in the
parameter:

```
x₁(ε) = s + εd ,  x₂(ε) = −s + εd ,   w₁(ε) = (s−εd)/(2s) ,  w₂(ε) = (s+εd)/(2s) .
```

Pairing the slack `H` against that law gives `slackPath`, and

> **`slackPath_second_deriv`** — with `H` and `H′` vanishing at both atoms,
> `slackPath` vanishes to second order and
> `slackPath″(0) = d²·(H″(s) + H″(−s))/2`.

That is the whole diagonal computation: a *one-variable* Taylor expansion at
*fixed* points, with no differentiation of any curve.

At the symmetric point `H(x) = f_e(xt) − λf_e(x) − ℓ₀`, `λ = t·artanh(st)/artanh s`,
so `H″(x) = t²/(1−x²t²) − λ/(1−x²)` is **even** (`slackHess_even`) and

> **`slackHess_eq_Fpp`**, **`slackHess_eq_Fqq`** — its value at the atoms is
> exactly `F_pp` (resp. `F_qq`),

whence

> **`slackPath_second_deriv_Fpp`** — the `U`-side second-order coefficient is
> `d²·F_pp`, i.e. `A_U = ½F_pp d²ε² + λ(R−Cu) + o(ε²)`.

**What is left of the identification** is the off-diagonal half: the bilinear
cross term.  Writing `P(ε₁,ε₂) = B(μ(ε₁), ν(ε₂))` for the bilinear value, the
cross term is `Q(ε) = P(ε,ε) − P(ε,0) − P(0,ε) + P(0,0)`, so
`Q″(0) = 2·∂²P/∂ε₁∂ε₂(0,0) = 2 d₁d₂·F_pq` — three one-variable second
derivatives of an explicit four-term function.  With it, the total second-order
coefficient is `½[F_pp d₁² + 2F_pq d₁d₂ + F_qq d₂²]`, positive by
`saddle_direction`.

### 7e⁵. The cross term, and the assembly

**Cross term.**  `Q(ε) = ⟨Δφ_ε, δμ(ε)⟩` pairs two objects that *both* vanish at
`ε = 0`, so it vanishes to second order with `Q″(0)` equal to twice the product
of the two first-order data.  Splitting the pairing as

```
Q = (a₁−½)·Δφ_ε(x₁(ε)) + (a₂−½)·Δφ_ε(x₂(ε))
      + ½(Δφ_ε(x₁(ε)) − Δφ_ε(s)) + ½(Δφ_ε(x₂(ε)) − Δφ_ε(−s))
```

makes the first two summands literal products of vanishing functions, which

> **`second_deriv_of_mul_vanishing`** — `G(0) = K(0) = 0` `⟹` `(GK)″(0) =
> 2G′(0)K′(0)`

handles.  The last two are differences in the *evaluation point*; they vanish to
second order for the same reason (`Δφ_0 ≡ 0` kills the `x`-derivative), but
their coefficients are genuinely mixed second derivatives — the one part of the
identification still to be written out.  Its value is
`2 d₁d₂·F_pq`, so the total second-order coefficient is
`½[F_pp d₁² + 2F_pq d₁d₂ + F_qq d₂²]`.

**Assembly.**  The argument closes in the shape

> **`not_max_of_second_order`** — if the feasibility margin has strictly
> *negative* second derivative (so the family is strictly feasible just to the
> right of `0`) while the value gain has strictly *positive* one, maximality
> fails.

with the positivity supplied by

> **`hessian_form_pos`** — the quadratic form is positive in the saddle
> direction `(1, −F_pq/F_qq)`, which is `saddle_direction`, i.e. `saddle_iii`.

`neg_of_second_deriv_neg` is the feasibility half; the `−η∇R` term of the curve
supplies its strict negativity.

So `(C)` is now: instantiate `gain` and `feas` with the value and rate along the
explicit polynomial curve, and supply four second-order facts — the two diagonal
ones (`slackPath_second_deriv_Fpp` and its mirror) done, the cross term reduced
as above, and `feas″(0) = −2η(∇R·g) < 0` from the curve's own definition.

### 7e⁶. The mixed partials, uniformly

Every summand of the cross term has the **same** shape.  The weights
`aᵢ(ε)bⱼ(ε)` are a product of two affine functions, hence quadratic; the atom
product `xᵢ(ε)yⱼ(ε)` is a product of two affine functions, hence quadratic too.
So each of the sixteen terms is

```
(c₀ + c₁ε + c₂ε²) · f(g₀ + g₁ε + g₂ε²)
```

and **one** lemma differentiates all of them:

> **`hasDerivAt_polyMul`** — the first derivative, `polyMulComp`;
> **`polyMul_second`** — the second derivative at `0`,
> ```
> 2c₂·f(g₀) + 2c₁·f′(g₀)g₁ + c₀·(f″(g₀)g₁² + 2g₂·f′(g₀)) .
> ```

The `c₀ f″(g₀) g₁²` part is the genuinely mixed contribution — the `∂²/∂ε₁∂ε₂`
that the `Δφ` split could not reach.  With `f(z) = (1+z)log(1+z)`,
`f′ = log(1+z)+1`, `f″ = 1/(1+z)`, all sixteen coefficients are explicit at the
four base points `±s·±t`.

**What is left of `(C)`** is now purely instantiation: apply `polyMul_second`
sixteen times with the constants read off from
`aᵢ(ε) = (s∓εd₁)/(2s)`, `bⱼ(ε) = (t∓εd₂)/(2t)`, `xᵢ(ε) = ±s+εd₁`,
`yⱼ(ε) = ±t+εd₂`, sum, and check the total against `2d₁d₂·F_pq` — an identity in
`s`, `t`, `artanh(st)` after `log(1 ± st) → artanh` substitution.  Then feed
`not_max_of_second_order` with `hessian_form_pos`.

### 7e⁷. The instantiation, done

Along the **linear** curve `xᵢ(ε) = ±s + εd₁`, `yⱼ(ε) = ±t + εd₂` with the forced
weights, `polyMul_second` applied four times to the value and twice to each rate
gives, with `x = st`, `P = sd₂+td₁`, `M = td₁−sd₂`:

> **`value_second_coeff`**
> ```
> (d₁d₂/x)(f(x) − f(−x)) − (P²/x)f′(x) + (M²/x)f′(−x)
>     + ½(f″(x)P² + f″(−x)M²) + d₁d₂(f′(x) + f′(−x))
>   = 2d₁d₂·F_pq + (t²d₁² + s²d₂²)·[1/(1−x²) − 2·artanh x/x]
> ```
> **`rate_second_coeff`** — `R_U″(0) = d₁²·[1/(1−s²) − 2·artanh s/s]`.

In the value sum the `log(1−x²)` contributions cancel identically, leaving only
`artanh x` — which is why the answer is expressible through `F_pq` at all.

The ε²-correction of the curve contributes `2∇V·e = 2λ∇R·e`, since `∇V = λ∇R`
at a critical point, so the total second-order coefficient is
`V″ − λ_U R_U″ − λ_V R_V″`, and

> **`total_second_order_eq`** — that equals
> `F_pp d₁² + 2F_pq d₁d₂ + F_qq d₂²`.

The `d₁²` coefficients match because `λ_U·artanh(s)/s = t²·artanh(x)/x`, which is
exactly `λ_U = t·artanh x/artanh s` with `x = st`.  **The identification is
complete**: with `hessian_form_pos` the form is positive in the saddle
direction, and `not_max_of_second_order` closes the argument.

What is left of `(C)` is the last mile of plumbing: exhibit the corrected curve
as a family of `Chan`s (`chanOfAtoms`/`chanOfAtomsV`), check that the pieces
above are the second derivatives of *those* value and rate functions, and apply
`not_max_of_second_order`.

### 7e⁸. The plumbing: a correction to the plan

Writing the last mile turned up a fact the plan had assumed away.  The rate's
second derivative along the **pure translation** is

```
R_U″(0) = d₁²·[ 1/(1−s²) − 2·artanh s / s ]
```

and that bracket **changes sign**, at bias `s ≈ 0.79639` (`α ≈ 0.10181`):

| `s` | 0.1 | 0.5 | 0.7 | 0.8 | 0.9 |
| --- | --- | --- | --- | --- | --- |
| bracket | −0.997 | −0.864 | −0.517 | **+0.031** | +1.992 |

Below the crossover the translation *decreases* the rate, so it is strictly
feasible — but that is **not** enough, and an earlier reading of this table that
said the correction could be skipped there is wrong: with `R″ < 0` the gain's
second derivative is `V″ = form + λ_U R_U″ + λ_V R_V″ < form`, of indeterminate
sign, because wasting rate budget costs value.  Above the crossover the
translation increases the rate and is outright infeasible.  So the `ε²`-correction
is required in **both** regimes — and a correction with `e₁ ≠ e₂` destroys the two features
that made `polyMul_second` applicable: the gap `x₁−x₂` is no longer constant
(so the forced weights become a *ratio* of quadratics) and the atom products
become quartic.  A common shift `e₁ = e₂` is useless, because `(1,1)` is exactly
the tangent direction and so changes the rate not at all.

Hence

> **`genMul_second`** — the same second-derivative computation for
> `c(ε)·f(g(ε))` with **no shape assumption** on `c` or `g`:
> ```
> T″(0) = c″(0)f(g₀) + 2c′(0)f′(g₀)g′(0) + c(0)(f″(g₀)g′(0)² + f′(g₀)g″(0)) ,
> ```
> together with `hasDerivAt_genMul` for the first derivative.

This subsumes `polyMul_second` and covers the corrected curve.  The `η`-corrected
curve works uniformly in both regimes:

```
gain″ = form − 2λη(∇R·g) > 0  for small η ,      R − Cu = −η(∇R·g)ε² + o(ε²) < 0 .
```

Its forced weight `w₁ = −x₂/(x₁−x₂)` is a genuine quotient once `e₁ ≠ e₂`, with
Taylor data supplied by

> **`quot_second`** — `(N/D)″(0)` via the derivative function `(N′D−ND′)/D²`;
> **`weight_taylor`** — `w₁(0) = ½`, `w₁′(0) = −d₁/(2s)`,
> `w₁″(0) = −(e₁+e₂)/(2s)`.

The remaining work: instantiate `genMul_second` with those weights and the
quartic atom products, and feed `not_max_of_second_order`.

### 7e⁹. The corrected curve's rate

Instantiating `genMul_second` twice with `c = wᵢ` (Taylor data from
`weight_taylor`), `g = xᵢ`, `f = f_e`:

> **`rate_corrected_coeff`**
> ```
> R_U″(0) = d²·[1/(1−s²) − 2·artanh s/s] + artanh(s)·(e₁ − e₂) .
> ```

The `f_e(±s)` terms cancel because mass preservation forces `w₁″ = −w₂″` and `f_e`
is even (`fe_even`); `artanh` is odd (`artanh_odd`).  Since

> **`rate_grad_symmetric`** — `∇R = (artanh s/2, −artanh s/2)` at the symmetric
> point,

this reads `R_U″(0) = R″_lin + 2(∇R·e)`.  **That is exactly what the correction
buys**: `e₁ − e₂` moves the second-order rate drift by an arbitrary amount
(`exists_correction`, using `artanh s > 0`), so it can be driven to
`−2η(∇R·g) < 0` — strict feasibility — in *either* regime of §7e⁸, at a value
cost `2λ·(∇R·e)` that the strict margin of `hessian_form_pos` absorbs.

Remaining: the same instantiation for the *value* (four terms, quartic
arguments), whose correction contributes `2λ(∇R·e)` because `∇V = λ∇R`; then
`not_max_of_second_order`.

### 7e¹⁰. The corrected curve's value, and the choice of corrections

In `V″(0) = Σᵢⱼ [(wᵢρⱼ)″f(gᵢⱼ⁰) + 2(wᵢρⱼ)′f′(gᵢⱼ⁰)gᵢⱼ′ + (wᵢρⱼ)(f″gᵢⱼ′² + f′gᵢⱼ″)]`
the correction data enters twice, and the first place **cancels**: mass
preservation gives `w₁″ = −w₂″` and `ρ₁″ = −ρ₂″`, so the `f(gᵢⱼ⁰)` terms sum to
zero (`value_weightcorr_cancel`).  What survives telescopes:

> **`value_correction_coeff`**
> ```
> ½·Σᵢⱼ f′(gᵢⱼ⁰)(eᵢyⱼ⁰ + fⱼxᵢ⁰) = ½(f′(x) − f′(−x))·[t(e₁−e₂) + s(f₁−f₂)]
>                                = artanh(x)·[t(e₁−e₂) + s(f₁−f₂)] .
> ```

That is exactly `2λ_U(∇R_U·e) + 2λ_V(∇R_V·f)`, because `λ_U·artanh s = t·artanh x`
and `λ_V·artanh t = s·artanh x`.  So, writing `A = artanh(s)(e₁−e₂)`,
`B = artanh(t)(f₁−f₂)` — free by `exists_correction` —

```
V″(0)   = V″_lin + λ_U·A + λ_V·B ,
R_U″(0) = R″_lin,U + A ,          R_V″(0) = R″_lin,V + B .
```

Both verified numerically against the actual curve to full precision.  Finally

> **`exists_good_corrections`** — with `Vlin − λ_U Rlin,U − λ_V Rlin,V = form > 0`
> (which is `total_second_order_eq` plus `hessian_form_pos`) and `λ ≥ 0`, there
> are `A, B` making **both** rate drifts strictly negative and the value gain
> strictly positive: take `A = −Rlin,U − η`, `B = −Rlin,V − η` with
> `η = form/(2(λ_U+λ_V+1))`, giving `gain″ = form − (λ_U+λ_V)η ≥ form/2 > 0`.

**The second-order analysis of `(C)` is complete.**  What remains is only to run
these functions through the `Chan` layer: realise `ε ↦ (chanOfAtoms, chanOfAtomsV)`
for the corrected atoms, use `rate_chanOfAtoms`/`value_chanOfAtoms` to identify
`mutualInfo` with the `twoAtomL` expressions, note the derivatives just computed
are theirs, and apply `not_max_of_second_order`.

### 7e¹¹. The `Chan` layer, wired

The second-order machinery speaks about explicit functions of four atom
parameters; these lemmas say the `Chan`-level quantities *are* those functions.

> **`atomValue_chanOfAtomsV`** — the atom value of an atom-built `V`-side channel
> is `(−d/(c−d))f(zc) + (c/(c−d))f(zd)`;
>
> **`value_pair_atoms`** — the value of a *pair* of atom-built channels is the
> explicit four-term function
> ```
> (−b/(a−b))[(−d/(c−d))f(ac) + (c/(c−d))f(ad)]
>   + (a/(a−b))[(−d/(c−d))f(bc) + (c/(c−d))f(bd)] ;
> ```
> **`rate_pair_atoms`**, **`rateV_pair_atoms`** — the rates are
> `(−b/(a−b))f_e(a) + (a/(a−b))f_e(b)` and its mirror.

and finally

> **`curve_max_bound`** — if both atom-built rates are within budget, the
> atom-built value cannot beat the maximiser's.

That is precisely the `hmax` hypothesis of `not_max_of_second_order`, with
`gain = value − V*` and `feas = rate − C`.  **The `Chan` layer is closed**: the
whole of `(C)` is now a statement about the explicit atom functions, for which
every second-order fact is proved (§7e⁴–§7e¹⁰).

What is not yet written is the last mechanical link: packaging the explicit atom
functions *composed with the curve* as `gain`/`feas` and exhibiting their
`HasDerivAt` chains — the coefficients are `rate_corrected_coeff`,
`value_second_coeff` and `value_correction_coeff`, the engines are
`hasDerivAt_genMul`/`genMul_second`, and the conclusion is
`exists_good_corrections` fed to `not_max_of_second_order`.

### 7e¹². The chains: localisation, and the curve's bottom layer

Two things were needed before the `HasDerivAt` chains could be assembled.

**Localisation.**  `f_e` and `f` are differentiable only where their arguments are
in range, so the global hypothesis `∀ x, HasDerivAt g (g′ x) x` in
`pos_of_second_deriv_pos` / `neg_of_second_deriv_neg` /
`not_max_of_second_order` was unusable.  All three now take
`∀ᶠ x in 𝓝 0, HasDerivAt g (g′ x) x`; the proof extracts a radius and runs the
monotonicity argument on `[0, ε]` with `ε` below both it and the
positivity radius.

**The curve's bottom layer.**

```
atomC p d e ε = p + dε + eε²        atomC' d e ε = d + 2eε
wC  s d e₁ e₂ = −atomC(−s)/(atomC s − atomC(−s))        (the forced weight)
```

with `hasDerivAt_atomC`, `hasDerivAt_atomC'`, `hasDerivAt_wC` (quotient rule,
conditional on the gap being nonzero), `gap_ne_zero_eventually` (the gap is
`2s + ε²(e₁−e₂)`, so nonzero near `0` by continuity), and

> **`hasDerivAt_wC'`** — the weight's second derivative at `0` is
> `−(e₁+e₂)/(2s)`, via `quot_second`,

matching `weight_taylor`.  Note `atomC` is written `p + dε + eε²` precisely so
that it is *syntactically* the shape `hasDerivAt_quad` produces — the derivative
lemma is then literally that lemma, with no massaging.

What remains is the mechanical composition: feed `wC`, `atomC` into
`hasDerivAt_genMul`/`genMul_second` for the two rate terms and the four value
terms, sum, identify the coefficients with `rate_corrected_coeff`,
`value_second_coeff` + `value_correction_coeff`, and apply
`not_max_of_second_order` with `curve_max_bound` and `exists_good_corrections`.

### 7e¹³. The rate chain, composed

```
R_U(ε) = w(ε)·f_e(xₐ(ε)) + (1−w(ε))·f_e(x_b(ε))
```

with `w = wC`, `xₐ = atomC s d e₁`, `x_b = atomC (−s) d e₂`.  Two applications of
`hasDerivAt_genMul` give

> **`hasDerivAt_rateCurve`** — `HasDerivAt (rateCurve …) (rateCurve' … ε) ε`
> for all `ε` near `0`,

the side conditions being `gap_ne_zero_eventually` and `atom_mem_eventually`
(the atoms stay in `(−1,1)`, so `f_e` is differentiable there).  Two applications
of `genMul_second`, with `w(0) = ½` and `w′(0) = −d/(2s)` (`wC_zero`,
`wC'_zero`) and `w″(0) = −(e₁+e₂)/(2s)` (`hasDerivAt_wC'`), give

> **`hasDerivAt_rateCurve'`** —
> ```
> R_U″(0) = d²·[1/(1−s²) − 2·artanh s/s] + artanh(s)·(e₁ − e₂) ,
> ```

the coefficient identified by `rate_corrected_coeff`.  This is the first chain
assembled end to end: from the `Chan`-level rate, through the explicit atom
functions, to a second derivative in closed form — with the correction `e₁ − e₂`
sitting exactly where it is needed.

The value chain is the same construction with four terms and product weights
`w·ρ`; its coefficients are `value_second_coeff` and `value_correction_coeff`.

### 7e¹⁴. The value chain, per term

Each value term is `c·f(g)` with `c = wᵢρⱼ` and `g = xᵢyⱼ` both *products*, so
the data fed to `genMul_second` comes from product rules:

> **`hasDerivAt_mul2`**, **`hasDerivAt_mul2'`** — the product rule for the first
> derivative and for the second at `0`, `(AB)″(0) = A₂B + 2A′B′ + AB₂`.

Specialising the engine to `f(z) = (1+z)log(1+z)`:

> **`hasDerivAt_valTerm`** — `HasDerivAt (valTerm c g) (valTerm' c c′ g g′ ε) ε`;
> **`hasDerivAt_valTerm'`** —
> ```
> term″(0) = c₂·f(g₀) + 2c′(0)·(log(1+g₀)+1)g′(0)
>            + c(0)·[ g′(0)²/(1+g₀) + (log(1+g₀)+1)·g₂ ] ,
> ```

the `f″ = 1/(1+z)` derivative being discharged inline.  For the term `(i,j)`,

```
c(0) = ¼ ,  c′(0) = ½(wᵢ′ + ρⱼ′) ,  c₂ = wᵢ″ρⱼ + 2wᵢ′ρⱼ′ + wᵢρⱼ″ ,
g(0) = xᵢ⁰yⱼ⁰ , g′(0) = d₁yⱼ⁰ + xᵢ⁰d₂ , g₂ = 2eᵢyⱼ⁰ + 2d₁d₂ + 2xᵢ⁰fⱼ ,
```

the last supplied by **`hasDerivAt_atomProd'`**, and the weight data by
`hasDerivAt_wC` / `hasDerivAt_wC'`.

What remains is the four-term sum: add the `hasDerivAt_valTerm` facts for the
first derivative, add the four `hasDerivAt_valTerm'` coefficients, and match the
total against `value_second_coeff` + `value_correction_coeff` — a `ring`
identity over the atoms `f(±x)`, `f′(±x)`, `f″(±x)`.  Then
`not_max_of_second_order` with `curve_max_bound` and `exists_good_corrections`.

### 7e¹⁵. The four-term sum

With the per-term data of §7e¹⁴ — `c(0) = ¼`, `c′(0) = ½(wᵢ′+ρⱼ′)`,
`c₂ = wᵢ″ρⱼ + 2wᵢ′ρⱼ′ + wᵢρⱼ″`, `g(0) = ±st`, `g′(0) = ±P` or `∓M`,
`g₂ = 2eᵢyⱼ⁰ + 2d₁d₂ + 2xᵢ⁰fⱼ` — the four `hasDerivAt_valTerm'` coefficients add
to a closed form:

> **`value_four_term_sum`**
> ```
> Σᵢⱼ [c₂f(g₀) + 2c′(0)f′(g₀)g′(0) + c(0)(f″(g₀)g′(0)² + f′(g₀)g₂)]
>   = 2d₁d₂·F_pq + (t²d₁² + s²d₂²)[1/(1−x²) − 2·artanh x/x]
>     + artanh(x)·[t(e₁−e₂) + s(f₁−f₂)] ,
> ```

i.e. exactly `value_second_coeff` plus `value_correction_coeff`.  The `e`/`f`
data cancels out of the `f(g₀)` terms — `c₂(1,1) + c₂(2,2) = d₁d₂/(st)` and
`c₂(1,2) + c₂(2,1) = −d₁d₂/(st)`, the `E = e₁+e₂` and `F = f₁+f₂` parts
cancelling pairwise — which is why the correction survives only through
`e₁−e₂` and `f₁−f₂`.

Validated numerically: the coefficient sum with this data reproduces the actual
`V″(0)` of the corrected curve to full precision, at two parameter points with
all four corrections nonzero.

`hasDerivAt_sum4` / `hasDerivAt_sum4'` add the four terms.  What remains is
bookkeeping: name the four `c`'s and `g`'s as functions, apply
`hasDerivAt_valTerm` / `hasDerivAt_valTerm'` to each, and conclude with
`not_max_of_second_order`, `curve_max_bound`, `exists_good_corrections`.

### 7e¹⁶. The value curve, assembled

`valueCurve` is the four-term sum with `c = wᵢρⱼ` and `g = xᵢyⱼ` written out, and
`valueCurve'` its derivative, the four `valTerm'`s with the product-rule
derivative functions.

> **`hasDerivAt_valueCurve`** — `HasDerivAt (valueCurve …) (valueCurve' … ε) ε`
> for all `ε` near `0`.

The side conditions are `gap_ne_zero_eventually` on each side and
`one_add_prod_pos_eventually` for each of the four atom products (`f` is
differentiable where `1 + xᵢyⱼ > 0`, and `xᵢyⱼ → ±st ∈ (−1,1)`).

One Lean wrinkle worth recording: `hasDerivAt_mul2`'s derivative arguments are
higher-order metavariables, so for the terms built from `1 − w` the primed
functions must be supplied explicitly — `(A' := fun e => -(wC' …  e))` — or
unification picks the wrong shape.

With `hasDerivAt_sum4'` and the four `hasDerivAt_valTerm'` coefficients,
`value_four_term_sum` then gives `V″(0)` in closed form.  Everything for `(C)`
is in place; what is left is to state the final theorem and chain the pieces:
`gain = valueCurve − V*`, `feas = rateCurve − C` on each side,
`exists_good_corrections` to pick `e₁−e₂` and `f₁−f₂`, `curve_max_bound` for the
maximality hypothesis, and `not_max_of_second_order` for the contradiction.

### 7e¹⁷. The final chaining

> **`not_max_of_second_order2`** — the two-constraint version: `gain″(0) > 0`
> with both `fU″(0) < 0` and `fV″(0) < 0`, against
> `∀ε, fU ε ≤ 0 → fV ε ≤ 0 → gain ε ≤ 0`, is contradictory.

and the base-point facts, all pure algebra once the weights are `½`:

> **`rateCurve_zero`** — `R_U(0) = f_e(s)`, the BSC rate;
> **`valueCurve_zero`** — `V(0) = ½(f(st) + f(−st)) = f_e(st)`, the BSC value;
> **`rateCurve'_zero`** — `R_U′(0) = 0`;
> **`valueCurve'_zero`** — `V′(0) = 0`.

The last two are the *stationarity* of the symmetric point, and they fall out
term by term: in the rate the two `f_e` contributions cancel against each other
(`fe_even`) and the two `artanh` contributions cancel (`artanh_odd`); in the
value the `c′(0)` coefficients cancel in pairs across `(1,1)/(2,2)` and
`(1,2)/(2,1)`, and the `g′(0)` terms cancel as `P − P` and `M − M`.

So no first-order term survives, in either the value or the rates, and the
comparison is genuinely second order — which is the whole content of `(C)`.

**Still to write**: `hasDerivAt_valueCurve'` (the four `hasDerivAt_valTerm'`
applications summed by `hasDerivAt_sum4'` and matched to `value_four_term_sum`,
the exact analogue of `hasDerivAt_rateCurve'`), the identification of
`rateCurve`/`valueCurve` with the `pair_atoms` expressions so `curve_max_bound`
applies, and the final theorem chaining these through
`not_max_of_second_order2`.

### 7e¹⁸. The three items, and the contradiction chained

**`rateCurve_eq` / `valueCurve_eq`** identify the curve functions with the
`pair_atoms` expressions (the content is `1 − (−b/(a−b)) = a/(a−b)`), so
`curve_max_bound` applies to them.

**`hasDerivAt_valueCurve'`** — the four `hasDerivAt_valTerm'` applications, summed
by `hasDerivAt_sum4'` and matched to `value_four_term_sum`:

```
V″(0) = 2d₁d₂·F_pq + (t²d₁² + s²d₂²)[1/(1−x²) − 2·artanh x/x]
        + artanh(x)·[t(e₁−e₂) + s(f₁−f₂)] .
```

The weight second derivatives enter through `hasDerivAt_mul2'` with
`hasDerivAt_wC'` (and its negation for the `1 − w` factors), the atom-product
ones through `hasDerivAt_atomProd'`.

**`curve_contradiction`** — the chain.  With `gain ε = V(ε) − V*` and
`feas ε = R(ε) − R(0)` on each side, both vanish at `0` with vanishing first
derivative (`valueCurve_zero`, `valueCurve'_zero`, `rateCurve'_zero`), their
second derivatives are the closed forms above, and `not_max_of_second_order2`
(whose maximality hypothesis is now `∀ᶠ ε in 𝓝[>]0`, matching what
`curve_max_bound` supplies near `0`) delivers `False` as soon as the three
second-order signs hold.

Using `feas = R(ε) − R(0)` rather than `R(ε) − C` is deliberate: it makes
`feas 0 = 0` automatic without assuming the rate constraint is active, and
`R(ε) ≤ R(0) ≤ C` still gives feasibility.

**What is left for `BSCNotMax`**: pick `d = (1, −F_pq/F_qq)` so that
`hessian_form_pos` gives the form positive, use `exists_good_corrections` and
`exists_correction` to produce `e₁,e₂,f₁,f₂` meeting the three sign conditions,
and discharge `hmax` from `curve_max_bound` through `rateCurve_eq` /
`valueCurve_eq`.

### 7e¹⁹. `(C)`: the symmetric pair is not a maximiser

> **`exists_curve_corrections`** — with the Hessian form positive there are
> `e₁,e₂,f₁,f₂` making both rate drifts strictly negative and the value gain
> strictly positive.  `exists_good_corrections` supplies `A = artanh(s)(e₁−e₂)`
> and `B = artanh(t)(f₁−f₂)`; `exists_correction` realises them; the
> multiplier identity `artanh(x)·t·(e₁−e₂) = λ_U·A` converts the gain condition.
>
> **`hmax_discharge`** — near `ε = 0` the curve is a pair of genuine channels
> (`atom_pos_eventually`, `atom_neg_eventually`), so `curve_max_bound` applies
> through `rateCurve_eq` and `valueCurve_eq`.
>
> **`symmetric_not_max`** — chaining these with `curve_contradiction` at the
> saddle direction `d = (1, −F_pq/F_qq)`:
>
> ```
> a maximiser whose bias magnitudes are s, t ∈ (0,1) and whose value is the
> BSC value ½(f(st) + f(−st))  ⟹  False .
> ```

**That is `(C)` at the level of biases** — the entire saddle argument, from
`saddle_iii` through the Hessian identification, the corrected curve, and both
`HasDerivAt` chains, to a contradiction with maximality.  Axiom-clean apart from
the `native_decide` axiom that `saddle_iii` carries.

What separates this from the `BSCNotMax` `Prop` is only the reduction of
`BothBSC` to the bias data: extract `s = |1−2α|`, `t = |1−2β|` from the two
`bsc` channels, check the rate and value formulas, and dispose of the degenerate
`s = 0` or `t = 0` cases (where the value is `0`, handled by `zsValue_pos`).

### 7e²⁰. **`(C)` is a theorem**

`bscNotMax_holds : BSCNotMax`.  The reduction of `BothBSC` to bias data:

* `biasOf_bsc` / `biasOfSnd_bsc` — a BSC's biases are `±(1−2α)`, its marginals
  `½`;
* `fe_eq_half_fFun` — `f_e(z) = ½(f(z) + f(−z))`, so the BSC pair's value
  `f_e((1−2α)(1−2β))` is exactly the `symmetric_not_max` hypothesis;
* `fe_abs` handles the sign: the bias *magnitudes* `s = |1−2α|`, `t = |1−2β|`
  satisfy `f_e(st) = f_e((1−2α)(1−2β))` because `f_e` is even;
* two degenerate branches — `s = 0` (or `t = 0`) makes the value `f_e(0) = 0`,
  beaten by the Z/S pair (`zsValue_pos`); `|1−2α| = 1` makes the rate
  `f_e(1) = log 2`, above the budget by `zsRate_lt_log_two`, so infeasible;
* the interior case is `symmetric_not_max`.

Axioms: `propext, Classical.choice, Quot.sound` and the one `native_decide`
axiom inherited from `saddle_iii`, for the Pólya expansion.  (The regime-2 sweep
was moved to the kernel afterwards, `decide +kernel` in `CoreSweep.lean`, and
adds no axiom.)  Nothing else.

**So `(A)`, `(B)`, `(C)` and `(D)` are all theorems.**  `(B)` is
`interiorIsBSC_of_noCorner`, which carries the two extra hypotheses discussed in
§7c¹⁴ — `¬USideCorner` and non-degeneracy — that belong to the assembly rather
than to `(B)` itself.  Closing Conjecture 1 at `p = 0` now needs only that
assembly step: `conjecture1_p0_of_two` consumes `MaxIsBSCorCorner` and
`BSCNotMax`, and the second is now supplied.

### 7e²¹. The assembly: Conjecture 1 at `p = 0`, modulo one case

> **`conjecture1_p0_of_Ucorner`** — given only that a maximiser with a `U`-side
> corner and *no* `V`-side corner satisfies the bound, `Conjecture1_p0` holds.

Everything else is discharged inside:

* degenerate marginals on either side — value `0`, below `zsValue_pos`;
* a `V`-side corner — `cornerBound`, i.e. `(D)`;
* a vanishing bias on either side — `value_zero_of_bias_zero` (with
  `bias_all_zero`: mean zero makes one zero bias force the other), again value
  `0`;
* the interior non-degenerate case — `interiorIsBSC_of_noCorner` gives
  `BothBSC`, which `bscNotMax_holds` refutes.

**Why the remaining case is genuinely separate.**  The value is symmetric under
swapping the two sides (`jointUV 0 cL cR` transposes to `jointUV 0 cR cL`, and
`mutualInfo` is transpose-invariant), so a `U`-corner *looks* like a `V`-corner
after the swap.  But the **rates are not symmetric**: `cornerBound` needs
`I(U;X) ≤ zsRate a` and `I(Y;V) ≤ zsRate d`, and after swapping one would need
`cR`'s rate against `zsRate a`, which is not what feasibility supplies.  So the
case needs the mirror of `(D)` — a certificate on the `V` side — rather than a
symmetry argument.  It is also not vacuous: the conjectured optimum, the Z/S
pair, is a *double* corner, so single-corner maximisers are exactly what has to
be ruled out.

### 7e²². **Conjecture 1 at `p = 0` is a theorem**

The last case dissolved.  `zsValue` is **symmetric**:

```
zsValue a d = d/(1+d)·log(1+a) + (1−ad)/((1+a)(1+d))·log(1−ad) + a/(1+a)·log(1+d)
```

— exchanging `a` and `d` permutes the three terms (`zsValue_symm`).  And
`mutualInfo` is transpose-invariant, with

```
jointUX c = transpose (jointYV c) ,      jointUV 0 cR cL = transpose (jointUV 0 cL cR)
```

(the second because `dsbs p` is symmetric).  So swapping the two sides turns a
`U`-corner into a `V`-corner *and* exchanges the budgets, and `cornerBound`
applies verbatim:

> **`cornerBoundU`** — the mirror of `(D)`, axiom-clean.

I had expected this case to need a fresh certificate on the `V` side; it does
not.  The earlier reading — that the asymmetry of the rate constraints blocks
the swap — was wrong: the swap exchanges the budgets *too*, and the value bound
`zsValue` is invariant under that exchange.

> **`conjecture1_p0_holds : Conjecture1_p0`**

Axioms: `propext`, `Classical.choice`, `Quot.sound`, and a single
the `native_decide` axiom, from the 24129-monomial Pólya expansion of the kernel
lemma (`KernelCertFast.lean`).  The other computed step, the 650-cell interval
sweep of regime 2, is checked by the **kernel** (`CoreSweep.lean`) and adds no
axiom.  Zero `sorry`s.

The full chain: `(A)` existence → `(B)` classification (Green identity, fold,
`(♦)`, bitangency, KKT) → `(C)` the saddle (the kernel lemma, the diagonal
reduction, `saddle_iii`, the Hessian identification, the corrected curve) →
`(D)` the corner bound and its mirror → assembly.

### 7g. **Conjecture 2 at `p = 0` is a theorem — and needs no certificate**

> **`conjecture2_p0_holds : Conjecture2_p0`**
> Axioms: `propext`, `Classical.choice`, `Quot.sound`. **No `native_decide`.**

`CornerDominationMin` — the hypothesis of the old reduction — is **false as
stated**.  Numerically, against `cL` with atoms `(0.492, −0.997)` and `d = 0.755`
the S-channel gives `0.2433` while the *flipped* S-channel (atoms `(d, −1)`
instead of `(1, −d)`) gives `0.1975`: the corner must align with `cL`'s skew.
The conjecture itself survives — a global 4-parameter search over both sides
finds the minimum at the aligned Z/Z pair, matching `mzsValue` to `8·10⁻¹⁰`.

A **joint two-variable certificate** `f(st) ≥ affine + λf_e(s) + μf_e(t)` would have
bypassed the variational argument, but it is overdetermined: four contact
equations plus four tangency conditions against six unknowns.  So Conjecture 2
takes the same four-step route as Conjecture 1:

* **`(A′)` `minExistsC`** — compactness, with `Set.Ici` in place of `Set.Iic`.
* **`(B′)`** — *free*.  KKT for `min V` under `R ≥ C` and for `max V` under
  `R ≤ C` have the **same** form, `∇V = λ∇R` with `λ ≥ 0`: negating the
  direction turns one directional hypothesis into the other verbatim
  (`le_zero_of_deriv_of_min`, `stationary_of_min`).  So the whole `§7c⁗`
  classification was restated once for `OptPairC = IsMaxPairC ∨ IsMinPairC`,
  a twelve-site edit, and `interiorIsBSC_of_noCorner` now serves both.
* **`(C′)` `symmetric_not_min`** — **cheaper** than `(C)`.  The maximisation
  needed the *indefinite* Hessian direction, i.e. the saddle inequality `(iii)`
  and its two certified computations.  The minimisation only needs
  `form < 0`, and `d₂ = 0` gives `form = F_pp < 0` by `Fpp_neg` alone.  The
  corrections now push both rates **up** (`exists_bad_corrections`), which is
  feasibility for `R ≥ C`.
* **`(D′)` `cornerBoundMin`** — `bestResponse_ge_of_certificate` with the mirror
  certificate `MDFun_nonpos`, reflected by `σ`.  Two new ingredients: `mzsValue`
  is increasing in `d` (`mzsValue_strictMonoOn_snd`, from the closed form
  `mzsNum a d/((1+a)(1+d))`; the derivative numerator collapses to
  `(1−a)log((1−a)/(1+da)) + 2a·log(2/(1−d))`, positive by three `log x ≤ x−1`
  bounds and `log 2 > ½`), and the case `d′ = 1` — a *deterministic* `V`-side,
  which `cornerBound` could exclude but `cornerBoundMin` cannot: it is handled
  by the trivial certificate `(0,0,1)` plus `mzsValue a d < zsRate a =
  mzsValue a 1`.  The mirror `cornerBoundMinU` is again the side-swap, since
  `mzsNum a d = mzsNum d a` termwise.

Both conjectures of Entropy 24(9):1321 are now theorems at `p = 0`.

### 7h. **Library layout: the proof vs. the `Exploration` space**

The library is now split by the *transitive dependency closure* of its three
theorems — `averaged_bsc_maximise_mutual_information`, `conjecture1_p0_holds`,
`conjecture2_p0_holds`.  `BSCAveraging.Basic` imports exactly that closure
(15.0k lines, 42 files); everything else — 21.3k lines, 19 files — moved to
`BSCAveraging/Exploration/`, still `sorry`-free and still built.

The closure was computed inside Lean (walk `ConstantInfo` types *and* values
from the three roots; note `ConstantInfo.value?` returns `none` for theorems in
Lean 4.32, so match `.thmInfo` explicitly).  Three corrections to the naive
"outside the closure ⟹ unused" rule were needed, each found by a failing build:

* `@[simp]` lemmas may fire without appearing in the resulting term (simp
  closes by `rfl`), so they are never moved out on their own — only when they
  mention something that is itself leaving;
* `private` helpers are invisible across modules, so a private lemma used only
  by exiting declarations must exit with them;
* a declaration whose *name* occurs anywhere in the retained code stays, no
  matter what the closure says — this catches everything the term-level walk
  cannot see.

`Exploration/Misc.lean` (the old `Exploration.lean`) re-derives names that the
main development also defines, so it now lives in `BSCAveraging.Legacy`.

### 7i. **The regime-2 sweep is now kernel-checked**

`core_pos_regime2` no longer uses `native_decide`; it is `decide +kernel`, and
its axioms are `propext`, `Classical.choice`, `Quot.sound`.  So
`conjecture1_p0_holds` now depends on **one** the `native_decide` axiom, the kernel
lemma's coefficient check, instead of two sources.

Three measurements decided the design (all on the hard end of the range, warm
cache; earlier numbers that looked 5× worse were cold-cache artefacts):

* **0.83 s per cell** at the original `(k,n,m) = (4,25,10¹²)`, flat across
  `[0.45,3]`; **0.58 s** at `(4,10,10⁹)`, the cheapest parameters that still
  pass all 650 cells (even `n = 8` passes — the generated witnesses have ample
  slack).  Parameter tuning is worth 25 %, no more: the cost is not the series
  length but the per-`ℚ`-operation overhead of kernel reduction, about 1.7 ms.
* **Caching works.**  `fOk` costs about three `coshI`, matching the number of
  *distinct* subterms, so the kernel is not re-reducing the repeated `let`-bound
  intervals.  Restructuring for sharing would gain nothing.
* **Memory is the real constraint.**  One `decide` over 20 cells peaks at
  4.4 GB — roughly 200 MB per cell of retained intermediate `ℚ`s with their
  proof fields.  Over all 650 that is tens of gigabytes (the first attempt ate
  40 GB before it was killed).  Chunking fixes it: peak RSS *plateaus* near
  4 GB (40 cells → 3.5 GB, 80 → 3.9 GB), because the allocator reuses the arena
  between declarations.

So: 65 blocks of ten cells, each its own `decide +kernel`, recombined with
`List.all_append`.  **355 s and 6.7 GB**, against 14 s for `native_decide`.

**The kernel lemma cannot follow.**  It is not a matter of tuning:

* `Poly.collect` calls `List.mergeSort`, which is defined by well-founded
  recursion and **does not reduce in the kernel** — even a two-monomial product
  gets stuck.  A fuel-driven structural sort would be needed first.
* Even then, the expansion costs `6.8·10⁶` monomial products and `1.5·10⁸`
  comparisons in the collecting sort (counted by simulating `PE.norm` in
  Python).  At the kernel throughput measured above that is hours, and the
  retained intermediates would be far past the machine's memory.

That is three to four orders of magnitude, not a constant factor, so
`kerQPE_allNonneg` stays under `native_decide`.

### 7j. A 100×-smaller certificate for the kernel lemma — the route out of `native_decide`

The search for a cheaper certificate succeeded on paper.  Three changes, each
validated numerically end to end (`numerics/` scripts in the scratch record):

**1. Better coordinates.**  With `y = θ/(1−θ)`, `A = 1−u`, `B = 1−v` and
`C = 1−uv = A+B−AB`,

```
f_i = 1/(1+y_iA),   g_i = 1/(1+y_iC),   r_i = (1+y_iA)/(1+y_iB)
```

and, writing `F_i = 1+y_iA`, `G_i = 1+y_iC`, `H_i = 1+y_iB`, the cleared kernel
is the compact

```
Σ_i F_jF_k · G_i(G_j+G_k) · H_jH_k · (F_i²H_jH_k − F_jF_kH_i²) .
```

Ordering by `y₁ ≤ y₂ ≤ y₃` (`y = z₁, z₁+z₂, z₁+z₂+z₃`) and `A = a`, `B = a+b`
gives **five** variables instead of seven and **2044 monomials instead of
24129** — with expansion cost `7.2·10⁴` products instead of `6.8·10⁶`, a factor
of 95.

**2. The certificate decouples by z-monomial.**  Grouping the expansion by its
`z`-part gives **142 groups**, each a polynomial in `(a,b)` alone — and *every
one is nonnegative on the triangle* `a,b ≥ 0`, `a+b ≤ 1`.  Since `z^α ≥ 0`, that
suffices.  Each group is divisible by `a·b`: `a = 0` is the face `u = 1` and
`b = 0` is `u = v`, the two places where the kernel vanishes identically.

**3. Blow up the remaining corner, then Bernstein.**  After factoring `a^i b^j`
the quotients still vanish at the vertex `a = b = 0` (i.e. `u = v = 1`, where
`r ≡ 1`), which is what defeats Pólya — no elevation up to 40 works.  The
substitution

```
a = s(1−w),  b = sw          i.e.  s = 1−v,  w = (u−v)/(1−v)
```

maps the box `[0,1]²` onto the triangle and turns the corner zero into a factor
`s^{m}`.  On the box the natural certificate is the Bernstein basis, and there

> **every one of the 142 groups has nonnegative Bernstein coefficients at
> elevation 0** — no elevation at all.

Scaled by the binomials, `b_{IJ} = Σ_{p≤I,q≤J} c_{pq}·C(d_s−p, I−p)·C(d_w−q, J−q)`,
the coefficients are **integers**: 1404 of them, all `≥ 0`, max `2592`.

**Validation.**  The cleared five-variable polynomial agrees with the original
kernel times its explicit denominator to `2.7·10⁻¹¹` over 2000 random points,
and the certificate reconstructs the polynomial to `6.8·10⁻¹⁵`.

**What this buys.**  The kernel check becomes: expand `7.2·10⁴` products
(against `6.8·10⁶`), then verify 1404 integer inequalities.  That is inside what
the Lean kernel can do — the `decide +kernel` sweep already performs comparable
work per cell.  Formalising it still needs three things, none of them research:

* the change of variables, as an algebraic identity relating the original
  `KernelLemma` statement to the new cleared polynomial (a `field_simp; ring` on
  a moderate expression, probably in the abstract-letters style of §7f¹²);
* a structural (fuel-driven) replacement for `List.mergeSort`, which is
  well-founded and does not reduce in the kernel at all;
* the Bernstein step: the identity `group = a^i b^j s^m Σ b_{IJ} B_I(s)B_J(w)`
  per group, and `B_I ≥ 0` on the box.

**What failed, and why it is worth recording.**  A "hybrid split"
`kerQ = P₁ + P₂` with `P₂` structurally nonneg buys nothing: *verifying* the
split is itself a polynomial identity, so it costs the same expansion.  The
kernel is not monotone in `u` or in `v` (both derivatives take both signs over
2·10⁵ samples), so the vanishing face `u = 1` cannot be reached by integration.
And the lemma is *not* a consequence of monotonicity alone: with `f, g, r` free
decreasing positive triples — even imposing `g/f` and `fg` decreasing — it fails
on 25–34 % of samples.  The specific rational structure is essential, which is
why the abstract Schur/comonotone route stalls.

#### 7j′. Implementation attempt, and where it stands

Implemented and kept:

* **`Poly.msort`** in `Reflect.lean` — a fuel-driven structural merge sort over
  a tail-recursive `Poly.mergeAux`, with `Poly.eval_merge` / `Poly.eval_msort`,
  now the sort used by `Poly.collect` in place of `List.mergeSort`.  With it the kernel *can* reduce `PE.norm`: the two-monomial
  product that used to get stuck now goes through, and a degree-12 trinomial
  power (91 monomials) takes about a second.
* **`Exploration/KernelCertBern.lean`** — the new tree `kerBPE` over
  `(z₁,z₂,z₃,s,s′,w,w′)`, whose expansion is **4000 monomials, every
  coefficient a positive integer**, at `2.1·10⁵` products.  Its `native_decide`
  check takes **5.8 s**, against 138 s for the 24129-monomial tree of
  `KernelCertFast.lean`.

What did **not** work, and the numbers that say so:

* Kernel throughput on this kind of symbolic list arithmetic is about `10⁴`
  elementary steps per second.  The expansion needs `2.1·10⁵` products plus
  roughly `3·10⁶` sort steps — minutes at best in principle, but
* the kernel **retains every intermediate**.  `Poly.mul` builds the entire
  unsorted product list before collecting, and the largest one here has `68544`
  entries.  `decide +kernel` on `kerBPE_allNonneg` peaked at **89 GB** and timed
  out at ten minutes.
* Reordering the seven factors of each term to minimise `Σ|p||q|` (all `7!`
  orders searched) improves the product count only `1.8×`, `76940 → 42719` per
  term, and leaves the largest intermediate unchanged at `5384`.
* `Poly.msort` needed a **tail-recursive** merge before it could be wired into
  `Poly.collect`: the first version recursed in the cons position, and on
  `KernelCertFast`'s `68544`-entry lists the *compiled* code overflowed the
  stack, aborting `native_decide` (exit 134).  `Poly.mergeAux` accumulates the
  output in reverse and flushes it with `List.reverseAux`; with that,
  `Poly.collect` now uses `msort` and `KernelCertFast` builds in 152 s against
  138 s for `List.mergeSort` — a 10 % price for a sort the kernel can reduce.

**The merge-based product, measured.**  `Poly.cmul` was then rewritten to merge
each scaled copy of `q` into an already collected accumulator, so that no list
larger than the output is ever built (`Poly.addC`, `Poly.eval_cmul` by induction
on `p`).  It does what it was meant to do and it is still not enough:

| | flatMap + sort | merge-based |
| --- | --- | --- |
| `KernelCertFast` (`native_decide`) | 152 s | 170 s |
| `decide +kernel` on `kerBPE` | 89 GB | **> 30 GB** (guard) |

Bounding the *list length* does not bound the memory, because the kernel retains
every intermediate accumulator, and `2.1·10⁵` products means a great many of
them.  Three-fold better, two orders short.

**Splitting the sum does not help either.**  If each of the three cyclic terms
were separately coefficient-nonnegative, each could be its own `decide +kernel`
and the sum would need no expansion at all.  They are not: `term(0,1,2)` is
nonnegative (5384 monomials, min coefficient 1), but `term(1,2,0)` has 3186
negative coefficients and `term(2,0,1)` is negative in *all* 4912.  The
cancellation between the three is essential, so any regrouping has to be
verified by an expansion, which is the cost we are trying to avoid.

**The `ring` route, measured too.**  The last idea was to abandon reflection for
this step: supply the expansion as data, check `allNonneg` on it by a linear
scan, and prove the identity `Poly.eval kerBC ρ = ⟨product form⟩` by `ring`.
The first two thirds work and are cheap:

* the 4000-entry `Poly` literal elaborates in about 8 s (103 KB of source), and
  `decide +kernel` on `kerBC.allNonneg` passes — a linear scan is exactly the
  kind of thing the kernel is fine with;
* unfolding `Poly.eval` over the 4000-element list with `simp only` costs
  **2.2 GB** and completes (it needs `maxSteps` raised; the default 100000 is
  not enough).

`ring` on the resulting identity does not: **> 43 GB and > 8.7 minutes, still
unfinished** when the run was stopped.  So the size of the normalised object,
not the mechanism, is what defeats every route.  For comparison, `native_decide`
on the same tree takes **5.8 s**.

That closes the three routes: kernel expansion (30–89 GB), splitting the cyclic
sum (impossible — only one of the three terms is coefficient-nonnegative), and
`ring` (>43 GB).  `kerQPE_allNonneg` stays under `native_decide`, and the
certificate work still pays for itself: `KernelCertFast`'s check would drop from
138 s to 5.8 s if the bridge to the new coordinates were written.

#### 7j″. The bridge to the new coordinates

`Exploration/KernelBridgeB.lean` connects the small certificate to `kernelSum`.
The substitution is chosen so that **both units evaluate to `1`**,

```
y_i = θ_i/(1−θ_i),  z₁ = y₁, z₂ = y₂−y₁, z₃ = y₃−y₂,
s = 1−v,  s' = v,  w = (u−v)/(1−v),  w' = (1−u)/(1−v),
```

and then no scaling factor survives: `s+s' = 1`, `w+w' = 1`, `A = s·w' = 1−u`,
`B = s = 1−v`, `C = A+B−AB = 1−uv`, so the tree evaluates *exactly* to

```
Σ_i F̂_jF̂_k · Ĝ_i(Ĝ_j+Ĝ_k) · Ĥ_jĤ_k · (F̂_i²Ĥ_jĤ_k − F̂_jF̂_kĤ_i²),
F̂ = 1+y(1−u) = (1−θu)/(1−θ),  Ĝ = 1+y(1−uv),  Ĥ = 1+y(1−v).
```

The chain is four steps, none of which expands anything:

* `eval_kerBPE_subst` — the tree at the substituted point, by `simp only` with
  the five normalisations above.  **No `ring` on the product**: that would
  expand to 4000 monomials and cost >43 GB, as §7j′ measured.  The five facts
  are rewritten in place and the two sides become syntactically equal.
* `clearB_abstract` — the clearing identity in **nine** abstract letters
  (against twelve in `KernelBridge.lean`), one `field_simp; ring`.
* `FB_yOf`/`GB_yOf`/`HB_yOf` and `one_div_FB`/`one_div_GB`/`FB_div_HB` —
  `f = 1/F̂`, `g = 1/Ĝ`, `r = F̂/Ĥ`, each a two-line rewrite.
* `kernelSum_nonneg_B`, then `kernelSum_nonneg_B'` with the ordering removed by
  the existing `kernelSum_swap` lemmas.

> **`kernelSum_nonneg_B'`** — the kernel lemma for `θᵢ ∈ [0,1)`, `0 ≤ v ≤ u < 1`,
> through a certificate that checks in **5.8 s** instead of 138 s.

**What is still missing for a drop-in replacement.**  Only the endpoint
`θᵢ = 1`, where `y = θ/(1−θ)` is infinite.  `KernelBridge.lean` proves the
`θᵢ ≤ 1` version, and the diagonal reduction needs it there: its integrand runs
over `θ = s²` with `s ∈ [0,1]`.  The fix is a continuity argument — the kernel
sum is continuous in a scaling parameter `c ↑ 1` applied to all three `θᵢ`, and
the denominators stay away from zero — not a new obstruction, just work.

### 7k. The certificate in one big integer — kernel-checkable after all

`Exploration/KernelCertKron.lean`.  §7i–§7j′ all tried to do *symbolic*
polynomial arithmetic in the kernel and were killed by retained intermediates
(30–89 GB expansion, >43 GB `ring`, the cyclic sum unsplittable).  None used the
one thing the kernel does fast: GMP arithmetic on `Nat` literals.  On v4.32.0
`Nat.pow`, `mul`, `sub`, `div`, `mod`, `land`, `ble` on literals all reduce in
the kernel by GMP (`pow` with exponent `< 2^24`) — a 12-fold product of 2 MB
numbers, a `pow` to `371292`, and a `land` against a 20 Mbit mask check in
0.3 s.

**Kronecker substitution.**  Never expand.  Dehomogenise (`t₄ = s₃ = 1`) and
evaluate the tree `kerQPE` at

```
(t₁,t₂,t₃,t₄,s₁,s₂,s₃) = (B, B^13, B^169, 1, B^2197, B^28561, 1),   B = 2^64.
```

Bidegree `(12,12)` puts every exponent of `t₁,t₂,t₃,s₁,s₂` at `≤ 12`, so the
exponent vector maps injectively to the slot `e₁+13e₂+169e₃+2197e₅+28561e₆ <
371293`, and the value `N` is the coefficient vector in base `B`.  The
structural L1 bound of the tree (products and sums of the factors' L1 norms,
no expansion) is `1667733694599168 < 2^51 < B/2`, so no digit overflows or
borrows, and by balanced-representation uniqueness

> all coefficients `≥ 0`  ⟺  every 64-bit digit has top bit `0`
> ⟺  `N.land mask = 0`,  `mask = 2^63·(B^371293−1)/(B−1)`.

**Measured.**

| | wall (incl. 2.7 s import) | peak RSS over the 1.66 GB import |
| --- | --- | --- |
| evaluate the product form at the point, `0 ≤ N`, `N < B^371293` | 2.7 s | — |
| **`N.land mask = 0`** — the certificate | **3.3 s** | **+230 MB** |
| divide-and-conquer digit scan instead of the mask | 72 s | 14 GB |
| `native_decide` on `kerQPE.norm.allNonneg` (`KernelCertFast.lean`) | 138 s | — |

Negative control: a leaf threshold of `2^26`, below the largest coefficient
`74 216 288`, fails.  Not the 7-variable homogeneous version: `13^7` slots is a
500 MB number and the `pow` exponent exceeds `2^24`.  Not the D&C scan: the
kernel retains every level of the recursion.

**What is missing is glue, not computation** (a few hundred lines, no research):

* `evalZ` versus `PE.eval` under the cast `ℤ → ℝ`, and `Poly.eval` likewise, so
  `PE.eval_norm` transfers to `ℤ`;
* structural `PE.l1bound : PE → ℕ` and `PE.bideg : PE → Option (ℕ × ℕ)` with
  lemmas that `PE.norm` respects them through `collect` (permutation, merge of
  equal keys), `cmul` (`M7.mul` adds exponents, L1 submultiplicative), `cpow`,
  `neg`, `++`; `decide` then computes `kerQPE.l1bound` and `kerQPE.bideg`;
* balanced base-`B` uniqueness, and `land mask = 0 → ∀ e, (N / B^e) % B < 2^63`
  (`Nat.testBit_land`, `Nat.testBit_two_pow`, `Nat.geomSum_eq` for `mask`).

With those, `kerQPE_allNonneg` follows from `Kron.digits_mask`, and the
development is at `[propext, Classical.choice, Quot.sound]` throughout.

### 7l. Could (C) be replaced by a global comparison, or by a path? — no shortcut

`numerics/corner_path.py`.  Steps (A), (B), (D) leave an optimiser in {BSC
pair, corner, degenerate}.  So (C) — the BSC pair is a saddle — could be
replaced by the **global** statement

> `V(BSC_s, BSC_t) ≤ V(Z_a, S_d)` whenever the rates agree, `f_e(s) = R_Z(a)`,
> `f_e(t) = R_Z(d)` (and `≥ V(Z_a, Z_d)` for the minimum):

a BSC optimiser would then be matched by a feasible corner, and the whole of
§4.3–§4.4 (Hessian, second-order KKT, kernel lemma and its certificate, the
core inequality with its three regimes and the 650-cell sweep) would go.

**The inequality is true, numerically, with clean slack.**  On a 199×199 grid,
both directions, no violation.  `V_ZS/V_BSC − 1` is about `4.1 %` for small
biases (not a moment effect: `V_ZS ≈ ad` against `V_BSC ≈ ½s²t²` with
`a ≈ r/ln 2`, `s² ≈ 2r`, ratio `1/(2 ln²2) = 1.0407`) and tends to `0` only at
`(s,t) → (1,1)`, linearly: `1.2·10⁻³` at `1−s = 10⁻²`, `9.7·10⁻⁵` at `10⁻³`.
`V_ZZ/V_BSC` runs from `0.40` to `1`.

**It does not decompose into one-sided steps.**  The natural proof would be two
LP-certificate steps of the kind in §4.5: (1) fix `V = BSC_t`, replace `BSC_s`
by `Z_a` at equal rate; (2) fix `U = Z_a`, replace `BSC_t` by `S_d` — step (2)
is the corner theorem.  Step (1) is **false**:

```
V(Z_a, BSC_t) / V(BSC_s, BSC_t) at equal rate:  0.72 … 0.97, always < 1
```

Against a fixed BSC the corner is *worse*, which is `F_pp < 0` of the Hessian
lemma: along either side alone, at fixed rate, the BSC is a local maximum.  The
corner only wins when both sides skew, in opposite directions, and that gain
is the off-diagonal `F_pq`.  The comparison is the saddle stated globally.

**The path.**  Move both sides at once: keep each side a mean-zero two-atom
law, move its centre linearly, `p = ℓ(a−1)/2`, `q = ℓ(1−d)/2`, and solve the
half-gap from the fixed rate.  `ℓ = 0` is the BSC pair, `ℓ = 1` is exactly
`(Z_a, S_d)`.  Along it `V(ℓ)` is **monotone and convex at all 361 grid points
(21 steps each)**, with `V'(0) = 0` and most of the gain in the last tenth:

```
s=t=0.5   V(ℓ)/V(0):  1.0000 1.0001 1.0004 1.0008 1.0016 1.0027 1.0043 1.0068 1.0107 1.0178 1.0396
```

Two things a proof along the path would have to contain:

* `V'(0) = 0` by parity, so positivity near `ℓ = 0` is again the quadratic
  form of Lemma 4.8, in the *specific* direction `((a−1)/2, (1−d)/2)`:
  `V''(0)/V(0) ≈ 4·10⁻⁴`, small because that direction is far from the
  optimal `(1, −F_pq/F_qq)`, and implicit in `a, d`.  The path fixes which
  direction to check; it does not remove the Hessian.
* Away from `0` the gain is a **race**, not a monotone quantity.  Splitting
  `V = E f_e(ST) + E f_o(ST)` along the path at `s = t = ½`:

  ```
  ℓ     even/V₀   odd/V₀
  0.0   1.0000   +0.0000
  0.4   0.9653   +0.0363
  0.8   0.8657   +0.1450
  1.0   0.7862   +0.2535
  ```

  the even part falls 21 %, the odd gain `Ω` rises 25 %, net `+4 %`.  So
  monotonicity is "`Ω` outruns the even loss everywhere on the path, for every
  `(s,t)`" — a three-parameter inequality with an implicit endpoint.  §3's
  tools bound `Ω` from *above* for opposite skews; here one needs a lower bound
  on `Ω'` beating an explicit even-part loss.

**Without the rate constraint there is no path.**  Interpolating the atoms
linearly to the corner, `s₁ = (1−ℓ)s + ℓa`, `s₂ = −(1−ℓ)s − ℓ`, weights from
mean zero, and ignoring the intermediate rates: the intermediate laws have much
larger gaps, hence much larger value, and `V(ℓ)` overshoots and comes back —
`×9.5` at `s = t = 0.1` — or dips *below* `V(0)` in the middle (`s = t = 0.9`,
minimum `0.979`).  Non-monotone at all 1521 grid points.  Holding the rates is
what makes the path monotone; drop it and there is nothing to prove along it.

**Is convexity along the path provable?**  Three measurements say where such a
proof would have to be hard (`corner_path.py` (3c)):

* `V''(ℓ)/V(0)` is smallest at `ℓ = 0` everywhere and grows by two to three
  orders toward `ℓ = 1` (`s = t = 0.1`: `1.1·10⁻³` at `ℓ = .05`, `3.5` at
  `.95`).  The binding point is the Hessian at the BSC.
* At `ℓ = 0` the claim is that the path direction `((a−1)/2, (1−d)/2)` lies
  *inside* the positive cone of the indefinite form — strictly more than the
  saddle inequality, which says the cone is nonempty.  For `s = t` the
  direction is the cone's axis, the best possible, and the margin
  `Q/(|F_pp|p₁² + |F_qq|q₁²)` still vanishes like `s²` because the cone
  collapses: `(0.974, 1.026)` and `+0.0003` at `s = t = 0.05`, `(0.756, 1.322)`
  and `+0.039` at `0.5`.  Intrinsic, not a bad path: at small bias every law at
  equal rate ties to leading order, `V ≈ ½E S²E T²`, and the direction is
  implicit in `R_Z⁻¹`.  So the `ℓ = 0` piece is a sixth-order-in-bias
  inequality with an implicit direction: what the kernel lemma proves, plus
  more.  It cannot cost less than the certificate.
* `V'(ℓ)/V(0)` diverges logarithmically as `ℓ → 1` — the atom reaching `−1`,
  `f'(z) = 1 + ln(1+z)` — harmless for convexity, one more thing to handle.

The path *creates* the degeneracy: the global comparison has a zero-order 4 %
gap at small bias exactly where the path is flat to sixth order.  Its only thin
region is `(s,t) → (1,1)`, slack `≈ 0.1·(1−s)`.  If anything replaces (C)
analytically it is the global inequality attacked directly — perturbation at
`(1,1)` plus the bulk — not convexity along a path through the BSC.

**How a direct attack on the global comparison would go** (`corner_path.py`
(3d)).  Write `Δ(s,t) = V_ZS(a(s),d(t)) − f_e(st)` with `a = R_Z⁻¹∘f_e`.

* *Where it is thin.*  Not the diagonal — there the relative slack is largest,
  `≈ 4 %` — but the **edges** `s = 1` and `t = 1`, where it vanishes
  identically: at `s = 1` the U-side is noiseless in both pairs (`BSC₁ = Z₁`),
  so both values equal the V-rate.  Along `st = x` the minimum is at
  `s → 1` for every `x`.  So there is no diagonal reduction; the critical set is
  the boundary.
* *The edge is first-order regular.*  Both values are regular in `(σ, α)`,
  `s = 1−σ`, `a = 1−α`; the only singular object is the rate inversion,
  `(σ/2)ln(2/σ) ≈ (α/4)ln(2/α)`, so `α/σ → 2` with `1/ln(1/σ)` corrections
  (`2.26` at `σ = 0.1`, `2.10` at `10⁻⁶`).  Hence

  ```
  Δ/(σ·V_BSC) = [ t·artanh t − (α/σ)·∂ₐV_ZS(1,d) ] / f_e(t) + O(σ),
  ```

  verified against the observed slope to three digits for `σ ≤ 10⁻³`
  (`0.414/0.414`, `0.449/0.449`), and the limit coefficient
  `c(t) = [t·artanh t − 2∂ₐV_ZS(1,d(t))]/f_e(t)` is `0.56 … 0.60` on all of
  `(0,1)` — positive with margin, nearly constant.  The finite-`σ` slope is
  smaller (`0.21` at `σ = 0.1`) only because `α/σ > 2`.
* *The corner is doubly degenerate.*  At `s = t = 1−σ` the `O(σ)` term cancels
  and `Δ/V_BSC ≈ ln 2 · σ/ln(1/σ)` (`slack/σ · ln(1/σ) → 0.69`).  A proof there
  needs the log-correction of the inversion exactly.
* *The bulk is not crude-boundable.*  The explicit `a ≥ f_e(s)/ln 2` (from
  `R_Z(a) ≤ a ln 2`, exact at `s = 1`) loses `13 %` at `s ≈ 0.87` against a
  true slack of `1 %`: `1 − a ≈ 2σ` while `1 − f_e(s)/ln 2 ≈ (σ/2ln 2)ln(2/σ)`.
  Bounds accurate to first order with log terms are needed; `R_Z` is concave on
  `(0, 0.45)` and convex after, so one-sided Newton bounds change side.
* *The minimum side is easier*: at the edge `(V_BSC − V_ZZ)/V_BSC ≈ σ ln(1/σ)`,
  the log does not cancel.

So a proof would be: (i) an edge strip `σ ≤ σ₀` by the first-order expansion
with a rigorous remainder and explicit two-sided bounds on `α(σ)` carrying the
log term; (ii) a corner box by the double expansion; (iii) the bulk
`s,t ≤ 1−σ₀`, slack `≳ 0.2σ₀`, by sharper explicit bounds on `a(s)` and then
either an analytic argument nobody has or a kernel-checked 2-D sweep.  Not
shorter than §4.3–§4.4, and the axiom it would remove is already removable by
§7k.  Worth doing only if (iii) turns out to have an analytic proof.

**Verdict.**  Right way to see *why* the corner wins — anti-aligned skew buys
odd gain faster than it loses even value — and convexity in `ℓ` with
`V'(0) = 0` would be the cleanest single hypothesis (one second-order statement
along the whole path, of which Lemma 4.8 is the `ℓ = 0` case).  But it is a
different, unproved route to the same place, not a reduction: the local piece
is the Hessian in a worse direction, the global piece a quantitative race.  (C)
stays.

### 7f. The saddle inequality (iii) — proved

`(iii)` is the last analytic step of Conjecture 1 at `p = 0`:

> for `α, β ∈ (0,1)` and `x = αβ`, with `g(y) = (1−y²)·artanh y / y`,
> `(1 − g(x))² > x²·(g(x)/g(α) − 1)(g(x)/g(β) − 1)`.

**Reduction to one variable.**  For fixed product `x = αβ` the right-hand side
depends only on `x`, and `κ_ακ_β` is *maximised on the diagonal* (verified to 50
digits; a proof of this step is still open).  On the diagonal, writing
`y = tanh θ` and clearing `g`, the statement becomes classical:

```
1/log Z − 1/(Z−1) > tanh θ/(2θ),     Z = cosh 2θ
```

equivalently `1 − L(σ) > tanh θ/θ` with `L` the **Langevin function**
`L(z) = coth z − 1/z` and `σ = ½ log cosh 2θ`, using `1/log(1+t) − 1/t =
1/s − 1/(eˢ−1)`.  Cleared of denominators:

```
Δ(θ) := 2θ sinh²θ − log cosh(2θ)·[θ + sinh²θ·tanh θ]  >  0            (Δ)
```

with a zero of order **nine** at `θ = 0`, `Δ = (8/45)θ⁹ − (8/21)θ¹¹ + …`.

**Why the soft arguments fail.**  The slack is `(2/45)θ⁴` at `0` and
`log2/(4θ²)` at `∞`, vanishing at both ends, so every standard tool loses
exactly the margin: `log(1+t) ≤ t/√(1+t)`, the Padé bounds `t(2+t)/(2+2t)` and
`t(6+t)/(6+4t)`, the Langevin bound `L(z) < tanh(z/3)` (good only to `θ ≲ 2.3`),
the Chebyshev association bound on the increasing density `tanh v`, and the
single-crossing weight bound — the last two both reduce to `tanh(u/2) ≥ u/2`,
which is false.  Series positivity fails too: the coefficients of `Δ` alternate
with growing magnitude, and the two-variable form has mixed-sign coefficients
from `u²v⁴` on.  Naive interval arithmetic dies of the dependency problem: at
`θ = 2.5·10⁻⁴` the enclosure is `±6·10⁻¹⁰` around a true value of `10⁻³³`.

**The proof.**  Three regimes with explicit constants, overlapping to cover
`(0,∞)` — `numerics/p0_saddle_inequality_proof.py`:

1. **`0 < θ ≤ 0.45`.**  Write `Δ/θ⁹ = Σ_k h_k θ^{2k}`, `h_0 = 8/45`,
   `h_1 = −8/21`, … (nine exact rational coefficients).  `Δ` is analytic for
   `|θ| < π/4`; on `|θ| = 0.75`, using `|sinh θ| ≤ sinh 0.75`,
   `|cosh 2θ| ≥ cos 1.5` and `|tanh θ| ≤ tan 0.75`, one gets `|Δ| ≤ M = 9.05`,
   hence by Cauchy `|h_k| ≤ (M/0.75⁹)·(1/0.75²)^k = 120.5·1.7778^k`.  The
   resulting lower bound `Σ_{k≤8} h_kθ^{2k} − 120.5·(1.7778θ²)⁹/(1−1.7778θ²)`
   has minimum **0.1015 > 0** on `(0,0.45]` (grid of 450 points; the bound's
   derivative is `< 5` there, so the grid check is rigorous).
2. **`0.45 ≤ θ ≤ 3`.**  Certified stepping: every factor of `Δ′` is positive and
   increasing and `sech² ≤ 1`, so
   `K(b) = 2sh² + 4b·sh·ch + 2(b+sh²) + log cosh 2b·(1 + 2sh·ch + sh²)`
   majorises `|Δ′|` on `(0,b]`, giving `Δ(x) ≥ Δ(a) − K·(x−a)` and a step of
   `0.9·Δ(a)/K`.  **6243 steps** carry `0.45 → 3`, all strictly positive.
3. **`θ ≥ 3`.**  Elementary: `log cosh 2θ ≤ 2θ − log2 + e^{−4θ}`, `tanh θ ≤ 1`,
   `θ/sinh²θ ≤ 4.02θe^{−2θ}`, so the claim reduces to
   `log 2 > e^{−4θ} + 8.04θ²e^{−2θ}`, whose right side is `0.179` at `θ = 3`
   and decreasing.

`(0,0.45] ∪ [0.45,3] ∪ [3,∞) = (0,∞)`.  ∎

The proof is computer-assisted in regime 2 (a finite certified computation) and
in the grid check of regime 1; both are finite and reproducible, and both would
formalise, though regime 2 would need 6243 certified steps or a smarter
argument.  **What is still open in the chain: the diagonal reduction** — that
`κ_ακ_β` is maximised on `αβ = const` at `α = β`.


**The diagonal reduction — the one link still open.**  With `u = α²`, `v = β²`
and `Ĝ(z) = G̃(√z) = 2Σ_{k≥1} z^k/(4k²−1)` (positive coefficients, `Ĝ(1) = 1`),
the reduction "`κ_ακ_β` is maximised on `αβ = const` at `α = β`" is equivalent,
after taking `d/dw` along `α = √x e^w`, `β = √x e^{−w}`, to

```
R(u,v) := vĜ′(v)(1−Ĝ(u))(Ĝ(u)−Ĝ(uv)) − uĜ′(u)(1−Ĝ(v))(Ĝ(v)−Ĝ(uv))  ≥ 0   (u ≥ v)
```

`R` is antisymmetric and vanishes on the diagonal, so `R = (u−v)·S` with `S`
symmetric; the claim is `S ≥ 0` on `(0,1)²`.  The exact coefficients of `S`
(`numerics/p0_diagonal_reduction.py`) have a suggestive shape — **positive
diagonal, negative off-diagonal**:

```
s_ii = 0.05926, 0.03894, 0.02275, 0.01477, 0.01034, …
s_1j = −0.01693, −0.01185, −0.00759, −0.00506, …          (all i≠j negative)
```

so the natural attack is diagonal dominance.  It does not survive the crude
bound: with `u^i v^j + u^j v^i ≤ 2(uv)^{min(i,j)}` the sufficient condition is
`s_ii ≥ 2Σ_{j>i}|s_ij|`, and already row 1 fails (`Σ_{j>1}|s_1j| ≈ 0.053` versus
`s_11/2 = 0.0296`).  The bound is lossy because it discards `max(u,v)^{|i−j|}`,
which is small exactly where the negative coefficients live.  A sharper
pairing — or a certified two-dimensional argument that bypasses the reduction
entirely — is what remains.

Note the reduction is *not* needed if `(iii)` is attacked directly in two
variables: the three-regime scheme of this section would have to be run on
`(0,1)²`, where the only degeneracy is the corner `(α,β) → (0,0)` with margin
`ΛΛ′ − 1 ≈ (4/15)ε²`.


**The single-crossing lemma reduces to a rational inequality.**  Three steps.

*(i) The obstruction is not general.*  The diagonal reduction `N ≥ 0`, where

```
N := A(v)B(u)C(u) − A(u)B(v)C(v),   A = zĜ′, B = 1−Ĝ, C = Ĝ−Ĝ(t),  t = uv,
```

is **false for general laws** — `c = {1 ↦ 0.1, 2 ↦ 0.9}` gives `N < 0` at
`(u,v) = (0.9,0.3)` (80 violations among two-atom laws,
`numerics/p0_general_law_counterexample.py`).  So no argument that ignores the
weights can work.  It is also not termwise: symmetrising the cubic form over
index triples leaves 2964 of 3584 coefficients negative.

*(ii) `N` annihilates the geometric family, and our law is a geometric mixture.*
For `Ĝ_θ(z) = (1−θ)z/(1−θz)` one finds `N ≡ 0` identically (verified to 30
digits, every `θ`), exactly as for point masses.  And the mixing measure of our
law is explicit:

```
c_k = 2/((2k−1)(2k+1)) = ∫₀¹ x^{2k−2}(1−x²) dx = ∫₀¹ (1−θ)θ^{k−1} · dθ/(2√θ)
```

with `∫₀¹ dθ/(2√θ) = 1`: **`c` is the mixture of geometrics with density
`1/(2√θ)`**.

*(iii) Hence a kernel criterion.*  `A, B, C` are linear in the law, so
`N = ∭ K(θ₁,θ₂,θ₃) dμ³ = ∭ K_sym dμ³`, where

```
K = uv(1−u)(1−v)·(1−θ₁)(1−θ₃)/(1−θ₃uv) · [ 1/D₁ − 1/D₂ ]
D₁ = (1−θ₁v)²(1−θ₂u)(1−θ₃u),      D₂ = (1−θ₁u)²(1−θ₂v)(1−θ₃v)
```

and `K_sym` is the average over the six permutations.  `D₁, D₂` are symmetric in
`(θ₂,θ₃)`, so the six terms collapse to three:

```
K_sym = (uv(1−u)(1−v)/6)·Σ_i (1−θ_i)·S_{jk}·(D₂^{(i)} − D₁^{(i)})/(D₁^{(i)}D₂^{(i)})
S_{jk} = (1−θ_j)/(1−θ_j t) + (1−θ_k)/(1−θ_k t)
```

> **Kernel lemma.**  `K_sym ≥ 0` for `θ₁,θ₂,θ₃ ∈ (0,1)`, `1 > u ≥ v > 0`,
> with equality iff `θ₁ = θ₂ = θ₃`.

Given it, `N ≥ 0` for every geometric mixture, in particular ours — the diagonal
reduction — and with §7f all of `(iii)`.  Verified with **zero violations over
2401 points** (`numerics/p0_geometric_kernel.py`), the only near-zero values
sitting on the diagonal as predicted.  This is a **rational** inequality in five
variables: no transcendental functions remain, so after clearing the manifestly
positive denominators it is polynomial positivity on a box, where an SOS
certificate would finish it.

`K` itself is *not* signed — `(1−θ₁u)²/(1−θ₁v)² ≤ 1` fights
`(1−θ₂v)(1−θ₃v)/((1−θ₂u)(1−θ₃u)) ≥ 1` — so the symmetrisation is essential.


**Toward the kernel lemma: reduction, decomposition, and what fails.**

*Reduction to three variables.*  Dividing `K_sym` by its positive factors
(`P_i = a_ib_i`, `a_i = 1−θ_iu`, `b_i = 1−θ_iv`) and setting

```
r_i = a_i/b_i ∈ (0,1),   f(θ) = (1−θ)/(1−θu),   g(θ) = (1−θ)/(1−θt),   t = uv
λ_i = f(θ_i)·(g(θ_j) + g(θ_k))
```

the kernel lemma becomes exactly

```
(KL)      Σ_i λ_i · (r_i² − r_j r_k)  ≥  0 .
```

Equivalently, with `ν_i = λ_i/r_i`, `x_i = r_i³`, `ρ = r₁r₂r₃`, it says the
`ν`-weighted arithmetic mean of the `x_i` dominates their **unweighted**
geometric mean: `Σν_ix_i ≥ ρ·Σν_i`.  With equal weights that is AM–GM.

*A Schur-type decomposition.*  From
`r_i² − r_jr_k = ½[(r_i²−r_j²)+(r_i²−r_k²)] + ½(r_j−r_k)²`,

```
Σ_i λ_i(r_i² − r_jr_k) = ½ Σ_{i<l}(λ_i−λ_l)(r_i²−r_l²) + ½ Σ_{i<l} λ_m (r_i−r_l)²
```

(`m` the third index).  **The second sum is manifestly nonnegative** — it is the
slack the association arguments were missing.  The first is the Chebyshev term,
genuinely negative sometimes (784 of 4000 random cases), so a proof must let the
second absorb it.

*What does not work* (all checked, `numerics/p0_kernel_*.py`):

| attempt | outcome |
| --- | --- |
| general laws instead of ours | false — two-atom counterexample `{1:0.1, 2:0.9}` |
| termwise positivity of the cubic form | 2964 of 3584 symmetrised coefficients negative |
| Chebyshev association (`λ/r` monotone in `r`) | not monotone: 8542 of 11783 grid steps |
| pairwise version of the decomposition | 1604 of 4000 cases have a negative pair term |

The boundary case is safe: at `θ_m = 1` the third weight vanishes and (KL)
becomes `f_ig_l(r_i²−r_lr_m) + f_lg_i(r_l²−r_ir_m) ≥ 0`, verified over 3000
cases, minimum `4.2·10⁻⁷`.

*The certificate route.*  Clearing denominators gives an explicit polynomial `Q`
(`numerics/p0_kernel_polynomial.py`): **degree 22, 5923 monomials** in six
variables, identically zero on `A₁ = A₂ = A₃`, validated against `K_sym` to six
digits.  Substituting `A_i = 1−θ_i ≥ 0` and putting `(c,δ,v)` on the simplex
(`u = δ+v`, `1−u = c`) makes every building block have **nonnegative
coefficients**:

```
1−θ_i u = A_i u + c,    1−θ_i v = A_i v + c + δ,    1−θ_i t = A_i t + c + u(c+δ)
```

so the natural certificate is the ansatz `Q = Σ_{i<j}(A_i−A_j)²·M_{ij}` with the
`M_{ij}` nonneg-coefficient (permuted copies of one polynomial, by symmetry).
That is **linear programming, not an SDP** — but at degree 22 in six variables
the LP is large, and that is where this stands.


**The LP was run — and it is infeasible, for a structural reason.**

Ansatz `Q = Σ_{i<j}(A_i−A_j)²·M_{ij}` with `M_{ij}` in a nonnegative cone
(`numerics/p0_kernel_lp.py`):

| cone for `M_{ij}` | LP size | result |
| --- | --- | --- |
| monomials in `(A,c,δ,v)`, A-deg ≤ 8 | 25662 × 8645 | infeasible |
| Bernstein in `A_i,θ_i`, per-var degree `D = 3,4,5,6` | up to 59514 × 17836 | infeasible |
| ditto, times `(c+δ+v)^k`, `k = 1,2,4,6` | up to 68238 × 19278 | infeasible |

*The first row had to fail*, and the reason is instructive: `Q` is **negative
off the box** — at `A ≈ (5.97, 5.94, 3.31)`, `(c,δ,v) ≈ (0.11,0.22,0.67)` one
gets `Q ≈ −3103` (`numerics/p0_kernel_lp_obstruction.py`).  A nonneg-coefficient
certificate would force `Q ≥ 0` on the whole orthant `A ≥ 0`, so the upper
bounds `A_i ≤ 1` must enter — hence the Bernstein/Handelman rows.  Those fail
too, and not for lack of degree: `Q_hom` has per-variable A-degree exactly `4`,
well inside `D = 6`, and simplex degree elevation up to `k = 6` changes nothing.

**Conclusion: the certificate is not of diagonal Handelman type.**  A genuine
SOS/SDP with cross terms is needed — e.g. `Q = δᵀ M δ` for the difference vector
`δ = (A₁−A₂, A₂−A₃, A₃−A₁)` and a matrix `M` of polynomials that is PSD on the
box.  That is an SDP, and no SDP solver is available in this environment.

Two facts any certificate must respect, both found while running this:

* `Q ≥ 0` on the box × simplex is confirmed by global minimisation (min `0`, not
  merely sampling);
* besides the diagonal, `Q` vanishes on `{A_i = A_j = 0}` — i.e. `θ_i = θ_j = 1`,
  where the weights `f(1) = g(1) = 0` kill everything.  So the `M_{ij}` must
  vanish there too, which the LP cone can express but evidently cannot satisfy.

### 7f′. The comonotone reduction of the kernel lemma

After the SDP route closed (below), the kernel lemma was attacked *structurally*,
through `schur_decomposition`.  That produced a genuine simplification, and it is
now the recommended statement of the open problem.

**Setup.**  With `t = uv`, `A = 1−θ`, `a = 1−θu`, `b = 1−θv`, `w = 1−θt`, put

```
f(θ) = A/a ,   g(θ) = A/w ,   r(θ) = a/b ,   φ(θ) = g/f = a/w ,
S φ  = Σ_i φ(θ_i)·(r_i² − r_j r_k) ,          G = g(θ₁)+g(θ₂)+g(θ₃) .
```

All four of `f`, `g`, `f·g`, `φ`, `r` are **decreasing** on `θ ∈ (0,1)` (for
`0 < v ≤ u < 1`), each by the difference identities of §7f: e.g.
`f(θ₁)−f(θ₂) = (θ₂−θ₁)(1−u)/(a₁a₂)` and `r(θ₁)−r(θ₂) = (θ₂−θ₁)(u−v)/(b₁b₂)`.

**Reduction.**  The kernel weight is `λ_i = f(θ_i)·(G − g(θ_i))`, so

```
Σ_i λ_i (r_i² − r_j r_k)  =  G · S f  −  S (f·g) ,        (kernel_split)
```

and by comonotone Schur — in `schur_decomposition` the Chebyshev bracket is
termwise nonnegative once the weights are comonotone with `r`, the other bracket
being nonnegative outright — **both halves are separately nonnegative**:

```
S f ≥ 0        (kerSum_f_nonneg)
S (f·g) ≥ 0    (kerSum_fg_nonneg)
```

So the kernel lemma is exactly the **ratio bound**

```
S (f·g)  ≤  G · S f                                            (KL)
```

between two quantities already known to be nonnegative.  Equivalently, the sole
obstruction is the failure of `λ` itself to be comonotone with `r`:

```
λ_i − λ_l  =  g_m·(f_i − f_l)  +  f_i f_l·(φ_l − φ_i) ,
              ^ ≥ 0                ^ ≤ 0, the only negative term anywhere
```

with `f_i − f_l = (θ_l−θ_i)(1−u)/(a_i a_l)` and
`φ_i − φ_l = (θ_l−θ_i)·u(1−v)/(w_i w_l)` — the `P`/`N` pair of the pairwise
analysis, re-derived.

**All three `g`'s in `G` are needed** (`numerics/p0_kernel_comonotone.py`,
3·10⁵ samples): `S(f·g) ≤ g_max·S f` fails on 97% of samples (worst overshoot
2.99×) and `S(f·g) ≤ (g_max+g_mid)·S f` still fails on 31% (worst 1.50×), while
`S(f·g) ≤ G·S f` never fails.  So (KL) is sharp in each summand.

**Why the pairwise version fails, precisely.**  Writing the Schur decomposition
per pair, `Σ_i λ_i(r_i²−r_jr_k) = ½ Σ_{i<l} E_il` with
`E_il = C_il(P_m − N_il) + D_il`, `C, P, N, D ≥ 0`
(`numerics/p0_kernel_schur_struct.py`, 2·10⁴ samples):

* at most **one** of the three `E_il` is ever negative — counts `{0: 12491,
  1: 7509, 2: 0, 3: 0}`;
* the absorption always works, but with worst ratio
  `(Σ negative)/(Σ positive) = 0.975`.

Dropping the `D` terms is fatal (`numerics/p0_kernel_tightness.py`): the three
`D`-free absorptions overshoot by factors 160, 210, 238.

**Where it is tight, and why that is the whole difficulty.**  Global maximisation
of `(Σ neg)/(Σ pos)` returns `1.000000`, but at the corner `θ = (1,0,1)`, `u = 1`,
where every `P`, `N` and `λ` vanishes — a `0/0` artefact.  The genuine tight
regime, found by a focused scan, is `θ₁,θ₃ → 1`, `θ₂ → 0`, `u → 1`
(ratio `0.9955` at `θ = (0.9977, 0.0084, 0.9984)`, `u = 0.994`, `v = 0.534`).
Setting `A₁ = εp`, `A₂ = 1`, `A₃ = εq`, `c = 1−u = κε` gives the exact limits
(`numerics/p0_kernel_corner_limit.py`, verified to 6 digits at `ε = 10⁻⁶`)

```
E₁₂ → −[p/(p+κ) − q/(q+κ)] ,   E₂₃ → +[p/(p+κ) − q/(q+κ)] ,   E₁₃ = O(ε²) ,
```

i.e. `E₁₂ + E₂₃ → 0` **identically**: the leading orders cancel and positivity is
decided at order `ε`.  In this limit `C_il N_il → f_i` and `D_il → λ_m → f_m`, so
the cancellation is exactly `f₁ − f₃` against `f₃ − f₁`.  Consequently the
pairwise grouping is the wrong grouping near this corner; a proof must either
expand there or use a grouping that respects the cancellation.  The direct
regrouping `Σ_{i<l}(g_l f_i c_i + g_i f_l c_l)` is *worse* — it has a negative
member on 100% of samples, two of them on 68% (`numerics/p0_kernel_pairing.py`).

**Status.**  (KL) in the form `S(f·g) ≤ G·S f` is the single remaining gap in the
`p = 0` program.  Its two sides are now theorems in Lean, as is every algebraic
identity feeding it; what is missing is one inequality between them, known to be
asymptotically tight in the corner above (slack `Θ(ε)`).

### 7f″. The face `u = 1`, and the face derivative — both settled

Expanding at the corner of §7f′ turned out to expose something exact and much
stronger than a corner statement.

**The kernel vanishes on the whole face `u = 1`.**  At `u = 1`, `a_i = 1−θ_i =
A_i`, so `f ≡ 1`; and `w_i = 1−θ_i v = b_i`, so `g_i = A_i/b_i = r_i`.  Hence

```
kernel|_{u=1} = Σ_i (r_j + r_k)(r_i² − r_j r_k) ≡ 0        (kernel_vanishes_on_face)
```

— the two symmetric sums cancel term by term.  This is the source of *every*
near-tight measurement in §7f′: the corner `θ₁,θ₃→1, θ₂→0, u→1` merely sits on
this face, and the "exact leading-order cancellation" found there is the face
identity in disguise.  It also explains why no global certificate could have a
uniform margin.

**The face derivative is nonnegative, with a Pólya certificate.**  With
`s_i = θ_i/b_i` the face carries the affine relation

```
r_i + (1−v)·s_i = 1 ,
```

so `s_i = (1−r_i)/κ`, `κ = 1−v`, and the entire derivative collapses to a
polynomial in `(r₁,r₂,r₃,κ)` with `r_i ∈ (0,1)`.  Using `f′_i = −s_i/r_i`,
`g′_i = −v r_i s_i`, `r′_i = s_i` (all at `c = 0`, `c = 1−u`):

```
κ·r₁r₂r₃ · ∂(kernel)/∂c |_{c=0}  =  κ·faceX(r) + faceY(r)
faceX = r₁r₂r₃·[ r₁r₂(r₁−r₂)² + r₁r₃(r₁−r₃)² + r₂r₃(r₂−r₃)² ]
faceY = an 18-term degree-7 polynomial, symmetric, vanishing on the diagonal
```

`faceX ≥ 0` is immediate.  `faceY ≥ 0` on `[0,1]³` but **not** off it (it reaches
`−164` on `(0,3)³`), so the box is essential — and the certificate is Pólya's in
the ordered simplex coordinates

```
w = r₃ ,  q = r₂ − r₃ ,  p = r₁ − r₂ ,  m = 1 − r₁ ,     w+q+p+m = 1 :
```

there `faceY` is a combination of **53 monomials with positive integer
coefficients** (min 1, max 57), *with no degree elevation*.  Both statements are
now Lean theorems: `faceX_nonneg`, `faceY_nonneg`.

So the kernel is zero on the degenerate face and enters `u < 1` with a
nonnegative slope everywhere on it.  The boundary layer that defeated every
global certificate attempt (LP, Handelman, Putinar, δ-module SOS) is settled.

**Two routes that died on the way** (`numerics/p0_kernel_monotone.py`,
`numerics/p0_kernel_corner_coeff.py`):

* monotonicity: `∂KL/∂v ≤ 0` fails on 12% of samples, `∂KL/∂u ≥ 0` on 17%,
  "increasing in the `θ`-spread" on 1.2% — so the `v = u` zero cannot be
  integrated up;
* `Σ D ≥ Σ C·N` (the `c`-free absorption suggested by the corner shape) fails on
  67% of samples: the `C·P` terms are indispensable away from the face.

**What is left.**  Nothing: §7f‴ settles the kernel lemma outright, by carrying
the ordered-simplex idea of this section over to the full five-variable
problem.

### 7f‴. The kernel lemma is **proved** — a Pólya certificate on the ordered bi-simplex

The face analysis of §7f″ says the ordering is what makes a nonnegative-coefficient
certificate exist (the unordered symmetric Handelman LP was infeasible; the
ordered Pólya one succeeded at zero elevation).  Applying the same idea to the
whole problem closes it.

**Setup.**  Clear the manifestly positive denominators: with
`A_i = 1−θ_i`, `a_i = 1−θ_iu`, `b_i = 1−θ_iv`, `w_i = 1−θ_iuv`,

```
kerQ  :=  (kernel) · ∏a_i · ∏w_i · ∏b_i²
       =  Σ_i A_i·a_j a_k·(A_j w_i w_k + A_k w_i w_j)·(a_i²b_j²b_k² − a_j a_k b_i²b_j b_k)
```

a polynomial of total degree 21 in `(θ₁,θ₂,θ₃,u,v)` with 1136 monomials, integer
coefficients, per-variable degrees `(4,4,4,6,6)`.  Since the kernel is symmetric
in the `θ_i`, assume `θ₁ ≤ θ₂ ≤ θ₃`, and use the **ordered bi-simplex
coordinates**

```
t₁ = θ₁ ,  t₂ = θ₂−θ₁ ,  t₃ = θ₃−θ₂ ,  t₄ = 1−θ₃          (t_i ≥ 0, Σt = 1)
s₁ = v  ,  s₂ = u−v  ,  s₃ = 1−u                          (s_i ≥ 0, Σs = 1)
```

which parametrise exactly `0 ≤ θ₁ ≤ θ₂ ≤ θ₃ ≤ 1` and `0 ≤ v ≤ u ≤ 1`.

**The certificate.**  In these coordinates `kerQ` has θ-block degree `10` and
`uv`-block degree `11`; bihomogenising to bidegree `(10,11)` gives

> `kerQ = Σ_α c_α · t₁^{α₁}t₂^{α₂}t₃^{α₃}t₄^{α₄} · s₁^{β₁}s₂^{β₂}s₃^{β₃}`
> with **11385 monomials and every `c_α` a positive integer** (min 1, max
> 2 394 983), **no degree elevation**.

Hence `kerQ ≥ 0`, hence the kernel lemma.  ∎

**Why it works, and why the earlier attempts could not.**  In the raw monomial
basis 870 of `kerQ`'s 1743 coefficients are negative, so no unordered
nonneg-coefficient certificate exists — which is exactly what the LP runs
reported.  The ordering is not a convenience; it is the whole content.  The two
zero loci of `kerQ` — the diagonal `θ₁=θ₂=θ₃` (i.e. `t₂=t₃=0`) and the face
`u=1` (i.e. `s₃=0`) of §7f″ — are *faces* of the product of simplices, which is
the situation where Pólya-type certificates survive vanishing.  In the box
coordinates used before, the diagonal is an interior set and every certificate
was blocked.

**Verification** (`numerics/p0_kernel_polya.py`, `..._verify.py`,
`..._identity.py`), all in exact integer/rational arithmetic:

* `kerQ` reproduces the kernel times the denominator (float check, `1.4e−16`);
* the expansion has 11385 monomials, zero negative coefficients;
* the identity `kerQ = Σ c_α ⋯` holds exactly at 200 random ordered rational
  points, and at 60 *unconstrained* rational points once `t₄`, `s₃` are written
  as `1−t₁−t₂−t₃`, `1−s₁−s₂` — i.e. it is a genuine polynomial identity, which
  is what the Lean proof checks.

**Consequence.**  With the kernel lemma, `N ≥ 0` for every geometric mixture,
hence the diagonal reduction, hence — with the one-variable core already proved
in §7f — the saddle inequality **(iii) in full**.  That was the last open
analytic link in the `p = 0` chain for Conjecture 1.

### 7f⁗. Formalising the certificate: reflection beats `ring`

The certificate of §7f‴ can be handed to Lean in two ways, and the difference is
hours versus minutes.

**The direct way (attempted, abandoned; no such file is in the repository).**
Write the identity
`kerQ = Σ c_α · monomial_α` out in full and call `ring`.  The file is 900 KB.
Two costs, both large: Lean must *parse and elaborate* the term — every numeral
an `OfNat ℝ`, every `*` an `HMul` application, some 10⁶ `Expr` nodes — and then
`ring` must build a proof term for the whole normalisation.  Measured: >3 h and
21 GB, still running.  Choosing the cheapest pair of eliminated coordinates
(`t₁,s₁` rather than `t₄,s₃`) cuts the monomial products from 6.3M to 2.2M, but
the floor is set by `ring`'s throughput and by the expansion of `kerQ` itself
(6817 monomials in those coordinates), so no choice of certificate makes this
fast.

**The reflection way (`Reflect.lean` + `KernelCertFast.lean`): 142 s.**  Nothing
large is written down at all.  `Reflect.lean` sets up

```
M7    -- a seven-slot exponent record (fixed arity: no length side conditions)
Poly  := List (M7 × ℤ)          -- not assumed sorted or collected
PE    -- syntax tree: var, int, add, sub, mul, pow
PE.norm : PE → Poly             -- expansion, collecting after every product
PE.eval : PE → (Fin 7 → ℝ) → ℝ
```

with the soundness theorem `Poly.eval e.norm ρ = e.eval ρ` (an induction over
`PE`, proved once) and `PE.eval_nonneg_of_norm`: if every coefficient of
`e.norm` is nonnegative then `e.eval ρ ≥ 0` for nonnegative `ρ`.  Collection is
what keeps this feasible — `Poly.mul` multiplies out pairwise, so without it the
term count is the *product* of the input counts; `Poly.collect` sorts by a
packed key and merges adjacent equal monomials, its soundness needing only
permutation-invariance of a list sum, so the key need not be injective and the
fuel-based merge is safe even if the fuel runs out.

Then `KernelCertFast.lean` writes the cleared kernel as a **small syntax tree**
`kerQPE` (the same product form as always, thirty lines), and Lean *computes*
its expansion: **24129 monomials, every coefficient nonnegative** — an
independent reconstruction of the certificate, by Lean rather than by the Python
of `numerics/p0_kernel_polya.py`.  `eval_kerQPE` holds by `rfl`: the tree
unfolds definitionally to the product form, so no tactic ever normalises a large
expression.

Cost of the check: one `native_decide`, i.e. compiled integer arithmetic, which
adds the `native_decide` axiom to that theorem's axioms.  The soundness layer itself,
and everything else in the development, stays at
`[propext, Classical.choice, Quot.sound]`.  The `ring` route never finished, so
there is **no** axiom-clean proof of `kerQPE_allNonneg` in the repository; this
is the one place where the development leaves the three standard axioms.

The general lesson, worth keeping: for a certificate of this size the bottleneck
is not the mathematics and not even the tactic, it is *having the certificate in
the source at all*.  Encode the polynomial as data and compute it.

### 7f⁶. (C) in Lean: the branch gap is the wrong target

`(C)` — the BSC pair is not a maximiser — has two possible discharges, and the
Lean work made the choice clear.

**The branch route, reduced.**  `Conj12.lean` now proves
`bscNotMax_of_branchGap : BranchGap → BSCNotMax`, where

```
BranchGap :  f_e(s·t) < zsValue a d     whenever  f_e(s) ≤ zsRate a  and  f_e(t) ≤ zsRate d.
```

The witness is the Z/S pair itself: `zChan` is now a `Chan` with
`zChan_rate : I(U;X) = zsRate a` and
`zChan_sChan_value : I(U;V) = zsValue a d` (the latter uses the kernel identity
in its `…_of_nonneg` form — the Z/S pair is exactly the configuration with the
degenerate cell `s·t = −1`).  Note the statement of `BranchGap` avoids `f_e⁻¹`
entirely: the rate constraints enter as inequalities and monotonicity does the
rest.  That is the formalisation-friendly form of the branch comparison.

**But `BranchGap` is unproved mathematics, and the obvious bound is useless.**
The natural tool is `f_e(st) ≤ 2f_e(s)f_e(t)` (sharp as `s,t → 0`; proof: `f_e(x)/x²`
is increasing, so `f_e(st) ≤ t²f_e(s)`, and `f_e(t) ≥ t²/2`).  Combined with
`2·zsRate a·zsRate d < zsValue a d` it would give `BranchGap` — but that second
inequality holds on **1% of the square** (6 of 529 grid points, all at tiny
rates), the ratio `2·zsRate·zsRate / zsValue` reaching `1.376` at `a,d ≈ 0.98`.
So the product bound is far too lossy except in the small-rate corner, and
formalising it buys nothing.

**Conclusion: take the (iii) route for `(C)`.**  §7f/§7f‴ *prove* (iii) — the
one-variable core in three regimes plus the diagonal reduction via the kernel
lemma.  The branch comparison, by contrast, has no proof at all: it is
numerically solid but tight at the full-rate corner (§7f′ measurements), and
nothing in the analysis suggests an easy argument there.  For `(C)` in Lean the
remaining work is therefore

1. the second-order link — `saddle ⟺ ΛΛ′ > 1` — the Hessian of the two-variable
   value function at the symmetric point; and
2. formalising (iii)'s one-variable core, whose interval sweep now has a
   template in `Reflect.lean`: encode the computation as data, prove one
   soundness lemma, discharge by computation.

`BranchGap` stays in the file as the alternative discharge, clearly marked as
unproved.

### 7f⁷. The skew route does not bypass the second order

`SignFlip.lean` proves that asymmetry pays: `Ω > 0` exactly when the two skews
oppose.  That suggests a cheap proof of `(C)` — perturb the BSC pair to opposite
skews and gain `Ω > 0`.  It does not work, for a reason worth recording.

Perturbing the symmetric pair `(α,α)`, `(β,β)` to atoms `(α+ε, α−ε)` and
`(β−ε, β+ε)` at `δ = 1` (`numerics/p0_skew.py`):

```
   eps      value change     rate change      change/eps²
  1e-2     −1.991e-5        −4.320e-5        −0.1991 / −0.4320
  1e-4     −1.991e-9        −4.319e-9        −0.1991 / −0.4319
```

Both the value **and** the rate fall, and both at order `ε²`.  So the skewed pair
is feasible but *worse* on its own; what it buys is slack in the rate budget,
`0.432ε²`, against a value loss of `0.199ε²`.  Whether the trade is profitable
is exactly the question of whether the freed rate can be re-spent for more than
it cost — i.e. a comparison of second-order coefficients, which is the Hessian
criterion `ΛΛ′ > 1`, which is (iii).

Two consequences.  The sign flip organises the second-order computation but
cannot replace it: there is no first-order gain to exploit, because the
symmetric point is stationary in the skew directions by symmetry.  And the
`δ < 1` hypothesis carried by `omegaTwoPoint_pos`/`_neg` — which at `p = 0`
would need a limiting argument — is moot here, since the route is blocked
anyway.

So `(C)` in Lean requires the constrained second-order analysis: a family with
the rate held exactly constant (implicit function theorem), the value's Hessian
at the symmetric point, and its determinant identified with `1 − ΛΛ′`.  Together
with (iii)'s one-variable core, that is the whole of `(C)`.

### 7f⁸. The interval layer, and why the naive extension is not enough

`Interval.lean` (~600 lines, `sorry`-free, axiom-clean) is the computational
foundation for (iii)'s core in Lean:

* `Iv` over `ℚ` with `+ − × ÷`, `scale`, `isPos`;
* `outward` rounding to a `1/m` grid — **essential**: without it each squaring
  squares the denominator and endpoints reach thousands of digits;
* `exp`: Taylor for `|q| ≤ 1` (`Real.exp_bound`), argument reduction by `2^k`,
  rounded repeated squaring, then a monotone interval extension;
* `cosh`, `sinh`, `tanh`; `log` **by inversion** — no series, just witnesses
  `exp p ≤ z ≤ exp q` verified through the `exp` enclosures;
* `FI`/`FI2`, extensions of `F(θ) = 1/log Z − 1/(Z−1) − tanh θ/(2θ)`;
* `Cell`, `cellOk`, `tiles`, and **`sweep_sound`**: cells that tile `[A,B]` and
  pass the decidable test give `F > 0` on `[A,B]`, with no Lipschitz constants
  and no derivative bounds.

It works: `cellOk ⟨1, 1.001, 1.3249, 1.3270⟩ 4 25 10¹² = true`, certifying
`F ≥ 0.0102` there.  A practical wrinkle found on the way: the `log` witnesses
must lie strictly *outside* the true range, since the check compares enclosure
against enclosure.

**But the naive extension cannot cover the hard end.**  `F` is a difference of
large nearly-equal terms — at `θ = 0.45`, `2.779 − 2.309 − 0.469 = 0.0013` — and
interval arithmetic cannot see the cancellation, so the width of the enclosure
is the *sum* of the term variations, about `22w` for a cell of width `w`.
Positivity then needs `w ≲ 5·10⁻⁵` at the left end, i.e. of order `10⁵` cells.
Rewriting `1/log Z − 1/(Z−1)` as the single fraction
`((Z−1) − log Z)/(log Z·(Z−1))` (`FI2`) removes one cancellation but not the
dependency between `Z−1` and `log Z`, whose widths still add: measured
`FI2.lo = −0.0022` on `[0.45, 0.4502]`.

**The fix is the mean-value (centred) form**, and it is what makes the Python
proof of §7f cheap: `F(θ) ∈ F(c) ± L·w/2` with `L` an enclosure of `|F′|` on the
cell.  `F′` is *tiny* — `F` moves from `0.0013` to `0.0018` across `[0.45,0.5]`
— so the error is about `0.005w` instead of `22w`, and `[0.45,3]` needs of order
`10²` cells rather than `10⁵`.  Point evaluation carries no cell-width
dependency at all, so its accuracy is set only by the `exp`/`log` precision,
which is cheap to raise.  The missing piece is therefore an interval extension
of `F′`, mechanical from the parts already built (`Z′ = 2 sinh 2θ`, and so on).

### 7f⁹. The centred form works: `F′` enclosed, hard end certified

`CoreDeriv.lean` supplies what §7f⁸ identified as missing.

**The derivative.**  `F` is restated with `⁻¹` and `tanh = sinh/cosh` so the
composition rules apply directly (Mathlib has no `Real.hasDerivAt_tanh`), and
`hasDerivAt_F` assembles `F′` from `HasDerivAt.cosh`, `.log`, `.inv`, `.div`.
`F_eq` bridges to the sweep's `tanh` form.

**The mean-value step.**  `F_pos_of_center`: if `|F′| ≤ L` on `[a,b]` and
`L·(b−a) < F(c)` for a single point `c`, then `F > 0` on the whole cell.  This
is what the naive extension could not do — it converts cell positivity into one
*point* evaluation plus a derivative bound.

**The enclosure of `F′`.**  `FpI`/`mem_FpI`, built from the same `Interval.lean`
pieces.  `F′` cancels too — at `θ = 0.45` it is `−11.07 + 10.94 + 0.13 ≈ 0.01` —
so its enclosure is loose, but that does not matter: `L` only multiplies the
cell width.  And the looseness shrinks fast with the cell: `absBound` is `1.59`
on `[0.45,0.46]` but `0.0916` on `[0.45,0.4505]`.

**Measured at the hard end** (`[0.45, 0.4505]`, `k=4`, `n=25`, grid `10⁻¹²`):

```
L = absBound (FpI …)                    = 0.0916
point enclosure  F(c).lo                = 0.0012631      (true F(c) = 0.0013044)
test   L·(b−a) = 4.6e−5  <  0.0012631   ✓  margin ≈ 27×
```

Empirically `L ≈ 180w`, so the test needs `180w² < F`, giving `w ≈ 2·10⁻³` at
the hard end and **of order 1300 cells for `[0.45,3]`** — the same order as the
6243 Lipschitz steps of the Python proof, and for the same reason: both bound
`F′` rather than the individual terms.

What remains for regime 2: the combined per-cell test (`FpI` side conditions,
the point evaluation `FI2 ⟨c,c⟩`, and the margin check) as one decidable
conjunction, its soundness via `F_pos_of_center`, and the generated cell list.

### 7f¹⁰. Regime 2 of (iii)'s core is a Lean theorem

```
core_pos_regime2 : ∀ θ : ℝ, (45/100 : ℚ) ≤ θ → θ ≤ 3 → 0 < F θ
```

650 cells tiling `[0.45, 3]`, each discharged by the centred test `cellOkC` in
exact rational arithmetic, the tiling by `tilesC`, assembled by `sweepC_sound`.
Whole file builds in **16 s**.

The chain, all proved: `hasDerivAt_F` → `F_pos_of_center` (mean value) →
`fp_sound` (Lipschitz bound from `mem_FpI`) and `f_sound` (point enclosure from
`mem_FI2`) → `pos_of_cellOkC` → `sweepC_sound`.  Only the two cell checks are
computational (`native_decide`); every structural lemma is axiom-clean.

650 cells against the Python proof's 6243 Lipschitz steps: the centred form with
an *enclosure-derived* `L` per cell beats a single global Lipschitz constant.

Two practical lessons, both of which cost a debugging cycle:

* the `log` witnesses must bracket the **enclosure** of `log(cosh 2θ)`, not its
  true range — `coshI` builds its lower bound as `(e^{2a} + e^{−2b})/2`, pairing
  the two anti-correlated terms at opposite endpoints, so the enclosure is
  strictly wider than the truth and witnesses read off the truth fail;
* `maxRecDepth` must be raised for a list literal of this size.

Cell generator: `numerics/p0_gen_cells.py`, width `10⁻³` below `0.6`, coarsening
to `10⁻²` above `2`.

Remaining for (iii)'s core: the regimes `(0, 0.45]` (Taylor coefficients plus a
Cauchy tail bound) and `[3, ∞)` (elementary exponential bounds), both analytic
rather than computational.  Remaining for `(C)`: those, plus the second-order
link and the diagonal reduction.

### 7f¹¹. Regime 3 done; regime 1 vanishes to ninth order

**Regime 3 (`θ ≥ 3`) is a Lean theorem, and axiom-clean** — no `native_decide`.
`core_pos_regime3`, from `log cosh u = u − log 2 + log(1+e^{−2u})`, `tanh ≤ 1`,
`1/(Z−1) ≤ 4e^{−2θ}`, and `16θ²e^{−2θ} < 0.69` (the last via `θ² ≤ 9e^{θ−3}`).
Supporting: `cosh_eq_exp_mul`, `log_cosh_eq`, `exp_six_gt` (`e⁶ > 250`, proved as
`(e^{1/8})^{48} ≥ (9/8)^{48} ≈ 279` — the naive `e³ ≥ 4` gives only `e⁶ ≥ 16`),
`sq_le_exp`, `exp_dominates`, `inv_cosh_sub_one_le`.

**Regime 1 (`0 < θ ≤ 0.45`) is much harder than the notes implied.**  Clearing
denominators, the core is `N(θ) > 0` with

```
N(θ) = 2θ(Z−1) − 2θ·log Z − tanh θ·log Z·(Z−1),      Z = cosh 2θ
```

and measurement gives, unambiguously,

```
N(θ) ~ (16/45)·θ⁹        (log-log slope 9.0 over four decades; N/θ⁹ → 0.3555555…)
```

The inequality is tight to **ninth order** at `0`.  That kills every cheap
route, and each failure is quantitative:

* the interval sweep cannot reach `0`: the margin is `Θ(θ⁹)` while the
  enclosures carry `Θ(θ²)` relative error, so the required cell width collapses
  like `θ³` and `∫dθ/θ³` diverges;
* the trapezoid bound `log(1+x) ≤ x(x+2)/(2(x+1))` (3rd-order accurate) reduces
  the claim to `sinh θ·cosh θ < θ` — **false**;
* the Padé bound `log(1+x) ≤ x(6+x)/(6+4x)` (4th-order) reduces it to
  `3 sinh θ + sinh³θ < 3θ cosh θ` — **false**, by `0.4θ⁵`;
* truncating the log series needs about **eleven** terms at `θ = 0.45`, since
  `x = 2sinh²(0.45) = 0.433` and the Mathlib remainder `x^{n+1}/(1−x)` must fall
  below `N/(2θ) = 2.0·10⁻⁴`.

So regime 1 needs what the Python proof used: exact Taylor coefficients of `N`
to high order plus a rigorous tail bound.  Two formalisation routes, both real
work:

1. *real-variable*: bound `log(1+x)` by an alternating truncation (Mathlib's
   `abs_log_sub_add_sum_range_le`) and `sinh`/`cosh` by truncations with
   remainders, reducing to positivity of an explicit rational polynomial of
   degree ≈ 30 on `(0, 0.45]` — which could then be attacked by the ordered
   simplex/Pólya trick of §7f‴ after factoring out `θ⁹`;
2. *complex-analytic*: Cauchy estimates on `|θ| = 0.75`, as in the Python proof.

Route 1 keeps everything real and reuses machinery already in the project; it is
the one to try.

### 7f¹². Regime 1, and the one-variable core on all of `(0,∞)`

`Regime1.lean` closes the last regime.  The log-free reduction of §7f¹¹ says

```
F(θ) > 0   ⟺   Z < exp y ,      Z = cosh 2θ ,   y = 2θ(Z−1)/W ,
W = 2θ + tanh θ·(Z−1)
```

and on `(0,0.45]` the fourth partial sum of `exp y` already suffices
(`F_pos_of_exp_bound`).  With `s = sinh θ`, `c = cosh θ`, `a = θc`, `D = a + s³`
one has `y = 2as²/D`, and the required bound clears to the polynomial inequality

```
3s(a+s³)³  <  3a²(a+s³)² + 2a³s²(a+s³) + a⁴s⁴                       (ALG)
```

(`alg_ineq`).  Substituting the degree-5/4 Taylor envelopes of `sinh`/`cosh`
with explicit remainder `E` (monotone substitution, `gcongr`), the gap of (ALG)
is `θ⁸ · Q(θ)` with `Q` an explicit 53-monomial polynomial of degree 60,
`Q(0) = 4/15`; `Qpoly_pos` bounds each of the 52 non-constant terms on
`(0,0.45]` and `linarith` closes it — total negative mass `0.0191` against
`q₀ = 0.2667`.  Hence `core_pos_regime1`, **axiom-clean** (no `native_decide`).

`CorePos.lean` glues the three regimes:

> **`core_pos`** — for every `θ > 0`,
> `1/log(cosh 2θ) − 1/(cosh 2θ − 1) − tanh θ/(2θ) > 0`.

Its only non-standard axiom is the `native_decide` axiom, inherited from regime 2's
650-cell interval sweep.

### 7f¹³. The diagonal case of (iii), by exact algebra

`Diagonal.lean`.  Writing `y = tanh θ`, `Z = cosh 2θ`, `S = sinh 2θ`,
`L = log Z`, the three identities

```
g(tanh θ) = 2θ/S ,      g(tanh²θ) = 2ZL/S² ,      tanh²θ = (Z−1)²/S²
```

(the middle one from `artanh(tanh²θ) = ½ log cosh 2θ`, itself from
`(1+tanh²θ)/(1−tanh²θ) = cosh 2θ`) turn the diagonal case of (iii) into

```
diag · S⁴ = 2 Z S · N(θ) ,      N(θ) = 2θ(Z−1)·L·F(θ) ,
diag = (1 − g(y²))·g(y) − y²·(g(y²) − g(y)) .
```

So `diag_pos` is a two-line consequence of `core_pos`.  No new analysis.

### 7f¹⁴. `KernelLemma` is a theorem, not a `Prop`

`KernelBridge.lean` connects the reflection certificate to the kernel sum.  The
obstacle was that `kerQR = kernelSum · kernelDen` is a degree-21 identity in five
variables: `ring` times out at 200 000 heartbeats.  The fix is the same one that
made the certificate itself cheap — **do the algebra in abstract letters**.  With
`Aᵢ, aᵢ, bᵢ, wᵢ` opaque, `kernel_clear_abstract` is a few dozen monomials and
`field_simp; ring` closes it instantly; the `θ`-dependence is then reinstated by
`simp only` rewrites of the twelve atoms, which never expand anything.

With the ordering removed by the symmetry of `kernelSum` (six cases), this gives

* `kernelSum_nonneg` — the kernel lemma for `0 ≤ θᵢ ≤ 1`, `0 ≤ v ≤ u < 1`;
* `kernelLemma_holds : KernelLemma` — the `Prop` of `KernelAlgebra.lean`
  discharged.

### 7f¹⁵. The mixture representation, and the diagonal reduction in Lean

`MixtureRep.lean`.  Substituting `θ = s²` turns the mixing measure `dθ/(2√θ)`
into Lebesgue measure on `[0,1]`, and all three functionals become elementary
antiderivatives:

```
g(α)   = ∫₀¹ (1−α²)/(1−s²α²) ds                     primitive (1−α²)artanh(sα)/α
1−g(α) = ∫₀¹ (1−s²)α²/(1−s²α²) ds                   primitive s − (1−α²)artanh(sα)/α
A(α)   = ∫₀¹ α²(1−s²)/(1−s²α²)² ds                  primitive
         (1+α²)artanh(sα)/(2α) − s(1−α²)/(2(1−s²α²))
       = ((1+α²)artanh α − α)/(2α)  =  −α·g′(α)/2 .
```

`DiagReduction.lean` then proves `N ≥ 0` **without any Fubini**.  The point is
that a product of three one-dimensional integrals equals the iterated triple
integral of the product term by `integral_const_mul` alone (`integral3_sum`,
stated for a finite sum of product terms).  Consequently:

* each of the six permutations of the three dummy variables gives the *same*
  value, so `∭ Σ_σ P∘σ = 6N` — the permutation sum costs nothing;
* the *integrand* `Σ_σ P∘σ` is symmetric, and `sym_pointwise` identifies it with
  `uv(1−u)(1−v)/(a₁a₂a₃) · kernelSum`, again by an abstract-letters
  `field_simp; ring` after `cIf_closed` puts the `C`-integrand in product form;
* pointwise nonnegativity is `kernelSum_nonneg`, and three nested
  `intervalIntegral.integral_nonneg` finish.

> **`Nfun_nonneg`** — `0 ≤ A(β)B(α)C(α) − A(α)B(β)C(β)` for `0 < β ≤ α < 1`.

### 7f¹⁶. **(iii) is a Lean theorem**

`SaddleIII.lean`.  Two more ingredients:

* `hasDerivAt_gFun : g′(y) = −2A(y)/y`, hence `gFun_strictAntiOn` on `(0,1)`;
* along the hyperbola `αβ = x`, with `β = x/α`,

  ```
  R(α) = C(α)C(β)/(B(α)B(β)) ,
  R′(α) = −(2g(x)/α)·N(α,β)/(B(α)B(β))²
  ```

  — the clean form comes from `B + C = g(x)` being *constant* along the
  hyperbola, which collapses the quotient-rule expansion exactly onto `N`.

By `Nfun_nonneg`, `R′ ≤ 0`, so `R` is antitone on `[√x, 1)`
(`Rat_antitoneOn`): **the value is maximal on the diagonal**.  On the diagonal
`diag_pos` gives `(g(x)−g(y))/g(y) < (1−g(x))/x`, and squaring finishes:

> **`saddle_iii`** — for `α,β ∈ (0,1)` and `x = αβ`,
> ```
> x²·(g(x)−g(α))(g(x)−g(β))  <  (1 − g(x))²·g(α)g(β) .
> ```

Axioms: `propext, Classical.choice, Quot.sound` plus the `native_decide` axiom from the
two computational certificates (the Pólya expansion and the regime-2 sweep).
Zero `sorry`s.

**What this closes.**  (iii) was the last *open* analytic statement in the `p=0`
chain: §7f left the diagonal reduction unproved, §7f‴ proved it on paper via the
kernel lemma, and the above formalises both halves.  What remains for
Conjecture 1 at `p = 0` is not analysis but the two structural items: `(B)`
`InteriorIsBSC` and the second-order link of `(C)` (§7f⁶–§7f⁷).

### 7c⁵. What of all this is in Lean

`KernelAlgebra.lean` and the additions to `PZero.lean` / `BiasCoords.lean` /
`BestResponse.lean` close the mechanical parts of §7:

* `artanh_edge` — the **boundary case of (iii)**, `β < artanh β(1−β²/3)`, proved
  from `artanh_mul_lt` by the derivative `(2β/3)[β/(1−β²) − artanh β] > 0`;
* `mutualInfo_jointUV_eq_kernel_sum_of_nonneg` — the kernel identity with
  `0 ≤ 1+δst` instead of `0 <`, so the **impossible cell** is covered; both
  best-response certificates now carry the weaker hypothesis;
* `sChan`, `marg₂_sChan`, `biasOfSnd_sChan`, `mutualInfo_le_of_sChan` — the
  S-channel as a `Chan`, and the certificate turned into a bound on `I(U;V)`
  for **arbitrary** binary `cL`: at `p = 0`, `I(U;X) ≤ Cu` implies
  `I(U;V) ≤ λ₀ + λ₂·Cu`.  This is the plumbing that was flagged as missing;
* `schur_decomposition`, `cube_sum_ge_three_mul`, `rFun_sub`, `fFun'_sub`,
  `fg_cross` — the algebra of the diagonal reduction;
* `geometric_kernel_zero` — the kernel form vanishes on every geometric law;
* `kernel_false_for_general_law` — the two-atom counterexample, so the
  "no weight-blind argument" claim is now a theorem, not an observation;
* `two_mul_log_two_sq_lt_one` — the extremal constant `2log²2 < 1` of the
  branch-comparison route;
* `kernel_nonneg_of_comonotone`, `comonotone_of_decreasing`, `mul_comonotone`,
  `kernel_split`, `kerSum_f_nonneg`, `kerSum_fg_nonneg` — the comonotone
  reduction of §7f′: the kernel splits as `G·S f − S(f·g)` and **both halves are
  nonnegative**, so the open part is only the ratio bound `S(f·g) ≤ G·S f`.

`KernelLemma` and `BranchComparison` are stated as `Prop`s, never assumed.


**The SDP was run too — also infeasible, at every ansatz tried.**  With cvxpy
(SCS + CLARABEL) available, the SOS route was attempted properly
(`numerics/p0_kernel_sos.py`, harness self-test in
`numerics/p0_kernel_sos_selftest.py`).

Direct SOS on the full five-variable `Q` is hopeless — degree 22 needs
degree-11 multipliers, a Gram matrix of size `C(17,6) ≈ 12 400`.  So the tests
were run at **fixed rational `(u,v)`**, where `Q` is degree 10 in
`(A₁,A₂,A₃)` and every SDP is small:

| ansatz | result |
| --- | --- |
| plain Putinar `σ₀ + Σ A_k σ_k + Σ (1−A_k) σ_k′` | infeasible |
| `Σ_{i<j}(A_i−A_j)²·[SOS + box·SOS]` | infeasible |
| `Σ_{i<j}A_iA_j(A_i−A_j)²·[SOS + box·SOS]` (respects both zero loci) | infeasible |
| **δ-module SOS with cross terms**, `h = 3` and `h = 4` | infeasible |

The harness is validated: it returns `optimal` on constructed members of the
same cones, including a degree-10 instance.  One run reported
`optimal_inaccurate`, but tightening the tolerance turned it into `infeasible`
— it was numerical noise, not a certificate.

The modelling lesson worth keeping: `Σ(A_i−A_j)²σ_{ij}` captures only the
*diagonal* of a matrix certificate.  `Q` vanishes to order two on the
codimension-2 line `A₁=A₂=A₃`, so the correct object is `Q = δᵀMδ` with `δ` the
difference vector and `M` a polynomial matrix PSD on the box — i.e. an SOS in
the **module generated by the differences**, cross terms included.  That is the
last row above, and it fails too at these degrees.

So: no low-degree SOS certificate exists, even pointwise in `(u,v)`.  What
remains is higher degree (Putinar degrees blow up when the zero set is
degenerate, and here there are two: the interior diagonal and the three edges
`A_i = A_j = 0`), a symmetry-adapted or sparse SDP to make that affordable, and
then exact rationalisation — which the degeneracy makes delicate, since the
certificate has no slack to absorb rounding.

### 7d. Why the corner is forced, and the assembly of Conjectures 1 and 2

If `T` has an atom at exactly `t = +1` then `φ_T'(s) → −∞` as `s → −1⁺`
(the `f'(z) = log(1+z) + 1` factor).  So the marginal gain of moving the `S`
atom off `−1` is infinitely negative: the corner is *forced*, and symmetrically
`S` having an atom at `−1` forces `T` to have one at `+1`.  Operationally this
is the "impossible cell": at `s t = −1` the kernel `1 + δ s t` vanishes, and the
pair `(u,v)` cannot occur.  This exists only at `p = 0`.

**Both items this section used to list as missing are now closed.**

* *Plumbing.*  `bestResponse_le_of_certificate` used to carry `1 + δ·s·t > 0`,
  which fails exactly at the optimum.  It now carries `0 ≤ 1 + δ·s·t`, via
  `mutualInfo_jointUV_eq_kernel_sum_of_nonneg`, so the impossible cell is
  covered and `mutualInfo_le_of_sChan` applies to the Z/S pair itself.
* *Joint optimality.*  This needed a non-affine comparison of the two branches.
  §7e supplies it without any branch comparison: the BSC pair is a **saddle** at
  `p = 0`, which is inequality (iii) — and (iii) is now proved outright
  (one-variable core §7f, diagonal reduction §7f‴).

The old caveat that the sign-flip lemmas carry `δ < 1` while `p = 0` is `δ = 1`
is also moot: at `p = 0` the orientation comes from the certificates
(`DFun_nonneg` for the max, `MDFun_nonpos` for the min), which are proved *at*
`p = 0`, so no limiting argument at `δ = 1` is needed.  The sign flip remains the
conceptual reason the two conjectures differ only in a sign.

### 7d′. The assembly

> **Superseded — kept as the record of an intermediate state.**  The status
> column below was written when steps 1 and 2 were still paper arguments.  They
> are now Lean theorems: `(A)` is `maxExistsC`/`minExistsC` and `(B)` is
> `interiorIsBSC_of_noCorner`.  §7e²² and §7g are the current account, and
> `Basic.lean` is authoritative.  In particular the closing paragraph's
> "formalisation debt" no longer exists, and `CornerDomination` is no longer a
> hypothesis of anything.

Conjecture 1 (`p = 0`, the only case the paper states) is the composite of four
steps; Conjecture 2 is the same chain with the mirror certificate.

| # | Step | Status |
| --- | --- | --- |
| 1 | A maximiser exists and is a best response on each side, hence an alternating-maximisation fixed point.  Binary `U,V` suffice (Pichler, Prop 4.3) | paper (standard); cardinality bound published |
| 2 | Fixed points are the symmetric BSC pair, or have an atom at `±1` | Lean for the symmetric direction (`interior_response_symmetric`); interior uniqueness is §7c⁗ (Λ symmetry ⟹ Green's-function fold ⟹ tangent-line bound for convex `log cosh`) — **paper** |
| 3 | The BSC pair is **not** a local maximum: it is a saddle, `ΛΛ′ > 1`, i.e. inequality (iii) | **proved** — §7f (one-variable core, three regimes, computer-assisted) + §7f‴ (diagonal reduction via the kernel lemma).  In Lean: the boundary case `artanh_edge`, the kernel lemma's certificate (`KernelCert.lean`) |
| 4 | At the corner, the Z/S pair is optimal, with the correct orientation | **Lean**: `mutualInfo_le_of_sChan` — against the S-channel, *every* binary `cL` with `I(U;X) ≤ Cu` obeys `I(U;V) ≤ λ₀ + λ₂·Cu`, with contact exactly at the Z-channel's atoms.  Mirror: `MDFun_nonpos` |

Steps 1+2 say a maximiser is either the BSC pair or a corner pair; step 3 kills
the BSC pair; step 4 identifies the corner pair as Z/S.  So **Conjectures 1 and
2 at `p = 0` are proved**, with the two qualifications worth stating plainly:

* the argument is **computer-assisted twice** — the one-variable core of (iii)
  (6243 certified Lipschitz steps plus a Taylor/Cauchy tail bound) and the
  kernel lemma's Pólya certificate (exact integer arithmetic, 11385 monomials);
* step 2's interior uniqueness and step 1's variational preliminaries are
  **paper arguments, not formalised**.  `Conj12.lean` states both conjectures as
  `Prop`s — never assumed — together with the one composite ingredient
  (`CornerDomination`) that steps 1–3 deliver, and derives the conjectures from
  it, so the remaining formalisation debt is pinned to a single named statement.

