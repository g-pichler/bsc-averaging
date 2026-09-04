# Do averaged binary symmetric channels maximize mutual information?

> **Historical document.**  This was the repository's top-level README while the
> attack was in progress; it now lives beside `NOTES.md` in `Exploration/` and is
> kept as a record of the route.  It is **not** the current status of the
> development: several sections below still read as open that have since been
> closed.  For the current statement of what is proved, with what axioms, read
> the repository root `README.md` and `BSCAveraging/Basic.lean` — where those
> disagree with this file, they are authoritative.  Unqualified module names
> (`Main.lean`, `CoreSweep.lean`, …) refer to modules of `BSCAveraging/`, one
> directory above this file; `NOTES.md` and `numerics/` are this directory's.

A Lean 4 / Mathlib formalization of the setup of

> [MathOverflow 285151](https://mathoverflow.net/questions/285151/do-averaged-binary-symmetric-channels-maximize-mutual-information),
> *Do averaged binary symmetric channels maximize mutual information?*
> (Georg Pichler, 2017; unanswered),

a refinement of
[MathOverflow 213084](https://mathoverflow.net/questions/213084/do-binary-symmetric-channels-maximize-mutual-information),
*Do binary symmetric channels maximize mutual information?*, which was answered
negatively.

This library depends on Mathlib and nothing else.

> ## ★ The conjecture is proved, for every `p ∈ [0,1]`
>
> ```lean
> theorem averaged_bsc_maximise_mutual_information {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
>     convexHull ℝ (regionA p) = convexHull ℝ (regionB p)
> ```
>
> `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
> This also settles Conjecture 5.2 of Pichler–Piantanida–Matz,
> *Distributed Information-Theoretic Clustering*, IMAIAI **11** (2022),
> [doi:10.1093/imaiai/iaab007](https://doi.org/10.1093/imaiai/iaab007).
>
> **Read `Main.lean` first** — it states the result and gives the road map, with
> every step linked to the theorem that proves it.

## The question

Let `(X, Y)` be a doubly symmetric binary source with parameter `p ∈ [0, 1/2]`:
`X, Y ~ Bernoulli(1/2)` and `P(X ≠ Y) = p`. Two regions in `ℝ³` with
coordinates `(R₀, R₁, R₂)`:

* **𝒜** — triples for which there exist *binary* `U, V` forming the Markov
  chain `U — X — Y — V` with

  ```
  R₁ ≥ I(U;X),   R₂ ≥ I(Y;V),   R₀ ≤ I(U;V).
  ```

* **ℬ** — triples for which there exist `a, b ∈ [0,1]` with

  ```
  R₁ ≥ 1 − H(a),   R₂ ≥ 1 − H(b),   R₀ ≤ 1 − H(a ∗ p ∗ b),
  ```

  i.e. 𝒜 with the channels `X → U`, `Y → V` restricted to be symmetric.
  (`a ∗ b = a(1−b) + (1−a)b` is binary convolution.)

**Question:** is `conv(𝒜) = conv(ℬ)`?

MO 213084 asked whether `𝒜 = ℬ` and received a counterexample at `p = 0`: at
`R₁ = R₂ = 0.4` bits the BSC pair achieves `I(U;V) < 0.1895`, while a near-Z
channel pair achieves `> 0.19`. So the convex hull is essential to the present
question, and the counterexample does not settle it.

## Units

Everything is in **nats** (natural logarithm). The source's "1 bit" is
`Real.log 2`, and `1 − H(a)` reads `log 2 - h2 a`.

## What is proved

All `sorry`-free.  Every theorem depends only on `propext`, `Classical.choice`
and `Quot.sound`.  (When this document was written `conjecture1_p0_holds` carried
one further axiom, from the `native_decide` check of the Pólya certificate; that
check is now done by the kernel, `KernelKron.lean`, see `NOTES.md` §7k.)
All of this is checked by `#print axioms` in `Basic.lean`.

Rows marked **†** are in `Exploration.lean`: proved, but *not* used by the main
theorem.  Everything unmarked is on the proof path.

| Statement | Lean name |
| --- | --- |
| `I ≥ 0` for any joint law on `Bool × Bool` (Gibbs) | `mutualInfo_nonneg` |
| `h₂ c ≤ log 2` | `h2_le_log_two` |
| `I(X;Y) = log 2 − h₂ p` for the DSBS | `mutualInfo_dsbs` |
| BSCs `a`, `p`, `b` in series form a BSC with crossover `a ∗ p ∗ b` | `jointUV_bsc` |
| `I(U;X) = log 2 − h₂ a`, `I(Y;V) = log 2 − h₂ b`, `I(U;V) = log 2 − h₂ (a∗p∗b)` | `mutualInfo_jointUX_bsc`, `mutualInfo_jointYV_bsc`, `mutualInfo_jointUV_bsc` |
| both regions are down-closed in `R₀`, up-closed in `R₁, R₂` | `regionA_mono`, `regionB_mono` |
| **`ℬ ⊆ 𝒜`** | `regionB_subset_regionA` |
| hence `conv ℬ ⊆ conv 𝒜` | `convexHull_regionB_subset` |
| **★ THE CONJECTURE, for every `p ∈ [0,1]`** | `averaged_bsc_maximise_mutual_information`, `averagedBSCConjecture_all` |
| ★ the same for `p ∈ [0,1/2]`, and the reflection `p ↦ 1−p` | `averagedBSCConjecture_of_mem`, `averagedBSCConjecture_one_sub` |
| ★ the open interval `0 < p < 1/2` (the substance) | `averagedBSCConjecture_of_lt_half` |
| the separation step: domination in every direction ⟹ `𝒜 ⊆ conv ℬ` | `regionA_subset_convexHull_regionB` |
| every `R ∈ 𝒜` is dominated by a point of `ℬ`, degenerate cases included | `exists_regionB_dominating_all` |
| the bridge: the Lagrangian of a binary channel pair **is** `lagrTwoPoint` | `lagrangian_eq_lagrTwoPoint_closed` |
| **the two-point theorem**: `F ≤ M` for any bound `M` on the four corner values of `g` | `lagrTwoPoint_le_of_corner_bounds_closed` |
| (S4), the opposite-skew half: `Ω ≤ gMax4 − gSum` | `omegaTwoPoint_le_spread` |
| the three steps of (S4) | `HStep_mixed_diff_neg`, `lam_kap_mul_le_min_weight`, `spread_ge_min_weight_mul` |
| its analytic core: `K(z) = 1 − artanh z/z + z·artanh z` is increasing | `KStepFun_strictMonoOn`, `lt_one_add_sq_mul_artanh` |
| `f_e(δPQ)` is strictly supermodular in `(P,Q)` | `fe_mul_supermodular` |
| the regions and their hulls are closed | `isClosed_regionA`, `isClosed_convexHull_regionA`, `isClosed_convexHull_regionB` |
| **`conv` of a compact set in `ℝ³` is compact** (absent from Mathlib v4.32.0) | `isCompact_convexHull` |
| `ℬ` contains the orthant `{R₀ ≤ 0, R₁ ≥ 0, R₂ ≥ 0}` | `orthant_subset_regionB` |
| the conjecture ⟺ `𝒜 ⊆ conv ℬ` | `averagedBSCConjecture_iff` |
| at `p = 1/2`, `I(U;V) = 0` for *every* channel pair | `mutualInfo_jointUV_half` |
| at `p = 1/2` both regions equal `{R₀ ≤ 0, R₁ ≥ 0, R₂ ≥ 0}` | `regionA_half`, `regionB_half` |
| **the conjecture holds at `p = 1/2`** | `averagedBSCConjecture_half` |
| two-term log-sum inequality | `log_sum_two` |
| **data processing**: pushing a coordinate through a channel cannot raise `I` | `mutualInfo_compose_le` |
| `I(U;V) ≤ I(U;X)` and `I(U;V) ≤ I(Y;V)` | `mutualInfo_jointUV_le_jointUX`, `mutualInfo_jointUV_le_jointYV` |
| hence `𝒜 ⊆ {R₀ ≤ min (R₁, R₂)}`, and `0 ≤ R₁, R₂`, `R₀ ≤ log 2` on `𝒜` | `regionA_fst_le_snd_fst`, `regionA_fst_le_snd_snd`, `regionA_snd_fst_nonneg`, `regionA_snd_snd_nonneg`, `regionA_fst_le_log_two` |
| `I ≤ log 2` for any joint law †| `mutualInfo_le_log_two` |
| **cut-set**: `I(U;V) ≤ I(X;Y) = log 2 − h₂ p` | `mutualInfo_jointUV_le_source` |
| the DPI + cut-set outer bound is convex, so it bounds the **hull** †| `convex_outerBound`, `convexHull_regionA_subset_outerBound` |
| **the conjecture holds at `p = 0`** (where `𝒜 ≠ ℬ`) | `averagedBSCConjecture_zero` |
| at `p = 0` the outer bound is exactly the answer: `conv 𝒜 = conv ℬ = outerBound 0` †| `convexHull_regionA_zero_eq_outerBound`, `convexHull_regionB_zero_eq_outerBound` |
| `y < artanh y`, and the trapezoid bound `f_e(y) < y·artanh y/2` for `f_e = ∫ artanh` | `self_lt_artanh`, `fe_le_half_mul` |
| the curvature profile factors as `g = Q·R`, with `g` and `Q` strictly decreasing †| `gFun_eq_Qfun_mul_Rfun`, `gFun_strictAntiOn`, `Qfun_strictAntiOn` |
| the value constraint `R(s) + R(t) < R(x)` upgrades to `g(s) + g(t) < g(x)`, i.e. `κ_s κ_t > 1` †| `gFun_add_lt`, `kappa_prod_gt_one` |
| **local rigidity**: at a symmetric fixed point of positive value the linearized skew map contracts, `Λ·Λ' < x² < 1` †| `lambda_prod_lt`, `lambda_prod_lt_one` |
| `z ↦ artanh z / z` is strictly increasing, and `fo z − z·fo′ z = artanh z − z` | `artanh_div_strictMonoOn`, `fo_sub_mul_deriv` |
| the odd kernel `(r,q) ↦ w(r·q)` is strictly supermodular | `wFun_mixed_diff_pos` |
| **global sign flip**: `Ω > 0` iff the two skews point opposite ways — so at any maximizer they are anti-correlated | `omegaTwoPoint_neg`, `omegaTwoPoint_pos` |
| the odd part of the best-response objective is `O(y) = κ·y·[w(dy) − w(cy)]`, with a definite sign for every `y` †| `oddPart_eq`, `oddPart_pos`, `wFun_strictMonoOn` |
| the skew force `O′(u) − O(u)/u = κ·[M(du) − M(cu)]` is signed for **every** `u`, not just to first order †| `oddPart_deriv_sub_eq`, `forceFun_pos` |
| the two-atom value `V(u,v)` in centre/half-gap coordinates, its two partial derivatives, and: joint stationarity ⟹ `(u²−v²)(G′(v+u) − G′(v−u)) = 0`, i.e. bitangency †| `envVal`, `hasDerivAt_envVal_v`, `hasDerivAt_envVal_u`, `stationary_imp_bitangent` |
| the even part of `G` cancels out of `∂V/∂v\ †|_{v=0}`, so the force at symmetry is exactly `forceFun` | `envVal_deriv_v_zero_of_split`, `envVal_deriv_v_zero_eq_forceFun` |
| **Mrs. Gerber's Lemma**, differential form in bias coordinates: `κ(1−q²)artanh q < (1−(κq)²)artanh(κq)` — the same statement as `gFun` decreasing †| `mgl_bias`, `gFun_lt_gFun_mul` |
| **Mrs. Gerber's Lemma, Jensen form**: `w₁f_e(κq₁) + w₂f_e(κq₂) ≤ f_e(κt)` when `w₁f_e(q₁)+w₂f_e(q₂) = f_e(t)` — proved without ever constructing `f_e⁻¹` †| `mgl_jensen`, `mglRatio_strictAntiOn`, `mglH_ge_of_mem` |
| `f_e` strictly increasing on `[0,1)` †| `fe_strictMonoOn` |
| `f(z) = (1+z)log(1+z)` lies below its chord on `[−a,a]`, hence **data processing** `E f(δST) ≤ E f_e(S)` in bias coordinates †| `fFun_le_chord`, `dpi_row`, `lagrKernel_le` |
| **the conjecture holds whenever `μ ≥ 1`** (and symmetrically `ν ≥ 1`), so `μ, ν ∈ [0,1)` is WLOG †| `lagrangian_nonpos_of_one_le_mu` |
| `artanh(m+u) − artanh(m−u) ≥ 2·artanh u`, hence **`f_e` is supermodular**: `f_e(m+k)+f_e(m−k) ≥ 2f_e(m)+2f_e(k)` †| `artanh_add_sub_ge`, `fe_supermodular` |
| `log(1+z)·(1+λz) ≤ z` on `(−1,1]`, `λ = 1/log 2 − 1` †| `log_mul_one_add_lamC_le` |
| a linear functional bounded on `S` is bounded on `convexHull ℝ S` †| `convexHull_le_of_le` |
| **`R ≤ concEnv F_p`**: the DSIB function of Dikshtein–Ordentlich–Shamai is below the concave envelope of the BSC surface | `mutualInfo_le_concEnvBSC`, `concEnvBSC` |
| its dual form, `I(U;V) ≤ μ·C_u + ν·C_v + M` for any bound `M` on the BSC Lagrangian | `mutualInfo_le_of_bsc_bound`, `lagrangian_le_of_bsc_bound` |
| the envelope is the infimum of those affine bounds, and lies above the BSC surface | `concEnvBSC_le_of_bsc_bound`, `bsc_le_concEnvBSC` |
| **the one-sided best-response bound** from a dual certificate, both sides | `bestResponse_le_of_certificate`, `bestResponse_le_of_certificate'` |
| **the `p = 0` certificate (Conj 1)**: `D ≥ 0` on `[−1,1]`, contacts at `a` and `−1` | `DFun_nonneg` |
| **the certificate as a channel bound**: at `p = 0`, against the S-channel, *every* binary `cL` with `I(U;X) ≤ Cu` has `I(U;V) ≤ λ₀ + λ₂·Cu` — so the Z-channel is a **global** best response | `mutualInfo_le_of_sChan`, `sChan`, `marg₂_sChan`, `biasOfSnd_sChan` |
| the kernel identity with **degenerate cells** allowed (`0 ≤ 1+δst`), covering the `p = 0` impossible cell | `mutualInfo_jointUV_eq_kernel_sum_of_nonneg` |
| **the boundary case of (iii)**: `β < artanh β·(1 − β²/3)` | `artanh_edge` |
| the Schur-type decomposition behind the kernel lemma, and its equal-weight case | `schur_decomposition`, `cube_sum_ge_three_mul` |
| **comonotone Schur**: nonnegative weights comonotone with `r` make the kernel sum nonnegative | `kernel_nonneg_of_comonotone`, `comonotone_of_decreasing`, `mul_comonotone` |
| **the kernel splits as `G·S f − S(f·g)`, and both halves are nonnegative** — so the open part of the kernel lemma is only the ratio bound `S(f·g) ≤ G·S f` | `kernel_split`, `kerSum_f_nonneg`, `kerSum_fg_nonneg` |
| **the kernel vanishes identically on the face `u = 1`** — the source of every vanishing margin | `kernel_vanishes_on_face` |
| **the face derivative is nonnegative**: `κ·r₁r₂r₃·∂(kernel)/∂c\|_{c=0} = κ·faceX + faceY`, both parts `≥ 0` on the ordered cube (Pólya certificate, 53 positive-integer monomials, no elevation) | `faceX_nonneg`, `faceY_nonneg` |
| **the kernel lemma** — `kerQ ≥ 0` on the ordered bi-simplex, by a Pólya certificate with 11385 positive-integer monomials and no degree elevation.  This closes the diagonal reduction, hence (iii) in full | `kerQ_nonneg_ordered` |
| the difference identities `r_i−r_l`, `f_i−f_l`, `f_ig_l−f_lg_i`, each carrying a factor `(θ_l−θ_i)` | `rFun_sub`, `fFun'_sub`, `fg_cross` |
| **the kernel form annihilates every geometric law** — why the mixture route is the right one | `geometric_kernel_zero` |
| **no weight-blind argument can work**: the two-atom law `{1↦1/10, 2↦9/10}` violates it | `kernel_false_for_general_law` |
| the extremal constant of the branch-comparison route, `2log²2 < 1` | `two_mul_log_two_sq_lt_one` |
| **the mirror certificate (Conj 2)**: `D ≤ 0` on `[−1,1]`, contacts at `−a` and `+1` | `MDFun_nonpos` |
| the two shapes, generic in the multipliers | `GFun_nonneg_of_contacts`, `GFun_nonpos_of_contacts` |
| **against a symmetric `T`, a bitangent interior response is symmetric** — no half-asymmetric interior fixed point at `p = 0` | `interior_response_symmetric` |
| its two steps: the mirrored certificate forces `λ₁ = 0`; `D″` has ≤ 1 positive zero | `lam1_eq_zero`, `DSym''_eq_zero_unique`, `no_two_positive_contacts` |
| the mirror key inequality — *not* log-sum, but two uses of `log x ≤ x−1` | `key_mirror` |
| its two collapses: `D″·(1−s²)(1−ds)` is **linear**, and `N(a) ≥ 0` **is** log-sum | `DFun''_eq`, `key_log_sum`, `N_at_a_nonneg` |
| the closed forms `λ₂ = log((1−da)/(1+d))/log((1−a)/2)`, `0 < λ₂ < 1` | `lam2_pos`, `lam2_lt_one`, `DFun_at_a`, `DFun_neg_one` |
| **the bias parametrization** (`NOTES.md` §2): `I(U;X) = Σ_u π_u f_e(s_u)`, the kernel identity `P(u,v) = π_u ρ_v (1 + δ s_u t_v)`, and `I(U;V) = Σ_{u,v} π_u ρ_v f(δ s_u t_v)` | `mutualInfo_jointUX_eq_bias`, `jointUV_eq_kernel`, `mutualInfo_jointUV_eq_kernel_sum` |
| **the sharp bound `ρ = I/𝒥 ≤ 2 − 1/log 2`** for every mean-zero law on `[−1,1]` — lemma (L1) of `NOTES.md` §6 †| `mutual_le_c0_mul_jeffreys` |

Established on paper (not yet formalized), see `NOTES.md` §6: at **any**
alternating-maximization fixed point, with `𝒥 := I + L` the Jeffreys divergence
between joint and product (`L` = Lautum information) and `ρ := I/𝒥`,

```
μ·𝒥(U;X) = 𝒥(U;V) = ν·𝒥(Y;V) ,      F = 𝒥(U;V)·[ ρ(U;V) − ρ(U;X) − ρ(Y;V) ]
```

so `μ, ν` are the Jeffreys contraction ratios of the two hops, and §5d's profile
`R(y) = f_e(y)/(y·artanh y)` **is** `ρ`.  Plus an equalizer (KKT) condition:
`μ·D(π_X‖P_{X|u}) − D(ρ_V‖P_{V|u})` is constant on `supp U`.

Both endpoints of the parameter range are therefore settled: `p = 0` and
`p = 1/2`. The `p = 0` case is the interesting one — it is exactly where
MO 213084's counterexample to `𝒜 = ℬ` lives, yet the *hulls* still coincide:
data processing caps `R₀` at `min (R₁, R₂)`, and time-sharing the noiseless
pair `(log 2, log 2, log 2)` against the useless pair `(0,0,0)` already attains
that cap.

The statement is a `Prop`, and is now a theorem:

```lean
def AveragedBSCConjecture (p : ℝ) : Prop :=
  convexHull ℝ (regionA p) = convexHull ℝ (regionB p)
```

## Layout

The library has two trees.

* **`BSCAveraging.Basic`** — *the proof*.  It imports exactly the transitive
  dependency closure of the three theorems
  (`averaged_bsc_maximise_mutual_information`, `conjecture1_p0_holds`,
  `conjecture2_p0_holds`) and runs `#print axioms` on every result.
* **`BSCAveraging.Exploration`** — everything else that was proved along the
  way.  `sorry`-free, but used by none of the three.

The split is mechanical: a declaration lives in `Exploration/` iff it is outside
that closure and is not referenced by anything inside it.  For a file `X.lean`
that is partly used, the unused part is `Exploration/X.lean`, which imports
`BSCAveraging.X` and repeats its section headers so the two read in parallel.

`lake build BSCAveraging` builds both; `lake build BSCAveraging.Basic` builds
only the proof.

## Files

Read in this order.  `Main.lean` is the entry point for MO 285151; `Conj2.lean`
is the last file of the Entropy 24(9):1321 chain.

| File | Contents |
| --- | --- |
| **`Main.lean`** | **start here** — the MO 285151 theorem, the road map, and a pointer to the theorem proving each step |
| `Definitions.lean` | `bconv` (`⊛`), `Chan`, `bsc`, `dsbs`, `entropy1`/`entropy2`/`mutualInfo`, `h2`, the joint laws `jointUX`, `jointYV`, `jointUV` |
| `Regions.lean` | `regionA`, `regionB`, `ℬ ⊆ 𝒜`, the conjecture and its reduction, the `p = 1/2` case |
| `BSC.lean` | marginals and entropy of `dsbs`, series composition of BSCs, the `p = 1/2` product structure |
| `Nonneg.lean` | Gibbs' inequality via `log x ≤ x − 1`, cell by cell; `I ≤ log 2` |
| `DataProcessing.lean` | log-sum inequality, `mutualInfo_compose_le`, DPI along the chain |
| `Zero.lean` | data processing outer bound on `𝒜`; the `p = 0` case |
| `Rigidity.lean` | an `artanh` calculus layer (Mathlib has none), `y < artanh y` — **the inequality the whole proof rests on** — and the trapezoid bound for `f_e = ∫ artanh` |
| `SignFlip.lean` | the odd part `fo` of `f`, monotonicity of `artanh z / z`, supermodularity of the odd kernel, and the **global sign flip** for `Ω` |
| `Lagrangian.lean` | the chord bound for `f` and data processing in bias coordinates |
| `BiasCoords.lean` | the bias parametrisation: `I(U;X) = Σ π_u f_e(s_u)`, the kernel identity `P(u,v) = π_u ρ_v (1 + δ s_u t_v)`, and `I(U;V) = Σ π_u ρ_v f(δ s_u t_v)` |
| `FixedPoint.lean` | **the two-point theorem** `lagrTwoPoint_le_of_corner_bounds_closed` |
| `Bridge.lean` | mean-zero forces `π_false = b/(a+b)`, matching the weights built into `lagrTwoPoint` |
| `Closedness.lean` | the regions are closed; `isCompact_convexHull` (absent from Mathlib v4.32.0), proved via Carathéodory |
| `Assembly.lean` | bridge ⟹ domination ⟹ Hahn–Banach separation ⟹ the MO conjecture |
| `BestResponse.lean` | the one-sided LP dual: a certificate `φ_T(s) ≤ λ₀+λ₁s+λ₂f_e(s)` bounds `I(U;V)` for **every** channel on that side (`NOTES.md` §7) |
| `PZero.lean` | the `p = 0` certificates, both signs: the Z-channel is a global best response to the S-channel for the **max** (Conj 1) and the **min** (Conj 2) |
| `Reflect.lean`, `KernelKron.lean`, `KernelCertFast.lean` | polynomials as data; the kernel lemma by reflection — its 24129 coefficients read off one big-integer Kronecker evaluation, checked by the kernel |
| `KernelAlgebra.lean` | `zsRate`, `zsValue`, the Schur decomposition and the comonotone reduction |
| `Conj12.lean` | the two conjectures as `Prop`s, the feasible sets, `maxExistsC`/`minExistsC`, `OptPairC`, the corner extraction and `cornerBound` |
| `Interval.lean`, `CoreDeriv.lean`, `CoreSweep.lean`, `Regime1.lean`, `CorePos.lean` | the one-variable core `core_pos` in three regimes (interval arithmetic; the 650-cell sweep runs in the **kernel**, `decide +kernel`, and adds no axiom) |
| `Diagonal.lean`, `MixtureRep.lean`, `KernelBridge.lean`, `DiagReduction.lean`, `SaddleIII.lean` | the diagonal case, the geometric-mixture representation, the kernel certificate bridge, the diagonal reduction, and **`saddle_iii`** |
| `LogCosh.lean` | the §7c⁗ programme: the Green identity, the fold, `(♦)`, the residual and bitangency |
| `TwoAtom.lean`, `BitangencyBridge.lean`, `KKT.lean`, `TwoAtomChan.lean` | the Hessian at the symmetric point (`hessian_indefinite`), the bridge to `Chan`, 2-D KKT |
| `BFinish.lean`, `BFinishV.lean` | step **(B)**: stationarity of an optimiser on each side, the skews vanish, `interiorIsBSC_of_noCorner` |
| `CFinish.lean` | step **(C)** for the maximisation, and **Conjecture 1 at `p = 0`** |
| `Conj2.lean` | steps **(A′)–(D′)** and **Conjecture 2 at `p = 0`** |
| `Basic.lean` | imports the proof path, `#print axioms` on every result |
| `Exploration/` | proved but **not used** by any of the three theorems: Mrs. Gerber's Lemma in bias coordinates, the sharp ratio bound `ρ ≤ 2 − 1/log 2`, the even/odd split, the concave-envelope corollary (`Envelope`), the symmetric-response analysis (`PZeroSymm`), the CAS calibration dumps (`Cal0`, `Cal1`, `Calib` — not imported, hence not built), and the unused part of each proof file |
| `NOTES.md` | the full record: the attack, the proof, and the dozen refuted routes |
| `numerics/*.py` | exploratory scripts, not part of the Lean build |

Build with

```
lake build BSCAveraging          # proof + exploration
lake build BSCAveraging.Basic    # the proof only
```

## Modelling notes

* The Markov chain `U — X — Y — V` is structural, not a hypothesis: `U` is
  produced from `X` by a channel `cL` and `V` from `Y` by `cR`, so
  `jointUV p cL cR` is by construction the law of a chain.
* `X ~ Bernoulli(1/2)` is likewise built in (the `/ 2` in `jointUX`). The
  MO 213084 answer lists this as a separate constraint on `U`'s distribution;
  parametrizing by the *forward* channels `X → U`, `Y → V` rather than by
  `U` and the backward channel makes it automatic.
* `mutualInfo` is an explicit four-term algebraic expression, not Mathlib's
  measure-theoretic entropy. This keeps the region definitions elementary; the
  price is that `I ≥ 0` has to be proved (`Nonneg.lean`).

## Numerical evidence: the conjecture looks true for every `p`

Because both regions are monotone in the same directions, `conv 𝒜 = conv ℬ`
holds iff their support functions agree, i.e. iff for all `μ, ν ≥ 0`

```
sup over arbitrary binary cL, cR  [ I(U;V) − μ I(U;X) − ν I(Y;V) ]
  =  sup over a, b ∈ [0,1]        [ same, with BSCs ].
```

(`λ₀ = 0` is trivial and `λ₀ > 0` rescales to `1`; the sign pattern
`λ₀ ≥ 0, λ₁, λ₂ ≤ 0` is forced by the common recession cone.) A gap in any
direction would refute the conjecture. `numerics/support_gap.py` scans this,
with closed forms for all three mutual informations, a 4-D grid plus L-BFGS-B
refinement on the general side and a dense 2-D grid plus refinement on the BSC
side.

**Result** (726 combinations, `p ∈ [0, 0.45]`, `μ, ν ∈ [0.05, 0.95]`;
`numerics/scan-results.txt`): the largest observed `sup_general − sup_BSC` is
`3.5·10⁻⁶` bits, at the level of the optimizer's own tolerance, and in every
single direction the maximizing *general* channel pair returned is itself a BSC
pair. No gap anywhere.

Two further probes, independent of the support-function optimizer
(`numerics/convex_hull_lp.py`): 3392 sampled points of `𝒜` — random channel
pairs plus deliberately Z/S-like ones, `p ∈ [0, 0.4]` — all lie in `conv ℬ` by
exact LP over a BSC grid, zero failures; and a global search maximizing
`R₀ − (envelope of ℬ at (R₁,R₂))` over all four channel parameters bottoms out
at `≤ 1.1·10⁻¹⁴` bits for every `p` tested.

`NOTES.md` §5d proves **local rigidity**: at every symmetric fixed point of
positive value the linearized skew map contracts, `ΛΛ' < x² = (δst)² < 1`, so no
asymmetric branch bifurcates. The proof is elementary — it turns on the identity
`g = Q·R` and the monotonicity of `Q(y) = (1−y²)artanh(y)²/f_e(y)`.

`NOTES.md` §7f traces the last open link of Conjecture 1 down to one explicit
**rational** inequality: (iii) ⟸ its one-variable core (**proved**, three
regimes) + the diagonal reduction ⟸ a kernel lemma
`Σᵢ λᵢ(rᵢ² − r_j r_k) ≥ 0` in five variables.  There `Ĝ(z) = 2Σz^k/(4k²−1)`
turns out to be the geometric mixture with density `1/(2√θ)`, and the cubic form
annihilates every geometric law.  A Schur-type decomposition splits the kernel
lemma into a Chebyshev term plus a manifestly nonnegative one; the certificate
route is an LP over `Q = Σ(Aᵢ−Aⱼ)²Mᵢⱼ` for an explicit degree-22 polynomial `Q`
(infeasible, as is every SOS/SDP ansatz tried).

§7f′ then reduces the kernel lemma structurally.  With
`S φ = Σᵢ φ(θᵢ)(rᵢ²−r_jr_k)` and `G = Σ g(θᵢ)`, the weight is
`λᵢ = f(θᵢ)(G−g(θᵢ))`, so the kernel equals `G·S f − S(f·g)` — and **both halves
are theorems** (`kerSum_f_nonneg`, `kerSum_fg_nonneg`), because `f`, `f·g` and
`r` are all decreasing in `θ`.  What remains open is one ratio bound,
`S(f·g) ≤ G·S f`, sharp in each of the three summands of `G`.  It is
asymptotically tight in the corner `θ₁,θ₃→1`, `θ₂→0`, `u→1`, where the pair
terms cancel at leading order (`E₁₂+E₂₃ → 0`) and positivity is decided at
order `ε`.

§7f″ then finds the exact reason: at `u = 1` one has `f ≡ 1` and `g = r`, so the
kernel **vanishes identically on the whole face `u = 1`**
(`kernel_vanishes_on_face`) — the corner was merely a point of that face.  On
the face the first datum is the slope in `c = 1−u`, and it is nonnegative
everywhere: the affine face relation `rᵢ + (1−v)sᵢ = 1` collapses the derivative
to `κ·faceX + faceY` in `(r₁,r₂,r₃,κ)`, with `faceX ≥ 0` outright and
`faceY ≥ 0` on the ordered cube by a Pólya certificate with 53 positive-integer
coefficients and no degree elevation (`faceX_nonneg`, `faceY_nonneg`).

§7f‴ then **closes the kernel lemma**.  The face analysis showed that the
*ordering* is what makes a nonnegative-coefficient certificate exist; applied to
the full problem, that works: clear the positive denominators to get the
degree-21 polynomial `kerQ`, use the symmetry of the kernel to assume
`θ₁ ≤ θ₂ ≤ θ₃`, and pass to the ordered bi-simplex coordinates
`t = (θ₁, θ₂−θ₁, θ₃−θ₂, 1−θ₃)`, `s = (v, u−v, 1−u)`.  There `kerQ` is a
combination of **11385 monomials with positive integer coefficients**, with no
degree elevation — a Pólya certificate, verified in exact arithmetic.  In the
unordered basis 870 of 1743 coefficients are negative, which is exactly why
every earlier LP/SOS attempt was infeasible.  With the kernel lemma, the
diagonal reduction follows, and with it the saddle inequality (iii) in full —
the last open analytic link of Conjecture 1 at `p = 0`.

`NOTES.md` §7f **proves the saddle inequality (iii)** — the last analytic step of
Conjecture 1 at `p = 0` — by reducing it to the classical one-variable statement
`1/log Z − 1/(Z−1) > tanh θ/(2θ)`, `Z = cosh 2θ`, and settling that in three
regimes: exact Taylor coefficients plus a Cauchy tail bound on `(0,0.45]`,
6243 certified Lipschitz steps on `[0.45,3]`, and elementary exponential bounds
on `[3,∞)`.  Open in that chain: the diagonal reduction.

`NOTES.md` §7c⁗ proves that at `p = 0` the **only interior fixed point is the
symmetric (BSC) pair**: the Λ symmetry (`Λ` depends on the two skews only through
their sum `X = u+v`) turns each bitangency residual into a chord-deficit
integral, a Green's-function fold reduces positivity to one inequality, and that
inequality is the tangent-line bound for the convex `log cosh`.  On paper, not
yet formalized.

`NOTES.md` carries the rest of the analysis: the problem reduces to an explicit
four-variable optimization over "channel biases", symmetric configurations are
closed under alternating maximization, and the remaining gap is exactly the
possibility of an asymmetric fixed point — which is where the Z/S channels live
in the pointwise problem, and which every numerical probe says is absent here.

### Why this is consistent with the pointwise counterexamples

Dikshtein, Ordentlich and Shamai
([Entropy **24**(9):1321, 2022](https://www.mdpi.com/1099-4300/24/9/1321),
ISIT 2021) study the same optimization *without* the convex hull — the
"double-sided information bottleneck" `max I(U;V)` s.t. `I(U;X) ≤ C_u`,
`I(Y;V) ≤ C_v` for a DSBS. They prove BSC optimality as `p → 1/2` (their
Theorem 1) and conjecture that Z and S channels are optimal at `p = 0`
(Conjecture 1), with BSCs optimal for `p` above a threshold (Conjecture 3).
So the pointwise claim is false near `p = 0` — which is MO 213084.

The hull question is untouched by that work, and the two are compatible.
Reproducing their regime at `p = 0`, `C_u = C_v = 0.4` bits: general channels
attain `0.19539` (near-Z/S pair) against `0.18950` for BSCs, matching the
MO 213084 answer — but the concave envelope of the BSC region at that point is
`0.4`, twice as large. The Z/S advantage lives strictly inside the *non-concave*
part of the rate region, which is exactly what `conv` erases.

### What the hull theorem does and does not give that paper

`Envelope.lean` derives the pointwise corollary `R(C_u,C_v,p) ≤ concEnv F_p`,
where `F_p(C_u,C_v) = 1 − H(a ∗ p ∗ b)` is their BSC lower bound (Proposition 5,
first term).  Numerically this beats their upper bound (Proposition 6) on 51 %
of the `(C_u,C_v)` grid at `p = 0.02`, rising to 64 % at `p = 0.4`, by up to
0.036 bits.  It also settles the time-sharing variant flagged in their
concluding remarks: with time sharing the answer is `concEnv F_p` for every `p`.

It does **not** touch their Conjectures 1–3, and the obstruction is structural:
`F_p` is strictly below its own concave envelope throughout the open square for
*every* `p` (at `p = 0.35` the gap still reaches 0.008 bits; the touching set is
only the boundary edges), so the hull erases exactly the region those
conjectures live in.  The sharpest illustration is their Theorem 1: BSC
optimality holds as `p → 1/2`, yet there `F_p ≈ c·u(C_u)·u(C_v)` is a product,
hence a saddle, hence non-concave — the hull result cannot see the optimality
that is actually true.

## Roadmap

The conjecture is proved for every `p ∈ [0,1]`, so the roadmap is now a record
rather than a plan; `NOTES.md` §6 has the full account, including the refuted
routes, which is the more useful half.

Optional extensions, none of them needed for the result:

1. **The `p = 0` counterexample** to the *unhulled* `𝒜 = ℬ` (MO 213084), as an
   explicit pair of rational channel matrices plus numeric bounds — it would
   show the convex hull in the question is not cosmetic.  (The hull statement at
   `p = 0` is proved; this would show the unhulled one fails.)
2. **Upstream `isCompact_convexHull`** to Mathlib.  The proof in
   `Closedness.lean` is stated for `ℝ³` but is Carathéodory plus a compactness
   argument, and generalises to any finite-dimensional real topological vector
   space.
3. **Sharpen (S4).**  The proved slack factor is `max(acδ, bdδ) < 1`; numerically
   `Ω/(gMax4 − gSum) ≲ 0.684`, so the bound is not tight.  Of interest only if
   one wants the extremal configurations.
