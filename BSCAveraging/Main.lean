import BSCAveraging.Assembly

/-! # Averaged binary symmetric channels maximise mutual information

**Start here.**  This file states the result and gives the road map; every step
links to the theorem that proves it.

Let `(X,Y)` be a doubly symmetric binary source with crossover `p`, and consider
Markov chains `U — X — Y — V` with `U`, `V` binary.  Write

* `𝒜 = regionA p` — the rate triples `(R₀,R₁,R₂)` attainable with **arbitrary**
  binary channels `X → U`, `Y → V`, meaning `I(U;X) ≤ R₁`, `I(Y;V) ≤ R₂`,
  `R₀ ≤ I(U;V)`;
* `ℬ = regionB p` — the same, restricted to **binary symmetric** channels.

## The theorem

`averagedBSCConjecture_all : 0 ≤ p → p ≤ 1 → conv 𝒜 = conv ℬ`

This is MathOverflow 285151 (G. Pichler, 2017) and Conjecture 5.2 of
Pichler–Piantanida–Matz, *Distributed Information-Theoretic Clustering*,
IMAIAI 11 (2022).  `#print axioms` reports only
`propext, Classical.choice, Quot.sound`.

## Road map

Since `ℬ ⊆ 𝒜` (`regionB_subset_regionA`), only `𝒜 ⊆ conv ℬ` is at stake
(`averagedBSCConjecture_iff`).  The endpoints are separate and easy:
`p = 1/2` (`averagedBSCConjecture_half`) and `p = 0`
(`averagedBSCConjecture_zero`); and `p ↦ 1 − p` is a symmetry
(`averagedBSCConjecture_one_sub`).  For `0 < p < 1/2`, with `δ = 1 − 2p`:

1. **Support-function reduction** — `regionA_subset_convexHull_regionB`.
   `ℬ` contains the orthant `{R₀ ≤ 0, R₁ ≥ 0, R₂ ≥ 0}`
   (`orthant_subset_regionB`), which forces any separating functional to be
   `F = R₀ − μR₁ − νR₂` with `μ,ν ≥ 0`.  Separation is Mathlib's
   `geometric_hahn_banach_closed_point`, applied to `conv ℬ`, which is closed
   (`isClosed_convexHull_regionB`) because `ℬ` is `compact + cone`
   (`regionB_eq_add_cone`) and `conv` of a compact set in `ℝ³` is compact
   (`isCompact_convexHull` — absent from Mathlib, proved here).

2. **Domination** — `exists_regionB_dominating_all`: every `R ∈ 𝒜` is beaten, in
   each direction `F`, by a point of `ℬ`.  Degenerate configurations (a vanishing
   marginal, or equal biases) have `I(U;V) = 0` and are dominated by `(0,0,0)`.

3. **The bridge** — `lagrangian_eq_lagrTwoPoint_closed`: for binary channels the
   Lagrangian `I(U;V) − μI(U;X) − νI(Y;V)` *equals* the explicit two-point
   expression `lagrTwoPoint δ μ ν a b c d`.

   Notation, used throughout.  The **bias families** are one number per value of
   `U`, resp. `V`:
   ```
   s_u = 1 − 2·P(X=1 | U=u),   t_v = 1 − 2·P(Y=1 | V=v),   both in [−1,1]
   ```
   and the **bias random variables** are `S = s_U`, `T = t_V` (independent, since
   `U — X — Y — V`).  A mean-zero two-point law is `S ∈ {a, −b}` with
   `P(S = a) = b/(a+b)` — **positive atom first** — so in Lean
   ```
   a = s_false,  b = −s_true,   c = t_false,  d = −t_true,   all in [0,1]
   ```
   after relabelling `U` or `V` if needed (`lagrTwoPoint_neg_swap`).  The weights
   are forced, not chosen: `X` and `Y` uniform give `Σ π_u s_u = 0`, hence
   `π_false = b/(a+b)` (`pi_false_eq`), which is exactly what `lagrTwoPoint`
   already has built in.

4. **The two-point theorem** — `lagrTwoPoint_le_of_corner_bounds_closed`:
   `F ≤ M` for any bound `M` on the four "corner" values `g(·,·)`, where
   `g(P,Q) = f_e(δPQ) − μf_e(P) − νf_e(Q)` is exactly the value of the BSC pair with
   those biases (`exists_regionB_point`).  Taking `M = sup_ℬ F` gives `F ≤ J_sym`.

## The heart of it

Step 4 splits by the *relative sign of the two skews*.  Writing
`F = Σ wᵢⱼ·g(|sᵢ|,|tⱼ|) + Ω` (`lagrTwoPoint_eq_gSum_add_Omega`), the first term is
an average of four values of `g`, hence `≤ max g`.  So everything turns on the
odd gain `Ω`:

* **same-direction skews** — `Ω < 0` by the global sign flip
  (`omegaTwoPoint_neg`), so `F < J_sym` outright
  (`lagrTwoPoint_lt_of_same_skew`);
* **opposite skews** — `Ω > 0`, and one needs `Ω ≤ gMax4 − gSum`
  (`omegaTwoPoint_le_spread`), proved in three steps:

```
Ω ≤ λκδ·|Δ_g|                 HStep_mixed_diff_neg
  ≤ min(w_ac,w_bd)·|Δ_g|      lam_kap_mul_le_min_weight   (a·c·δ ≤ 1, b·d·δ ≤ 1)
  ≤ gMax4 − gSum              spread_ge_min_weight_mul    (2×2 algebra)
```

The first step is the analytic core: with `H(u) = fo(δu)/u + δ·f_e(δu)` one has
`u·H′(u) = δ·K(δu)` for `K(z) = 1 − artanh z/z + z·artanh z`, and

```
K′(z) = artanh z·(1 + 1/z²) − 1/z ≥ 0   ⟺   z ≤ (1+z²)·artanh z
```

which is `self_lt_artanh`.  **The whole proof rests on `z < artanh z`.**

## Files

`Definitions` `Regions` `BSC` `Nonneg` `DataProcessing` `Zero` — the setting.
`Rigidity` `SignFlip` `Lagrangian` — `f_e`, `artanh`, and the sign flip.
`BiasCoords` `Bridge` — the bias parametrisation and the bridge to `mutualInfo`.
`FixedPoint` — the two-point theorem.
`Closedness` — compactness, closed hulls, separation.
`Assembly` — the chain above.
`Basic` — `#print axioms` for every result.
`Exploration` — proved results *not* used here (MGL, the sharp ratio bound, the
even/odd split, the skew mechanism); see `NOTES.md`.
-/

namespace BSCAveraging

/-- **Averaged binary symmetric channels maximise mutual information.**

For every crossover `p ∈ [0,1]`, the convex hull of the region attainable with
arbitrary binary channels equals the convex hull of the region attainable with
binary *symmetric* channels. -/
theorem averaged_bsc_maximise_mutual_information {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    convexHull ℝ (regionA p) = convexHull ℝ (regionB p) :=
  averagedBSCConjecture_all hp0 hp1

end BSCAveraging
