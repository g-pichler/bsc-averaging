import BSCAveraging.Main
/-! # `Envelope` — exploration

None of this file is used by the three theorems of `BSCAveraging.Basic`; it is
kept as a record of the search. -/

/-! # An upper bound on the double-sided information bottleneck

The hull theorem `averaged_bsc_maximise_mutual_information` has a *pointwise*
corollary.  Dikshtein, Ordentlich and Shamai (*The Double-Sided Information
Bottleneck Function*, Entropy **24**(9):1321, 2022) study, for a DSBS with
crossover `p`, the function

```
R(Cu, Cv, p) = max { I(U;V) : U — X — Y — V,  I(U;X) ≤ Cu,  I(Y;V) ≤ Cv }
```

and its BSC lower bound (their Proposition 5, first term)
`F_p(Cu,Cv) = log 2 − h₂(a ⊛ p ⊛ b)` with `a = h₂⁻¹(log 2 − Cu)`,
`b = h₂⁻¹(log 2 − Cv)`.  Since `regionA` is exactly the hypograph of `R` and
`regionB` that of `F_p`, the hull theorem says the two have the same **concave
envelope**, and therefore

```
R(Cu, Cv, p)  ≤  concEnvBSC p Cu Cv  =  (concave envelope of F_p)(Cu, Cv).
```

Two forms are proved:

* `mutualInfo_le_of_bsc_bound` — the dual (support-function) form: for
  `μ, ν ≥ 0` and any `M` bounding the BSC Lagrangian
  `log 2 − h₂(a ⊛ p ⊛ b) − μ(log 2 − h₂ a) − ν(log 2 − h₂ b)`,
  `I(U;V) ≤ μ·Cu + ν·Cv + M`.  This is the form one evaluates numerically; the
  envelope is the infimum of these affine bounds.
* `mutualInfo_le_concEnvBSC` — the primal form, with `concEnvBSC` defined as a
  `sSup` over `convexHull ℝ (regionB p)`, together with the matching
  achievability `bsc_le_concEnvBSC` (`F_p ≤ concEnvBSC`) and
  `concEnvBSC_le_of_bsc_bound` (every affine bound bounds the envelope).

The bound is **not** tight: `F_p` lies strictly below its concave envelope
throughout the open square `(0,1)²` for every `p`, which is precisely why the
hull theorem does not settle Conjectures 1–3 of that paper.  What it does
settle is the time-sharing version of their problem, raised in their concluding
remarks.

See `BSCAveraging.Main`. -/

open Real

namespace BSCAveraging

variable {p : ℝ}

/-! ## The achieved rate triple lies in `conv ℬ` -/

/-- The triple achieved by a channel pair, with the rate constraints `Cu`, `Cv`
in force, is a point of `𝒜` — the constraints in `regionA` are inequalities. -/
lemma mem_regionA_of_chan {Cu Cv : ℝ} (cL cR : Chan)
    (hu : mutualInfo (jointUX cL) ≤ Cu) (hv : mutualInfo (jointYV cR) ≤ Cv) :
    ((mutualInfo (jointUV p cL cR), Cu, Cv) : ℝ × ℝ × ℝ) ∈ regionA p :=
  ⟨cL, cR, hu, hv, le_rfl⟩

/-- **The corollary of the hull theorem**: every achieved triple is a convex
combination of BSC triples. -/
theorem mem_convexHull_regionB_of_chan (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {Cu Cv : ℝ}
    (cL cR : Chan) (hu : mutualInfo (jointUX cL) ≤ Cu)
    (hv : mutualInfo (jointYV cR) ≤ Cv) :
    ((mutualInfo (jointUV p cL cR), Cu, Cv) : ℝ × ℝ × ℝ) ∈ convexHull ℝ (regionB p) := by
  rw [← averaged_bsc_maximise_mutual_information hp0 hp1]
  exact subset_convexHull ℝ _ (mem_regionA_of_chan cL cR hu hv)

/-! ## A linear functional bounded on a set is bounded on its hull -/

/-- A linear functional bounded on `S` is bounded by the same constant on
`convexHull ℝ S`.  (Same statement as `Exploration.convexHull_le_of_le`,
repeated so that this file depends only on the proof path.) -/
theorem convexHull_linear_le {S : Set (ℝ × ℝ × ℝ)} {c₀ c₁ c₂ M : ℝ}
    (h : ∀ x ∈ S, c₀ * x.1 + c₁ * x.2.1 + c₂ * x.2.2 ≤ M) :
    ∀ x ∈ convexHull ℝ S, c₀ * x.1 + c₁ * x.2.1 + c₂ * x.2.2 ≤ M := by
  have hconv : Convex ℝ {x : ℝ × ℝ × ℝ | c₀ * x.1 + c₁ * x.2.1 + c₂ * x.2.2 ≤ M} := by
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have hexp : c₀ * (s * x.1 + t * y.1) + c₁ * (s * x.2.1 + t * y.2.1)
        + c₂ * (s * x.2.2 + t * y.2.2)
        = s * (c₀ * x.1 + c₁ * x.2.1 + c₂ * x.2.2)
          + t * (c₀ * y.1 + c₁ * y.2.1 + c₂ * y.2.2) := by
      ring
    show c₀ * (s * x.1 + t * y.1) + c₁ * (s * x.2.1 + t * y.2.1)
        + c₂ * (s * x.2.2 + t * y.2.2) ≤ M
    rw [hexp]
    have h1 : s * (c₀ * x.1 + c₁ * x.2.1 + c₂ * x.2.2) ≤ s * M :=
      mul_le_mul_of_nonneg_left hx hs
    have h2 : t * (c₀ * y.1 + c₁ * y.2.1 + c₂ * y.2.2) ≤ t * M :=
      mul_le_mul_of_nonneg_left hy ht
    have h3 : s * M + t * M = M := by rw [← add_mul, hst, one_mul]
    linarith
  exact convexHull_min h hconv

/-! ## The dual (support-function) form of the bound -/

/-- The BSC Lagrangian bound transfers to arbitrary binary channels: if `M`
bounds `log 2 − h₂(a ⊛ p ⊛ b) − μ(log 2 − h₂ a) − ν(log 2 − h₂ b)` over all
BSC pairs, then it bounds the same Lagrangian for *every* pair of binary
channels. -/
theorem lagrangian_le_of_bsc_bound {μ ν M : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hM : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      log 2 - h2 ((a ⊛ p) ⊛ b) - μ * (log 2 - h2 a) - ν * (log 2 - h2 b) ≤ M)
    (cL cR : Chan) :
    mutualInfo (jointUV p cL cR) - μ * mutualInfo (jointUX cL)
      - ν * mutualInfo (jointYV cR) ≤ M := by
  have hbnd : ∀ x ∈ regionB p, (1 : ℝ) * x.1 + (-μ) * x.2.1 + (-ν) * x.2.2 ≤ M := by
    rintro x ⟨a, b, ha0, ha1, hb0, hb1, hA, hB, hC⟩
    have h1 : μ * (log 2 - h2 a) ≤ μ * x.2.1 := mul_le_mul_of_nonneg_left hA hμ
    have h2 : ν * (log 2 - h2 b) ≤ ν * x.2.2 := mul_le_mul_of_nonneg_left hB hν
    have h3 := hM a b ha0 ha1 hb0 hb1
    linarith
  have := convexHull_linear_le hbnd _
    (mem_convexHull_regionB_of_chan hp0 hp1 cL cR le_rfl le_rfl)
  simpa using by linarith [this]

/-- The affine upper bound on the DSIB function: for `μ, ν ≥ 0`,
`R(Cu,Cv,p) ≤ μ·Cu + ν·Cv + M` whenever `M` bounds the BSC Lagrangian. -/
theorem mutualInfo_le_of_bsc_bound {μ ν M Cu Cv : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hM : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      log 2 - h2 ((a ⊛ p) ⊛ b) - μ * (log 2 - h2 a) - ν * (log 2 - h2 b) ≤ M)
    (cL cR : Chan) (hu : mutualInfo (jointUX cL) ≤ Cu)
    (hv : mutualInfo (jointYV cR) ≤ Cv) :
    mutualInfo (jointUV p cL cR) ≤ μ * Cu + ν * Cv + M := by
  have hL := lagrangian_le_of_bsc_bound hp0 hp1 hμ hν hM cL cR
  have h1 : μ * mutualInfo (jointUX cL) ≤ μ * Cu := mul_le_mul_of_nonneg_left hu hμ
  have h2 : ν * mutualInfo (jointYV cR) ≤ ν * Cv := mul_le_mul_of_nonneg_left hv hν
  linarith

/-! ## The primal form: the concave envelope of the BSC surface -/

/-- **The concave envelope of the BSC surface** at the rate pair `(Cu, Cv)`:
the largest `R₀` reachable by *time-sharing* BSC pairs whose average rates are
at most `(Cu, Cv)`.  Equivalently, the upper boundary of `conv ℬ` over
`(Cu, Cv)`. -/
noncomputable def concEnvBSC (p Cu Cv : ℝ) : ℝ :=
  sSup {r : ℝ | ((r, Cu, Cv) : ℝ × ℝ × ℝ) ∈ convexHull ℝ (regionB p)}

/-- The set defining `concEnvBSC` is bounded above by `Cu`: data processing
`I(U;V) ≤ I(U;X)` is a linear inequality, hence survives the hull. -/
lemma bddAbove_concEnvSet (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Cu Cv : ℝ) :
    BddAbove {r : ℝ | ((r, Cu, Cv) : ℝ × ℝ × ℝ) ∈ convexHull ℝ (regionB p)} := by
  refine ⟨Cu, fun r hr => ?_⟩
  have hbnd : ∀ x ∈ regionB p, (1 : ℝ) * x.1 + (-1) * x.2.1 + 0 * x.2.2 ≤ 0 := by
    intro x hx
    have := regionA_fst_le_snd_fst hp0 hp1 (regionB_subset_regionA hp0 hp1 hx)
    linarith
  have := convexHull_linear_le hbnd _ hr
  simp only at this
  linarith

/-- The set defining `concEnvBSC` is nonempty for nonnegative rates: the
useless pair attains `(0, Cu, Cv)`. -/
lemma nonempty_concEnvSet (p : ℝ) {Cu Cv : ℝ} (hu : 0 ≤ Cu) (hv : 0 ≤ Cv) :
    {r : ℝ | ((r, Cu, Cv) : ℝ × ℝ × ℝ) ∈ convexHull ℝ (regionB p)}.Nonempty :=
  ⟨0, subset_convexHull ℝ _ (orthant_subset_regionB p (R := ((0 : ℝ), Cu, Cv)) le_rfl hu hv)⟩

/-- **`R ≤ concEnv F_p`.**  The double-sided information bottleneck function of
Dikshtein–Ordentlich–Shamai is bounded above by the concave envelope of the BSC
surface, for every crossover `p` and every rate pair. -/
theorem mutualInfo_le_concEnvBSC (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {Cu Cv : ℝ}
    (cL cR : Chan) (hu : mutualInfo (jointUX cL) ≤ Cu)
    (hv : mutualInfo (jointYV cR) ≤ Cv) :
    mutualInfo (jointUV p cL cR) ≤ concEnvBSC p Cu Cv :=
  le_csSup (bddAbove_concEnvSet hp0 hp1 Cu Cv)
    (mem_convexHull_regionB_of_chan hp0 hp1 cL cR hu hv)

/-- Achievability: the BSC surface itself lies below its envelope, so the bound
of `mutualInfo_le_concEnvBSC` is sandwiched between `F_p` and the envelope. -/
theorem bsc_le_concEnvBSC (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b Cu Cv : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hA : log 2 - h2 a ≤ Cu) (hB : log 2 - h2 b ≤ Cv) :
    log 2 - h2 ((a ⊛ p) ⊛ b) ≤ concEnvBSC p Cu Cv :=
  le_csSup (bddAbove_concEnvSet hp0 hp1 Cu Cv)
    (subset_convexHull ℝ _ ⟨a, b, ha0, ha1, hb0, hb1, hA, hB, le_rfl⟩)

/-- Every affine bound bounds the envelope: `concEnv F_p` is the infimum of the
affine functions `μ·Cu + ν·Cv + M` of `mutualInfo_le_of_bsc_bound`.  This is
what makes the numerical evaluation of the envelope legitimate. -/
theorem concEnvBSC_le_of_bsc_bound {μ ν M Cu Cv : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hCu : 0 ≤ Cu) (hCv : 0 ≤ Cv)
    (hM : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      log 2 - h2 ((a ⊛ p) ⊛ b) - μ * (log 2 - h2 a) - ν * (log 2 - h2 b) ≤ M) :
    concEnvBSC p Cu Cv ≤ μ * Cu + ν * Cv + M := by
  refine csSup_le (nonempty_concEnvSet p hCu hCv) (fun r hr => ?_)
  have hbnd : ∀ x ∈ regionB p, (1 : ℝ) * x.1 + (-μ) * x.2.1 + (-ν) * x.2.2 ≤ M := by
    rintro x ⟨a, b, ha0, ha1, hb0, hb1, hA, hB, hC⟩
    have h1 : μ * (log 2 - h2 a) ≤ μ * x.2.1 := mul_le_mul_of_nonneg_left hA hμ
    have h2 : ν * (log 2 - h2 b) ≤ ν * x.2.2 := mul_le_mul_of_nonneg_left hB hν
    have h3 := hM a b ha0 ha1 hb0 hb1
    linarith
  have := convexHull_linear_le hbnd _ hr
  simp only at this
  linarith

end BSCAveraging
