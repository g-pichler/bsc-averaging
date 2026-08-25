# BSCAveraging

A Lean 4 / Mathlib development that settles three previously open problems about
binary channels on a **doubly symmetric binary source** (DSBS).

A DSBS with parameter `p` is a pair `(X, Y)` of `Bernoulli(1/2)` bits with
`P(X ≠ Y) = p`. Throughout, `U` and `V` are the outputs of two independent
binary channels applied to `X` and to `Y`, so that `U — X — Y — V` is a Markov
chain. Everything is in **nats** (natural logarithm), so the sources' "1 bit"
is `Real.log 2`.

| # | Result | Lean name | Axioms |
| --- | --- | --- | --- |
| 1 | MathOverflow 285151: `conv 𝒜 = conv ℬ` for every `p ∈ [0,1]` | `averaged_bsc_maximise_mutual_information` | standard |
| 2 | Dikshtein–Ordentlich–Shamai, Conjecture 1, at `p = 0` | `conjecture1_p0_holds` | standard + one `native_decide` axiom |
| 3 | Dikshtein–Ordentlich–Shamai, Conjecture 2, at `p = 0` | `conjecture2_p0_holds` | standard |

"standard" means `propext`, `Classical.choice`, `Quot.sound`. The whole
development is `sorry`-free and contains no hand-written `axiom` declaration;
the only non-standard axiom anywhere in it is the one `native_decide` mints for
the Pólya certificate of result 2.

## 1. Averaged binary symmetric channels maximize mutual information

[MathOverflow 285151](https://mathoverflow.net/questions/285151/do-averaged-binary-symmetric-channels-maximize-mutual-information)
(Georg Pichler, 2017; still unanswered there) asks about two sets of rate
triples `(R₀, R₁, R₂)`:

* `regionA p` — those for which **some** pair of binary channels satisfies
  `I(U;X) ≤ R₁`, `I(Y;V) ≤ R₂` and `R₀ ≤ I(U;V)`;
* `regionB p` — the same, with both channels **binary symmetric** with
  crossovers `a` and `b`, where the three mutual informations become
  `log 2 − h₂(a)`, `log 2 − h₂(b)` and `log 2 − h₂(a ∗ p ∗ b)`.

`regionB p ⊆ regionA p` is elementary. The question is whether taking convex
hulls closes the gap — equivalently, whether averaged binary symmetric channels
already exhaust what arbitrary binary channels achieve. The predecessor
question,
[MathOverflow 213084](https://mathoverflow.net/questions/213084/do-binary-symmetric-channels-maximize-mutual-information),
asked for `regionA p = regionB p` and received a counterexample at `p = 0`, so
the hull is essential and that counterexample leaves the present question open.

```lean
theorem averaged_bsc_maximise_mutual_information {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    convexHull ℝ (regionA p) = convexHull ℝ (regionB p)
```

The same statement settles **Conjecture 5.2** of Pichler, Piantanida and Matz,
*Distributed Information-Theoretic Clustering*, Information and Inference
**11** (2022) 1029–1082,
[doi:10.1093/imaiai/iaab007](https://doi.org/10.1093/imaiai/iaab007), which
asks exactly for the convex hull of the inner bound to equal that of the outer
bound.

Read `BSCAveraging/Main.lean` first — it states the result and gives the road
map, with every step linked to the theorem that proves it.

## 2, 3. The two `p = 0` conjectures of the double-sided information bottleneck

Dikshtein, Ordentlich and Shamai (Shitz), *The Double-Sided Information
Bottleneck Function*, Entropy **24**(9):1321 (2022),
[doi:10.3390/e24091321](https://doi.org/10.3390/e24091321), study

```
R(Cu, Cv) = max { I(U;V) : U — X — Y — V,  I(X;U) ≤ Cu,  I(Y;V) ≤ Cv }
```

and state three conjectures. Conjectures 1 and 2 concern `p = 0`, i.e. `X = Y`:

> **Conjecture 1.** Let `X = Y`. The optimal test channels achieving
> `R(Cu, Cv, 0)` are a Z-channel and an S-channel respectively.
>
> **Conjecture 2.** The test channels that maximize `I(X;U,V)` are both Z
> channels.

Both are proved here, for binary `U` and `V`, in **value form**: no admissible
pair exceeds the Z/S value, and none undercuts the Z/Z value.

```lean
theorem conjecture1_p0_holds : Conjecture1_p0
theorem conjecture2_p0_holds : Conjecture2_p0
```

The four steps of both proofs, and the certificates they use, are described in
`BSCAveraging/Basic.lean`; `BSCAveraging/Exploration/NOTES.md` §7 is the long form.

## Scope and known gaps

Stated once, for all three results.

* **Binary channels on both sides.** `Chan` is a `2 × 2` row-stochastic matrix.
  For result 1 this is the setting of the source question. For results 2 and 3
  the reduction of the double-sided bottleneck over arbitrary alphabets to
  binary test channels is Proposition 3 of the Dikshtein–Ordentlich–Shamai
  paper and Proposition 4.3 of the Pichler–Piantanida–Matz paper; it is
  **cited, not formalized here**. Read as statements about `R(Cu, Cv, 0)` with
  unrestricted alphabets, results 2 and 3 are conditional on that published
  cardinality bound.
* **`p = 0` only** for results 2 and 3 — the only case the paper's Conjectures 1
  and 2 state. Conjecture 3 of that paper, which concerns `p` above a
  threshold, is not addressed. `BSCAveraging/Exploration/NOTES.md` §7a records a structural
  obstruction: every lemma on the proof path is `δ`-uniform, so no
  recombination of this toolkit can prove Conjecture 3.
* **Value, not uniqueness.** Results 2 and 3 say the conjectured optimal value
  is not beaten. They do not claim the conjectured pair is the *only*
  optimiser.
* **The objective translation for Conjecture 2.** The paper maximizes
  `I(X;U,V)`; the Lean statement minimizes `I(U;V)` at fixed rates. The
  identity `I(U;V) = I(U;X) + I(V;X) − I(X;U,V)` that relates the two is the
  authors' own, stated as Remark 5 of the paper, but it is **not formalized
  here** — the Lean statement is the minimization form directly.
* **One `native_decide` axiom in result 2.** `conjecture1_p0_holds` reaches
  `native_decide` through the 24129-monomial Pólya certificate of its kernel
  lemma (`BSCAveraging/KernelCertFast.lean`). On Lean v4.32.0 `native_decide`
  mints a per-declaration auxiliary axiom rather than citing
  `Lean.ofReduceBool`, so the axiom report names
  `BSCAveraging.Reflect.kerQPE_allNonneg._native.native_decide.ax_1_1`. The other computed step of that
  proof, the 650-cell interval sweep of regime 2 of the core, is checked by the
  Lean **kernel** (`BSCAveraging/CoreSweep.lean`) and adds no axiom.
* **Two endpoints of result 1 were already known.** Pichler–Piantanida–Matz
  themselves note that Conjecture 5.2 holds at `p = 0`, from their Corollary 4.1
  and Proposition 4.3; and `p = 1/2` is degenerate, both regions collapsing to
  `{R₀ ≤ 0, R₁ ≥ 0, R₂ ≥ 0}` without convexification. Those cases are reproved
  here, not established. The new content is `p ∈ (0, 1/2) ∪ (1/2, 1)`.
* **The binary restriction costs nothing for result 1.** Conjecture 5.2 is
  stated for `S_i`, which is *defined* with the cardinality bounds
  `|U| ≤ |X|`, `|V| ≤ |Y|`, and Proposition 4.3 of the same paper gives
  `conv(S_i) = conv(R_i)`. The caveat above applies only to results 2 and 3.
* **Novelty is not independently established.** MathOverflow 285151 has no
  answer and no comments (checked via the StackExchange API: asked 2017-11-03,
  0 answers). The Dikshtein–Ordentlich–Shamai paper has one recorded citing
  work, a 2024 *Entropy* editorial that mentions the setting but not the
  conjectures; no resolution of either conjecture was found. No prior Lean
  formalization of any of the three problems was found. That search is the
  authors' own and is not offered as evidence of priority.

## Layout

```
BSCAveraging.lean            library root: Basic (the proof) + Exploration
BSCAveraging/
  Basic.lean                 imports exactly the dependency closure of the three
                             theorems, and runs `#print axioms` on every step
  Main.lean                  road map for result 1
  Definitions.lean           channels, the DSBS, entropy, mutual information,
                             and every definition a Challenge reproduces
  Regions.lean               the conjecture, and what is proved about the regions
  Conj12.lean, Conj2.lean,
  CFinish.lean, ...          results 2 and 3
  CoreSweep.lean             the kernel-checked interval sweep
  KernelCertFast.lean        the `native_decide` Pólya certificate
  Exploration/               exploration, experiments and documentation, not used
                             in the final result
Submission/                  the Palomar Challenges and their configurations
Solutions/                   the matching Solutions, under their own root
```

`BSCAveraging/Exploration/NOTES.md` is a working record written as the attack 
proceeded. It is organised by route rather than by the final argument, and most
routes in it were refuted. Where a section's status line disagrees with
`BSCAveraging/Basic.lean`, `Basic.lean` is authoritative.

## Build

```
lake exe cache get     # optional, for the Mathlib oleans
lake build
```

Requires the pinned Lean and Mathlib in `lean-toolchain` and `lakefile.toml`.

## Submission modules

`Submission/` holds one Challenge per submitted result, with its Comparator
configuration and its `formalization.yaml`; `Solutions/` holds the matching
Solution:

| Challenge | Solution | Theorem compared |
| --- | --- | --- |
| `Submission/MO285151/` | `Solutions/MO285151/` | `BSCAveraging.MO285151.averaged_bsc_maximise_mutual_information` |
| `Submission/Conjecture2/` | `Solutions/Conjecture2/` | `BSCAveraging.DSIB.conjecture2_p0` |

The two sit under different root components on purpose. Comparator exports the
Challenge from a protected directory placed first on `LEAN_PATH`, and Lean
resolves a module by its **root** component alone, so a Solution sharing the
Challenge's root is looked for in that directory and not found — the failure
reported as [PalomarSubmission issue 108](https://github.com/PalomarRegistry/PalomarSubmission/issues/108).

**On this branch there is deliberately no configuration for Conjecture 1.**
`conjecture1_p0_holds` is proved in `BSCAveraging/CFinish.lean` and remains part
of the library — result 2 of the table above — but its Pólya certificate is
checked by `native_decide`, so the theorem carries an auxiliary axiom and cannot
meet Palomar's permitted-axiom rule. The two configurations that remain depend
only on `propext`, `Classical.choice` and `Quot.sound`.

Note that `BSCAveraging.Conj2` transitively imports `BSCAveraging.KernelCertFast`,
so the `native_decide` is inside Conjecture 2's *import* closure. That is not a
dependency: `#print axioms BSCAveraging.DSIB.conjecture2_p0` reports exactly the
three standard axioms. Comparator checks what a declaration depends on, not what
the project happens to contain.

Each `Challenge.lean` is self-contained over Mathlib: it repeats verbatim the
definitions its statement needs and states the theorem with `sorry`. Each
`Solution.lean` imports the one library module it needs — `BSCAveraging.Main`
and `BSCAveraging.Conj2` respectively — and discharges it. The Challenge module
documentation carries the mathematical account of that one result.

## Licence

Apache-2.0; see `LICENSE`.
