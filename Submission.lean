/-
# The Palomar Challenge modules

Each subdirectory holds one Challenge together with its Comparator
configuration and its `formalization.yaml`:

* `Submission/MO285151/`    — MathOverflow 285151, `conv 𝒜 = conv ℬ`;
* `Submission/Conjecture2/` — Dikshtein-Ordentlich-Shamai, Conjecture 2 (`p = 0`).

Each Challenge is self-contained over Mathlib: it repeats verbatim the
definitions its statement needs and states the theorem with `sorry`.  The
Solution that discharges it is `Solutions/<same subdirectory>/Solution.lean`,
under its own root component — see `Solutions.lean` for why.

Conjecture 1 is proved in the library (`BSCAveraging/CFinish.lean`) but has no
configuration on this branch: its Pólya certificate runs under `native_decide`,
so the theorem carries an auxiliary axiom that Comparator rejects.

A Challenge and its Solution declare the *same* names and are never imported
into the same module, so this file deliberately imports none of them.
-/
