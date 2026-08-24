/-
# The Palomar submission modules

Each subdirectory holds one Challenge/Solution pair together with its
Comparator configuration and its `formalization.yaml`:

* `Submission/MO285151/`    — MathOverflow 285151, `conv 𝒜 = conv ℬ`;
* `Submission/Conjecture2/` — Dikshtein-Ordentlich-Shamai, Conjecture 2 (`p = 0`).

Conjecture 1 is proved in the library (`BSCAveraging/CFinish.lean`) but has no
configuration on this branch: its Pólya certificate runs under `native_decide`,
so the theorem carries an auxiliary axiom that Comparator rejects.

A Challenge and its Solution declare the *same* names and are never imported
into the same module, so this file deliberately imports none of them.
-/
