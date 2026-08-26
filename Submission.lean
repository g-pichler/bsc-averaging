/-
# The Palomar Challenge modules

Each subdirectory holds one Challenge together with its Comparator
configuration and its `formalization.yaml`:

* `Submission/MO285151/`    — MathOverflow 285151, `conv 𝒜 = conv ℬ`;
* `Submission/Conjecture1/` — Dikshtein-Ordentlich-Shamai, Conjecture 1 (`p = 0`);
* `Submission/Conjecture2/` — Dikshtein-Ordentlich-Shamai, Conjecture 2 (`p = 0`).

Each Challenge is self-contained over Mathlib: it repeats verbatim the
definitions its statement needs and states the theorem with `sorry`.  The
Solution that discharges it is `Solutions/<same subdirectory>/Solution.lean`,
under its own root component — see `Solutions.lean` for why.

The Conjecture 1 configuration is carried here but does not meet Palomar's
permitted-axiom rule: its Pólya certificate runs under `native_decide`, so the
theorem carries an auxiliary axiom that Comparator rejects.  It is ready for the
day that certificate is checked by the kernel instead.

A Challenge and its Solution declare the *same* names and are never imported
into the same module, so this file deliberately imports none of them.
-/
