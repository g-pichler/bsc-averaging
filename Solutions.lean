/-
# The Palomar solution modules

One `Solution` per Challenge of `Submission/`, discharging its statement from
the library:

* `Solutions/MO285151/`    — `BSCAveraging.Main`;
* `Solutions/Conjecture2/` — `BSCAveraging.Conj2`.

The Solutions sit under their own root component rather than beside their
Challenges.  Comparator exports the Challenge from a protected directory placed
first on `LEAN_PATH`, and Lean resolves a module by its **root** component
alone, so a Solution sharing the Challenge's root is looked for in that
directory and not found (PalomarSubmission issue 108).

A Challenge and its Solution declare the *same* names and are never imported
into the same module, so this file deliberately imports none of them.
-/
