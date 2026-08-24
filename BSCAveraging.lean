/-
# Root module of the `BSCAveraging` library

MathOverflow 285151, *Do averaged binary symmetric channels maximize mutual
information?*, and Conjectures 1 and 2 of Dikshtein–Ordentlich–Shamai, *The
Double-Sided Information Bottleneck Function*, Entropy **24**(9):1321.

Two trees:

* `BSCAveraging.Basic` — **the proof**.  It imports exactly the transitive
  dependency closure of the three theorems and runs the `#print axioms`
  soundness checks.
* `BSCAveraging.Exploration` — everything else: proved, `sorry`-free, and used
  by none of them.

Both are built here.
-/

import BSCAveraging.Basic
import BSCAveraging.Exploration
