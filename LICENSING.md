# Licensing

Copyright (c) 2026 Jeromie Beasley.

| What | Licence |
| :--- | :--- |
| Lean files, scripts, workflows, configuration and generated outputs (the code and proofs) | `MIT OR Apache-2.0`, at your option. See [`LICENSE`](LICENSE), [`LICENSE-MIT`](LICENSE-MIT) and [`LICENSE-APACHE`](LICENSE-APACHE) |
| README, LIMITATIONS, PROVENANCE, AI_USE, and any paper, figure or other prose (the written text) | CC BY 4.0. See [`LICENSE-CC-BY-4.0.md`](LICENSE-CC-BY-4.0.md) |

SPDX identifier for the code: `MIT OR Apache-2.0`.

The Lean library files with a Mathlib-style header (`Series.lean`, `Problem21.lean`,
`Euler21.lean` and `ReviewedProblem21.lean` in `RamanujanChallenge/`) say "Released under
Apache 2.0 license as described in the file LICENSE". `LICENSE` points to the full Apache
text in `LICENSE-APACHE` and offers MIT as the alternative. The Apache option exists so that
pieces of this library can be offered to Mathlib, which accepts Apache-2.0 only.

## Exception pending review

`RamanujanChallenge/Exact.lean` and `RamanujanChallenge/Pincherle.lean` are **not** offered
under Apache-2.0 and have no Apache header. Parts of them match the Lean skeleton
`Code/2.1/LeanFormal/LeanFormal/PiPCF.lean` in the Ramanujan Machine group's repository, which
is licensed under GPL-3.0:

* `Exact.lean`: the definitions `lamS` and `lamD` and the theorems `lamS_root`, `lamD_root`,
  `lamS_pos`, `lamD_neg` and `abs_lamS_lt_abs_lamD`, with essentially the same proofs.
* `Pincherle.lean`: `IsSolution`, `convNum`, `convDen`, `IsMinimalWeak` (the skeleton's
  `IsMinimal`), the statement shape of `pincherle`, and the coefficient formulas `A21`, `B21`.

Until that provenance is reviewed, these two files stay under the terms they carried before
the dual licence was added. Nothing from them is to be offered to Mathlib.

Credit for any part: Jeromie Beasley, with a link to this repository or to the paper's DOI.
