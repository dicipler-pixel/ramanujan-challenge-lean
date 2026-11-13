# Licensing

Copyright (c) 2026 Jeromie Beasley.

| What | Licence |
| :--- | :--- |
| Lean files, scripts, workflows, configuration and generated outputs (the code and proofs) | `MIT OR Apache-2.0`, at your option. See [`LICENSE`](LICENSE), [`LICENSE-MIT`](LICENSE-MIT) and [`LICENSE-APACHE`](LICENSE-APACHE) |
| README, LIMITATIONS, PROVENANCE, AI_USE, and any paper, figure or other prose (the written text) | CC BY 4.0. See [`LICENSE-CC-BY-4.0.md`](LICENSE-CC-BY-4.0.md) |

SPDX identifier for the code: `MIT OR Apache-2.0`.

All seven Lean library files in `RamanujanChallenge/` (`Exact.lean`, `Pincherle.lean`,
`Series.lean`, `Problem21.lean`, `EulerIntegral.lean`, `Euler21.lean`, `ReviewedProblem21.lean`) carry the Mathlib-style
header "Released under Apache 2.0 license as described in the file LICENSE"; `scripts/verify.py`
fails if any of them loses it. `LICENSE` points to the full Apache
text in `LICENSE-APACHE` and offers MIT as the alternative. The Apache option exists so that
pieces of this library can be offered to Mathlib, which accepts Apache-2.0 only.

## No GPL exception

An earlier revision (commit `31a2bb3`) kept `Exact.lean` and `Pincherle.lean` out of the
Apache option because parts of them matched the Lean skeleton
`Code/2.1/LeanFormal/LeanFormal/PiPCF.lean` in the Ramanujan Machine group's GPL-3.0 repository.
Those parts were removed and replaced by an independent rewrite on 17 October 2026 (branch
`phase2-cleanroom`; see `PROVENANCE.md`), and the exception no longer applies. What remains in
common with that file is mathematics, not expression: the challenge's own coefficients `a_n`,
`b_n`, the paper's normaliser `r_n` (Eq. 21), and the statements of the facts being proved.

Credit for any part: Jeromie Beasley, with a link to this repository or to the paper's DOI.
