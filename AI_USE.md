# AI use

The Ramanujan Challenge submissions behind this library were made by Jeromie Beasley with AI
tools (Claude and ChatGPT) used as research assistants; the same tools wrote and repaired the
Lean proofs here and organised this repository. The Problem 2.1 analysis
(`RamanujanChallenge/Problem21.lean`, `RamanujanChallenge/Euler21.lean`, `scripts/precheck3.py`,
three false controls) was written on
17 October 2026 by Grok Bot, an AI agent working for the author. It found the
creative-telescoping certificate and the dominance bound in SymPy, checked them there, and then
had the Lean kernel check them.

No statement here rests on an AI's say-so. Every proof is checked by the Lean kernel and
replayed by an independent kernel checker (`scripts/check_review.py`), every theorem's axioms are audited,
and every false control must be rejected for the check to pass. What the statements mean, and
what they do not claim, is set out in plain words in `README.md` and `LIMITATIONS.md`.

On 17 October 2026 Grok Bot also cleaned the library to Mathlib style (zero build warnings,
Mathlib's standard linter set, `#lint` and `lint-style`) without changing any theorem statement.

The separate review edition was produced by OpenAI Codex on 18 October 2026 UTC at the
author's request. Codex reviewed the supplied archive, added the reviewed interface and direct
error-bound proof (`RamanujanChallenge/ReviewedProblem21.lean`), and hardened the checks
(`scripts/verify.py`, `scripts/check_review.py`, `scripts/test_verify.py`). Codex also reviewed
the Grok Bot cleanup independently. Grok Bot merged the two editions on 17 October 2026
(Chicago time). The merged copy has local build and kernel replay evidence; no claim is made
that it has run on hosted CI.

On 17 October 2026 (Chicago time), at the author's request, Grok Bot added the dual licence
(`MIT OR Apache-2.0`) and the Mathlib-style headers. It also compared the library line by line
with the Technion's GPL-3.0 skeleton and kept the Apache option off the two files that overlap
it (see `PROVENANCE.md`). No proof or theorem statement changed.

On 17 October 2026 (Chicago time), at the author's request, Grok Bot rewrote the parts of
`Exact.lean` and `Pincherle.lean` that had matched the Technion's GPL-3.0 skeleton. The new
definitions and proofs (a `CFData` structure with transfer-matrix recurrences, recessive
solutions via little-o, Pincherle's theorem by little-o algebra, the 2.1 roots from Mathlib's
quadratic formula, the rescaled coefficients as quotients by `r_n`) were written from the
mathematics without opening the Technion file. That file was fetched afterwards only for a
similarity check. The agent had seen the earlier overlapping versions in this repository the
same day; `PROVENANCE.md` says so and records the result of the check. The downstream proofs were
re-derived, and the theorem inventory changed from 132 to 146 names (see `scripts/config.json`).

On 18 October 2026 (Chicago time), at the author's request, Grok Bot proved the general real
Euler integral for `₂F₁` (`RamanujanChallenge/EulerIntegral.lean`) and re-derived the Problem 2.1
case from it. The theorem inventory changed from 146 to 152 names. No earlier theorem statement or
proof changed. The same day OpenAI Codex proved the theorem independently at the author's
request (commit `e977cf2`); Grok Bot compared the two and merged the better parts of each
(branch `phase2-final-merged`, 153 names; see `PROVENANCE.md` and `COMPARISON.md`).
