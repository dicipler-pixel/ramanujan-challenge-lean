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
