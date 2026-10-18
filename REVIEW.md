# Review of the separate Problem 2.1 edition

> Merge note (17 October 2026, Chicago time). This is Codex's review of its own edition, kept
> as written. On this branch the five original Lean files carry the Grok Bot style cleanup
> (`7cebef4`), so the remarks below about unchanged original files and retained linter
> warnings no longer apply here. See "Merged branch" at the end.

Reviewed 18 October 2026 UTC by OpenAI Codex at Jeromie Beasley's request.
Base archive: `ramanujan-challenge-lean-phase2-4f7bd95.zip`.
Base archive SHA-256: `9ebfedcf2457fdc86e595f513bedebbb37f42c00b035b2c7050d4930476835a9`.
Base commit recorded by the ZIP: `4f7bd95db51fb49d03ce920f645a2be340a97a5a`.

## Mathematical conclusion

No defect was found in the supplied proof of the Problem 2.1 limit. All five
original Lean sources remain unchanged in this edition. Their kernel checks and
axiom audit passed before the changes. The review also checked the coefficients,
initial values, index shifts, nonzero-denominator obligations, recurrence transport,
minimality conditions, integral anchors and hypergeometric identification.

This is not a proof of all six challenge problems, nor a completion of every lemma
in the official Lean skeleton. It is a proof of its final Problem 2.1 convergence
statement by a route that replaces general Poincaré–Perron with a direct bound.
Kernel checking verifies the formal statements; the explicit definitions and
source comparison address whether those statements encode the intended problem.

Official comparison source fetched during review:
https://github.com/RamanujanMachine/RamanujanChallengeSolutions/blob/main/Code/2.1/LeanFormal/LeanFormal/PiPCF.lean
GitHub blob SHA: `7b2a921061961fe10a2f21d930c2dd49e450da4b`.
Its `a`, `b`, `convNum`, `convDen` and final limit agree with the original library.
The official `IsMinimal` omits eventual nonvanishing of the companion; the
library's corrected definition and counterexample address this explicitly.
The reviewed direct proof does not use either Pincherle formulation.

## New proof interface

`RamanujanChallenge.Reviewed` independently restates the coefficients and defines
actual convergents with `P 0 = -42`, `Q 0 = 1`, `P 1 = 44370`, `Q 1 = -1047`.
The recurrence advances using `a (n+2)` and `b (n+2)`. Induction proves these
sequences equal the original numerator and denominator sequences shifted by one.
Thus the original dummy index with denominator zero is excluded from this interface.

Eight new theorems establish the two identifications, all denominator nonvanishing,
initial values, the evaluated Pincherle value, an exact residual, a geometric error
bound, and convergence. With `L = 6/(3-π)`, the new statements include

```
P n / Q n - L = (Z21 (n+1) / Q n) / Z21 0
‖P n / Q n - L‖ ≤ (300 * sqrt 2 / Z21 0) * (1/5)^n
```

`Z21 0` is proved positive where needed. The bound follows from the original
`Z21_div_convDen_le`. `Reviewed.limit` applies the squeeze theorem to this bound;
it does not invoke `pcf21_tendsto` or `pincherle`. This is an alternate final
argument built on the original analysis, not a separate discovery of that analysis.

## Findings and fixes

| Finding | Impact | Change |
| --- | --- | --- |
| CI ran `lake update` before verification | The checked dependency set could differ from the archived lockfile | Use the committed manifest, check it remains unchanged |
| Inventory checked counts, not exact names | A same-count replacement could pass the inventory check | Record and compare all 132 names; require all source modules to be configured |
| Comment stripping did not handle nested Lean comments | Declarations could be misidentified | Nested-comment scanner and regression tests; include public `lemma` declarations |
| A plain type mismatch counted as a mathematical negative test | An unrelated typing error could qualify as negative evidence | Remove that category; keep infrastructure-error rejection and exact control count |
| Old success report could survive a failed rerun | Stale evidence could be mistaken for the current result | Delete success reports before each run and write them only on success |
| README badge points to the original public branch | Badge cannot certify this separate archive | New README identifies local evidence and retains original README as history |
| Limitations described the official Euler lemma as general | Overstated the difference in scope | Clarify it is the same parameter family, expressed using different definitions |

Negative controls are pipeline sanity checks, not independent proofs that arbitrary
false statements are rejected. The source inventory scanner supports this project's
simple namespace/declaration style; it is not a complete Lean parser or a security
boundary for hostile source files. The kernel and axiom audit provide the proof checks.

## Reproduction and evidence

Run `lake exe cache get`, then `python3 scripts/check_review.py` with the pinned Lean.
The checked configuration contains six modules, 132 named theorems and six false
controls. Six Python regression tests exercise verifier failure modes. The final
status is in `verification/review_checks.json`; axiom dependencies and source hashes
are in `verification/report.json`. Build, replay, audit and negative-control logs
are included. `verification/original_source_comparison.json` records byte equality
of the five original Lean sources against the supplied ZIP.

Local runtime note: this environment needed an LD_PRELOAD shim mapping only
`readlink("/proc/<own-pid>/exe")` to `readlink("/proc/self/exe")` because of its PID
namespace. The Lean compiler and proof sources were not modified. The shim source
is included in `verification/runtime/lean-proc-compat.c` for transparency. Normal
Linux environments do not need this workaround. Mathlib's pinned dependencies and
cache were reused locally; source files in the separate edition were built anew.

Remaining original linter warnings concern style, deprecated syntax and redundant
tactics. No claim of warning-free code, new mathematical priority, independent
human review, or hosted CI for this edition is made. The original five proof files
are preserved to keep the mathematical changes easy to inspect.

## Merged branch

Codex's follow-up review of the Grok Bot cleanup (`7cebef4`) found no mathematical regression:
all 124 theorem signatures unchanged, zero-warning build, kernel replay, standard lint and
declaration lint passing, and `ReviewedProblem21.lean` compiling against the cleaned modules.
It noted that the `aCE` and `bCE` docstrings swapped "partial numerator" and "partial
denominator". Under this library's convention, the continued fraction is `K(b_n / a_n)` and
the recurrence is `X (n+2) = a (n+1) X (n+1) + b (n+1) X n`, so `a` holds the partial
denominators and `b` the partial numerators. The docstrings are corrected on this branch.

This branch combines the cleanup, `ReviewedProblem21.lean`, and the hardened verifier and CI.
The theorem name list in `scripts/config.json` covers all 132 public theorems. License
headers for a possible Mathlib submission are not added yet.
