# Provenance

`RamanujanChallenge/Exact.lean` and the three files in `FalseControls/` were written for this
repository from Jeromie Beasley's Ramanujan Challenge submission packages for Problems 2.1–2.6
(final cuts of 31 July – 1 August 2026: `Problem_2_1`, `Problem_2_2`, `Problem_2_3`,
`Problem_2_4`, `Problem_2_5_fixed`, `Problem_2_6`), each of which carries its own verification
scripts (`verify_*.py`). Earlier iterations of the same packages (24–31 July 2026) are kept in
the author's archive; nothing in them is absent from the final cuts.

The problems themselves are the Ramanujan Machine group's (Technion), published in *Ramanujan
Challenge Proofs* (2 August 2026) with code at
https://github.com/RamanujanMachine/RamanujanChallengeSolutions. The matrices `L, B, C` of
Problem 2.5 are the `n⁹, n⁸, n⁷` coefficients of the challenge's own `M(n)`, recomputed from the
published entries before being stated here.

Every identity in `Exact.lean` was checked symbolically (SymPy) before being written in Lean;
the pre-checks are `scripts/precheck.py` (phase 1) and `scripts/precheck2.py` (phase 2: the 2.2
Casoratian closed form, the 2.6 operator factorisation and term ratio, and the negative test of
the 2.4 order-2 recurrence). The explicit factors `R₂`, `M₂` of Problem 2.6 come from the
author's Sage `quo_rem` computation of August 2026 and are re-verified by `precheck2.py`.

`RamanujanChallenge/Problem21.lean` (17 October 2026) follows §4 of *Ramanujan Challenge
Proofs* (2 August 2026). It uses the trajectory `(1,1,3)`, Lemma 3's coefficients `A(n)`, `B(n)`
(Eqs. 14–15), the normalisation `r_n`, `s_n` (Eqs. 21–24), Euler's integral (Eq. 28) in the
paper's substitution `t = 2u²/(1+u²)` (Eqs. 36–37), and the anchors of Lemma 7. Two pieces are
new here:
* the telescoping certificate `Φ`, found by a SymPy ansatz `R = u(1−u²)P(u²)/(1+u²)³`;
* the dominance bound that replaces Poincaré–Perron.

`RamanujanChallenge/Euler21.lean` proves Euler's integral (the paper's Lemma 1) for these
parameters, the classical way: Beta integrals, the binomial series, termwise integration.

Every identity was checked in SymPy first (`scripts/precheck3.py`).

## Codex review edition and merge (18 October 2026 UTC)

At the author's request, Codex added `ReviewedProblem21.lean`: the explicit convergent
interface starting at the first actual convergent `-42`, a residual identity, a geometric
error bound `(300√2 / Z21 0)·(1/5)^n`, and a limit proof from that bound that does not invoke
`pcf21_tendsto` or `pincherle`. These additions depend on the original proof lemmas; they are
not a claim of an independent discovery or a new proof of all six problems. Codex also
hardened the verifier (exact name inventory, nested-comment handling, stricter false-control
rules, no stale reports) and the CI (committed lockfile, no `lake update`). Its review records
are in `REVIEW.md`.

This branch merges that edition into the Grok Bot style cleanup (commit `7cebef4`). The five
original Lean files carry the cleanup; `ReviewedProblem21.lean` is Codex's file unchanged.

## Dual licence and Technion overlap (17 October 2026, Chicago time)

At the author's request the code was made dual-licensed, `MIT OR Apache-2.0`, and the
Mathlib-style Apache header (author: Jeromie Beasley) was added to `Series.lean`,
`Problem21.lean`, `Euler21.lean` and `ReviewedProblem21.lean`. Grok Bot, an AI agent working
for the author, made this change. `ReviewedProblem21.lean` was written by Codex (an AI tool)
for the author's review edition at his request. It is included under his name because it was
made for him and he directed it; the AI help is stated here and in `AI_USE.md`.

A line-by-line comparison with the Technion's GPL-3.0 skeleton
(`RamanujanMachine/RamanujanChallengeSolutions`, `Code/2.1/LeanFormal/LeanFormal/PiPCF.lean`)
found matching code in two files, both written on 16 October 2026 (phases 3a and 3c):

* `Exact.lean`: `lamS`, `lamD`, `lamS_root`, `lamD_root`, `lamS_pos`, `lamD_neg`,
  `abs_lamS_lt_abs_lamD` (same names and essentially the same proofs);
* `Pincherle.lean`: `IsSolution`, `convNum`, `convDen`, the skeleton's minimality definition
  (here `IsMinimalWeak`), the statement shape of `pincherle`, and the formulas `A21`, `B21`.

These two files were at first not relicensed. They have since been rewritten; see the next
section.

## Independent rewrite of the overlapping parts (17 October 2026, Chicago time)

At the author's request, Grok Bot (an AI agent working for him) replaced every declaration
listed above with independently designed definitions and proofs, on the local branch
`phase2-cleanroom` (from `phase2-dual-license`, commit `31a2bb3`). The rewrite was written from
the mathematics only: the three-term recurrence, its characteristic equation, Pincherle's
theorem and the paper's Eq. (21). The Technion file was not opened while the new code was
written. It was fetched once afterwards, only to measure similarity
(`audit/similarity_PiPCF.md`).

One limitation is stated plainly. The agent that wrote the rewrite had worked on this
repository earlier the same day, so it had seen the earlier (overlapping) versions of these
declarations. The new code therefore uses a deliberately different design rather than a
lightly edited one:

* **Recurrences (`Pincherle.lean`).** A structure `CFData` (partial denominators and numerators)
  replaces the pair of sequences. The recurrence is stated in transfer-matrix form
  (`CFData.transfer`, `CFData.Satisfies`), and the solutions form a submodule
  (`CFData.solutions`). The convergent numerators and denominators are orbits of the start
  vectors `![1, d₀]` and `![0, 1]` under the transfer matrices (`CFData.state`, `CFData.orbit`,
  `CFData.numer`, `CFData.denom`, `CFData.convergent`), not a two-step recursive definition.
* **Minimality.** `CFData.IsRecessive` asks for a dominating solution that is eventually
  nonzero, with `y =o[atTop] w` (Mathlib's little-o). The "not a scalar multiple" clause is
  dropped from the definition and proved instead (`CFData.IsRecessive.ne_smul`).
* **Pincherle (`CFData.tendsto_convergent`).** The proof is new: little-o algebra
  (`IsLittleO.right_isBigO_sub`, `isLittleO_const_smul_right`, `IsBigO.eq_zero_imp`,
  `IsLittleO.tendsto_div_nhds_zero`) in place of an explicit quotient computation.
* **Counterexample.** It is stated as an existence theorem over `CFData`
  (`pincherle_needs_eventually_ne_zero`), with the period-two fraction `altCF`. The skeleton's
  minimality definition is no longer restated anywhere.
* **Roots (`Exact.lean`).** The roots of `4x² + 594x − 729` come from Mathlib's quadratic
  formula (`quadratic_eq_zero_iff`, with `discrim_charPoly21`). Their order of moduli is proved
  through Vieta's sum and product (`subdominantRoot21_add_dominantRoot21`,
  `subdominantRoot21_mul_dominantRoot21`, `dominantRoot21_neg_and_subdominantRoot21_pos`,
  `abs_subdominantRoot21_lt_abs_dominantRoot21`).
* **Rescaled coefficients (`Problem21.lean`).** `midCoeff21 = a/r` and
  `tailCoeff21 = b/(r·r(·−1))` are defined as quotients by the normaliser, so Eq. (22) holds by
  construction. The factored formulas are no longer written out as definitions. Their limits
  (`tendsto_midCoeff21`, `tendsto_tailCoeff21`) are proved by scaling numerator and normaliser
  by `n³` (`n⁶`). `r21` is written in a regrouped form `(8/3)((x+1)(2x+3))²(5x+1)/((6x+7)(6x+11))`.

Everything downstream (`Problem21.lean`, `Euler21.lean`, `ReviewedProblem21.lean`) was re-derived
against the new interface, and the main statements keep their meaning: `pcf21_tendsto`
(convergents `cf21.numer n / cf21.denom n → 6/(3 − π)`), `F21_eq_hypergeometric`,
`hypergeometric21_rec`, `Reviewed.error_bound` and `Reviewed.limit`. After the rewrite, all six
library files carry the Apache header, and the GPL exception was removed from `LICENSE` and
`LICENSING.md`.

The similarity measurement (per declaration, token sequence and verbatim lines, against
`PiPCF.lean` at SHA-256 `b82635f6…16e35ef`) found no shared line of 12 or more characters in any
of the six files (previously 13 in `Exact.lean` and 5 in `Pincherle.lean`). The highest
token similarities left are short formula definitions that encode the same mathematics: the
challenge's `a_n`, `b_n` (`a1`, `b1`, `a21`, `b21`, `Reviewed.a`, `Reviewed.b`), the paper's
`r_n` (`r21`), and the quotients `midCoeff21`, `tailCoeff21` that contain `a_n` and `b_n`.
Details are in `audit/similarity_PiPCF.md`.
