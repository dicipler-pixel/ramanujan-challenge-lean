# Euler integral: Grok Bot edition vs Codex edition, and the merge

Compared editions, both built on `phase2-cleanroom` (`f5c9e82`):
- **Grok Bot** `phase2-final-grok` at `b6a7961`, file `RamanujanChallenge/EulerIntegral.lean`, 178 lines.
- **Codex** `gpt-final-e977cf2` at `e977cf2`, file `RamanujanChallenge/EulerGeneral.lean`, 235 lines. It was imported unchanged from `euler-general_e977cf2.bundle`.

Grok Bot re-checked both on 18 October 2026 (Chicago time) with Lean v4.34.1 and Mathlib `d13f23b`, using the same local cache for each.

| | Grok Bot `b6a7961` | Codex `e977cf2` |
| :--- | :--- | :--- |
| Main statement | `ordinaryHypergeometric_eq_integral {a b c x : ℝ} (hb : 0 < b) (hbc : b < c) (hx : \|x\| < 1)`, with integrand `(1 - x * t) ^ (-a)` | The same mathematics, with `a` explicit. The main theorem uses `1 / (1 - z*t)^a`, and the conventional `(1-z*t)^(-a)` form is `ordinaryHypergeometric_eq_eulerIntegral` |
| Hypotheses | `0 < b < c`, `\|x\| < 1`, any real `a` | Same |
| Integrability theorem | None | `euler_integrand_intervalIntegrable` |
| Dependencies | Mathlib only, but `import Mathlib` | Mathlib only, with targeted imports |
| Real Beta integral | Private (`integral_beta`, `intervalIntegrable_beta`), so it doesn't clash with PR #44677 | Public `beta_integral_real` and `weight_integrable`, which duplicate #44677 and the same-named lemma in `Euler21.lean` |
| Pochhammer bound | `\|(a)ₖ\| ≤ (\|a\|)ₖ` | `\|(a)ₖ\| ≤ (\|a\|+1)ₖ`, which is looser |
| Public API | 5 theorems | 15 theorems and 2 public definitions (`weight`, `term`) with no docstrings |
| Namespace | `RamanujanChallenge` | `EulerIntegralReview` |
| Problem 2.1 | Re-derived as a corollary (`E21_eq_eulerIntegral`, `hypergeometric_eq_euler_of_general`) | Only an `example` showing that the family is in the theorem's domain. The library's 2.1 identity is not re-derived |
| Instance checks | None | Negative `a` and `z`, singular endpoints, the 2.1 family, and `a = z = 0` |
| False control | None new | `z = 0` normalization, which doesn't use the theorem |
| Integration | Inside `verify.py` / `check_review.py`, 152 names | A separate `check_euler_general.py` and `verification-euler/`, 161 names |
| Docs | README, LIMITATIONS, PROVENANCE, LICENSING and AI_USE updated, and placeholder wording removed | Only a new README section. LIMITATIONS still says Euler's integral is not general, and the README badge still uses the placeholder word |
| Build warnings | 0 | 0 |
| Axioms (main theorem) | propext, Classical.choice, Quot.sound | Same |
| Kernel replay | passed | passed |
| Standard lint set | clean | **1 warning**: line 101 is longer than 100 characters |
| `#lint` | clean | **2 errors** (docBlame on `weight` and `term`) |
| `lint-style` | clean | clean |
| Full `check_review.py` | passes | **fails** at the standard-lint step |
| Focused `check_euler_general.py` | n/a | passes (as claimed) |
| PiPCF.lean similarity | max 0.36, 0 shared lines | max 0.48, 0 shared lines |
| Licence header | yes | yes |

**Verdict.**
- The two proofs are mathematically equivalent, and both are correct.
- The Grok Bot edition is the better base. It's shorter, uses the tighter bound, keeps a smaller public API, re-derives the 2.1 corollary, and passes the full gate.
- The Codex edition does three things better: targeted imports, an integrability theorem, and instance checks.

**Merged branch `phase2-final-merged`.** Base `b6a7961`, plus:
- targeted imports (from Codex);
- `intervalIntegrable_eulerIntegrand` (after Codex's integrability theorem);
- `checks/EulerSpecializations.lean`, adapted from Codex's checks and run by `check_review.py` with warnings as errors;
- a new false control, `FalseControls/euler_prefactor_wrong.lean`: an inverted Gamma prefactor, run through the theorem, which reduces to the false `∫₀¹ (1 − t) dt = 0`.

That makes 153 theorems and 8 false controls. The Codex branch is kept unchanged as `gpt-final-e977cf2`.
