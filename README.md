<div align="center">

# Ramanujan Challenge submissions — Lean proofs of the exact algebra

![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-132-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)

Jeromie Beasley

</div>

---

## The idea in one line

The Ramanujan Challenge (Technion, 2026) asks for proofs that six recurrences and continued
fractions converge to π, γ, π + e, Catalan's G and ζ(2) + ζ(3). My submissions established the
exact algebra around each one — determinant identities, a Pochhammer product, a telescoping
cubic, a nilpotent leading-order algebra, a partial-fraction decomposition — with high-precision
numerics for the limits. This library states that algebra and has the Lean kernel check it.
**Problem 2.1 is closed in full:** `pcf21_tendsto` proves that the continued fraction converges to
`6/(3 − π)`. The other challenge limits are not formalised; see [`LIMITATIONS.md`](LIMITATIONS.md).

## What is proved

| Problem | Result | Theorem |
| :--- | :--- | :--- |
| 2.1 | Casoratian step `W_{n+1} = −b_{n+2} W_n`; the determinant identity `A_{n+1}B_n − A_nB_{n+1} = (−1)^n (∏ b)(A_1B_0 − A_0B_1)` for every `n` | `casoratian_step`, `casoratian_closed` |
| 2.1 | Consecutive convergents differ by the Casoratian over `B_{n+1}B_n` | `convergent_difference` |
| 2.1 | `∏_{k=1}^{n} b_k = 25^n ((2n+1)!)² (1/5)_n (11/5)_n` for every `n` | `b1_succ_factor`, `pochhammer_product` |
| 2.2 | `P(n+1) = 8n³ + 75n² + 231n + 232` for the cubic factor `P` of `a_0`; the companion matrix has `det = −a_3/a_0`; the ratio `−a_3/a_0 = (n+1)(n+2)⁴(n+3)P(n+1)/P(n)` and its product `n!((n+1)!)⁴((n+2)!/2)P(n)/68` for every `n` (the Casoratian closed form) | `telescoping_factor`, `companion3_det`, `P22_pos`, `casoratian22_ratio`, `casoratian22_closed` |
| 2.3 | `(√2+1)(√2−1) = 1`; both are roots of `λ² − 2√2λ + 1` | `roots_reciprocal`, `rPlus_char`, `rMinus_char`, `sqrt2_sq` |
| 2.3 | `p_n`, `q_n` defined from the challenge recurrence; the kernel computes `p_5 = 730267195392`, `q_5 = 124622119440` | `p23_five` |
| 2.2 | `q_n` defined from the recurrence; `q_0, q_1, q_2 = 13056, 833400, 73876320` | `q22_values` |
| 2.5 | `φ² = φ + 1`, `φ⁵ = 5φ + 3`; `φ⁵` is a root of Zudilin's `x² − 11x − 1` and the roots have product `−1` | `sqrt5_sq`, `phi_sq`, `phi_pow5`, `zudilin_root`, `zudilin_product` |
| 2.5 | `L² = 0`, `LB = BL = 0`, `B² = −288L`, `B³ = 0`, `LC = −272L`, `CL = −16L` | `L_sq`, `L_mul_B`, `B_mul_L`, `B_sq`, `B_cube`, `L_mul_C`, `C_mul_L` |
| 2.6 | The recurrence operator factors exactly, `L_c = M₂ · R₂`, with `R₂ = (n² + 15n/2 + 14)S − (n²/4 + 3n/2 + 9/4)` and `M₂ = (−12n³ − 164n² − 740n − 1100)S + (12n³ + 140n² + 536n + 672)`; the hypergeometric piece's term ratio `(n+4)²/(4(n+5)(n+9/2))` | `factor_S2`, `factor_S1`, `factor_S0`, `h_ratio_cross` |
| 2.6 | `n³ + 14n² + 65n + 100 = (n+4)(n+5)²`; `r(n) = 1/(7(n+4)) − 1/(7(n+5)) + 1/(14(n+5)²)`; `1/35 − (1/14)(1 + 1/4 + 1/9 + 1/16 + 1/25) = −547/7200` (the rational part of `Σ r(n)`; `r` is the rational solution of the top factor of the partial-sum operator, not one of the three limits that assemble `S_∞`) | `r26_denom`, `r26_partial`, `r26_constant` |

| 2.1 | **Pincherle's theorem** (convergence direction): if `Z` is a minimal solution of the three-term recurrence with `Z 0 ≠ 0` and dominant companion `D` eventually nonzero, the convergents `P_n/Q_n` tend to `a_0 − Z_1/Z_0`. Also: the solution space is spanned by the convergent numerators and denominators; two solutions agreeing at 0 and 1 agree everywhere; with `b_n ≠ 0` an eventually-zero solution is zero | `pincherle`, `solution_eq_combo`, `solution_unique`, `solution_eq_mul_convDen`, `solution_eq_zero_of_eventually_zero` |
| 2.1 | Minimality from ratio limits: solutions with `Z(n+1)/Z(n) → λ_s`, `D(n+1)/D(n) → λ_d`, `|λ_s| < |λ_d|` make `Z` minimal (Mathlib's ratio test), so Pincherle applies; the 2.1 roots `λ_s = (−297+135√5)/4`, `λ_d = (−297−135√5)/4` of `λ² + (297/2)λ − 729/4`, with `λ_sλ_d = −729/4` and `|λ_s| < |λ_d|` | `isMinimal_of_ratio`, `pincherle_of_ratio`, `lamS_root`, `lamD_root`, `lamS_mul_lamD`, `abs_lamS_lt_abs_lamD` |
| 2.1 | The rescaled coefficients converge: `A(n) → −297/2`, `B(n) → 729/4` (the skeleton's `A_limit`, `B_limit`) | `A21_limit`, `B21_limit` |
| 2.1 | **Counterexample to the Technion skeleton's `pincherle` statement.** Their definition of minimal solution omits `D n ≠ 0` eventually; under Lean's `x / 0 = 0` the period-2 recurrence `a = 17/2, 0, …`, `b = −4, 1/4, …` with `Z_n = 2^{−n}` satisfies every hypothesis of their statement while the convergents `P_n/Q_n` are `0` at even `n` and tend to `8` at odd `n` | `zCE_isMinimalWeak`, `bCE_ne_zero`, `technion_pincherle_fails` |

| 2.1 | **The challenge limit: `P_n/Q_n → 6/(3 − π)`** for `a_n = −220n³−484n²−301n−42`, `b_n = 4n²(2n+1)²(5n−4)(5n+6)` | `pcf21_tendsto` |
| 2.1 | **Reviewed interface (Codex):** convergents indexed from the first actual one, `P 0 = −42`, `Q 0 = 1`, every `Q n ≠ 0`; the exact residual `P_n/Q_n − 6/(3−π) = (Z(n+1)/Q_n)/Z(0)`; the geometric bound `‖P_n/Q_n − 6/(3−π)‖ ≤ (300√2/Z(0))·(1/5)^n`; and the limit from that bound alone, without `pcf21_tendsto` or `pincherle` | `Reviewed.P_eq`, `Reviewed.Q_eq`, `Reviewed.Q_ne_zero`, `Reviewed.initial_values`, `Reviewed.value`, `Reviewed.error_identity`, `Reviewed.error_bound`, `Reviewed.limit` |
| 2.1 | Lemma 3 of the official proof: `F_{n+2} = A(n)F_{n+1} + B(n)F_n` for every `n ≥ 1`, for `F_n` given by Euler's integral (in the paper's substitution `t = 2u²/(1+u²)`). Proved by creative telescoping: an explicit antiderivative `Φ` with `Φ' = −2n(2n+1)(5n+6)ω_n + (220n³+484n²+301n+42)ω_{n+1} + 2(n+1)(2n+3)(5n+1)ω_{n+2}`, plus the Gamma-prefactor ratio | `hasDerivAt_Phi21`, `K21_rec`, `kap21_succ`, `F21_rec` |
| 2.1 | Lemma 7, the anchors: `F_1 = (15√2/2)(π − 3)`, `F_2 = (1155√2/8)(22 − 7π)` | `K21_zero`, `K21_one`, `F21_zero`, `F21_one` |
| 2.1 | **Euler's integral (Lemma 1) for the sequence:** `F_n` is Mathlib's `₂F₁(n+½, n+½; 3n+½; 1/2)`. The proof uses the real Beta integral, the binomial series, termwise integration (dominated convergence) and the change of variables `t = 2u²/(1+u²)`. In `₂F₁` form: Lemma 3, `₂F₁(3/2,3/2;7/2;1/2) = (15√2/2)(π−3)` and `₂F₁(5/2,5/2;13/2;1/2) = (1155√2/8)(22−7π)` | `F21_eq_hypergeometric`, `hypergeometric_eq_euler`, `E21_eq`, `beta_integral_real`, `hasSum_one_div_one_sub_rpow`, `hypergeometric21_rec`, `hypergeometric21_one`, `hypergeometric21_two` |
| 2.1 | Lemma 4, the rescaling: `r_nA(n) = a_n`, `r_nr_{n−1}B(n) = b_n`; `X_n = s_nF_{n+2}` solves the challenge recurrence | `r21_mul_A21`, `r21_mul_r21_mul_B21`, `Z21_isSolution` |
| 2.1 | Lemmas 5–6, minimality, by a direct dominance bound in place of Poincaré–Perron: `−A(x) ≥ 100`, the denominators alternate with `|Q_{k+1}| ≥ s_k·100^k`, `0 < F_n ≤ 15√2·20^{n−1}`, hence `|X/Q| ≤ 300√2·5^{−k}` | `negA21_ge`, `convDen21_bound`, `F21_pos`, `F21_le`, `Z21_div_convDen_le`, `Z21_isMinimal` |

| 2.6 | **`Σ_{n≥1} r(n) = π²/84 − 547/7200`** — the first limit in the library: the telescoping part sums to `1/35`, the `1/(14(n+5)²)` part to `(1/14)(ζ(2) − 5269/3600)` via Mathlib's `hasSum_zeta_two` | `r26_hasSum`, `hasSum_telescope`, `hasSum_inv_sq_shift` |

The exact algebra is in [`RamanujanChallenge/Exact.lean`](RamanujanChallenge/Exact.lean);
Pincherle's theorem and the counterexample are in
[`RamanujanChallenge/Pincherle.lean`](RamanujanChallenge/Pincherle.lean); the Problem 2.6 series is in
[`RamanujanChallenge/Series.lean`](RamanujanChallenge/Series.lean); the Problem 2.1 analysis and the
challenge limit are in [`RamanujanChallenge/Problem21.lean`](RamanujanChallenge/Problem21.lean), and Euler's
integral identifying `F_n` with Mathlib's `₂F₁` is in
[`RamanujanChallenge/Euler21.lean`](RamanujanChallenge/Euler21.lean). The reviewed interface and the
direct error-bound proof are in
[`RamanujanChallenge/ReviewedProblem21.lean`](RamanujanChallenge/ReviewedProblem21.lean); see
[`REVIEW.md`](REVIEW.md).

## How it is checked

Run `lake exe cache get`, then `python3 scripts/check_review.py` (do not run `lake update`; the
committed `lake-manifest.json` fixes the dependency set). It runs the verifier's regression tests,
builds every module against Lean v4.34.1 and Mathlib v4.34.1, replays each one in Lean's
independent kernel checker, audits the axioms of all 132 named theorems (only `propext`,
`Classical.choice`, `Quot.sound`), and requires six deliberately false statements to fail.
Evidence is written to `verification/`. [The workflow](.github/workflows/build.yml) runs the
same command; this merged copy has local evidence only and no hosted CI run.

Every identity was also checked symbolically before being written in Lean
([`scripts/precheck.py`](scripts/precheck.py), [`scripts/precheck2.py`](scripts/precheck2.py),
[`scripts/precheck3.py`](scripts/precheck3.py) for Problem 2.1's analysis).

## The challenge

The problems and their official proofs are the Ramanujan Machine group's: *Ramanujan Challenge
Proofs* (Technion, 2 August 2026), code at
[RamanujanMachine/RamanujanChallengeSolutions](https://github.com/RamanujanMachine/RamanujanChallengeSolutions).
Their repository carries a Lean skeleton for Problem 2.1 whose analytic steps are left as `sorry`
(still the case on 17 October 2026). `Problem21.lean` proves the challenge limit without them;
[`LIMITATIONS.md`](LIMITATIONS.md) says which of their statements are still not proved here.

## Licence

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
