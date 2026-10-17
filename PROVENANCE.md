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

Every identity was checked in SymPy first (`scripts/precheck3.py`).
