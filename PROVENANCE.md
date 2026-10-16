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
that pre-check is `scripts/precheck.py`.
