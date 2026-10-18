# Similarity of the library to the Technion's `PiPCF.lean`

Compared file: `RamanujanMachine/RamanujanChallengeSolutions`, `Code/2.1/LeanFormal/LeanFormal/PiPCF.lean`
(branch `main`, fetched 17 October 2026 after the rewrite was written, SHA-256
`b82635f6f2064e8f6933d5ebe3d5ad60b2814260f37b0ff7a980480aa16e35ef`, 311 lines, 59 declarations).
The file itself is not included here.

Method (`scripts/similarity_pipcf.py`, raw data in `similarity_PiPCF.json`): comments stripped, each top-level declaration
tokenised; for each of ours, the best `difflib` ratio of its token sequence against any PiPCF declaration
(**token**), the same with identifiers replaced by a placeholder (**structure**), and the count of
whitespace-normalised lines of 12 or more characters that occur verbatim in PiPCF.lean (**shared lines**).
Short unrelated declarations (for example the Problem 2.3 and 2.6 coefficient polynomials) score
0.5–0.65 against some PiPCF declaration, so that range is the noise floor for one-line formulas.

## Per file

| File | Decls (before → after) | Max token sim before | Max token sim after | Shared lines before | Shared lines after |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `Exact.lean` | 71 → 71 | 1.00 (`lamS_pos`) | 0.93 (`b1`) | 13 | 0 |
| `Pincherle.lean` | 37 → 43 | 0.98 (`A21`) | 0.63 (`CFData.transfer`) | 5 | 0 |
| `Series.lean` | 7 → 7 | 0.57 (`r26Term_eq`) | 0.57 (`r26Term_eq`) | 0 | 0 |
| `Problem21.lean` | 49 → 58 | 0.97 (`r21`) | 0.91 (`r21`) | 0 | 0 |
| `Euler21.lean` | 22 → 22 | 0.65 (`F21_eq_hypergeometric`) | 0.65 (`F21_eq_hypergeometric`) | 0 | 0 |
| `ReviewedProblem21.lean` | 12 → 12 | 0.82 (`b`) | 0.82 (`b`) | 0 | 0 |

## The replaced declarations

| Before (31a2bb3) | token | structure | shared lines | After (approximate counterpart) | token | structure | shared lines |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `lamS` | 0.97 | 0.97 | 0/1 | `subdominantRoot21` | 0.72 | 0.77 | 0/1 |
| `lamD` | 0.97 | 0.97 | 0/1 | `dominantRoot21` | 0.72 | 0.77 | 0/1 |
| `lamS_root` | 0.93 | 0.93 | 1/3 | `charPoly21_eq_zero_iff` | 0.36 | 0.45 | 0/3 |
| `lamD_root` | 0.93 | 0.93 | 1/3 | `discrim_charPoly21` | 0.43 | 0.52 | 0/4 |
| `lamS_mul_lamD` | 0.79 | 0.83 | 2/4 | `subdominantRoot21_mul_dominantRoot21` | 0.57 | 0.67 | 0/4 |
| `lamS_pos` | 1.00 | 1.00 | 3/3 | `dominantRoot21_neg_and_subdominantRoot21_pos` | 0.34 | 0.44 | 0/10 |
| `lamD_neg` | 1.00 | 1.00 | 2/2 | `subdominantRoot21_add_dominantRoot21` | 0.45 | 0.65 | 0/2 |
| `abs_lamS_lt_abs_lamD` | 1.00 | 1.00 | 4/4 | `abs_subdominantRoot21_lt_abs_dominantRoot21` | 0.60 | 0.79 | 0/5 |
| `IsSolution` | 0.92 | 1.00 | 0/2 | `CFData.Satisfies` | 0.46 | 0.67 | 0/2 |
| `IsSolution` | 0.92 | 1.00 | 0/2 | `CFData.mem_solutions` | 0.55 | 0.85 | 0/3 |
| `convNum` | 0.84 | 1.00 | 0/2 | `CFData.numer` | 0.48 | 0.59 | 0/1 |
| `convDen` | 0.86 | 1.00 | 0/2 | `CFData.denom` | 0.53 | 0.60 | 0/1 |
| `IsMinimal` | 0.82 | 0.91 | 0/3 | `CFData.IsRecessive` | 0.35 | 0.62 | 0/2 |
| `IsMinimalWeak` | 0.89 | 1.00 | 1/3 | `pincherle_needs_eventually_ne_zero` | 0.20 | 0.35 | 0/19 |
| `pincherle` | 0.17 | 0.18 | 0/43 | `CFData.tendsto_convergent` | 0.19 | 0.31 | 0/38 |
| `A21` | 0.98 | 0.99 | 2/3 | `midCoeff21` | 0.88 | 0.91 | 0/1 |
| `B21` | 0.98 | 0.99 | 2/3 | `tailCoeff21` | 0.84 | 0.87 | 0/2 |
| `r21` | 0.97 | 0.99 | 0/2 | `r21` | 0.91 | 0.92 | 0/2 |

## Highest remaining token similarities (after)

| File | Declaration | token | closest PiPCF decl | structure | shared lines |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `Exact` | `b1` | 0.93 | `b` | 0.95 | 0/1 |
| `Problem21` | `r21` | 0.91 | `r` | 0.92 | 0/2 |
| `Exact` | `a1` | 0.90 | `a` | 0.93 | 0/1 |
| `Problem21` | `midCoeff21` | 0.88 | `a` | 0.91 | 0/1 |
| `Problem21` | `tailCoeff21` | 0.84 | `b` | 0.87 | 0/2 |
| `ReviewedProblem21` | `b` | 0.82 | `b` | 0.93 | 0/1 |
| `Exact` | `m1` | 0.76 | `a` | 0.79 | 0/1 |
| `ReviewedProblem21` | `a` | 0.73 | `a` | 0.85 | 0/1 |
| `Exact` | `subdominantRoot21` | 0.72 | `lamS` | 0.77 | 0/1 |
| `Exact` | `dominantRoot21` | 0.72 | `lamD` | 0.77 | 0/1 |
| `ReviewedProblem21` | `Q` | 0.72 | `convDen` | 0.83 | 0/2 |
| `Problem21` | `b21` | 0.69 | `b` | 0.81 | 0/2 |
| `Problem21` | `F21_one` | 0.67 | `F_two` | 0.81 | 0/2 |
| `ReviewedProblem21` | `P` | 0.66 | `convDen` | 0.75 | 0/3 |
| `Euler21` | `F21_eq_hypergeometric` | 0.65 | `F` | 0.74 | 0/4 |

The top entries are one-line formulas that state the same mathematics: the challenge's own
coefficients `a_n`, `b_n` (`a1`, `b1`, `a21`, `b21`, `Reviewed.a`, `Reviewed.b`), the paper's
normaliser `r_n` of Eq. (21) (`r21`, now written in regrouped form), and the quotients
`midCoeff21 = a/r`, `tailCoeff21 = b/(r·r(·−1))`, which contain those polynomials. No declaration
in any of the six files shares a line with PiPCF.lean.
