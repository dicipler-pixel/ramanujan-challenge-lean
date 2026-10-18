# General real Euler integral — independent Codex edition

Base: recovered `phase2-cleanroom` at `f5c9e82`, kept on a separate branch.
New file: `RamanujanChallenge/EulerGeneral.lean`.

## Exact target

For arbitrary real `a`, real `b,c,z` satisfying `0 < b`, `b < c`, and `|z| < 1`:

```
ordinaryHypergeometric a b c z =
  Real.Gamma c / (Real.Gamma b * Real.Gamma (c-b)) *
    ∫ t in (0:ℝ)..1, t^(b-1) * (1-t)^(c-b-1) * (1-z*t)^(-a)
```

This is Mathlib's existing series-defined hypergeometric function, not an integral
introduced as a replacement definition. A separate theorem establishes interval
integrability. Negative `a`, negative `z`, `a=0`, `z=0`, and integrable singularities
at either endpoint are included. The boundary `|z|=1`, continuation to `z<-1`, and
complex parameters are not claimed.

## Argument

1. Use the real Beta integral, obtained from Mathlib's complex Beta/Gamma identity.
2. Expand `(1-z*t)^(-a)` using Mathlib's binomial power series.
3. Bound the absolute value of each rising factorial at `a` by its positive
   counterpart at `|a|+1`. Dominate signed terms at `z` by terms at `|z|`.
4. The majorant sums to a continuous bounded kernel times an integrable Beta
   weight. Apply dominated convergence for termwise integration.
5. Each integrated term is a Beta integral. Gamma recurrence gives the standard
   hypergeometric coefficients, including the correct Gamma prefactor.

## Existing work and attribution

The real Beta, Gamma-shift, and binomial helper proofs are adapted from the user's
existing `Euler21.lean`. The integrability bridge uses the complex Beta convergence
theorem, following the approach also present in Altabeh's Mathlib PR
https://github.com/leanprover-community/mathlib4/pull/44677
(head `940e138d01ff07fe681cd877eec502136a2dc7c0`, open when checked).
The proposed upstream real Beta API can replace the local bridge once available
on the chosen Mathlib version. This edition does not claim invention of the Beta
integral or a general hypergeometric contribution already made by others.

## Comparison with Grok's independent edition

Compare theorem statements before comparing proof length:

- Does the result refer to Mathlib's `ordinaryHypergeometric`?
- Are `a` and `z` allowed to be negative?
- Are `0<b<1` and `0<c-b<1` handled without assuming continuity at endpoints?
- Is the normalizing Gamma quotient proved, with nonzero denominators justified?
- Is the integral proved integrable?
- Does the proof specialize to the original 2.1 family?
- Are every new theorem's axioms checked and warnings rejected?
- Are dependencies pinned and unmodified?

No edits have been made to Grok's version or the prior challenge proof files.
No public messages, emails, pushes, or PRs are part of this local development.

## Validation status

**Passed on 2026-10-18, Lean v4.34.1, Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`.**

- The new module builds and passes a fresh source check with warnings as errors.
- All 15 named declarations pass the axiom audit; the union is only
  `Classical.choice`, `Quot.sound`, and `propext`.
- Independent `leanchecker` replay passed.
- Three specialization checks passed: negative a/z with singular endpoints,
  the Problem 2.1 parameter family, and a=z=0 integrability.
- The deliberately false normalization at z=0 was rejected with an unsolved goal.
- The dependency manifest was unchanged; dependency source checkouts are unmodified.

Run `python3 scripts/check_euler_general.py` after fetching the cache. Evidence is
in `verification-euler/report.json` and its accompanying logs. The full repository
inventory is updated from 146 to 161; this focused run certifies the 15 new-module
declarations, not a fresh replay of the 146 unchanged declarations.

The execution environment needed an external process-path compatibility shim for
the official Lean binaries. No compiler, kernel, Mathlib source, or proof checks
were modified. The shim is not needed by the normal reproduction command.

CI now includes the general-module specialization checks, but this local branch
has not been pushed and the edited workflow has not yet run on GitHub.
