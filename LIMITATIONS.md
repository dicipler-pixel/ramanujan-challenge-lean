# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* **No limit is formalised.** The challenge asks for the values π, γ, π + e, Catalan's G and
  ζ(2) + ζ(3). None of those limits is proved in this library. The theorems here are the exact
  algebra that the submissions established: Casoratian and determinant identities, a Pochhammer
  product, polynomial and matrix identities, a partial-fraction decomposition and the rational
  constant it produces.
* **Problem 2.1.** The telescoping series for the continued fraction is set up (the determinant
  identity and the convergent difference) and the partial products of `b_n` are given in closed
  form for every `n`; summing the series to `6/(3−π)` needs Pincherle's theorem, Poincaré–Perron
  and Euler's integral, which are not here. The Ramanujan Machine group's own Lean skeleton for
  this problem (`Code/2.1/LeanFormal/PiPCF.lean` in their solutions repository) proves the
  coboundary and rescaling identities and leaves those analytic steps as `sorry`; they are the
  natural next targets.
* **Problem 2.2.** Only the telescoping identity behind the Casoratian and the companion
  determinant are proved. Nothing about `γ`.
* **Problem 2.3.** Only the algebra of the characteristic roots `√2 ± 1`.
* **Problem 2.4.** Nothing yet. The order-4 recurrence for `Σ_k C(m,k)² H_k²` found by guessing in
  the submission needs a creative-telescoping certificate before it can be stated for all `m`.
* **Problem 2.5.** Only the relations among the leading-order matrices `L, B, C` of `M(n)`. The
  five-dimensionality of the algebra they generate, and the proven interval for `G` with the
  convergents inside it, are not yet formalised.
* **Problem 2.6.** The partial fractions of the rational solution `r(n)` and the rational part of
  its sum are proved; the sum itself, `π²/84 − 547/7200`, which needs `ζ(2) = π²/6` and a shifted
  tail, is not yet here, nor is the operator factorisation, whose explicit factors are not in the
  submission package.
