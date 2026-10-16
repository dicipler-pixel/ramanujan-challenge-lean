# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* **No limit is formalised.** The challenge asks for the values π, γ, π + e, Catalan's G and
  ζ(2) + ζ(3). None of those limits is proved in this library. The theorems here are the exact
  algebra that the submissions established: Casoratian and determinant identities, a Pochhammer
  product, polynomial and matrix identities, a partial-fraction decomposition and the rational
  constant it produces.
* **Problem 2.1.** The telescoping series for the continued fraction is set up (the determinant
  identity and the convergent difference), the partial products of `b_n` are given in closed
  form for every `n`, and Pincherle's theorem is proved in the direction needed: a minimal
  solution with `Z 0 ≠ 0` forces `P_n/Q_n → a_0 − Z_1/Z_0`. What is still missing for
  `6/(3−π)`: that the specific `₂F₁` solution is minimal (Poincaré–Perron with the root ratio
  `|λ_s/λ_d| < 1`), the limits of the rescaled coefficients, and Euler's integral giving the
  anchors `F_1`, `F_2`.
* **The Technion skeleton's Pincherle statement is false as written.** Their
  `Code/2.1/LeanFormal/PiPCF.lean` defines a minimal solution by `Z n / D n → 0` only; with
  Lean's convention `x / 0 = 0` a dominant solution vanishing at infinitely many indices passes
  that test, and then the convergents need not converge. `technion_pincherle_fails` exhibits
  explicit period-2 coefficients for which all of their hypotheses hold and the conclusion is
  false. The corrected definition (`IsMinimal`) adds `∀ᶠ n, D n ≠ 0`; their extra hypothesis
  `b n ≠ 0` is not needed for this direction. Their skeleton's remaining `sorry`s
  (`A_limit`, `B_limit`, `poincare_perron`, `euler_integral`, `F_growth`, `minimal_F`,
  `minimal_X`, `F_one`, `F_two`) stay open here too.
* **Problem 2.2.** The telescoping identity, the companion determinant, the Casoratian ratio and
  its closed-form product are proved. Nothing about `γ`: the recurrence operator is irreducible
  over `ℚ(n)` (Sage, August 2026) and no closed form for `q_n` is known.
* **Problem 2.3.** Only the algebra of the characteristic roots `√2 ± 1`.
* **Problem 2.4.** Nothing yet. The order-4, degree-10 recurrence for `T(m) = Σ_k C(m,k)² H_k²`
  was found by guessing (`ore_algebra`, exact to `m = 89`) and needs a creative-telescoping
  certificate before it can be stated for all `m`. The order-2 recurrence that creative telescoping
  produced in August 2026, `(m+2)³T(m+2) − 2(2m+3)(2m²+6m+5)T(m+1) + 4(m+1)(2m+1)(2m+3)T(m) = 0`,
  does **not** hold for the bounded sum (it fails at every `m` from 0 to 5; the boundary terms of
  the variable-range sum were never compensated), so it is not stated here.
* **Problem 2.5.** The relations among the leading-order matrices `L, B, C` of `M(n)` and the
  algebra of Zudilin's characteristic roots are proved. The five-dimensionality of the algebra
  `L, B, C` generate, and the proven interval for `G` with the convergents inside it, are not yet
  formalised. The open proof route from August 2026: with the reverse-order product
  `M_N = M(N−1)⋯M(1)M(0)`, the matrix ratios `P_N/Q_N` agree with Zudilin's `v_n/u_n → G` to 15+
  digits by `N = 7–11`; an order-3 scalar companion recurrence was extracted from `M(n)` by a
  Krylov coboundary; the decisive test — whether that order-3 operator has Zudilin's order-2
  operator as a right factor up to gauge — has not been run. Nothing about `G` itself is proved.
* **Problem 2.6.** The operator factorisation `L_c = M₂ · R₂` is proved coefficient by coefficient,
  with the hypergeometric term ratio of the partial-sum operator's middle factor. The partial
  fractions of the rational solution `r(n)` of its top factor and the rational part of `Σ r(n)` are
  proved; `Σ r(n) = π²/84 − 547/7200` itself needs `ζ(2) = π²/6` and a shifted tail and is not yet
  here. One correction to the submission's own framing, found in the August review: `Σ r(n)` is
  **not** one of the three limits that assemble `S_∞` — the verified connection formula uses
  `{1, Σ h, p₃(∞)}` with `α = u₁`, `β = u₂`, `γ = −21/2` — so `r` belongs to the structure of the
  operator, not to the evaluation of the sum. The one open constant `p₃(∞) = 0.000632226574…` has
  no closed form in `{1, π², ζ(3), log 2}` (PSLQ at 60 and 90 digits), and the second basis
  solution `v₂ = w₂ t₂` and the three-layer connection formula are not yet formalised.
