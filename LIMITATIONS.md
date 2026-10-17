# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* **Two limits are formalised.** `Σ_{n≥1} r(n) = π²/84 − 547/7200` for the Problem 2.6 rational
  solution (`Series.lean`, from Mathlib's `ζ(2) = π²/6`), and **the Problem 2.1 challenge limit
  `6/(3 − π)`** (`pcf21_tendsto` in `Problem21.lean`). The other four challenge limits (γ, π + e,
  Catalan's G, ζ(2) + ζ(3)) are not proved here; for those problems the theorems are the exact
  algebra the submissions established.
* **Problem 2.1 is closed, with one stated difference from the paper's wording.**
  `pcf21_tendsto` proves that the convergents `P_n/Q_n` of `a_n = −220n³−484n²−301n−42`,
  `b_n = 4n²(2n+1)²(5n−4)(5n+6)` tend to `6/(3 − π)`, with no `sorry` and only the three
  standard axioms. The four items this file used to list are done:
  1. coefficient limits `A(n) → −297/2`, `B(n) → 729/4`: `A21_limit`, `B21_limit` (`Pincherle.lean`);
  2. minimality of the hypergeometric solution: `Z21_isMinimal`. This is **not** proved through
     Poincaré–Perron or Stirling. It uses a direct dominance bound for this recurrence:
     `−A(x) ≥ 100` for `x ≥ 0` (`negA21_ge`), so the convergent denominators alternate in sign
     with `|Q_{k+1}| ≥ s_k·100^k` (`convDen21_bound`), while `0 < F_n ≤ 15√2·20^{n−1}`
     (`F21_pos`, `F21_le`). That is enough for `X/Q → 0` (`Z21_div_convDen_le`). The sharper
     statement `F_{n+1}/F_n → λ_s`, which the paper gets from Laplace's method plus
     Poincaré–Perron, is **not** formalised, and nothing needs it. General Poincaré–Perron is
     in neither Mathlib nor this library;
  3. the anchors `F_1 = (15√2/2)(π−3)`, `F_2 = (1155√2/8)(22−7π)`: `F21_zero`, `F21_one`;
  4. the limit itself: `pcf21_tendsto`, via `pincherle`.

  **The stated difference.** In `Problem21.lean`, `F_n` is *defined* by the paper's
  Euler-integral formula (Eq. 28), written in the paper's own substitution `t = 2u²/(1+u²)`
  (Eqs. 36–37):
  `F_n = Γ(3n+½)/(Γ(n+½)Γ(2n)) · 2^{n+3/2} ∫₀¹ u^{2n}(1−u²)^{2n−1}/(1+u²)^{2n} du`.
  Lemma 3 (the recurrence) is then proved for this sequence directly, by creative telescoping
  with an explicit certificate (`hasDerivAt_Phi21`, `K21_rec`). The challenge limit depends only
  on this sequence, so `pcf21_tendsto` is complete as stated. Two classical facts are **not**
  formalised:
  * Euler's integral identity (the paper's Lemma 1): this integral equals Mathlib's series
    `ordinaryHypergeometric (n+½) (n+½) (3n+½) (1/2)`;
  * the change of variables back to the `t`-form of Eq. 28.

  Mathlib has `₂F₁`, the Beta integral and the binomial series, but not Euler's integral for
  `₂F₁`. `scripts/precheck3.py` checks the substitution symbolically (SymPy, `n = 1…5`) and
  Euler's identity numerically against `mpmath.hyp2f1` (40 digits, `n = 1…5`); that is
  evidence, not a Lean proof. Neither fact is needed for `6/(3 − π)`.
* **The Technion skeleton's Pincherle statement is false as written.** Their
  `Code/2.1/LeanFormal/PiPCF.lean` defines a minimal solution by `Z n / D n → 0` only; with
  Lean's convention `x / 0 = 0` a dominant solution vanishing at infinitely many indices passes
  that test, and then the convergents need not converge. `technion_pincherle_fails` exhibits
  explicit period-2 coefficients for which all of their hypotheses hold and the conclusion is
  false. The corrected definition (`IsMinimal`) adds `∀ᶠ n, D n ≠ 0`; their extra hypothesis
  `b n ≠ 0` is not needed for this direction. Their skeleton's remaining `sorry`s
  (`A_limit`, `B_limit`, `poincare_perron`, `euler_integral`, `F_growth`, `minimal_F`,
  `minimal_X`, `F_one`, `F_two`) were checked on 17 October 2026 and are still open in their
  repository (last commit 2 August 2026). This library gets past each of them without their
  statements: `A21_limit`/`B21_limit`; `Z21_isMinimal` in place of `poincare_perron`, `F_growth`,
  `minimal_F`, `minimal_X`; `F21_zero`/`F21_one` in place of `F_one`/`F_two`. Their general
  `poincare_perron` and `euler_integral` statements are not proved here.
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
  proved, and `Σ_{n≥1} r(n) = π²/84 − 547/7200` is proved in `Series.lean` (`r26_hasSum`) from
  Mathlib's `hasSum_zeta_two`. One correction to the submission's own framing, found in the August review: `Σ r(n)` is
  **not** one of the three limits that assemble `S_∞` — the verified connection formula uses
  `{1, Σ h, p₃(∞)}` with `α = u₁`, `β = u₂`, `γ = −21/2` — so `r` belongs to the structure of the
  operator, not to the evaluation of the sum. The one open constant `p₃(∞) = 0.000632226574…` has
  no closed form in `{1, π², ζ(3), log 2}` (PSLQ at 60 and 90 digits), and the second basis
  solution `v₂ = w₂ t₂` and the three-layer connection formula are not yet formalised.
