/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Euler's integral representation of `₂F₁` (real parameters)

For real `a, b, c, x` with `0 < b < c` and `|x| < 1`,
$$ {}_2F_1(a, b; c; x) = \frac{\Gamma(c)}{\Gamma(b)\Gamma(c-b)}
  \int_0^1 t^{b-1}(1-t)^{c-b-1}(1-xt)^{-a}\,dt, $$
stated for Mathlib's `ordinaryHypergeometric` (`ordinaryHypergeometric_eq_integral`).

The proof is the classical one: expand `(1 - x t)^{-a}` by the binomial series, integrate term
by term (dominated convergence, with the bound `|(a)ₖ| ≤ (|a|)ₖ`), evaluate each term as a Beta
integral, and use `Γ(s + k) = (s)ₖ Γ(s)`. The integrand may be unbounded at either endpoint
(`b < 1` or `c - b < 1`); integrability comes from the convergence of the Beta integral.

`intervalIntegrable_eulerIntegrand` records that the integrand is integrable on `[0, 1]`.

This file depends only on Mathlib.
-/

open Filter Topology MeasureTheory intervalIntegral

namespace RamanujanChallenge

/-- The real Beta integrand is interval integrable on `[0, 1]` for positive exponents.
(Private; the same statement is proposed for Mathlib in PR #44677.) -/
private lemma intervalIntegrable_beta {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntervalIntegrable (fun t : ℝ => t ^ (p - 1) * (1 - t) ^ (q - 1)) volume 0 1 := by
  have h := (Complex.betaIntegral_convergent (u := p) (v := q) (by simpa) (by simpa)).norm
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 <|
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 h).congr_fun (fun t ht => ?_)
      measurableSet_Ioc
  have h1 : 0 ≤ 1 - t := sub_nonneg.2 ht.2
  have e : (t : ℂ) ^ ((p : ℂ) - 1) * (1 - (t : ℂ)) ^ ((q : ℂ) - 1) =
      ((t ^ (p - 1) * (1 - t) ^ (q - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1.le, Complex.ofReal_cpow h1]
    push_cast
    ring_nf
  dsimp only
  rw [e, Complex.norm_real, Real.norm_of_nonneg
    (mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg h1 _))]

/-- The real Beta integral `∫₀¹ t^{p−1}(1−t)^{q−1} dt = Γ(p)Γ(q)/Γ(p+q)`.
(Private; the same statement is proposed for Mathlib in PR #44677.) -/
private lemma integral_beta {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ t in (0:ℝ)..1, t ^ (p - 1) * (1 - t) ^ (q - 1) =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
  have hB := Complex.betaIntegral_eq_Gamma_mul_div p q (by simpa) (by simpa)
  have hI : Complex.betaIntegral p q =
      ((∫ t in (0:ℝ)..1, t ^ (p - 1) * (1 - t) ^ (q - 1) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le zero_le_one] at ht
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1, Complex.ofReal_cpow (by linarith [ht.2])]
    push_cast
    ring_nf
  rw [hI, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal] at hB
  exact_mod_cast hB

/-- `Γ(s + k) = (s)ₖ Γ(s)` for real `s > 0`. -/
theorem Gamma_add_nat_eq_ascPochhammer_mul {s : ℝ} (hs : 0 < s) (k : ℕ) :
    Real.Gamma (s + k) = (ascPochhammer ℝ k).eval s * Real.Gamma s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one (by positivity), ih,
      ascPochhammer_succ_eval]
    ring

/-- `|(a)ₖ| ≤ (|a|)ₖ`. -/
theorem abs_ascPochhammer_eval_le (a : ℝ) (k : ℕ) :
    |(ascPochhammer ℝ k).eval a| ≤ (ascPochhammer ℝ k).eval |a| := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, abs_mul]
    have h0 : 0 ≤ (ascPochhammer ℝ k).eval |a| := (abs_nonneg _).trans ih
    have h1 : |a + k| ≤ |a| + k := (abs_add_le _ _).trans (by simp)
    exact mul_le_mul ih h1 (abs_nonneg _) h0

/-- The binomial series `(1 − y)^{−a} = Σ (a)ₖ yᵏ / k!` for `|y| < 1`. -/
theorem hasSum_ascPochhammer_mul_pow (a : ℝ) {y : ℝ} (hy : |y| < 1) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k).eval a * y ^ k)
      ((1 - y) ^ (-a)) := by
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum
    (y := y) (by
      have h1 : ‖y‖₊ < 1 := by rw [← NNReal.coe_lt_coe]; simpa using hy
      simpa [enorm_eq_nnnorm] using h1)
  simp only [zero_add] at h
  have hy1 : 0 ≤ 1 - y := by linarith [(abs_lt.1 hy).2]
  rw [Real.rpow_neg hy1, ← one_div]
  convert h using 1
  funext k
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, Ring.choose_eq_smul,
    Polynomial.descPochhammer_smeval_eq_ascPochhammer, Polynomial.ascPochhammer_smeval_eq_eval]
  rw [show a + k - 1 - k + 1 = a by ring]
  simp [smul_eq_mul, mul_comm]

/-- Each term of the expanded Euler integrand is a Beta integral. -/
private lemma integral_term {a b c x : ℝ} (hb : 0 < b) (hbc : b < c) (k : ℕ) :
    ∫ t in (0:ℝ)..1, t ^ (b - 1) * (1 - t) ^ (c - b - 1) *
        (((k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k).eval a * (x * t) ^ k) =
      ((k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k).eval a * x ^ k *
        (Real.Gamma (b + k) * Real.Gamma (c - b) / Real.Gamma (c + k)) := by
  have hB := integral_beta (p := b + k) (q := c - b) (by positivity) (by linarith)
  rw [show b + k + (c - b) = c + k by ring] at hB
  rw [← hB, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
  rw [Set.uIoc_of_le zero_le_one] at ht
  rw [show b + k - 1 = b - 1 + k by ring, Real.rpow_add_natCast ht.1.ne', mul_pow]
  ring

/-- **Euler's integral representation of `₂F₁`** for real parameters: if `0 < b < c` and
`|x| < 1`, then
`₂F₁(a, b; c; x) = Γ(c) / (Γ(b) Γ(c − b)) * ∫₀¹ t^{b−1} (1−t)^{c−b−1} (1 − x t)^{−a} dt`. -/
theorem ordinaryHypergeometric_eq_integral {a b c x : ℝ} (hb : 0 < b) (hbc : b < c)
    (hx : |x| < 1) :
    ordinaryHypergeometric a b c x =
      Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) *
        ∫ t in (0:ℝ)..1, t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a) := by
  have hc : 0 < c := hb.trans hbc
  have hcb : 0 < c - b := sub_pos.2 hbc
  set w : ℝ → ℝ := fun t => t ^ (b - 1) * (1 - t) ^ (c - b - 1) with hw
  have hmem : ∀ t ∈ Set.uIoc (0:ℝ) 1, 0 < t ∧ t ≤ 1 := by
    intro t ht; rw [Set.uIoc_of_le zero_le_one] at ht; exact ht
  have hw0 : ∀ t ∈ Set.uIoc (0:ℝ) 1, 0 ≤ w t := fun t ht => by
    have := hmem t ht
    exact mul_nonneg (Real.rpow_nonneg this.1.le _) (Real.rpow_nonneg (by linarith) _)
  have hxa : |(|x|)| < 1 := by rwa [abs_abs]
  have hC := hasSum_ascPochhammer_mul_pow |a| hxa
  set F : ℕ → ℝ → ℝ := fun k t =>
    w t * (((k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k).eval a * (x * t) ^ k) with hF
  set bound : ℕ → ℝ → ℝ := fun k t =>
    w t * (((k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k).eval |a| * |x| ^ k) with hbound
  have hS : HasSum (fun k => ∫ t in (0:ℝ)..1, F k t)
      (∫ t in (0:ℝ)..1, t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence bound
      (fun k => ?_) (fun k => Eventually.of_forall fun t ht => ?_)
      (Eventually.of_forall fun t _ => (hC.mul_left (w t)).summable) ?_
      (Eventually.of_forall fun t ht => ?_)
    · exact Measurable.aestronglyMeasurable (by rw [hF, hw]; fun_prop)
    · obtain ⟨ht0, ht1⟩ := hmem t ht
      simp only [hF, hbound, Real.norm_eq_abs, abs_mul, abs_pow, abs_inv, Nat.abs_cast,
        abs_of_nonneg (hw0 t ht), abs_of_pos ht0]
      have hA := abs_ascPochhammer_eval_le a k
      gcongr
      · exact mul_nonneg (by positivity) ((abs_nonneg _).trans hA)
      · exact mul_le_of_le_one_right (abs_nonneg x) ht1
    · have he : (fun t => ∑' k, bound k t) = fun t => w t * (1 - |x|) ^ (-|a|) := by
        funext t; simp only [hbound]; rw [tsum_mul_left, hC.tsum_eq]
      rw [he]
      exact (intervalIntegrable_beta hb hcb).mul_const _
    · obtain ⟨ht0, ht1⟩ := hmem t ht
      have hxt : |x * t| < 1 := by
        rw [abs_mul, abs_of_pos ht0]
        exact lt_of_le_of_lt (mul_le_of_le_one_right (abs_nonneg x) ht1) hx
      exact (hasSum_ascPochhammer_mul_pow a hxt).mul_left (w t)
  have hGb := (Real.Gamma_pos_of_pos hb).ne'
  have hGc := (Real.Gamma_pos_of_pos hc).ne'
  have hGcb := (Real.Gamma_pos_of_pos hcb).ne'
  rw [ordinaryHypergeometric_eq_tsum]
  refine (HasSum.tsum_eq ?_)
  convert hS.mul_left (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) using 1
  funext k
  have hk : ∫ t in (0:ℝ)..1, F k t =
      ((k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k).eval a * x ^ k *
        (Real.Gamma (b + k) * Real.Gamma (c - b) / Real.Gamma (c + k)) :=
    integral_term hb hbc k
  rw [hk, smul_eq_mul, Gamma_add_nat_eq_ascPochhammer_mul hb,
    Gamma_add_nat_eq_ascPochhammer_mul hc]
  have hAc : (ascPochhammer ℝ k).eval c ≠ 0 := (ascPochhammer_pos k c hc).ne'
  field_simp

/-- The Euler integrand `t^{b−1}(1−t)^{c−b−1}(1 − x t)^{−a}` is interval integrable on `[0, 1]`
for `0 < b < c` and `|x| < 1`, although it may be unbounded at either endpoint. -/
theorem intervalIntegrable_eulerIntegrand (a : ℝ) {b c x : ℝ} (hb : 0 < b) (hbc : b < c)
    (hx : |x| < 1) :
    IntervalIntegrable (fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a))
      volume 0 1 := by
  have hpos : ∀ t ∈ Set.uIcc (0:ℝ) 1, 0 < 1 - x * t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h : |x * t| < 1 := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (abs_nonneg x) ht.2) hx
    linarith [le_abs_self (x * t)]
  have hk : ContinuousOn (fun t : ℝ => (1 - x * t) ^ (-a)) (Set.uIcc 0 1) :=
    ContinuousOn.rpow_const (by fun_prop) (fun t ht => Or.inl (hpos t ht).ne')
  exact (intervalIntegrable_beta hb (sub_pos.2 hbc)).mul_continuousOn hk

end RamanujanChallenge
