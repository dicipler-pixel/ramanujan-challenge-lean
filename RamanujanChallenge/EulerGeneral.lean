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

/-! General real Euler representation on the open unit disk.
Independent Codex edition; helper proofs adapted from Euler21.lean.
-/
open Filter Topology MeasureTheory

namespace EulerIntegralReview

/-- The real Beta integral. -/
theorem beta_integral_real {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ x in (0:ℝ)..1, x ^ (p - 1) * (1 - x) ^ (q - 1) =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (p : ℂ)) (t := (q : ℂ))
    (by simpa using hp) (by simpa using hq)
  have hG : Real.Gamma (p + q) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hI : Complex.betaIntegral p q =
      ((∫ x in (0:ℝ)..1, x ^ (p - 1) * (1 - x) ^ (q - 1) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hx
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1, Complex.ofReal_cpow (by linarith [hx.2])]
    push_cast; ring_nf
  rw [hI, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal] at hB
  have := hB
  norm_cast at this
  rw [eq_div_iff hG, mul_comm]
  exact this.symm

/-- `Γ(x + k) = (x)_k Γ(x)` for `x > 0`. -/
theorem Gamma_add_nat_real {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Real.Gamma (x + k) = (ascPochhammer ℝ k).eval x * Real.Gamma x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one (by positivity), ih, ascPochhammer_succ_eval]
    ring

/-- The binomial series `(1 − y)^{−a} = Σ (a)_k y^k / k!` for `|y| < 1`. -/
theorem hasSum_one_div_one_sub_rpow (a : ℝ) {y : ℝ} (hy : |y| < 1) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k).eval a * y ^ k)
      (1 / (1 - y) ^ a) := by
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum
    (y := y) (by
      have h1 : ‖y‖₊ < 1 := by rw [← NNReal.coe_lt_coe]; simpa using hy
      simpa [enorm_eq_nnnorm] using h1)
  simp only [zero_add] at h
  convert h using 1
  funext k
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, Ring.choose_eq_smul,
    Polynomial.descPochhammer_smeval_eq_ascPochhammer, Polynomial.ascPochhammer_smeval_eq_eval]
  rw [show a + k - 1 - k + 1 = a by ring]
  simp [smul_eq_mul, mul_comm]

noncomputable def weight (b q t : ℝ) : ℝ := t ^ (b - 1) * (1 - t) ^ (q - 1)

noncomputable def term (a b q z : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ((k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k).eval a * (z * t) ^ k * weight b q t

theorem weight_nonneg (b q : ℝ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ weight b q t :=
  mul_nonneg (Real.rpow_nonneg h0 _) (Real.rpow_nonneg (sub_nonneg.mpr h1) _)

theorem abs_pochhammer_le (a : ℝ) (k : ℕ) :
    |(ascPochhammer ℝ k).eval a| ≤ (ascPochhammer ℝ k).eval (|a| + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, abs_mul]
    apply mul_le_mul ih _ (abs_nonneg _) (le_of_lt (ascPochhammer_pos k _ (by positivity)))
    calc
      |a + (k : ℝ)| ≤ |a| + |(k : ℝ)| := abs_add_le _ _
      _ ≤ |a| + 1 + k := by simp only [abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k)]; linarith

theorem abs_mul_lt_one {z t : ℝ} (hz : |z| < 1) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |z * t| < 1 := by
  rw [abs_mul, abs_of_nonneg h0]
  exact (mul_le_of_le_one_right (abs_nonneg z) h1).trans_lt hz

theorem hasSum_term (a b q : ℝ) {z t : ℝ} (hz : |z| < 1)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    HasSum (fun k => term a b q z k t) (weight b q t * (1 / (1 - z*t)^a)) := by
  have h := (hasSum_one_div_one_sub_rpow a (abs_mul_lt_one hz h0 h1)).mul_right (weight b q t)
  simpa only [term, mul_comm (1 / (1 - z*t)^a)] using h

theorem norm_term_le (a b q z : ℝ) (k : ℕ) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ‖term a b q z k t‖ ≤ term (|a| + 1) b q |z| k t := by
  have hw := weight_nonneg b q h0 h1
  simp only [term, Real.norm_eq_abs, abs_mul, abs_inv, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg k.factorial : (0:ℝ) ≤ k.factorial), abs_of_nonneg h0, abs_of_nonneg hw]
  gcongr
  exact abs_pochhammer_le a k

/-- The endpoint-singular real Beta weight is integrable. -/
theorem weight_integrable {b q : ℝ} (hb : 0 < b) (hq : 0 < q) :
    IntervalIntegrable (weight b q) volume 0 1 := by
  have h := (Complex.betaIntegral_convergent (u := b) (v := q) (by simpa) (by simpa)).norm
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 <|
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 h).congr_fun (fun t ht => ?_)
      measurableSet_Ioc
  have he : ((weight b q t : ℝ) : ℂ) =
      (t : ℂ)^((b : ℂ)-1) * (1-(t : ℂ))^((q : ℂ)-1) := by
    unfold weight
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1.le,
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2)]
    push_cast
    rfl
  dsimp only
  rw [← he, Complex.norm_real, Real.norm_of_nonneg (weight_nonneg b q ht.1.le ht.2)]

theorem kernel_continuous (a : ℝ) {z : ℝ} (hz : |z| < 1) :
    ContinuousOn (fun t : ℝ => 1 / (1-z*t)^a) (Set.uIcc 0 1) := by
  have hp : ∀ t ∈ Set.uIcc (0:ℝ) 1, 0 < 1-z*t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h := abs_mul_lt_one hz ht.1 ht.2
    linarith [le_abs_self (z*t)]
  refine ContinuousOn.div continuousOn_const ?_ ?_
  · exact ContinuousOn.rpow_const (by fun_prop) (fun t ht => Or.inl (hp t ht).ne')
  · intro t ht
    exact (Real.rpow_pos_of_pos (hp t ht) a).ne'

/-- Absolute domination, including negative a and z and singular Beta endpoints. -/
theorem hasSum_integral_term (a : ℝ) {b q z : ℝ}
    (hb : 0 < b) (hq : 0 < q) (hz : |z| < 1) :
    HasSum (fun k => ∫ t in (0:ℝ)..1, term a b q z k t)
      (∫ t in (0:ℝ)..1, weight b q t * (1 / (1-z*t)^a)) := by
  have hmem : ∀ t ∈ Set.uIoc (0:ℝ) 1, 0 ≤ t ∧ t ≤ 1 := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    exact ⟨ht.1.le, ht.2⟩
  have hz' : |(|z|)| < 1 := by simpa using hz
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k t => term (|a|+1) b q |z| k t) ?_ ?_ ?_ ?_ ?_
  · intro k
    unfold term weight
    fun_prop
  · intro k
    exact Filter.Eventually.of_forall fun t ht => norm_term_le a b q z k (hmem t ht).1 (hmem t ht).2
  · exact Filter.Eventually.of_forall fun t ht =>
      (hasSum_term (|a|+1) b q hz' (hmem t ht).1 (hmem t ht).2).summable
  · refine ((weight_integrable hb hq).mul_continuousOn (kernel_continuous (|a|+1) hz')).congr ?_
    intro t ht
    exact (hasSum_term (|a|+1) b q hz' (hmem t ht).1 (hmem t ht).2).tsum_eq.symm
  · exact Filter.Eventually.of_forall fun t ht => hasSum_term a b q hz (hmem t ht).1 (hmem t ht).2

theorem integral_term (a z : ℝ) {b q : ℝ} (hb : 0 < b) (hq : 0 < q) (k : ℕ) :
    ∫ t in (0:ℝ)..1, term a b q z k t =
      ((k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k).eval a * z^k *
        (Real.Gamma (b+k) * Real.Gamma q / Real.Gamma (b+q+k)) := by
  have hi : ∫ t in (0:ℝ)..1, term a b q z k t =
      ((k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k).eval a * z^k *
        ∫ t in (0:ℝ)..1, t^(b+k-1) * (1-t)^(q-1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have he : t^(b+k-1) = t^(b-1) * t^k := by
      rw [show b+(k:ℝ)-1 = (b-1)+k by ring, Real.rpow_add ht.1, Real.rpow_natCast]
    rw [he]
    unfold term weight
    rw [mul_pow]
    ring
  rw [hi, beta_integral_real (by positivity : 0 < b+(k:ℝ)) hq]
  congr 3
  ring

/-- Euler's integral for Mathlib's real Gaussian hypergeometric function. -/
theorem ordinaryHypergeometric_eq_integral (a : ℝ) {b c z : ℝ}
    (hb : 0 < b) (hbc : b < c) (hz : |z| < 1) :
    ordinaryHypergeometric a b c z =
      Real.Gamma c / (Real.Gamma b * Real.Gamma (c-b)) *
        ∫ t in (0:ℝ)..1, t^(b-1) * (1-t)^(c-b-1) * (1 / (1-z*t)^a) := by
  have hq : 0 < c-b := sub_pos.mpr hbc
  have hc : 0 < c := hb.trans hbc
  have hGb := (Real.Gamma_pos_of_pos hb).ne'
  have hGq := (Real.Gamma_pos_of_pos hq).ne'
  have hGc := (Real.Gamma_pos_of_pos hc).ne'
  have hS := (hasSum_integral_term a hb hq hz).mul_left
    (Real.Gamma c / (Real.Gamma b * Real.Gamma (c-b)))
  rw [ordinaryHypergeometric_eq_tsum]
  apply HasSum.tsum_eq
  convert hS using 1
  · funext k
    rw [integral_term a z hb hq]
    rw [show b+(c-b)+(k:ℝ) = c+k by ring, Gamma_add_nat_real hb, Gamma_add_nat_real hc]
    have hAc : (ascPochhammer ℝ k).eval c ≠ 0 := (ascPochhammer_pos k c hc).ne'
    simp only [smul_eq_mul]
    field_simp
  · rfl

/-- The Euler integrand is integrable despite its possible endpoint singularities. -/
theorem euler_integrand_intervalIntegrable (a : ℝ) {b c z : ℝ}
    (hb : 0 < b) (hbc : b < c) (hz : |z| < 1) :
    IntervalIntegrable (fun t : ℝ => t^(b-1) * (1-t)^(c-b-1) * (1-z*t)^(-a))
      volume 0 1 := by
  have h := (weight_integrable hb (sub_pos.mpr hbc)).mul_continuousOn
    (kernel_continuous a hz)
  refine h.congr fun t ht => ?_
  rw [Set.uIoc_of_le zero_le_one] at ht
  have hp : 0 ≤ 1-z*t := by
    have hlt := abs_mul_lt_one hz ht.1.le ht.2
    linarith [le_abs_self (z*t)]
  simp only [weight, Real.rpow_neg hp, one_div]

/-- The conventional negative-exponent form of Euler's integral representation. -/
theorem ordinaryHypergeometric_eq_eulerIntegral (a : ℝ) {b c z : ℝ}
    (hb : 0 < b) (hbc : b < c) (hz : |z| < 1) :
    ordinaryHypergeometric a b c z =
      Real.Gamma c / (Real.Gamma b * Real.Gamma (c-b)) *
        ∫ t in (0:ℝ)..1, t^(b-1) * (1-t)^(c-b-1) * (1-z*t)^(-a) := by
  rw [ordinaryHypergeometric_eq_integral a hb hbc hz]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  have hp : 0 ≤ 1-z*t := by
    have hlt := abs_mul_lt_one hz ht.1 ht.2
    linarith [le_abs_self (z*t)]
  dsimp only
  rw [Real.rpow_neg hp, one_div]

end EulerIntegralReview
