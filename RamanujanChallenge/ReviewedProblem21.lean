/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import RamanujanChallenge.Problem21

/-!
# Separate review interface for Problem 2.1

The coefficients and initial values below restate the continued fraction explicitly.
Index zero is its first convergent, -42; no zero-denominator dummy term is used.
This module depends on, and credits, the original proof. It is not an independent
derivation of the analytic lemmas. The error identity and bound expose its quantitative
content for checking and use.
-/

open Filter Topology

namespace RamanujanChallenge.Reviewed

/-- Partial denominators of the challenge continued fraction. -/
def a (n : ℕ) : ℝ := -220 * (n : ℝ)^3 - 484 * (n : ℝ)^2 - 301 * n - 42

/-- Partial numerators of the challenge continued fraction. -/
def b (n : ℕ) : ℝ := 4 * (n : ℝ)^2 * (2 * n + 1)^2 * (5 * n - 4) * (5 * n + 6)

/-- Numerators, starting with the convergent `a 0`. -/
def P : ℕ → ℝ
  | 0 => -42
  | 1 => a 1 * (-42) + b 1
  | n + 2 => a (n + 2) * P (n + 1) + b (n + 2) * P n

/-- Denominators, starting with denominator one. -/
def Q : ℕ → ℝ
  | 0 => 1
  | 1 => a 1
  | n + 2 => a (n + 2) * Q (n + 1) + b (n + 2) * Q n

theorem P_eq (n : ℕ) : P n = convNum a21 b21 (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [P, convNum, a21]
  | one => simp [P, convNum, a, b, a21, b21]
  | more n ih0 ih1 =>
    simp only [P, convNum, ih0, ih1, a, b, a21, b21]

theorem Q_eq (n : ℕ) : Q n = convDen a21 b21 (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [Q, convDen, a, a21]
  | more n ih0 ih1 =>
    simp only [Q, convDen, ih0, ih1, a, b, a21, b21]

/-- Every denominator in this indexing is nonzero, including the first. -/
theorem Q_ne_zero (n : ℕ) : Q n ≠ 0 := by
  rw [Q_eq]
  exact convDen21_ne n

/-- An explicit check of the first two convergents and their indexing. -/
theorem initial_values : P 0 = -42 ∧ Q 0 = 1 ∧ P 1 = 44370 ∧ Q 1 = -1047 := by
  norm_num [P, Q, a, b]

/-- The exact Pincherle value, exposed as a reusable equality. -/
theorem value : a21 0 - Z21 1 / Z21 0 = 6 / (3 - Real.pi) := by
  simp only [Z21, sig21, F21_zero, F21_one, a21]
  have hpi : Real.pi - 3 ≠ 0 := (sub_pos.mpr Real.pi_gt_three).ne'
  have hpi' : 3 - Real.pi ≠ 0 := (sub_neg.mpr Real.pi_gt_three).ne
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  norm_num [r21]
  field_simp
  ring

/-- Exact residual identity; division is justified by positive `Z21 0` and nonzero `Q n`. -/
theorem error_identity (n : ℕ) :
    P n / Q n - 6 / (3 - Real.pi) = (Z21 (n + 1) / Q n) / Z21 0 := by
  have hz : Z21 0 ≠ 0 := (mul_pos (sig21_pos 0) (F21_pos 0)).ne'
  have hq := Q_ne_zero n
  have h := congrFun (solution_eq_combo a21 b21 Z21 Z21_isSolution) (n + 1)
  rw [← P_eq, ← Q_eq] at h
  rw [← value]
  field_simp
  nlinarith [h]

/-- A geometric error bound for every actual convergent. -/
theorem error_bound (n : ℕ) :
    ‖P n / Q n - 6 / (3 - Real.pi)‖ ≤
      (300 * Real.sqrt 2 / Z21 0) * (1 / 5)^n := by
  have hz : 0 < Z21 0 := mul_pos (sig21_pos 0) (F21_pos 0)
  rw [error_identity, norm_div, Real.norm_eq_abs (Z21 0), abs_of_pos hz]
  calc
    ‖Z21 (n + 1) / Q n‖ / Z21 0 ≤
        (300 * Real.sqrt 2 * (1 / 5)^n) / Z21 0 :=
      div_le_div_of_nonneg_right (by simpa only [Q_eq] using Z21_div_convDen_le n) hz.le
    _ = _ := by ring

/-- The challenge limit, derived directly from the geometric error bound.
This proof does not invoke `pcf21_tendsto` or `pincherle`. -/
theorem limit : Tendsto (fun n => P n / Q n) atTop (𝓝 (6 / (3 - Real.pi))) := by
  have hzero : Tendsto (fun n => P n / Q n - 6 / (3 - Real.pi)) atTop (𝓝 0) := by
    refine squeeze_zero_norm error_bound ?_
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 5)
      (by norm_num)).const_mul (300 * Real.sqrt 2 / Z21 0)
    simpa using h
  simpa using hzero.add_const (6 / (3 - Real.pi))

end RamanujanChallenge.Reviewed
