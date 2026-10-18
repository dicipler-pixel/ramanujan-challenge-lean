/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import RamanujanChallenge.EulerIntegral

/-! Instances of the general Euler integral, checked with warnings as errors by
`scripts/check_review.py`. Adapted from the specialization checks of the Codex edition
(commit `e977cf2`). -/

open RamanujanChallenge

-- Both endpoints singular (b = 1/2, c − b = 1/2); a and x negative.
example :
    ordinaryHypergeometric (-2 : ℝ) (1 / 2) 1 (-1 / 2) =
      Real.Gamma 1 / (Real.Gamma (1 / 2) * Real.Gamma (1 - 1 / 2)) *
        ∫ t in (0:ℝ)..1, t ^ ((1 / 2 : ℝ) - 1) * (1 - t) ^ ((1 : ℝ) - 1 / 2 - 1) *
          (1 - (-1 / 2) * t) ^ (-(-2 : ℝ)) :=
  ordinaryHypergeometric_eq_integral (by norm_num) (by norm_num) (by norm_num)

-- The Problem 2.1 family lies in the theorem's domain.
example (m : ℕ) :
    ordinaryHypergeometric ((m : ℝ) + 3 / 2) ((m : ℝ) + 3 / 2) (3 * (m : ℝ) + 7 / 2) (1 / 2) =
      Real.Gamma (3 * (m : ℝ) + 7 / 2) /
        (Real.Gamma ((m : ℝ) + 3 / 2) * Real.Gamma ((3 * (m : ℝ) + 7 / 2) - ((m : ℝ) + 3 / 2))) *
        ∫ t in (0:ℝ)..1, t ^ (((m : ℝ) + 3 / 2) - 1) *
          (1 - t) ^ ((3 * (m : ℝ) + 7 / 2) - ((m : ℝ) + 3 / 2) - 1) *
          (1 - (1 / 2) * t) ^ (-((m : ℝ) + 3 / 2)) :=
  ordinaryHypergeometric_eq_integral (by positivity) (by linarith) (by norm_num)

-- Integrability, with a = 0 and x = 0 and both endpoints singular.
example : IntervalIntegrable
    (fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1) * (1 - t) ^ ((1 : ℝ) - 1 / 2 - 1) *
      (1 - 0 * t) ^ (-(0 : ℝ)))
    MeasureTheory.volume 0 1 :=
  intervalIntegrable_eulerIntegrand 0 (by norm_num) (by norm_num) (by norm_num)
