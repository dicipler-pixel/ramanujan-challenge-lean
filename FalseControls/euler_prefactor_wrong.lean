import RamanujanChallenge.EulerIntegral
-- Euler's integral with the Gamma prefactor inverted, at a = 0, b = 1, c = 3, x = 0.
-- The true prefactor is Γ(3)/(Γ(1)Γ(2)) = 2 and the integral is 1/2, so the claimed value 1/4 is
-- false (the series is 1).
example : ordinaryHypergeometric (0 : ℝ) 1 3 (0 : ℝ) =
    Real.Gamma 1 * Real.Gamma 2 / Real.Gamma 3 *
      ∫ t in (0:ℝ)..1, t ^ ((1 : ℝ) - 1) * (1 - t) ^ ((3 : ℝ) - 1 - 1) *
        (1 - 0 * t) ^ (-(0 : ℝ)) := by
  have h3 : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_two]
    norm_num
  rw [RamanujanChallenge.ordinaryHypergeometric_eq_integral (by norm_num) (by norm_num)
    (by norm_num), h3]
  norm_num [Real.Gamma_two]
