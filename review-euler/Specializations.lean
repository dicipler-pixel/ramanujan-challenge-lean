import RamanujanChallenge.EulerGeneral

open EulerIntegralReview

-- Both Beta endpoints are singular; a and z are negative.
example :
    ordinaryHypergeometric (-2 : ℝ) (1/2) 1 (-1/2) =
      Real.Gamma 1 / (Real.Gamma (1/2) * Real.Gamma (1-1/2)) *
        ∫ t in (0:ℝ)..1, t^(1/2-1:ℝ) * (1-t)^(1-1/2-1:ℝ) *
          (1-(-1/2)*t)^(-(-2):ℝ) := by
  exact ordinaryHypergeometric_eq_eulerIntegral (-2) (by norm_num) (by norm_num) (by norm_num)

-- The existing Problem 2.1 family is inside the general theorem's domain.
example (m : ℕ) :
    ordinaryHypergeometric ((m:ℝ)+3/2) ((m:ℝ)+3/2) (3*(m:ℝ)+7/2) (1/2) =
      Real.Gamma (3*(m:ℝ)+7/2) /
        (Real.Gamma ((m:ℝ)+3/2) * Real.Gamma ((3*(m:ℝ)+7/2)-((m:ℝ)+3/2))) *
        ∫ t in (0:ℝ)..1, t^(((m:ℝ)+3/2)-1) *
          (1-t)^((3*(m:ℝ)+7/2)-((m:ℝ)+3/2)-1) *
          (1-(1/2)*t)^(-((m:ℝ)+3/2)) := by
  exact ordinaryHypergeometric_eq_eulerIntegral _ (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) m]) (by norm_num)

-- The endpoint-singular integrability result also allows a = 0 and z = 0.
example : IntervalIntegrable
    (fun t : ℝ => t^(1/2-1:ℝ) * (1-t)^(1-1/2-1:ℝ) * (1-0*t)^(-0:ℝ))
    MeasureTheory.volume 0 1 := by
  exact euler_integrand_intervalIntegrable 0 (by norm_num) (by norm_num) (by norm_num)
