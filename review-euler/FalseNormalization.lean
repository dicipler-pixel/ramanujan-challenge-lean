import RamanujanChallenge.EulerGeneral

-- Deliberately false: the series has value 1 at z=0, not 2.
example : ordinaryHypergeometric (1:ℝ) 1 2 (0:ℝ) = 2 := by
  norm_num [ordinaryHypergeometric_zero]
