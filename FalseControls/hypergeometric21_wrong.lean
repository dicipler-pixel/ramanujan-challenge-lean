import RamanujanChallenge.Euler21
-- ₂F₁(3/2, 3/2; 7/2; 1/2) = (15√2/2)(π − 3), not 15√2(π − 3).
example : ordinaryHypergeometric (3 / 2 : ℝ) (3 / 2) (7 / 2) (1 / 2 : ℝ) =
    15 * Real.sqrt 2 * (Real.pi - 3) := by
  rw [RamanujanChallenge.hypergeometric21_one]
  have hpi : Real.pi - 3 ≠ 0 := (sub_pos.mpr Real.pi_gt_three).ne'
  field_simp
  ring_nf
