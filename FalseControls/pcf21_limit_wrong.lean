import RamanujanChallenge.Problem21
-- The Pincherle value is a_0 − X_0/X_{−1} = 6/(3 − π), not 6/(3 + π).
example : RamanujanChallenge.cf21.partialDen 0 -
    RamanujanChallenge.Z21 1 / RamanujanChallenge.Z21 0 = 6 / (3 + Real.pi) := by
  simp only [RamanujanChallenge.cf21_partialDen, RamanujanChallenge.Z21, RamanujanChallenge.sig21, RamanujanChallenge.F21_zero,
    RamanujanChallenge.F21_one, RamanujanChallenge.a21]
  have hpi : Real.pi - 3 ≠ 0 := (sub_pos.mpr Real.pi_gt_three).ne'
  have hpi' : 3 + Real.pi ≠ 0 := by have := Real.pi_pos; linarith
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  norm_num [RamanujanChallenge.r21]
  field_simp
  ring
