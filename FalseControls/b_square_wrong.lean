import RamanujanChallenge.Exact
-- B² = −288 L, not −144 L: the (3,1) entry is 36864, not 18432.
example : RamanujanChallenge.B25 * RamanujanChallenge.B25 = (-144 : ℚ) • RamanujanChallenge.L25 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [RamanujanChallenge.L25, RamanujanChallenge.B25, Matrix.mul_apply, Fin.sum_univ_three] <;>
    norm_num
