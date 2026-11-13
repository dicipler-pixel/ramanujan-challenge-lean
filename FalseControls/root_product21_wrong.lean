import RamanujanChallenge.Exact
-- The roots of 4x² + 594x − 729 multiply to −729/4 (opposite signs), not +729/4.
example : RamanujanChallenge.subdominantRoot21 * RamanujanChallenge.dominantRoot21 = 729 / 4 := by
  rw [RamanujanChallenge.subdominantRoot21_mul_dominantRoot21]
  norm_num
