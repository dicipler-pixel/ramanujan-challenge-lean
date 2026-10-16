import RamanujanChallenge.Exact
-- The rational part of Σ r(n) is −547/7200, not −547/7000.
example : (1 : ℚ) / 35 - 1 / 14 * (1 + 1 / 4 + 1 / 9 + 1 / 16 + 1 / 25) = -547 / 7000 := by
  norm_num
