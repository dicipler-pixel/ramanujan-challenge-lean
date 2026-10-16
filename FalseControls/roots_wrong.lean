import RamanujanChallenge.Exact
-- (√2 + 1)(√2 − 1) = 1, not 2.
example : RamanujanChallenge.rPlus * RamanujanChallenge.rMinus = 2 := by
  unfold RamanujanChallenge.rPlus RamanujanChallenge.rMinus
  nlinarith [RamanujanChallenge.sqrt2_sq]
