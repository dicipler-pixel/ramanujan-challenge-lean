import RamanujanChallenge.Problem21
-- The middle coefficient of the 2.1 integral recurrence is 220n³ + 484n² + 301n + 42 (= −a_n);
-- with 43 in place of 42 the telescoping certificate no longer differentiates to it.
example (u : ℝ) : HasDerivAt (RamanujanChallenge.Phi21 0)
    (-(2 * 1 * 3 * 11) * RamanujanChallenge.w21 0 u
      + (220 + 484 + 301 + 43) * RamanujanChallenge.w21 1 u
      + 2 * 2 * 5 * 6 * RamanujanChallenge.w21 2 u) u := by
  have h := (RamanujanChallenge.hasDerivAt_N21 ((0:ℕ) + 1) u).fun_mul
    ((RamanujanChallenge.hasDerivAt_G21 u).fun_pow 0)
  convert h using 1
  · rfl
  have hd := RamanujanChallenge.one_add_sq_ne u
  simp only [RamanujanChallenge.N21, RamanujanChallenge.G21, RamanujanChallenge.w21,
    RamanujanChallenge.q21, pow_zero, Nat.cast_zero, zero_mul, mul_zero, add_zero, mul_one, zero_add]
  field_simp
  ring
