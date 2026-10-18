import Mathlib
import RamanujanChallenge.Exact

/-!
Problem 2.6: the series of the rational solution `r(n)` of the top factor of the partial-sum
operator sums to `π²/84 − 547/7200`.

`r(n) = (3n/14 + 1) / ((n+4)(n+5)²) = 1/(7(n+4)) − 1/(7(n+5)) + 1/(14(n+5)²)` (`r26_partial` in
`Exact.lean`). Summed over `n ≥ 1` the first two terms telescope to `1/35` and the third is
`(1/14)(ζ(2) − 1 − 1/4 − 1/9 − 1/16 − 1/25)`; Mathlib's `hasSum_zeta_two` supplies `ζ(2) = π²/6`.
This is the first limit in the library. It is the rational-solution series, not the three
limits `{1, Σh, p₃(∞)}` whose connection formula assembles `S_∞ = ζ(2) + ζ(3)`
(see LIMITATIONS.md).
-/

open Filter Topology

namespace RamanujanChallenge

/-- The real term `r(n+1)`, `n ≥ 0`, of the Problem 2.6 rational-solution series. -/
def r26Term (n : ℕ) : ℝ := ((r26 ((n : ℚ) + 1) : ℚ) : ℝ)

theorem r26Term_eq (n : ℕ) :
    r26Term n = 1 / 7 / ((n : ℝ) + 5) - 1 / 7 / ((n : ℝ) + 6) + 1 / 14 / ((n : ℝ) + 6) ^ 2 := by
  unfold r26Term
  rw [r26_partial _ (by positivity) (by positivity)]
  push_cast
  ring

theorem telescope_partial (N : ℕ) :
    ∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 5) - 1 / ((i : ℝ) + 6)) = 1 / 5 - 1 / ((N : ℝ) + 5) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem hasSum_telescope : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 5) - 1 / ((n : ℝ) + 6)) (1 / 5) := by
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ 1 / ((n : ℝ) + 5) - 1 / ((n : ℝ) + 6) := by
    intro n
    rw [sub_nonneg]
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  have h5 : Tendsto (fun N : ℕ => ((N : ℝ) + 5)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have h : Tendsto (fun N : ℕ => 1 / 5 - ((N : ℝ) + 5)⁻¹) atTop (𝓝 (1 / 5 - 0)) :=
    tendsto_const_nhds.sub h5
  rw [sub_zero] at h
  exact h.congr (fun N => by rw [telescope_partial N, one_div ((N : ℝ) + 5)])

theorem sum_inv_sq_six : ∑ i ∈ Finset.range 6, (1 : ℝ) / (i : ℝ) ^ 2 = 5269 / 3600 := by
  norm_num [Finset.sum_range_succ]

theorem hasSum_inv_sq_shift :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 6) ^ 2) (Real.pi ^ 2 / 6 - 5269 / 3600) := by
  have h := (hasSum_nat_add_iff' 6).mpr hasSum_zeta_two
  rw [sum_inv_sq_six] at h
  have hf : (fun n : ℕ => 1 / ((n : ℝ) + 6) ^ 2) = fun n : ℕ => 1 / ((n + 6 : ℕ) : ℝ) ^ 2 := by
    funext n; push_cast; ring
  rw [hf]
  exact h

/-- `Σ_{n ≥ 1} r(n) = π²/84 − 547/7200` for the Problem 2.6 rational solution `r`. -/
theorem r26_hasSum : HasSum r26Term (Real.pi ^ 2 / 84 - 547 / 7200) := by
  have h := (hasSum_telescope.mul_left (1 / 7)).add (hasSum_inv_sq_shift.mul_left (1 / 14))
  have hval : (1 / 7 : ℝ) * (1 / 5) + 1 / 14 * (Real.pi ^ 2 / 6 - 5269 / 3600) =
      Real.pi ^ 2 / 84 - 547 / 7200 := by ring
  rw [hval] at h
  convert h using 1
  funext n
  rw [r26Term_eq]
  ring

end RamanujanChallenge
