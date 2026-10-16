/-
Ramanujan Challenge for AI (Ramanujan Machine Group, Technion, 2026): the exact algebra
established in Jeromie Beasley's submissions to Problems 2.1–2.6, as machine-checked statements.

Every theorem here is finite algebra: a polynomial identity, a determinant, a matrix relation,
a partial-fraction decomposition, or a rational-number identity. Nothing here evaluates a limit;
the limits π, γ, π + e, G and ζ(2) + ζ(3) are not formalised (see LIMITATIONS.md).

Problem 2.1 (polynomial continued fraction for π).
  * The Casoratian of any three-term recurrence steps by −b, so the determinant identity
    A_{n+1}B_n − A_nB_{n+1} = (−1)^n (∏ b)(A_1B_0 − A_0B_1) holds for every n.
  * Consecutive convergents differ by that Casoratian over B_nB_{n−1}.
  * The partial products of b_n = 4n²(2n+1)²(5n−4)(5n+6) have the closed form
    ∏_{k=1}^{n} b_k = 25^n ((2n+1)!)² (1/5)_n (11/5)_n.
Problem 2.2 (γ as an Apéry limit).
  * The cubic factor of a_0 shifted by one is the cubic factor of a_3, which is what makes the
    Casoratian of the order-3 recurrence telescope; the companion matrix has determinant −a_3/a_0.
Problem 2.3 (π + e as an Apéry limit).
  * The characteristic roots √2 ± 1 are a reciprocal pair and the roots of λ² − 2√2 λ + 1.
Problem 2.5 (Catalan's constant).
  * The leading-order matrices L, B, C of M(n) = n⁹(L + B/n + C/n² + …) obey
    L² = 0, LB = BL = 0, B² = −288 L, B³ = 0, LC = −272 L, CL = −16 L.
Problem 2.6 (a series for ζ(2) + ζ(3)).
  * The rational solution r(n) = (3n/14 + 1)/(n³ + 14n² + 65n + 100) has denominator (n+4)(n+5)²
    and the partial fractions 1/(7(n+4)) − 1/(7(n+5)) + 1/(14(n+5)²); the rational part of its
    sum is 1/35 − (1/14)(1 + 1/4 + 1/9 + 1/16 + 1/25) = −547/7200.
-/
import Mathlib

namespace RamanujanChallenge

open Finset

/-! ## Problem 2.1: the determinant identity and the Pochhammer product -/

/-- `a_n` of Problem 2.1. -/
def a1 (x : ℚ) : ℚ := -220 * x ^ 3 - 484 * x ^ 2 - 301 * x - 42

/-- `b_n` of Problem 2.1. -/
def b1 (x : ℚ) : ℚ := 4 * x ^ 2 * (2 * x + 1) ^ 2 * (5 * x - 4) * (5 * x + 6)

/-- One step of the Casoratian of a three-term recurrence `u_{n+2} = a_{n+2} u_{n+1} + b_{n+2} u_n`:
the determinant of consecutive values is multiplied by `−b_{n+2}`. -/
theorem casoratian_step (a b A B : ℕ → ℚ)
    (hA : ∀ n, A (n + 2) = a (n + 2) * A (n + 1) + b (n + 2) * A n)
    (hB : ∀ n, B (n + 2) = a (n + 2) * B (n + 1) + b (n + 2) * B n) (n : ℕ) :
    A (n + 2) * B (n + 1) - A (n + 1) * B (n + 2)
      = -b (n + 2) * (A (n + 1) * B n - A n * B (n + 1)) := by
  rw [hA, hB]; ring

/-- The determinant (Wronskian) identity for continued fractions, for every `n`. -/
theorem casoratian_closed (a b A B : ℕ → ℚ)
    (hA : ∀ n, A (n + 2) = a (n + 2) * A (n + 1) + b (n + 2) * A n)
    (hB : ∀ n, B (n + 2) = a (n + 2) * B (n + 1) + b (n + 2) * B n) (n : ℕ) :
    A (n + 1) * B n - A n * B (n + 1)
      = (-1) ^ n * (∏ k ∈ range n, b (k + 2)) * (A 1 * B 0 - A 0 * B 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    show A (n + 2) * B (n + 1) - A (n + 1) * B (n + 2) = _
    rw [casoratian_step a b A B hA hB n, ih, prod_range_succ]
    ring

/-- Consecutive convergents differ by the Casoratian over `B_{n+1} B_n`. -/
theorem convergent_difference (A B : ℕ → ℚ) (n : ℕ) (h0 : B n ≠ 0) (h1 : B (n + 1) ≠ 0) :
    A (n + 1) / B (n + 1) - A n / B n
      = (A (n + 1) * B n - A n * B (n + 1)) / (B (n + 1) * B n) := by
  rw [div_sub_div _ _ h1 h0]
  ring

/-- The factor that enters the Pochhammer product at step `n → n + 1`. -/
theorem b1_succ_factor (x : ℚ) :
    b1 (x + 1) = 25 * (2 * x + 3) ^ 2 * (2 * x + 2) ^ 2 * (1 / 5 + x) * (11 / 5 + x) := by
  unfold b1; ring

/-- The exact closed form `∏_{k=1}^{n} b_k = 25^n ((2n+1)!)² (1/5)_n (11/5)_n`, for every `n`. -/
theorem pochhammer_product (n : ℕ) :
    ∏ k ∈ range n, b1 ((k : ℚ) + 1)
      = 25 ^ n * ((2 * n + 1).factorial : ℚ) ^ 2
          * (∏ i ∈ range n, ((1 : ℚ) / 5 + i)) * (∏ i ∈ range n, ((11 : ℚ) / 5 + i)) := by
  induction n with
  | zero => simp [Nat.factorial]
  | succ n ih =>
    have hf : ((2 * (n + 1) + 1).factorial : ℚ)
        = (2 * (n : ℚ) + 3) * (2 * (n : ℚ) + 2) * ((2 * n + 1).factorial : ℚ) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring, Nat.factorial_succ (2 * n + 1 + 1),
        Nat.factorial_succ (2 * n + 1)]
      push_cast
      ring
    rw [prod_range_succ, ih, prod_range_succ, prod_range_succ, hf, b1_succ_factor]
    ring

/-! ## Problem 2.2: the telescoping cubic and the companion determinant -/

/-- The cubic factor of `a_0(n)` in Problem 2.2. -/
def P22 (x : ℚ) : ℚ := 8 * x ^ 3 + 51 * x ^ 2 + 105 * x + 68

/-- Shifting the cubic factor of `a_0` by one gives the cubic factor of `a_3`: this is the
mechanism behind the telescoping Casoratian. -/
theorem telescoping_factor (x : ℚ) : P22 (x + 1) = 8 * x ^ 3 + 75 * x ^ 2 + 231 * x + 232 := by
  unfold P22; ring

/-- The row companion matrix of an order-3 recurrence has determinant `−a_3/a_0`. -/
theorem companion3_det (a0 a1 a2 a3 : ℚ) :
    Matrix.det !![(0 : ℚ), 1, 0; 0, 0, 1; -a3 / a0, -a2 / a0, -a1 / a0] = -a3 / a0 := by
  simp [Matrix.det_fin_three] <;> ring

/-! ## Problem 2.3: the characteristic roots are a reciprocal pair -/

theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- The dominant characteristic root `√2 + 1`. -/
noncomputable def rPlus : ℝ := Real.sqrt 2 + 1

/-- The recessive characteristic root `√2 − 1`. -/
noncomputable def rMinus : ℝ := Real.sqrt 2 - 1

theorem roots_reciprocal : rPlus * rMinus = 1 := by
  unfold rPlus rMinus
  linear_combination sqrt2_sq

theorem rPlus_char : rPlus ^ 2 - 2 * Real.sqrt 2 * rPlus + 1 = 0 := by
  unfold rPlus
  linear_combination (-1 : ℝ) * sqrt2_sq

theorem rMinus_char : rMinus ^ 2 - 2 * Real.sqrt 2 * rMinus + 1 = 0 := by
  unfold rMinus
  linear_combination (-1 : ℝ) * sqrt2_sq

/-! ## Problem 2.5: the leading-order transport algebra -/

/-- Coefficient of `n⁹` in `M(n)`. -/
def L25 : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, 0; 0, 0, 0; -128, 0, 0]

/-- Coefficient of `n⁸` in `M(n)`. -/
def B25 : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, 0; 192, 0, 0; -2808, 192, 0]

/-- Coefficient of `n⁷` in `M(n)`. -/
def C25 : Matrix (Fin 3) (Fin 3) ℚ := !![-272, 0, 0; 3944, -272, 0; -27184, 3752, -16]

theorem L_sq : L25 * L25 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L25, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem L_mul_B : L25 * B25 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L25, B25, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem B_mul_L : B25 * L25 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L25, B25, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem B_sq : B25 * B25 = (-288 : ℚ) • L25 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [L25, B25, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem B_cube : B25 * B25 * B25 = 0 := by
  rw [B_sq, Matrix.smul_mul, L_mul_B, smul_zero]

theorem L_mul_C : L25 * C25 = (-272 : ℚ) • L25 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [L25, C25, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem C_mul_L : C25 * L25 = (-16 : ℚ) • L25 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [L25, C25, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-! ## Problem 2.6: the rational solution and its partial fractions -/

/-- The rational solution `r(n)` of the first factor of the partial-sum operator. -/
def r26 (x : ℚ) : ℚ := (3 / 14 * x + 1) / (x ^ 3 + 14 * x ^ 2 + 65 * x + 100)

theorem r26_denom (x : ℚ) : x ^ 3 + 14 * x ^ 2 + 65 * x + 100 = (x + 4) * (x + 5) ^ 2 := by
  ring

theorem r26_partial (x : ℚ) (h4 : x + 4 ≠ 0) (h5 : x + 5 ≠ 0) :
    r26 x = 1 / 7 / (x + 4) - 1 / 7 / (x + 5) + 1 / 14 / (x + 5) ^ 2 := by
  unfold r26
  rw [r26_denom]
  field_simp
  ring

/-- The rational part of `Σ_{n≥1} r(n)`: the telescoping term gives `1/35`, and the shifted
`ζ(2)` tail removes the first five squares. -/
theorem r26_constant :
    (1 : ℚ) / 35 - 1 / 14 * (1 + 1 / 4 + 1 / 9 + 1 / 16 + 1 / 25) = -547 / 7200 := by
  norm_num

end RamanujanChallenge
