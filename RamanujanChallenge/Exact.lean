import Mathlib

/-!
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
    Casoratian of the order-3 recurrence telescope; the companion matrix has determinant −a_3/a_0,
    and the Casoratian is n!((n+1)!)⁴((n+2)!/2) P(n)/68 times its initial value, for every n.
Problem 2.3 (π + e as an Apéry limit).
  * The characteristic roots √2 ± 1 are a reciprocal pair and the roots of λ² − 2√2 λ + 1.
  * p_n and q_n are defined from the challenge's recurrence and the kernel computes
    p_5 = 730267195392 and q_5 = 124622119440; likewise q_n = 1, 12, 306, 13056, 833400, 73876320
    for Problem 2.2.
Problem 2.5 (Catalan's constant).
  * Zudilin's order-2 recurrence for G has characteristic polynomial x² − 11x − 1 with roots
    φ⁵ = 5φ + 3 and −φ⁻⁵ = 11 − φ⁵; the matrix convergents were matched to its ratios.
  * The leading-order matrices L, B, C of M(n) = n⁹(L + B/n + C/n² + …) obey
    L² = 0, LB = BL = 0, B² = −288 L, B³ = 0, LC = −272 L, CL = −16 L.
Problem 2.6 (a series for ζ(2) + ζ(3)).
  * The recurrence operator factors exactly, L_c = M₂ · R₂, with explicit first-order factors.
  * The hypergeometric piece of the partial-sum operator has the term ratio (n+4)²/(4(n+5)(n+9/2)).
  * The rational solution r(n) = (3n/14 + 1)/(n³ + 14n² + 65n + 100) has denominator (n+4)(n+5)²
    and the partial fractions 1/(7(n+4)) − 1/(7(n+5)) + 1/(14(n+5)²); the rational part of its
    sum is 1/35 − (1/14)(1 + 1/4 + 1/9 + 1/16 + 1/25) = −547/7200.
-/

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
    change A (n + 2) * B (n + 1) - A (n + 1) * B (n + 2) = _
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

/-! ### Problem 2.1: the limiting characteristic roots

After the rescaling that makes the coefficients converge, the recurrence for `F_n` has
`A(n) → −297/2` and `B(n) → 729/4`, so Poincaré–Perron's characteristic polynomial is
`λ² + (297/2) λ − 729/4` with roots `λ_s = (−297 + 135√5)/4 ≈ 1.217` and
`λ_d = (−297 − 135√5)/4 ≈ −149.7`. The `₂F₁` solution grows like `λ_s^n`, the dominant one like
`λ_d^n`; `|λ_s| < |λ_d|` is what makes it minimal (`isMinimal_of_ratio` in `Pincherle.lean`). -/

/-- The subdominant root `λ_s`. -/
noncomputable def lamS : ℝ := (-297 + 135 * Real.sqrt 5) / 4

/-- The dominant root `λ_d`. -/
noncomputable def lamD : ℝ := (-297 - 135 * Real.sqrt 5) / 4

theorem lamS_root : lamS ^ 2 + 297 / 2 * lamS - 729 / 4 = 0 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold lamS
  linear_combination (18225 / 16 : ℝ) * h5

theorem lamD_root : lamD ^ 2 + 297 / 2 * lamD - 729 / 4 = 0 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold lamD
  linear_combination (18225 / 16 : ℝ) * h5

theorem lamS_mul_lamD : lamS * lamD = -729 / 4 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold lamS lamD
  linear_combination (-18225 / 16 : ℝ) * h5

theorem lamS_pos : 0 < lamS := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  unfold lamS
  nlinarith

theorem lamD_neg : lamD < 0 := by
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  unfold lamD
  linarith

theorem abs_lamS_lt_abs_lamD : |lamS| < |lamD| := by
  rw [abs_of_pos lamS_pos, abs_of_neg lamD_neg]
  unfold lamS lamD
  linarith [Real.sqrt_nonneg 5]

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
  simp [Matrix.det_fin_three]

/-- The cubic factor is positive at every natural number, so the Casoratian ratio is defined. -/
theorem P22_pos (k : ℕ) : 0 < P22 (k : ℚ) := by
  unfold P22; positivity

/-- The Casoratian ratio `−a_3(n)/a_0(n)` of Problem 2.2 in telescoping form. -/
theorem casoratian22_ratio (x : ℚ) :
    -((x + 1) * (x + 2) ^ 4 * (x + 3) * (8 * x ^ 3 + 75 * x ^ 2 + 231 * x + 232)) / (-(P22 x))
      = (x + 1) * (x + 2) ^ 4 * (x + 3) * P22 (x + 1) / P22 x := by
  rw [telescoping_factor, neg_div_neg_eq]

/-- The Casoratian of Problem 2.2 in closed form: the product of the ratios telescopes to
`n! ((n+1)!)⁴ ((n+2)!/2) P(n)/68`, for every `n`. -/
theorem casoratian22_closed (n : ℕ) :
    ∏ k ∈ range n, (((k : ℚ) + 1) * ((k : ℚ) + 2) ^ 4 * ((k : ℚ) + 3) * P22 ((k : ℚ) + 1) / P22 k)
      = (n.factorial : ℚ) * ((n + 1).factorial : ℚ) ^ 4 * ((n + 2).factorial : ℚ) / 2
          * P22 n / 68 := by
  induction n with
  | zero => norm_num [P22, Nat.factorial]
  | succ n ih =>
    have hf1 : ((n + 1).factorial : ℚ) = ((n : ℚ) + 1) * (n.factorial : ℚ) := by
      rw [Nat.factorial_succ n]; push_cast; ring
    have hf2 : ((n + 1 + 1).factorial : ℚ) = ((n : ℚ) + 2) * ((n + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ (n + 1)]; push_cast; ring
    have hf3 : ((n + 1 + 2).factorial : ℚ) = ((n : ℚ) + 3) * ((n + 2).factorial : ℚ) := by
      rw [show n + 1 + 2 = (n + 2) + 1 by ring, Nat.factorial_succ (n + 2)]; push_cast; ring
    have hP : P22 (n : ℚ) ≠ 0 := (P22_pos n).ne'
    rw [prod_range_succ, ih, hf3, hf2, hf1]
    push_cast
    field_simp

/-- `a_1(n)` of Problem 2.2. -/
def a22Coeff1 (x : ℚ) : ℚ :=
  24 * x ^ 5 + 337 * x ^ 4 + 1833 * x ^ 3 + 4818 * x ^ 2 + 6092 * x + 2928

/-- `a_2(n)` of Problem 2.2. -/
def a22Coeff2 (x : ℚ) : ℚ :=
  -(x + 2) * (x + 3) * (24 * x ^ 5 + 273 * x ^ 4 + 1150 * x ^ 3 + 2154 * x ^ 2 + 1635 * x + 268)

/-- `a_3(n)` of Problem 2.2. -/
def a22Coeff3 (x : ℚ) : ℚ :=
  (x + 1) * (x + 2) ^ 4 * (x + 3) * (8 * x ^ 3 + 75 * x ^ 2 + 231 * x + 232)

/-- The denominator sequence `q_n` of Problem 2.2, indexed so that `q22 (n + 3) = q_n`:
`q_{-3} = 1`, `q_{-2} = 12`, `q_{-1} = 306`, and `a_0(n) q_n + a_1(n) q_{n-1} + a_2(n) q_{n-2}
+ a_3(n) q_{n-3} = 0` for `n ≥ 0`, with `a_0 = −P`. -/
def q22 : ℕ → ℚ
  | 0 => 1
  | 1 => 12
  | 2 => 306
  | k + 3 => (a22Coeff1 k * q22 (k + 2) + a22Coeff2 k * q22 (k + 1) + a22Coeff3 k * q22 k) / P22 k

/-- The first six denominators of Problem 2.2, as the challenge states them. -/
theorem q22_values :
    q22 3 = 13056 ∧ q22 4 = 833400 ∧ q22 5 = 73876320 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [q22, a22Coeff1, a22Coeff2, a22Coeff3, P22]

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

/-- `A_0(n)` of Problem 2.3 (note the sign: `−n³ + 2n² + 7n + 3`, not `−(n³ + 2n² + 7n + 3)`). -/
def A23Coeff0 (x : ℚ) : ℚ := -x ^ 3 + 2 * x ^ 2 + 7 * x + 3

/-- `A_1(n)` of Problem 2.3. -/
def A23Coeff1 (x : ℚ) : ℚ := (x + 2) * (2 * x ^ 4 + x ^ 3 - 26 * x ^ 2 - 48 * x - 19)

/-- `A_2(n)` of Problem 2.3. -/
def A23Coeff2 (x : ℚ) : ℚ :=
  (x + 2) * (x ^ 6 + 9 * x ^ 5 + 8 * x ^ 4 - 87 * x ^ 3 - 249 * x ^ 2 - 234 * x - 68)

/-- `A_3(n)` of Problem 2.3. -/
def A23Coeff3 (x : ℚ) : ℚ :=
  (x + 1) ^ 2 * (x + 2) * (2 * x ^ 5 + 3 * x ^ 4 - 13 * x ^ 3 - 21 * x ^ 2 + 4)

/-- `A_4(n)` of Problem 2.3. -/
def A23Coeff4 (x : ℚ) : ℚ := -x ^ 3 * (x + 1) ^ 2 * (x + 2) * (x ^ 3 + x ^ 2 - 8 * x - 11)

/-- The numerator sequence `p_n` of Problem 2.3, indexed so that `p23 (n + 3) = p_n`:
`p_{-3} = 1`, `p_{-2} = 1`, `p_{-1} = 20`, `p_0 = 296`, and the order-4 recurrence for `n ≥ 1`. -/
def p23 : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | 2 => 20
  | 3 => 296
  | k + 4 => -(A23Coeff1 (k + 1) * p23 (k + 3) + A23Coeff2 (k + 1) * p23 (k + 2)
      + A23Coeff3 (k + 1) * p23 (k + 1) + A23Coeff4 (k + 1) * p23 k) / A23Coeff0 (k + 1)

/-- The denominator sequence `q_n` of Problem 2.3, indexed so that `q23 (n + 3) = q_n`:
`q_{-3} = 1`, `q_{-2} = 0`, `q_{-1} = 4`, `q_0 = 48`. -/
def q23 : ℕ → ℚ
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 48
  | k + 4 => -(A23Coeff1 (k + 1) * q23 (k + 3) + A23Coeff2 (k + 1) * q23 (k + 2)
      + A23Coeff3 (k + 1) * q23 (k + 1) + A23Coeff4 (k + 1) * q23 k) / A23Coeff0 (k + 1)

/-- The sanity anchor of the 2.3 write-up: `p_5 = 730267195392`, computed by the kernel from the
recurrence; and `q_5 = 124622119440`. -/
theorem p23_five : p23 8 = 730267195392 ∧ q23 8 = 124622119440 := by
  refine ⟨?_, ?_⟩ <;> norm_num [p23, q23, A23Coeff0, A23Coeff1, A23Coeff2, A23Coeff3, A23Coeff4]

/-! ## Problem 2.5: the leading-order transport algebra -/

/-- Coefficient of `n⁹` in `M(n)`. -/
def L25 : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, 0; 0, 0, 0; -128, 0, 0]

/-- Coefficient of `n⁸` in `M(n)`. -/
def B25 : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, 0; 192, 0, 0; -2808, 192, 0]

/-- Coefficient of `n⁷` in `M(n)`. -/
def C25 : Matrix (Fin 3) (Fin 3) ℚ := !![-272, 0, 0; 3944, -272, 0; -27184, 3752, -16]

theorem L_sq : L25 * L25 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L25, Matrix.mul_apply, Fin.sum_univ_three]

theorem L_mul_B : L25 * B25 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L25, B25, Matrix.mul_apply, Fin.sum_univ_three]

theorem B_mul_L : B25 * L25 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [L25, B25, Matrix.mul_apply, Fin.sum_univ_three]

theorem B_sq : B25 * B25 = (-288 : ℚ) • L25 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [L25, B25, Matrix.mul_apply, Fin.sum_univ_three]

theorem B_cube : B25 * B25 * B25 = 0 := by
  rw [B_sq, Matrix.smul_mul, L_mul_B, smul_zero]

theorem L_mul_C : L25 * C25 = (-272 : ℚ) • L25 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [L25, C25, Matrix.mul_apply, Fin.sum_univ_three]

theorem C_mul_L : C25 * L25 = (-16 : ℚ) • L25 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [L25, C25, Matrix.mul_apply, Fin.sum_univ_three]

/-! ### Problem 2.5, the Zudilin route: the characteristic roots of Zudilin's Catalan recurrence -/

theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- The golden ratio. -/
noncomputable def phi : ℝ := (Real.sqrt 5 + 1) / 2

theorem phi_sq : phi ^ 2 = phi + 1 := by
  unfold phi; linear_combination (1 / 4 : ℝ) * sqrt5_sq

/-- `φ⁵ = 5φ + 3` (the Fibonacci numbers `F₅ = 5`, `F₄ = 3`). -/
theorem phi_pow5 : phi ^ 5 = 5 * phi + 3 := by
  have h := phi_sq
  linear_combination (phi ^ 3 + phi ^ 2 + 2 * phi + 3) * h

/-- `φ⁵` is a root of Zudilin's characteristic polynomial `x² − 11x − 1` (arXiv:math/0201024), the
order-2 Apéry-like recurrence for Catalan's constant that the 2.5 matrix ratios were matched to. -/
theorem zudilin_root : (phi ^ 5) ^ 2 - 11 * phi ^ 5 - 1 = 0 := by
  rw [phi_pow5]; linear_combination (25 : ℝ) * phi_sq

/-- The second root is `11 − φ⁵ = −φ⁻⁵`: the two roots have product `−1`. -/
theorem zudilin_product : phi ^ 5 * (11 - phi ^ 5) = -1 := by
  linear_combination (-1 : ℝ) * zudilin_root

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

/-- Leading coefficient of the Problem 2.6 operator, `A(m) = −2(m+3)³(2m+5)(3m+5)`. -/
def A26 (m : ℚ) : ℚ := -2 * (m + 3) ^ 3 * (2 * m + 5) * (3 * m + 5)

/-- Middle coefficient, `B(m) = (m+2)²(15m³+85m²+155m+93)`. -/
def B26 (m : ℚ) : ℚ := (m + 2) ^ 2 * (15 * m ^ 3 + 85 * m ^ 2 + 155 * m + 93)

/-- Trailing coefficient, `C(m) = −(m+1)³(m+2)(3m+8)`. -/
def C26 (m : ℚ) : ℚ := -(m + 1) ^ 3 * (m + 2) * (3 * m + 8)

/-- The right factor `R₂ = r₁(n) S + r₀(n)`: its `S` coefficient. -/
def r1 (x : ℚ) : ℚ := x ^ 2 + 15 / 2 * x + 14

/-- The right factor `R₂ = r₁(n) S + r₀(n)`: its constant coefficient. -/
def r0 (x : ℚ) : ℚ := -(1 / 4 * x ^ 2 + 3 / 2 * x + 9 / 4)

/-- The left factor `M₂ = m₁(n) S + m₀(n)`: its `S` coefficient. -/
def m1 (x : ℚ) : ℚ := -12 * x ^ 3 - 164 * x ^ 2 - 740 * x - 1100

/-- The left factor `M₂ = m₁(n) S + m₀(n)`: its constant coefficient. -/
def m0 (x : ℚ) : ℚ := 12 * x ^ 3 + 140 * x ^ 2 + 536 * x + 672

/-- Operator factorisation `L_c = M₂ · R₂` in the shift algebra (`S f(n) = f(n+1)`), where
`L_c = A(n+2) S² + B(n+2) S + C(n+2)`: the `S²` coefficient. -/
theorem factor_S2 (x : ℚ) : A26 (x + 2) = m1 x * r1 (x + 1) := by
  unfold A26 m1 r1; ring

/-- Operator factorisation `L_c = M₂ · R₂`: the `S` coefficient. -/
theorem factor_S1 (x : ℚ) : B26 (x + 2) = m1 x * r0 (x + 1) + m0 x * r1 x := by
  unfold B26 m1 r0 m0 r1; ring

/-- Operator factorisation `L_c = M₂ · R₂`: the constant coefficient. -/
theorem factor_S0 (x : ℚ) : C26 (x + 2) = m0 x * r0 x := by
  unfold C26 m0 r0; ring

/-- The hypergeometric piece of the partial-sum operator has term ratio `(n+4)²/(4(n+5)(n+9/2))`,
which is the first-order recurrence `(n² + 19n/2 + 45/2) h(n+1) = (n²/4 + 2n + 4) h(n)`. -/
theorem h_ratio_cross (x : ℚ) :
    (x + 4) ^ 2 * (x ^ 2 + 19 / 2 * x + 45 / 2) =
      (x ^ 2 / 4 + 2 * x + 4) * (4 * (x + 5) * (x + 9 / 2)) := by
  ring

/-- The rational part of `Σ_{n≥1} r(n)`: the telescoping term gives `1/35`, and the shifted
`ζ(2)` tail removes the first five squares. -/
theorem r26_constant :
    (1 : ℚ) / 35 - 1 / 14 * (1 + 1 / 4 + 1 / 9 + 1 / 16 + 1 / 25) = -547 / 7200 := by
  norm_num

end RamanujanChallenge
