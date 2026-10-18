import Mathlib

/-!
Pincherle's theorem for three-term recurrences, in the form needed by Problem 2.1
(the polynomial continued fraction for π), together with a machine-checked
counterexample to the statement used in the Technion solution skeleton.

Setting. A sequence `Z` solves the recurrence `Z (n+2) = a (n+1) Z (n+1) + b (n+1) Z n`.
The convergents of the continued fraction `K(b_n / a_n)` are `P n / Q n` where `P = convNum`
and `Q = convDen` are the solutions with `(P 0, P 1) = (1, a 0)` and `(Q 0, Q 1) = (0, 1)`.

Pincherle. If `Z` is a minimal solution with `Z 0 ≠ 0`, then `P n / Q n → a 0 - Z 1 / Z 0`.

The hypothesis. The Technion skeleton (`RamanujanMachine/RamanujanChallengeSolutions`,
`Code/2.1/LeanFormal/LeanFormal/PiPCF.lean`, stated there without proof) defines a minimal
solution as
a solution `Z` with a companion solution `D`, not a scalar multiple of `Z`, such that
`Z n / D n → 0`. Because Lean sets `x / 0 = 0`, that definition is satisfied by a `D` that
vanishes infinitely often, and then the conclusion is false (`technion_pincherle_fails`
below gives explicit period-2 coefficients). `IsMinimal` here adds the clause
`∀ᶠ n, D n ≠ 0`, which the classical statement carries implicitly (the quotient `Z n / D n`
is only meaningful when `D n ≠ 0`). With that clause the theorem is proved, and the
skeleton's extra hypothesis `∀ n ≥ 1, b n ≠ 0` is not needed for this direction.
-/

open Filter Topology

namespace RamanujanChallenge

/-- `Z` solves the three-term recurrence `Z (n+2) = a (n+1) * Z (n+1) + b (n+1) * Z n`. -/
def IsSolution (a b Z : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, Z (n + 2) = a (n + 1) * Z (n + 1) + b (n + 1) * Z n

/-- Numerators of the convergents: the solution with `P 0 = 1`, `P 1 = a 0`. -/
def convNum (a b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => a 0
  | n + 2 => a (n + 1) * convNum a b (n + 1) + b (n + 1) * convNum a b n

/-- Denominators of the convergents: the solution with `Q 0 = 0`, `Q 1 = 1`. -/
def convDen (a b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => a (n + 1) * convDen a b (n + 1) + b (n + 1) * convDen a b n

/-- Minimal solution (corrected form): a solution `Z` with a dominant companion `D`, not a
scalar multiple of `Z`, eventually nonzero, with `Z n / D n → 0`. -/
def IsMinimal (a b Z : ℕ → ℝ) : Prop :=
  IsSolution a b Z ∧ ∃ D : ℕ → ℝ, IsSolution a b D ∧ (∀ c : ℝ, D ≠ c • Z) ∧
    (∀ᶠ n in atTop, D n ≠ 0) ∧ Tendsto (fun n => Z n / D n) atTop (𝓝 0)

/-- The Technion skeleton's definition of a minimal solution: as `IsMinimal` but without
the requirement that `D` be eventually nonzero. -/
def IsMinimalWeak (a b Z : ℕ → ℝ) : Prop :=
  IsSolution a b Z ∧ ∃ D : ℕ → ℝ, IsSolution a b D ∧ (∀ c : ℝ, D ≠ c • Z) ∧
    Tendsto (fun n => Z n / D n) atTop (𝓝 0)

theorem isMinimal_weak {a b Z : ℕ → ℝ} (h : IsMinimal a b Z) : IsMinimalWeak a b Z := by
  obtain ⟨hZ, D, hD, hDZ, -, hlim⟩ := h
  exact ⟨hZ, D, hD, hDZ, hlim⟩

theorem convNum_isSolution (a b : ℕ → ℝ) : IsSolution a b (convNum a b) := fun n => by
  simp only [convNum]

theorem convDen_isSolution (a b : ℕ → ℝ) : IsSolution a b (convDen a b) := fun n => by
  simp only [convDen]

theorem zero_isSolution (a b : ℕ → ℝ) : IsSolution a b (fun _ => 0) := fun n => by simp

theorem IsSolution.const_mul {a b Z : ℕ → ℝ} (hZ : IsSolution a b Z) (k : ℝ) :
    IsSolution a b (fun n => k * Z n) := by
  intro n
  change k * Z (n + 2) = a (n + 1) * (k * Z (n + 1)) + b (n + 1) * (k * Z n)
  rw [hZ n]; ring

theorem IsSolution.sub_smul {a b D Z : ℕ → ℝ} (hD : IsSolution a b D) (hZ : IsSolution a b Z)
    (c : ℝ) : IsSolution a b (fun n => D n - c * Z n) := by
  intro n
  change D (n + 2) - c * Z (n + 2) =
    a (n + 1) * (D (n + 1) - c * Z (n + 1)) + b (n + 1) * (D n - c * Z n)
  rw [hD n, hZ n]; ring

theorem IsSolution.combo (a b : ℕ → ℝ) (α β : ℝ) :
    IsSolution a b (fun n => α * convNum a b n + β * convDen a b n) := by
  intro n
  change α * convNum a b (n + 2) + β * convDen a b (n + 2) =
    a (n + 1) * (α * convNum a b (n + 1) + β * convDen a b (n + 1)) +
      b (n + 1) * (α * convNum a b n + β * convDen a b n)
  rw [convNum_isSolution a b n, convDen_isSolution a b n]; ring

/-- Two solutions that agree at `0` and `1` agree everywhere. -/
theorem solution_unique (a b Y Z : ℕ → ℝ) (hY : IsSolution a b Y) (hZ : IsSolution a b Z)
    (h0 : Y 0 = Z 0) (h1 : Y 1 = Z 1) : Y = Z := by
  funext n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih0 ih1 => rw [hY n, hZ n, ih0, ih1]

/-- Every solution is `W 0 • P + (W 1 - a 0 * W 0) • Q`: the solution space is spanned by
the convergent numerators and denominators. -/
theorem solution_eq_combo (a b W : ℕ → ℝ) (hW : IsSolution a b W) :
    W = fun n => W 0 * convNum a b n + (W 1 - a 0 * W 0) * convDen a b n := by
  refine solution_unique a b W _ hW (IsSolution.combo a b (W 0) (W 1 - a 0 * W 0)) ?_ ?_
  · show W 0 = W 0 * convNum a b 0 + (W 1 - a 0 * W 0) * convDen a b 0
    simp only [convNum, convDen]; ring
  · show W 1 = W 0 * convNum a b 1 + (W 1 - a 0 * W 0) * convDen a b 1
    simp only [convNum, convDen]; ring

/-- A solution vanishing at `0` is a multiple of the convergent denominators. -/
theorem solution_eq_mul_convDen (a b E : ℕ → ℝ) (hE : IsSolution a b E) (hE0 : E 0 = 0) :
    E = fun n => E 1 * convDen a b n := by
  refine solution_unique a b E _ hE (IsSolution.const_mul (convDen_isSolution a b) (E 1)) ?_ ?_
  · show E 0 = E 1 * convDen a b 0
    rw [hE0]; simp [convDen]
  · show E 1 = E 1 * convDen a b 1
    simp [convDen]

/-- When `b` never vanishes the recurrence runs backwards: a solution that is eventually
zero is identically zero. This is where the skeleton's hypothesis `b n ≠ 0` enters
classically; the corrected Pincherle theorem below does not need it. -/
theorem solution_eq_zero_of_eventually_zero (a b Z : ℕ → ℝ) (hb : ∀ n : ℕ, 1 ≤ n → b n ≠ 0)
    (hZ : IsSolution a b Z) (N : ℕ) (h : ∀ m, N ≤ m → Z m = 0) : ∀ m, Z m = 0 := by
  induction N with
  | zero => exact fun m => h m (Nat.zero_le m)
  | succ N ih =>
    apply ih
    intro m hm
    obtain hEq | hlt := Nat.eq_or_lt_of_le hm
    · rw [← hEq]
      have h2 := hZ N
      rw [h (N + 2) (by omega), h (N + 1) (by omega)] at h2
      have h3 : b (N + 1) * Z N = 0 := by linear_combination -h2
      exact (mul_eq_zero.mp h3).resolve_left (hb (N + 1) (by omega))
    · exact h m hlt

/-- **Pincherle's theorem** (convergence direction). If `Z` is a minimal solution with
`Z 0 ≠ 0`, the convergents `P n / Q n` tend to `a 0 - Z 1 / Z 0`. -/
theorem pincherle (a b Z : ℕ → ℝ) (hZ : IsMinimal a b Z) (hZ0 : Z 0 ≠ 0) :
    Tendsto (fun n => convNum a b n / convDen a b n) atTop (𝓝 (a 0 - Z 1 / Z 0)) := by
  obtain ⟨hZs, D, hDs, hDZ, hDne, hlim⟩ := hZ
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = D 0 / Z 0 := ⟨_, rfl⟩
  -- E = D - c Z is a solution vanishing at 0, hence a multiple of Q; E 1 ≠ 0 since D ≠ c Z.
  have hEs : IsSolution a b (fun n => D n - c * Z n) := IsSolution.sub_smul hDs hZs c
  have hE0 : D 0 - c * Z 0 = 0 := by
    rw [hc, div_mul_eq_mul_div, mul_div_assoc, div_self hZ0, mul_one, sub_self]
  have hE1 : D 1 - c * Z 1 ≠ 0 := by
    intro h1
    apply hDZ c
    have hEz : (fun n => D n - c * Z n) = fun _ => 0 :=
      solution_unique a b _ _ hEs (zero_isSolution a b) hE0 h1
    funext n
    have hn : D n - c * Z n = 0 := congrFun hEz n
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith
  have hQ : ∀ n, convDen a b n = (D n - c * Z n) / (D 1 - c * Z 1) := by
    intro n
    have hn : D n - c * Z n = (D 1 - c * Z 1) * convDen a b n :=
      congrFun (solution_eq_mul_convDen a b _ hEs hE0) n
    rw [eq_div_iff hE1, mul_comm]
    exact hn.symm
  -- Z / Q = E 1 · (Z/D) / (1 - c · Z/D) → 0.
  have hu : Tendsto (fun n => (D 1 - c * Z 1) * (Z n / D n) / (1 - c * (Z n / D n))) atTop
      (𝓝 0) := by
    have h : Tendsto (fun n => (D 1 - c * Z 1) * (Z n / D n) / (1 - c * (Z n / D n))) atTop
        (𝓝 ((D 1 - c * Z 1) * 0 / (1 - c * 0))) :=
      (tendsto_const_nhds.mul hlim).div (tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim))
        (by norm_num : (1 : ℝ) - c * 0 ≠ 0)
    simp only [mul_zero, sub_zero, zero_div] at h
    exact h
  have hg : Tendsto (fun n => ((D 1 - c * Z 1) * (Z n / D n) / (1 - c * (Z n / D n)) -
      (Z 1 - a 0 * Z 0)) / Z 0) atTop (𝓝 ((0 - (Z 1 - a 0 * Z 0)) / Z 0)) :=
    (hu.sub tendsto_const_nhds).div_const (Z 0)
  have hlimval : (0 - (Z 1 - a 0 * Z 0)) / Z 0 = a 0 - Z 1 / Z 0 := by
    rw [sub_div, zero_div, sub_div, mul_div_assoc, div_self hZ0, mul_one]; ring
  rw [hlimval] at hg
  have hne : ∀ᶠ n in atTop, 1 - c * (Z n / D n) ≠ 0 :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim) :
      Tendsto (fun n => 1 - c * (Z n / D n)) atTop (𝓝 (1 - c * 0))).eventually_ne (by norm_num)
  refine hg.congr' ?_
  filter_upwards [hDne, hne] with n hD h1
  have hcombo : Z n = Z 0 * convNum a b n + (Z 1 - a 0 * Z 0) * convDen a b n :=
    congrFun (solution_eq_combo a b Z hZs) n
  have hDc : D n - c * Z n ≠ 0 := by
    have : D n - c * Z n = D n * (1 - c * (Z n / D n)) := by field_simp
    rw [this]; exact mul_ne_zero hD h1
  have hP : convNum a b n =
      (Z n - (Z 1 - a 0 * Z 0) * ((D n - c * Z n) / (D 1 - c * Z 1))) / Z 0 := by
    rw [eq_div_iff hZ0, ← hQ n]; linear_combination -hcombo
  rw [hQ n, hP]
  field_simp

/-! ### The skeleton's statement is false

Period-2 coefficients `a = 17/2, 0, 17/2, 0, …` and `b = -4, 1/4, -4, 1/4, …`.
`Z n = (1/2)^n` is a solution; the convergent denominators are `0, 1, 0, -4, 0, 16, …`,
vanishing at every even index. All hypotheses of the skeleton's `pincherle` hold
(`IsMinimalWeak`, `Z 0 ≠ 0`, `b n ≠ 0`), yet `P n / Q n` is `0` at even `n` and tends to
`8 = a 0 - Z 1 / Z 0` only along odd `n`, so it has no limit. -/

/-- Partial numerators of the counterexample: `17/2` at even `n`, `0` at odd `n`. -/
noncomputable def aCE (n : ℕ) : ℝ := if n % 2 = 0 then 17 / 2 else 0

/-- Partial denominators of the counterexample: `−4` at even `n`, `1/4` at odd `n`. -/
noncomputable def bCE (n : ℕ) : ℝ := if n % 2 = 0 then -4 else 1 / 4

/-- The counterexample's minimal solution `Z_n = 2^{−n}`. -/
noncomputable def zCE (n : ℕ) : ℝ := (1 / 2) ^ n

theorem zCE_isSolution : IsSolution aCE bCE zCE := by
  intro n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have ha : aCE (2 * k + 1) = 0 := by unfold aCE; rw [ite_eq_right (by omega)]
    have hb : bCE (2 * k + 1) = 1 / 4 := by unfold bCE; rw [ite_eq_right (by omega)]
    rw [ha, hb]; unfold zCE; ring
  · have ha : aCE (2 * k + 1 + 1) = 17 / 2 := by unfold aCE; rw [ite_eq_left (by omega)]
    have hb : bCE (2 * k + 1 + 1) = -4 := by unfold bCE; rw [ite_eq_left (by omega)]
    rw [ha, hb]; unfold zCE; ring

theorem qCE_formula (k : ℕ) :
    convDen aCE bCE (2 * k) = 0 ∧ convDen aCE bCE (2 * k + 1) = (-4) ^ k := by
  induction k with
  | zero => simp [convDen]
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    have ha0 : aCE (2 * k + 1) = 0 := by unfold aCE; rw [ite_eq_right (by omega)]
    have hb0 : bCE (2 * k + 1) = 1 / 4 := by unfold bCE; rw [ite_eq_right (by omega)]
    have ha1 : aCE (2 * k + 1 + 1) = 17 / 2 := by unfold aCE; rw [ite_eq_left (by omega)]
    have hb1 : bCE (2 * k + 1 + 1) = -4 := by unfold bCE; rw [ite_eq_left (by omega)]
    have hQ2 : convDen aCE bCE (2 * k + 2) = 0 := by
      rw [convDen_isSolution aCE bCE (2 * k), ha0, hb0, h0, h1]; ring
    have hQ3 : convDen aCE bCE (2 * k + 1 + 2) = (-4) ^ (k + 1) := by
      rw [convDen_isSolution aCE bCE (2 * k + 1), ha1, hb1, h1]
      have h2 : convDen aCE bCE (2 * k + 1 + 1) = 0 := hQ2
      rw [h2]; ring
    refine ⟨?_, ?_⟩
    · rw [show 2 * (k + 1) = 2 * k + 2 by ring]; exact hQ2
    · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring]; exact hQ3

theorem pCE_formula (n : ℕ) : convNum aCE bCE n = zCE n + 8 * convDen aCE bCE n := by
  have hP : zCE n = zCE 0 * convNum aCE bCE n + (zCE 1 - aCE 0 * zCE 0) * convDen aCE bCE n :=
    congrFun (solution_eq_combo aCE bCE zCE zCE_isSolution) n
  have hz0 : zCE 0 = 1 := by simp [zCE]
  have hz1 : zCE 1 = 1 / 2 := by simp [zCE]
  have ha0 : aCE 0 = 17 / 2 := by unfold aCE; rw [ite_eq_left (by decide)]
  rw [hz0, hz1, ha0] at hP
  linear_combination -hP

theorem zCE_isMinimalWeak : IsMinimalWeak aCE bCE zCE := by
  refine ⟨zCE_isSolution, convDen aCE bCE, convDen_isSolution aCE bCE, ?_, ?_⟩
  · intro c h
    have h0 : (0 : ℝ) = c * (1 / 2) ^ 0 := congrFun h 0
    have h1 : (1 : ℝ) = c * (1 / 2) ^ 1 := congrFun h 1
    norm_num at h0 h1
    linarith
  · refine squeeze_zero_norm (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num) :
        Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0))
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [(qCE_formula k).1, div_zero, norm_zero]; positivity
    · unfold zCE
      rw [(qCE_formula k).2, norm_div, norm_pow, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      exact div_le_self (by positivity) (one_le_pow₀ (by norm_num))

theorem bCE_ne_zero (n : ℕ) : bCE n ≠ 0 := by
  unfold bCE; split_ifs <;> norm_num

/-- The skeleton's `pincherle` statement fails for `aCE, bCE, zCE`: every hypothesis holds
(`zCE_isMinimalWeak`, `zCE 0 ≠ 0`, `bCE_ne_zero`) but the convergents do not converge. -/
theorem technion_pincherle_fails :
    ¬ Tendsto (fun n => convNum aCE bCE n / convDen aCE bCE n) atTop
        (𝓝 (aCE 0 - zCE 1 / zCE 0)) := by
  intro hT
  have h4 : ∀ k : ℕ, ((-4 : ℝ)) ^ k ≠ 0 := fun k => pow_ne_zero k (by norm_num)
  have heven : Tendsto (fun k : ℕ => convNum aCE bCE (2 * k) / convDen aCE bCE (2 * k)) atTop
      (𝓝 0) :=
    tendsto_const_nhds.congr (fun k => by rw [(qCE_formula k).1, div_zero])
  have hkey : ∀ k : ℕ, zCE (2 * k + 1) / (-4) ^ k = 1 / 2 * (-1 / 16) ^ k := by
    intro k
    unfold zCE
    rw [div_eq_iff (h4 k), pow_succ, pow_mul, mul_assoc, ← mul_pow, mul_comm]
    norm_num
  have h16 : Tendsto (fun k : ℕ => ((-1 / 16 : ℝ)) ^ k) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    rw [abs_lt]; constructor <;> norm_num
  have hodd : Tendsto (fun k : ℕ => convNum aCE bCE (2 * k + 1) / convDen aCE bCE (2 * k + 1))
      atTop (𝓝 8) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (8 : ℝ)) atTop (𝓝 8)).add
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2))).mul h16)
    rw [mul_zero, add_zero] at h
    refine h.congr (fun k => ?_)
    show (8 : ℝ) + 1 / 2 * (-1 / 16) ^ k = _
    rw [pCE_formula, (qCE_formula k).2, add_div, mul_div_assoc, div_self (h4 k), mul_one, hkey k]
    ring
  have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_mono (fun k => (by omega : k ≤ 2 * k)) tendsto_id
  have h2' : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => (by omega : k ≤ 2 * k + 1)) tendsto_id
  have hE := tendsto_nhds_unique (hT.comp h2) heven
  have hO := tendsto_nhds_unique (hT.comp h2') hodd
  rw [hE] at hO
  norm_num at hO

/-! ### Minimality from ratio limits

Poincaré–Perron supplies a basis `u_s, u_d` of solutions with `u(n+1)/u(n) → λ_s, λ_d`, the roots
of the limiting characteristic polynomial. The step from there to Pincherle is that a solution
whose ratio tends to the root of smaller modulus is minimal; Mathlib's ratio test does it. -/

theorem isMinimal_of_ratio (a b Z D : ℕ → ℝ) (ls ld : ℝ) (hZ : IsSolution a b Z)
    (hD : IsSolution a b D) (hZne : ∀ᶠ n in atTop, Z n ≠ 0) (hDne : ∀ᶠ n in atTop, D n ≠ 0)
    (hZr : Tendsto (fun n => Z (n + 1) / Z n) atTop (𝓝 ls))
    (hDr : Tendsto (fun n => D (n + 1) / D n) atTop (𝓝 ld)) (hlt : |ls| < |ld|) :
    IsMinimal a b Z := by
  have hld : ld ≠ 0 := by
    intro h
    rw [h, abs_zero] at hlt
    exact absurd hlt (not_lt.mpr (abs_nonneg ls))
  refine ⟨hZ, D, hD, ?_, hDne, ?_⟩
  · intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨n, hn⟩ := hDne.exists
      apply hn
      rw [hc]
      simp
    have hsame : Tendsto (fun n => D (n + 1) / D n) atTop (𝓝 ls) := by
      refine hZr.congr (fun n => ?_)
      rw [hc]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_div_mul_left _ _ hc0]
    have heq := tendsto_nhds_unique hsame hDr
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · have hf : ∀ᶠ n in atTop, Z n / D n ≠ 0 := by
      filter_upwards [hZne, hDne] with n h1 h2
      exact div_ne_zero h1 h2
    have hr0 : Tendsto (fun n => ‖Z (n + 1) / Z n / (D (n + 1) / D n)‖) atTop (𝓝 ‖ls / ld‖) :=
      (hZr.div hDr hld).norm
    have hfun : (fun n => ‖Z (n + 1) / D (n + 1)‖ / ‖Z n / D n‖) =
        fun n => ‖Z (n + 1) / Z n / (D (n + 1) / D n)‖ := by
      funext n
      rw [← norm_div, div_div_div_comm]
    have hr : Tendsto (fun n => ‖Z (n + 1) / D (n + 1)‖ / ‖Z n / D n‖) atTop (𝓝 ‖ls / ld‖) := by
      rw [hfun]
      exact hr0
    have hl1 : ‖ls / ld‖ < 1 := by
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, div_lt_one (abs_pos.mpr hld)]
      exact hlt
    exact (summable_of_ratio_test_tendsto_lt_one (f := fun n => Z n / D n) hl1 hf
      hr).tendsto_atTop_zero

/-- Pincherle from ratio limits: a solution `Z` with `Z 0 ≠ 0` whose ratio tends to the root of
smaller modulus, beside a solution whose ratio tends to the other root, determines the limit of
the convergents. -/
theorem pincherle_of_ratio (a b Z D : ℕ → ℝ) (ls ld : ℝ) (hZ : IsSolution a b Z)
    (hD : IsSolution a b D) (hZne : ∀ᶠ n in atTop, Z n ≠ 0) (hDne : ∀ᶠ n in atTop, D n ≠ 0)
    (hZr : Tendsto (fun n => Z (n + 1) / Z n) atTop (𝓝 ls))
    (hDr : Tendsto (fun n => D (n + 1) / D n) atTop (𝓝 ld)) (hlt : |ls| < |ld|)
    (hZ0 : Z 0 ≠ 0) :
    Tendsto (fun n => convNum a b n / convDen a b n) atTop (𝓝 (a 0 - Z 1 / Z 0)) :=
  pincherle a b Z (isMinimal_of_ratio a b Z D ls ld hZ hD hZne hDne hZr hDr hlt) hZ0

/-! ### Problem 2.1: the limits of the rescaled coefficients

After the coboundary rescaling in the Technion skeleton, the recurrence for `F_n` has coefficients
`A(x), B(x)` below (their `A`, `B`), and `A(n) → −297/2`, `B(n) → 729/4`: the characteristic
polynomial `λ² + (297/2)λ − 729/4` of `lamS_root`, `lamD_root`. Both limits are stated without proof
in the skeleton (`A_limit`, `B_limit`). -/

/-- The rescaled middle coefficient of the 2.1 recurrence. -/
noncomputable def A21 (x : ℝ) : ℝ :=
  -(3 * (6 * x + 7) * (6 * x + 11) * (220 * x ^ 3 + 484 * x ^ 2 + 301 * x + 42)) /
    (8 * (x + 1) ^ 2 * (2 * x + 3) ^ 2 * (5 * x + 1))

/-- The rescaled trailing coefficient of the 2.1 recurrence. -/
noncomputable def B21 (x : ℝ) : ℝ :=
  9 * (5 * x + 6) * (6 * x + 1) * (6 * x + 5) * (6 * x + 7) * (6 * x + 11) /
    (16 * (x + 1) ^ 2 * (2 * x + 3) ^ 2 * (5 * x + 1))

/-- `A21 n` as a rational function of `u = 1/n`: numerator. -/
noncomputable def A21num (u : ℝ) : ℝ :=
  -(3 * (6 + 7 * u) * (6 + 11 * u) * (220 + 484 * u + 301 * u ^ 2 + 42 * u ^ 3))

/-- `A21 n` as a rational function of `u = 1/n`: denominator. -/
noncomputable def A21den (u : ℝ) : ℝ := 8 * (1 + u) ^ 2 * (2 + 3 * u) ^ 2 * (5 + u)

/-- `B21 n` as a rational function of `u = 1/n`: numerator. -/
noncomputable def B21num (u : ℝ) : ℝ :=
  9 * (5 + 6 * u) * (6 + u) * (6 + 5 * u) * (6 + 7 * u) * (6 + 11 * u)

/-- `B21 n` as a rational function of `u = 1/n`: denominator. -/
noncomputable def B21den (u : ℝ) : ℝ := 16 * (1 + u) ^ 2 * (2 + 3 * u) ^ 2 * (5 + u)

theorem tendsto_inv_natCast : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

theorem A21_limit : Tendsto (fun n : ℕ => A21 n) atTop (𝓝 (-297 / 2)) := by
  have hp : Continuous A21num := by unfold A21num; fun_prop
  have hq : Continuous A21den := by unfold A21den; fun_prop
  have hq0 : A21den 0 ≠ 0 := by norm_num [A21den]
  have h : Tendsto (fun n : ℕ => A21num ((n : ℝ)⁻¹) / A21den ((n : ℝ)⁻¹)) atTop
      (𝓝 (A21num 0 / A21den 0)) :=
    ((hp.tendsto 0).comp tendsto_inv_natCast).div ((hq.tendsto 0).comp tendsto_inv_natCast) hq0
  have hval : A21num 0 / A21den 0 = -297 / 2 := by norm_num [A21num, A21den]
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [A21num, A21den, A21]
  field_simp

theorem B21_limit : Tendsto (fun n : ℕ => B21 n) atTop (𝓝 (729 / 4)) := by
  have hp : Continuous B21num := by unfold B21num; fun_prop
  have hq : Continuous B21den := by unfold B21den; fun_prop
  have hq0 : B21den 0 ≠ 0 := by norm_num [B21den]
  have h : Tendsto (fun n : ℕ => B21num ((n : ℝ)⁻¹) / B21den ((n : ℝ)⁻¹)) atTop
      (𝓝 (B21num 0 / B21den 0)) :=
    ((hp.tendsto 0).comp tendsto_inv_natCast).div ((hq.tendsto 0).comp tendsto_inv_natCast) hq0
  have hval : B21num 0 / B21den 0 = 729 / 4 := by norm_num [B21num, B21den]
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [B21num, B21den, B21]
  field_simp

end RamanujanChallenge
