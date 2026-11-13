/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import RamanujanChallenge.Exact
import RamanujanChallenge.Pincherle

/-!
Problem 2.1 of the Ramanujan Challenge, closed: the polynomial continued fraction
`a_n = −220n³ − 484n² − 301n − 42`, `b_n = 4n²(2n+1)²(5n−4)(5n+6)` converges to `6/(3 − π)`
(`pcf21_tendsto`).

The route is the official one (*Ramanujan Challenge Proofs*, Technion, 2 August 2026, §4,
trajectory `(1,1,3)` of the ₂F₁ conservative matrix field), step by step:

* **Euler's integral (Eq. 28).**
  `F_n = Γ(3n+½)/(Γ(n+½)Γ(2n)) ∫₀¹ t^{n−½}(1−t)^{2n−1}(1−t/2)^{−n−½} dt`.
  Under the paper's own substitution `t = 2u²/(1+u²)` (`t = 2 sin²θ`, `u = tan θ`, Eqs. 36–37)
  the integral is `2^{n+3/2} ∫₀¹ u^{2n}(1−u²)^{2n−1}/(1+u²)^{2n} du`. Here `F21 m = F_{m+1}` is
  defined by that formula: `F21 m = kap21 m * K21 m`, `K21 m = ∫₀¹ w21 m`,
  `w21 m u = u²(1−u²)/(1+u²)² · G(u)^m`, `G(u) = u²(1−u²)²/(1+u²)²`.
* **Lemma 3 (scalar recurrence).** `F_{n+2} = A(n)F_{n+1} + B(n)F_n` for every `n ≥ 1`
  (`F21_rec`), with `A = midCoeff21 = a/r`, `B = tailCoeff21 = b/(r·r(·−1))`. Proved by
  creative telescoping:
  `Phi21 m` is an explicit antiderivative (`hasDerivAt_Phi21`) of
  `P₀ω_n + P₁ω_{n+1} + P₂ω_{n+2}` with `P₀ = −2n(2n+1)(5n+6)`, `P₁ = 220n³+484n²+301n+42 = −a_n`,
  `P₂ = 2(n+1)(2n+3)(5n+1)`; it vanishes at `u = 0` and `u = 1`, so `K21_rec` follows from
  the fundamental theorem of calculus, and the Gamma prefactor contributes the ratio
  `kap21_succ`.
* **Lemma 7 (anchors).** `F_1 = (15√2/2)(π − 3)`, `F_2 = (1155√2/8)(22 − 7π)` (`F21_zero`,
  `F21_one`), from explicit arctan antiderivatives (`K21_zero`, `K21_one`).
* **Lemma 4 (rescaling, Eqs. 21–24).** `r_n A(n) = a_n`, `r_n r_{n−1} B(n) = b_n`, and
  `X_n = s_n F_{n+2}` solves the challenge recurrence (`Z21_mem_solutions`, `Z21 m = X_{m−1}`).
* **Lemmas 5–6 (minimality).** Instead of Poincaré–Perron plus Stirling, a direct dominance
  bound for this recurrence: `−A(x) ≥ 100` for `x ≥ 0` and `b_n ≥ 0`, so the convergent
  denominators alternate in sign with `|Q_{k+1}| ≥ s_k·100^k` (`denom21_bound`), while
  `0 < F_n ≤ 15√2·20^{n−1}` (`F21_pos`, `F21_le`); hence `|X/Q| ≤ 300√2·5^{−k} → 0`
  (`norm_Z21_div_denom21_le`), so `X` is recessive, dominated by `Q` (`Z21_isRecessive`).
* **Theorem 2.** Pincherle's theorem (`CFData.tendsto_convergent`) then gives
  `P_n/Q_n → a_0 − X_0/X_{−1} = −42 − 24F_2/(77F_1) = 6/(3 − π)`.

`Euler21.lean` proves that this `F_n` is Mathlib's `ordinaryHypergeometric (n+½) (n+½) (3n+½) (1/2)`
(`F21_eq_hypergeometric`).

Every identity here was checked in SymPy before it was written in Lean
(`scripts/precheck3.py`).
-/

open Filter Topology Asymptotics

namespace RamanujanChallenge

/-- `G(u) = u²(1−u²)²/(1+u²)²`: the ratio `ω_{n+1}/ω_n` of consecutive integrands
(`h(t)` of the official proof after `t = 2u²/(1+u²)`). -/
noncomputable def G21 (u : ℝ) : ℝ := u ^ 2 * (1 - u ^ 2) ^ 2 / (1 + u ^ 2) ^ 2
/-- The integrand `ω_{m+1}(u) = u^{2m+2}(1−u²)^{2m+1}/(1+u²)^{2m+2}`. -/
noncomputable def w21 (m : ℕ) (u : ℝ) : ℝ := u ^ 2 * (1 - u ^ 2) / (1 + u ^ 2) ^ 2 * G21 u ^ m
/-- The polynomial factor of the telescoping certificate. -/
noncomputable def q21 (n u : ℝ) : ℝ :=
  (10 * n ^ 2 + 12 * n + 2) * u ^ 8 + (30 * n ^ 2 + 41 * n + 6) * u ^ 6
    - (60 * n ^ 2 + 82 * n + 18) * u ^ 4 - (30 * n ^ 2 + 51 * n + 14) * u ^ 2
    + (10 * n ^ 2 + 12 * n)
/-- The rational part of the certificate. -/
noncomputable def N21 (n u : ℝ) : ℝ := -(u ^ 3 * (1 - u ^ 2) ^ 2 * q21 n u / (1 + u ^ 2) ^ 5)
/-- The certificate `Φ_m(u) = −u³(1−u²)² q(m+1,u)/(1+u²)⁵ · G(u)^m`. -/
noncomputable def Phi21 (m : ℕ) (u : ℝ) : ℝ := N21 ((m : ℝ) + 1) u * G21 u ^ m

theorem one_add_sq_ne (u : ℝ) : 1 + u ^ 2 ≠ 0 := by positivity

theorem hasDerivAt_G21 (u : ℝ) :
    HasDerivAt G21
      ((2 * u * (1 - u ^ 2) ^ 2 + u ^ 2 * (2 * (1 - u ^ 2) * (-(2 * u)))) / (1 + u ^ 2) ^ 2
      - u ^ 2 * (1 - u ^ 2) ^ 2 * (2 * (1 + u ^ 2) * (2 * u)) / ((1 + u ^ 2) ^ 2) ^ 2) u := by
  have h1 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
    simpa using hasDerivAt_pow 2 u
  have h2 : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-(2 * u)) u := by
    simpa using (hasDerivAt_const u (1:ℝ)).fun_sub h1
  have h3 : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_const u (1:ℝ)).fun_add h1
  have h := (h1.fun_mul (h2.fun_pow 2)).fun_div (h3.fun_pow 2) (pow_ne_zero 2 (one_add_sq_ne u))
  convert h using 1
  · rfl
  have hd := one_add_sq_ne u
  norm_num
  field_simp

theorem hasDerivAt_N21 (n u : ℝ) : HasDerivAt (N21 n) (-(
    ((3 * u ^ 2 * (1 - u ^ 2) ^ 2 + u ^ 3 * (2 * (1 - u ^ 2) * (-(2 * u)))) * q21 n u
      + u ^ 3 * (1 - u ^ 2) ^ 2 * ((10 * n ^ 2 + 12 * n + 2) * (8 * u ^ 7)
        + (30 * n ^ 2 + 41 * n + 6) * (6 * u ^ 5)
        - (60 * n ^ 2 + 82 * n + 18) * (4 * u ^ 3) - (30 * n ^ 2 + 51 * n + 14) * (2 * u)))
          / (1 + u ^ 2) ^ 5
    - u ^ 3 * (1 - u ^ 2) ^ 2 * q21 n u * (5 * (1 + u ^ 2) ^ 4 * (2 * u))
      / ((1 + u ^ 2) ^ 5) ^ 2)) u := by
  have hp : ∀ k : ℕ, HasDerivAt (fun u : ℝ => u ^ k) (k * u ^ (k - 1)) u :=
    fun k => hasDerivAt_pow k u
  have h1 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by simpa using hp 2
  have h2 : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-(2 * u)) u := by
    simpa using (hasDerivAt_const u (1:ℝ)).fun_sub h1
  have h3 : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_const u (1:ℝ)).fun_add h1
  have hq : HasDerivAt (q21 n) ((10 * n ^ 2 + 12 * n + 2) * (8 * u ^ 7)
        + (30 * n ^ 2 + 41 * n + 6) * (6 * u ^ 5)
        - (60 * n ^ 2 + 82 * n + 18) * (4 * u ^ 3) - (30 * n ^ 2 + 51 * n + 14) * (2 * u)) u := by
    have := (((((hp 8).const_mul (10 * n ^ 2 + 12 * n + 2)).fun_add
      ((hp 6).const_mul (30 * n ^ 2 + 41 * n + 6))).fun_sub
      ((hp 4).const_mul (60 * n ^ 2 + 82 * n + 18))).fun_sub
      ((hp 2).const_mul (30 * n ^ 2 + 51 * n + 14))).fun_add
      (hasDerivAt_const u (10 * n ^ 2 + 12 * n))
    convert this using 1
    · funext x; unfold q21; ring
    · norm_num
  have h3' : HasDerivAt (fun u : ℝ => u ^ 3) (3 * u ^ 2) u := by simpa using hp 3
  have h := (((h3'.fun_mul (h2.fun_pow 2)).fun_mul hq).fun_div (h3.fun_pow 5)
    (pow_ne_zero 5 (one_add_sq_ne u))).fun_neg
  convert h using 1
  · rfl
  have hd := one_add_sq_ne u
  norm_num
  field_simp
  ring

/-- The certificate: `Φ' = P0 ω_m + P1 ω_{m+1} + P2 ω_{m+2}`. -/
theorem hasDerivAt_Phi21 (m : ℕ) (u : ℝ) : HasDerivAt (Phi21 m)
    (-(2 * ((m:ℝ) + 1) * (2 * ((m:ℝ) + 1) + 1) * (5 * ((m:ℝ) + 1) + 6)) * w21 m u
      + (220 * ((m:ℝ) + 1) ^ 3 + 484 * ((m:ℝ) + 1) ^ 2 + 301 * ((m:ℝ) + 1) + 42) * w21 (m + 1) u
      + 2 * ((m:ℝ) + 2) * (2 * ((m:ℝ) + 1) + 3) * (5 * ((m:ℝ) + 1) + 1) * w21 (m + 2) u) u := by
  have h := (hasDerivAt_N21 ((m:ℝ) + 1) u).fun_mul ((hasDerivAt_G21 u).fun_pow m)
  convert h using 1
  · rfl
  have hd := one_add_sq_ne u
  rcases m with _ | k
  · simp only [N21, G21, w21, q21, pow_zero, Nat.cast_zero, zero_mul, mul_zero, add_zero, mul_one,
      zero_add]
    field_simp
    ring
  · simp only [N21, G21, w21, q21, Nat.add_sub_cancel, pow_succ, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

/-- `K21 m = ∫₀¹ ω_{m+1}(u) du`. -/
noncomputable def K21 (m : ℕ) : ℝ := ∫ u in (0:ℝ)..1, w21 m u

theorem continuous_G21 : Continuous G21 := by
  unfold G21
  exact Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)

theorem continuous_w21 (m : ℕ) : Continuous (w21 m) := by
  unfold w21
  exact (Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)).mul
    (continuous_G21.pow m)

theorem K21_rec (m : ℕ) :
    2 * ((m:ℝ) + 2) * (2 * ((m:ℝ) + 1) + 3) * (5 * ((m:ℝ) + 1) + 1) * K21 (m + 2) =
      2 * ((m:ℝ) + 1) * (2 * ((m:ℝ) + 1) + 1) * (5 * ((m:ℝ) + 1) + 6) * K21 m
        - (220 * ((m:ℝ) + 1) ^ 3 + 484 * ((m:ℝ) + 1) ^ 2 + 301 * ((m:ℝ) + 1) + 42)
          * K21 (m + 1) := by
  have hi : ∀ k, IntervalIntegrable (w21 k) MeasureTheory.volume 0 1 :=
    fun k => (continuous_w21 k).intervalIntegrable 0 1
  have hc : ∀ (c : ℝ) k, IntervalIntegrable (fun u => c * w21 k u) MeasureTheory.volume 0 1 :=
    fun c k => ((continuous_w21 k).const_smul c).intervalIntegrable 0 1
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun x _ => hasDerivAt_Phi21 m x) (((hc _ m).add (hc _ (m + 1))).add (hc _ (m + 2)))
  have hb : Phi21 m 1 - Phi21 m 0 = 0 := by simp [Phi21, N21]
  rw [hb, intervalIntegral.integral_add ((hc _ m).add (hc _ (m + 1))) (hc _ (m + 2)),
    intervalIntegral.integral_add (hc _ m) (hc _ (m + 1)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hF
  unfold K21
  linear_combination hF

/-- Antiderivative for the first anchor. -/
theorem K21_zero : K21 0 = (Real.pi - 3) / 2 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun u => 2 * Real.arctan u - u - u / (1 + u ^ 2)) (w21 0 x) x := by
    intro x
    have hx := one_add_sq_ne x
    have h := (((Real.hasDerivAt_arctan x).const_mul 2).fun_sub (hasDerivAt_id x)).fun_sub
      ((hasDerivAt_id x).fun_div ((hasDerivAt_const x (1:ℝ)).fun_add (hasDerivAt_pow 2 x)) hx)
    convert h using 1
    · funext u; simp
    simp only [w21, pow_zero, mul_one, id]
    norm_num
    field_simp
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun x _ => hd x)
    ((continuous_w21 0).intervalIntegrable 0 1)
  unfold K21
  rw [h, Real.arctan_one, Real.arctan_zero]
  ring

theorem K21_one : K21 1 = 11 - 7 * Real.pi / 2 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun u => (33 * u ^ 5 + 50 * u ^ 3 + 21 * u) / (3 * (1 + u ^ 2) ^ 3)
      - u ^ 3 / 3 + 7 * u - 14 * Real.arctan u) (w21 1 x) x := by
    intro x
    have hx := one_add_sq_ne x
    have hp : ∀ k : ℕ, HasDerivAt (fun u : ℝ => u ^ k) (k * x ^ (k - 1)) x :=
      fun k => hasDerivAt_pow k x
    have hnum := (((hp 5).const_mul 33).fun_add ((hp 3).const_mul 50)).fun_add ((hp 1).const_mul 21)
    have hden := (((hasDerivAt_const x (1:ℝ)).fun_add (hp 2)).fun_pow 3).const_mul 3
    have h := (((hnum.fun_div hden (by positivity)).fun_sub ((hp 3).div_const 3)).fun_add
      ((hp 1).const_mul 7)).fun_sub ((Real.hasDerivAt_arctan x).const_mul 14)
    convert h using 1
    · funext u; simp
    simp only [w21, G21, pow_one]
    norm_num
    field_simp
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun x _ => hd x)
    ((continuous_w21 1).intervalIntegrable 0 1)
  unfold K21
  rw [h, Real.arctan_one, Real.arctan_zero]
  ring

theorem w21_pos (m : ℕ) {u : ℝ} (h0 : 0 < u) (h1 : u < 1) : 0 < w21 m u := by
  have h2 : 0 < 1 - u ^ 2 := by nlinarith
  unfold w21 G21
  positivity

theorem w21_le_one (m : ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : w21 m u ≤ 1 := by
  have h2 : 0 ≤ 1 - u ^ 2 := by nlinarith
  have hu2 : u ^ 2 ≤ 1 := by nlinarith
  have hd : 1 ≤ (1 + u ^ 2) ^ 2 := by nlinarith
  have hG0 : 0 ≤ G21 u := by unfold G21; positivity
  have hG1 : G21 u ≤ 1 := by
    unfold G21
    rw [div_le_one (by positivity)]
    have : (1 - u ^ 2) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hw1 : u ^ 2 * (1 - u ^ 2) / (1 + u ^ 2) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hw0 : 0 ≤ u ^ 2 * (1 - u ^ 2) / (1 + u ^ 2) ^ 2 := by positivity
  unfold w21
  calc u ^ 2 * (1 - u ^ 2) / (1 + u ^ 2) ^ 2 * G21 u ^ m ≤ 1 * 1 := by
        apply mul_le_mul hw1 (pow_le_one₀ hG0 hG1) (by positivity) (by norm_num)
    _ = 1 := by norm_num

theorem K21_pos (m : ℕ) : 0 < K21 m :=
  intervalIntegral.intervalIntegral_pos_of_pos_on ((continuous_w21 m).intervalIntegrable 0 1)
    (fun _ hx => w21_pos m hx.1 hx.2) (by norm_num)

theorem K21_le_one (m : ℕ) : K21 m ≤ 1 := by
  have h := intervalIntegral.integral_mono_on (a := 0) (b := 1) (by norm_num)
    ((continuous_w21 m).intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
    (fun x hx => w21_le_one m hx.1 hx.2)
  simpa [K21] using h

/-! ### The Euler-integral normalisation and the hypergeometric sequence -/

/-- `κ_{m+1} = Γ(3n+1/2)/(Γ(n+1/2)Γ(2n)) · 2^{n+3/2}` with `n = m+1`. -/
noncomputable def kap21 (m : ℕ) : ℝ :=
  Real.Gamma (3 * ((m:ℝ) + 1) + 1 / 2) /
      (Real.Gamma (((m:ℝ) + 1) + 1 / 2) * Real.Gamma (2 * ((m:ℝ) + 1)))
    * 2 ^ (m + 2) * Real.sqrt 2

/-- `F21 m = F_{m+1}`. -/
noncomputable def F21 (m : ℕ) : ℝ := kap21 m * K21 m

theorem kap21_pos (m : ℕ) : 0 < kap21 m := by
  unfold kap21
  have h1 := Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < 3 * ((m:ℝ) + 1) + 1 / 2)
  have h2 := Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < ((m:ℝ) + 1) + 1 / 2)
  have h3 := Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < 2 * ((m:ℝ) + 1))
  have h4 : 0 < Real.sqrt 2 := by positivity
  positivity

theorem kap21_succ (m : ℕ) :
    kap21 (m + 1) =
      3 * (6 * (m:ℝ) + 7) * (6 * (m:ℝ) + 11) / (4 * ((m:ℝ) + 1) * (2 * (m:ℝ) + 3)) * kap21 m := by
  unfold kap21
  set x : ℝ := 3 * ((m:ℝ) + 1) + 1 / 2 with hx
  set y : ℝ := ((m:ℝ) + 1) + 1 / 2 with hy
  set z : ℝ := 2 * ((m:ℝ) + 1) with hz
  have ex : 3 * (((m + 1 : ℕ) : ℝ) + 1) + 1 / 2 = x + 1 + 1 + 1 := by rw [hx]; push_cast; ring
  have ey : (((m + 1 : ℕ) : ℝ) + 1) + 1 / 2 = y + 1 := by rw [hy]; push_cast; ring
  have ez : 2 * (((m + 1 : ℕ) : ℝ) + 1) = z + 1 + 1 := by rw [hz]; push_cast; ring
  have hx0 : 0 < x := by rw [hx]; positivity
  have hy0 : 0 < y := by rw [hy]; positivity
  have hz0 : 0 < z := by rw [hz]; positivity
  rw [ex, ey, ez, Real.Gamma_add_one (by positivity), Real.Gamma_add_one (by positivity),
    Real.Gamma_add_one hx0.ne', Real.Gamma_add_one hy0.ne', Real.Gamma_add_one (by positivity),
    Real.Gamma_add_one hz0.ne']
  have g1 := (Real.Gamma_pos_of_pos hx0).ne'
  have g2 := (Real.Gamma_pos_of_pos hy0).ne'
  have g3 := (Real.Gamma_pos_of_pos hz0).ne'
  rw [hx, hy, hz]
  field_simp
  ring

theorem kap21_zero : kap21 0 = 15 * Real.sqrt 2 := by
  unfold kap21
  have e1 : 3 * (((0:ℕ):ℝ) + 1) + 1 / 2 = (3 / 2 + 1) + 1 := by norm_num
  have e2 : (((0:ℕ):ℝ) + 1) + 1 / 2 = 3 / 2 := by norm_num
  have e3 : 2 * (((0:ℕ):ℝ) + 1) = 2 := by norm_num
  rw [e1, e2, e3, Real.Gamma_add_one (by norm_num), Real.Gamma_add_one (by norm_num),
    Real.Gamma_two]
  have g := (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 3 / 2)).ne'
  field_simp
  norm_num

theorem kap21_one : kap21 1 = 1155 * Real.sqrt 2 / 4 := by
  rw [kap21_succ, kap21_zero]; norm_num; ring

/-- **Anchor `F_1`** (Lemma 7 of the official proof): `F_1 = (15√2/2)(π − 3)`. -/
theorem F21_zero : F21 0 = 15 * Real.sqrt 2 / 2 * (Real.pi - 3) := by
  rw [F21, kap21_zero, K21_zero]; ring

/-- **Anchor `F_2`** (Lemma 7 of the official proof): `F_2 = (1155√2/8)(22 − 7π)`. -/
theorem F21_one : F21 1 = 1155 * Real.sqrt 2 / 8 * (22 - 7 * Real.pi) := by
  rw [F21, kap21_one, K21_one]; ring

theorem F21_pos (m : ℕ) : 0 < F21 m := mul_pos (kap21_pos m) (K21_pos m)

/-! ### The challenge coefficients, the normaliser `r_n`, and the rescaled coefficients -/

/-- `a_n` of Problem 2.1 over `ℝ`. -/
noncomputable def a21 (n : ℕ) : ℝ := -220 * (n:ℝ) ^ 3 - 484 * (n:ℝ) ^ 2 - 301 * (n:ℝ) - 42

/-- `b_n` of Problem 2.1 over `ℝ`. -/
noncomputable def b21 (n : ℕ) : ℝ :=
  4 * (n:ℝ) ^ 2 * (2 * (n:ℝ) + 1) ^ 2 * (5 * (n:ℝ) - 4) * (5 * (n:ℝ) + 6)

theorem a21_eq_a1 (n : ℕ) : a21 n = ((a1 n : ℚ) : ℝ) := by simp [a21, a1]
theorem b21_eq_b1 (n : ℕ) : b21 n = ((b1 n : ℚ) : ℝ) := by simp [b21, b1]

/-- The challenge continued fraction of Problem 2.1: partial denominators `a_n`, partial
numerators `b_n`. -/
noncomputable def cf21 : CFData := ⟨a21, b21⟩

@[simp] theorem cf21_partialDen (n : ℕ) : cf21.partialDen n = a21 n := rfl
@[simp] theorem cf21_partialNum (n : ℕ) : cf21.partialNum n = b21 n := rfl

/-- The normaliser `r_n` of Equation (21), written as `(8/3) ((x+1)(2x+3))² (5x+1)` over
`(6x+7)(6x+11)`. -/
noncomputable def r21 (x : ℝ) : ℝ :=
  8 / 3 * ((x + 1) * (2 * x + 3)) ^ 2 * (5 * x + 1) / ((6 * x + 7) * (6 * x + 11))

theorem r21_pos_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 < r21 x := by unfold r21; positivity

theorem r21_pos (n : ℕ) : 0 < r21 n := r21_pos_of_nonneg (Nat.cast_nonneg n)

/-- The rescaled middle coefficient of Lemma 3: the cubic `a(x)` divided by the normaliser
`r(x)`, so that `r_n A(n) = a_n` holds by construction. -/
noncomputable def midCoeff21 (x : ℝ) : ℝ := (-220 * x ^ 3 - 484 * x ^ 2 - 301 * x - 42) / r21 x

/-- The rescaled trailing coefficient of Lemma 3: the sextic `b(x)` divided by
`r(x) r(x − 1)`, so that `r_n r_{n−1} B(n) = b_n` holds by construction. -/
noncomputable def tailCoeff21 (x : ℝ) : ℝ :=
  4 * x ^ 2 * (2 * x + 1) ^ 2 * (5 * x - 4) * (5 * x + 6) / (r21 x * r21 (x - 1))

/-- **Lemma 3 of the official proof**: `F_{n+2} = A(n) F_{n+1} + B(n) F_n` for every `n ≥ 1`
(here `n = m + 1`), with `A = midCoeff21`, `B = tailCoeff21`. -/
theorem F21_rec (m : ℕ) :
    F21 (m + 2) = midCoeff21 ((m + 1 : ℕ) : ℝ) * F21 (m + 1) +
      tailCoeff21 ((m + 1 : ℕ) : ℝ) * F21 m := by
  have hK := K21_rec m
  have k1 := kap21_succ m
  have k2 := kap21_succ (m + 1)
  have hP : 2 * ((m:ℝ) + 2) * (2 * ((m:ℝ) + 1) + 3) * (5 * ((m:ℝ) + 1) + 1) ≠ 0 := by positivity
  have hK2 : K21 (m + 2) = (2 * ((m:ℝ) + 1) * (2 * ((m:ℝ) + 1) + 1) * (5 * ((m:ℝ) + 1) + 6) * K21 m
        - (220 * ((m:ℝ) + 1) ^ 3 + 484 * ((m:ℝ) + 1) ^ 2 + 301 * ((m:ℝ) + 1) + 42) * K21 (m + 1)) /
      (2 * ((m:ℝ) + 2) * (2 * ((m:ℝ) + 1) + 3) * (5 * ((m:ℝ) + 1) + 1)) := by
    rw [eq_div_iff hP]; linear_combination hK
  unfold F21
  rw [k2, k1, hK2]
  unfold midCoeff21 tailCoeff21 r21
  push_cast
  rw [add_sub_cancel_right]
  have h1 : (4 * ((m:ℝ) + 1) * (2 * (m:ℝ) + 3)) ≠ 0 := by positivity
  have h2 : (4 * ((m:ℝ) + 1 + 1) * (2 * ((m:ℝ) + 1) + 3)) ≠ 0 := by positivity
  have h3 : 0 < (m:ℝ) + 1 := by positivity
  field_simp
  ring

theorem F21_le (m : ℕ) : F21 m ≤ 15 * Real.sqrt 2 * 20 ^ m := by
  have hk : ∀ m : ℕ, kap21 m ≤ 15 * Real.sqrt 2 * 20 ^ m := by
    intro m
    induction m with
    | zero => rw [kap21_zero]; simp
    | succ k ih =>
      rw [kap21_succ]
      have hr :
          3 * (6 * (k:ℝ) + 7) * (6 * (k:ℝ) + 11) / (4 * ((k:ℝ) + 1) * (2 * (k:ℝ) + 3)) ≤ 20 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      have hp := kap21_pos k
      calc 3 * (6 * (k:ℝ) + 7) * (6 * (k:ℝ) + 11) / (4 * ((k:ℝ) + 1) * (2 * (k:ℝ) + 3)) * kap21 k
          ≤ 20 * (15 * Real.sqrt 2 * 20 ^ k) :=
            mul_le_mul hr ih hp.le (by norm_num)
        _ = 15 * Real.sqrt 2 * 20 ^ (k + 1) := by ring
  unfold F21
  calc kap21 m * K21 m ≤ kap21 m * 1 := mul_le_mul_of_nonneg_left (K21_le_one m) (kap21_pos m).le
    _ ≤ 15 * Real.sqrt 2 * 20 ^ m := by rw [mul_one]; exact hk m

/-! ### Transport to the challenge recurrence (Lemma 4) -/

/-- Equation (22), first half: `r_n A(n) = a_n`. -/
theorem r21_mul_midCoeff21 (n : ℕ) : r21 n * midCoeff21 n = a21 n := by
  rw [midCoeff21, mul_div_cancel₀ _ (r21_pos n).ne', a21]

/-- Equation (22), second half: `r_n r_{n−1} B(n) = b_n` (`n ≥ 1`). -/
theorem r21_mul_r21_mul_tailCoeff21 (n : ℕ) :
    r21 ((n + 1 : ℕ) : ℝ) * r21 n * tailCoeff21 ((n + 1 : ℕ) : ℝ) = b21 (n + 1) := by
  have hr : ((n + 1 : ℕ) : ℝ) - 1 = n := by push_cast; ring
  rw [tailCoeff21, hr, mul_div_cancel₀ _ (mul_ne_zero (r21_pos _).ne' (r21_pos n).ne'), b21]

/-- `σ m = s_{m−1}` of Equation (23): `s_{−1} = 77/24`, `s_n = r_n s_{n−1}`. -/
noncomputable def sig21 : ℕ → ℝ
  | 0 => 77 / 24
  | m + 1 => r21 m * sig21 m

theorem sig21_pos (m : ℕ) : 0 < sig21 m := by
  induction m with
  | zero => norm_num [sig21]
  | succ k ih => exact mul_pos (r21_pos k) ih

/-- `Z21 m = X_{m−1} = s_{m−1} F_{m+1}` of Equation (24). -/
noncomputable def Z21 (m : ℕ) : ℝ := sig21 m * F21 m

/-- **Lemma 4**: `X_n = s_n F_{n+2}` solves the challenge recurrence. -/
theorem Z21_mem_solutions : Z21 ∈ cf21.solutions := by
  rw [CFData.mem_solutions]
  intro n
  have hF := F21_rec n
  have hA := r21_mul_midCoeff21 (n + 1)
  have hB := r21_mul_r21_mul_tailCoeff21 n
  simp only [cf21_partialDen, cf21_partialNum]
  simp only [Z21, sig21]
  rw [hF, ← hA, ← hB]
  ring

/-! ### Minimality (Lemmas 5 and 6) by a direct dominance bound -/

theorem neg_midCoeff21_ge (x : ℝ) (hx : 0 ≤ x) : 100 ≤ -midCoeff21 x := by
  have hr := r21_pos_of_nonneg hx
  have hD : 0 < (6 * x + 7) * (6 * x + 11) := by positivity
  rw [midCoeff21, neg_div', le_div_iff₀ hr, r21, mul_div_assoc', div_le_iff₀ hD]
  nlinarith [pow_pos (by linarith : (0:ℝ) < x + 1) 5, sq_nonneg x, mul_nonneg hx (sq_nonneg x),
    pow_nonneg hx 4, pow_nonneg hx 5]

theorem b21_succ_nonneg (n : ℕ) : 0 ≤ b21 (n + 1) := by
  unfold b21; push_cast
  have : (0:ℝ) ≤ 5 * ((n:ℝ) + 1) - 4 := by have := (Nat.cast_nonneg n : (0:ℝ) ≤ n); linarith
  positivity

/-- The convergent denominators alternate in sign and grow at least like `σ · 100^k`. -/
theorem denom21_bound (k : ℕ) :
    sig21 (k + 1) * 100 ^ k ≤ (-1) ^ k * cf21.denom (k + 1) ∧
      sig21 (k + 2) * 100 ^ (k + 1) ≤ (-1) ^ (k + 1) * cf21.denom (k + 2) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · norm_num [sig21, r21]
    · rw [show (0 + 2 : ℕ) = 0 + 2 from rfl, CFData.denom_add_two]
      norm_num [sig21, r21, a21, b21]
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    have hrec : cf21.denom (k + 3) =
        a21 (k + 2) * cf21.denom (k + 2) + b21 (k + 2) * cf21.denom (k + 1) :=
      CFData.denom_add_two cf21 (k + 1)
    have hA := r21_mul_midCoeff21 (k + 2)
    have hneg := neg_midCoeff21_ge ((k + 2 : ℕ) : ℝ) (Nat.cast_nonneg _)
    have hr := r21_pos (k + 2)
    have hs0 := sig21_pos (k + 1)
    have hs := sig21_pos (k + 2)
    have hb := b21_succ_nonneg (k + 1)
    have hsig : sig21 (k + 3) = r21 ((k + 2 : ℕ) : ℝ) * sig21 (k + 2) := rfl
    have hQ1 : 0 ≤ (-1) ^ k * cf21.denom (k + 1) := le_trans (by positivity) h0
    have hpow : (-1 : ℝ) ^ (k + 1 + 1) = (-1) ^ k := by rw [pow_succ, pow_succ]; ring
    have hpow2 : (-1 : ℝ) ^ (k + 1) = -(-1) ^ k := by rw [pow_succ]; ring
    rw [show k + 1 + 2 = k + 3 by ring, hrec, hsig, hpow, show k + 1 + 1 = k + 2 by ring]
    rw [hpow2] at h1
    -- (-1)^k Q(k+3) = (-a)((-1)^{k+1} Q(k+2)) + b ((-1)^k Q(k+1))
    have key :
        (-1) ^ k * (a21 (k + 2) * cf21.denom (k + 2) + b21 (k + 2) * cf21.denom (k + 1))
        = (r21 ((k + 2 : ℕ) : ℝ) * (-midCoeff21 ((k + 2 : ℕ) : ℝ))) *
            (-(-1) ^ k * cf21.denom (k + 2))
          + b21 (k + 2) * ((-1) ^ k * cf21.denom (k + 1)) := by
      rw [← hA]; ring
    rw [key]
    have hbt : 0 ≤ b21 (k + 2) * ((-1) ^ k * cf21.denom (k + 1)) := mul_nonneg hb hQ1
    have hmain : r21 ((k + 2 : ℕ) : ℝ) * sig21 (k + 2) * 100 ^ (k + 2) ≤
        (r21 ((k + 2 : ℕ) : ℝ) * (-midCoeff21 ((k + 2 : ℕ) : ℝ))) *
          (-(-1) ^ k * cf21.denom (k + 2)) := by
      calc r21 ((k + 2 : ℕ) : ℝ) * sig21 (k + 2) * 100 ^ (k + 2)
          = (r21 ((k + 2 : ℕ) : ℝ) * 100) * (sig21 (k + 2) * 100 ^ (k + 1)) := by ring
        _ ≤ (r21 ((k + 2 : ℕ) : ℝ) * (-midCoeff21 ((k + 2 : ℕ) : ℝ))) *
            (-(-1) ^ k * cf21.denom (k + 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hneg hr.le) h1 (by positivity) (by nlinarith)
    linarith

theorem denom21_ne_zero (k : ℕ) : cf21.denom (k + 1) ≠ 0 := by
  intro h
  have h0 := (denom21_bound k).1
  rw [h, mul_zero] at h0
  have : 0 < sig21 (k + 1) * 100 ^ k := mul_pos (sig21_pos _) (by positivity)
  linarith

theorem norm_Z21_div_denom21_le (k : ℕ) :
    ‖Z21 (k + 1) / cf21.denom (k + 1)‖ ≤ 300 * Real.sqrt 2 * (1 / 5) ^ k := by
  have hb := (denom21_bound k).1
  have hs := sig21_pos (k + 1)
  have hF := F21_le (k + 1)
  have hF0 := F21_pos (k + 1)
  have hQ0 : 0 ≤ (-1) ^ k * cf21.denom (k + 1) := le_trans (by positivity) hb
  have hQ : |cf21.denom (k + 1)| = (-1) ^ k * cf21.denom (k + 1) := by
    rw [← abs_of_nonneg hQ0, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hQpos : 0 < (-1) ^ k * cf21.denom (k + 1) :=
    lt_of_lt_of_le (mul_pos hs (by positivity)) hb
  have hZ : 0 < Z21 (k + 1) := mul_pos hs hF0
  rw [Real.norm_eq_abs, abs_div, hQ, abs_of_pos hZ, div_le_iff₀ hQpos]
  have h20 : (20:ℝ) ^ (k + 1) = 20 * ((1 / 5) ^ k * 100 ^ k) := by
    rw [← mul_pow]; norm_num; ring
  calc Z21 (k + 1) = sig21 (k + 1) * F21 (k + 1) := rfl
    _ ≤ sig21 (k + 1) * (15 * Real.sqrt 2 * 20 ^ (k + 1)) := mul_le_mul_of_nonneg_left hF hs.le
    _ = 300 * Real.sqrt 2 * (1 / 5) ^ k * (sig21 (k + 1) * 100 ^ k) := by rw [h20]; ring
    _ ≤ 300 * Real.sqrt 2 * (1 / 5) ^ k * ((-1) ^ k * cf21.denom (k + 1)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)

/-- **Lemma 6**: `X_n` is a recessive (minimal) solution of the challenge recurrence, dominated
by the convergent denominators. -/
theorem Z21_isRecessive : cf21.IsRecessive Z21 := by
  have hne : ∀ᶠ n in atTop, cf21.denom n ≠ 0 := by
    rw [eventually_atTop]
    exact ⟨1, fun n hn => by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact denom21_ne_zero k⟩
  refine ⟨Z21_mem_solutions, cf21.denom, cf21.denom_mem_solutions, hne, ?_⟩
  rw [isLittleO_iff_tendsto' (hne.mono fun n hn h => absurd h hn),
    ← tendsto_add_atTop_iff_nat 1]
  refine squeeze_zero_norm (fun k => norm_Z21_div_denom21_le k) ?_
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 5)
    (by norm_num)).const_mul (300 * Real.sqrt 2)
  rw [mul_zero] at h
  exact h

/-- **Theorem 2 (the challenge limit).** The polynomial continued fraction of Problem 2.1,
`a_n = −220n³ − 484n² − 301n − 42`, `b_n = 4n²(2n+1)²(5n−4)(5n+6)`, converges to `6/(3 − π)`:
its convergents `P_n/Q_n` tend to `6/(3 − π)`. -/
theorem pcf21_tendsto :
    Tendsto (fun n => cf21.numer n / cf21.denom n) atTop (𝓝 (6 / (3 - Real.pi))) := by
  have hZ0 : Z21 0 ≠ 0 := (mul_pos (sig21_pos 0) (F21_pos 0)).ne'
  have h := CFData.tendsto_convergent Z21_isRecessive hZ0
  have hval : cf21.partialDen 0 - Z21 1 / Z21 0 = 6 / (3 - Real.pi) := by
    simp only [cf21_partialDen, Z21, sig21, F21_zero, F21_one, a21]
    have hpi : Real.pi - 3 ≠ 0 := (sub_pos.mpr Real.pi_gt_three).ne'
    have hpi' : 3 - Real.pi ≠ 0 := (sub_neg.mpr Real.pi_gt_three).ne
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    norm_num [r21]
    field_simp
    ring
  rw [hval] at h
  exact h

/-! ### The rescaled coefficients converge (the limits behind the characteristic equation)

With `u = 1/n`: `a(n)/n³`, `r(n)/n³`, `r(n−1)/n³` and `b(n)/n⁶` are continuous functions of `u`
with values `−220`, `40/27`, `40/27` and `400` at `u = 0`. Hence
`A(n) → −220 · 27/40 = −297/2` and `B(n) → 400 · (27/40)² = 729/4`, the coefficients of the
characteristic equation `4x² + 594x − 729 = 0` of `charPoly21_eq_zero_iff` (`Exact.lean`). -/

theorem tendsto_comp_inv_natCast {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun n : ℕ => g (n : ℝ)⁻¹) atTop (𝓝 (g 0)) :=
  (hg.tendsto 0).comp (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)

theorem tendsto_midCoeff21 : Tendsto (fun n : ℕ => midCoeff21 n) atTop (𝓝 (-297 / 2)) := by
  have ha := tendsto_comp_inv_natCast
    (g := fun u => -220 - 484 * u - 301 * u ^ 2 - 42 * u ^ 3) (by fun_prop)
  have hp := tendsto_comp_inv_natCast
    (g := fun u => 8 * (1 + u) ^ 2 * (2 + 3 * u) ^ 2 * (5 + u)) (by fun_prop)
  have hq := tendsto_comp_inv_natCast
    (g := fun u => 3 * (6 + 7 * u) * (6 + 11 * u)) (by fun_prop)
  have h : Tendsto (fun n : ℕ =>
      (-220 - 484 * (n : ℝ)⁻¹ - 301 * (n : ℝ)⁻¹ ^ 2 - 42 * (n : ℝ)⁻¹ ^ 3) /
      (8 * (1 + (n : ℝ)⁻¹) ^ 2 * (2 + 3 * (n : ℝ)⁻¹) ^ 2 * (5 + (n : ℝ)⁻¹) /
        (3 * (6 + 7 * (n : ℝ)⁻¹) * (6 + 11 * (n : ℝ)⁻¹)))) atTop (𝓝 (-297 / 2)) := by
    convert ha.div (hp.div hq (by norm_num)) (by norm_num) using 2
    norm_num
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [midCoeff21, r21]
  field_simp

theorem tendsto_tailCoeff21 : Tendsto (fun n : ℕ => tailCoeff21 n) atTop (𝓝 (729 / 4)) := by
  have hb := tendsto_comp_inv_natCast
    (g := fun u => 4 * (2 + u) ^ 2 * (5 - 4 * u) * (5 + 6 * u)) (by fun_prop)
  have hp := tendsto_comp_inv_natCast
    (g := fun u => 8 * (1 + u) ^ 2 * (2 + 3 * u) ^ 2 * (5 + u)) (by fun_prop)
  have hq := tendsto_comp_inv_natCast
    (g := fun u => 3 * (6 + 7 * u) * (6 + 11 * u)) (by fun_prop)
  have hp' := tendsto_comp_inv_natCast
    (g := fun u => 8 * (2 + u) ^ 2 * (5 - 4 * u)) (by fun_prop)
  have hq' := tendsto_comp_inv_natCast
    (g := fun u => 3 * (6 + u) * (6 + 5 * u)) (by fun_prop)
  have h : Tendsto (fun n : ℕ =>
      4 * (2 + (n : ℝ)⁻¹) ^ 2 * (5 - 4 * (n : ℝ)⁻¹) * (5 + 6 * (n : ℝ)⁻¹) /
        (8 * (1 + (n : ℝ)⁻¹) ^ 2 * (2 + 3 * (n : ℝ)⁻¹) ^ 2 * (5 + (n : ℝ)⁻¹) /
            (3 * (6 + 7 * (n : ℝ)⁻¹) * (6 + 11 * (n : ℝ)⁻¹)) *
          (8 * (2 + (n : ℝ)⁻¹) ^ 2 * (5 - 4 * (n : ℝ)⁻¹) /
            (3 * (6 + (n : ℝ)⁻¹) * (6 + 5 * (n : ℝ)⁻¹))))) atTop (𝓝 (729 / 4)) := by
    convert hb.div ((hp.div hq (by norm_num)).mul (hp'.div hq' (by norm_num))) (by norm_num)
      using 2
    norm_num
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : (n : ℝ) * 5 - 4 ≠ 0 := ne_of_gt (by linarith)
  have e1 : (5 : ℝ) * ((n : ℝ) - 1) + 1 ≠ 0 := ne_of_gt (by linarith)
  have e2 : (n : ℝ) - 1 + 1 ≠ 0 := ne_of_gt (by linarith)
  have e3 : (2 : ℝ) * ((n : ℝ) - 1) + 3 ≠ 0 := ne_of_gt (by linarith)
  have e4 : (6 : ℝ) * ((n : ℝ) - 1) + 7 ≠ 0 := ne_of_gt (by linarith)
  have e5 : (6 : ℝ) * ((n : ℝ) - 1) + 11 ≠ 0 := ne_of_gt (by linarith)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  rw [show (5 : ℝ) - 4 * (n : ℝ)⁻¹ = (5 * n - 4) / n by field_simp]
  simp only [tailCoeff21, r21]
  field_simp
  ring

end RamanujanChallenge
