import RamanujanChallenge.Problem21

/-!
Euler's integral for the Problem 2.1 hypergeometric sequence: `F21` is Mathlib's `₂F₁`.

`Problem21.lean` defines `F_n` (`F21 m`, `n = m + 1`) through Euler's integral in the paper's
substitution `t = 2u²/(1+u²)`, and proves the challenge limit from it. This file proves that
`F_n` is the official `F_n = ₂F₁(n+½, n+½; 3n+½; 1/2)` of Eq. 13, as a value of
`ordinaryHypergeometric` (`F21_eq_hypergeometric`). The proof is the classical one behind the
paper's Lemma 1 (Euler's integral), in four steps:

* the real Beta integral `∫₀¹ x^{p−1}(1−x)^{q−1} = Γ(p)Γ(q)/Γ(p+q)` (`beta_integral_real`),
  from Mathlib's `Complex.Gamma_mul_Gamma_eq_betaIntegral`;
* the binomial series `(1 − y)^{−a} = Σ (a)_k y^k/k!` for `|y| < 1`
  (`hasSum_one_div_one_sub_rpow`), from Mathlib's
  `Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero`;
* termwise integration by dominated convergence (`hasSum_integral_gEk`). Each term is a Beta
  integral (`integral_gEk`), and `Γ(x+k) = (x)_k Γ(x)` (`Gamma_add_nat_real`) turns the sum into
  the `₂F₁` series (`hypergeometric_eq_euler`);
* the change of variables `t = 2u²/(1+u²)` back to `Problem21.lean`'s integral (`E21_eq`).

Corollaries in `₂F₁` form: Lemma 3 for the official sequence (`hypergeometric21_rec`) and the
two anchors `₂F₁(3/2,3/2;7/2;1/2) = (15√2/2)(π−3)`, `₂F₁(5/2,5/2;13/2;1/2) = (1155√2/8)(22−7π)`
(`hypergeometric21_one`, `hypergeometric21_two`).
-/

open Filter Topology

namespace RamanujanChallenge

/-- `x^{j+½} = x^j √x` for `x ≥ 0`. -/
theorem rpow_nat_add_half {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    x ^ ((j : ℝ) + 1 / 2) = x ^ j * Real.sqrt x := by
  rw [Real.rpow_add' hx (by positivity), Real.rpow_natCast, Real.sqrt_eq_rpow]

/-- The real Beta integral. -/
theorem beta_integral_real {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ x in (0:ℝ)..1, x ^ (p - 1) * (1 - x) ^ (q - 1) =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (p : ℂ)) (t := (q : ℂ))
    (by simpa using hp) (by simpa using hq)
  have hG : Real.Gamma (p + q) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hI : Complex.betaIntegral p q =
      ((∫ x in (0:ℝ)..1, x ^ (p - 1) * (1 - x) ^ (q - 1) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hx
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1, Complex.ofReal_cpow (by linarith [hx.2])]
    push_cast; ring_nf
  rw [hI, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal] at hB
  have := hB
  norm_cast at this
  rw [eq_div_iff hG, mul_comm]
  exact this.symm

/-- `Γ(x + k) = (x)_k Γ(x)` for `x > 0`. -/
theorem Gamma_add_nat_real {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Real.Gamma (x + k) = (ascPochhammer ℝ k).eval x * Real.Gamma x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one (by positivity), ih, ascPochhammer_succ_eval]
    ring

/-- The binomial series `(1 − y)^{−a} = Σ (a)_k y^k / k!` for `|y| < 1`. -/
theorem hasSum_one_div_one_sub_rpow (a : ℝ) {y : ℝ} (hy : |y| < 1) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k).eval a * y ^ k)
      (1 / (1 - y) ^ a) := by
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum
    (y := y) (by
      have h1 : ‖y‖₊ < 1 := by rw [← NNReal.coe_lt_coe]; simpa using hy
      simpa [enorm_eq_nnnorm] using h1)
  simp only [zero_add] at h
  convert h using 1
  funext k
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, Ring.choose_eq_smul,
    Polynomial.descPochhammer_smeval_eq_ascPochhammer, Polynomial.ascPochhammer_smeval_eq_eval]
  rw [show a + k - 1 - k + 1 = a by ring]
  simp [smul_eq_mul, mul_comm]

/-- The Euler integrand of `F_{m+1}` in the paper's variable `t` (Eq. 28):
`t^{n−½}(1−t)^{2n−1}(1−t/2)^{−n−½}` with `n = m+1`. -/
noncomputable def gE21 (m : ℕ) (t : ℝ) : ℝ :=
  t ^ m * Real.sqrt t * (1 - t) ^ (2 * m + 1) * (1 / (1 - t / 2) ^ ((m : ℝ) + 3 / 2))

/-- The Euler integral of Eq. 28 (without its Gamma prefactor). -/
noncomputable def E21 (m : ℕ) : ℝ := ∫ t in (0:ℝ)..1, gE21 m t

/-- The `k`-th term of the binomial expansion of the Euler integrand. -/
noncomputable def gEk (m k : ℕ) (t : ℝ) : ℝ :=
  ((k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k).eval ((m : ℝ) + 3 / 2) * (t / 2) ^ k *
    (t ^ m * Real.sqrt t * (1 - t) ^ (2 * m + 1))

theorem continuous_gEk (m k : ℕ) : Continuous (gEk m k) := by
  unfold gEk; fun_prop

theorem gEk_nonneg (m k : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ gEk m k t := by
  have hA : 0 < (ascPochhammer ℝ k).eval ((m : ℝ) + 3 / 2) := ascPochhammer_pos k _ (by positivity)
  have : 0 ≤ 1 - t := by linarith
  unfold gEk; positivity

theorem hasSum_gEk (m : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    HasSum (fun k => gEk m k t) (gE21 m t) := by
  have hy : |t / 2| < 1 := by rw [abs_lt]; constructor <;> linarith
  have h := (hasSum_one_div_one_sub_rpow ((m : ℝ) + 3 / 2) hy).mul_left
    (t ^ m * Real.sqrt t * (1 - t) ^ (2 * m + 1))
  convert h using 1
  · funext k; unfold gEk; ring
  · unfold gE21; ring

theorem continuousOn_gE21 (m : ℕ) : ContinuousOn (gE21 m) (Set.uIcc 0 1) := by
  unfold gE21
  refine ContinuousOn.mul (by fun_prop) (ContinuousOn.div continuousOn_const ?_ ?_)
  · refine ContinuousOn.rpow_const (by fun_prop) (fun x _ => Or.inr (by positivity))
  · intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    have : 0 < 1 - x / 2 := by linarith [hx.2]
    positivity

/-- Termwise integration of the binomial expansion (dominated convergence). -/
theorem hasSum_integral_gEk (m : ℕ) :
    HasSum (fun k => ∫ t in (0:ℝ)..1, gEk m k t) (E21 m) := by
  have hmem : ∀ t ∈ Set.uIoc (0:ℝ) 1, 0 ≤ t ∧ t ≤ 1 := by
    intro t ht; rw [Set.uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le, ht.2⟩
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun k t => gEk m k t)
    (fun k => (continuous_gEk m k).aestronglyMeasurable)
    (fun k => Filter.Eventually.of_forall fun t ht => ?_) ?_ ?_ ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg (gEk_nonneg m k (hmem t ht).1 (hmem t ht).2)]
  · exact Filter.Eventually.of_forall fun t ht =>
      (hasSum_gEk m (hmem t ht).1 (hmem t ht).2).summable
  · exact ((continuousOn_gE21 m).intervalIntegrable).congr fun t ht =>
      ((hasSum_gEk m (hmem t ht).1 (hmem t ht).2).tsum_eq).symm
  · exact Filter.Eventually.of_forall fun t ht => hasSum_gEk m (hmem t ht).1 (hmem t ht).2

/-- Each term is a Beta integral. -/
theorem integral_gEk (m k : ℕ) :
    ∫ t in (0:ℝ)..1, gEk m k t =
      ((k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k).eval ((m : ℝ) + 3 / 2) * (1 / 2) ^ k *
        (Real.Gamma ((m : ℝ) + 3 / 2 + k) * Real.Gamma (2 * (m : ℝ) + 2) /
          Real.Gamma (3 * (m : ℝ) + 7 / 2 + k)) := by
  have hB := beta_integral_real (p := ((m + k : ℕ) : ℝ) + 1 / 2 + 1) (q := 2 * (m : ℝ) + 2)
    (by positivity) (by positivity)
  have hint : ∫ t in (0:ℝ)..1, gEk m k t =
      ((k.factorial : ℝ))⁻¹ * (ascPochhammer ℝ k).eval ((m : ℝ) + 3 / 2) *
        (1 / 2) ^ k * ∫ x in (0:ℝ)..1,
          x ^ (((m + k : ℕ) : ℝ) + 1 / 2 + 1 - 1) * (1 - x) ^ (2 * (m : ℝ) + 2 - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hx
    have h1 : ((m + k : ℕ) : ℝ) + 1 / 2 + 1 - 1 = ((m + k : ℕ) : ℝ) + 1 / 2 := by ring
    have h2 : 2 * (m : ℝ) + 2 - 1 = ((2 * m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [h1, h2, rpow_nat_add_half hx.1, Real.rpow_natCast]
    unfold gEk
    rw [div_pow, pow_add]
    simp only [one_div, inv_pow]
    ring
  rw [hint, hB]
  congr 2
  · push_cast; ring_nf
  · push_cast; ring_nf

/-- **Euler's integral for `F_{m+1}`** (the paper's Lemma 1 at `a = b = n+½`, `c = 3n+½`,
`z = 1/2`): Mathlib's `₂F₁(n+½, n+½; 3n+½; 1/2)` equals
`Γ(3n+½)/(Γ(n+½)Γ(2n)) ∫₀¹ t^{n−½}(1−t)^{2n−1}(1−t/2)^{−n−½} dt`. -/
theorem hypergeometric_eq_euler (m : ℕ) :
    ordinaryHypergeometric (((m : ℝ) + 1) + 1 / 2) (((m : ℝ) + 1) + 1 / 2)
        (3 * ((m : ℝ) + 1) + 1 / 2) (1 / 2 : ℝ) =
      Real.Gamma (3 * ((m : ℝ) + 1) + 1 / 2) /
          (Real.Gamma (((m : ℝ) + 1) + 1 / 2) * Real.Gamma (2 * ((m : ℝ) + 1)))
        * E21 m := by
  set a : ℝ := ((m : ℝ) + 1) + 1 / 2 with ha
  set c : ℝ := 3 * ((m : ℝ) + 1) + 1 / 2 with hc
  have ha0 : 0 < a := by rw [ha]; positivity
  have hc0 : 0 < c := by rw [hc]; positivity
  have hGa := (Real.Gamma_pos_of_pos ha0).ne'
  have hGc := (Real.Gamma_pos_of_pos hc0).ne'
  have hG2 := (Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < 2 * ((m : ℝ) + 1))).ne'
  have hS := (hasSum_integral_gEk m).mul_left
    (Real.Gamma c / (Real.Gamma a * Real.Gamma (2 * ((m : ℝ) + 1))))
  rw [ordinaryHypergeometric_eq_tsum]
  refine (HasSum.tsum_eq ?_)
  convert hS using 1
  funext k
  rw [integral_gEk, smul_eq_mul]
  have e1 : (m : ℝ) + 3 / 2 = a := by rw [ha]; ring
  have e2 : 3 * (m : ℝ) + 7 / 2 = c := by rw [hc]; ring
  have e3 : 2 * (m : ℝ) + 2 = 2 * ((m : ℝ) + 1) := by ring
  rw [e1, e2, e3, Gamma_add_nat_real ha0, Gamma_add_nat_real hc0]
  have hAc : (ascPochhammer ℝ k).eval c ≠ 0 := (ascPochhammer_pos k c hc0).ne'
  field_simp

/-- The paper's substitution `t = 2u²/(1+u²)` (`t = 2 sin²θ`, `u = tan θ`). -/
noncomputable def phi21 (u : ℝ) : ℝ := 2 * u ^ 2 / (1 + u ^ 2)

theorem hasDerivAt_phi21 (u : ℝ) : HasDerivAt phi21 (4 * u / (1 + u ^ 2) ^ 2) u := by
  have hd := one_add_sq_ne u
  have h := (((hasDerivAt_pow 2 u).const_mul 2).fun_div ((hasDerivAt_const u (1:ℝ)).fun_add
    (hasDerivAt_pow 2 u)) hd)
  convert h using 1
  · rfl
  norm_num
  field_simp
  ring

theorem gE21_phi21 (m : ℕ) {u : ℝ} (h0 : 0 ≤ u) :
    gE21 m (phi21 u) * (4 * u / (1 + u ^ 2) ^ 2) = 2 ^ (m + 2) * Real.sqrt 2 * w21 m u := by
  have hd : 0 < 1 + u ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.mpr hd
  have hss : Real.sqrt (1 + u ^ 2) ^ 2 = 1 + u ^ 2 := Real.sq_sqrt hd.le
  have h2 : 0 < Real.sqrt 2 := by positivity
  have e1 : 1 - phi21 u / 2 = 1 / (1 + u ^ 2) := by unfold phi21; field_simp; ring
  have e2 : 1 - phi21 u = (1 - u ^ 2) / (1 + u ^ 2) := by unfold phi21; field_simp; ring
  have e3 : Real.sqrt (phi21 u) = Real.sqrt 2 * u / Real.sqrt (1 + u ^ 2) := by
    unfold phi21
    rw [Real.sqrt_div' _ hd.le, Real.sqrt_mul (by norm_num), Real.sqrt_sq h0]
  have e4 : (1 / (1 + u ^ 2)) ^ ((m : ℝ) + 3 / 2) =
      (1 / (1 + u ^ 2)) ^ (m + 1) * (1 / Real.sqrt (1 + u ^ 2)) := by
    rw [show (m : ℝ) + 3 / 2 = ((m + 1 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      rpow_nat_add_half (by positivity), Real.sqrt_div' _ hd.le, Real.sqrt_one]
  unfold gE21 w21 G21
  rw [e1, e2, e3, e4]
  unfold phi21
  simp only [div_pow, mul_pow, one_pow, ← pow_mul]
  have hd' := hd.ne'
  field_simp
  ring

/-- The change of variables `t = 2u²/(1+u²)` (Eqs. 36–37): the Euler integral is
`2^{n+3/2}` times the rational integral `K21`. -/
theorem E21_eq (m : ℕ) : E21 m = 2 ^ (m + 2) * Real.sqrt 2 * K21 m := by
  have himg : phi21 '' Set.uIcc 0 1 ⊆ Set.uIcc 0 1 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Set.uIcc_of_le zero_le_one] at hu ⊢
    have hd : 0 < 1 + u ^ 2 := by positivity
    unfold phi21
    constructor
    · positivity
    · rw [div_le_one hd]; nlinarith [hu.1, hu.2]
  have hcv := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := 1) (f := phi21)
    (f' := fun u => 4 * u / (1 + u ^ 2) ^ 2) (g := gE21 m) (fun x _ => hasDerivAt_phi21 x)
    (Continuous.continuousOn (Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)))
    ((continuousOn_gE21 m).mono himg)
  have h0 : phi21 0 = 0 := by simp [phi21]
  have h1 : phi21 1 = 1 := by norm_num [phi21]
  rw [h0, h1] at hcv
  unfold E21
  rw [← hcv, K21, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun u hu => ?_)
  rw [Set.uIcc_of_le zero_le_one] at hu
  exact gE21_phi21 m hu.1

/-- **The hypergeometric identification.** The sequence `F21` of `Problem21.lean` is the official
`F_n = ₂F₁(n+½, n+½; 3n+½; 1/2)` of Eq. 13 (`n = m + 1`), as a value of Mathlib's
`ordinaryHypergeometric`. -/
theorem F21_eq_hypergeometric (m : ℕ) :
    F21 m = ordinaryHypergeometric (((m : ℝ) + 1) + 1 / 2) (((m : ℝ) + 1) + 1 / 2)
      (3 * ((m : ℝ) + 1) + 1 / 2) (1 / 2 : ℝ) := by
  rw [hypergeometric_eq_euler, E21_eq, F21, kap21]
  ring

/-- The official sequence `F_n = ₂F₁(n+½, n+½; 3n+½; 1/2)` (Eq. 13) satisfies Lemma 3:
`F_{n+2} = A(n) F_{n+1} + B(n) F_n` for every `n ≥ 1` (`n = m + 1`). -/
theorem hypergeometric21_rec (m : ℕ) :
    ordinaryHypergeometric (((m + 2 : ℕ) : ℝ) + 1 + 1 / 2) (((m + 2 : ℕ) : ℝ) + 1 + 1 / 2)
        (3 * (((m + 2 : ℕ) : ℝ) + 1) + 1 / 2) (1 / 2 : ℝ) =
      A21 ((m + 1 : ℕ) : ℝ) * ordinaryHypergeometric (((m + 1 : ℕ) : ℝ) + 1 + 1 / 2)
          (((m + 1 : ℕ) : ℝ) + 1 + 1 / 2) (3 * (((m + 1 : ℕ) : ℝ) + 1) + 1 / 2) (1 / 2 : ℝ) +
        B21 ((m + 1 : ℕ) : ℝ) * ordinaryHypergeometric (((m : ℕ) : ℝ) + 1 + 1 / 2)
          (((m : ℕ) : ℝ) + 1 + 1 / 2) (3 * (((m : ℕ) : ℝ) + 1) + 1 / 2) (1 / 2 : ℝ) := by
  rw [← F21_eq_hypergeometric, ← F21_eq_hypergeometric, ← F21_eq_hypergeometric]
  exact F21_rec m

/-- Lemma 7, first anchor, as a value of Mathlib's `₂F₁`:
`₂F₁(3/2, 3/2; 7/2; 1/2) = (15√2/2)(π − 3)`. -/
theorem hypergeometric21_one :
    ordinaryHypergeometric (3 / 2 : ℝ) (3 / 2) (7 / 2) (1 / 2 : ℝ) =
      15 * Real.sqrt 2 / 2 * (Real.pi - 3) := by
  have h := F21_eq_hypergeometric 0
  norm_num at h
  rw [← h, F21_zero]

/-- Lemma 7, second anchor, as a value of Mathlib's `₂F₁`:
`₂F₁(5/2, 5/2; 13/2; 1/2) = (1155√2/8)(22 − 7π)`. -/
theorem hypergeometric21_two :
    ordinaryHypergeometric (5 / 2 : ℝ) (5 / 2) (13 / 2) (1 / 2 : ℝ) =
      1155 * Real.sqrt 2 / 8 * (22 - 7 * Real.pi) := by
  have h := F21_eq_hypergeometric 1
  norm_num at h
  rw [← h, F21_one]

end RamanujanChallenge
