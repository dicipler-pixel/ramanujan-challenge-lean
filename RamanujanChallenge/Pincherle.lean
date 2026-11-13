/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib

/-!
# Continued-fraction recurrences and Pincherle's theorem

A generalized continued fraction `d₀ + n₁/(d₁ + n₂/(d₂ + ⋯))` is recorded as a `CFData`: its
partial denominators `d` and partial numerators `n`. Its three-term recurrence is written in
transfer-matrix form: a sequence `y` satisfies it when, for every `k`,

  `!![0, 1; n (k+1), d (k+1)] *ᵥ ![y k, y (k+1)] = ![y (k+1), y (k+2)]`.

The solutions form a submodule `CFData.solutions` of `ℕ → ℝ`. The convergent numerators
`CFData.numer` and denominators `CFData.denom` are the orbits of the start vectors `![1, d₀]`
and `![0, 1]` under the transfer matrices, and `CFData.convergent k = numer k / denom k`.

A solution `y` is *recessive* (`CFData.IsRecessive`) when some solution `w`, eventually nonzero,
dominates it in the sense of little-o: `y =o[atTop] w`.

Main results.
* `CFData.tendsto_convergent`: **Pincherle's theorem** (convergence direction). If `y` is
  recessive and `y 0 ≠ 0`, the convergents tend to `d₀ − y 1 / y 0`.
* `CFData.isRecessive_of_ratio`, `CFData.tendsto_convergent_of_ratio`: recessiveness from ratio
  limits `y (k+1)/y k → ρ`, `w (k+1)/w k → σ` with `|ρ| < |σ|`.
* `CFData.pincherle_needs_eventually_ne_zero`: if the companion is not required to be
  eventually nonzero (so that `y k / w k → 0` may hold only because Lean's `x / 0 = 0`), the
  conclusion fails, even with every partial numerator nonzero. The witness is the period-two
  fraction `altCF`.

This file was written from the mathematics of three-term recurrences (the standard statement
of Pincherle's theorem, e.g. Gautschi, *SIAM Review* 9 (1967)); see `PROVENANCE.md`.
-/

open Filter Topology Asymptotics Matrix

namespace RamanujanChallenge

/-- A generalized continued fraction `d₀ + n₁/(d₁ + n₂/(d₂ + ⋯))`. -/
structure CFData where
  /-- The partial denominators `d k`. -/
  partialDen : ℕ → ℝ
  /-- The partial numerators `n k`. -/
  partialNum : ℕ → ℝ

/-- The transfer matrix taking `![y k, y (k+1)]` to `![y (k+1), y (k+2)]`. -/
def CFData.transfer (c : CFData) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; c.partialNum (k + 1), c.partialDen (k + 1)]

theorem CFData.transfer_mulVec (c : CFData) (k : ℕ) (u v : ℝ) :
    c.transfer k *ᵥ ![u, v] = ![v, c.partialNum (k + 1) * u + c.partialDen (k + 1) * v] := by
  ext i
  fin_cases i <;> simp [CFData.transfer, mulVec, dotProduct, Fin.sum_univ_two]

/-- `y` satisfies the recurrence of `c`, in transfer-matrix form. -/
def CFData.Satisfies (c : CFData) (y : ℕ → ℝ) : Prop :=
  ∀ k, c.transfer k *ᵥ ![y k, y (k + 1)] = ![y (k + 1), y (k + 2)]

/-- The transfer-matrix form unfolds to the scalar three-term recurrence. -/
theorem CFData.satisfies_iff (c : CFData) (y : ℕ → ℝ) : c.Satisfies y ↔
    ∀ k, y (k + 2) = c.partialDen (k + 1) * y (k + 1) + c.partialNum (k + 1) * y k := by
  refine forall_congr' fun k => ?_
  rw [c.transfer_mulVec]
  constructor
  · intro h
    have h1 := congrFun h 1
    simp only [cons_val_one, cons_val_zero] at h1
    linarith
  · intro h
    ext i
    fin_cases i
    · rfl
    · simp only [Fin.mk_one, cons_val_one, cons_val_zero]
      rw [h]
      ring

/-- The solutions of the recurrence, as a real vector space of sequences. -/
def CFData.solutions (c : CFData) : Submodule ℝ (ℕ → ℝ) where
  carrier := {y | c.Satisfies y}
  add_mem' := by
    intro y z hy hz
    change c.Satisfies _ at hy hz ⊢
    rw [c.satisfies_iff] at hy hz ⊢
    intro k
    simp only [Pi.add_apply]
    rw [hy k, hz k]
    ring
  zero_mem' := by
    change c.Satisfies _
    rw [c.satisfies_iff]
    intro k
    simp
  smul_mem' := by
    intro r y hy
    change c.Satisfies _ at hy ⊢
    rw [c.satisfies_iff] at hy ⊢
    intro k
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hy k]
    ring

theorem CFData.mem_solutions (c : CFData) (y : ℕ → ℝ) : y ∈ c.solutions ↔
    ∀ k, y (k + 2) = c.partialDen (k + 1) * y (k + 1) + c.partialNum (k + 1) * y k :=
  c.satisfies_iff y

/-- The state vectors `![y k, y (k+1)]` of the solution with initial state `v`. -/
def CFData.state (c : CFData) (v : Fin 2 → ℝ) : ℕ → Fin 2 → ℝ
  | 0 => v
  | k + 1 => c.transfer k *ᵥ c.state v k

/-- The solution with initial state `v`: the first coordinate of the state. -/
def CFData.orbit (c : CFData) (v : Fin 2 → ℝ) (k : ℕ) : ℝ := c.state v k 0

theorem CFData.state_eq (c : CFData) (v : Fin 2 → ℝ) (k : ℕ) :
    c.state v k = ![c.orbit v k, c.orbit v (k + 1)] := by
  have eta : ∀ w : Fin 2 → ℝ, w = ![w 0, w 1] := fun w => by
    ext i; fin_cases i <;> rfl
  ext i
  fin_cases i
  · rfl
  · change c.state v k 1 = (c.transfer k *ᵥ c.state v k) 0
    rw [eta (c.state v k), c.transfer_mulVec]
    rfl

theorem CFData.orbit_mem_solutions (c : CFData) (v : Fin 2 → ℝ) : c.orbit v ∈ c.solutions := by
  intro k
  rw [← c.state_eq, ← c.state_eq]
  rfl

/-- The convergent numerators: the orbit of `![1, d₀]`. -/
def CFData.numer (c : CFData) : ℕ → ℝ := c.orbit ![1, c.partialDen 0]

/-- The convergent denominators: the orbit of `![0, 1]`. -/
def CFData.denom (c : CFData) : ℕ → ℝ := c.orbit ![0, 1]

/-- The convergents `numer k / denom k`. -/
noncomputable def CFData.convergent (c : CFData) (k : ℕ) : ℝ := c.numer k / c.denom k

theorem CFData.numer_mem_solutions (c : CFData) : c.numer ∈ c.solutions := c.orbit_mem_solutions _

theorem CFData.denom_mem_solutions (c : CFData) : c.denom ∈ c.solutions := c.orbit_mem_solutions _

@[simp] theorem CFData.numer_zero (c : CFData) : c.numer 0 = 1 := rfl
@[simp] theorem CFData.numer_one (c : CFData) : c.numer 1 = c.partialDen 0 := by
  change (c.transfer 0 *ᵥ ![1, c.partialDen 0]) 0 = _
  rw [c.transfer_mulVec]; rfl
@[simp] theorem CFData.denom_zero (c : CFData) : c.denom 0 = 0 := rfl
@[simp] theorem CFData.denom_one (c : CFData) : c.denom 1 = 1 := by
  change (c.transfer 0 *ᵥ ![0, 1]) 0 = _
  rw [c.transfer_mulVec]; rfl

theorem CFData.numer_add_two (c : CFData) (k : ℕ) :
    c.numer (k + 2) = c.partialDen (k + 1) * c.numer (k + 1) + c.partialNum (k + 1) * c.numer k :=
  (c.mem_solutions _).1 c.numer_mem_solutions k

theorem CFData.denom_add_two (c : CFData) (k : ℕ) :
    c.denom (k + 2) = c.partialDen (k + 1) * c.denom (k + 1) + c.partialNum (k + 1) * c.denom k :=
  (c.mem_solutions _).1 c.denom_mem_solutions k

/-- A solution is determined by its first two values. -/
theorem CFData.ext_of_mem_solutions {c : CFData} {y z : ℕ → ℝ} (hy : y ∈ c.solutions)
    (hz : z ∈ c.solutions) (h0 : y 0 = z 0) (h1 : y 1 = z 1) : y = z := by
  rw [c.mem_solutions] at hy hz
  have key : ∀ k, y k = z k ∧ y (k + 1) = z (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih => exact ⟨ih.2, by rw [hy k, hz k, ih.1, ih.2]⟩
  funext k
  exact (key k).1

/-- Every solution is `y 0 • numer + (y 1 - d₀ * y 0) • denom`. -/
theorem CFData.eq_numer_denom_combo {c : CFData} {y : ℕ → ℝ} (hy : y ∈ c.solutions) :
    y = y 0 • c.numer + (y 1 - c.partialDen 0 * y 0) • c.denom := by
  refine CFData.ext_of_mem_solutions hy
    (add_mem (c.solutions.smul_mem _ c.numer_mem_solutions)
      (c.solutions.smul_mem _ c.denom_mem_solutions)) ?_ ?_
  · simp
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, CFData.numer_one, CFData.denom_one]
    ring

/-- A solution vanishing at `0` is a multiple of the denominators. -/
theorem CFData.eq_smul_denom {c : CFData} {y : ℕ → ℝ} (hy : y ∈ c.solutions) (h0 : y 0 = 0) :
    y = y 1 • c.denom := by
  have h := CFData.eq_numer_denom_combo hy
  rw [h0, zero_smul, zero_add, mul_zero, sub_zero] at h
  exact h

/-- If no partial numerator vanishes, a solution that is eventually zero is zero: the recurrence
can be run backwards. -/
theorem CFData.eq_zero_of_eventually_eq_zero {c : CFData} {y : ℕ → ℝ}
    (hn : ∀ k, c.partialNum (k + 1) ≠ 0) (hy : y ∈ c.solutions) (h : ∀ᶠ k in atTop, y k = 0) :
    y = 0 := by
  rw [c.mem_solutions] at hy
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  have down : ∀ j k, N ≤ j + k → y k = 0 := by
    intro j
    induction j with
    | zero => exact fun k hk => hN k (by simpa using hk)
    | succ j ih =>
      intro k hk
      have h2 : y (k + 2) = 0 := ih (k + 2) (by omega)
      have h1 : y (k + 1) = 0 := ih (k + 1) (by omega)
      have hk' := hy k
      rw [h2, h1, mul_zero, zero_add] at hk'
      exact (mul_eq_zero.1 hk'.symm).resolve_left (hn k)
  funext k
  exact down N k (by omega)

/-- `y` is a recessive (minimal) solution: some solution `w` that is eventually nonzero
dominates it, `y = o(w)`. -/
def CFData.IsRecessive (c : CFData) (y : ℕ → ℝ) : Prop :=
  y ∈ c.solutions ∧ ∃ w ∈ c.solutions, (∀ᶠ k in atTop, w k ≠ 0) ∧ y =o[atTop] w

/-- A recessive solution is not proportional to its dominating companion. -/
theorem CFData.IsRecessive.ne_smul {y w : ℕ → ℝ} (hw : ∀ᶠ k in atTop, w k ≠ 0)
    (hyw : y =o[atTop] w) (r : ℝ) : w ≠ r • y := by
  rintro rfl
  have hr : r ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hw.exists
    exact hk (by simp)
  have hself : y =o[atTop] y := (isLittleO_const_smul_right hr).1 hyw
  refine isLittleO_irrefl' ?_ hself
  refine (hw.mono fun k hk => ?_).frequently
  intro hyk
  exact hk (by simp [norm_eq_zero.1 hyk])

/-- **Pincherle's theorem** (convergence direction). If `y` is a recessive solution with
`y 0 ≠ 0`, the convergents tend to `d₀ − y 1 / y 0`. -/
theorem CFData.tendsto_convergent {c : CFData} {y : ℕ → ℝ} (hy : c.IsRecessive y)
    (hy0 : y 0 ≠ 0) : Tendsto c.convergent atTop (𝓝 (c.partialDen 0 - y 1 / y 0)) := by
  obtain ⟨hys, w, hws, hwne, hyw⟩ := hy
  -- `e = w − k • y` vanishes at `0`, so it is a multiple of the denominators.
  set k : ℝ := w 0 / y 0 with hk
  set e : ℕ → ℝ := w - k • y with he
  have hes : e ∈ c.solutions := sub_mem hws (c.solutions.smul_mem k hys)
  have he0 : e 0 = 0 := by
    simp only [he, hk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hed : e = e 1 • c.denom := CFData.eq_smul_denom hes he0
  -- `w = O(e)`, hence `y = o(e)`.
  have hwe : w =O[atTop] e := by
    have h := (hyw.const_smul_left k).right_isBigO_sub
    refine h.congr_right fun n => ?_
    simp [he]
  have hye : y =o[atTop] e := hyw.trans_isBigO hwe
  have he1 : e 1 ≠ 0 := by
    intro h1
    have hz : e = 0 := by rw [hed, h1, zero_smul]
    have hz' : ∀ᶠ n in atTop, e n = 0 → w n = 0 := hwe.eq_zero_imp
    obtain ⟨n, hn, hwn⟩ := (hwne.and hz').exists
    exact hn (hwn (by simp [hz]))
  have hyd : y =o[atTop] c.denom := by
    have h : y =o[atTop] fun n => e 1 • c.denom n := by
      refine hye.congr_right fun n => ?_
      rw [hed]
      simp
    exact (isLittleO_const_smul_right he1).1 h
  have hlim : Tendsto (fun n => y n / c.denom n) atTop (𝓝 0) := hyd.tendsto_div_nhds_zero
  have hdne : ∀ᶠ n in atTop, c.denom n ≠ 0 := by
    filter_upwards [hwne, hwe.eq_zero_imp] with n hn himp hd
    apply hn
    apply himp
    rw [hed]
    simp [hd]
  -- Write the convergent through `y / denom`.
  set β : ℝ := y 1 - c.partialDen 0 * y 0
  have hcombo : ∀ n, y n = y 0 * c.numer n + β * c.denom n := fun n => by
    have h := congrFun (CFData.eq_numer_denom_combo hys) n
    simpa using h
  have hT : Tendsto (fun n => (y n / c.denom n - β) / y 0) atTop (𝓝 ((0 - β) / y 0)) :=
    (hlim.sub_const β).div_const (y 0)
  have hval : (0 - β) / y 0 = c.partialDen 0 - y 1 / y 0 := by
    simp only [β]
    field_simp
    ring
  rw [hval] at hT
  refine hT.congr' ?_
  filter_upwards [hdne] with n hn
  simp only [CFData.convergent]
  rw [hcombo n]
  field_simp
  ring

/-- Recessiveness from ratio limits: if `y (k+1)/y k → ρ` and `w (k+1)/w k → σ` with
`|ρ| < |σ|`, both eventually nonzero, then `y` is recessive, dominated by `w`. -/
theorem CFData.isRecessive_of_ratio {c : CFData} {y w : ℕ → ℝ} {ρ σ : ℝ}
    (hy : y ∈ c.solutions) (hw : w ∈ c.solutions) (hyne : ∀ᶠ k in atTop, y k ≠ 0)
    (hwne : ∀ᶠ k in atTop, w k ≠ 0) (hρ : Tendsto (fun k => y (k + 1) / y k) atTop (𝓝 ρ))
    (hσ : Tendsto (fun k => w (k + 1) / w k) atTop (𝓝 σ)) (hlt : |ρ| < |σ|) :
    c.IsRecessive y := by
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    simp only [abs_zero] at hlt
    exact (abs_nonneg ρ).not_gt hlt
  refine ⟨hy, w, hw, hwne, ?_⟩
  rw [isLittleO_iff_tendsto' (hwne.mono fun k hk h => absurd h hk)]
  -- The quotient `q = y / w` has ratio tending to `ρ / σ`, of modulus below one.
  set q : ℕ → ℝ := fun k => y k / w k
  have hq : Tendsto (fun k => ‖q (k + 1)‖ / ‖q k‖) atTop (𝓝 (|ρ| / |σ|)) := by
    have h := (hρ.div hσ hσ0).norm
    rw [Real.norm_eq_abs, abs_div] at h
    refine h.congr fun k => ?_
    simp only [Pi.div_apply, q]
    rw [← norm_div, div_div_div_comm]
  have hqne : ∀ᶠ k in atTop, q k ≠ 0 := by
    filter_upwards [hyne, hwne] with k h1 h2
    exact div_ne_zero h1 h2
  have hl : |ρ| / |σ| < 1 := (div_lt_one (abs_pos.2 hσ0)).2 hlt
  exact (summable_of_ratio_test_tendsto_lt_one hl hqne hq).tendsto_atTop_zero

/-- Pincherle's theorem under ratio hypotheses. -/
theorem CFData.tendsto_convergent_of_ratio {c : CFData} {y w : ℕ → ℝ} {ρ σ : ℝ}
    (hy : y ∈ c.solutions) (hw : w ∈ c.solutions) (hyne : ∀ᶠ k in atTop, y k ≠ 0)
    (hwne : ∀ᶠ k in atTop, w k ≠ 0) (hρ : Tendsto (fun k => y (k + 1) / y k) atTop (𝓝 ρ))
    (hσ : Tendsto (fun k => w (k + 1) / w k) atTop (𝓝 σ)) (hlt : |ρ| < |σ|) (hy0 : y 0 ≠ 0) :
    Tendsto c.convergent atTop (𝓝 (c.partialDen 0 - y 1 / y 0)) :=
  CFData.tendsto_convergent (CFData.isRecessive_of_ratio hy hw hyne hwne hρ hσ hlt) hy0

/-! ### The nonvanishing clause cannot be dropped

Take the period-two fraction with `d = 17/2, 0, 17/2, 0, …` and `n = −4, 1/4, −4, 1/4, …`.
The sequence `y k = 2⁻ᵏ` solves its recurrence, while the denominators are `0` at every even
index and `(−4)ʲ` at index `2j+1`. Then `y k / denom k → 0` (it is `0` at even `k` by Lean's
convention `x / 0 = 0`), `denom` is not a multiple of `y`, every partial numerator is nonzero,
and yet the convergents are `0` at even `k` and tend to `8` along odd `k`. -/

/-- The period-two continued fraction of the counterexample. -/
noncomputable def altCF : CFData where
  partialDen k := if Even k then 17 / 2 else 0
  partialNum k := if Even k then -4 else 1 / 4

/-- The solution `2⁻ᵏ` of `altCF`. -/
noncomputable def altSeq (k : ℕ) : ℝ := 2⁻¹ ^ k

theorem altCF_partialDen_even (j : ℕ) : altCF.partialDen (2 * j) = 17 / 2 := by
  simp [altCF]

theorem altCF_partialDen_odd (j : ℕ) : altCF.partialDen (2 * j + 1) = 0 := by
  simp [altCF]

theorem altCF_partialNum_even (j : ℕ) : altCF.partialNum (2 * j) = -4 := by
  simp [altCF]

theorem altCF_partialNum_odd (j : ℕ) : altCF.partialNum (2 * j + 1) = 1 / 4 := by
  simp [altCF]

theorem altCF_partialNum_ne_zero (k : ℕ) : altCF.partialNum k ≠ 0 := by
  simp only [altCF]
  split_ifs <;> norm_num

theorem altSeq_mem_solutions : altSeq ∈ altCF.solutions := by
  rw [CFData.mem_solutions]
  intro k
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [altCF_partialDen_odd, altCF_partialNum_odd]
    simp only [altSeq]
    ring
  · rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, altCF_partialDen_even, altCF_partialNum_even]
    simp only [altSeq]
    ring

theorem altCF_denom (j : ℕ) :
    altCF.denom (2 * j) = 0 ∧ altCF.denom (2 * j + 1) = (-4) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hev : altCF.denom (2 * (j + 1)) = 0 := by
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, CFData.denom_add_two, altCF_partialDen_odd,
        altCF_partialNum_odd, ih.1]
      ring
    refine ⟨hev, ?_⟩
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring, CFData.denom_add_two,
      show 2 * j + 1 + 1 = 2 * (j + 1) by ring, altCF_partialDen_even, altCF_partialNum_even,
      ih.2, hev]
    ring

theorem altCF_numer (k : ℕ) : altCF.numer k = altSeq k + 8 * altCF.denom k := by
  have h := congrFun (CFData.eq_numer_denom_combo altSeq_mem_solutions) k
  have hd0 : altCF.partialDen 0 = 17 / 2 := by simpa using altCF_partialDen_even 0
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, altSeq, hd0] at h
  simp only [altSeq]
  norm_num at h
  linear_combination -h

theorem altCF_not_tendsto :
    ¬ Tendsto altCF.convergent atTop (𝓝 (altCF.partialDen 0 - altSeq 1 / altSeq 0)) := by
  intro hT
  have hev : Tendsto (fun j : ℕ => altCF.convergent (2 * j)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun j => by simp [CFData.convergent, (altCF_denom j).1]
  have hodd : Tendsto (fun j : ℕ => altCF.convergent (2 * j + 1)) atTop (𝓝 8) := by
    have h16 : Tendsto (fun j : ℕ => (2⁻¹ : ℝ) * (-16)⁻¹ ^ j) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        (show |(-16 : ℝ)⁻¹| < 1 by norm_num [abs_inv])).const_mul (2⁻¹ : ℝ)
      simpa using this
    have h := h16.const_add 8
    rw [add_zero] at h
    refine h.congr fun j => ?_
    have h4 : ((-4 : ℝ)) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
    have e : (2⁻¹ : ℝ) ^ (2 * j + 1) / (-4) ^ j = 2⁻¹ * (-16)⁻¹ ^ j := by
      rw [pow_succ, pow_mul, div_eq_mul_inv, ← inv_pow, mul_right_comm, ← mul_pow]
      norm_num
      ring
    simp only [CFData.convergent, altCF_numer, (altCF_denom j).2, altSeq]
    rw [add_div, mul_div_assoc, div_self h4, e]
    ring
  have h2 : Tendsto (fun j : ℕ => 2 * j) atTop atTop :=
    tendsto_atTop_mono (fun j => (by omega : j ≤ 2 * j)) tendsto_id
  have h2' : Tendsto (fun j : ℕ => 2 * j + 1) atTop atTop :=
    tendsto_atTop_mono (fun j => (by omega : j ≤ 2 * j + 1)) tendsto_id
  have e1 := tendsto_nhds_unique (hT.comp h2) hev
  have e2 := tendsto_nhds_unique (hT.comp h2') hodd
  rw [e1] at e2
  norm_num at e2

/-- Without the requirement that the companion be eventually nonzero, Pincherle's conclusion
fails: there is a continued fraction with every partial numerator nonzero, a solution `y` with
`y 0 ≠ 0`, and a solution `w` not proportional to `y` with `y k / w k → 0`, whose convergents
do not tend to `d₀ − y 1 / y 0`. -/
theorem pincherle_needs_eventually_ne_zero :
    ∃ (c : CFData) (y w : ℕ → ℝ), y ∈ c.solutions ∧ w ∈ c.solutions ∧ (∀ r : ℝ, w ≠ r • y) ∧
      Tendsto (fun k => y k / w k) atTop (𝓝 0) ∧ y 0 ≠ 0 ∧ (∀ k, c.partialNum k ≠ 0) ∧
      ¬ Tendsto c.convergent atTop (𝓝 (c.partialDen 0 - y 1 / y 0)) := by
  refine ⟨altCF, altSeq, altCF.denom, altSeq_mem_solutions, altCF.denom_mem_solutions,
    fun r hr => ?_, ?_, by simp [altSeq], altCF_partialNum_ne_zero, altCF_not_tendsto⟩
  · have h0 := congrFun hr 0
    have h1 := congrFun hr 1
    simp only [Pi.smul_apply, smul_eq_mul, altSeq, CFData.denom_zero, CFData.denom_one,
      pow_zero, pow_one, mul_one] at h0 h1
    rw [← h0] at h1
    norm_num at h1
  · refine squeeze_zero_norm (fun k => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num))
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · simp [(altCF_denom j).1]
    · simp only [(altCF_denom j).2, altSeq, norm_div, norm_pow, norm_neg, norm_inv,
        Real.norm_ofNat]
      exact div_le_self (by positivity) (one_le_pow₀ (by norm_num))

end RamanujanChallenge
