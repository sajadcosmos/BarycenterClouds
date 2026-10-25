/-
# Barycentric Clouds: Centers of Mass of Random Complex Numbers under Analytic Maps

Complete Lean 4 / Mathlib formalisation of the paper (single-file version).

-/
import Mathlib

-- ============================================================================
-- Source part: Bary1.lean
-- ============================================================================

open Finset BigOperators

namespace Barycenter

/-! ## Part 1. The combinatorial moment sums -/

/-- `Qsum μ m n = ∑_{k₁+⋯+kₘ=n} (n choose k)² ∏ μ_{k_j}` (multinomial coefficients),
defined through the recursion obtained by splitting off the last step. -/
noncomputable def Qsum (μ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, n => if n = 0 then 1 else 0
  | m + 1, n => ∑ i ∈ range (n + 1), ((n.choose i : ℕ) : ℝ) ^ 2 * μ i * Qsum μ m (n - i)

/-- The normalised moment `q_{m,n} = m^{-2n} Qsum μ m n` (this is `E|S_m|^{2n}`). -/
noncomputable def qmom (μ : ℕ → ℝ) (m n : ℕ) : ℝ := Qsum μ m n / (m : ℝ) ^ (2 * n)

/-- Pearson random-walk constant `κ_{m,n}`: the case of unit radial moments. -/
noncomputable def kappa (m n : ℕ) : ℝ := qmom (fun _ => 1) m n

lemma Qsum_zero_left (μ : ℕ → ℝ) (n : ℕ) : Qsum μ 0 n = if n = 0 then 1 else 0 := rfl

lemma Qsum_succ (μ : ℕ → ℝ) (m n : ℕ) :
    Qsum μ (m + 1) n = ∑ i ∈ range (n + 1), ((n.choose i : ℕ) : ℝ) ^ 2 * μ i * Qsum μ m (n - i) :=
  rfl

lemma Qsum_zero_right (μ : ℕ → ℝ) (h0 : μ 0 = 1) (m : ℕ) : Qsum μ m 0 = 1 := by
  induction m with
  | zero => simp [Qsum]
  | succ m ih => simp [Qsum_succ, ih, h0]

lemma Qsum_nonneg (μ : ℕ → ℝ) (hμ : ∀ i, 0 ≤ μ i) (m n : ℕ) : 0 ≤ Qsum μ m n := by
  induction m generalizing n with
  | zero => simp only [Qsum_zero_left]; split_ifs <;> norm_num
  | succ m ih =>
    rw [Qsum_succ]
    exact sum_nonneg fun i _ => mul_nonneg (mul_nonneg (sq_nonneg _) (hμ i)) (ih _)

lemma Qsum_one (μ : ℕ → ℝ) (h0 : μ 0 = 1) (m : ℕ) : Qsum μ m 1 = m * μ 1 := by
  induction m with
  | zero => simp [Qsum]
  | succ m ih =>
    rw [Qsum_succ]
    simp [sum_range_succ, ih, Qsum_zero_right μ h0, h0]
    ring

lemma Qsum_two (μ : ℕ → ℝ) (h0 : μ 0 = 1) (m : ℕ) :
    Qsum μ m 2 = m * μ 2 + 2 * m * (m - 1) * μ 1 ^ 2 := by
  induction m with
  | zero => simp [Qsum]
  | succ m ih =>
    rw [Qsum_succ]
    simp [sum_range_succ, ih, Qsum_zero_right μ h0, Qsum_one μ h0, h0]
    ring

lemma Qsum_three (μ : ℕ → ℝ) (h0 : μ 0 = 1) (m : ℕ) :
    Qsum μ m 3 = m * μ 3 + 9 * m * (m - 1) * μ 1 * μ 2
      + 6 * m * (m - 1) * (m - 2) * μ 1 ^ 3 := by
  induction m with
  | zero => simp [Qsum]
  | succ m ih =>
    rw [Qsum_succ]
    simp [sum_range_succ, ih, Qsum_zero_right μ h0, Qsum_one μ h0, Qsum_two μ h0, h0,
      Nat.choose]
    ring

/-- `q_{m,1} = μ₁/m`. -/
theorem qmom_one (μ : ℕ → ℝ) (h0 : μ 0 = 1) {m : ℕ} (hm : 1 ≤ m) : qmom μ m 1 = μ 1 / m := by
  have : (m : ℝ) ≠ 0 := by positivity
  rw [qmom, Qsum_one μ h0]; field_simp; ring

/-- `q_{m,2} = (μ₂ + 2(m-1)μ₁²)/m³` (equation (3.3) of the paper). -/
theorem qmom_two (μ : ℕ → ℝ) (h0 : μ 0 = 1) {m : ℕ} (hm : 1 ≤ m) :
    qmom μ m 2 = (μ 2 + 2 * (m - 1) * μ 1 ^ 2) / m ^ 3 := by
  have : (m : ℝ) ≠ 0 := by positivity
  rw [qmom, Qsum_two μ h0]; field_simp; ring

/-- `q_{m,3} = (μ₃ + 9(m-1)μ₁μ₂ + 6(m-1)(m-2)μ₁³)/m⁵` (equation (3.4) of the paper). -/
theorem qmom_three (μ : ℕ → ℝ) (h0 : μ 0 = 1) {m : ℕ} (hm : 1 ≤ m) :
    qmom μ m 3 = (μ 3 + 9 * (m - 1) * μ 1 * μ 2 + 6 * (m - 1) * (m - 2) * μ 1 ^ 3) / m ^ 5 := by
  have : (m : ℝ) ≠ 0 := by positivity
  rw [qmom, Qsum_three μ h0]; field_simp; ring

/-! ### Small cases of `κ` (Example 3.5) -/

theorem kappa_one {m : ℕ} (hm : 1 ≤ m) : kappa m 1 = 1 / m := by
  simpa using qmom_one (fun _ => (1 : ℝ)) rfl hm

theorem kappa_two {m : ℕ} (hm : 1 ≤ m) : kappa m 2 = (2 * m - 1) / m ^ 3 := by
  rw [kappa, qmom_two _ rfl hm]; ring

theorem kappa_three {m : ℕ} (hm : 1 ≤ m) : kappa m 3 = (6 * m ^ 2 - 9 * m + 4) / m ^ 5 := by
  rw [kappa, qmom_three _ rfl hm]; ring

lemma Qsum_one_left (μ : ℕ → ℝ) (n : ℕ) : Qsum μ 1 n = μ n := by
  rw [Qsum_succ, sum_eq_single n]
  · simp [Qsum_zero_left]
  · intro i hi hin
    have : n - i ≠ 0 := by have := mem_range.1 hi; omega
    simp [Qsum_zero_left, this]
  · simp

lemma Qsum_two_left_unit (n : ℕ) : Qsum (fun _ => 1) 2 n = ((2 * n).choose n : ℝ) := by
  rw [Qsum_succ]
  simp only [Qsum_one_left, mul_one]
  exact_mod_cast Nat.sum_range_choose_sq n

theorem kappa_two_left (n : ℕ) : kappa 2 n = ((2 * n).choose n : ℝ) / 4 ^ n := by
  rw [kappa, qmom, Qsum_two_left_unit]
  norm_num [pow_mul]

lemma Qsum_three_left_unit (n : ℕ) :
    Qsum (fun _ => 1) 3 n = ∑ k ∈ range (n + 1), ((n.choose k : ℝ)) ^ 2 * ((2 * k).choose k : ℝ) := by
  rw [Qsum_succ]
  simp only [Qsum_two_left_unit, mul_one]
  rw [← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hi : i < n + 1 := mem_range.1 hi
  have e1 : n + 1 - 1 - i = n - i := by omega
  have e2 : n - (n - i) = i := by omega
  rw [e1, e2, Nat.choose_symm (by omega : i ≤ n)]

theorem kappa_three_left (n : ℕ) :
    kappa 3 n = (∑ k ∈ range (n + 1), ((n.choose k : ℝ)) ^ 2 * ((2 * k).choose k : ℝ)) / 9 ^ n := by
  rw [kappa, qmom, Qsum_three_left_unit]
  norm_num [pow_mul]

theorem Qsum_eq_multinomial_sum {ι : Type*} [DecidableEq ι] (μ : ℕ → ℝ) (s : Finset ι) (n : ℕ) :
    Qsum μ s.card n = ∑ k ∈ s.piAntidiag n,
      ((Nat.multinomial s k : ℕ) : ℝ) ^ 2 * ∏ i ∈ s, μ (k i) := by
  induction s using Finset.cons_induction generalizing n with
  | empty =>
    by_cases hn : n = 0
    · subst hn; simp [Qsum_zero_left]
    · simp [Qsum_zero_left, hn]
  | cons i s hi ih =>
    rw [card_cons, Qsum_succ, piAntidiag_cons, sum_disjiUnion,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine sum_congr rfl fun a ha => ?_
    rw [ih, mul_sum, sum_map]
    refine sum_congr rfl fun g hg => ?_
    have hgi : g i = 0 := by
      by_contra h
      exact hi ((mem_piAntidiag.1 hg).2 i h)
    have hgs : ∑ j ∈ s, g j = n - a := (mem_piAntidiag.1 hg).1
    have ha' : a ≤ n := by have := mem_range.1 ha; omega
    simp only [addRightEmbedding_apply]
    rw [Nat.multinomial_cons, prod_cons]
    set F : ι → ℕ := g + fun t => if t = i then a else 0 with hFdef
    have h1 : F i = a := by simp [hFdef, hgi]
    have h2 : ∀ j ∈ s, F j = g j := by
      intro j hj
      have : j ≠ i := fun h => hi (h ▸ hj)
      simp [hFdef, this]
    rw [h1, sum_congr rfl h2, hgs, Nat.multinomial_congr h2, prod_congr rfl (fun j hj => show μ (F j) = μ (g j) by rw [h2 j hj]),
      Nat.add_sub_cancel' ha']
    push_cast
    ring

/-- The multinomial expression (1.6) of `κ_{m,n}`: `κ_{m,n} = m^{-2n} ∑_{|k|=n} (n choose k)²`. -/
theorem kappa_eq_multinomial (m n : ℕ) :
    kappa m n = (∑ k ∈ (univ : Finset (Fin m)).piAntidiag n,
      ((Nat.multinomial univ k : ℕ) : ℝ) ^ 2) / (m : ℝ) ^ (2 * n) := by
  rw [kappa, qmom]
  have := Qsum_eq_multinomial_sum (fun _ => (1 : ℝ)) (univ : Finset (Fin m)) n
  simp only [card_univ, Fintype.card_fin, prod_const_one, mul_one] at this
  rw [this]

/-- The multinomial expression (3.2) of `q_{m,n}`. -/
theorem qmom_eq_multinomial (μ : ℕ → ℝ) (m n : ℕ) :
    qmom μ m n = (∑ k ∈ (univ : Finset (Fin m)).piAntidiag n,
      ((Nat.multinomial univ k : ℕ) : ℝ) ^ 2 * ∏ j, μ (k j)) / (m : ℝ) ^ (2 * n) := by
  rw [qmom]
  have := Qsum_eq_multinomial_sum μ (univ : Finset (Fin m)) n
  simp only [card_univ, Fintype.card_fin] at this
  rw [this]

lemma Qsum_succ_ge (μ : ℕ → ℝ) (hμ : ∀ i, 0 ≤ μ i) (h0 : μ 0 = 1) (m n : ℕ) :
    μ n ≤ Qsum μ (m + 1) n := by
  rw [Qsum_succ]
  have := single_le_sum (f := fun i => ((n.choose i : ℕ) : ℝ) ^ 2 * μ i * Qsum μ m (n - i))
    (fun i _ => mul_nonneg (mul_nonneg (sq_nonneg _) (hμ i)) (Qsum_nonneg μ hμ m _))
    (self_mem_range_succ n)
  simpa [Qsum_zero_right μ h0] using this

lemma Qsum_unit_pos {m : ℕ} (hm : 1 ≤ m) (n : ℕ) : 0 < Qsum (fun _ => 1) m n := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact lt_of_lt_of_le one_pos (Qsum_succ_ge _ (fun _ => zero_le_one) rfl m' n)

lemma kappa_pos {m : ℕ} (hm : 1 ≤ m) (n : ℕ) : 0 < kappa m n := by
  rw [kappa, qmom]; have := Qsum_unit_pos hm n; positivity

lemma qmom_nonneg (μ : ℕ → ℝ) (hμ : ∀ i, 0 ≤ μ i) (m n : ℕ) : 0 ≤ qmom μ m n := by
  rw [qmom]; have := Qsum_nonneg μ hμ m n; positivity

/-- `∑_{|k|=n} (n choose k)² ≤ n! m^n`. -/
lemma Qsum_unit_le (m n : ℕ) : Qsum (fun _ => 1) m n ≤ (n.factorial : ℝ) * (m : ℝ) ^ n := by
  induction m generalizing n with
  | zero => cases n <;> simp [Qsum_zero_left]
  | succ m ih =>
    rw [Qsum_succ]
    calc ∑ i ∈ range (n + 1), ((n.choose i : ℕ) : ℝ) ^ 2 * 1 * Qsum (fun _ => 1) m (n - i)
        ≤ ∑ i ∈ range (n + 1), ((n.choose i : ℕ) : ℝ) ^ 2 * 1 *
            (((n - i).factorial : ℝ) * (m : ℝ) ^ (n - i)) := by
          gcongr with i hi; exact ih _
      _ ≤ ∑ i ∈ range (n + 1), (n.factorial : ℝ) * ((n.choose i : ℕ) * (m : ℝ) ^ (n - i)) := by
          refine sum_le_sum fun i hi => ?_
          have hi : i ≤ n := by have := mem_range.1 hi; omega
          have key : (n.choose i : ℝ) * ((n - i).factorial : ℝ) ≤ n.factorial := by
            have h := Nat.choose_mul_factorial_mul_factorial hi
            have h' : (n.choose i : ℝ) * ((n - i).factorial : ℝ) * (i.factorial : ℝ)
                = n.factorial := by
              have : n.choose i * (n - i).factorial * i.factorial = n.factorial := by
                rw [mul_right_comm]; exact h
              exact_mod_cast this
            have hf : (1 : ℝ) ≤ i.factorial := by
              exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero i)
            nlinarith [show (0 : ℝ) ≤ (n.choose i : ℝ) * ((n - i).factorial : ℝ) by positivity]
          have hm : (0 : ℝ) ≤ (n.choose i : ℝ) * (m : ℝ) ^ (n - i) := by positivity
          calc ((n.choose i : ℕ) : ℝ) ^ 2 * 1 * (((n - i).factorial : ℝ) * (m : ℝ) ^ (n - i))
              = ((n.choose i : ℝ) * ((n - i).factorial : ℝ)) *
                  ((n.choose i : ℝ) * (m : ℝ) ^ (n - i)) := by ring
            _ ≤ (n.factorial : ℝ) * ((n.choose i : ℝ) * (m : ℝ) ^ (n - i)) := by gcongr
      _ = (n.factorial : ℝ) * (1 + (m : ℝ)) ^ n := by
          rw [← mul_sum, add_pow]
          congr 1
          refine sum_congr rfl fun i hi => ?_
          rw [one_pow]; ring
      _ = (n.factorial : ℝ) * ((m + 1 : ℕ) : ℝ) ^ n := by push_cast; ring

/-- `κ_{m,n} ≤ n!/m^n` (part of Lemma 3.6). -/
theorem kappa_le_factorial_div {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    kappa m n ≤ (n.factorial : ℝ) / (m : ℝ) ^ n := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [kappa, qmom, div_le_div_iff₀ (by positivity) (by positivity)]
  calc Qsum (fun _ => 1) m n * (m : ℝ) ^ n ≤ ((n.factorial : ℝ) * (m : ℝ) ^ n) * (m : ℝ) ^ n := by
        gcongr; exact Qsum_unit_le m n
    _ = (n.factorial : ℝ) * (m : ℝ) ^ (2 * n) := by ring

/-- Comparison with unit steps, combinatorial form: if `μ_i ≤ M^i` for `i ≤ n`, then
`Qsum μ m k ≤ M^k Qsum 1 m k` for `k ≤ n`. -/
lemma Qsum_le_pow_mul (μ : ℕ → ℝ) (hμ : ∀ i, 0 ≤ μ i) {M : ℝ} (hM : 0 ≤ M) {n : ℕ}
    (hμM : ∀ i ≤ n, μ i ≤ M ^ i) (m : ℕ) :
    ∀ k ≤ n, Qsum μ m k ≤ M ^ k * Qsum (fun _ => 1) m k := by
  induction m with
  | zero =>
    intro k _
    by_cases hk : k = 0 <;> simp [Qsum_zero_left, hk]
  | succ m ih =>
    intro k hk
    rw [Qsum_succ, Qsum_succ, mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hi : i ≤ k := by have := mem_range.1 hi; omega
    have h1 := hμM i (by omega)
    have h2 := ih (k - i) (by omega)
    have hpow : M ^ k = M ^ i * M ^ (k - i) := by rw [← pow_add]; congr 1; omega
    rw [hpow]
    have := Qsum_nonneg μ hμ m (k - i)
    calc ((k.choose i : ℕ) : ℝ) ^ 2 * μ i * Qsum μ m (k - i)
        ≤ ((k.choose i : ℕ) : ℝ) ^ 2 * M ^ i * (M ^ (k - i) * Qsum (fun _ => 1) m (k - i)) := by
          gcongr
      _ = M ^ i * M ^ (k - i) * (((k.choose i : ℕ) : ℝ) ^ 2 * 1 * Qsum (fun _ => 1) m (k - i)) := by
          ring

/-- Equality analysis for Lemma 3.6: if `m ≥ 2`, `n ≥ 2`, `μ_i ≤ M^i` for `i ≤ n` and
`Qsum μ m n = M^n Qsum 1 m n`, then `μ₁ = M`. -/
lemma Qsum_eq_pow_mul_imp (μ : ℕ → ℝ) (hμ : ∀ i, 0 ≤ μ i) {M : ℝ} (hM : 0 ≤ M) {n : ℕ}
    (hn : 2 ≤ n) (hμM : ∀ i ≤ n, μ i ≤ M ^ i) {m : ℕ} (hm : 2 ≤ m)
    (heq : Qsum μ m n = M ^ n * Qsum (fun _ => 1) m n) : μ 1 = M := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hm' : 1 ≤ m' := by omega
  by_contra hne
  have hlt : μ 1 < M := lt_of_le_of_ne (by simpa using hμM 1 (by omega)) hne
  have hMpos : 0 < M := lt_of_le_of_lt (hμ 1) hlt
  apply absurd heq (ne_of_lt _)
  rw [Qsum_succ, Qsum_succ, mul_sum]
  apply sum_lt_sum
  · intro i hi
    have hi : i ≤ n := by have := mem_range.1 hi; omega
    have h1 := hμM i hi
    have h2 := Qsum_le_pow_mul μ hμ hM hμM m' (n - i) (by omega)
    have hpow : M ^ n = M ^ i * M ^ (n - i) := by rw [← pow_add]; congr 1; omega
    rw [hpow]
    have := Qsum_nonneg μ hμ m' (n - i)
    calc ((n.choose i : ℕ) : ℝ) ^ 2 * μ i * Qsum μ m' (n - i)
        ≤ ((n.choose i : ℕ) : ℝ) ^ 2 * M ^ i * (M ^ (n - i) * Qsum (fun _ => 1) m' (n - i)) := by
          gcongr
      _ = M ^ i * M ^ (n - i) * (((n.choose i : ℕ) : ℝ) ^ 2 * 1 * Qsum (fun _ => 1) m' (n - i)) := by
          ring
  · refine ⟨1, by simp; omega, ?_⟩
    have h2 := Qsum_le_pow_mul μ hμ hM hμM m' (n - 1) (by omega)
    have hpos := Qsum_unit_pos hm' (n - 1)
    have hpow : M ^ n = M * M ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    rw [hpow]
    have hc : (0 : ℝ) < ((n.choose 1 : ℕ) : ℝ) ^ 2 := by
      have : 0 < n.choose 1 := Nat.choose_pos (by omega)
      positivity
    have hQ := Qsum_nonneg μ hμ m' (n - 1)
    have hμ1 := hμ 1
    calc ((n.choose 1 : ℕ) : ℝ) ^ 2 * μ 1 * Qsum μ m' (n - 1)
        ≤ ((n.choose 1 : ℕ) : ℝ) ^ 2 * μ 1 * (M ^ (n - 1) * Qsum (fun _ => 1) m' (n - 1)) := by
          gcongr
      _ < ((n.choose 1 : ℕ) : ℝ) ^ 2 * M * (M ^ (n - 1) * Qsum (fun _ => 1) m' (n - 1)) := by
          gcongr
      _ = M * M ^ (n - 1) * (((n.choose 1 : ℕ) : ℝ) ^ 2 * 1 * Qsum (fun _ => 1) m' (n - 1)) := by
          ring

/-- Complex Gaussian radial moments `μ_i = i! v^i` give `Qsum = n! m^n v^n`, i.e.
`q_{m,n} = n! (v/m)^n` (Example 5.4). -/
theorem Qsum_gaussian (v : ℝ) (m n : ℕ) :
    Qsum (fun i => (i.factorial : ℝ) * v ^ i) m n = (n.factorial : ℝ) * (m : ℝ) ^ n * v ^ n := by
  induction m generalizing n with
  | zero => cases n <;> simp [Qsum_zero_left]
  | succ m ih =>
    rw [Qsum_succ]
    simp_rw [ih]
    have : ∀ i ∈ range (n + 1), ((n.choose i : ℕ) : ℝ) ^ 2 * ((i.factorial : ℝ) * v ^ i) *
        (((n - i).factorial : ℝ) * (m : ℝ) ^ (n - i) * v ^ (n - i))
        = (n.factorial : ℝ) * v ^ n * ((m : ℝ) ^ (n - i) * (n.choose i : ℝ)) := by
      intro i hi
      have hi : i ≤ n := by have := mem_range.1 hi; omega
      have h := Nat.choose_mul_factorial_mul_factorial hi
      have h' : (n.choose i : ℝ) * (i.factorial : ℝ) * ((n - i).factorial : ℝ) = n.factorial := by
        exact_mod_cast h
      have hv : v ^ n = v ^ i * v ^ (n - i) := by rw [← pow_add]; congr 1; omega
      rw [hv, ← h']; ring
    rw [sum_congr rfl this, ← mul_sum]
    have h2 : ∑ i ∈ range (n + 1), (m : ℝ) ^ (n - i) * (n.choose i : ℝ) = (1 + (m : ℝ)) ^ n := by
      rw [add_pow]; refine sum_congr rfl fun i _ => ?_; rw [one_pow, one_mul]
    rw [h2]; push_cast; ring

theorem qmom_gaussian (v : ℝ) {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    qmom (fun i => (i.factorial : ℝ) * v ^ i) m n = (n.factorial : ℝ) * (v / m) ^ n := by
  have : (m : ℝ) ≠ 0 := by positivity
  rw [qmom, Qsum_gaussian, div_pow, pow_mul]; field_simp; ring

end Barycenter

-- ============================================================================
-- Source part: Bary2.lean
-- ============================================================================

open Finset BigOperators Filter Topology

namespace Barycenter

/-! ## Part 2. Polynomial structure of `Qsum` in `m` and the leading asymptotics (4.? / 6.?) -/

/-- Coefficients of `Qsum μ m n` in the binomial basis `(m choose j)`. -/
noncomputable def dcoef (μ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, n => if n = 0 then 1 else 0
  | j + 1, n => ∑ i ∈ range n, ((n.choose (i + 1) : ℕ) : ℝ) ^ 2 * μ (i + 1) * dcoef μ j (n - (i + 1))

lemma dcoef_succ (μ : ℕ → ℝ) (j n : ℕ) :
    dcoef μ (j + 1) n = ∑ i ∈ range n,
      ((n.choose (i + 1) : ℕ) : ℝ) ^ 2 * μ (i + 1) * dcoef μ j (n - (i + 1)) := rfl

lemma dcoef_eq_zero_of_lt (μ : ℕ → ℝ) : ∀ j n, n < j → dcoef μ j n = 0
  | 0, n, h => absurd h (Nat.not_lt_zero _)
  | j + 1, n, h => by
    rw [dcoef_succ]
    refine sum_eq_zero fun i hi => ?_
    rw [dcoef_eq_zero_of_lt μ j (n - (i + 1)) (by have := mem_range.1 hi; omega), mul_zero]

lemma dcoef_diag (μ : ℕ → ℝ) (n : ℕ) :
    dcoef μ n n = ((n.factorial : ℕ) : ℝ) ^ 2 * μ 1 ^ n := by
  induction n with
  | zero => simp [dcoef]
  | succ n ih =>
    rw [dcoef_succ, sum_eq_single 0]
    · simp [ih, Nat.factorial_succ]; ring
    · intro i hi hi0
      rw [dcoef_eq_zero_of_lt μ n _ (by have := mem_range.1 hi; omega), mul_zero]
    · intro h; simp at h

lemma dcoef_zero_right (μ : ℕ → ℝ) (j : ℕ) : dcoef μ (j + 1) 0 = 0 := by
  simp [dcoef_succ]

/-- `Qsum μ m n = ∑_{j ≤ N} (m choose j) d_{j,n}` for every `N ≥ n`. -/
lemma Qsum_eq_sum_choose (μ : ℕ → ℝ) (h0 : μ 0 = 1) (m : ℕ) :
    ∀ n N, n ≤ N → Qsum μ m n = ∑ j ∈ range (N + 1), ((m.choose j : ℕ) : ℝ) * dcoef μ j n := by
  induction m with
  | zero =>
    intro n N _
    rw [sum_range_succ', sum_eq_zero (fun j _ => by simp)]
    simp [Qsum_zero_left, dcoef]
  | succ m ih =>
    intro n N hnN
    -- right-hand side manipulation
    have hR : ∑ j ∈ range (N + 1), (((m + 1).choose j : ℕ) : ℝ) * dcoef μ j n
        = (∑ j ∈ range (N + 1), ((m.choose j : ℕ) : ℝ) * dcoef μ j n)
          + ∑ j ∈ range N, ((m.choose j : ℕ) : ℝ) * dcoef μ (j + 1) n := by
      rw [sum_range_succ', sum_range_succ' (fun j => ((m.choose j : ℕ) : ℝ) * dcoef μ j n)]
      simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, sum_add_distrib, Nat.choose_zero_right]
      ring
    rw [hR, ← ih n N hnN, Qsum_succ, sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, one_pow, h0, one_mul, Nat.sub_zero]
    rw [add_comm]
    congr 1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [dcoef_zero_right]
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    simp_rw [dcoef_succ, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i hi => ?_
    rw [ih (n - (i + 1)) N' (by omega), mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring

/-- Leading asymptotics (6.4): `m^n q_{m,n} → n! μ₁^n` as `m → ∞`, i.e.
`q_{m,n} = n! μ₁^n / m^n + o(m^{-n})`. -/
theorem tendsto_pow_mul_qmom (μ : ℕ → ℝ) (h0 : μ 0 = 1) (n : ℕ) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ n * qmom μ m n) atTop
      (𝓝 ((n.factorial : ℝ) * μ 1 ^ n)) := by
  -- rewrite as a finite sum
  have hrepr : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ n * qmom μ m n
      = ∑ j ∈ range (n + 1), (((m.choose j : ℕ) : ℝ) / (m : ℝ) ^ n) * dcoef μ j n := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (m : ℝ) ≠ 0 := by positivity
    rw [qmom, Qsum_eq_sum_choose μ h0 m n n le_rfl, sum_div, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [pow_mul]; field_simp; ring
  rw [tendsto_congr' hrepr]
  have hlim : ∀ j ∈ range (n + 1), Tendsto (fun m : ℕ => (((m.choose j : ℕ) : ℝ) / (m : ℝ) ^ n))
      atTop (𝓝 (if j = n then 1 / (n.factorial : ℝ) else 0)) := by
    intro j hj
    have hj : j ≤ n := by have := mem_range.1 hj; omega
    split_ifs with hjn
    · subst hjn
      -- choose m j / m^j → 1/j!
      have hdesc : ∀ m : ℕ, (((m.choose j : ℕ) : ℝ) / (m : ℝ) ^ j)
          = ((m.descFactorial j : ℕ) : ℝ) / (m : ℝ) ^ j / (j.factorial : ℝ) := by
        intro m
        rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast
        have : (j.factorial : ℝ) ≠ 0 := by positivity
        field_simp
      simp_rw [hdesc]
      apply Tendsto.div_const
      -- descFactorial m j / m^j → 1
      have hlow : ∀ᶠ m : ℕ in atTop, (1 - (j : ℝ) / m) ^ j ≤ ((m.descFactorial j : ℕ) : ℝ) / (m : ℝ) ^ j := by
        filter_upwards [eventually_ge_atTop (j + 1)] with m hm
        have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
        have h1 := Nat.pow_sub_le_descFactorial m j
        have h2 : ((m - j : ℕ) : ℝ) ^ j ≤ ((m.descFactorial j : ℕ) : ℝ) := by
          have : (m - j) ^ j ≤ m.descFactorial j :=
            le_trans (Nat.pow_le_pow_left (by omega) j) h1
          exact_mod_cast this
        rw [le_div_iff₀ (by positivity)]
        calc (1 - (j : ℝ) / m) ^ j * (m : ℝ) ^ j = ((m : ℝ) - j) ^ j := by
              rw [← mul_pow]; congr 1; field_simp
          _ = ((m - j : ℕ) : ℝ) ^ j := by rw [Nat.cast_sub (by omega)]
          _ ≤ _ := h2
      have hup : ∀ᶠ m : ℕ in atTop, ((m.descFactorial j : ℕ) : ℝ) / (m : ℝ) ^ j ≤ 1 := by
        filter_upwards [eventually_ge_atTop 1] with m hm
        have hm' : (0 : ℝ) < m := by exact_mod_cast hm
        rw [div_le_one (by positivity)]
        exact_mod_cast Nat.descFactorial_le_pow m j
      have hl : Tendsto (fun m : ℕ => (1 - (j : ℝ) / m) ^ j) atTop (𝓝 1) := by
        have : Tendsto (fun m : ℕ => (j : ℝ) / m) atTop (𝓝 0) :=
          tendsto_const_div_atTop_nhds_zero_nat (j : ℝ)
        simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub this).pow j)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds hlow hup
    · have hjlt : j < n := lt_of_le_of_ne hj hjn
      -- 0 ≤ choose m j / m^n ≤ 1/m
      have hup : ∀ᶠ m : ℕ in atTop, (((m.choose j : ℕ) : ℝ) / (m : ℝ) ^ n) ≤ 1 / (m : ℝ) := by
        filter_upwards [eventually_ge_atTop 1] with m hm
        have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
        have hc : ((m.choose j : ℕ) : ℝ) ≤ (m : ℝ) ^ j := by
          exact_mod_cast Nat.choose_le_pow m j
        rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        calc ((m.choose j : ℕ) : ℝ) * m ≤ (m : ℝ) ^ j * m := by gcongr
          _ = (m : ℝ) ^ (j + 1) := by ring
          _ ≤ (m : ℝ) ^ n := pow_le_pow_right₀ hm' (by omega)
      have hlow : ∀ᶠ m : ℕ in atTop, (0 : ℝ) ≤ (((m.choose j : ℕ) : ℝ) / (m : ℝ) ^ n) :=
        Eventually.of_forall fun m => by positivity
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)) hlow hup
  have := tendsto_finset_sum (range (n + 1)) fun j hj => (hlim j hj).mul_const (dcoef μ j n)
  convert this using 1
  rw [sum_eq_single n]
  · rw [if_pos rfl, dcoef_diag]
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · intro j _ hjn; rw [if_neg hjn, zero_mul]
  · intro h; simp at h

/-- `m^n κ_{m,n} → n!` as `m → ∞` (Example 3.5: `κ_{m,n} ∼ n!/m^n`). -/
theorem tendsto_pow_mul_kappa (n : ℕ) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ n * kappa m n) atTop (𝓝 (n.factorial : ℝ)) := by
  simpa using tendsto_pow_mul_qmom (fun _ => (1 : ℝ)) rfl n

end Barycenter

-- ============================================================================
-- Source part: Bary3.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

namespace Barycenter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## Part 3. Rotationally invariant laws and the moment calculus -/

/-- A complex random variable is rotationally invariant if `e^{iθ} X` has the law of `X`
for every real `θ`. -/
def RotInv (X : Ω → ℂ) (P : Measure Ω) : Prop :=
  ∀ θ : ℝ, IdentDistrib (fun ω => Complex.exp (θ * Complex.I) * X ω) X P P

/-- Radial moments `μ_n = E|X|^{2n}`. -/
noncomputable def radMom (X : Ω → ℂ) (P : Measure Ω) (n : ℕ) : ℝ := ∫ ω, ‖X ω‖ ^ (2 * n) ∂P

/-- A complex random variable has finite moments of all orders. -/
def AllMoments (X : Ω → ℂ) (P : Measure Ω) : Prop := ∀ p : ℕ, MemLp X p P

/-- Mixed moment `E[W^p \bar W^q]`. -/
noncomputable def cmom (W : Ω → ℂ) (P : Measure Ω) (p q : ℕ) : ℂ :=
  ∫ ω, W ω ^ p * conj (W ω) ^ q ∂P

lemma norm_pow_mul_conj_pow (z : ℂ) (p q : ℕ) : ‖z ^ p * conj z ^ q‖ = ‖z‖ ^ (p + q) := by
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_conj, pow_add]

variable [IsProbabilityMeasure P]

lemma AllMoments.integrable_norm_pow {W : Ω → ℂ} (h : AllMoments W P) (p : ℕ) :
    Integrable (fun ω => ‖W ω‖ ^ p) P := (h p).integrable_norm_pow'

omit [IsProbabilityMeasure P] in
lemma AllMoments.aestronglyMeasurable {W : Ω → ℂ} (h : AllMoments W P) :
    AEStronglyMeasurable W P := (h 1).1

lemma AllMoments.integrable_pow_mul_conj_pow {W : Ω → ℂ} (h : AllMoments W P) (p q : ℕ) :
    Integrable (fun ω => W ω ^ p * conj (W ω) ^ q) P := by
  refine (h.integrable_norm_pow (p + q)).mono' ?_ (Eventually.of_forall fun ω => ?_)
  · have hW := h.aestronglyMeasurable
    exact (hW.pow p).mul ((Complex.continuous_conj.comp_aestronglyMeasurable hW).pow q)
  · rw [norm_pow_mul_conj_pow]

lemma AllMoments.integrable_pow {W : Ω → ℂ} (h : AllMoments W P) (p : ℕ) :
    Integrable (fun ω => W ω ^ p) P := by
  simpa using h.integrable_pow_mul_conj_pow p 0

omit [IsProbabilityMeasure P] in
lemma AllMoments.add {U V : Ω → ℂ} (hU : AllMoments U P) (hV : AllMoments V P) :
    AllMoments (fun ω => U ω + V ω) P := fun p => (hU p).add (hV p)

omit [IsProbabilityMeasure P] in
lemma AllMoments.const_mul {U : Ω → ℂ} (hU : AllMoments U P) (c : ℂ) :
    AllMoments (fun ω => c * U ω) P := fun p => (hU p).const_mul c

omit [IsProbabilityMeasure P] in
lemma AllMoments.finset_sum {ι : Type*} {X : ι → Ω → ℂ} (s : Finset ι)
    (h : ∀ j ∈ s, AllMoments (X j) P) : AllMoments (fun ω => ∑ j ∈ s, X j ω) P :=
  fun p => memLp_finset_sum' s (fun j hj => h j hj p) |>.congr_norm
    (by
      have := memLp_finset_sum' s (fun j hj => h j hj p)
      exact (memLp_finset_sum s (fun j hj => h j hj p)).1)
    (Eventually.of_forall fun ω => by simp [Finset.sum_apply])

omit [IsProbabilityMeasure P] in
lemma cmom_self (W : Ω → ℂ) (p : ℕ) : cmom W P p p = ((∫ ω, ‖W ω‖ ^ (2 * p) ∂P : ℝ) : ℂ) := by
  rw [cmom, ← integral_complex_ofReal]
  congr 1; ext ω
  rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

omit [IsProbabilityMeasure P] in
/-- **Lemma 3.2 (Orthogonality).** For rotationally invariant `X` with finite moments,
`E[X^p \bar X^q] = δ_{pq} μ_p`. -/
theorem RotInv.cmom_eq {X : Ω → ℂ} (hrot : RotInv X P) (p q : ℕ) :
    cmom X P p q = if p = q then (radMom X P p : ℂ) else 0 := by
  split_ifs with hpq
  · subst hpq; rw [cmom_self]; rfl
  · -- rotate by θ = π/(p - q)
    set θ : ℝ := Real.pi / ((p : ℝ) - q) with hθ
    have hpq' : ((p : ℝ) - q) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hpq)
    have key := ((hrot θ).comp (u := fun z : ℂ => z ^ p * conj z ^ q) (by fun_prop)).integral_eq
    simp only [Function.comp_def] at key
    have hrw : ∀ ω, (Complex.exp (θ * Complex.I) * X ω) ^ p * conj (Complex.exp (θ * Complex.I) * X ω) ^ q
        = - (X ω ^ p * conj (X ω) ^ q) := by
      intro ω
      have hc : conj (Complex.exp (θ * Complex.I)) = Complex.exp (-(θ * Complex.I)) := by
        rw [← Complex.exp_conj]; simp [Complex.conj_ofReal]
      rw [map_mul, hc, mul_pow, mul_pow]
      have h1 : Complex.exp (θ * Complex.I) ^ p * Complex.exp (-(θ * Complex.I)) ^ q = -1 := by
        rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
        have : (p : ℂ) * (θ * Complex.I) + (q : ℂ) * -(θ * Complex.I) = Real.pi * Complex.I := by
          rw [hθ]; push_cast
          have : ((p : ℂ) - q) ≠ 0 := by exact_mod_cast hpq'
          field_simp; ring
        rw [this, Complex.exp_pi_mul_I]
      calc Complex.exp (θ * Complex.I) ^ p * X ω ^ p * (Complex.exp (-(θ * Complex.I)) ^ q * conj (X ω) ^ q)
          = (Complex.exp (θ * Complex.I) ^ p * Complex.exp (-(θ * Complex.I)) ^ q) *
              (X ω ^ p * conj (X ω) ^ q) := by ring
        _ = _ := by rw [h1]; ring
    simp_rw [hrw, integral_neg] at key
    rw [cmom]
    linear_combination -key / 2

/-- Mixed moments of a sum of two independent variables with orthogonal moments. -/
theorem cmom_add_of_indep {U V : Ω → ℂ} (hU : AllMoments U P) (hV : AllMoments V P)
    (hind : IndepFun U V P)
    {α β : ℕ → ℝ} (hα : ∀ a b, cmom U P a b = if a = b then (α a : ℂ) else 0)
    (hβ : ∀ a b, cmom V P a b = if a = b then (β a : ℂ) else 0) (p q : ℕ) :
    cmom (fun ω => U ω + V ω) P p q =
      if p = q then ((∑ k ∈ range (p + 1), ((p.choose k : ℕ) : ℝ) ^ 2 * α k * β (p - k) : ℝ) : ℂ)
      else 0 := by
  have hexp : ∀ ω, (U ω + V ω) ^ p * conj (U ω + V ω) ^ q =
      ∑ k ∈ range (p + 1), ∑ l ∈ range (q + 1),
        ((p.choose k : ℂ) * (q.choose l : ℂ)) *
          ((U ω ^ k * conj (U ω) ^ l) * (V ω ^ (p - k) * conj (V ω) ^ (q - l))) := by
    intro ω
    rw [map_add, add_pow, add_pow, sum_mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    ring
  have hterm : ∀ k l, Integrable (fun ω => ((p.choose k : ℂ) * (q.choose l : ℂ)) *
      ((U ω ^ k * conj (U ω) ^ l) * (V ω ^ (p - k) * conj (V ω) ^ (q - l)))) P := by
    intro k l
    refine Integrable.const_mul ?_ _
    have hi : IndepFun (fun ω => U ω ^ k * conj (U ω) ^ l)
        (fun ω => V ω ^ (p - k) * conj (V ω) ^ (q - l)) P :=
      hind.comp (φ := fun z : ℂ => z ^ k * conj z ^ l) (ψ := fun z : ℂ => z ^ (p - k) * conj z ^ (q - l))
        (by fun_prop) (by fun_prop)
    exact hi.integrable_mul (hU.integrable_pow_mul_conj_pow k l)
      (hV.integrable_pow_mul_conj_pow (p - k) (q - l))
  have hval : ∀ k l, ∫ ω, ((p.choose k : ℂ) * (q.choose l : ℂ)) *
      ((U ω ^ k * conj (U ω) ^ l) * (V ω ^ (p - k) * conj (V ω) ^ (q - l))) ∂P
      = ((p.choose k : ℂ) * (q.choose l : ℂ)) * (cmom U P k l * cmom V P (p - k) (q - l)) := by
    intro k l
    rw [integral_const_mul]
    congr 1
    have hi : IndepFun (fun ω => U ω ^ k * conj (U ω) ^ l)
        (fun ω => V ω ^ (p - k) * conj (V ω) ^ (q - l)) P :=
      hind.comp (φ := fun z : ℂ => z ^ k * conj z ^ l) (ψ := fun z : ℂ => z ^ (p - k) * conj z ^ (q - l))
        (by fun_prop) (by fun_prop)
    exact hi.integral_fun_mul_eq_mul_integral
      (hU.integrable_pow_mul_conj_pow k l).1 (hV.integrable_pow_mul_conj_pow (p - k) (q - l)).1
  rw [cmom]
  simp_rw [hexp]
  rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _ fun l _ => hterm k l)]
  simp_rw [integral_finset_sum _ (fun l _ => hterm _ l), hval, hα, hβ]
  -- now a purely combinatorial evaluation
  have inner : ∀ k ∈ range (p + 1), ∑ l ∈ range (q + 1),
      ((p.choose k : ℂ) * (q.choose l : ℂ)) *
        ((if k = l then (α k : ℂ) else 0) * (if p - k = q - l then (β (p - k) : ℂ) else 0))
      = if k ≤ q ∧ p - k = q - k then ((p.choose k : ℂ) * (q.choose k : ℂ)) * ((α k : ℂ) * β (p - k))
        else 0 := by
    intro k hk
    rw [sum_eq_single k]
    · by_cases hkq : k ≤ q
      · by_cases h2 : p - k = q - k <;> simp [hkq, h2]
      · have : q.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [hkq, this]
    · intro l _ hlk; simp [Ne.symm hlk]
    · intro hk'
      have : q.choose k = 0 := Nat.choose_eq_zero_of_lt (by simp at hk'; omega)
      simp [this]
  rw [sum_congr rfl inner]
  split_ifs with hpq
  · subst hpq
    push_cast
    refine sum_congr rfl fun k hk => ?_
    have hk : k ≤ p := by have := mem_range.1 hk; omega
    simp [hk]; ring
  · refine sum_eq_zero fun k hk => ?_
    have hk : k ≤ p := by have := mem_range.1 hk; omega
    rw [if_neg]; omega

/-- Basic hypotheses on the darts: independent, identically distributed, rotationally
invariant, with finite moments of all orders. -/
structure RadialSample {ι : Type*} (X : ι → Ω → ℂ) (P : Measure Ω) : Prop where
  meas : ∀ j, Measurable (X j)
  indep : iIndepFun X P
  ident : ∀ i j, IdentDistrib (X i) (X j) P P
  rot : ∀ j, RotInv (X j) P
  mom : ∀ j, AllMoments (X j) P

namespace RadialSample

variable {ι : Type*} {X : ι → Ω → ℂ}

omit [IsProbabilityMeasure P] in
lemma radMom_eq (hX : RadialSample X P) (i j : ι) : radMom (X i) P = radMom (X j) P := by
  ext n
  exact ((hX.ident i j).comp (u := fun z : ℂ => ‖z‖ ^ (2 * n)) (by fun_prop)).integral_eq

lemma radMom_zero (j : ι) : radMom (X j) P 0 = 1 := by
  simp [radMom]

omit [IsProbabilityMeasure P] in
lemma radMom_nonneg (j : ι) (n : ℕ) : 0 ≤ radMom (X j) P n :=
  integral_nonneg fun _ => by positivity

/-- **Lemma 3.4 (Moments of the center), unnormalised form.** For a finite set `s` of indices
and `T = ∑_{j∈s} X_j`, `E[T^p \bar T^q] = δ_{pq} Qsum μ |s| p`. -/
theorem cmom_sum (hX : RadialSample X P) (i₀ : ι) (s : Finset ι) (p q : ℕ) :
    cmom (fun ω => ∑ j ∈ s, X j ω) P p q =
      if p = q then (Qsum (radMom (X i₀) P) s.card p : ℂ) else 0 := by
  classical
  induction s using Finset.induction_on generalizing p q with
  | empty =>
    simp only [sum_empty, card_empty, Qsum_zero_left]
    rw [cmom]
    by_cases hp : p = 0 <;> by_cases hq : q = 0 <;> simp [hp, hq]
    · omega
  | insert i s hi ih =>
    have hsum : (fun ω => ∑ j ∈ insert i s, X j ω) = fun ω => X i ω + ∑ j ∈ s, X j ω := by
      ext ω; rw [sum_insert hi]
    rw [hsum, card_insert_of_notMem hi]
    have hind : IndepFun (X i) (fun ω => ∑ j ∈ s, X j ω) P := by
      have := (hX.indep.indepFun_finset_sum_of_notMem hX.meas hi).symm
      convert this using 1
      ext ω; simp [Finset.sum_apply]
    rw [cmom_add_of_indep (hX.mom i) (AllMoments.finset_sum s fun j _ => hX.mom j) hind (α := radMom (X i₀) P) (β := Qsum (radMom (X i₀) P) s.card)
      (fun a b => by rw [(hX.rot i).cmom_eq, hX.radMom_eq i i₀])
      (fun a b => ih a b)]
    rfl

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary4.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

namespace Barycenter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Part 4. The center `S_m` and the means of powers `W_m^{(n)}` -/

/-- The centred center of mass `S_m = m^{-1} ∑_{j<m} X_j` (so `ω_m = a + S_m`). -/
noncomputable def Scen (X : ℕ → Ω → ℂ) (m : ℕ) (ω : Ω) : ℂ := (m : ℂ)⁻¹ * ∑ j ∈ range m, X j ω

/-- The mean of `n`th powers `W_m^{(n)} = m^{-1} ∑_{j<m} X_j^n`. -/
noncomputable def Wpow (X : ℕ → Ω → ℂ) (m n : ℕ) (ω : Ω) : ℂ :=
  (m : ℂ)⁻¹ * ∑ j ∈ range m, X j ω ^ n

omit [IsProbabilityMeasure P] in
lemma cmom_const_mul (W : Ω → ℂ) (c : ℂ) (p q : ℕ) :
    cmom (fun ω => c * W ω) P p q = c ^ p * conj c ^ q * cmom W P p q := by
  rw [cmom, cmom, ← integral_const_mul]
  congr 1; ext ω; rw [map_mul]; ring

/-- Cross moments `E[U^p \overline{(U+V)}^q]` for independent `U, V`. -/
theorem cross_add_of_indep {U V : Ω → ℂ} (hU : AllMoments U P) (hV : AllMoments V P)
    (hind : IndepFun U V P) {α : ℕ → ℝ}
    (hα : ∀ a b, cmom U P a b = if a = b then (α a : ℂ) else 0)
    (hβ : ∀ b, cmom V P 0 b = if b = 0 then 1 else 0) (p q : ℕ) :
    ∫ ω, U ω ^ p * conj (U ω + V ω) ^ q ∂P = if p = q then (α p : ℂ) else 0 := by
  have hexp : ∀ ω, U ω ^ p * conj (U ω + V ω) ^ q =
      ∑ l ∈ range (q + 1), (q.choose l : ℂ) *
          ((U ω ^ p * conj (U ω) ^ l) * (V ω ^ 0 * conj (V ω) ^ (q - l))) := by
    intro ω
    rw [map_add, add_pow, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    ring
  have hi : ∀ l, IndepFun (fun ω => U ω ^ p * conj (U ω) ^ l)
      (fun ω => V ω ^ 0 * conj (V ω) ^ (q - l)) P := fun l =>
    hind.comp (φ := fun z : ℂ => z ^ p * conj z ^ l) (ψ := fun z : ℂ => z ^ 0 * conj z ^ (q - l))
      (by fun_prop) (by fun_prop)
  have hterm : ∀ l, Integrable (fun ω => (q.choose l : ℂ) *
      ((U ω ^ p * conj (U ω) ^ l) * (V ω ^ 0 * conj (V ω) ^ (q - l)))) P := fun l =>
    ((hi l).integrable_mul (hU.integrable_pow_mul_conj_pow p l)
      (hV.integrable_pow_mul_conj_pow 0 (q - l))).const_mul _
  simp_rw [hexp]
  rw [integral_finset_sum _ fun l _ => hterm l]
  have hval : ∀ l, ∫ ω, (q.choose l : ℂ) *
      ((U ω ^ p * conj (U ω) ^ l) * (V ω ^ 0 * conj (V ω) ^ (q - l))) ∂P
      = (q.choose l : ℂ) * (cmom U P p l * cmom V P 0 (q - l)) := by
    intro l
    rw [integral_const_mul]
    congr 1
    exact (hi l).integral_fun_mul_eq_mul_integral
      (hU.integrable_pow_mul_conj_pow p l).1 (hV.integrable_pow_mul_conj_pow 0 (q - l)).1
  simp_rw [hval, hα, hβ]
  split_ifs with hpq
  · subst hpq
    rw [sum_eq_single p]
    · simp
    · intro l hl hlp
      have : l < p ∨ p < l := lt_or_gt_of_ne hlp
      have hl' : l ≤ p := by have := mem_range.1 hl; omega
      rcases this with h | h
      · simp [Ne.symm hlp]
      · omega
    · intro h; simp at h
  · refine sum_eq_zero fun l hl => ?_
    have hl' : l ≤ q := by have := mem_range.1 hl; omega
    by_cases hlp : p = l
    · have : q - l ≠ 0 := by omega
      simp [this]
    · simp [hlp]

namespace RadialSample

variable {X : ℕ → Ω → ℂ}

/-- **Lemma 3.4 (Moments of the center).** `E[S_m^p \bar S_m^q] = δ_{pq} q_{m,p}`. -/
theorem cmom_Scen (hX : RadialSample X P) (m p q : ℕ) :
    cmom (Scen X m) P p q = if p = q then (qmom (radMom (X 0) P) m p : ℂ) else 0 := by
  have h1 : Scen X m = fun ω => ((m : ℂ)⁻¹) * ∑ j ∈ range m, X j ω := rfl
  rw [h1, cmom_const_mul, hX.cmom_sum 0 (range m) p q, card_range]
  split_ifs with hpq
  · subst hpq
    rw [qmom]; push_cast
    rw [map_inv₀, Complex.conj_natCast, ← mul_pow, pow_mul, div_eq_inv_mul, ← inv_pow, sq,
      mul_inv]
  · simp

omit [IsProbabilityMeasure P] in
lemma allMoments_Scen (hX : RadialSample X P) (m : ℕ) : AllMoments (Scen X m) P :=
  (AllMoments.finset_sum (range m) fun j _ => hX.mom j).const_mul _

omit [IsProbabilityMeasure P] in
lemma measurable_Scen (hX : RadialSample X P) (m : ℕ) : Measurable (Scen X m) :=
  measurable_const.mul (Finset.measurable_sum _ fun j _ => hX.meas j)

omit [IsProbabilityMeasure P] in
lemma integral_pow_eq_zero (hX : RadialSample X P) (j : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    ∫ ω, X j ω ^ p ∂P = 0 := by
  have := (hX.rot j).cmom_eq p 0
  rw [if_neg (by omega)] at this
  simpa [cmom] using this

/-- `E W_m^{(n)} = 0` for `n ≥ 1` (Lemma 3.3). -/
theorem integral_Wpow (hX : RadialSample X P) (m : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ ω, Wpow X m n ω ∂P = 0 := by
  simp only [Wpow]
  rw [integral_const_mul, integral_finset_sum _ fun j _ => (hX.mom j).integrable_pow n]
  simp [hX.integral_pow_eq_zero _ hn]

/-- **Lemma 3.3 (Monomial centers).** `E[W^{(p)} \overline{W^{(q)}}] = δ_{pq} μ_p / m`. -/
theorem integral_Wpow_mul_conj (hX : RadialSample X P) {m : ℕ} (hm : 1 ≤ m) {p q : ℕ}
    (hp : 1 ≤ p) :
    ∫ ω, Wpow X m p ω * conj (Wpow X m q ω) ∂P =
      if p = q then ((radMom (X 0) P p / m : ℝ) : ℂ) else 0 := by
  have hexp : ∀ ω, Wpow X m p ω * conj (Wpow X m q ω) =
      ((m : ℂ)⁻¹) ^ 2 * ∑ j ∈ range m, ∑ k ∈ range m, X j ω ^ p * conj (X k ω) ^ q := by
    intro ω
    rw [Wpow, Wpow, map_mul, map_sum, map_inv₀, Complex.conj_natCast]
    simp_rw [map_pow]
    rw [mul_mul_mul_comm, sum_mul_sum, sq]
  have hint : ∀ j k, Integrable (fun ω => X j ω ^ p * conj (X k ω) ^ q) P := by
    intro j k
    by_cases hjk : j = k
    · subst hjk; exact (hX.mom j).integrable_pow_mul_conj_pow p q
    · have hi : IndepFun (fun ω => X j ω ^ p) (fun ω => conj (X k ω) ^ q) P :=
        (hX.indep.indepFun hjk).comp (φ := fun z : ℂ => z ^ p) (ψ := fun z : ℂ => conj z ^ q)
          (by fun_prop) (by fun_prop)
      exact hi.integrable_mul ((hX.mom j).integrable_pow p)
        (by simpa using (hX.mom k).integrable_pow_mul_conj_pow 0 q)
  have hval : ∀ j k, ∫ ω, X j ω ^ p * conj (X k ω) ^ q ∂P =
      if j = k then (if p = q then (radMom (X 0) P p : ℂ) else 0) else 0 := by
    intro j k
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl, ← cmom, (hX.rot j).cmom_eq, hX.radMom_eq j 0]
    · rw [if_neg hjk]
      have hi : IndepFun (fun ω => X j ω ^ p) (fun ω => conj (X k ω) ^ q) P :=
        (hX.indep.indepFun hjk).comp (φ := fun z : ℂ => z ^ p) (ψ := fun z : ℂ => conj z ^ q)
          (by fun_prop) (by fun_prop)
      rw [hi.integral_fun_mul_eq_mul_integral ((hX.mom j).integrable_pow p).1
        (by simpa using ((hX.mom k).integrable_pow_mul_conj_pow 0 q).1),
        hX.integral_pow_eq_zero j hp, zero_mul]
  simp_rw [hexp]
  rw [integral_const_mul, integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => hint j k]
  simp_rw [integral_finset_sum _ fun k _ => hint _ k, hval]
  simp only [sum_ite_eq, mem_range]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  split_ifs with hpq
  · rw [sum_congr rfl (fun x hx => if_pos (mem_range.1 hx))]
    simp only [sum_const, card_range, nsmul_eq_mul]
    push_cast; field_simp
  · simp

/-- **Lemma 3.4, mixed moment.** `E[W^{(p)} \bar S_m^q] = δ_{pq} μ_p m^{-p}`. -/
theorem integral_Wpow_mul_conj_Scen (hX : RadialSample X P) {m : ℕ} (hm : 1 ≤ m) (p q : ℕ) :
    ∫ ω, Wpow X m p ω * conj (Scen X m ω) ^ q ∂P =
      if p = q then ((radMom (X 0) P p / (m : ℝ) ^ p : ℝ) : ℂ) else 0 := by
  classical
  -- each summand
  have hj : ∀ j ∈ range m, ∫ ω, X j ω ^ p * conj (∑ i ∈ range m, X i ω) ^ q ∂P =
      if p = q then (radMom (X 0) P p : ℂ) else 0 := by
    intro j hjm
    have hsplit : ∀ ω, ∑ i ∈ range m, X i ω = X j ω + ∑ i ∈ (range m).erase j, X i ω := by
      intro ω; exact (add_sum_erase (range m) (fun i => X i ω) hjm).symm
    simp_rw [hsplit]
    have hind : IndepFun (X j) (fun ω => ∑ i ∈ (range m).erase j, X i ω) P := by
      have := (hX.indep.indepFun_finset_sum_of_notMem hX.meas (notMem_erase j (range m))).symm
      convert this using 1
      ext ω; simp [Finset.sum_apply]
    rw [cross_add_of_indep (hX.mom j) (AllMoments.finset_sum _ fun i _ => hX.mom i) hind
      (α := radMom (X 0) P) (fun a b => by rw [(hX.rot j).cmom_eq, hX.radMom_eq j 0])
      (fun b => by
        rw [hX.cmom_sum 0 _ 0 b]
        by_cases hb : b = 0
        · subst hb; simp [Qsum_zero_right _ (radMom_zero (X := X) 0)]
        · simp [Ne.symm hb, hb])]
  have hexp : ∀ ω, Wpow X m p ω * conj (Scen X m ω) ^ q =
      ((m : ℂ)⁻¹) ^ (q + 1) * ∑ j ∈ range m, X j ω ^ p * conj (∑ i ∈ range m, X i ω) ^ q := by
    intro ω
    rw [Wpow, Scen, map_mul, map_inv₀, Complex.conj_natCast, mul_pow, mul_sum, sum_mul, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  have hint : ∀ j ∈ range m, Integrable (fun ω => X j ω ^ p * conj (∑ i ∈ range m, X i ω) ^ q) P := by
    intro j _
    have hA := (hX.mom j)
    have hB := AllMoments.finset_sum (range m) fun i _ => hX.mom i
    refine (((hA.integrable_norm_pow (2 * p)).add (hB.integrable_norm_pow (2 * q)))).mono' ?_
      (Eventually.of_forall fun ω => ?_)
    · exact (hA.aestronglyMeasurable.pow p).mul
        ((Complex.continuous_conj.comp_aestronglyMeasurable hB.aestronglyMeasurable).pow q)
    · rw [norm_mul, norm_pow, norm_pow, Complex.norm_conj]
      set a := ‖X j ω‖; set b := ‖∑ i ∈ range m, X i ω‖
      have ha : 0 ≤ a ^ p := by positivity
      have hb : 0 ≤ b ^ q := by positivity
      have : a ^ p * b ^ q ≤ (a ^ p) ^ 2 + (b ^ q) ^ 2 := by nlinarith [sq_nonneg (a ^ p - b ^ q)]
      calc a ^ p * b ^ q ≤ (a ^ p) ^ 2 + (b ^ q) ^ 2 := this
        _ = a ^ (2 * p) + b ^ (2 * q) := by ring
  simp_rw [hexp]
  rw [integral_const_mul, integral_finset_sum _ hint, sum_congr rfl hj]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  split_ifs with hpq
  · subst hpq
    simp only [sum_const, card_range, nsmul_eq_mul]
    push_cast; rw [inv_pow]; field_simp; ring
  · simp

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary5.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

namespace Barycenter

/-! ## Part 5. Comparison with unit steps (Lemma 3.6) -/

lemma Qsum_geom (c : ℝ) (m n : ℕ) :
    Qsum (fun k => c ^ k) m n = c ^ n * Qsum (fun _ => 1) m n := by
  induction m generalizing n with
  | zero => by_cases hn : n = 0 <;> simp [Qsum_zero_left, hn]
  | succ m ih =>
    rw [Qsum_succ, Qsum_succ, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi : i ≤ n := by have := mem_range.1 hi; omega
    rw [ih, show c ^ n = c ^ i * c ^ (n - i) by rw [← pow_add]; congr 1; omega]
    ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Lyapunov's inequality for the radial moments: `μ_k ≤ μ_n^{k/n}` for `1 ≤ k ≤ n`. -/
lemma radMom_le_rpow {X : Ω → ℂ} (hX : AllMoments X P) {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    radMom X P k ≤ (radMom X P n) ^ ((k : ℝ) / n) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp : (1 : ℝ) ≤ (n : ℝ) / k := by
    rw [le_div_iff₀ hk', one_mul]; exact_mod_cast hkn
  have hY : ∀ ω, (‖X ω‖ ^ (2 * k)) ^ ((n : ℝ) / k) = ‖X ω‖ ^ (2 * n) := by
    intro ω
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast]
    congr 1; push_cast; field_simp
  have hJ := (convexOn_rpow hp).map_integral_le (μ := P) (f := fun ω => ‖X ω‖ ^ (2 * k))
    ((Real.continuous_rpow_const (by linarith)).continuousOn) isClosed_Ici
    (Eventually.of_forall fun ω => Set.mem_Ici.2 (by positivity))
    (hX.integrable_norm_pow _) (by simpa [Function.comp_def, hY] using hX.integrable_norm_pow (2 * n))
  simp only [hY] at hJ
  have h0 : 0 ≤ radMom X P k := integral_nonneg fun _ => by positivity
  calc radMom X P k = ((radMom X P k) ^ ((n : ℝ) / k)) ^ ((k : ℝ) / n) := by
        rw [← Real.rpow_mul h0]; field_simp; simp
    _ ≤ (radMom X P n) ^ ((k : ℝ) / n) := by
        apply Real.rpow_le_rpow (by positivity) hJ (by positivity)

/-- Lyapunov's inequality in the form `μ_k ≤ M^k` with `M = μ_n^{1/n}`, for `k ≤ n`. -/
lemma radMom_le_pow_root {X : Ω → ℂ} (hX : AllMoments X P) {n : ℕ} :
    ∀ k ≤ n, radMom X P k ≤ ((radMom X P n) ^ ((1 : ℝ) / n)) ^ k := by
  intro k hkn
  have hμn : 0 ≤ radMom X P n := integral_nonneg fun _ => by positivity
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [radMom]
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hμn]
    convert radMom_le_rpow hX hk hkn using 2
    ring

namespace RadialSample

variable {X : ℕ → Ω → ℂ}

/-- **Lemma 3.6, first inequality.** `q_{m,n} ≤ μ_n κ_{m,n}`. -/
theorem qmom_le (hX : RadialSample X P) (m n : ℕ) :
    qmom (radMom (X 0) P) m n ≤ radMom (X 0) P n * kappa m n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [qmom, kappa, Qsum_zero_right _ (radMom_zero (X := X) 0), radMom_zero (X := X) 0,
      Qsum_zero_right (fun _ => (1 : ℝ)) rfl]
  set μ := radMom (X 0) P
  set M := μ n ^ ((1 : ℝ) / n)
  have hμn : 0 ≤ μ n := radMom_nonneg (X := X) 0 n
  have hM : 0 ≤ M := Real.rpow_nonneg hμn _
  have hMn : M ^ n = μ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμn]; field_simp; simp
  have h := Qsum_le_pow_mul μ (radMom_nonneg (X := X) 0) hM (radMom_le_pow_root (hX.mom 0)) m n le_rfl
  rw [hMn] at h
  rw [kappa, qmom, qmom, mul_div_assoc']
  exact div_le_div_of_nonneg_right h (by positivity)

/-- **Lemma 3.6, equality case.** For `m, n ≥ 2`, `q_{m,n} = μ_n κ_{m,n}` iff `|X|` is almost
surely constant. -/
theorem qmom_eq_iff (hX : RadialSample X P) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    qmom (radMom (X 0) P) m n = radMom (X 0) P n * kappa m n ↔
      ∃ c : ℝ, ∀ᵐ ω ∂P, ‖X 0 ω‖ = c := by
  set μ := radMom (X 0) P with hμdef
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  constructor
  · intro heq
    set M := μ n ^ ((1 : ℝ) / n)
    have hμn : 0 ≤ μ n := radMom_nonneg (X := X) 0 n
    have hM : 0 ≤ M := Real.rpow_nonneg hμn _
    have hMn : M ^ n = μ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hμn]; field_simp; simp
    have hQ : Qsum μ m n = M ^ n * Qsum (fun _ => 1) m n := by
      rw [kappa, qmom, qmom, mul_div_assoc'] at heq
      rw [hMn]
      exact (div_left_inj' (by positivity)).1 heq
    have h1 := Qsum_eq_pow_mul_imp μ (radMom_nonneg (X := X) 0) hM hn
      (radMom_le_pow_root (hX.mom 0)) hm hQ
    -- `μ₁^n = μ_n`
    have hpow : μ 1 ^ n = μ n := by rw [h1, hMn]
    -- strict Jensen for `t ↦ t^n` applied to `Y = |X|²`
    have hJ := (strictConvexOn_pow (by omega : 2 ≤ n)).ae_eq_const_or_map_average_lt (μ := P)
      (f := fun ω => ‖X 0 ω‖ ^ 2) (continuous_pow n).continuousOn isClosed_Ici
      (Eventually.of_forall fun ω => Set.mem_Ici.2 (by positivity))
      ((hX.mom 0).integrable_norm_pow 2)
      (by simpa [Function.comp_def, ← pow_mul] using (hX.mom 0).integrable_norm_pow (2 * n))
    simp only [average_eq_integral] at hJ
    rcases hJ with hae | hlt
    · refine ⟨Real.sqrt (∫ ω, ‖X 0 ω‖ ^ 2 ∂P), ?_⟩
      filter_upwards [hae] with ω hω
      simp only [Function.const_apply] at hω
      rw [← hω, Real.sqrt_sq (norm_nonneg _)]
    · exfalso
      have e1 : ∫ ω, ‖X 0 ω‖ ^ 2 ∂P = μ 1 := by simp [hμdef, radMom]
      have e2 : ∫ ω, (‖X 0 ω‖ ^ 2) ^ n ∂P = μ n := by simp [hμdef, radMom, ← pow_mul]
      rw [e1, e2, hpow] at hlt
      exact lt_irrefl _ hlt
  · rintro ⟨c, hc⟩
    have hμk : ∀ k, μ k = (c ^ 2) ^ k := by
      intro k
      simp only [hμdef, radMom]
      rw [integral_congr_ae (g := fun _ => c ^ (2 * k)) (hc.mono fun ω hω => by simp only [hω])]
      simp [← pow_mul]
    have hμfun : μ = fun k => (c ^ 2) ^ k := funext hμk
    rw [kappa, qmom, qmom, hμfun, Qsum_geom]
    ring

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary6.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

namespace Barycenter

/-! ## Part 6. Steinhaus variables and the random-walk constants -/

instance fact_two_pi_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The sample space of an i.i.d. sequence of Steinhaus variables. -/
abbrev SteinhausΩ := ℕ → AddCircle (2 * Real.pi)

/-- Product of normalised Haar measures on the circle. -/
noncomputable def steinhausMeasure : Measure SteinhausΩ :=
  Measure.infinitePi fun _ => AddCircle.haarAddCircle

instance : IsProbabilityMeasure steinhausMeasure := by
  unfold steinhausMeasure; infer_instance

/-- The Steinhaus variables `U_j`, uniform on the unit circle. -/
noncomputable def steinhaus (j : ℕ) (ω : SteinhausΩ) : ℂ := (AddCircle.toCircle (ω j) : ℂ)

lemma measurable_toCircle_coe :
    Measurable fun x : AddCircle (2 * Real.pi) => ((AddCircle.toCircle x : Circle) : ℂ) :=
  (continuous_subtype_val.comp AddCircle.continuous_toCircle).measurable

lemma norm_steinhaus (j : ℕ) (ω : SteinhausΩ) : ‖steinhaus j ω‖ = 1 := by
  simp [steinhaus]

lemma exp_mul_toCircle (θ : ℝ) (x : AddCircle (2 * Real.pi)) :
    Complex.exp (θ * Complex.I) * ((AddCircle.toCircle x : Circle) : ℂ)
      = ((AddCircle.toCircle ((θ : AddCircle (2 * Real.pi)) + x) : Circle) : ℂ) := by
  rw [AddCircle.toCircle_add, AddCircle.toCircle_apply_mk]
  have : 2 * Real.pi / (2 * Real.pi) * θ = θ := by
    field_simp
  rw [this]
  simp [Circle.coe_exp]

/-- The Steinhaus variables form a radial sample with `|U_j| = 1`. -/
theorem steinhaus_radialSample : RadialSample steinhaus steinhausMeasure where
  meas j := measurable_toCircle_coe.comp (measurable_pi_apply j)
  indep := by
    have := iIndepFun_infinitePi (P := fun _ : ℕ => (AddCircle.haarAddCircle :
      Measure (AddCircle (2 * Real.pi)))) (X := fun _ x => ((AddCircle.toCircle x : Circle) : ℂ))
      (fun _ => measurable_toCircle_coe)
    exact this
  ident i j := by
    refine ⟨(measurable_toCircle_coe.comp (measurable_pi_apply i)).aemeasurable,
      (measurable_toCircle_coe.comp (measurable_pi_apply j)).aemeasurable, ?_⟩
    have hi : steinhaus i = (fun x : AddCircle (2 * Real.pi) => ((AddCircle.toCircle x : Circle) : ℂ))
        ∘ (fun ω : SteinhausΩ => ω i) := rfl
    have hj : steinhaus j = (fun x : AddCircle (2 * Real.pi) => ((AddCircle.toCircle x : Circle) : ℂ))
        ∘ (fun ω : SteinhausΩ => ω j) := rfl
    rw [hi, hj, ← Measure.map_map measurable_toCircle_coe (measurable_pi_apply i),
      ← Measure.map_map measurable_toCircle_coe (measurable_pi_apply j), steinhausMeasure,
      Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]
  rot j θ := by
    have hmeas := measurable_toCircle_coe.comp (measurable_pi_apply (X := fun _ : ℕ =>
      AddCircle (2 * Real.pi)) j)
    refine ⟨(measurable_const.mul hmeas).aemeasurable, hmeas.aemeasurable, ?_⟩
    have he : Measurable (fun ω : SteinhausΩ => ω j) := measurable_pi_apply j
    have hc : Measurable (fun x : AddCircle (2 * Real.pi) => (θ : AddCircle (2 * Real.pi)) + x) :=
      measurable_const_add _
    have hev : steinhausMeasure.map (fun ω : SteinhausΩ => ω j) = AddCircle.haarAddCircle :=
      Measure.infinitePi_map_eval _ j
    have h1 : (fun ω : SteinhausΩ => Complex.exp (θ * Complex.I) * steinhaus j ω) =
        ((fun x : AddCircle (2 * Real.pi) => ((AddCircle.toCircle x : Circle) : ℂ)) ∘
          (fun x => (θ : AddCircle (2 * Real.pi)) + x)) ∘ (fun ω : SteinhausΩ => ω j) := by
      ext ω; simp only [Function.comp_apply, steinhaus, exp_mul_toCircle]
    have hj : steinhaus j = (fun x : AddCircle (2 * Real.pi) => ((AddCircle.toCircle x : Circle) : ℂ))
        ∘ (fun ω : SteinhausΩ => ω j) := rfl
    rw [h1, hj, ← Measure.map_map (measurable_toCircle_coe.comp hc) he,
      ← Measure.map_map measurable_toCircle_coe he, hev, ← Measure.map_map measurable_toCircle_coe hc,
      map_add_left_eq_self]
  mom j p := MemLp.of_bound
    (measurable_toCircle_coe.comp (measurable_pi_apply j)).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => (norm_steinhaus j ω).le)

lemma radMom_steinhaus (n : ℕ) : radMom (steinhaus 0) steinhausMeasure n = 1 := by
  simp [radMom, norm_steinhaus]

/-- `κ_{m,n} = E|m^{-1}(U_1+⋯+U_m)|^{2n}`: the probabilistic meaning (1.6) of `κ`. -/
theorem kappa_eq_integral (m n : ℕ) :
    kappa m n = ∫ ω, (‖Scen steinhaus m ω‖ ^ 2) ^ n ∂steinhausMeasure := by
  have h := steinhaus_radialSample.cmom_Scen m n n
  rw [if_pos rfl, cmom_self] at h
  have h1 : radMom (steinhaus 0) steinhausMeasure = fun _ => 1 := funext radMom_steinhaus
  rw [h1] at h
  simp_rw [← pow_mul]
  exact_mod_cast h.symm

lemma norm_Scen_steinhaus_le {m : ℕ} (ω : SteinhausΩ) : ‖Scen steinhaus m ω‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Scen]
  rw [Scen, norm_mul, norm_inv, Complex.norm_natCast]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [inv_mul_le_iff₀ hm', mul_one]
  calc ‖∑ j ∈ range m, steinhaus j ω‖ ≤ ∑ j ∈ range m, ‖steinhaus j ω‖ := norm_sum_le _ _
    _ = m := by simp [norm_steinhaus]

lemma integrable_T_pow (m n : ℕ) :
    Integrable (fun ω => (‖Scen steinhaus m ω‖ ^ 2) ^ n) steinhausMeasure := by
  simpa [← pow_mul] using (steinhaus_radialSample.allMoments_Scen m).integrable_norm_pow (2 * n)

/-- **Lemma 3.6, second inequality.** `κ_{m,n} ≤ 1/m` for `m, n ≥ 1`. -/
theorem kappa_le_inv {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) : kappa m n ≤ 1 / m := by
  rw [← kappa_one hm, kappa_eq_integral, kappa_eq_integral]
  refine integral_mono (integrable_T_pow m n) (integrable_T_pow m 1) fun ω => ?_
  have h0 : 0 ≤ ‖Scen steinhaus m ω‖ ^ 2 := by positivity
  have h1 : ‖Scen steinhaus m ω‖ ^ 2 ≤ 1 := by
    have := norm_Scen_steinhaus_le (m := m) ω
    nlinarith [norm_nonneg (Scen steinhaus m ω)]
  simpa using pow_le_pow_of_le_one h0 h1 hn

/-- **Lemma 3.6, monotonicity.** For `m ≥ 2`, `n ↦ κ_{m,n}` is strictly decreasing. -/
theorem kappa_strictAnti {m : ℕ} (hm : 2 ≤ m) : StrictAnti (kappa m) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  by_contra hcon
  push_neg at hcon
  set T : SteinhausΩ → ℝ := fun ω => ‖Scen steinhaus m ω‖ ^ 2 with hT
  have hT0 : ∀ ω, 0 ≤ T ω := fun ω => by positivity
  have hT1 : ∀ ω, T ω ≤ 1 := fun ω => by
    have := norm_Scen_steinhaus_le (m := m) ω
    simp only [hT]; nlinarith [norm_nonneg (Scen steinhaus m ω)]
  have hnonneg : 0 ≤ fun ω => T ω ^ n - T ω ^ (n + 1) := fun ω => by
    simp only [Pi.zero_apply, sub_nonneg]
    exact pow_le_pow_of_le_one (hT0 ω) (hT1 ω) (Nat.le_succ n)
  have hint : Integrable (fun ω => T ω ^ n - T ω ^ (n + 1)) steinhausMeasure :=
    (integrable_T_pow m n).sub (integrable_T_pow m (n + 1))
  have hzero : ∫ ω, (T ω ^ n - T ω ^ (n + 1)) ∂steinhausMeasure = 0 := by
    rw [integral_sub (integrable_T_pow m n) (integrable_T_pow m (n + 1))]
    have h1 := kappa_eq_integral m n
    have h2 := kappa_eq_integral m (n + 1)
    have hle : ∫ ω, T ω ^ (n + 1) ∂steinhausMeasure ≤ ∫ ω, T ω ^ n ∂steinhausMeasure :=
      integral_mono (integrable_T_pow m (n + 1)) (integrable_T_pow m n) fun ω =>
        pow_le_pow_of_le_one (hT0 ω) (hT1 ω) (Nat.le_succ n)
    simp only [hT] at hle ⊢
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hint).1 hzero
  -- hence `T² = T` almost surely
  have hsq : (fun ω => T ω ^ 2) =ᵐ[steinhausMeasure] T := by
    filter_upwards [hae] with ω hω
    simp only [Pi.zero_apply, sub_eq_zero] at hω
    have : T ω ^ n * (1 - T ω) = 0 := by rw [mul_sub, mul_one, ← pow_succ, hω, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · have : T ω = 0 := (pow_eq_zero_iff'.mp h).1
      rw [this]; norm_num
    · have : T ω = 1 := by linarith
      rw [this]; norm_num
  have hk : kappa m 2 = kappa m 1 := by
    rw [kappa_eq_integral, kappa_eq_integral]
    simp only [pow_one]
    exact integral_congr_ae hsq
  rw [kappa_two (by omega), kappa_one (by omega)] at hk
  have hm' : (m : ℝ) ≠ 0 := by positivity
  field_simp at hk
  have : ((m : ℝ) - 1) ^ 2 = 0 := by nlinarith
  have : (m : ℝ) = 1 := by nlinarith [sq_nonneg ((m : ℝ) - 1), pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 this]
  have : m = 1 := by exact_mod_cast this
  omega

end Barycenter

-- ============================================================================
-- Source part: Bary7.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 7. `L²` theory of analytic functions of variables with orthogonal monomials -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Taylor partial sums `∑_{n<N} b_n z^n`. -/
noncomputable def psum (b : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ := ∑ n ∈ range N, b n * z ^ n

/-- A complex random variable whose monomials are orthogonal:
`E[W^p \bar W^q] = δ_{pq} ν_p`. -/
structure OrthoMoments (W : Ω → ℂ) (P : Measure Ω) (ν : ℕ → ℝ) : Prop where
  meas : Measurable W
  mom : AllMoments W P
  orth : ∀ p q, cmom W P p q = if p = q then (ν p : ℂ) else 0

omit [IsProbabilityMeasure P] in
/-- Complex Cauchy–Schwarz inequality for integrals. -/
lemma norm_integral_mul_conj_le {F G : Ω → ℂ} (hF : MemLp F 2 P) (hG : MemLp G 2 P) :
    ‖∫ ω, F ω * conj (G ω) ∂P‖ ≤
      Real.sqrt (∫ ω, ‖F ω‖ ^ 2 ∂P) * Real.sqrt (∫ ω, ‖G ω‖ ^ 2 ∂P) := by
  have h2 : ENNReal.ofReal 2 = 2 := by simp
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (f := fun ω => ‖F ω‖) (g := fun ω => ‖G ω‖)
    (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun _ => norm_nonneg _)
    (by rw [h2]; exact hF.norm) (by rw [h2]; exact hG.norm)
  simp only [Real.rpow_two] at hCS
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hCS
  calc ‖∫ ω, F ω * conj (G ω) ∂P‖ ≤ ∫ ω, ‖F ω * conj (G ω)‖ ∂P := norm_integral_le_integral_norm _
    _ = ∫ ω, ‖F ω‖ * ‖G ω‖ ∂P := by simp
    _ ≤ _ := hCS

omit [IsProbabilityMeasure P] in
lemma integral_norm_sq_nonneg (F : Ω → ℂ) : 0 ≤ ∫ ω, ‖F ω‖ ^ 2 ∂P :=
  integral_nonneg fun _ => by positivity

omit [IsProbabilityMeasure P] in
/-- Inner products pass to `L²` limits. -/
theorem tendsto_integral_mul_conj {F G : Ω → ℂ} {Fn Gn : ℕ → Ω → ℂ}
    (hF : MemLp F 2 P) (hG : MemLp G 2 P) (hFn : ∀ N, MemLp (Fn N) 2 P) (hGn : ∀ N, MemLp (Gn N) 2 P)
    (hcF : Tendsto (fun N => ∫ ω, ‖F ω - Fn N ω‖ ^ 2 ∂P) atTop (𝓝 0))
    (hcG : Tendsto (fun N => ∫ ω, ‖G ω - Gn N ω‖ ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun N => ∫ ω, Fn N ω * conj (Gn N ω) ∂P) atTop (𝓝 (∫ ω, F ω * conj (G ω) ∂P)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- decomposition of the error
  have hdec : ∀ N, ∫ ω, Fn N ω * conj (Gn N ω) ∂P - ∫ ω, F ω * conj (G ω) ∂P =
      ∫ ω, (F ω - Fn N ω) * conj (G ω - Gn N ω) ∂P - ∫ ω, (F ω - Fn N ω) * conj (G ω) ∂P
        - ∫ ω, F ω * conj (G ω - Gn N ω) ∂P := by
    intro N
    have i1 : Integrable (fun ω => (F ω - Fn N ω) * conj (G ω - Gn N ω)) P :=
      (hF.sub (hFn N)).integrable_mul ((hG.sub (hGn N)).star) (p := 2) (q := 2)
    have i2 : Integrable (fun ω => (F ω - Fn N ω) * conj (G ω)) P :=
      (hF.sub (hFn N)).integrable_mul hG.star (p := 2) (q := 2)
    have i3 : Integrable (fun ω => F ω * conj (G ω - Gn N ω)) P :=
      hF.integrable_mul ((hG.sub (hGn N)).star) (p := 2) (q := 2)
    have i4 : Integrable (fun ω => F ω * conj (G ω)) P := hF.integrable_mul hG.star (p := 2) (q := 2)
    have i5 : Integrable (fun ω => Fn N ω * conj (Gn N ω)) P :=
      (hFn N).integrable_mul (hGn N).star (p := 2) (q := 2)
    have e : ∀ ω, Fn N ω * conj (Gn N ω) - F ω * conj (G ω) =
        ((F ω - Fn N ω) * conj (G ω - Gn N ω) - (F ω - Fn N ω) * conj (G ω))
          - F ω * conj (G ω - Gn N ω) := by
      intro ω; simp only [map_sub]; ring
    rw [← integral_sub i5 i4]
    simp_rw [e]
    have i12 : Integrable (fun ω => (F ω - Fn N ω) * conj (G ω - Gn N ω)
        - (F ω - Fn N ω) * conj (G ω)) P := i1.sub i2
    rw [integral_sub i12 i3, integral_sub i1 i2]
  have hsF := hcF.sqrt
  have hsG := hcG.sqrt
  simp only [Real.sqrt_zero] at hsF hsG
  have hbound : ∀ N, ‖∫ ω, Fn N ω * conj (Gn N ω) ∂P - ∫ ω, F ω * conj (G ω) ∂P‖ ≤
      Real.sqrt (∫ ω, ‖F ω - Fn N ω‖ ^ 2 ∂P) * Real.sqrt (∫ ω, ‖G ω - Gn N ω‖ ^ 2 ∂P)
      + Real.sqrt (∫ ω, ‖F ω - Fn N ω‖ ^ 2 ∂P) * Real.sqrt (∫ ω, ‖G ω‖ ^ 2 ∂P)
      + Real.sqrt (∫ ω, ‖F ω‖ ^ 2 ∂P) * Real.sqrt (∫ ω, ‖G ω - Gn N ω‖ ^ 2 ∂P) := by
    intro N
    rw [hdec]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · exact norm_integral_mul_conj_le (hF.sub (hFn N)) (hG.sub (hGn N))
    · exact norm_integral_mul_conj_le (hF.sub (hFn N)) hG
    · exact norm_integral_mul_conj_le hF (hG.sub (hGn N))
  refine squeeze_zero (fun N => norm_nonneg _) hbound ?_
  have := ((hsF.mul hsG).add (hsF.mul_const (Real.sqrt (∫ ω, ‖G ω‖ ^ 2 ∂P)))).add
    (hsG.const_mul (Real.sqrt (∫ ω, ‖F ω‖ ^ 2 ∂P)))
  simpa using this

lemma AllMoments.memLp_pow {W : Ω → ℂ} (hW : AllMoments W P) (n : ℕ) :
    MemLp (fun ω => W ω ^ n) 2 P := by
  refine (memLp_two_iff_integrable_sq_norm (f := fun ω => W ω ^ n)
    (hW.aestronglyMeasurable.pow n)).2 ?_
  simpa [norm_pow, ← pow_mul, mul_comm] using hW.integrable_norm_pow (2 * n)

namespace OrthoMoments

variable {W : Ω → ℂ} {ν : ℕ → ℝ}

lemma integrable_pow_mul_conj_pow (hW : OrthoMoments W P ν) (p q : ℕ) :
    Integrable (fun ω => W ω ^ p * conj (W ω) ^ q) P := hW.mom.integrable_pow_mul_conj_pow p q

lemma memLp_psum (hW : OrthoMoments W P ν) (b : ℕ → ℂ) (s : Finset ℕ) :
    MemLp (fun ω => ∑ n ∈ s, b n * W ω ^ n) 2 P :=
  memLp_finset_sum s fun n _ => (hW.mom.memLp_pow n).const_mul (b n)

/-- `E|∑_{n∈s} b_n W^n|² = ∑_{n∈s} |b_n|² ν_n`. -/
theorem integral_norm_sq_sum (hW : OrthoMoments W P ν) (b : ℕ → ℂ) (s : Finset ℕ) :
    ∫ ω, ‖∑ n ∈ s, b n * W ω ^ n‖ ^ 2 ∂P = ∑ n ∈ s, ‖b n‖ ^ 2 * ν n := by
  have hc : ∀ ω, ((‖∑ n ∈ s, b n * W ω ^ n‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ s, ∑ q ∈ s, (b p * conj (b q)) * (W ω ^ p * conj (W ω) ^ q) := by
    intro ω
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    simp only [map_mul, map_pow]; ring
  have hint : ∀ p q, Integrable (fun ω => (b p * conj (b q)) * (W ω ^ p * conj (W ω) ^ q)) P :=
    fun p q => (hW.integrable_pow_mul_conj_pow p q).const_mul _
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hc]
  rw [integral_finset_sum _ fun p _ => integrable_finset_sum _ fun q _ => hint p q]
  simp_rw [integral_finset_sum _ fun q _ => hint _ q, integral_const_mul]
  have : ∀ p q, ∫ ω, W ω ^ p * conj (W ω) ^ q ∂P = if p = q then (ν p : ℂ) else 0 :=
    fun p q => hW.orth p q
  simp_rw [this, mul_ite, mul_zero, sum_ite_eq]
  push_cast
  refine sum_congr rfl fun p hp => ?_
  rw [if_pos hp, Complex.mul_conj']

end OrthoMoments

end Barycenter

namespace Barycenter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma continuous_psum (b : ℕ → ℂ) (N : ℕ) : Continuous (psum b N) := by
  unfold psum; fun_prop

lemma measurable_of_hasSum {g : ℂ → ℂ} {b : ℕ → ℂ}
    (hg : ∀ z, HasSum (fun n => b n * z ^ n) (g z)) : Measurable g :=
  measurable_of_tendsto_metrizable (f := fun M => psum b M)
    (fun M => (continuous_psum b M).measurable)
    (tendsto_pi_nhds.2 fun z => (hg z).tendsto_sum_nat)

lemma psum_sub_psum (b : ℕ → ℂ) {N M : ℕ} (h : N ≤ M) (z : ℂ) :
    psum b M z - psum b N z = ∑ n ∈ Ico N M, b n * z ^ n := by
  unfold psum
  rw [← sum_range_add_sum_Ico _ h, add_sub_cancel_left]

namespace OrthoMoments

variable {W : Ω → ℂ} {ν : ℕ → ℝ}

/-- The `L²` tail estimate: `E|g(W) - ∑_{n<N} b_n W^n|² ≤ ∑_{n ≥ N} |b_n|² ν_n`, obtained from the
orthogonality of the monomials and Fatou's lemma. -/
theorem tail_bound (hW : OrthoMoments W P ν) (hν : ∀ n, 0 ≤ ν n) {g : ℂ → ℂ} {b : ℕ → ℂ}
    (hg : ∀ z, HasSum (fun n => b n * z ^ n) (g z)) (hs : Summable fun n => ‖b n‖ ^ 2 * ν n)
    (N : ℕ) :
    MemLp (fun ω => g (W ω) - psum b N (W ω)) 2 P ∧
      ∫ ω, ‖g (W ω) - psum b N (W ω)‖ ^ 2 ∂P ≤
        (∑' n, ‖b n‖ ^ 2 * ν n) - ∑ n ∈ range N, ‖b n‖ ^ 2 * ν n := by
  set T := (∑' n, ‖b n‖ ^ 2 * ν n) - ∑ n ∈ range N, ‖b n‖ ^ 2 * ν n with hT
  have hnn : ∀ n, 0 ≤ ‖b n‖ ^ 2 * ν n := fun n => mul_nonneg (by positivity) (hν n)
  have hmeas : Measurable fun ω => g (W ω) - psum b N (W ω) :=
    ((measurable_of_hasSum hg).comp hW.meas).sub ((continuous_psum b N).measurable.comp hW.meas)
  -- the approximating differences
  set D : ℕ → Ω → ℂ := fun M ω => psum b M (W ω) - psum b N (W ω) with hD
  have hDmem : ∀ M, MemLp (D M) 2 P := fun M =>
    (hW.memLp_psum b (range M)).sub (hW.memLp_psum b (range N))
  have hDint : ∀ M, N ≤ M → ∫ ω, ‖D M ω‖ ^ 2 ∂P ≤ T := by
    intro M hM
    have : ∀ ω, D M ω = ∑ n ∈ Ico N M, b n * W ω ^ n := fun ω => psum_sub_psum b hM (W ω)
    simp_rw [this, hW.integral_norm_sq_sum]
    have h1 := hs.sum_le_tsum (range M) (fun n _ => hnn n)
    rw [← sum_range_add_sum_Ico _ hM] at h1
    linarith
  have hpt : ∀ ω, Tendsto (fun M => ENNReal.ofReal (‖D M ω‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (‖g (W ω) - psum b N (W ω)‖ ^ 2))) := by
    intro ω
    have h1 : Tendsto (fun M => D M ω) atTop (𝓝 (g (W ω) - psum b N (W ω))) :=
      ((hg (W ω)).tendsto_sum_nat).sub_const _
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_norm.tendsto _).comp h1 |>.pow 2)
  have hlint : ∫⁻ ω, ENNReal.ofReal (‖g (W ω) - psum b N (W ω)‖ ^ 2) ∂P ≤ ENNReal.ofReal T := by
    calc ∫⁻ ω, ENNReal.ofReal (‖g (W ω) - psum b N (W ω)‖ ^ 2) ∂P
        = ∫⁻ ω, liminf (fun M => ENNReal.ofReal (‖D M ω‖ ^ 2)) atTop ∂P := by
          congr 1; ext ω; exact ((hpt ω).liminf_eq).symm
      _ ≤ liminf (fun M => ∫⁻ ω, ENNReal.ofReal (‖D M ω‖ ^ 2) ∂P) atTop :=
          lintegral_liminf_le' fun M => ((hDmem M).1.norm.pow 2).aemeasurable.ennreal_ofReal
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal T) atTop := by
          refine liminf_le_liminf ?_
          filter_upwards [eventually_ge_atTop N] with M hM
          rw [← ofReal_integral_eq_lintegral_ofReal
            ((memLp_two_iff_integrable_sq_norm (hDmem M).1).1 (hDmem M))
            (Eventually.of_forall fun _ => by positivity)]
          exact ENNReal.ofReal_le_ofReal (hDint M hM)
      _ = ENNReal.ofReal T := liminf_const _
  have hint : Integrable (fun ω => ‖g (W ω) - psum b N (W ω)‖ ^ 2) P := by
    refine ⟨(hmeas.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => by positivity)]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2 hint, ?_⟩
  have hT0 : 0 ≤ T := by
    have := hs.sum_le_tsum (range N) (fun n _ => hnn n); linarith
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => by positivity)
    (hmeas.norm.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hT0 hlint

lemma tendsto_tail {b : ℕ → ℂ} (hs : Summable fun n => ‖b n‖ ^ 2 * ν n) :
    Tendsto (fun N => (∑' n, ‖b n‖ ^ 2 * ν n) - ∑ n ∈ range N, ‖b n‖ ^ 2 * ν n) atTop (𝓝 0) := by
  have := (hs.hasSum.tendsto_sum_nat).const_sub (∑' n, ‖b n‖ ^ 2 * ν n)
  simpa using this

/-- `g(W) ∈ L²` and the Taylor partial sums converge to it in `L²`. -/
theorem memLp_and_tendsto (hW : OrthoMoments W P ν) (hν : ∀ n, 0 ≤ ν n) {g : ℂ → ℂ} {b : ℕ → ℂ}
    (hg : ∀ z, HasSum (fun n => b n * z ^ n) (g z)) (hs : Summable fun n => ‖b n‖ ^ 2 * ν n) :
    MemLp (fun ω => g (W ω)) 2 P ∧
      Tendsto (fun N => ∫ ω, ‖g (W ω) - psum b N (W ω)‖ ^ 2 ∂P) atTop (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · have h := (hW.tail_bound hν hg hs 0).1
    have h2 := hW.memLp_psum b (range 0)
    convert h.add h2 using 1
    ext ω; simp [psum]
  · refine squeeze_zero (fun N => integral_nonneg fun _ => by positivity)
      (fun N => (hW.tail_bound hν hg hs N).2) (tendsto_tail hs)

/-- Parseval-type identity: `E|g(W)|² = ∑ |b_n|² ν_n`. -/
theorem integral_norm_sq_comp (hW : OrthoMoments W P ν) (hν : ∀ n, 0 ≤ ν n) {g : ℂ → ℂ}
    {b : ℕ → ℂ} (hg : ∀ z, HasSum (fun n => b n * z ^ n) (g z))
    (hs : Summable fun n => ‖b n‖ ^ 2 * ν n) :
    ∫ ω, ‖g (W ω)‖ ^ 2 ∂P = ∑' n, ‖b n‖ ^ 2 * ν n := by
  obtain ⟨hmem, hconv⟩ := hW.memLp_and_tendsto hν hg hs
  have h := tendsto_integral_mul_conj hmem hmem (fun N => hW.memLp_psum b (range N))
    (fun N => hW.memLp_psum b (range N)) hconv hconv
  have h2 : ∀ N, ∫ ω, psum b N (W ω) * conj (psum b N (W ω)) ∂P
      = ((∑ n ∈ range N, ‖b n‖ ^ 2 * ν n : ℝ) : ℂ) := by
    intro N
    rw [← hW.integral_norm_sq_sum b (range N), ← integral_complex_ofReal]
    congr 1; ext ω; rw [Complex.mul_conj', psum, Complex.ofReal_pow]
  replace h := Tendsto.congr (fun N => h2 N) h
  have h3 : ∫ ω, g (W ω) * conj (g (W ω)) ∂P = ((∫ ω, ‖g (W ω)‖ ^ 2 ∂P : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; congr 1; ext ω; rw [Complex.mul_conj', Complex.ofReal_pow]
  rw [h3] at h
  have h4 := Complex.continuous_ofReal.tendsto _ |>.comp (hs.hasSum.tendsto_sum_nat)
  exact_mod_cast tendsto_nhds_unique h h4

end OrthoMoments

end Barycenter

-- ============================================================================
-- Source part: Bary8.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Part 8. Cross inner products of analytic images -/

lemma AllMoments.integrable_pow_mul_conj_pow₂ {U V : Ω → ℂ} (hU : AllMoments U P)
    (hV : AllMoments V P) (p q : ℕ) : Integrable (fun ω => U ω ^ p * conj (V ω) ^ q) P := by
  refine ((hU.integrable_norm_pow (2 * p)).add (hV.integrable_norm_pow (2 * q))).mono' ?_
    (Eventually.of_forall fun ω => ?_)
  · exact (hU.aestronglyMeasurable.pow p).mul
      ((Complex.continuous_conj.comp_aestronglyMeasurable hV.aestronglyMeasurable).pow q)
  · rw [norm_mul, norm_pow, norm_pow, Complex.norm_conj]
    set x := ‖U ω‖; set y := ‖V ω‖
    have hx : 0 ≤ x ^ p := by positivity
    have hy : 0 ≤ y ^ q := by positivity
    have : x ^ p * y ^ q ≤ (x ^ p) ^ 2 + (y ^ q) ^ 2 := by nlinarith [sq_nonneg (x ^ p - y ^ q)]
    calc x ^ p * y ^ q ≤ (x ^ p) ^ 2 + (y ^ q) ^ 2 := this
      _ = x ^ (2 * p) + y ^ (2 * q) := by ring

/-- Inner product of two analytic images `E[g(U) \overline{g(V)}]` when the cross moments
are diagonal: `E[U^p \bar V^q] = δ_{pq} λ_p`. -/
theorem integral_comp_mul_conj_comp {U V : Ω → ℂ} {νU νV lam : ℕ → ℝ}
    (hU : OrthoMoments U P νU) (hV : OrthoMoments V P νV) (hνU : ∀ n, 0 ≤ νU n)
    (hνV : ∀ n, 0 ≤ νV n) {g : ℂ → ℂ} {b : ℕ → ℂ}
    (hg : ∀ z, HasSum (fun n => b n * z ^ n) (g z))
    (hsU : Summable fun n => ‖b n‖ ^ 2 * νU n) (hsV : Summable fun n => ‖b n‖ ^ 2 * νV n)
    (hcross : ∀ p q, ∫ ω, U ω ^ p * conj (V ω) ^ q ∂P = if p = q then (lam p : ℂ) else 0)
    (hsl : Summable fun n => ‖b n‖ ^ 2 * lam n) :
    ∫ ω, g (U ω) * conj (g (V ω)) ∂P = ((∑' n, ‖b n‖ ^ 2 * lam n : ℝ) : ℂ) := by
  obtain ⟨hmU, hcU⟩ := hU.memLp_and_tendsto hνU hg hsU
  obtain ⟨hmV, hcV⟩ := hV.memLp_and_tendsto hνV hg hsV
  have h := tendsto_integral_mul_conj hmU hmV (fun N => hU.memLp_psum b (range N))
    (fun N => hV.memLp_psum b (range N)) hcU hcV
  have h2 : ∀ N, ∫ ω, (∑ n ∈ range N, b n * U ω ^ n) * conj (∑ n ∈ range N, b n * V ω ^ n) ∂P
      = ((∑ n ∈ range N, ‖b n‖ ^ 2 * lam n : ℝ) : ℂ) := by
    intro N
    have hexp : ∀ ω, (∑ n ∈ range N, b n * U ω ^ n) * conj (∑ n ∈ range N, b n * V ω ^ n)
        = ∑ p ∈ range N, ∑ q ∈ range N, (b p * conj (b q)) * (U ω ^ p * conj (V ω) ^ q) := by
      intro ω
      rw [map_sum, sum_mul_sum]
      refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
      simp only [map_mul, map_pow]; ring
    have hint : ∀ p q, Integrable (fun ω => (b p * conj (b q)) * (U ω ^ p * conj (V ω) ^ q)) P :=
      fun p q => (hU.mom.integrable_pow_mul_conj_pow₂ hV.mom p q).const_mul _
    simp_rw [hexp]
    rw [integral_finset_sum _ fun p _ => integrable_finset_sum _ fun q _ => hint p q]
    simp_rw [integral_finset_sum _ fun q _ => hint _ q, integral_const_mul, hcross, mul_ite,
      mul_zero, sum_ite_eq]
    push_cast
    refine sum_congr rfl fun p hp => ?_
    rw [if_pos hp, Complex.mul_conj']
  replace h := Tendsto.congr (fun N => h2 N) h
  have h4 := Complex.continuous_ofReal.tendsto _ |>.comp (hsl.hasSum.tendsto_sum_nat)
  exact tendsto_nhds_unique h h4

/-- Mean of an analytic image: if `b₀ = 0` then `E g(U) = 0`. -/
theorem integral_comp_eq_zero {U : Ω → ℂ} {νU : ℕ → ℝ} (hU : OrthoMoments U P νU)
    (hνU : ∀ n, 0 ≤ νU n) {g : ℂ → ℂ} {b : ℕ → ℂ}
    (hg : ∀ z, HasSum (fun n => b n * z ^ n) (g z)) (hsU : Summable fun n => ‖b n‖ ^ 2 * νU n)
    (hb0 : b 0 = 0) (hmean : ∀ p, 1 ≤ p → ∫ ω, U ω ^ p ∂P = 0) :
    ∫ ω, g (U ω) ∂P = 0 := by
  obtain ⟨hmU, hcU⟩ := hU.memLp_and_tendsto hνU hg hsU
  have h1 : MemLp (fun _ : Ω => (1 : ℂ)) 2 P := memLp_const 1
  have h := tendsto_integral_mul_conj hmU h1 (fun N => hU.memLp_psum b (range N))
    (fun _ => h1) hcU (by simp)
  simp only [map_one, mul_one] at h
  have h2 : ∀ N, ∫ ω, ∑ n ∈ range N, b n * U ω ^ n ∂P = 0 := by
    intro N
    rw [integral_finset_sum _ fun n _ => (hU.mom.integrable_pow n).const_mul _]
    refine sum_eq_zero fun n _ => ?_
    rw [integral_const_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hb0]
    · rw [hmean n hn, mul_zero]
  replace h := Tendsto.congr (fun N => h2 N) h
  exact tendsto_nhds_unique h tendsto_const_nhds

end Barycenter

-- ============================================================================
-- Source part: Bary9.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Part 9. Analytic maps: exact means, variances and covariance (Proposition 4.1) -/

/-- The center of the image cloud `A_m(f) = m^{-1} ∑_{j<m} f(Z_j)` with `Z_j = a + X_j`. -/
noncomputable def Aimg (f : ℂ → ℂ) (a : ℂ) (X : ℕ → Ω → ℂ) (m : ℕ) (ω : Ω) : ℂ :=
  (m : ℂ)⁻¹ * ∑ j ∈ range m, f (a + X j ω)

/-- The image of the center `B_m(f) = f(ω_m)` with `ω_m = a + S_m`. -/
noncomputable def Bimg (f : ℂ → ℂ) (a : ℂ) (X : ℕ → Ω → ℂ) (m : ℕ) (ω : Ω) : ℂ :=
  f (a + Scen X m ω)

/-- The Taylor energy `V_f = ∑_{n ≥ 1} |c_n|² μ_n`. -/
noncomputable def Vf (c : ℕ → ℂ) (μ : ℕ → ℝ) : ℝ := ∑' n, ‖c (n + 1)‖ ^ 2 * μ (n + 1)

lemma kappa_le_one {m : ℕ} (hm : 1 ≤ m) (n : ℕ) : kappa m n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [kappa, qmom, Qsum_zero_right (fun _ => (1 : ℝ)) rfl]
  · refine (kappa_le_inv hm hn).trans ?_
    rw [div_le_one (by positivity)]; exact_mod_cast hm

/-! ### Taylor data -/

/-- Coefficients of `g(z) = f(a+z) - f(a)`. -/
noncomputable def gcoef (c : ℕ → ℂ) : ℕ → ℂ := Function.update c 0 0

lemma gcoef_zero (c : ℕ → ℂ) : gcoef c 0 = 0 := by simp [gcoef]

lemma gcoef_succ (c : ℕ → ℂ) (n : ℕ) : gcoef c (n + 1) = c (n + 1) := by simp [gcoef]

lemma coeff_zero_eq {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) : c 0 = f a := by
  have h := hf 0
  simp only [add_zero] at h
  have h2 : HasSum (fun n => c n * (0 : ℂ) ^ n) (c 0) := by
    convert hasSum_ite_eq 0 (c 0) using 1
    ext n; rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [zero_pow (by omega), mul_zero, if_neg (by omega)]
  exact h2.unique h

lemma hasSum_g {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) (z : ℂ) :
    HasSum (fun n => gcoef c n * z ^ n) (f (a + z) - f a) := by
  have h := (hf z).update 0 0
  have e : Function.update (fun n => c n * z ^ n) 0 0 = fun n => gcoef c n * z ^ n := by
    ext n; by_cases hn : n = 0
    · subst hn; simp [gcoef]
    · simp [gcoef, hn]
  rw [e] at h
  convert h using 1
  simp [coeff_zero_eq hf]; ring

lemma summable_gcoef {c : ℕ → ℂ} {ν : ℕ → ℝ} (hν : ∀ n, 0 ≤ ν n)
    (hs : Summable fun n => ‖c n‖ ^ 2 * ν n) : Summable fun n => ‖gcoef c n‖ ^ 2 * ν n := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (hν n)) (fun n => ?_) hs
  by_cases hn : n = 0
  · subst hn; simp [gcoef]; exact mul_nonneg (by positivity) (hν 0)
  · simp [gcoef, hn]

lemma tsum_gcoef {c : ℕ → ℂ} {ν : ℕ → ℝ} (hs : Summable fun n => ‖gcoef c n‖ ^ 2 * ν n) :
    ∑' n, ‖gcoef c n‖ ^ 2 * ν n = ∑' n, ‖c (n + 1)‖ ^ 2 * ν (n + 1) := by
  rw [hs.tsum_eq_zero_add]
  simp [gcoef_zero, gcoef_succ]

lemma summable_le {c : ℕ → ℂ} {ν ν' : ℕ → ℝ} (h0 : ∀ n, 0 ≤ ν' n) (hle : ∀ n, ν' n ≤ ν n)
    (hs : Summable fun n => ‖c n‖ ^ 2 * ν n) : Summable fun n => ‖c n‖ ^ 2 * ν' n :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (h0 n))
    (fun n => mul_le_mul_of_nonneg_left (hle n) (by positivity)) hs

namespace RadialSample

variable {X : ℕ → Ω → ℂ}

omit [IsProbabilityMeasure P] in
lemma orthoMoments_X (hX : RadialSample X P) (j : ℕ) :
    OrthoMoments (X j) P (radMom (X 0) P) :=
  ⟨hX.meas j, hX.mom j, fun p q => by rw [(hX.rot j).cmom_eq, hX.radMom_eq j 0]⟩

lemma orthoMoments_S (hX : RadialSample X P) (m : ℕ) :
    OrthoMoments (Scen X m) P (qmom (radMom (X 0) P) m) :=
  ⟨hX.measurable_Scen m, hX.allMoments_Scen m, hX.cmom_Scen m⟩

lemma integral_Scen_pow (hX : RadialSample X P) (m : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    ∫ ω, Scen X m ω ^ p ∂P = 0 := by
  have := hX.cmom_Scen m p 0
  rw [if_neg (by omega)] at this
  simpa [cmom] using this

lemma cross_X_X (hX : RadialSample X P) {j k : ℕ} (hjk : j ≠ k) (p q : ℕ) :
    ∫ ω, X j ω ^ p * conj (X k ω) ^ q ∂P =
      if p = q then (((if p = 0 then 1 else 0 : ℝ)) : ℂ) else 0 := by
  have hi : IndepFun (fun ω => X j ω ^ p) (fun ω => conj (X k ω) ^ q) P :=
    (hX.indep.indepFun hjk).comp (φ := fun z : ℂ => z ^ p) (ψ := fun z : ℂ => conj z ^ q)
      (by fun_prop) (by fun_prop)
  rw [hi.integral_fun_mul_eq_mul_integral ((hX.mom j).integrable_pow p).1
    (by simpa using ((hX.mom k).integrable_pow_mul_conj_pow 0 q).1)]
  have hq : ∫ ω, conj (X k ω) ^ q ∂P = conj (∫ ω, X k ω ^ q ∂P) := by
    rw [← integral_conj]; simp
  rw [hq]
  have hpow : ∀ i r, ∫ ω, X i ω ^ r ∂P = if r = 0 then 1 else 0 := by
    intro i r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · rw [hX.integral_pow_eq_zero i hr, if_neg (by omega)]
  rw [hpow, hpow]
  by_cases hp : p = 0 <;> by_cases hq' : q = 0
  · subst hp; subst hq'; simp
  · subst hp; simp [hq', Ne.symm hq']
  · subst hq'; simp [hp]
  · simp [hp, hq']

/-- Per-dart mixed moment: `E[X_j^p \bar S_m^q] = δ_{pq} μ_p m^{-p}` for `j < m`. -/
theorem cross_X_S (hX : RadialSample X P) {m j : ℕ} (hjm : j < m) (p q : ℕ) :
    ∫ ω, X j ω ^ p * conj (Scen X m ω) ^ q ∂P =
      if p = q then ((radMom (X 0) P p / (m : ℝ) ^ p : ℝ) : ℂ) else 0 := by
  classical
  have hjm' : j ∈ range m := mem_range.2 hjm
  have hj : ∫ ω, X j ω ^ p * conj (∑ i ∈ range m, X i ω) ^ q ∂P =
      if p = q then (radMom (X 0) P p : ℂ) else 0 := by
    have hsplit : ∀ ω, ∑ i ∈ range m, X i ω = X j ω + ∑ i ∈ (range m).erase j, X i ω := by
      intro ω; exact (add_sum_erase (range m) (fun i => X i ω) hjm').symm
    simp_rw [hsplit]
    have hind : IndepFun (X j) (fun ω => ∑ i ∈ (range m).erase j, X i ω) P := by
      have := (hX.indep.indepFun_finset_sum_of_notMem hX.meas (notMem_erase j (range m))).symm
      convert this using 1
      ext ω; simp [Finset.sum_apply]
    rw [cross_add_of_indep (hX.mom j) (AllMoments.finset_sum _ fun i _ => hX.mom i) hind
      (α := radMom (X 0) P) (fun a b => by rw [(hX.rot j).cmom_eq, hX.radMom_eq j 0])
      (fun b => by
        rw [hX.cmom_sum 0 _ 0 b]
        by_cases hb : b = 0
        · subst hb; simp [Qsum_zero_right _ (radMom_zero (X := X) 0)]
        · simp [Ne.symm hb, hb])]
  have hexp : ∀ ω, X j ω ^ p * conj (Scen X m ω) ^ q =
      ((m : ℂ)⁻¹) ^ q * (X j ω ^ p * conj (∑ i ∈ range m, X i ω) ^ q) := by
    intro ω
    rw [Scen, map_mul, map_inv₀, Complex.conj_natCast, mul_pow]; ring
  simp_rw [hexp]
  rw [integral_const_mul, hj]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  split_ifs with hpq
  · subst hpq; push_cast; rw [inv_pow]; field_simp
  · simp

/-! ### Proposition 4.1 -/

variable {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

/-- **Proposition 4.1, `V_f` as a variance.** `V_f = E|f(a+X) - f(a)|²`. -/
theorem Vf_eq_integral (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    Vf c (radMom (X 0) P) = ∫ ω, ‖f (a + X 0 ω) - f a‖ ^ 2 ∂P := by
  have hν := radMom_nonneg (X := X) (P := P) 0
  have hsb := summable_gcoef hν hs
  rw [(hX.orthoMoments_X 0).integral_norm_sq_comp hν (hasSum_g hf) hsb, tsum_gcoef hsb, Vf]

/-- `f(a+X) ∈ L²`. -/
theorem memLp_comp_X (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) (j : ℕ) :
    MemLp (fun ω => f (a + X j ω) - f a) 2 P :=
  ((hX.orthoMoments_X j).memLp_and_tendsto (radMom_nonneg (X := X) 0) (hasSum_g hf)
    (summable_gcoef (radMom_nonneg (X := X) 0) hs)).1

lemma summable_q (hX : RadialSample X P) {m : ℕ} (hm : 1 ≤ m)
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    Summable fun n => ‖c n‖ ^ 2 * qmom (radMom (X 0) P) m n :=
  summable_le (qmom_nonneg _ (radMom_nonneg (X := X) 0) m)
    (fun n => (hX.qmom_le m n).trans (by
      have := kappa_le_one hm n; have := radMom_nonneg (X := X) (P := P) 0 n; nlinarith)) hs

theorem memLp_comp_S (hX : RadialSample X P) {m : ℕ} (hm : 1 ≤ m)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    MemLp (fun ω => f (a + Scen X m ω) - f a) 2 P :=
  ((hX.orthoMoments_S m).memLp_and_tendsto (qmom_nonneg _ (radMom_nonneg (X := X) 0) m)
    (hasSum_g hf) (summable_gcoef (qmom_nonneg _ (radMom_nonneg (X := X) 0) m)
      (hX.summable_q hm hs))).1

omit [MeasurableSpace Ω] in
lemma Aimg_sub (hm : 1 ≤ m) (ω : Ω) :
    Aimg f a X m ω - f a = (m : ℂ)⁻¹ * ∑ j ∈ range m, (f (a + X j ω) - f a) := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [Aimg, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_sub]
  field_simp

/-- **Proposition 4.1 (means).** `E A_m(f) = f(a)`. -/
theorem integral_Aimg (hX : RadialSample X P) {m : ℕ} (hm : 1 ≤ m)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    ∫ ω, Aimg f a X m ω ∂P = f a := by
  have hν := radMom_nonneg (X := X) (P := P) 0
  have hzero : ∀ j, ∫ ω, (f (a + X j ω) - f a) ∂P = 0 := fun j =>
    integral_comp_eq_zero (hX.orthoMoments_X j) hν (g := fun z => f (a + z) - f a) (hasSum_g hf)
      (summable_gcoef hν hs) (gcoef_zero c) (fun p hp => hX.integral_pow_eq_zero j hp)
  have hint : ∀ j, Integrable (fun ω => f (a + X j ω) - f a) P := fun j =>
    (hX.memLp_comp_X hf hs j).integrable one_le_two
  have e : ∀ ω, Aimg f a X m ω = f a + (m : ℂ)⁻¹ * ∑ j ∈ range m, (f (a + X j ω) - f a) := by
    intro ω; rw [← Aimg_sub hm]; ring
  simp_rw [e]
  rw [integral_add (integrable_const _) ((integrable_finset_sum _ fun j _ => hint j).const_mul _),
    integral_const_mul, integral_finset_sum _ fun j _ => hint j]
  simp [hzero]

/-- **Proposition 4.1 (means).** `E B_m(f) = f(a)`. -/
theorem integral_Bimg (hX : RadialSample X P) {m : ℕ} (hm : 1 ≤ m)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    ∫ ω, Bimg f a X m ω ∂P = f a := by
  have hν := qmom_nonneg _ (radMom_nonneg (X := X) (P := P) 0) m
  have hzero : ∫ ω, (f (a + Scen X m ω) - f a) ∂P = 0 :=
    integral_comp_eq_zero (hX.orthoMoments_S m) hν (g := fun z => f (a + z) - f a) (hasSum_g hf)
      (summable_gcoef hν (hX.summable_q hm hs)) (gcoef_zero c)
      (fun p hp => hX.integral_Scen_pow m hp)
  have hint := (hX.memLp_comp_S hm hf hs).integrable one_le_two
  have e : ∀ ω, Bimg f a X m ω = f a + (f (a + Scen X m ω) - f a) := by
    intro ω; rw [Bimg]; ring
  simp_rw [e]
  rw [integral_add (integrable_const _) hint, hzero]
  simp

/-- **Proposition 4.1, (4.2).** `E|A_m(f) - f(a)|² = V_f / m`. -/
theorem integral_norm_sq_Aimg (hX : RadialSample X P) {m : ℕ} (hm : 1 ≤ m)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    ∫ ω, ‖Aimg f a X m ω - f a‖ ^ 2 ∂P = Vf c (radMom (X 0) P) / m := by
  set μ := radMom (X 0) P
  have hν := radMom_nonneg (X := X) (P := P) 0
  have hsb := summable_gcoef hν hs
  set G : ℕ → Ω → ℂ := fun j ω => f (a + X j ω) - f a
  have hG : ∀ j k, ∫ ω, G j ω * conj (G k ω) ∂P = if j = k then (Vf c μ : ℂ) else 0 := by
    intro j k
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl, integral_comp_mul_conj_comp (hX.orthoMoments_X j) (hX.orthoMoments_X j) hν hν
        (g := fun z => f (a + z) - f a) (hasSum_g hf) hsb hsb (lam := μ)
        (fun p q => (hX.orthoMoments_X j).orth p q) hsb, tsum_gcoef hsb]
      rfl
    · rw [if_neg hjk, integral_comp_mul_conj_comp (hX.orthoMoments_X j) (hX.orthoMoments_X k) hν hν
        (g := fun z => f (a + z) - f a) (hasSum_g hf) hsb hsb
        (lam := fun p => if p = 0 then 1 else 0) (hX.cross_X_X hjk)
        (summable_of_ne_finset_zero (s := {0}) (fun n hn => by simp at hn; simp [hn]))]
      rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
      simp [gcoef_zero]
  have hmem : ∀ j, MemLp (G j) 2 P := fun j => hX.memLp_comp_X hf hs j
  have hc : ∀ ω, ((‖Aimg f a X m ω - f a‖ ^ 2 : ℝ) : ℂ) =
      ((m : ℂ)⁻¹) ^ 2 * ∑ j ∈ range m, ∑ k ∈ range m, G j ω * conj (G k ω) := by
    intro ω
    rw [Complex.ofReal_pow, ← Complex.mul_conj', Aimg_sub hm, map_mul, map_sum, map_inv₀,
      Complex.conj_natCast, mul_mul_mul_comm, sum_mul_sum, sq]
  have hint : ∀ j k, Integrable (fun ω => G j ω * conj (G k ω)) P := fun j k =>
    (hmem j).integrable_mul (hmem k).star (p := 2) (q := 2)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hc]
  rw [integral_const_mul, integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => hint j k]
  simp_rw [integral_finset_sum _ fun k _ => hint _ k, hG, sum_ite_eq]
  rw [sum_congr rfl (fun j hj => if_pos hj)]
  simp only [sum_const, card_range, nsmul_eq_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  push_cast
  field_simp

/-- **Proposition 4.1, (4.3).** `E|B_m(f) - f(a)|² = ∑_{n≥1} |c_n|² q_{m,n}`. -/
theorem integral_norm_sq_Bimg (hX : RadialSample X P) {m : ℕ} (hm : 1 ≤ m)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    ∫ ω, ‖Bimg f a X m ω - f a‖ ^ 2 ∂P =
      ∑' n, ‖c (n + 1)‖ ^ 2 * qmom (radMom (X 0) P) m (n + 1) := by
  have hν := qmom_nonneg _ (radMom_nonneg (X := X) (P := P) 0) m
  have hsb := summable_gcoef hν (hX.summable_q hm hs)
  rw [← tsum_gcoef hsb]
  exact (hX.orthoMoments_S m).integral_norm_sq_comp hν (g := fun z => f (a + z) - f a)
    (hasSum_g hf) hsb

/-- **Proposition 4.1, (4.4).** `E[(A_m(f) - f(a)) \overline{(B_m(f) - f(a))}] =
∑_{n≥1} |c_n|² μ_n / m^n`. -/
theorem integral_cov_AB (hX : RadialSample X P) {m : ℕ} (hm : 1 ≤ m)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    ∫ ω, (Aimg f a X m ω - f a) * conj (Bimg f a X m ω - f a) ∂P =
      ((∑' n, ‖c (n + 1)‖ ^ 2 * (radMom (X 0) P (n + 1) / (m : ℝ) ^ (n + 1)) : ℝ) : ℂ) := by
  set μ := radMom (X 0) P
  have hν := radMom_nonneg (X := X) (P := P) 0
  have hνq := qmom_nonneg _ hν m
  have hsb := summable_gcoef hν hs
  have hsq := summable_gcoef hνq (hX.summable_q hm hs)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlam0 : ∀ n, 0 ≤ μ n / (m : ℝ) ^ n := fun n => div_nonneg (hν n) (by positivity)
  have hlamle : ∀ n, μ n / (m : ℝ) ^ n ≤ μ n := fun n =>
    div_le_self (hν n) (one_le_pow₀ hm1)
  have hsl := summable_le hlam0 hlamle hsb
  set G : ℕ → Ω → ℂ := fun j ω => f (a + X j ω) - f a
  have hGS : ∀ j ∈ range m, ∫ ω, G j ω * conj (f (a + Scen X m ω) - f a) ∂P =
      ((∑' n, ‖c (n + 1)‖ ^ 2 * (μ (n + 1) / (m : ℝ) ^ (n + 1)) : ℝ) : ℂ) := by
    intro j hj
    rw [integral_comp_mul_conj_comp (hX.orthoMoments_X j) (hX.orthoMoments_S m) hν hνq
      (g := fun z => f (a + z) - f a) (hasSum_g hf) hsb hsq
      (lam := fun n => μ n / (m : ℝ) ^ n) (hX.cross_X_S (mem_range.1 hj)) hsl, tsum_gcoef hsl]
  have hmem : ∀ j, MemLp (G j) 2 P := fun j => hX.memLp_comp_X hf hs j
  have hmemS := hX.memLp_comp_S hm hf hs
  have hexp : ∀ ω, (Aimg f a X m ω - f a) * conj (Bimg f a X m ω - f a) =
      (m : ℂ)⁻¹ * ∑ j ∈ range m, G j ω * conj (f (a + Scen X m ω) - f a) := by
    intro ω; rw [Aimg_sub hm, Bimg, mul_assoc, sum_mul]
  have hint : ∀ j, Integrable (fun ω => G j ω * conj (f (a + Scen X m ω) - f a)) P := fun j =>
    (hmem j).integrable_mul hmemS.star (p := 2) (q := 2)
  simp_rw [hexp]
  rw [integral_const_mul, integral_finset_sum _ fun j _ => hint j, sum_congr rfl hGS]
  simp only [sum_const, card_range, nsmul_eq_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  field_simp

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary10.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Part 10. The sharp comparison of the two centers (Theorem 4.2 = Theorem A) -/

lemma kappa_antitone {m : ℕ} (hm : 2 ≤ m) : Antitone (kappa m) := (kappa_strictAnti hm).antitone

lemma summable_shift {c : ℕ → ℂ} {ν : ℕ → ℝ} (hs : Summable fun n => ‖c n‖ ^ 2 * ν n) :
    Summable fun n => ‖c (n + 1)‖ ^ 2 * ν (n + 1) :=
  (summable_nat_add_iff 1).2 hs

lemma tsum_eq_zero_iff_of_nonneg' {F : ℕ → ℝ} (h0 : ∀ n, 0 ≤ F n) (hs : Summable F) :
    ∑' n, F n = 0 ↔ ∀ n, F n = 0 := by
  constructor
  · intro h n
    have := (hasSum_zero_iff_of_nonneg h0).1 (h ▸ hs.hasSum)
    exact congr_fun this n
  · intro h; simp [h]

namespace RadialSample

variable {X : ℕ → Ω → ℂ} {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

/-- `μ_n ≥ μ₁^n > 0` when `μ₁ > 0`. -/
lemma radMom_pos (hX : RadialSample X P) (hμ1 : 0 < radMom (X 0) P 1) {n : ℕ} (hn : 1 ≤ n) :
    0 < radMom (X 0) P n := by
  have h := radMom_le_rpow (hX.mom 0) le_rfl hn
  rcases (radMom_nonneg (X := X) (P := P) 0 n).lt_or_eq with h' | h'
  · exact h'
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← h', Real.zero_rpow (by positivity)] at h
    linarith

/-- Termwise comparison used in Theorem 4.2. -/
lemma term_le (hX : RadialSample X P) {m d : ℕ} (hm : 2 ≤ m)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) (k : ℕ) (hk : 1 ≤ k) :
    ‖c k‖ ^ 2 * qmom (radMom (X 0) P) m k ≤ kappa m d * (‖c k‖ ^ 2 * radMom (X 0) P k) := by
  by_cases hkd : k < d
  · simp [hlow k hk hkd]
  · have h1 := hX.qmom_le m k
    have h2 := kappa_antitone hm (not_lt.1 hkd)
    have hμ := radMom_nonneg (X := X) (P := P) 0 k
    have h3 : radMom (X 0) P k * kappa m k ≤ radMom (X 0) P k * kappa m d :=
      mul_le_mul_of_nonneg_left h2 hμ
    have hc : 0 ≤ ‖c k‖ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h3) hc]

/-- **Theorem 4.2, inequality (4.6).** `E|B_m(f) - f(a)|² ≤ κ_{m,d} V_f` where `d` is the order of
`f - f(a)` at `a`. -/
theorem main_le (hX : RadialSample X P) {m d : ℕ} (hm : 2 ≤ m)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) :
    ∫ ω, ‖Bimg f a X m ω - f a‖ ^ 2 ∂P ≤ kappa m d * Vf c (radMom (X 0) P) := by
  rw [hX.integral_norm_sq_Bimg (by omega) hf hs, Vf, ← tsum_mul_left]
  exact (summable_shift (hX.summable_q (by omega) hs)).tsum_le_tsum
    (fun n => hX.term_le hm hlow (n + 1) (by omega)) ((summable_shift hs).mul_left _)

/-- **Theorem 4.2, the identity in (4.6).** `κ_{m,d} V_f = m κ_{m,d} E|A_m(f) - f(a)|²`. -/
theorem main_eq_A (hX : RadialSample X P) {m : ℕ} (hm : 1 ≤ m) (d : ℕ)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    kappa m d * Vf c (radMom (X 0) P) = m * kappa m d * ∫ ω, ‖Aimg f a X m ω - f a‖ ^ 2 ∂P := by
  rw [hX.integral_norm_sq_Aimg hm hf hs]
  have : (m : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Theorem 4.2, the constant.** `m κ_{m,d} ≤ min {1, d! m^{1-d}}`. -/
theorem main_constant {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) :
    m * kappa m d ≤ 1 ∧ m * kappa m d ≤ (d.factorial : ℝ) / (m : ℝ) ^ (d - 1) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · have := kappa_le_inv hm hd
    rw [le_div_iff₀ hm'] at this; linarith
  · have h := kappa_le_factorial_div hm d
    have e : (m : ℝ) ^ d = m * (m : ℝ) ^ (d - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e] at h
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at h
    linarith

/-- The deficit terms `κ_{m,d} |c_k|² μ_k - |c_k|² q_{m,k}` (indexed by `k = n+1`). -/
lemma deficit_eq (hX : RadialSample X P) {m d : ℕ} (hm : 2 ≤ m)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) :
    (∫ ω, ‖Bimg f a X m ω - f a‖ ^ 2 ∂P = kappa m d * Vf c (radMom (X 0) P)) ↔
      ∀ k, 1 ≤ k → ‖c k‖ ^ 2 * qmom (radMom (X 0) P) m k =
        kappa m d * (‖c k‖ ^ 2 * radMom (X 0) P k) := by
  set F : ℕ → ℝ := fun n => kappa m d * (‖c (n + 1)‖ ^ 2 * radMom (X 0) P (n + 1)) -
    ‖c (n + 1)‖ ^ 2 * qmom (radMom (X 0) P) m (n + 1)
  have hF0 : ∀ n, 0 ≤ F n := fun n => sub_nonneg.2 (hX.term_le hm hlow (n + 1) (by omega))
  have hFs : Summable F :=
    ((summable_shift hs).mul_left _).sub (summable_shift (hX.summable_q (by omega) hs))
  have htsum : ∑' n, F n = kappa m d * Vf c (radMom (X 0) P) -
      ∫ ω, ‖Bimg f a X m ω - f a‖ ^ 2 ∂P := by
    rw [hX.integral_norm_sq_Bimg (by omega) hf hs, Vf, ← tsum_mul_left,
      ← ((summable_shift hs).mul_left _).tsum_sub (summable_shift (hX.summable_q (by omega) hs))]
  constructor
  · intro h k hk
    have := (tsum_eq_zero_iff_of_nonneg' hF0 hFs).1 (by rw [htsum, h, sub_self]) (k - 1)
    simp only [F, Nat.sub_add_cancel hk] at this
    linarith
  · intro h
    have : ∑' n, F n = 0 := (tsum_eq_zero_iff_of_nonneg' hF0 hFs).2 fun n => by
      simp only [F]; rw [h (n + 1) (by omega), sub_self]
    linarith

/-- Strictness for `k > d`. -/
lemma term_lt (hX : RadialSample X P) (hμ1 : 0 < radMom (X 0) P 1) {m d k : ℕ} (hm : 2 ≤ m)
    (hdk : d < k) (hck : c k ≠ 0) :
    ‖c k‖ ^ 2 * qmom (radMom (X 0) P) m k < kappa m d * (‖c k‖ ^ 2 * radMom (X 0) P k) := by
  have h1 := hX.qmom_le m k
  have h2 := kappa_strictAnti hm hdk
  have hμ := hX.radMom_pos hμ1 (n := k) (by omega)
  have hc : 0 < ‖c k‖ ^ 2 := by positivity
  have h3 : radMom (X 0) P k * kappa m k < radMom (X 0) P k * kappa m d :=
    mul_lt_mul_of_pos_left h2 hμ
  nlinarith [mul_lt_mul_of_pos_left (lt_of_le_of_lt h1 h3) hc]

/-- **Theorem 4.2 (i): equality for `d = 1`.** Equality holds iff `f(a+z) = f(a) + c₁ z`. -/
theorem main_eq_iff_one (hX : RadialSample X P) (hμ1 : 0 < radMom (X 0) P 1) {m : ℕ}
    (hm : 2 ≤ m) (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    (∫ ω, ‖Bimg f a X m ω - f a‖ ^ 2 ∂P = kappa m 1 * Vf c (radMom (X 0) P)) ↔
      ∀ n, 2 ≤ n → c n = 0 := by
  rw [hX.deficit_eq hm hf hs (d := 1) (fun n h1 h2 => by omega)]
  constructor
  · intro h n hn
    by_contra hcn
    exact absurd (h n (by omega)) (ne_of_lt (hX.term_lt hμ1 hm (by omega) hcn))
  · intro h k hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have : k = 1 := by omega
      subst this
      rw [qmom_one _ (radMom_zero (X := X) 0) (by omega), kappa_one (by omega)]
      ring
    · simp [h k hk2]

/-- **Theorem 4.2 (ii): equality for `d ≥ 2`.** Equality holds iff `f(a+z) = f(a) + c_d z^d` and
`|X|` is almost surely constant. -/
theorem main_eq_iff_ge_two (hX : RadialSample X P) (hμ1 : 0 < radMom (X 0) P 1) {m d : ℕ}
    (hm : 2 ≤ m) (hd : 2 ≤ d) (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) (hcd : c d ≠ 0) :
    (∫ ω, ‖Bimg f a X m ω - f a‖ ^ 2 ∂P = kappa m d * Vf c (radMom (X 0) P)) ↔
      (∀ n, d < n → c n = 0) ∧ ∃ ρ : ℝ, ∀ᵐ ω ∂P, ‖X 0 ω‖ = ρ := by
  rw [hX.deficit_eq hm hf hs hlow]
  constructor
  · intro h
    refine ⟨fun n hn => ?_, ?_⟩
    · by_contra hcn
      exact absurd (h n (by omega)) (ne_of_lt (hX.term_lt hμ1 hm hn hcn))
    · have hd' := h d (by omega)
      have hc : ‖c d‖ ^ 2 ≠ 0 := by positivity
      have : qmom (radMom (X 0) P) m d = radMom (X 0) P d * kappa m d := by
        have e : ‖c d‖ ^ 2 * qmom (radMom (X 0) P) m d =
            ‖c d‖ ^ 2 * (radMom (X 0) P d * kappa m d) := by rw [hd']; ring
        exact mul_left_cancel₀ hc e
      exact (hX.qmom_eq_iff hm hd).1 this
  · rintro ⟨hhigh, hrho⟩ k hk
    rcases lt_trichotomy k d with hkd | rfl | hkd
    · simp [hlow k hk hkd]
    · rw [(hX.qmom_eq_iff hm hd).2 hrho]; ring
    · simp [hhigh k hkd]

end RadialSample

/-- **Theorem 4.2, optimality of `κ_{m,d}`.** For Steinhaus sampling and `f(z) = z^d` equality
holds in (4.6), so the constant cannot be improved. -/
theorem main_optimal {m d : ℕ} (hm : 2 ≤ m) (hd : 1 ≤ d) :
    ∫ ω, ‖Bimg (fun z => z ^ d) 0 steinhaus m ω - (fun z : ℂ => z ^ d) 0‖ ^ 2 ∂steinhausMeasure
      = kappa m d * Vf (fun n => if n = d then 1 else 0) (radMom (steinhaus 0) steinhausMeasure)
      ∧ Vf (fun n => if n = d then 1 else 0) (radMom (steinhaus 0) steinhausMeasure) = 1 := by
  have hX := steinhaus_radialSample
  have hμ : radMom (steinhaus 0) steinhausMeasure = fun _ => 1 := funext radMom_steinhaus
  have hf : ∀ z : ℂ, HasSum (fun n => (if n = d then (1 : ℂ) else 0) * z ^ n) ((0 + z) ^ d) := by
    intro z
    simp only [zero_add, ite_mul, one_mul, zero_mul]
    convert hasSum_ite_eq d (z ^ d) using 2 with n
    split_ifs with h <;> simp [h]
  have hs : Summable fun n => ‖(if n = d then (1 : ℂ) else 0)‖ ^ 2 * radMom (steinhaus 0)
      steinhausMeasure n :=
    summable_of_ne_finset_zero (s := {d}) (fun n hn => by simp at hn; simp [hn])
  have hV : Vf (fun n => if n = d then 1 else 0) (radMom (steinhaus 0) steinhausMeasure) = 1 := by
    rw [Vf, hμ, tsum_eq_single (d - 1)]
    · simp [Nat.sub_add_cancel hd]
    · intro n hn; have : n + 1 ≠ d := by omega
      simp [this]
  refine ⟨?_, hV⟩
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · have : d = 1 := by omega
    subst this
    exact (hX.main_eq_iff_one (by rw [hμ]; norm_num) hm hf hs).2 fun n hn => by simp; omega
  · refine (hX.main_eq_iff_ge_two (by rw [hμ]; norm_num) hm hd2 hf hs
      (fun n h1 h2 => by simp; omega) (by simp)).2 ⟨fun n hn => by simp; omega, 1, ?_⟩
    exact Eventually.of_forall fun ω => norm_steinhaus 0 ω

end Barycenter

-- ============================================================================
-- Source part: Bary11.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Part 11. Corollaries 4.3 (deficit) and 4.4 (deviation bounds and convergence) -/

/-- `κ_{m,2} - κ_{m,3} = (2m³ - 7m² + 9m - 4)/m⁵`. -/
theorem kappa_two_sub_three {m : ℕ} (hm : 1 ≤ m) :
    kappa m 2 - kappa m 3 = (2 * m ^ 3 - 7 * m ^ 2 + 9 * m - 4) / (m : ℝ) ^ 5 := by
  rw [kappa_two hm, kappa_three hm]
  have : (m : ℝ) ≠ 0 := by positivity
  field_simp; ring

theorem kappa_two_sub_three_pos {m : ℕ} (hm : 2 ≤ m) : 0 < kappa m 2 - kappa m 3 :=
  sub_pos.2 (kappa_strictAnti hm (by norm_num))

namespace RadialSample

variable {X : ℕ → Ω → ℂ} {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

/-- The deficit `D_m(f) = κ_{m,2} V_f - E|B_m(f) - f(a)|²` as a series. -/
lemma deficit_tsum (hX : RadialSample X P) {m : ℕ} (hm : 1 ≤ m) (d : ℕ)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    kappa m d * Vf c (radMom (X 0) P) - ∫ ω, ‖Bimg f a X m ω - f a‖ ^ 2 ∂P =
      ∑' n, (kappa m d * (‖c (n + 1)‖ ^ 2 * radMom (X 0) P (n + 1)) -
        ‖c (n + 1)‖ ^ 2 * qmom (radMom (X 0) P) m (n + 1)) := by
  rw [hX.integral_norm_sq_Bimg hm hf hs, Vf, ← tsum_mul_left,
    ← ((summable_shift hs).mul_left _).tsum_sub (summable_shift (hX.summable_q hm hs))]

/-- **Corollary 4.3 (deficit at a quadratic critical point).** If `m ≥ 2` and `c₁ = 0`, then
`D_m(f) ≥ 2(m-1)/m³ |c₂|² (μ₂ - μ₁²) + (κ_{m,2} - κ_{m,3}) ∑_{n≥3} |c_n|² μ_n`. -/
theorem deficit_ge (hX : RadialSample X P) {m : ℕ} (hm : 2 ≤ m)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) (hc1 : c 1 = 0) :
    2 * (m - 1) / (m : ℝ) ^ 3 * ‖c 2‖ ^ 2 * (radMom (X 0) P 2 - radMom (X 0) P 1 ^ 2)
      + (kappa m 2 - kappa m 3) * ∑' n, ‖c (n + 3)‖ ^ 2 * radMom (X 0) P (n + 3)
      ≤ kappa m 2 * Vf c (radMom (X 0) P) - ∫ ω, ‖Bimg f a X m ω - f a‖ ^ 2 ∂P := by
  set μ := radMom (X 0) P
  rw [hX.deficit_tsum (by omega) 2 hf hs]
  set F : ℕ → ℝ := fun n => kappa m 2 * (‖c (n + 1)‖ ^ 2 * μ (n + 1)) -
    ‖c (n + 1)‖ ^ 2 * qmom μ m (n + 1)
  have hFs : Summable F :=
    ((summable_shift hs).mul_left _).sub (summable_shift (hX.summable_q (by omega) hs))
  rw [hFs.tsum_eq_zero_add, ((summable_nat_add_iff 1).2 hFs).tsum_eq_zero_add]
  have hF0 : F 0 = 0 := by simp [F, hc1]
  have hF1 : F (0 + 1) = 2 * (m - 1) / (m : ℝ) ^ 3 * ‖c 2‖ ^ 2 * (μ 2 - μ 1 ^ 2) := by
    simp only [F, zero_add, Nat.reduceAdd]
    rw [qmom_two _ (radMom_zero (X := X) 0) (by omega), kappa_two (by omega)]
    have : (m : ℝ) ≠ 0 := by positivity
    field_simp; ring
  rw [hF0, hF1, zero_add]
  refine add_le_add le_rfl ?_
  rw [← tsum_mul_left]
  have hs3 : Summable fun n => ‖c (n + 3)‖ ^ 2 * μ (n + 3) := (summable_nat_add_iff 3).2 hs
  refine (hs3.mul_left _).tsum_le_tsum (fun n => ?_) ((summable_nat_add_iff 2).2 hFs)
  show (kappa m 2 - kappa m 3) * (‖c (n + 3)‖ ^ 2 * μ (n + 3)) ≤
    kappa m 2 * (‖c (n + 3)‖ ^ 2 * μ (n + 3)) - ‖c (n + 3)‖ ^ 2 * qmom μ m (n + 3)
  have h1 := hX.qmom_le m (n + 3)
  have h2 : kappa m (n + 3) ≤ kappa m 3 := kappa_antitone hm (by omega)
  have hμ := radMom_nonneg (X := X) (P := P) 0 (n + 3)
  have hc : 0 ≤ ‖c (n + 3)‖ ^ 2 := by positivity
  have h3 : μ (n + 3) * kappa m (n + 3) ≤ μ (n + 3) * kappa m 3 := mul_le_mul_of_nonneg_left h2 hμ
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h3) hc]

/-- **Corollary 4.3, optimality of the first coefficient.** For a pure quadratic
`f(a+z) = f(a) + c₂ z²` the deficit equals `2(m-1)/m³ |c₂|² (μ₂ - μ₁²)` exactly. -/
theorem deficit_pure_quadratic (hX : RadialSample X P) {m : ℕ} (hm : 2 ≤ m)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) (hc : ∀ n, 1 ≤ n → n ≠ 2 → c n = 0) :
    kappa m 2 * Vf c (radMom (X 0) P) - ∫ ω, ‖Bimg f a X m ω - f a‖ ^ 2 ∂P =
      2 * (m - 1) / (m : ℝ) ^ 3 * ‖c 2‖ ^ 2 * (radMom (X 0) P 2 - radMom (X 0) P 1 ^ 2) := by
  rw [hX.deficit_tsum (by omega) 2 hf hs, tsum_eq_single 1]
  · simp only [Nat.reduceAdd]
    rw [qmom_two _ (radMom_zero (X := X) 0) (by omega), kappa_two (by omega)]
    have : (m : ℝ) ≠ 0 := by positivity
    field_simp; ring
  · intro n hn
    rw [hc (n + 1) (by omega) (by omega)]; simp

/-- **Corollary 4.3, optimality of the second coefficient.** For a fixed radius and
`f(a+z) = f(a) + c₂ z² + c₃ z³` the deficit equals `(κ_{m,2} - κ_{m,3}) |c₃|² μ₃` exactly. -/
theorem deficit_fixed_radius (hX : RadialSample X P) {m : ℕ} (hm : 2 ≤ m)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n)
    (hc : ∀ n, 1 ≤ n → n ≠ 2 → n ≠ 3 → c n = 0) {ρ : ℝ} (hρ : ∀ᵐ ω ∂P, ‖X 0 ω‖ = ρ) :
    kappa m 2 * Vf c (radMom (X 0) P) - ∫ ω, ‖Bimg f a X m ω - f a‖ ^ 2 ∂P =
      (kappa m 2 - kappa m 3) * (‖c 3‖ ^ 2 * radMom (X 0) P 3) := by
  have hq2 := (hX.qmom_eq_iff hm (le_refl 2)).2 ⟨ρ, hρ⟩
  have hq3 := (hX.qmom_eq_iff hm (by norm_num : 2 ≤ 3)).2 ⟨ρ, hρ⟩
  rw [hX.deficit_tsum (by omega) 2 hf hs, tsum_eq_single 2]
  · simp only [Nat.reduceAdd]
    rw [hq3]; ring
  · intro n hn
    by_cases h1 : n = 1
    · subst h1; simp only [Nat.reduceAdd]; rw [hq2]; ring
    · rw [hc (n + 1) (by omega) (by omega) (by omega)]; simp

/-! ### Corollary 4.4 -/

omit [IsProbabilityMeasure P] in
lemma integral_norm_le_sqrt [IsProbabilityMeasure P] {Y : Ω → ℂ} (hY : MemLp Y 2 P) :
    ∫ ω, ‖Y ω‖ ∂P ≤ Real.sqrt (∫ ω, ‖Y ω‖ ^ 2 ∂P) := by
  have h := norm_integral_mul_conj_le hY (memLp_const (1 : ℂ))
  simp only [map_one, mul_one, norm_one, one_pow, integral_const, probReal_univ,
    smul_eq_mul, Real.sqrt_one] at h
  have h2 : ∫ ω, ‖Y ω‖ ∂P = ‖∫ ω, ((‖Y ω‖ : ℝ) : ℂ) ∂P‖ := by
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg
      (integral_nonneg fun _ => norm_nonneg _)]
  have h3 := norm_integral_mul_conj_le (hY.norm.ofReal) (memLp_const (1 : ℂ)) (P := P)
  simp only [map_one, mul_one, norm_one, one_pow, integral_const, probReal_univ,
    smul_eq_mul, Real.sqrt_one] at h3
  rw [h2]
  simpa using h3

omit [IsProbabilityMeasure P] in
lemma chebyshev_complex {Y : Ω → ℂ} (hY : MemLp Y 2 P) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ ‖Y ω‖} ≤ (∫ ω, ‖Y ω‖ ^ 2 ∂P) / ε ^ 2 := by
  have hint := (memLp_two_iff_integrable_sq_norm hY.1).1 hY
  have h := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => by positivity) hint
    (ε ^ 2)
  have hset : {ω | ε ^ 2 ≤ ‖Y ω‖ ^ 2} = {ω | ε ≤ ‖Y ω‖} := by
    ext ω; simp only [Set.mem_setOf_eq]
    exact pow_le_pow_iff_left₀ hε.le (norm_nonneg _) two_ne_zero
  rw [hset] at h
  rw [le_div_iff₀ (by positivity)]; linarith

/-- **Corollary 4.4, first-moment and Chebyshev bounds for `B_m(f)`.** -/
theorem deviation_B (hX : RadialSample X P) {m d : ℕ} (hm : 2 ≤ m)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, ‖Bimg f a X m ω - f a‖ ∂P ≤ Real.sqrt (kappa m d * Vf c (radMom (X 0) P)) ∧
      P.real {ω | ε ≤ ‖Bimg f a X m ω - f a‖} ≤ kappa m d * Vf c (radMom (X 0) P) / ε ^ 2 := by
  have hmem := hX.memLp_comp_S (m := m) (by omega) hf hs
  have hle := hX.main_le hm hf hs hlow
  constructor
  · exact (integral_norm_le_sqrt hmem).trans (Real.sqrt_le_sqrt hle)
  · exact (chebyshev_complex hmem hε).trans (div_le_div_of_nonneg_right hle (by positivity))

/-- **Corollary 4.4, first-moment and Chebyshev bounds for `A_m(f)`.** -/
theorem deviation_A (hX : RadialSample X P) {m : ℕ} (hm : 1 ≤ m)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, ‖Aimg f a X m ω - f a‖ ∂P ≤ Real.sqrt (Vf c (radMom (X 0) P) / m) ∧
      P.real {ω | ε ≤ ‖Aimg f a X m ω - f a‖} ≤ Vf c (radMom (X 0) P) / m / ε ^ 2 := by
  have hmem : MemLp (fun ω => Aimg f a X m ω - f a) 2 P := by
    have : (fun ω => Aimg f a X m ω - f a) =
        fun ω => (m : ℂ)⁻¹ * ∑ j ∈ range m, (f (a + X j ω) - f a) := funext fun ω => Aimg_sub hm ω
    rw [this]
    exact (memLp_finset_sum _ fun j _ => hX.memLp_comp_X hf hs j).const_mul _
  have heq := hX.integral_norm_sq_Aimg hm hf hs
  constructor
  · rw [← heq]; exact integral_norm_le_sqrt hmem
  · rw [← heq]; exact chebyshev_complex hmem hε

/-- **Corollary 4.4, convergence in `L²`.** -/
theorem tendsto_L2 (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    Tendsto (fun m => ∫ ω, ‖Aimg f a X m ω - f a‖ ^ 2 ∂P) atTop (𝓝 0) ∧
      Tendsto (fun m => ∫ ω, ‖Bimg f a X m ω - f a‖ ^ 2 ∂P) atTop (𝓝 0) := by
  have hV : Tendsto (fun m : ℕ => Vf c (radMom (X 0) P) / m) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hA : ∀ᶠ m : ℕ in atTop, ∫ ω, ‖Aimg f a X m ω - f a‖ ^ 2 ∂P = Vf c (radMom (X 0) P) / m :=
    (eventually_ge_atTop 1).mono fun m hm => hX.integral_norm_sq_Aimg hm hf hs
  refine ⟨(tendsto_congr' hA).2 hV, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hV
    (Eventually.of_forall fun m => integral_nonneg fun _ => by positivity) ?_
  filter_upwards [eventually_ge_atTop 2] with m hm
  have h := hX.main_le hm hf hs (d := 1) (fun n h1 h2 => by omega)
  rwa [kappa_one (by omega), one_div, ← div_eq_inv_mul] at h

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary12.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 12. Almost sure convergence of both centers (Corollary 4.4) -/

/-- Absolute convergence of an everywhere convergent power series on every circle. -/
lemma summable_norm_mul_pow_of_hasSum {g : ℂ → ℂ} {b : ℕ → ℂ}
    (hg : ∀ z, HasSum (fun n => b n * z ^ n) (g z)) (r : ℝ) (hr : 0 ≤ r) :
    Summable fun n => ‖b n‖ * r ^ n := by
  have h := (hg ((2 * r : ℝ) : ℂ)).summable.tendsto_atTop_zero
  have hev : ∀ᶠ n in atTop, ‖b n * ((2 * r : ℝ) : ℂ) ^ n‖ ≤ 1 := by
    have := (tendsto_norm_zero.comp h)
    exact (this.eventually (ge_mem_nhds one_pos))
  refine Summable.of_norm_bounded_eventually (g := fun n => (1 / 2 : ℝ) ^ n)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hev] with n hn
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hn
  rw [Real.norm_of_nonneg (by positivity)]
  have e : (2 * r) ^ n = 2 ^ n * r ^ n := mul_pow 2 r n
  rw [e] at hn
  rw [div_pow, one_pow, le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (b n), pow_nonneg hr n]

/-- An everywhere convergent power series defines a continuous function. -/
theorem continuous_of_hasSum {g : ℂ → ℂ} {b : ℕ → ℂ}
    (hg : ∀ z, HasSum (fun n => b n * z ^ n) (g z)) : Continuous g := by
  have hgeq : g = fun z => ∑' n, b n * z ^ n := funext fun z => (hg z).tsum_eq.symm
  rw [continuous_iff_continuousAt]
  intro z₀
  set r := ‖z₀‖ + 1
  have hcont : ContinuousOn g (Metric.closedBall 0 r) := by
    rw [hgeq]
    refine continuousOn_tsum (u := fun n => ‖b n‖ * r ^ n) (fun n => by fun_prop)
      (summable_norm_mul_pow_of_hasSum hg r (by positivity)) (fun n z hz => ?_)
    rw [norm_mul, norm_pow]
    have : ‖z‖ ≤ r := by simpa using hz
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) this n) (norm_nonneg _)
  refine hcont.continuousAt (Metric.closedBall_mem_nhds_of_mem ?_)
  simp [r]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace RadialSample

variable {X : ℕ → Ω → ℂ} {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

lemma smul_form (m : ℕ) (s : ℂ) : (m : ℂ)⁻¹ * s = ((m : ℝ)⁻¹ : ℝ) • s := by
  rw [Complex.real_smul]; push_cast; rfl

/-- `S_m → 0` almost surely (strong law of large numbers). -/
theorem ae_tendsto_Scen (hX : RadialSample X P) :
    ∀ᵐ ω ∂P, Tendsto (fun m => Scen X m ω) atTop (𝓝 0) := by
  have h := strong_law_ae (μ := P) X (by simpa using (hX.mom 0).integrable_pow 1)
    (fun i j hij => hX.indep.indepFun hij) (fun i => hX.ident i 0)
  have h0 : ∫ ω, X 0 ω ∂P = 0 := by simpa using hX.integral_pow_eq_zero 0 (le_refl 1)
  filter_upwards [h] with ω hω
  rw [h0] at hω
  refine hω.congr fun m => ?_
  rw [Scen, smul_form]

/-- **Corollary 4.4, almost sure convergence of the image of the center.** -/
theorem ae_tendsto_Bimg (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) :
    ∀ᵐ ω ∂P, Tendsto (fun m => Bimg f a X m ω) atTop (𝓝 (f a)) := by
  have hcont : Continuous fun z => f (a + z) := continuous_of_hasSum hf
  filter_upwards [hX.ae_tendsto_Scen] with ω hω
  have := (hcont.tendsto 0).comp hω
  simpa [Bimg, Function.comp_def] using this

/-- **Corollary 4.4, almost sure convergence of the center of the image cloud.** -/
theorem ae_tendsto_Aimg (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    ∀ᵐ ω ∂P, Tendsto (fun m => Aimg f a X m ω) atTop (𝓝 (f a)) := by
  have hmf : Measurable fun z => f (a + z) := measurable_of_hasSum hf
  set Y : ℕ → Ω → ℂ := fun j ω => f (a + X j ω)
  have hint : Integrable (Y 0) P := by
    have h1 := (hX.memLp_comp_X hf hs 0).integrable one_le_two
    refine (h1.add (integrable_const (f a))).congr (Eventually.of_forall fun ω => ?_)
    simp [Y]
  have hmean : ∫ ω, Y 0 ω ∂P = f a := by
    have hν := radMom_nonneg (X := X) (P := P) 0
    have hz := integral_comp_eq_zero (hX.orthoMoments_X 0) hν (g := fun z => f (a + z) - f a)
      (hasSum_g hf) (summable_gcoef hν hs) (gcoef_zero c)
      (fun p hp => hX.integral_pow_eq_zero 0 hp)
    rw [integral_sub ((hX.memLp_comp_X hf hs 0).integrable one_le_two |>.add
      (integrable_const (f a)) |>.congr (Eventually.of_forall fun ω => by simp))
      (integrable_const _)] at hz
    simp only [integral_const, probReal_univ, one_smul] at hz
    simpa [Y] using sub_eq_zero.1 hz
  have h := strong_law_ae (μ := P) Y hint
    (fun i j hij => (hX.indep.indepFun hij).comp hmf hmf)
    (fun i => (hX.ident i 0).comp hmf)
  filter_upwards [h] with ω hω
  rw [hmean] at hω
  refine hω.congr fun m => ?_
  rw [Aimg, smul_form]

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary13.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Part 13. The order of the map and the fluctuation scale (Theorem 6.1 = Theorem B) -/

lemma tendsto_pow_mul_qmom_of_lt (μ : ℕ → ℝ) (h0 : μ 0 = 1) {d k : ℕ} (hdk : d < k) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ d * qmom μ m k) atTop (𝓝 0) := by
  have h1 := tendsto_pow_mul_qmom μ h0 k
  have h2 : Tendsto (fun m : ℕ => (1 / (m : ℝ)) ^ (k - d)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).pow (k - d)
    rwa [zero_pow (by omega)] at this
  have := h1.mul h2
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have e : (m : ℝ) ^ k = (m : ℝ) ^ d * (m : ℝ) ^ (k - d) := by rw [← pow_add]; congr 1; omega
  rw [e, div_pow, one_pow]
  field_simp

namespace RadialSample

variable {X : ℕ → Ω → ℂ} {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

/-- **Theorem 6.1, (6.2).** `m^d E|B_m(f) - f(a)|² → |c_d|² d! μ₁^d`. -/
theorem tendsto_scaled_mse (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {d : ℕ} (hd : 1 ≤ d)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ d * ∫ ω, ‖Bimg f a X m ω - f a‖ ^ 2 ∂P) atTop
      (𝓝 (‖c d‖ ^ 2 * (d.factorial : ℝ) * radMom (X 0) P 1 ^ d)) := by
  set μ := radMom (X 0) P
  have h0 : μ 0 = 1 := radMom_zero (X := X) 0
  have hrepr : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ d * ∫ ω, ‖Bimg f a X m ω - f a‖ ^ 2 ∂P =
      ∑' n, (m : ℝ) ^ d * (‖c (n + 1)‖ ^ 2 * qmom μ m (n + 1)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    rw [hX.integral_norm_sq_Bimg hm hf hs, tsum_mul_left]
  rw [tendsto_congr' hrepr]
  set g : ℕ → ℝ := fun n => if n = d - 1 then ‖c d‖ ^ 2 * ((d.factorial : ℝ) * μ 1 ^ d) else 0
  have hg : ∑' n, g n = ‖c d‖ ^ 2 * (d.factorial : ℝ) * μ 1 ^ d := by
    rw [tsum_ite_eq]; ring
  rw [← hg]
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun n => (d.factorial : ℝ) * (‖c (n + 1)‖ ^ 2 * μ (n + 1)))
    ((summable_shift hs).mul_left _) (fun n => ?_) ?_
  · -- pointwise limits
    rcases lt_trichotomy (n + 1) d with hlt | heq | hgt
    · have hz : c (n + 1) = 0 := hlow (n + 1) (by omega) hlt
      have : g n = 0 := by simp only [g]; rw [if_neg (by omega)]
      rw [this]; simp [hz]
    · have : g n = ‖c d‖ ^ 2 * ((d.factorial : ℝ) * μ 1 ^ d) := by
        simp only [g]; rw [if_pos (by omega)]
      rw [this, heq]
      have := (tendsto_pow_mul_qmom μ h0 d).const_mul (‖c d‖ ^ 2)
      refine this.congr fun m => ?_
      ring
    · have : g n = 0 := by simp only [g]; rw [if_neg (by omega)]
      rw [this]
      have := (tendsto_pow_mul_qmom_of_lt μ h0 hgt).const_mul (‖c (n + 1)‖ ^ 2)
      rw [mul_zero] at this
      refine this.congr fun m => ?_
      ring
  · -- domination
    filter_upwards [eventually_ge_atTop 2] with m hm n
    have hq := qmom_nonneg μ (radMom_nonneg (X := X) 0) m (n + 1)
    rw [Real.norm_of_nonneg (by positivity)]
    by_cases hk : n + 1 < d
    · rw [hlow (n + 1) (by omega) hk]; simp
    · have h1 := hX.qmom_le m (n + 1)
      have h2 := kappa_antitone hm (not_lt.1 hk)
      have h3 := kappa_le_factorial_div (m := m) (by omega) d
      have hμ := radMom_nonneg (X := X) (P := P) 0 (n + 1)
      have hm' : (0 : ℝ) < (m : ℝ) ^ d := by positivity
      have h4 : (m : ℝ) ^ d * kappa m d ≤ d.factorial := by
        rw [le_div_iff₀ hm'] at h3; linarith
      have hc : 0 ≤ ‖c (n + 1)‖ ^ 2 := by positivity
      calc (m : ℝ) ^ d * (‖c (n + 1)‖ ^ 2 * qmom μ m (n + 1))
          ≤ (m : ℝ) ^ d * (‖c (n + 1)‖ ^ 2 * (μ (n + 1) * kappa m d)) := by
            gcongr; exact h1.trans (mul_le_mul_of_nonneg_left h2 hμ)
        _ = ((m : ℝ) ^ d * kappa m d) * (‖c (n + 1)‖ ^ 2 * μ (n + 1)) := by ring
        _ ≤ (d.factorial : ℝ) * (‖c (n + 1)‖ ^ 2 * μ (n + 1)) := by gcongr

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary14.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 14. General sampling laws and exact means (Section 7) -/

/-- `Bsum β m n = ∑_{|k|=n} (n choose k) ∏ β_{k_j}`, through the recursion on `m`. -/
noncomputable def Bsum (β : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, n => if n = 0 then 1 else 0
  | m + 1, n => ∑ i ∈ range (n + 1), ((n.choose i : ℕ) : ℂ) * β i * Bsum β m (n - i)

lemma Bsum_succ (β : ℕ → ℂ) (m n : ℕ) :
    Bsum β (m + 1) n = ∑ i ∈ range (n + 1), ((n.choose i : ℕ) : ℂ) * β i * Bsum β m (n - i) := rfl

lemma Bsum_zero_right (β : ℕ → ℂ) (h0 : β 0 = 1) (m : ℕ) : Bsum β m 0 = 1 := by
  induction m with
  | zero => simp [Bsum]
  | succ m ih => simp [Bsum_succ, ih, h0]

/-- The multinomial expression (7.1) for `Bsum`. -/
theorem Bsum_eq_multinomial_sum {ι : Type*} [DecidableEq ι] (β : ℕ → ℂ) (s : Finset ι) (n : ℕ) :
    Bsum β s.card n = ∑ k ∈ s.piAntidiag n, ((Nat.multinomial s k : ℕ) : ℂ) * ∏ i ∈ s, β (k i) := by
  induction s using Finset.cons_induction generalizing n with
  | empty =>
    by_cases hn : n = 0
    · subst hn; simp [Bsum]
    · simp [Bsum, hn]
  | cons i s hi ih =>
    rw [card_cons, Bsum_succ, piAntidiag_cons, sum_disjiUnion,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine sum_congr rfl fun a ha => ?_
    rw [ih, mul_sum, sum_map]
    refine sum_congr rfl fun g hg => ?_
    have hgi : g i = 0 := by
      by_contra h
      exact hi ((mem_piAntidiag.1 hg).2 i h)
    have hgs : ∑ j ∈ s, g j = n - a := (mem_piAntidiag.1 hg).1
    have ha' : a ≤ n := by have := mem_range.1 ha; omega
    simp only [addRightEmbedding_apply]
    rw [Nat.multinomial_cons, prod_cons]
    set F : ι → ℕ := g + fun t => if t = i then a else 0 with hFdef
    have h1 : F i = a := by simp [hFdef, hgi]
    have h2 : ∀ j ∈ s, F j = g j := by
      intro j hj
      have : j ≠ i := fun h => hi (h ▸ hj)
      simp [hFdef, this]
    rw [h1, sum_congr rfl h2, hgs, Nat.multinomial_congr h2,
      prod_congr rfl (fun j hj => show β (F j) = β (g j) by rw [h2 j hj]), Nat.add_sub_cancel' ha']
    push_cast
    ring

/-- If `β₁ = ⋯ = β_{n-1} = 0` then `Bsum β m n = m β_n` (used in Theorem 7.2). -/
lemma Bsum_of_vanishing (β : ℕ → ℂ) (h0 : β 0 = 1) {n : ℕ} (hn : 1 ≤ n)
    (hv : ∀ i, 1 ≤ i → i < n → β i = 0) (m : ℕ) : Bsum β m n = m * β n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  induction m with
  | zero => simp [Bsum]
  | succ m ih =>
    rw [Bsum_succ, sum_range_succ, sum_range_succ', sum_eq_zero]
    · simp [ih, h0, Bsum_zero_right β h0]; ring
    · intro i hi
      have hi' : i + 1 < n' + 1 := by have := mem_range.1 hi; omega
      rw [hv (i + 1) (by omega) hi']; simp

lemma Bsum_one (β : ℕ → ℂ) (h0 : β 0 = 1) (m : ℕ) : Bsum β m 1 = m * β 1 :=
  Bsum_of_vanishing β h0 le_rfl (fun i h1 h2 => by omega) m

/-- With `β₁ = 0`: `Bsum β m 2 = m β₂`. -/
lemma Bsum_two (β : ℕ → ℂ) (h0 : β 0 = 1) (h1 : β 1 = 0) (m : ℕ) : Bsum β m 2 = m * β 2 := by
  induction m with
  | zero => simp [Bsum]
  | succ m ih =>
    rw [Bsum_succ]; simp [sum_range_succ, ih, h0, h1, Bsum_zero_right β h0]; ring

/-- With `β₁ = 0`: `Bsum β m 3 = m β₃`. -/
lemma Bsum_three (β : ℕ → ℂ) (h0 : β 0 = 1) (h1 : β 1 = 0) (m : ℕ) : Bsum β m 3 = m * β 3 := by
  induction m with
  | zero => simp [Bsum]
  | succ m ih =>
    rw [Bsum_succ]
    simp [sum_range_succ, ih, h0, h1, Bsum_zero_right β h0, Bsum_two β h0 h1, Bsum_one β h0]
    ring

/-- With `β₁ = 0`: `Bsum β m 4 = m β₄ + 3 m (m-1) β₂²`. -/
lemma Bsum_four (β : ℕ → ℂ) (h0 : β 0 = 1) (h1 : β 1 = 0) (m : ℕ) :
    Bsum β m 4 = m * β 4 + 3 * m * (m - 1) * β 2 ^ 2 := by
  induction m with
  | zero => simp [Bsum]
  | succ m ih =>
    rw [Bsum_succ]
    simp [sum_range_succ, ih, h0, h1, Bsum_zero_right β h0, Bsum_two β h0 h1, Bsum_three β h0 h1,
      Bsum_one β h0, Nat.choose]
    ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Hypotheses of Section 7: i.i.d. complex variables with finite moments of all orders
(no rotational invariance). -/
structure IIDSample {ι : Type*} (X : ι → Ω → ℂ) (P : Measure Ω) : Prop where
  meas : ∀ j, Measurable (X j)
  indep : iIndepFun X P
  ident : ∀ i j, IdentDistrib (X i) (X j) P P
  mom : ∀ j, AllMoments (X j) P

/-- Analytic moments `β_n = E X^n`. -/
noncomputable def anMom (X : Ω → ℂ) (P : Measure Ω) (n : ℕ) : ℂ := ∫ ω, X ω ^ n ∂P

omit [IsProbabilityMeasure P] in
lemma RadialSample.toIIDSample {ι : Type*} {X : ι → Ω → ℂ} (hX : RadialSample X P) :
    IIDSample X P := ⟨hX.meas, hX.indep, hX.ident, hX.mom⟩

/-- `E (U+V)^n = ∑ C(n,i) E U^i E V^{n-i}` for independent `U, V`. -/
lemma integral_add_pow_of_indep {U V : Ω → ℂ} (hU : AllMoments U P) (hV : AllMoments V P)
    (hind : IndepFun U V P) (n : ℕ) :
    ∫ ω, (U ω + V ω) ^ n ∂P =
      ∑ i ∈ range (n + 1), (n.choose i : ℂ) * (∫ ω, U ω ^ i ∂P) * ∫ ω, V ω ^ (n - i) ∂P := by
  have hexp : ∀ ω, (U ω + V ω) ^ n = ∑ i ∈ range (n + 1), (n.choose i : ℂ) * (U ω ^ i * V ω ^ (n - i)) := by
    intro ω; rw [add_pow]; refine sum_congr rfl fun i _ => by ring
  have hi : ∀ i, IndepFun (fun ω => U ω ^ i) (fun ω => V ω ^ (n - i)) P := fun i =>
    hind.comp (φ := fun z : ℂ => z ^ i) (ψ := fun z : ℂ => z ^ (n - i)) (by fun_prop) (by fun_prop)
  have hint : ∀ i, Integrable (fun ω => (n.choose i : ℂ) * (U ω ^ i * V ω ^ (n - i))) P := fun i =>
    ((hi i).integrable_mul (hU.integrable_pow i) (hV.integrable_pow (n - i))).const_mul _
  simp_rw [hexp]
  rw [integral_finset_sum _ fun i _ => hint i]
  refine sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, (hi i).integral_fun_mul_eq_mul_integral (hU.integrable_pow i).1
    (hV.integrable_pow (n - i)).1]
  ring

namespace IIDSample

variable {ι : Type*} {X : ι → Ω → ℂ}

omit [IsProbabilityMeasure P] in
lemma anMom_eq (hX : IIDSample X P) (i j : ι) : anMom (X i) P = anMom (X j) P := by
  ext n
  exact ((hX.ident i j).comp (u := fun z : ℂ => z ^ n) (by fun_prop)).integral_eq

lemma anMom_zero (j : ι) : anMom (X j) P 0 = 1 := by simp [anMom]

/-- `E (∑_{j∈s} X_j)^n = Bsum β |s| n`. -/
theorem integral_sum_pow (hX : IIDSample X P) (i₀ : ι) (s : Finset ι) (n : ℕ) :
    ∫ ω, (∑ j ∈ s, X j ω) ^ n ∂P = Bsum (anMom (X i₀) P) s.card n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    by_cases hn : n = 0
    · subst hn; simp [Bsum]
    · simp [Bsum, hn, zero_pow hn]
  | insert i s hi ih =>
    have hsum : (fun ω => (∑ j ∈ insert i s, X j ω) ^ n) =
        fun ω => (X i ω + ∑ j ∈ s, X j ω) ^ n := by
      ext ω; rw [sum_insert hi]
    rw [hsum, card_insert_of_notMem hi]
    have hind : IndepFun (X i) (fun ω => ∑ j ∈ s, X j ω) P := by
      have := (hX.indep.indepFun_finset_sum_of_notMem hX.meas hi).symm
      convert this using 1
      ext ω; simp [Finset.sum_apply]
    rw [integral_add_pow_of_indep (hX.mom i) (AllMoments.finset_sum s fun j _ => hX.mom j) hind,
      Bsum_succ]
    refine sum_congr rfl fun k _ => ?_
    rw [ih, ← anMom, hX.anMom_eq i i₀]

end IIDSample

namespace IIDSample

variable {X : ℕ → Ω → ℂ}

/-- **Proposition 7.1 (exact polynomial bias).** `E S_m^n = m^{-n} ∑_{|k|=n} (n choose k) ∏ β_{k_j}`. -/
theorem integral_Scen_pow (hX : IIDSample X P) (m n : ℕ) :
    ∫ ω, Scen X m ω ^ n ∂P = Bsum (anMom (X 0) P) m n / (m : ℂ) ^ n := by
  simp only [Scen, mul_pow]
  rw [integral_const_mul, hX.integral_sum_pow 0 (range m) n, card_range, inv_pow, div_eq_inv_mul]

/-- **Proposition 7.1, special cases with `β₁ = 0`.** -/
theorem integral_Scen_pow_small (hX : IIDSample X P) {m : ℕ} (hm : 1 ≤ m)
    (h1 : anMom (X 0) P 1 = 0) :
    ∫ ω, Scen X m ω ^ 2 ∂P = anMom (X 0) P 2 / m ∧
    ∫ ω, Scen X m ω ^ 3 ∂P = anMom (X 0) P 3 / (m : ℂ) ^ 2 ∧
    ∫ ω, Scen X m ω ^ 4 ∂P = 3 * anMom (X 0) P 2 ^ 2 / (m : ℂ) ^ 2 +
      (anMom (X 0) P 4 - 3 * anMom (X 0) P 2 ^ 2) / (m : ℂ) ^ 3 := by
  have h0 : anMom (X 0) P 0 = 1 := anMom_zero (X := X) 0
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  refine ⟨?_, ?_, ?_⟩
  · rw [hX.integral_Scen_pow, Bsum_two _ h0 h1]; field_simp
  · rw [hX.integral_Scen_pow, Bsum_three _ h0 h1]; field_simp
  · rw [hX.integral_Scen_pow, Bsum_four _ h0 h1]; field_simp; ring

omit [IsProbabilityMeasure P] in
lemma allMoments_Scen (hX : IIDSample X P) (m : ℕ) : AllMoments (Scen X m) P :=
  (AllMoments.finset_sum (range m) fun j _ => hX.mom j).const_mul _

/-- Expectation of a polynomial of a variable in terms of its analytic moments. -/
lemma integral_eval_poly {W : Ω → ℂ} (hW : AllMoments W P) (Q : Polynomial ℂ) :
    ∫ ω, Q.eval (W ω) ∂P = ∑ k ∈ range (Q.natDegree + 1), Q.coeff k * ∫ ω, W ω ^ k ∂P := by
  have h : ∀ ω, Q.eval (W ω) = ∑ k ∈ range (Q.natDegree + 1), Q.coeff k * W ω ^ k := by
    intro ω; rw [Polynomial.eval_eq_sum_range]
  simp_rw [h]
  rw [integral_finset_sum _ fun k _ => (hW.integrable_pow k).const_mul _]
  simp_rw [integral_const_mul]

/-- A variable all of whose analytic moments vanish preserves all polynomial means. -/
lemma integral_eval_poly_of_vanishing {W : Ω → ℂ} (hW : AllMoments W P)
    (hv : ∀ n, 1 ≤ n → ∫ ω, W ω ^ n ∂P = 0) (a : ℂ) (Q : Polynomial ℂ) :
    ∫ ω, Q.eval (a + W ω) ∂P = Q.eval a := by
  set R := Q.comp (Polynomial.C a + Polynomial.X)
  have hR : ∀ z, Q.eval (a + z) = R.eval z := by intro z; simp [R]
  simp_rw [hR]
  rw [integral_eval_poly hW, sum_range_succ', sum_eq_zero]
  · simp [R, Polynomial.coeff_zero_eq_eval_zero]
  · intro k _; rw [hv (k + 1) (by omega), mul_zero]

/-- **Theorem 7.2 (a moment criterion for exact means).** For any fixed `m₀ ≥ 1`, the following
are equivalent: (1) `E X^n = 0` for all `n ≥ 1`; (2) `E P(a+X) = P(a)` for all polynomials;
(3) `E P(a + S_{m₀}) = P(a)` for all polynomials; (4) `E P(a+S_m) = P(a)` for all polynomials and
all `m ≥ 1`. (The paper states it for `m₀ ≥ 2`; the proof works verbatim for `m₀ ≥ 1`.) -/
theorem criterion (hX : IIDSample X P) (a : ℂ) {m₀ : ℕ} (hm₀ : 1 ≤ m₀) :
    List.TFAE [∀ n, 1 ≤ n → anMom (X 0) P n = 0,
      ∀ Q : Polynomial ℂ, ∫ ω, Q.eval (a + X 0 ω) ∂P = Q.eval a,
      ∀ Q : Polynomial ℂ, ∫ ω, Q.eval (a + Scen X m₀ ω) ∂P = Q.eval a,
      ∀ m, 1 ≤ m → ∀ Q : Polynomial ℂ, ∫ ω, Q.eval (a + Scen X m ω) ∂P = Q.eval a] := by
  have h0 : anMom (X 0) P 0 = 1 := anMom_zero (X := X) 0
  tfae_have 1 → 2 := fun h Q => integral_eval_poly_of_vanishing (hX.mom 0) h a Q
  tfae_have 2 → 1 := by
    intro h n hn
    have := h ((Polynomial.X - Polynomial.C a) ^ n)
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      add_sub_cancel_left, sub_self, zero_pow (by omega : n ≠ 0)] at this
    exact this
  tfae_have 1 → 4 := by
    intro h m hm Q
    refine integral_eval_poly_of_vanishing (hX.allMoments_Scen m) (fun n hn => ?_) a Q
    rw [hX.integral_Scen_pow, Bsum_of_vanishing _ h0 hn (fun i hi _ => h i hi)]
    rw [h n hn]; simp
  tfae_have 4 → 3 := fun h => h m₀ hm₀
  tfae_have 3 → 1 := by
    intro h
    have hm' : (m₀ : ℂ) ≠ 0 := by exact_mod_cast (by omega : m₀ ≠ 0)
    intro n hn
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hv : ∀ i, 1 ≤ i → i < n → anMom (X 0) P i = 0 := fun i hi hin => ih i hin hi
      have hS := h ((Polynomial.X - Polynomial.C a) ^ n)
      simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        add_sub_cancel_left, sub_self, zero_pow (by omega : n ≠ 0)] at hS
      rw [hX.integral_Scen_pow, Bsum_of_vanishing _ h0 hn hv] at hS
      have := div_eq_zero_iff.1 hS
      rcases this with h1 | h1
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact absurd h2 hm'
        · exact h2
      · exact absurd ((pow_eq_zero_iff (by omega : n ≠ 0)).1 h1) hm'
  tfae_finish

end IIDSample

/-- **Example 7.4 (bias for real sampling).** If `X = ±1` with `E X = 0` (so `β₁ = 0`, `β₂ = 1`),
then for `P(a+z) = z²` one has `E P(ω_m) = 1/m ≠ 0 = P(a)`. -/
theorem bias_real_sampling {X : ℕ → Ω → ℂ} (hX : IIDSample X P) {m : ℕ} (hm : 1 ≤ m)
    (hsq : ∀ᵐ ω ∂P, X 0 ω ^ 2 = 1) (hmean : ∫ ω, X 0 ω ∂P = 0) :
    ∫ ω, Scen X m ω ^ 2 ∂P = 1 / m := by
  have h1 : anMom (X 0) P 1 = 0 := by simpa [anMom] using hmean
  have h2 : anMom (X 0) P 2 = 1 := by
    simp only [anMom]
    rw [integral_congr_ae hsq]; simp
  rw [(hX.integral_Scen_pow_small hm h1).1, h2]

end Barycenter

-- ============================================================================
-- Source part: Bary15.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 15. I.i.d. samples from a given law; the uniform law on the unit disk (Section 2) -/

/-- A law `ν` on `ℂ` is rotationally invariant if it is preserved by every rotation. -/
def RotInvLaw (ν : Measure ℂ) : Prop :=
  ∀ θ : ℝ, ν.map (fun z => Complex.exp (θ * Complex.I) * z) = ν

/-- The product space carrying an i.i.d. sequence with law `ν`. -/
noncomputable def iidMeasure (ν : Measure ℂ) [IsProbabilityMeasure ν] : Measure (ℕ → ℂ) :=
  Measure.infinitePi fun _ => ν

instance (ν : Measure ℂ) [IsProbabilityMeasure ν] : IsProbabilityMeasure (iidMeasure ν) := by
  unfold iidMeasure; infer_instance

/-- The coordinate variables `X_j(ω) = ω_j`. -/
def coord (j : ℕ) (ω : ℕ → ℂ) : ℂ := ω j

lemma map_coord (ν : Measure ℂ) [IsProbabilityMeasure ν] (j : ℕ) :
    (iidMeasure ν).map (coord j) = ν :=
  Measure.infinitePi_map_eval _ j

/-- The coordinates of the product of copies of a rotationally invariant law with finite moments
of all orders form a radial sample. -/
theorem coord_radialSample (ν : Measure ℂ) [IsProbabilityMeasure ν] (hrot : RotInvLaw ν)
    (hmom : ∀ p : ℕ, MemLp id p ν) : RadialSample coord (iidMeasure ν) where
  meas j := measurable_pi_apply j
  indep := by
    have := iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ x => x)
      (fun _ => measurable_id)
    exact this
  ident i j := ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply j).aemeasurable, by
    rw [map_coord, map_coord]⟩
  rot j θ := by
    have hm : Measurable (fun z : ℂ => Complex.exp (θ * Complex.I) * z) := measurable_const_mul _
    refine ⟨(hm.comp (measurable_pi_apply j)).aemeasurable, (measurable_pi_apply j).aemeasurable, ?_⟩
    have h1 : (fun ω : ℕ → ℂ => Complex.exp (θ * Complex.I) * coord j ω) =
        (fun z : ℂ => Complex.exp (θ * Complex.I) * z) ∘ coord j := rfl
    rw [h1, ← Measure.map_map hm (measurable_pi_apply j), map_coord, hrot θ]
  mom j p := by
    have h := hmom p
    rw [← map_coord ν j] at h
    exact (memLp_map_measure_iff (μ := iidMeasure ν) (f := coord j) h.1
      (measurable_pi_apply j).aemeasurable).1 h

lemma radMom_coord (ν : Measure ℂ) [IsProbabilityMeasure ν] (n : ℕ) :
    radMom (coord 0) (iidMeasure ν) n = ∫ z, ‖z‖ ^ (2 * n) ∂ν := by
  have h := integral_map (μ := iidMeasure ν) (measurable_pi_apply 0).aemeasurable
    (f := fun z : ℂ => ‖z‖ ^ (2 * n)) (by fun_prop)
  rw [show (fun ω : ℕ → ℂ => ω 0) = coord 0 from rfl, map_coord] at h
  rw [radMom, h]; rfl

/-! ### The uniform law on the unit disk -/

/-- The uniform probability law on the closed unit disk `D` (density `π⁻¹`). -/
noncomputable def diskLaw : Measure ℂ :=
  ENNReal.ofReal (Real.pi⁻¹) • volume.restrict (Metric.closedBall (0 : ℂ) 1)

instance : IsProbabilityMeasure diskLaw := by
  constructor
  simp only [diskLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Complex.volume_closedBall, smul_eq_mul]
  rw [ENNReal.ofReal_one, one_pow, one_mul, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ Real.pi_ne_zero, ENNReal.ofReal_one]

theorem diskLaw_rotInv : RotInvLaw diskLaw := by
  intro θ
  have hf : (fun z => Complex.exp (θ * Complex.I) * z) = rotation (Circle.exp θ) := by
    ext1 z; rw [rotation_apply, Circle.coe_exp]
  have hmp : MeasurePreserving (rotation (Circle.exp θ)) (volume : Measure ℂ) volume :=
    (rotation (Circle.exp θ)).measurePreserving
  have hpre : (rotation (Circle.exp θ)) ⁻¹' Metric.closedBall (0 : ℂ) 1 =
      Metric.closedBall (0 : ℂ) 1 := by
    ext z; simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, rotation_apply,
      norm_mul, Circle.norm_coe, one_mul]
  have h2 := hmp.restrict_preimage (s := Metric.closedBall (0 : ℂ) 1) measurableSet_closedBall
  rw [hpre] at h2
  rw [diskLaw, hf, Measure.map_smul, h2.map_eq]

lemma diskLaw_ae_norm_le : ∀ᵐ z ∂diskLaw, ‖z‖ ≤ 1 := by
  refine Measure.ae_smul_measure ?_ _
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
  simpa using hz

lemma diskLaw_memLp (p : ℕ) : MemLp id p diskLaw :=
  MemLp.of_bound measurable_id.aestronglyMeasurable 1 diskLaw_ae_norm_le

/-- `E|Z|^{2n} = 1/(n+1)` for `Z` uniform on the disk. -/
theorem diskLaw_moment (n : ℕ) : ∫ z, ‖z‖ ^ (2 * n) ∂diskLaw = 1 / (n + 1) := by
  rw [diskLaw, integral_smul_measure, ← integral_indicator measurableSet_closedBall,
    ← Complex.integral_comp_polarCoord_symm]
  have hcongr : ∫ p in polarCoord.target, p.1 • (Metric.closedBall (0 : ℂ) 1).indicator
      (fun z => ‖z‖ ^ (2 * n)) (Complex.polarCoord.symm p) =
      ∫ p in polarCoord.target, (Set.Iic (1 : ℝ)).indicator (fun r => r ^ (2 * n + 1)) p.1 := by
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1
    simp only [Set.indicator, Metric.mem_closedBall, dist_zero_right,
      Complex.norm_polarCoord_symm, abs_of_pos hp1, Set.mem_Iic, smul_eq_mul]
    split_ifs <;> ring
  rw [hcongr, show polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi from rfl,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_fun_fst (f := fun r => (Set.Iic (1 : ℝ)).indicator (fun r => r ^ (2 * n + 1)) r)]
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    Set.Iic_inter_Ioi, ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
  simp only [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioo]
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by linarith [Real.pi_pos]),
    smul_eq_mul, smul_eq_mul]
  have := Real.pi_pos
  push_cast
  field_simp
  ring

end Barycenter

-- ============================================================================
-- Source part: Bary16.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 16. Monomials, and the unit-disk warm-up (Section 2) -/

/-- Taylor coefficients of the monomial `z ↦ z^d`. -/
def monoCoef (d : ℕ) (n : ℕ) : ℂ := if n = d then 1 else 0

lemma hasSum_monoCoef (d : ℕ) (z : ℂ) :
    HasSum (fun n => monoCoef d n * z ^ n) ((0 + z) ^ d) := by
  simp only [monoCoef, zero_add, ite_mul, one_mul, zero_mul]
  convert hasSum_ite_eq d (z ^ d) using 2 with n
  split_ifs with h <;> simp [h]

lemma summable_monoCoef (d : ℕ) (ν : ℕ → ℝ) : Summable fun n => ‖monoCoef d n‖ ^ 2 * ν n :=
  summable_of_ne_finset_zero (s := {d}) (fun n hn => by simp at hn; simp [monoCoef, hn])

lemma Vf_monoCoef {d : ℕ} (hd : 1 ≤ d) (ν : ℕ → ℝ) : Vf (monoCoef d) ν = ν d := by
  rw [Vf, tsum_eq_single (d - 1)]
  · simp [monoCoef, Nat.sub_add_cancel hd]
  · intro n hn; have : n + 1 ≠ d := by omega
    simp [monoCoef, this]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [MeasurableSpace Ω] in
lemma Aimg_monomial (X : ℕ → Ω → ℂ) (m n : ℕ) (ω : Ω) :
    Aimg (fun z => z ^ n) 0 X m ω = Wpow X m n ω := by
  simp [Aimg, Wpow]

omit [MeasurableSpace Ω] in
lemma Bimg_monomial (X : ℕ → Ω → ℂ) (m n : ℕ) (ω : Ω) :
    Bimg (fun z => z ^ n) 0 X m ω = Scen X m ω ^ n := by
  simp [Bimg]

namespace RadialSample

variable {X : ℕ → Ω → ℂ}

/-- `E|S_m^n|² = q_{m,n}`. -/
lemma integral_norm_sq_Scen_pow (hX : RadialSample X P) (m n : ℕ) :
    ∫ ω, ‖Scen X m ω ^ n‖ ^ 2 ∂P = qmom (radMom (X 0) P) m n := by
  have h := hX.cmom_Scen m n n
  rw [if_pos rfl, cmom_self] at h
  have h' := congrArg Complex.re h
  simp only [Complex.ofReal_re] at h'
  simp_rw [norm_pow, ← pow_mul, mul_comm n 2]
  exact h'

/-- `E|W_m^{(n)}|² = μ_n / m`. -/
lemma integral_norm_sq_Wpow (hX : RadialSample X P) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∫ ω, ‖Wpow X m n ω‖ ^ 2 ∂P = radMom (X 0) P n / m := by
  have h := hX.integral_norm_sq_Aimg (f := fun z => z ^ n) (a := 0) hm (hasSum_monoCoef n) (summable_monoCoef n _)
  simp only [Aimg_monomial, zero_pow (by omega : n ≠ 0), sub_zero] at h
  rw [h, Vf_monoCoef hn]

end RadialSample

/-! ### The unit disk -/

/-- The probability measure carrying the i.i.d. unit-disk darts `Z_j = coord j`. -/
noncomputable abbrev diskP : Measure (ℕ → ℂ) := iidMeasure diskLaw

theorem disk_radialSample : RadialSample coord diskP :=
  coord_radialSample diskLaw diskLaw_rotInv diskLaw_memLp

/-- The radial moments of the disk: `μ_n = 1/(n+1)`. -/
noncomputable def diskMom (n : ℕ) : ℝ := 1 / (n + 1)

lemma radMom_disk : radMom (coord 0) diskP = diskMom := by
  ext n; rw [radMom_coord, diskLaw_moment, diskMom]

/-- **Proposition 2.1 (Disk moments).** `E[Z^p \bar Z^q] = δ_{pq}/(p+1)`. -/
theorem disk_moments (j p q : ℕ) :
    ∫ ω, coord j ω ^ p * conj (coord j ω) ^ q ∂diskP =
      if p = q then ((1 / (p + 1) : ℝ) : ℂ) else 0 := by
  have h := (disk_radialSample.rot j).cmom_eq p q
  rw [disk_radialSample.radMom_eq j 0, radMom_disk] at h
  exact h

/-- **Theorem 2.2 (Mean of `n`th powers in the disk), (2.1).** -/
theorem disk_Wpow_mean {m n : ℕ} (hn : 1 ≤ n) : ∫ ω, Wpow coord m n ω ∂diskP = 0 :=
  disk_radialSample.integral_Wpow m hn

theorem disk_Wpow_cov {m p q : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p) :
    ∫ ω, Wpow coord m p ω * conj (Wpow coord m q ω) ∂diskP =
      if p = q then ((1 / ((p + 1) * m) : ℝ) : ℂ) else 0 := by
  rw [disk_radialSample.integral_Wpow_mul_conj hm hp, radMom_disk, diskMom]
  split_ifs
  · congr 1; field_simp
  · rfl

/-- **Theorem 2.2, (2.2).** First-moment (Cauchy–Schwarz) and Chebyshev bounds. -/
theorem disk_Wpow_bounds {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, ‖Wpow coord m n ω‖ ∂diskP ≤ 1 / Real.sqrt ((n + 1) * m) ∧
      diskP.real {ω | ε ≤ ‖Wpow coord m n ω‖} ≤ 1 / ((n + 1) * m * ε ^ 2) := by
  have h := disk_radialSample.deviation_A (f := fun z => z ^ n) (a := 0) hm (hasSum_monoCoef n) (summable_monoCoef n _) hε
  simp only [Aimg_monomial, zero_pow (by omega : n ≠ 0), sub_zero, Vf_monoCoef hn,
    radMom_disk, diskMom] at h
  refine ⟨h.1.trans_eq ?_, h.2.trans_eq ?_⟩
  · rw [div_div, Real.sqrt_div' _ (by positivity), Real.sqrt_one]
  · field_simp

/-- **Theorem 2.2, almost sure convergence.** `W_m^{(n)} → 0` almost surely. -/
theorem disk_Wpow_ae (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ ω ∂diskP, Tendsto (fun m => Wpow coord m n ω) atTop (𝓝 0) := by
  have h := disk_radialSample.ae_tendsto_Aimg (f := fun z => z ^ n) (a := 0) (hasSum_monoCoef n) (summable_monoCoef n _)
  simpa [Aimg_monomial, zero_pow (by omega : n ≠ 0)] using h

/-- **Example 2.3.** For darts uniform on the unit circle, `E|W_m^{(n)}|² = 1/m` for all `n`. -/
theorem circle_Wpow_sq {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∫ ω, ‖Wpow steinhaus m n ω‖ ^ 2 ∂steinhausMeasure = 1 / m := by
  rw [steinhaus_radialSample.integral_norm_sq_Wpow hm hn, radMom_steinhaus]

/-- **Proposition 2.4 (Powers of the center in the disk), means.** `E ω_m^n = 0`. -/
theorem disk_center_pow_mean (m : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ ω, Scen coord m ω ^ n ∂diskP = 0 :=
  disk_radialSample.integral_Scen_pow m hn

/-- `E|ω_m^n|² = q_{m,n}` with the disk moments `μ_k = 1/(k+1)`. -/
theorem disk_center_pow_sq (m n : ℕ) :
    ∫ ω, ‖Scen coord m ω ^ n‖ ^ 2 ∂diskP = qmom diskMom m n := by
  rw [disk_radialSample.integral_norm_sq_Scen_pow, radMom_disk]

lemma diskMom_zero : diskMom 0 = 1 := by norm_num [diskMom]

/-- **Proposition 2.4, (2.4).** The three explicit formulas. -/
theorem disk_center_pow_sq_formulas {m : ℕ} (hm : 1 ≤ m) :
    ∫ ω, ‖Scen coord m ω ^ 1‖ ^ 2 ∂diskP = 1 / (2 * m) ∧
    ∫ ω, ‖Scen coord m ω ^ 2‖ ^ 2 ∂diskP = (3 * m - 1) / (6 * m ^ 3) ∧
    ∫ ω, ‖Scen coord m ω ^ 3‖ ^ 2 ∂diskP = (3 * m ^ 2 - 3 * m + 1) / (4 * m ^ 5) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [disk_center_pow_sq, qmom_one _ diskMom_zero hm]; norm_num [diskMom]; ring
  · rw [disk_center_pow_sq, qmom_two _ diskMom_zero hm]; norm_num [diskMom]
    field_simp; ring
  · rw [disk_center_pow_sq, qmom_three _ diskMom_zero hm]; norm_num [diskMom]
    field_simp; ring

/-- **Proposition 2.4, asymptotics.** `m^n E|ω_m^n|² → n!/2^n`, i.e.
`E|ω_m^n|² = n! (2m)^{-n} (1 + o(1))`. -/
theorem disk_center_pow_sq_asymp (n : ℕ) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ n * ∫ ω, ‖Scen coord m ω ^ n‖ ^ 2 ∂diskP) atTop
      (𝓝 ((n.factorial : ℝ) / 2 ^ n)) := by
  simp_rw [disk_center_pow_sq]
  convert tendsto_pow_mul_qmom diskMom diskMom_zero n using 2
  norm_num [diskMom, div_eq_mul_inv]
  left; rw [one_div, inv_pow]

/-- **Proposition 2.4, bounds.** `E|ω_m^n|² ≤ κ_{m,n}/(n+1) ≤ min{1/m, n!/m^n}/(n+1)`. -/
theorem disk_center_pow_sq_le {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∫ ω, ‖Scen coord m ω ^ n‖ ^ 2 ∂diskP ≤ kappa m n / (n + 1) ∧
      kappa m n / (n + 1) ≤ min (1 / (m : ℝ)) ((n.factorial : ℝ) / (m : ℝ) ^ n) / (n + 1) := by
  constructor
  · have h := disk_radialSample.qmom_le m n
    rw [radMom_disk] at h
    rw [disk_center_pow_sq]
    refine h.trans_eq ?_
    rw [diskMom]; ring
  · exact div_le_div_of_nonneg_right (le_min (kappa_le_inv hm hn) (kappa_le_factorial_div hm n))
      (by positivity)

end Barycenter

-- ============================================================================
-- Source part: Bary17.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 17. Scaled samples, bounded samples and Cauchy's estimate -/

/-- For an everywhere convergent power series, `∑ |b_n|² ρ^{2n} < ∞` for every real `ρ`. -/
lemma summable_sq_of_hasSum {g : ℂ → ℂ} {b : ℕ → ℂ}
    (hg : ∀ z, HasSum (fun n => b n * z ^ n) (g z)) (ρ : ℝ) :
    Summable fun n => ‖b n‖ ^ 2 * ρ ^ (2 * n) := by
  have h := summable_norm_mul_pow_of_hasSum hg |ρ| (abs_nonneg ρ)
  have hev : ∀ᶠ n in atTop, ‖b n‖ * |ρ| ^ n ≤ 1 :=
    h.tendsto_atTop_zero.eventually (ge_mem_nhds one_pos)
  refine Summable.of_norm_bounded_eventually (g := fun n => ‖b n‖ * |ρ| ^ n) h ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hev] with n hn
  have e : ‖b n‖ ^ 2 * ρ ^ (2 * n) = (‖b n‖ * |ρ| ^ n) ^ 2 := by
    rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul, pow_mul, sq_abs]
  rw [e, Real.norm_of_nonneg (by positivity)]
  have h0 : 0 ≤ ‖b n‖ * |ρ| ^ n := by positivity
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace RadialSample

variable {X : ℕ → Ω → ℂ}

lemma radMom_le_of_bound (hX : RadialSample X P) {R : ℝ} (hR : ∀ᵐ ω ∂P, ‖X 0 ω‖ ≤ R) (n : ℕ) :
    radMom (X 0) P n ≤ R ^ (2 * n) := by
  have h := integral_mono_ae ((hX.mom 0).integrable_norm_pow (2 * n)) (integrable_const (R ^ (2 * n)))
    (hR.mono fun ω hω => pow_le_pow_left₀ (norm_nonneg _) hω (2 * n))
  simpa [radMom] using h

/-- For bounded samples (`|X| ≤ R` a.s.) the summability hypothesis on the Taylor coefficients is
automatic. -/
lemma summable_of_bound (hX : RadialSample X P) {R : ℝ} (hR : ∀ᵐ ω ∂P, ‖X 0 ω‖ ≤ R)
    {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ} (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) :
    Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (radMom_nonneg (X := X) 0 n))
    (fun n => mul_le_mul_of_nonneg_left (hX.radMom_le_of_bound hR n) (by positivity))
    (summable_sq_of_hasSum hf R)

omit [IsProbabilityMeasure P] in
/-- Scaling a radial sample by a constant gives a radial sample. -/
theorem const_mul (hX : RadialSample X P) (r : ℂ) : RadialSample (fun j ω => r * X j ω) P where
  meas j := measurable_const.mul (hX.meas j)
  indep := hX.indep.comp (fun _ z => r * z) (fun _ => measurable_const_mul r)
  ident i j := (hX.ident i j).comp (measurable_const_mul r)
  rot j θ := by
    have h := (hX.rot j θ).comp (measurable_const_mul r)
    convert h using 1
    funext ω; simp only [Function.comp]; ring
  mom j := (hX.mom j).const_mul r

end RadialSample

omit [IsProbabilityMeasure P] in
lemma radMom_const_mul (X : Ω → ℂ) (r : ℂ) (n : ℕ) :
    radMom (fun ω => r * X ω) P n = ‖r‖ ^ (2 * n) * radMom X P n := by
  simp only [radMom, norm_mul, mul_pow, integral_const_mul]

/-- The circle sample `r U_j` (Steinhaus variables scaled by `r`). -/
noncomputable def circSample (r : ℝ) (j : ℕ) (ω : SteinhausΩ) : ℂ := (r : ℂ) * steinhaus j ω

theorem circSample_radialSample (r : ℝ) : RadialSample (circSample r) steinhausMeasure :=
  steinhaus_radialSample.const_mul r

lemma radMom_circSample (r : ℝ) (n : ℕ) :
    radMom (circSample r 0) steinhausMeasure n = (r ^ 2) ^ n := by
  have h := radMom_const_mul (P := steinhausMeasure) (steinhaus 0) (r : ℂ) n
  rw [show (fun ω => (r : ℂ) * steinhaus 0 ω) = circSample r 0 from rfl] at h
  rw [h, radMom_steinhaus, Complex.norm_real, Real.norm_eq_abs, mul_one, pow_mul, sq_abs]

lemma norm_circSample (r : ℝ) (j : ℕ) (ω : SteinhausΩ) : ‖circSample r j ω‖ = |r| := by
  simp [circSample, norm_steinhaus]

/-- **Cauchy's estimate**, proved with the orthogonality of Steinhaus monomials:
if `|f(a+z)| ≤ M` on `|z| = R`, then `|c_n| R^n ≤ M`. -/
theorem cauchy_estimate {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) {R M : ℝ} (hR : 0 < R)
    (hM : ∀ z : ℂ, ‖z‖ = R → ‖f (a + z)‖ ≤ M) (n : ℕ) : ‖c n‖ * R ^ n ≤ M := by
  set W := circSample R 0
  set ν : ℕ → ℝ := fun k => (R ^ 2) ^ k
  have hX := circSample_radialSample R
  have hW : OrthoMoments W steinhausMeasure ν := by
    have := hX.orthoMoments_X 0
    have e : radMom (circSample R 0) steinhausMeasure = ν := funext (radMom_circSample R)
    rwa [e] at this
  have hν : ∀ k, 0 ≤ ν k := fun k => by positivity
  have hs : Summable fun k => ‖c k‖ ^ 2 * ν k := by
    simpa [ν, pow_mul] using summable_sq_of_hasSum hf R
  obtain ⟨hmem, hconv⟩ := hW.memLp_and_tendsto hν (g := fun z => f (a + z)) hf hs
  have hWn : MemLp (fun ω => W ω ^ n) 2 steinhausMeasure := hW.mom.memLp_pow n
  have hlim := tendsto_integral_mul_conj hmem hWn (fun N => hW.memLp_psum c (range N))
    (fun _ => hWn) hconv (by simp)
  have hval : ∀ N, n < N → ∫ ω, psum c N (W ω) * conj (W ω ^ n) ∂steinhausMeasure =
      c n * ν n := by
    intro N hN
    have e : ∀ ω, psum c N (W ω) * conj (W ω ^ n) =
        ∑ k ∈ range N, c k * (W ω ^ k * conj (W ω) ^ n) := by
      intro ω; rw [psum, sum_mul]; refine sum_congr rfl fun k _ => ?_; rw [map_pow]; ring
    simp_rw [e]
    rw [integral_finset_sum _ fun k _ => (hW.mom.integrable_pow_mul_conj_pow k n).const_mul _]
    simp_rw [integral_const_mul]
    have e2 : ∀ k, ∫ ω, W ω ^ k * conj (W ω) ^ n ∂steinhausMeasure =
        if k = n then (ν k : ℂ) else 0 := fun k => hW.orth k n
    simp_rw [e2, mul_ite, mul_zero]
    rw [sum_ite_eq' (range N) n, if_pos (mem_range.2 hN)]
  have hlim2 : Tendsto (fun N => ∫ ω, psum c N (W ω) * conj (W ω ^ n) ∂steinhausMeasure) atTop
      (𝓝 (c n * ν n)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop n] with N hN using (hval N hN).symm)
  have heq := tendsto_nhds_unique hlim hlim2
  -- bound the integral
  have hnormW : ∀ ω, ‖W ω‖ = R := fun ω => by
    rw [norm_circSample, abs_of_pos hR]
  have hbound : ‖∫ ω, f (a + W ω) * conj (W ω ^ n) ∂steinhausMeasure‖ ≤ M * R ^ n := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have : ∀ ω, ‖f (a + W ω) * conj (W ω ^ n)‖ ≤ M * R ^ n := fun ω => by
      rw [norm_mul, Complex.norm_conj, norm_pow, hnormW]
      exact mul_le_mul_of_nonneg_right (hM _ (hnormW ω)) (by positivity)
    simpa using integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _)
      (integrable_const (μ := steinhausMeasure) (M * R ^ n)) (Eventually.of_forall this)
  rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hν n)] at hbound
  have hRn : 0 < R ^ n := by positivity
  have e : ν n = R ^ n * R ^ n := by simp only [ν]; rw [← pow_mul, ← pow_add]; ring_nf
  rw [e] at hbound
  nlinarith

end Barycenter

-- ============================================================================
-- Source part: Bary18.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 18. Gauss's mean value theorem and Monte Carlo on circles (Section 8) -/

/-- Expectations of a Steinhaus variable are normalised integrals over `[0, 2π]`. -/
theorem integral_steinhaus (g : ℂ → ℂ) (hg : Continuous g) (j : ℕ) :
    ∫ ω, g (steinhaus j ω) ∂steinhausMeasure =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ θ in (0 : ℝ)..2 * Real.pi, g (Complex.exp (θ * Complex.I)) := by
  have hmap : steinhausMeasure.map (fun ω : SteinhausΩ => ω j) = AddCircle.haarAddCircle :=
    Measure.infinitePi_map_eval _ j
  have hc : Continuous fun x : AddCircle (2 * Real.pi) => g ((AddCircle.toCircle x : Circle) : ℂ) :=
    hg.comp (continuous_subtype_val.comp AddCircle.continuous_toCircle)
  have h1 := integral_map (μ := steinhausMeasure) (measurable_pi_apply j).aemeasurable
    hc.aestronglyMeasurable
  rw [hmap] at h1
  have h2 : ∫ ω, g (steinhaus j ω) ∂steinhausMeasure =
      ∫ ω, (fun x : AddCircle (2 * Real.pi) => g ((AddCircle.toCircle x : Circle) : ℂ)) (ω j)
        ∂steinhausMeasure := rfl
  rw [h2, ← h1, AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0, zero_add]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 2
  field_simp

variable {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

lemma Aimg_one {Ω : Type*} (X : ℕ → Ω → ℂ) (ω : Ω) : Aimg f a X 1 ω = f (a + X 0 ω) := by
  simp [Aimg]

/-- **Theorem 8.1 (Gauss), probabilistic form.** `E f(a + rU) = f(a)`. -/
theorem gauss_mean_circle (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) (r : ℝ) :
    ∫ ω, f (a + circSample r 0 ω) ∂steinhausMeasure = f a := by
  have hX := circSample_radialSample r
  have hs := hX.summable_of_bound (R := |r|)
    (Eventually.of_forall fun ω => (norm_circSample r 0 ω).le) hf
  have h := hX.integral_Aimg le_rfl hf hs
  simpa [Aimg_one] using h

/-- **Theorem 8.1 (Gauss's mean value theorem), (8.1), circle form.**
`f(a) = (2π)⁻¹ ∫_0^{2π} f(a + r e^{iθ}) dθ`. -/
theorem gauss_mean_value (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) (r : ℝ) :
    ((2 * Real.pi)⁻¹ : ℝ) • ∫ θ in (0 : ℝ)..2 * Real.pi, f (a + r * Complex.exp (θ * Complex.I))
      = f a := by
  have hcont : Continuous fun z => f (a + z) := continuous_of_hasSum hf
  have h := integral_steinhaus (fun z => f (a + r * z)) (hcont.comp (continuous_const.mul
    continuous_id)) 0
  rw [← h, ← gauss_mean_circle hf r]
  rfl

/-- **Theorem 8.1, (8.1), area form** (normalised area measure on the disk of radius `r`, written
through the substitution `z ↦ a + r z`): `E f(a + rZ) = f(a)` for `Z` uniform on the unit disk. -/
theorem gauss_mean_disk (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) (r : ℝ) :
    ∫ z, f (a + r * z) ∂diskLaw = f a := by
  have hX := disk_radialSample.const_mul (r : ℂ)
  have hb : ∀ᵐ ω ∂diskP, ‖(r : ℂ) * coord 0 ω‖ ≤ |r| := by
    have h0 : ∀ᵐ ω ∂diskP, ‖coord 0 ω‖ ≤ 1 := by
      have := diskLaw_ae_norm_le
      rw [← map_coord diskLaw 0] at this
      exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable this
    filter_upwards [h0] with ω hω
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg r) hω
  have hs := hX.summable_of_bound hb hf
  have h := hX.integral_Aimg le_rfl hf hs
  simp only [Aimg_one] at h
  have hcont : Continuous fun z => f (a + r * z) :=
    (continuous_of_hasSum hf).comp (continuous_const.mul continuous_id)
  have h2 := integral_map (μ := diskP) (measurable_pi_apply 0).aemeasurable
    hcont.aestronglyMeasurable
  rw [show (fun ω : ℕ → ℂ => ω 0) = coord 0 from rfl, map_coord] at h2
  rw [h2]; exact h

/-- **Theorem 8.1, (8.2).** The exact Monte Carlo error on circles:
`E|m⁻¹ ∑ f(a + r U_j) - f(a)|² = m⁻¹ ∑_{n ≥ 1} |c_n|² r^{2n}`. -/
theorem circle_variance (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) (r : ℝ) {m : ℕ}
    (hm : 1 ≤ m) :
    ∫ ω, ‖Aimg f a (circSample r) m ω - f a‖ ^ 2 ∂steinhausMeasure =
      (∑' n, ‖c (n + 1)‖ ^ 2 * r ^ (2 * (n + 1))) / m := by
  have hX := circSample_radialSample r
  have hs := hX.summable_of_bound (R := |r|)
    (Eventually.of_forall fun ω => (norm_circSample r 0 ω).le) hf
  rw [hX.integral_norm_sq_Aimg hm hf hs, Vf]
  congr 2; ext n; rw [radMom_circSample, ← pow_mul]

/-! ### Monte Carlo contour integration -/

/-- Coefficients of `z ↦ z f(a+z)`. -/
def shiftCoef (c : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => c n

lemma hasSum_shiftCoef (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) (z : ℂ) :
    HasSum (fun n => shiftCoef c n * z ^ n) ((0 + z) * f (a + (0 + z))) := by
  have h := (hf z).mul_left z
  rw [← hasSum_nat_add_iff' 1]
  simp only [range_one, sum_singleton, shiftCoef, zero_mul, sub_zero, zero_add]
  convert h using 1
  ext n; rw [pow_succ]; ring

/-- The Monte Carlo contour-integral estimator `C_m(f) = (2πi/m) ∑ f(Z_j)(Z_j - a)` with
`Z_j = a + r U_j`. -/
noncomputable def Cm (f : ℂ → ℂ) (a : ℂ) (r : ℝ) (m : ℕ) (ω : SteinhausΩ) : ℂ :=
  2 * Real.pi * Complex.I / m * ∑ j ∈ range m, f (a + circSample r j ω) * circSample r j ω

lemma Cm_eq (r : ℝ) (m : ℕ) (ω : SteinhausΩ) :
    Cm f a r m ω = 2 * Real.pi * Complex.I *
      Aimg (fun z => z * f (a + z)) 0 (circSample r) m ω := by
  simp only [Cm, Aimg, zero_add]
  rw [mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- **Proposition 8.2 (Monte Carlo contour integration), analytic case.** For `f` analytic,
`E C_m(f) = 0`, `E|C_m(f)|² = (4π²/m) ∑_{n ≥ 0} |c_n|² r^{2n+2}`, and the contour integral
`∮_{|z-a|=r} f(z) dz` vanishes. -/
theorem contour_analytic (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) (r : ℝ) {m : ℕ}
    (hm : 1 ≤ m) :
    ∫ ω, Cm f a r m ω ∂steinhausMeasure = 0 ∧
      ∫ ω, ‖Cm f a r m ω‖ ^ 2 ∂steinhausMeasure =
        4 * Real.pi ^ 2 / m * ∑' n, ‖c n‖ ^ 2 * r ^ (2 * n + 2) ∧
      circleIntegral f a r = 0 := by
  have hX := circSample_radialSample r
  have hg := hasSum_shiftCoef hf (a := a)
  have hb : ∀ᵐ ω ∂steinhausMeasure, ‖circSample r 0 ω‖ ≤ |r| :=
    Eventually.of_forall fun ω => (norm_circSample r 0 ω).le
  have hs := hX.summable_of_bound hb (f := fun z => z * f (a + z)) (a := 0) hg
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [Cm_eq]
    rw [integral_const_mul, hX.integral_Aimg hm hg hs]; simp
  · have hn : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le]
    have e : ∀ ω, ‖Cm f a r m ω‖ ^ 2 = (2 * Real.pi) ^ 2 *
        ‖Aimg (fun z => z * f (a + z)) 0 (circSample r) m ω - 0 * f (a + 0)‖ ^ 2 := by
      intro ω; rw [Cm_eq, norm_mul, hn]; simp; ring
    simp_rw [e]
    rw [integral_const_mul, hX.integral_norm_sq_Aimg hm hg hs, Vf]
    have e2 : ∀ n, ‖shiftCoef c (n + 1)‖ ^ 2 * radMom (circSample r 0) steinhausMeasure (n + 1)
        = ‖c n‖ ^ 2 * r ^ (2 * n + 2) := by
      intro n; rw [radMom_circSample, ← pow_mul, shiftCoef]; ring_nf
    simp_rw [e2]
    ring
  · -- `∮ f = 2π i E[rU f(a + rU)] = 0`
    have h := integral_steinhaus (fun z => Complex.I * (r * z * f (a + r * z)))
      (continuous_const.mul ((continuous_const.mul continuous_id).mul
        ((continuous_of_hasSum hf).comp (continuous_const.mul continuous_id)))) 0
    have hmean : ∫ ω, Complex.I * (r * steinhaus 0 ω * f (a + r * steinhaus 0 ω))
        ∂steinhausMeasure = 0 := by
      rw [integral_const_mul]
      have := hX.integral_Aimg (f := fun z => z * f (a + z)) (a := 0) le_rfl hg hs
      simp only [Aimg_one, zero_add, zero_mul] at this
      simp only [circSample] at this
      rw [this, mul_zero]
    rw [hmean] at h
    have h2 : ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.I * (r * Complex.exp (θ * Complex.I) *
        f (a + r * Complex.exp (θ * Complex.I))) = 0 := by
      have hpi : ((2 * Real.pi)⁻¹ : ℝ) ≠ 0 := by positivity
      exact (smul_eq_zero.1 h.symm).resolve_left hpi
    rw [circleIntegral]
    rw [← h2]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [deriv_circleMap, circleMap, zero_add, smul_eq_mul]
    ring

end Barycenter

-- ============================================================================
-- Source part: Bary19.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 19. Roots-of-unity rules (Proposition 8.3) -/

/-- The primitive `m`th root of unity `ζ = e^{2πi/m}`. -/
noncomputable def zeta (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

/-- The roots-of-unity filter `∑_{j<m} ζ^{jn} = m [m ∣ n]`. -/
lemma sum_zeta_pow {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    ∑ j ∈ range m, (zeta m ^ j) ^ n = if m ∣ n then (m : ℂ) else 0 := by
  have hprim : IsPrimitiveRoot (zeta m) m := Complex.isPrimitiveRoot_exp m hm
  have e : ∀ j, (zeta m ^ j) ^ n = (zeta m ^ n) ^ j := fun j => by rw [← pow_mul, ← pow_mul,
    mul_comm]
  simp_rw [e]
  split_ifs with h
  · have : zeta m ^ n = 1 := (hprim.pow_eq_one_iff_dvd n).2 h
    simp [this]
  · have hne : zeta m ^ n ≠ 1 := fun h' => h ((hprim.pow_eq_one_iff_dvd n).1 h')
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow, sub_self,
      zero_div]

/-- Filtered coefficients `c_n [m ∣ n, n ≠ 0]`. -/
def filtCoef (c : ℕ → ℂ) (m : ℕ) (n : ℕ) : ℂ := if m ∣ n ∧ n ≠ 0 then c n else 0

variable {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

/-- The roots-of-unity rule `T_m(f)(w) = m⁻¹ ∑_{j<m} f(a + w ζ^j)`. -/
noncomputable def Trule (f : ℂ → ℂ) (a : ℂ) (m : ℕ) (w : ℂ) : ℂ :=
  (m : ℂ)⁻¹ * ∑ j ∈ range m, f (a + w * zeta m ^ j)

lemma hasSum_Trule (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) {m : ℕ} (hm : 1 ≤ m)
    (w : ℂ) : HasSum (fun n => filtCoef c m n * w ^ n) (Trule f a m w - f a) := by
  have hm0 : m ≠ 0 := by omega
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
  have h1 := hasSum_sum (s := range m) fun j _ => hf (w * zeta m ^ j)
  have h2 := h1.mul_left ((m : ℂ)⁻¹)
  have h3 := h2.sub (hasSum_ite_eq 0 (c 0))
  rw [← coeff_zero_eq hf]
  convert h3 using 1
  ext n
  have e : ∑ j ∈ range m, c n * (w * zeta m ^ j) ^ n =
      c n * w ^ n * ∑ j ∈ range m, (zeta m ^ j) ^ n := by
    rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; rw [mul_pow]; ring
  rw [e, sum_zeta_pow hm0]
  have key : ∀ x : ℂ, (m : ℂ)⁻¹ * (x * m) = x := fun x => by field_simp
  by_cases hn : n = 0
  · subst hn; simp [filtCoef, key]
  · by_cases hd : m ∣ n
    · simp [filtCoef, hd, hn, key]
    · simp [filtCoef, hd, hn]

lemma filtCoef_support (c : ℕ → ℂ) {m : ℕ} (n : ℕ)
    (hn : n ∉ Set.range fun k : ℕ => (k + 1) * m) : filtCoef c m n = 0 := by
  simp only [filtCoef]
  split_ifs with h
  · exfalso
    obtain ⟨⟨t, rfl⟩, hne⟩ := h
    have ht : t ≠ 0 := by rintro rfl; simp at hne
    exact hn ⟨t - 1, by
      show (t - 1 + 1) * m = m * t
      rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero ht), mul_comm]⟩
  · rfl

lemma inj_mul {m : ℕ} (hm : 1 ≤ m) : Function.Injective fun k : ℕ => (k + 1) * m := by
  intro x y h
  have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < m) h
  omega

/-- **Proposition 8.3, the filter identity.**
`T_m(f) - f(a) = ∑_{k ≥ 1} c_{km} w^{km}` (here indexed by `k + 1`). -/
theorem Trule_sub (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) {m : ℕ} (hm : 1 ≤ m)
    (w : ℂ) :
    HasSum (fun k : ℕ => c ((k + 1) * m) * w ^ ((k + 1) * m)) (Trule f a m w - f a) := by
  have h := hasSum_Trule hf hm w
  rw [← (inj_mul hm).hasSum_iff (fun n hn => by rw [filtCoef_support c n hn, zero_mul])] at h
  convert h using 1
  ext k
  simp only [Function.comp, filtCoef]
  rw [if_pos ⟨Dvd.intro_left _ rfl, by positivity⟩]

/-- **Proposition 8.3, unbiasedness and variance.** With `U` a Steinhaus variable,
`E T_m(f)(rU) = f(a)` and `E|T_m(f)(rU) - f(a)|² = ∑_{k ≥ 1} |c_{km}|² r^{2km}`. -/
theorem Trule_mean_var (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) {m : ℕ}
    (hm : 1 ≤ m) (r : ℝ) :
    ∫ ω, Trule f a m (circSample r 0 ω) ∂steinhausMeasure = f a ∧
      ∫ ω, ‖Trule f a m (circSample r 0 ω) - f a‖ ^ 2 ∂steinhausMeasure =
        ∑' k : ℕ, ‖c ((k + 1) * m)‖ ^ 2 * r ^ (2 * ((k + 1) * m)) := by
  set ν : ℕ → ℝ := fun k => (r ^ 2) ^ k
  have hX := circSample_radialSample r
  have hW : OrthoMoments (circSample r 0) steinhausMeasure ν := by
    have := hX.orthoMoments_X 0
    have e : radMom (circSample r 0) steinhausMeasure = ν := funext (radMom_circSample r)
    rwa [e] at this
  have hν : ∀ k, 0 ≤ ν k := fun k => by positivity
  have hg := hasSum_Trule hf hm (a := a)
  have hs : Summable fun n => ‖filtCoef c m n‖ ^ 2 * ν n := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (hν n)) (fun n => ?_)
      (summable_sq_of_hasSum hf r)
    simp only [ν, ← pow_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by rw [pow_mul]; positivity)
    simp only [filtCoef]; split_ifs
    · rfl
    · simp
  have hmean : ∀ p, 1 ≤ p → ∫ ω, circSample r 0 ω ^ p ∂steinhausMeasure = 0 :=
    fun p hp => hX.integral_pow_eq_zero 0 hp
  constructor
  · have h := integral_comp_eq_zero hW hν (g := fun w => Trule f a m w - f a) hg hs
      (by simp [filtCoef]) hmean
    rw [integral_sub (by
      have := (hW.memLp_and_tendsto hν hg hs).1.integrable one_le_two
      exact (this.add (integrable_const (f a))).congr (Eventually.of_forall fun ω => by simp))
      (integrable_const _)] at h
    simpa [sub_eq_zero] using h
  · rw [hW.integral_norm_sq_comp hν (g := fun w => Trule f a m w - f a) hg hs]
    rw [← (inj_mul hm).tsum_eq (f := fun n => ‖filtCoef c m n‖ ^ 2 * ν n) (fun n hn => by
      by_contra h'
      exact hn (by simp [filtCoef_support c n h']))]
    congr 1; ext k
    simp only [filtCoef, ν, ← pow_mul]
    rw [if_pos ⟨Dvd.intro_left _ rfl, by positivity⟩]

/-- **Proposition 8.3, deterministic bound.** If `|f(a+z)| ≤ M` on `|z| = R` and `|w| ≤ r < R`,
then `|T_m(f)(w) - f(a)| ≤ M ρ/(1-ρ)` with `ρ = (r/R)^m`. -/
theorem Trule_bound (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) {m : ℕ} (hm : 1 ≤ m)
    {r R M : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hM : ∀ z : ℂ, ‖z‖ = R → ‖f (a + z)‖ ≤ M)
    {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖Trule f a m w - f a‖ ≤ M * (r / R) ^ m / (1 - (r / R) ^ m) := by
  have hR : 0 < R := hr.trans_lt hrR
  set ρ := (r / R) ^ m
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := pow_lt_one₀ (by positivity) ((div_lt_one hR).2 hrR) (by omega)
  have hsum : HasSum (fun k : ℕ => M * ρ * ρ ^ k) (M * ρ / (1 - ρ)) := by
    have := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_left (M * ρ)
    convert this using 1
  rw [← (Trule_sub hf hm w).tsum_eq]
  refine tsum_of_norm_bounded hsum fun k => ?_
  have hc := cauchy_estimate hf hR hM ((k + 1) * m)
  rw [norm_mul, norm_pow]
  have e1 : ρ * ρ ^ k = (r / R) ^ ((k + 1) * m) := by
    simp only [ρ]; rw [← pow_succ', ← pow_mul, mul_comm]
  have e : M * ρ * ρ ^ k = M / R ^ ((k + 1) * m) * r ^ ((k + 1) * m) := by
    rw [mul_assoc, e1, div_pow]; ring
  rw [e]
  have hRn : 0 < R ^ ((k + 1) * m) := by positivity
  have h1 : ‖c ((k + 1) * m)‖ ≤ M / R ^ ((k + 1) * m) := by rw [le_div_iff₀ hRn]; exact hc
  exact mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) hw _) (by positivity)
    ((norm_nonneg _).trans h1)

end Barycenter

-- ============================================================================
-- Source part: Bary20.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 20. Unit-disk estimates and Cauchy-type bounds (Corollary 4.6) -/

variable {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

lemma disk_ae_norm_le : ∀ᵐ ω ∂diskP, ‖coord 0 ω‖ ≤ 1 := by
  have := diskLaw_ae_norm_le
  rw [← map_coord diskLaw 0] at this
  exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable this

lemma diskMom_nonneg (n : ℕ) : 0 ≤ diskMom n := by rw [diskMom]; positivity

lemma Vf_disk (c : ℕ → ℂ) : Vf c diskMom = ∑' n : ℕ, ‖c (n + 1)‖ ^ 2 / (n + 2) := by
  rw [Vf]; congr 1; ext n; rw [diskMom]; push_cast; ring

lemma disk_summable (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) :
    Summable fun n => ‖c n‖ ^ 2 * radMom (coord 0) diskP n :=
  disk_radialSample.summable_of_bound disk_ae_norm_le hf

/-- **Corollary 4.6, (4.7), first identity.**
`E|A_m(f) - f(a)|² = m⁻¹ ∑_{n ≥ 1} |c_n|²/(n+1)` for unit-disk darts centred at `a`. -/
theorem disk_A (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) {m : ℕ} (hm : 1 ≤ m) :
    ∫ ω, ‖Aimg f a coord m ω - f a‖ ^ 2 ∂diskP = (∑' n : ℕ, ‖c (n + 1)‖ ^ 2 / (n + 2)) / m := by
  rw [disk_radialSample.integral_norm_sq_Aimg hm hf (disk_summable hf), radMom_disk, Vf_disk]

/-- **Corollary 4.6, (4.7), second estimate.** If `f - f(a)` has order `d`,
`E|f(ω_m) - f(a)|² ≤ κ_{m,d} ∑_{n ≥ 1} |c_n|²/(n+1)` (the terms with `n < d` vanish). -/
theorem disk_B (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) {m d : ℕ} (hm : 2 ≤ m)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) :
    ∫ ω, ‖Bimg f a coord m ω - f a‖ ^ 2 ∂diskP ≤
      kappa m d * ∑' n : ℕ, ‖c (n + 1)‖ ^ 2 / (n + 2) := by
  have h := disk_radialSample.main_le hm hf (disk_summable hf) hlow
  rwa [radMom_disk, Vf_disk] at h

/-- Cauchy's estimate gives `∑_{n ≥ 1} |c_n|²/(n+1) ≤ M_R² / (2(R²-1))`. -/
theorem Vf_disk_le (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) {R M : ℝ} (hR : 1 < R)
    (hM : ∀ z : ℂ, ‖z‖ = R → ‖f (a + z)‖ ≤ M) :
    Vf c diskMom ≤ M ^ 2 / (2 * (R ^ 2 - 1)) := by
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (R : ℂ) (by simp [hR0.le]))
  set q : ℝ := (R ^ 2)⁻¹
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have hgeo : HasSum (fun n : ℕ => M ^ 2 / 2 * q * q ^ n) (M ^ 2 / (2 * (R ^ 2 - 1))) := by
    have := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M ^ 2 / 2 * q)
    convert this using 1
    have h1 : R ^ 2 - 1 ≠ 0 := by nlinarith
    have h2 : R ^ 2 ≠ 0 := by positivity
    simp only [q]; field_simp
  have hle : ∀ n : ℕ, ‖c (n + 1)‖ ^ 2 * diskMom (n + 1) ≤ M ^ 2 / 2 * q * q ^ n := by
    intro n
    have hc := cauchy_estimate hf hR0 hM (n + 1)
    have hRn : 0 < R ^ (n + 1) := by positivity
    have h1 : ‖c (n + 1)‖ ^ 2 ≤ M ^ 2 / (R ^ (n + 1)) ^ 2 := by
      rw [le_div_iff₀ (by positivity), ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hc 2
    have h2 : diskMom (n + 1) ≤ 1 / 2 := by
      rw [diskMom, div_le_div_iff₀ (by positivity) (by norm_num)]; push_cast; linarith
    have e : M ^ 2 / 2 * q * q ^ n = M ^ 2 / (R ^ (n + 1)) ^ 2 * (1 / 2) := by
      simp only [q]; rw [mul_assoc, ← pow_succ', inv_pow, ← pow_mul, ← pow_mul,
        mul_comm 2 (n + 1)]
      field_simp
    rw [e]
    exact mul_le_mul h1 h2 (diskMom_nonneg _) (by positivity)
  rw [Vf, ← hgeo.tsum_eq]
  refine Summable.tsum_le_tsum hle ?_ hgeo.summable
  exact Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (diskMom_nonneg _)) hle
    hgeo.summable

/-- **Corollary 4.6, (4.8), first bound.** `E|A_m(f) - f(a)| ≤ M_R / √(2m(R²-1))`. -/
theorem disk_cauchy_A (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) {m : ℕ} (hm : 1 ≤ m)
    {R M : ℝ} (hR : 1 < R) (hM : ∀ z : ℂ, ‖z‖ = R → ‖f (a + z)‖ ≤ M) :
    ∫ ω, ‖Aimg f a coord m ω - f a‖ ∂diskP ≤ M / Real.sqrt (2 * m * (R ^ 2 - 1)) := by
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (R : ℂ) (by simp [hR0.le]))
  have h := (disk_radialSample.deviation_A hm hf (disk_summable hf) one_pos).1
  rw [radMom_disk] at h
  refine h.trans ?_
  have hV := Vf_disk_le hf hR hM
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hR2 : 0 < R ^ 2 - 1 := by nlinarith
  calc Real.sqrt (Vf c diskMom / m) ≤ Real.sqrt (M ^ 2 / (2 * (R ^ 2 - 1)) / m) :=
        Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hV hm'.le)
    _ = M / Real.sqrt (2 * m * (R ^ 2 - 1)) := by
        rw [div_div, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hM0]
        congr 2; ring

/-- **Corollary 4.6, (4.8), second bound.**
`E|f(ω_m) - f(a)| ≤ √(m κ_{m,d}) · M_R / √(2m(R²-1))`. -/
theorem disk_cauchy_B (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) {m d : ℕ}
    (hm : 2 ≤ m) (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) {R M : ℝ} (hR : 1 < R)
    (hM : ∀ z : ℂ, ‖z‖ = R → ‖f (a + z)‖ ≤ M) :
    ∫ ω, ‖Bimg f a coord m ω - f a‖ ∂diskP ≤
      Real.sqrt (m * kappa m d) * (M / Real.sqrt (2 * m * (R ^ 2 - 1))) := by
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (R : ℂ) (by simp [hR0.le]))
  have h := (disk_radialSample.deviation_B hm hf (disk_summable hf) hlow one_pos).1
  rw [radMom_disk] at h
  refine h.trans ?_
  have hV := Vf_disk_le hf hR hM
  have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hR2 : 0 < R ^ 2 - 1 := by nlinarith
  have hk : 0 ≤ kappa m d := kappa_pos (by omega) d |>.le
  calc Real.sqrt (kappa m d * Vf c diskMom) ≤ Real.sqrt (kappa m d * (M ^ 2 / (2 * (R ^ 2 - 1))))
        := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hV hk)
    _ = Real.sqrt (m * kappa m d) * (M / Real.sqrt (2 * m * (R ^ 2 - 1))) := by
        have e1 : M / Real.sqrt (2 * m * (R ^ 2 - 1)) = Real.sqrt (M ^ 2 / (2 * m * (R ^ 2 - 1)))
          := by rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hM0]
        rw [e1, ← Real.sqrt_mul (by positivity)]
        congr 1
        field_simp

end Barycenter

-- ============================================================================
-- Source part: Bary21.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 21. A random-polynomial reading (Proposition 9.1) -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace RadialSample

variable {X : ℕ → Ω → ℂ}

/-- Expectations of products of functions of independent darts factorise. -/
lemma integral_prod_range (hX : RadialSample X P) (g : ℕ → ℂ → ℂ) (hg : ∀ j, Measurable (g j))
    (hint : ∀ j, Integrable (fun ω => g j (X j ω)) P) (m : ℕ) :
    Integrable (fun ω => ∏ j ∈ range m, g j (X j ω)) P ∧
      ∫ ω, ∏ j ∈ range m, g j (X j ω) ∂P = ∏ j ∈ range m, ∫ ω, g j (X j ω) ∂P := by
  set Y : ℕ → Ω → ℂ := fun j ω => g j (X j ω)
  have hY : iIndepFun Y P := hX.indep.comp g hg
  have hYm : ∀ j, Measurable (Y j) := fun j => (hg j).comp (hX.meas j)
  induction m with
  | zero => simp
  | succ m ih =>
    have hind : IndepFun (∏ j ∈ range m, Y j) (Y m) P :=
      hY.indepFun_finset_prod_of_notMem hYm (by simp)
    have e : (fun ω => ∏ j ∈ range (m + 1), g j (X j ω)) = (∏ j ∈ range m, Y j) * Y m := by
      ext ω; simp [prod_range_succ, Y, Finset.prod_apply]
    have e2 : (∏ j ∈ range m, Y j) = fun ω => ∏ j ∈ range m, g j (X j ω) := by
      ext ω; simp [Y, Finset.prod_apply]
    rw [e]
    refine ⟨hind.integrable_mul (e2 ▸ ih.1) (hint m), ?_⟩
    rw [prod_range_succ, ← ih.2]
    have := hind.integral_mul_eq_mul_integral (e2 ▸ ih.1).1 (hint m).1
    rw [this, e2]

lemma integrable_X (hX : RadialSample X P) (j : ℕ) : Integrable (X j) P := by
  simpa using (hX.mom j).integrable_pow 1

lemma integrable_conj_X (hX : RadialSample X P) (j : ℕ) :
    Integrable (fun ω => conj (X j ω)) P := by
  simpa using (hX.mom j).integrable_pow_mul_conj_pow 0 1

lemma integrable_X_mul_conj (hX : RadialSample X P) (j : ℕ) :
    Integrable (fun ω => X j ω * conj (X j ω)) P := by
  simpa using (hX.mom j).integrable_pow_mul_conj_pow 1 1

/-- The elementary symmetric function `e_k(X_0, …, X_{m-1})`. -/
noncomputable def esym (X : ℕ → Ω → ℂ) (m k : ℕ) (ω : Ω) : ℂ :=
  ∑ S ∈ (range m).powersetCard k, ∏ j ∈ S, X j ω

/-- Mixed moments of monomials in distinct darts: `E[∏_S X_j \overline{∏_T X_j}] = δ_{ST} μ₁^{|S|}`. -/
lemma integral_prod_mul_conj_prod (hX : RadialSample X P) {m : ℕ} {S T : Finset ℕ}
    (hS : S ⊆ range m) (hT : T ⊆ range m) :
    Integrable (fun ω => (∏ j ∈ S, X j ω) * conj (∏ j ∈ T, X j ω)) P ∧
    ∫ ω, (∏ j ∈ S, X j ω) * conj (∏ j ∈ T, X j ω) ∂P =
      if S = T then ((radMom (X 0) P 1 ^ S.card : ℝ) : ℂ) else 0 := by
  classical
  set g : ℕ → ℂ → ℂ := fun j x => (if j ∈ S then x else 1) * (if j ∈ T then conj x else 1)
  have hg : ∀ j, Measurable (g j) := fun j => by
    simp only [g]; split_ifs <;> fun_prop
  have hint : ∀ j, Integrable (fun ω => g j (X j ω)) P := fun j => by
    simp only [g]; split_ifs
    · exact hX.integrable_X_mul_conj j
    · simpa using hX.integrable_X j
    · simpa using hX.integrable_conj_X j
    · simp
  have hval : ∀ j, ∫ ω, g j (X j ω) ∂P =
      if j ∈ S ∧ j ∈ T then (radMom (X 0) P 1 : ℂ) else if j ∈ S ∨ j ∈ T then 0 else 1 := by
    intro j
    have h0 : ∫ ω, X j ω ∂P = 0 := by simpa using hX.integral_pow_eq_zero j le_rfl
    simp only [g]
    by_cases hjS : j ∈ S <;> by_cases hjT : j ∈ T <;> simp only [hjS, hjT, if_true, if_false,
      and_self, true_or, or_true, and_true, and_false, mul_one, one_mul, or_self]
    · have := (hX.rot j).cmom_eq 1 1
      rw [if_pos rfl, hX.radMom_eq j 0] at this
      simpa [cmom] using this
    · exact h0
    · rw [integral_conj, h0, map_zero]
    · simp
  have hprod : ∀ ω, ∏ j ∈ range m, g j (X j ω) = (∏ j ∈ S, X j ω) * conj (∏ j ∈ T, X j ω) := by
    intro ω
    simp only [g, prod_mul_distrib, prod_ite_mem, map_prod]
    rw [inter_eq_right.2 hS, inter_eq_right.2 hT]
  obtain ⟨hI, hE⟩ := hX.integral_prod_range g hg hint m
  simp_rw [hprod] at hI hE
  refine ⟨hI, ?_⟩
  rw [hE]
  simp_rw [hval]
  split_ifs with hST
  · subst hST
    rw [prod_congr rfl fun j _ => (by by_cases h : j ∈ S <;> simp [h] :
      (if j ∈ S ∧ j ∈ S then (radMom (X 0) P 1 : ℂ) else if j ∈ S ∨ j ∈ S then 0 else 1) =
        if j ∈ S then (radMom (X 0) P 1 : ℂ) else 1)]
    rw [prod_ite_mem, inter_eq_right.2 hS, prod_const]; push_cast; rfl
  · obtain ⟨j, hj⟩ : ∃ j, (j ∈ S ∧ j ∉ T) ∨ (j ∈ T ∧ j ∉ S) := by
      by_contra h
      push_neg at h
      exact hST (Finset.ext fun j => ⟨fun hj => (h j).1 hj, fun hj => by
        by_contra hjS; exact absurd ((h j).2 hj) hjS⟩)
    have hjm : j ∈ range m := by rcases hj with h | h; exacts [hS h.1, hT h.1]
    refine prod_eq_zero hjm ?_
    rcases hj with h | h
    · simp [h.1, h.2]
    · simp [h.1, h.2]

/-- **Proposition 9.1 (Coefficients for rotationally invariant zeros), means.**
`E e_k = δ_{k0}`. -/
theorem integral_esym (hX : RadialSample X P) (m k : ℕ) :
    ∫ ω, esym X m k ω ∂P = if k = 0 then 1 else 0 := by
  have h : ∀ S ∈ (range m).powersetCard k, ∫ ω, ∏ j ∈ S, X j ω ∂P = if S = ∅ then 1 else 0 := by
    intro S hS
    have := (hX.integral_prod_mul_conj_prod (m := m) (mem_powersetCard.1 hS).1
      (empty_subset _)).2
    simp only [prod_empty, map_one, mul_one] at this
    rw [this]; split_ifs with h
    · simp [h]
    · rfl
  have hint : ∀ S ∈ (range m).powersetCard k, Integrable (fun ω => ∏ j ∈ S, X j ω) P := by
    intro S hS
    simpa using (hX.integral_prod_mul_conj_prod (m := m) (mem_powersetCard.1 hS).1
      (empty_subset _)).1
  simp only [esym]
  rw [integral_finset_sum _ hint, sum_congr rfl h]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [if_neg (by omega)]
    refine sum_eq_zero fun S hS => ?_
    rw [if_neg]
    rintro rfl
    simp at hS; omega

/-- **Proposition 9.1, covariances.** `E[e_k \overline{e_l}] = δ_{kl} C(m,k) μ₁^k`. -/
theorem integral_esym_mul_conj (hX : RadialSample X P) (m k l : ℕ) :
    ∫ ω, esym X m k ω * conj (esym X m l ω) ∂P =
      if k = l then (((m.choose k : ℕ) : ℝ) * radMom (X 0) P 1 ^ k : ℝ) else 0 := by
  have hexp : ∀ ω, esym X m k ω * conj (esym X m l ω) = ∑ S ∈ (range m).powersetCard k,
      ∑ T ∈ (range m).powersetCard l, (∏ j ∈ S, X j ω) * conj (∏ j ∈ T, X j ω) := by
    intro ω; simp only [esym, map_sum, sum_mul_sum]
  simp_rw [hexp]
  have key := fun S (hS : S ∈ (range m).powersetCard k) T (hT : T ∈ (range m).powersetCard l) =>
    hX.integral_prod_mul_conj_prod (mem_powersetCard.1 hS).1 (mem_powersetCard.1 hT).1
  rw [integral_finset_sum _ fun S hS => integrable_finset_sum _ fun T hT => (key S hS T hT).1]
  rw [sum_congr rfl fun S hS => integral_finset_sum _ fun T hT => (key S hS T hT).1]
  rw [sum_congr rfl fun S hS => sum_congr rfl fun T hT => (key S hS T hT).2]
  split_ifs with hkl
  · subst hkl
    rw [sum_congr rfl fun S hS => (by rw [sum_ite_eq, if_pos hS, (mem_powersetCard.1 hS).2] :
      _ = ((radMom (X 0) P 1 ^ k : ℝ) : ℂ))]
    rw [sum_const, card_powersetCard, card_range, nsmul_eq_mul]
    push_cast; ring
  · refine sum_eq_zero fun S hS => sum_eq_zero fun T hT => if_neg ?_
    rintro rfl
    exact hkl ((mem_powersetCard.1 hS).2.symm.trans (mem_powersetCard.1 hT).2)

/-- **Proposition 9.1, the polynomial.** `E|P_m(z)|² = (|z|² + μ₁)^m` for
`P_m(z) = ∏_{j<m} (z - X_j)`. -/
theorem integral_norm_sq_poly (hX : RadialSample X P) (m : ℕ) (z : ℂ) :
    ∫ ω, ‖∏ j ∈ range m, (z - X j ω)‖ ^ 2 ∂P = (‖z‖ ^ 2 + radMom (X 0) P 1) ^ m := by
  set g : ℕ → ℂ → ℂ := fun _ x => (z - x) * conj (z - x)
  have hg : ∀ j, Measurable (g j) := fun j => by simp only [g]; fun_prop
  have hint : ∀ j, Integrable (fun ω => g j (X j ω)) P := fun j => by
    have h1 := hX.integrable_X_mul_conj j
    have h2 := hX.integrable_X j
    have h3 := hX.integrable_conj_X j
    have e : (fun ω => g j (X j ω)) = fun ω => (z * conj z - z * conj (X j ω)
        - conj z * X j ω) + X j ω * conj (X j ω) := by
      ext ω; simp only [g, map_sub]; ring
    rw [e]
    exact (((integrable_const _).sub (h3.const_mul z)).sub (h2.const_mul _)).add h1
  have hval : ∀ j, ∫ ω, g j (X j ω) ∂P = ((‖z‖ ^ 2 + radMom (X 0) P 1 : ℝ) : ℂ) := by
    intro j
    have h0 : ∫ ω, X j ω ∂P = 0 := by simpa using hX.integral_pow_eq_zero j le_rfl
    have hc : ∫ ω, X j ω * conj (X j ω) ∂P = (radMom (X 0) P 1 : ℂ) := by
      have := (hX.rot j).cmom_eq 1 1
      rw [if_pos rfl, hX.radMom_eq j 0] at this
      simpa [cmom] using this
    have h1 := hX.integrable_X_mul_conj j
    have h2 := hX.integrable_X j
    have h3 := hX.integrable_conj_X j
    have e : (fun ω => g j (X j ω)) = fun ω => (z * conj z - z * conj (X j ω)
        - conj z * X j ω) + X j ω * conj (X j ω) := by
      ext ω; simp only [g, map_sub]; ring
    have hB : Integrable (fun ω => z * conj z - z * conj (X j ω)) P :=
      (integrable_const _).sub (h3.const_mul z)
    have hA : Integrable (fun ω => z * conj z - z * conj (X j ω) - conj z * X j ω) P :=
      hB.sub (h2.const_mul _)
    rw [e, integral_add hA h1, integral_sub hB (h2.const_mul _),
      integral_sub (integrable_const _) (h3.const_mul z), integral_const (z * conj z),
      integral_const_mul, integral_const_mul, integral_conj, h0, hc]
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  obtain ⟨-, hE⟩ := hX.integral_prod_range g hg hint m
  have hprod : ∀ ω, ((‖∏ j ∈ range m, (z - X j ω)‖ ^ 2 : ℝ) : ℂ) = ∏ j ∈ range m, g j (X j ω) := by
    intro ω
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_prod, ← prod_mul_distrib]
  have h := congrArg Complex.re hE
  simp_rw [← hprod] at h
  rw [integral_complex_ofReal] at h
  simp only [Complex.ofReal_re] at h
  rw [h, prod_congr rfl fun j _ => hval j, prod_const, card_range, ← Complex.ofReal_pow,
    Complex.ofReal_re]

end RadialSample

/-- **Proposition 9.1, unit-disk zeros.** `E|e_k|² = C(m,k) 2^{-k}` and the total coefficient
energy is `E ∑_k |e_k|² = (3/2)^m`. -/
theorem disk_esym (m : ℕ) :
    (∀ k, ∫ ω, ‖RadialSample.esym coord m k ω‖ ^ 2 ∂diskP = (m.choose k : ℝ) / 2 ^ k) ∧
      ∑ k ∈ range (m + 1), ∫ ω, ‖RadialSample.esym coord m k ω‖ ^ 2 ∂diskP = (3 / 2) ^ m := by
  have hk : ∀ k, ∫ ω, ‖RadialSample.esym coord m k ω‖ ^ 2 ∂diskP = (m.choose k : ℝ) / 2 ^ k := by
    intro k
    have h := disk_radialSample.integral_esym_mul_conj m k k
    rw [if_pos rfl, radMom_disk] at h
    have e : ∀ ω, RadialSample.esym coord m k ω * conj (RadialSample.esym coord m k ω) =
        ((‖RadialSample.esym coord m k ω‖ ^ 2 : ℝ) : ℂ) := fun ω => by
      rw [Complex.ofReal_pow, Complex.mul_conj']
    simp_rw [e, integral_complex_ofReal] at h
    have h' := Complex.ofReal_injective h
    rw [h']; simp [diskMom]; ring
  refine ⟨hk, ?_⟩
  simp_rw [hk]
  have := (add_pow (1 / 2 : ℝ) 1 m)
  rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num] at this
  rw [this]
  refine sum_congr rfl fun k _ => ?_
  rw [one_pow, mul_one, div_pow, one_pow]; ring

end Barycenter

-- ============================================================================
-- Source part: Bary22.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 22. Exact rational evaluation of `q_{m,n}`: Table 2.1 and Example 5.2 -/

/-- Row `(Qsum μ m 0, …, Qsum μ m N)` computed by dynamic programming over `m` (rational). -/
def qrowQ (μ : ℕ → ℚ) (N : ℕ) : ℕ → List ℚ
  | 0 => (List.range (N + 1)).map fun n => if n = 0 then 1 else 0
  | m + 1 =>
    let prev := qrowQ μ N m
    (List.range (N + 1)).map fun n =>
      ∑ i ∈ range (n + 1), ((n.choose i : ℕ) : ℚ) ^ 2 * μ i * prev.getD (n - i) 0

lemma getD_map_range {F : ℕ → ℚ} {N n : ℕ} (hn : n ≤ N) :
    ((List.range (N + 1)).map F).getD n 0 = F n := by
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

lemma qrowQ_spec (μ : ℕ → ℚ) (N m : ℕ) {n : ℕ} (hn : n ≤ N) :
    (((qrowQ μ N m).getD n 0 : ℚ) : ℝ) = Qsum (fun k => (μ k : ℝ)) m n := by
  induction m generalizing n with
  | zero =>
    rw [qrowQ, getD_map_range hn, Qsum_zero_left]
    split_ifs <;> simp
  | succ m ih =>
    rw [qrowQ, getD_map_range hn, Qsum_succ]
    push_cast
    refine sum_congr rfl fun i hi => ?_
    rw [ih (by omega)]

/-- The rational disk moments `1/(k+1)`. -/
def diskMomQ (k : ℕ) : ℚ := 1 / (k + 1)

lemma diskMom_eq_cast : diskMom = fun k => ((diskMomQ k : ℚ) : ℝ) := by
  ext k; simp [diskMom, diskMomQ]

/-- Exact evaluation of `q_{m,n}` for the unit disk. -/
lemma qmom_disk_eq (m n : ℕ) :
    qmom diskMom m n = (((qrowQ diskMomQ n m).getD n 0 / (m : ℚ) ^ (2 * n) : ℚ) : ℝ) := by
  rw [qmom, diskMom_eq_cast, ← qrowQ_spec diskMomQ n m le_rfl]
  push_cast; rfl

/-- Rational value of `q_{m,n}` for the unit disk. -/
def qdiskQ (m n : ℕ) : ℚ := (qrowQ diskMomQ n m).getD n 0 / (m : ℚ) ^ (2 * n)

lemma qmom_disk_eq' (m n : ℕ) : qmom diskMom m n = ((qdiskQ m n : ℚ) : ℝ) := qmom_disk_eq m n

/-- **Table 2.1, column `E|ω_m^n|²`, `m = 10`** (exact values; the table rounds them). -/
theorem table_disk_m10 :
    qmom diskMom 10 1 = 1 / 20 ∧ qmom diskMom 10 2 = 29 / 6000 ∧
    qmom diskMom 10 3 = 271 / 400000 ∧ qmom diskMom 10 4 = 6121 / 50000000 ∧
    qmom diskMom 10 5 = 80213 / 3000000000 := by
  simp only [qmom_disk_eq']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [(by native_decide : qdiskQ 10 1 = 1 / 20)]; norm_num
  · rw [(by native_decide : qdiskQ 10 2 = 29 / 6000)]; norm_num
  · rw [(by native_decide : qdiskQ 10 3 = 271 / 400000)]; norm_num
  · rw [(by native_decide : qdiskQ 10 4 = 6121 / 50000000)]; norm_num
  · rw [(by native_decide : qdiskQ 10 5 = 80213 / 3000000000)]; norm_num

/-- **Table 2.1, column `E|ω_m^n|²`, `m = 100`** (exact values; the table rounds them). -/
theorem table_disk_m100 :
    qmom diskMom 100 1 = 1 / 200 ∧ qmom diskMom 100 2 = 299 / 6000000 ∧
    qmom diskMom 100 3 = 29701 / 40000000000 ∧
    qmom diskMom 100 4 = 3675623 / 250000000000000 ∧
    qmom diskMom 100 5 = 1088058263 / 3000000000000000000 := by
  simp only [qmom_disk_eq']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [(by native_decide : qdiskQ 100 1 = 1 / 200)]; norm_num
  · rw [(by native_decide : qdiskQ 100 2 = 299 / 6000000)]; norm_num
  · rw [(by native_decide : qdiskQ 100 3 = 29701 / 40000000000)]; norm_num
  · rw [(by native_decide : qdiskQ 100 4 = 3675623 / 250000000000000)]; norm_num
  · rw [(by native_decide : qdiskQ 100 5 = 1088058263 / 3000000000000000000)]; norm_num

/-- Taylor coefficients of the rigid polynomial `g(z) = 1 + 5 z^{10}`. -/
def rigidCoef (n : ℕ) : ℂ := if n = 0 then 1 else if n = 10 then 5 else 0

/-- The rigid polynomial `g(z) = 1 + 5 z^{10}`. -/
def rigidPoly (w : ℂ) : ℂ := 1 + 5 * w ^ 10

lemma hasSum_rigid (z : ℂ) :
    HasSum (fun n => rigidCoef n * z ^ n) (rigidPoly (0 + z)) := by
  have h := (hasSum_ite_eq 0 (1 : ℂ)).add (hasSum_ite_eq 10 (5 * z ^ 10))
  simp only [zero_add, rigidPoly]
  convert h using 1
  ext n
  by_cases h0 : n = 0
  · subst h0; simp [rigidCoef]
  · by_cases h10 : n = 10
    · subst h10; simp [rigidCoef]
    · simp [rigidCoef, h0, h10]

/-- **Example 5.2 (a rigid polynomial).** For `g(z) = 1 + 5z^{10}` and unit-disk darts:
`E|A_m(g) - 1|² = 25/(11m)`, `E|B_m(g) - 1|² = 25 q_{m,10} ≤ 25 κ_{m,10}/11`, and
`m^{10} E|B_m(g) - 1|² → 25 · 10!/2^{10}`. -/
theorem rigid_example {m : ℕ} (hm : 1 ≤ m) :
    ∫ ω, ‖Aimg rigidPoly 0 coord m ω - 1‖ ^ 2 ∂diskP = 25 / (11 * m) ∧
    ∫ ω, ‖Bimg rigidPoly 0 coord m ω - 1‖ ^ 2 ∂diskP = 25 * qmom diskMom m 10 ∧
    25 * qmom diskMom m 10 ≤ 25 * kappa m 10 / 11 ∧
    Tendsto (fun m : ℕ => (m : ℝ) ^ 10 *
      ∫ ω, ‖Bimg rigidPoly 0 coord m ω - 1‖ ^ 2 ∂diskP) atTop
      (𝓝 (25 * (Nat.factorial 10 : ℝ) / 2 ^ 10)) := by
  have hf := hasSum_rigid
  have hs := disk_summable hf
  have e1 : rigidPoly 0 = 1 := by norm_num [rigidPoly]
  have hc : ∀ n, n ≠ 9 → ‖rigidCoef (n + 1)‖ = 0 := fun n hn => by
    have : n + 1 ≠ 10 := by omega
    simp [rigidCoef, this]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := disk_A hf hm
    rw [e1] at h
    rw [h, tsum_eq_single 9 fun n hn => by rw [hc n hn]; simp]
    norm_num [rigidCoef]; field_simp
  · have h := disk_radialSample.integral_norm_sq_Bimg hm hf hs
    rw [e1, radMom_disk] at h
    rw [h, tsum_eq_single 9 fun n hn => by rw [hc n hn]; simp]
    norm_num [rigidCoef]
  · have h := disk_radialSample.qmom_le m 10
    rw [radMom_disk] at h
    have : diskMom 10 = 1 / 11 := by norm_num [diskMom]
    rw [this] at h
    linarith
  · have h := disk_radialSample.tendsto_scaled_mse hf hs (d := 10) (by norm_num)
      (fun n h1 h2 => by
        have h3 : n ≠ 0 := by omega
        have h4 : n ≠ 10 := by omega
        simp [rigidCoef, h3, h4])
    rw [e1, radMom_disk] at h
    convert h using 2
    norm_num [rigidCoef, diskMom]

/-- **Example 5.2 (a rigid polynomial), numerical values.**
`25 q_{10,10} = 8637602752549/(44·10^{17}) ≈ 1.96·10^{-6}` and `7.6·10^{-16} < 25 q_{100,10} <
7.7·10^{-16}`. -/
theorem rigid_values :
    25 * qmom diskMom 10 10 = 8637602752549 / (44 * 10 ^ 17) ∧
    76 / 10 ^ 17 < 25 * qmom diskMom 100 10 ∧ 25 * qmom diskMom 100 10 < 77 / 10 ^ 17 := by
  simp only [qmom_disk_eq']
  refine ⟨?_, ?_, ?_⟩
  · rw [(by native_decide : qdiskQ 10 10 = 8637602752549 / (44 * 10 ^ 17) / 25)]; norm_num
  · have h : (76 / 10 ^ 17 : ℚ) < 25 * qdiskQ 100 10 := by native_decide
    have := (Rat.cast_lt (K := ℝ)).2 h
    push_cast at this ⊢; linarith
  · have h : 25 * qdiskQ 100 10 < (77 / 10 ^ 17 : ℚ) := by native_decide
    have := (Rat.cast_lt (K := ℝ)).2 h
    push_cast at this ⊢; linarith

end Barycenter

-- ============================================================================
-- Source part: Bary23.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 23. Entire maps under bounded sampling (Theorem 7.2, last claim) and the Gaussian
example (Example 5.3) -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

namespace IIDSample

variable {X : ℕ → Ω → ℂ}

/-- **Theorem 7.2, extension to entire maps.** If `|X| ≤ r` almost surely and all analytic
moments `E X^n` (`n ≥ 1`) vanish, then `E f(a + S_m) = f(a)` for every entire `f` and `m ≥ 1`
(for `m = 1` this is `E f(a + X) = f(a)`). -/
theorem integral_entire_of_vanishing (hX : IIDSample X P) {r : ℝ}
    (hr : ∀ j, ∀ᵐ ω ∂P, ‖X j ω‖ ≤ r) (hvan : ∀ n, 1 ≤ n → anMom (X 0) P n = 0)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z))) {m : ℕ} (hm : 1 ≤ m) :
    ∫ ω, f (a + Scen X m ω) ∂P = f a := by
  have h0 : anMom (X 0) P 0 = 1 := anMom_zero (X := X) 0
  -- moments of `S_m`
  have hmom : ∀ n, 1 ≤ n → ∫ ω, Scen X m ω ^ n ∂P = 0 := by
    intro n hn
    rw [hX.integral_Scen_pow, Bsum_of_vanishing _ h0 hn (fun i hi _ => hvan i hi), hvan n hn]
    simp
  -- boundedness of `S_m`
  have hS : ∀ᵐ ω ∂P, ‖Scen X m ω‖ ≤ r := by
    have hall : ∀ᵐ ω ∂P, ∀ j, ‖X j ω‖ ≤ r := ae_all_iff.2 hr
    filter_upwards [hall] with ω hω
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    rw [Scen, norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hm']
    calc ‖∑ j ∈ range m, X j ω‖ ≤ ∑ j ∈ range m, ‖X j ω‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range m, r := sum_le_sum fun j _ => hω j
      _ = m * r := by simp
  have hr0 : 0 ≤ r ∨ ∀ᵐ ω ∂P, False := by
    by_cases h : 0 ≤ r
    · exact Or.inl h
    · right; filter_upwards [hr 0] with ω hω; exact h ((norm_nonneg _).trans hω)
  rcases hr0 with hr0 | hfalse
  swap
  · exfalso
    have := measure_univ (μ := P)
    rw [ae_iff] at hfalse
    simp at hfalse
  have hsumm := summable_norm_mul_pow_of_hasSum hf r hr0
  set C := ∑' n, ‖c n‖ * r ^ n
  have hmeasS : Measurable (Scen X m) := measurable_const.mul
    (Finset.measurable_sum _ fun j _ => hX.meas j)
  -- partial sums
  set F : ℕ → Ω → ℂ := fun N ω => ∑ n ∈ range N, c n * Scen X m ω ^ n
  have hFint : ∀ N, ∫ ω, F N ω ∂P = if N = 0 then 0 else c 0 := by
    intro N
    simp only [F]
    rw [integral_finset_sum _ fun n _ => ((hX.allMoments_Scen m).integrable_pow n).const_mul _]
    simp_rw [integral_const_mul]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · rw [if_neg (by omega), sum_eq_single 0 (fun n _ hn => by rw [hmom n (by omega), mul_zero])
        (fun h => absurd (mem_range.2 hN) h)]
      simp
  have hlimF : ∀ ω, Tendsto (fun N => F N ω) atTop (𝓝 (f (a + Scen X m ω))) :=
    fun ω => (hf (Scen X m ω)).tendsto_sum_nat
  have hbound : ∀ N, ∀ᵐ ω ∂P, ‖F N ω‖ ≤ C := by
    intro N
    filter_upwards [hS] with ω hω
    calc ‖F N ω‖ ≤ ∑ n ∈ range N, ‖c n * Scen X m ω ^ n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range N, ‖c n‖ * r ^ n := sum_le_sum fun n _ => by
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hω n)
            (norm_nonneg _)
      _ ≤ C := hsumm.sum_le_tsum _ fun n _ => by positivity
  have hFmeas : ∀ N, AEStronglyMeasurable (F N) P := fun N =>
    (Finset.measurable_sum _ fun n _ => measurable_const.mul (hmeasS.pow_const n)).aestronglyMeasurable
  have hlim := tendsto_integral_of_dominated_convergence (fun _ => C) hFmeas
    (integrable_const C) hbound (Eventually.of_forall hlimF)
  have hlim2 : Tendsto (fun N => ∫ ω, F N ω ∂P) atTop (𝓝 (c 0)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [hFint N, if_neg (by omega)])
  rw [tendsto_nhds_unique hlim hlim2, coeff_zero_eq hf]

end IIDSample

lemma hasSum_exp_real (x : ℝ) : HasSum (fun n : ℕ => x ^ n / n.factorial) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x

lemma hasSum_exp_real_succ (x : ℝ) :
    HasSum (fun n : ℕ => x ^ (n + 1) / (n + 1).factorial) (Real.exp x - 1) := by
  have h := (hasSum_nat_add_iff' 1).2 (hasSum_exp_real x)
  simpa using h

/-- Taylor coefficients `t^n/n!` of `z ↦ e^{tz}`. -/
noncomputable def expCoef (t : ℂ) (n : ℕ) : ℂ := t ^ n / n.factorial

/-- The map `w ↦ e^{t(w-a)}`, i.e. `f(a+z) = e^{tz}`. -/
noncomputable def expShift (t a : ℂ) (w : ℂ) : ℂ := Complex.exp (t * (w - a))

lemma hasSum_expCoef (t a : ℂ) (z : ℂ) :
    HasSum (fun n => expCoef t n * z ^ n) (expShift t a (a + z)) := by
  have h : HasSum (fun n : ℕ => (t * z) ^ n / n.factorial) (Complex.exp (t * z)) := by
    rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.expSeries_div_hasSum_exp (t * z)
  simp only [expShift, add_sub_cancel_left]
  convert h using 1
  ext n; rw [expCoef, mul_pow]; ring

namespace RadialSample

variable {X : ℕ → Ω → ℂ}

/-- **Example 5.3 (unbounded sampling).** For any radial sample whose radial moments are those of
a complex Gaussian, `μ_n = n! v^n`, and `f(a+z) = e^{tz}`, with `x = v|t|²`:
`E|A_m(f) - 1|² = (e^x - 1)/m` and `E|B_m(f) - 1|² = E[(A_m(f)-1)\overline{(B_m(f)-1)}] =
e^{x/m} - 1`. -/
theorem gaussian_example (hX : RadialSample X P) {v : ℝ}
    (hμ : ∀ n, radMom (X 0) P n = n.factorial * v ^ n) (t : ℂ) {m : ℕ} (hm : 1 ≤ m) :
    ∫ ω, ‖Aimg (expShift t a) a X m ω - 1‖ ^ 2 ∂P =
      (Real.exp (v * ‖t‖ ^ 2) - 1) / m ∧
    ∫ ω, ‖Bimg (expShift t a) a X m ω - 1‖ ^ 2 ∂P =
      Real.exp (v * ‖t‖ ^ 2 / m) - 1 ∧
    ∫ ω, (Aimg (expShift t a) a X m ω - 1) *
      conj (Bimg (expShift t a) a X m ω - 1) ∂P =
      ((Real.exp (v * ‖t‖ ^ 2 / m) - 1 : ℝ) : ℂ) := by
  have hf := hasSum_expCoef t a
  have hfa : expShift t a a = 1 := by simp [expShift]
  have hμf : radMom (X 0) P = fun n => (n.factorial : ℝ) * v ^ n := funext hμ
  have hterm : ∀ n, ‖expCoef t n‖ ^ 2 * radMom (X 0) P n = (v * ‖t‖ ^ 2) ^ n / n.factorial := by
    intro n
    rw [hμ, expCoef, norm_div, norm_pow, Complex.norm_natCast]
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp; ring
  have hs : Summable fun n => ‖expCoef t n‖ ^ 2 * radMom (X 0) P n := by
    simp_rw [hterm]; exact (hasSum_exp_real _).summable
  have hm' : (m : ℝ) ≠ 0 := by have : (0 : ℝ) < m := by exact_mod_cast hm
                               positivity
  refine ⟨?_, ?_, ?_⟩
  · have h := hX.integral_norm_sq_Aimg hm hf hs
    rw [hfa] at h
    rw [h, Vf]
    simp_rw [hterm]
    rw [(hasSum_exp_real_succ _).tsum_eq]
  · have h := hX.integral_norm_sq_Bimg hm hf hs
    rw [hfa] at h
    rw [h, hμf]
    have e : ∀ n : ℕ, ‖expCoef t (n + 1)‖ ^ 2 *
        qmom (fun i => (i.factorial : ℝ) * v ^ i) m (n + 1) =
        (v * ‖t‖ ^ 2 / m) ^ (n + 1) / (n + 1).factorial := by
      intro n
      rw [qmom_gaussian v hm, expCoef, norm_div, norm_pow, Complex.norm_natCast]
      have : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
      field_simp; ring
    simp_rw [e]
    rw [(hasSum_exp_real_succ _).tsum_eq]
  · have h := hX.integral_cov_AB hm hf hs
    rw [hfa] at h
    rw [h]
    congr 1
    have e : ∀ n : ℕ, ‖expCoef t (n + 1)‖ ^ 2 * (radMom (X 0) P (n + 1) / (m : ℝ) ^ (n + 1)) =
        (v * ‖t‖ ^ 2 / m) ^ (n + 1) / (n + 1).factorial := by
      intro n
      rw [hμ, expCoef, norm_div, norm_pow, Complex.norm_natCast, div_pow]
      have : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
      have key : (m : ℝ) * m ^ n * (m : ℝ)⁻¹ * ((m : ℝ)⁻¹) ^ n = 1 := by
        rw [inv_pow]; field_simp
      field_simp
      linear_combination (-(‖t‖ ^ 2 * ‖t‖ ^ (n * 2) * v * v ^ n)) * key
    simp_rw [e]
    rw [(hasSum_exp_real_succ _).tsum_eq]

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary24.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 24. Monte Carlo contour integration for continuous integrands (Proposition 8.2) -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma integrable_of_bound {Y : Ω → ℂ} (hY : Measurable Y) {B : ℝ} (hb : ∀ ω, ‖Y ω‖ ≤ B) :
    Integrable Y P :=
  Integrable.of_bound hY.aestronglyMeasurable B (Eventually.of_forall hb)

/-- Variance of the mean of bounded i.i.d. complex variables:
`E|m⁻¹ ∑_{j<m} Y_j - E Y|² = (E|Y|² - |E Y|²)/m`. -/
theorem iid_variance {Y : ℕ → Ω → ℂ} (hind : iIndepFun Y P)
    (hid : ∀ j, IdentDistrib (Y j) (Y 0) P P) (hmeas : ∀ j, Measurable (Y j)) {B : ℝ}
    (hb : ∀ j ω, ‖Y j ω‖ ≤ B) {m : ℕ} (hm : 1 ≤ m) :
    ∫ ω, ‖(m : ℂ)⁻¹ * ∑ j ∈ range m, Y j ω - ∫ ω', Y 0 ω' ∂P‖ ^ 2 ∂P =
      (∫ ω, ‖Y 0 ω‖ ^ 2 ∂P - ‖∫ ω, Y 0 ω ∂P‖ ^ 2) / m := by
  set μ := ∫ ω, Y 0 ω ∂P
  have hμj : ∀ j, ∫ ω, Y j ω ∂P = μ := fun j => (hid j).integral_eq
  set Z : ℕ → Ω → ℂ := fun j ω => Y j ω - μ
  have hZmeas : ∀ j, Measurable (Z j) := fun j => (hmeas j).sub measurable_const
  have hZb : ∀ j ω, ‖Z j ω‖ ≤ B + ‖μ‖ := fun j ω => (norm_sub_le _ _).trans (by linarith [hb j ω])
  have hZint : ∀ j, Integrable (Z j) P := fun j => integrable_of_bound (hZmeas j) (hZb j)
  have hZmean : ∀ j, ∫ ω, Z j ω ∂P = 0 := fun j => by
    simp only [Z]; rw [integral_sub (integrable_of_bound (hmeas j) (hb j)) (integrable_const _),
      hμj j]; simp
  have hprodint : ∀ j k, Integrable (fun ω => Z j ω * conj (Z k ω)) P := fun j k =>
    integrable_of_bound ((hZmeas j).mul (Complex.continuous_conj.measurable.comp (hZmeas k)))
      (B := (B + ‖μ‖) * (B + ‖μ‖)) fun ω => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hZb j ω) (hZb k ω) (norm_nonneg _) ((norm_nonneg _).trans (hZb j ω))
  -- the diagonal term
  have hdiag : ∀ j, ∫ ω, Z j ω * conj (Z j ω) ∂P =
      (((∫ ω, ‖Y 0 ω‖ ^ 2 ∂P) - ‖μ‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    have e : ∀ ω, Z j ω * conj (Z j ω) = Y j ω * conj (Y j ω) - Y j ω * conj μ - μ * conj (Y j ω)
        + μ * conj μ := fun ω => by simp only [Z, map_sub]; ring
    simp_rw [e]
    have hYi := integrable_of_bound (P := P) (hmeas j) (hb j)
    have hYc : Integrable (fun ω => conj (Y j ω)) P :=
      integrable_of_bound (Complex.continuous_conj.measurable.comp (hmeas j)) (B := B)
        fun ω => by rw [Complex.norm_conj]; exact hb j ω
    have hYY : Integrable (fun ω => Y j ω * conj (Y j ω)) P :=
      integrable_of_bound ((hmeas j).mul (Complex.continuous_conj.measurable.comp (hmeas j)))
        (B := B * B) fun ω => by
          rw [norm_mul, Complex.norm_conj]
          exact mul_le_mul (hb j ω) (hb j ω) (norm_nonneg _) ((norm_nonneg _).trans (hb j ω))
    have h1 : Integrable (fun ω => Y j ω * conj (Y j ω) - Y j ω * conj μ) P :=
      hYY.sub (hYi.mul_const _)
    have h2 : Integrable (fun ω => Y j ω * conj (Y j ω) - Y j ω * conj μ - μ * conj (Y j ω)) P :=
      h1.sub (hYc.const_mul _)
    rw [integral_add h2 (integrable_const _), integral_sub h1 (hYc.const_mul _),
      integral_sub hYY (hYi.mul_const _), integral_mul_const, integral_const_mul, integral_conj,
      hμj j, integral_const]
    have hsq : ∫ ω, Y j ω * conj (Y j ω) ∂P = ((∫ ω, ‖Y 0 ω‖ ^ 2 ∂P : ℝ) : ℂ) := by
      have e2 : ∀ ω, Y j ω * conj (Y j ω) = ((‖Y j ω‖ ^ 2 : ℝ) : ℂ) := fun ω => by
        rw [Complex.ofReal_pow, Complex.mul_conj']
      simp_rw [e2]
      rw [integral_complex_ofReal]
      congr 1
      exact ((hid j).comp (measurable_norm.pow_const 2)).integral_eq
    rw [hsq]
    simp only [Complex.mul_conj', probReal_univ, one_smul]
    push_cast; ring
  -- off-diagonal terms
  have hoff : ∀ j k, j ≠ k → ∫ ω, Z j ω * conj (Z k ω) ∂P = 0 := by
    intro j k hjk
    have hi : IndepFun (Z j) (fun ω => conj (Z k ω)) P :=
      (hind.indepFun hjk).comp (φ := fun z => z - μ) (ψ := fun z => conj (z - μ))
        (by fun_prop) (by fun_prop)
    rw [hi.integral_fun_mul_eq_mul_integral (hZint j).1
      (Complex.continuous_conj.measurable.comp (hZmeas k)).aestronglyMeasurable, hZmean j, zero_mul]
  -- assemble
  have hm' : (m : ℝ) ≠ 0 := by have : (0 : ℝ) < m := by exact_mod_cast hm
                               positivity
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm'
  have hrewrite : ∀ ω, (((‖(m : ℂ)⁻¹ * ∑ j ∈ range m, Y j ω - μ‖ ^ 2 : ℝ)) : ℂ) =
      ((m : ℂ)⁻¹) ^ 2 * ∑ j ∈ range m, ∑ k ∈ range m, Z j ω * conj (Z k ω) := by
    intro ω
    have e : (m : ℂ)⁻¹ * ∑ j ∈ range m, Y j ω - μ = (m : ℂ)⁻¹ * ∑ j ∈ range m, Z j ω := by
      simp only [Z, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      field_simp
    rw [e, Complex.ofReal_pow, ← Complex.mul_conj', map_mul, map_sum, map_inv₀,
      Complex.conj_natCast, mul_mul_mul_comm, sum_mul_sum, pow_two]
  have hC : ∫ ω, ((‖(m : ℂ)⁻¹ * ∑ j ∈ range m, Y j ω - μ‖ ^ 2 : ℝ) : ℂ) ∂P =
      ((((∫ ω, ‖Y 0 ω‖ ^ 2 ∂P) - ‖μ‖ ^ 2) / m : ℝ) : ℂ) := by
    simp_rw [hrewrite]
    rw [integral_const_mul, integral_finset_sum _ fun j _ => integrable_finset_sum _
      fun k _ => hprodint j k]
    rw [sum_congr rfl fun j _ => integral_finset_sum _ fun k _ => hprodint j k]
    rw [sum_congr rfl fun j _ => (by
      rw [sum_eq_single j (fun k _ hkj => hoff j k (Ne.symm hkj))
        (fun h => absurd (mem_range.2 (by simpa using ‹j ∈ range m›)) h), hdiag j] :
      ∑ k ∈ range m, ∫ ω, Z j ω * conj (Z k ω) ∂P = (((∫ ω, ‖Y 0 ω‖ ^ 2 ∂P) - ‖μ‖ ^ 2 : ℝ) : ℂ))]
    rw [sum_const, card_range, nsmul_eq_mul]
    push_cast
    field_simp
  rw [integral_complex_ofReal] at hC
  exact_mod_cast hC

variable {f : ℂ → ℂ} {a : ℂ}

/-- The summands `Y_j = 2πi (Z_j - a) f(Z_j)` of the contour estimator. -/
noncomputable def contourTerm (f : ℂ → ℂ) (a : ℂ) (r : ℝ) (j : ℕ) (ω : SteinhausΩ) : ℂ :=
  2 * Real.pi * Complex.I * (circSample r j ω * f (a + circSample r j ω))

lemma Cm_eq_mean (r : ℝ) (m : ℕ) (ω : SteinhausΩ) :
    Cm f a r m ω = (m : ℂ)⁻¹ * ∑ j ∈ range m, contourTerm f a r j ω := by
  simp only [Cm, contourTerm, ← mul_sum]; ring_nf

/-- `∮_{|z-a|=r} f(z) dz = 2πi E[rU f(a + rU)]`. -/
lemma circleIntegral_eq_integral (hf : Continuous f) (r : ℝ) :
    circleIntegral f a r = ∫ ω, contourTerm f a r 0 ω ∂steinhausMeasure := by
  have h := integral_steinhaus (fun z => 2 * Real.pi * Complex.I * (r * z * f (a + r * z)))
    (continuous_const.mul ((continuous_const.mul continuous_id).mul
      (hf.comp (continuous_const.add (continuous_const.mul continuous_id))))) 0
  simp only [contourTerm, circSample]
  rw [h, circleIntegral, intervalIntegral.integral_const_mul, Complex.real_smul]
  rw [← intervalIntegral.integral_const_mul]
  have e : ∀ θ : ℝ, deriv (circleMap a r) θ • f (circleMap a r θ) =
      Complex.I * (r * Complex.exp (θ * Complex.I) * f (a + r * Complex.exp (θ * Complex.I))) :=
    fun θ => by simp only [deriv_circleMap, circleMap, zero_add, smul_eq_mul]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- **Proposition 8.2 (Monte Carlo contour integration), continuous integrands.** For continuous
`f`, `E|C_m(f) - I_f|² = m⁻¹ (4π² r² E|f(a+rU)|² - |I_f|²)` and `C_m(f) → I_f` almost surely and
in `L²`. -/
theorem contour_continuous (hf : Continuous f) (r : ℝ) :
    (∀ m, 1 ≤ m → ∫ ω, ‖Cm f a r m ω - circleIntegral f a r‖ ^ 2 ∂steinhausMeasure =
      (4 * Real.pi ^ 2 * r ^ 2 * ∫ ω, ‖f (a + circSample r 0 ω)‖ ^ 2 ∂steinhausMeasure
        - ‖circleIntegral f a r‖ ^ 2) / m) ∧
    Tendsto (fun m => ∫ ω, ‖Cm f a r m ω - circleIntegral f a r‖ ^ 2 ∂steinhausMeasure) atTop
      (𝓝 0) ∧
    ∀ᵐ ω ∂steinhausMeasure, Tendsto (fun m => Cm f a r m ω) atTop (𝓝 (circleIntegral f a r)) := by
  set h : ℂ → ℂ := fun u => 2 * Real.pi * Complex.I * (r * u * f (a + r * u))
  have hcont : Continuous h := continuous_const.mul ((continuous_const.mul continuous_id).mul
    (hf.comp (continuous_const.add (continuous_const.mul continuous_id))))
  have hY : ∀ j, contourTerm f a r j = h ∘ steinhaus j := fun j => rfl
  have hX := steinhaus_radialSample
  have hind : iIndepFun (contourTerm f a r) steinhausMeasure := by
    have := hX.indep.comp (fun _ => h) (fun _ => hcont.measurable)
    exact this
  have hid : ∀ j, IdentDistrib (contourTerm f a r j) (contourTerm f a r 0) steinhausMeasure
      steinhausMeasure := fun j => by
    rw [hY, hY]; exact (hX.ident j 0).comp hcont.measurable
  have hmeas : ∀ j, Measurable (contourTerm f a r j) := fun j => by
    rw [hY]; exact hcont.measurable.comp (hX.meas j)
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ Metric.closedBall (0 : ℂ) |r|, ‖f (a + z)‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) |r|).exists_bound_of_continuousOn
      ((hf.comp (continuous_const.add continuous_id)).continuousOn)
    exact ⟨M, hM⟩
  have hb : ∀ j ω, ‖contourTerm f a r j ω‖ ≤ 2 * Real.pi * (|r| * M) := by
    intro j ω
    have hn := norm_circSample r j ω
    have hM' := hM (circSample r j ω) (by simp [hn])
    simp only [contourTerm, norm_mul, hn]
    have : ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖Complex.I‖ = 2 * Real.pi := by simp [Real.pi_pos.le]
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM' (abs_nonneg r))
      (by positivity)
  have hI := circleIntegral_eq_integral (a := a) hf r
  have hsq : ∫ ω, ‖contourTerm f a r 0 ω‖ ^ 2 ∂steinhausMeasure =
      4 * Real.pi ^ 2 * r ^ 2 * ∫ ω, ‖f (a + circSample r 0 ω)‖ ^ 2 ∂steinhausMeasure := by
    rw [← integral_const_mul]
    congr 1; ext ω
    simp only [contourTerm, norm_mul, norm_circSample]
    have : ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖Complex.I‖ = 2 * Real.pi := by simp [Real.pi_pos.le]
    rw [this, mul_pow, mul_pow, mul_pow, sq_abs]; ring
  have hvar : ∀ m, 1 ≤ m → ∫ ω, ‖Cm f a r m ω - circleIntegral f a r‖ ^ 2 ∂steinhausMeasure =
      (4 * Real.pi ^ 2 * r ^ 2 * ∫ ω, ‖f (a + circSample r 0 ω)‖ ^ 2 ∂steinhausMeasure
        - ‖circleIntegral f a r‖ ^ 2) / m := by
    intro m hm
    simp_rw [Cm_eq_mean, hI]
    rw [iid_variance hind hid hmeas hb hm, hsq]
  refine ⟨hvar, ?_, ?_⟩
  · refine (tendsto_const_div_atTop_nhds_zero_nat (4 * Real.pi ^ 2 * r ^ 2 *
      ∫ ω, ‖f (a + circSample r 0 ω)‖ ^ 2 ∂steinhausMeasure - ‖circleIntegral f a r‖ ^ 2)).congr'
      ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    rw [hvar m hm]
  · have hlaw := strong_law_ae (μ := steinhausMeasure) (contourTerm f a r)
      (integrable_of_bound (hmeas 0) (hb 0)) (fun i j hij => hind.indepFun hij) hid
    filter_upwards [hlaw] with ω hω
    rw [hI]
    refine hω.congr fun m => ?_
    rw [Cm_eq_mean, RadialSample.smul_form]

end Barycenter

-- ============================================================================
-- Source part: Bary25.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal NNReal

namespace Barycenter

/-! ## Part 25. A nonradial law preserving every polynomial mean (Example 7.3) -/

lemma diskLaw_integrable_of_continuous {g : ℂ → ℂ} (hg : Continuous g) : Integrable g diskLaw := by
  have h : IntegrableOn g (Metric.closedBall (0 : ℂ) 1) volume :=
    hg.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)
  exact h.smul_measure ENNReal.ofReal_ne_top

/-- Mixed moments of the uniform law on the disk: `E_0[z^p \bar z^q] = δ_{pq}/(p+1)`. -/
lemma diskLaw_mixed (p q : ℕ) :
    ∫ z, z ^ p * conj z ^ q ∂diskLaw = if p = q then ((1 / (p + 1) : ℝ) : ℂ) else 0 := by
  have h := disk_moments 0 p q
  have h2 := integral_map (μ := diskP) (measurable_pi_apply 0).aemeasurable
    (f := fun z : ℂ => z ^ p * conj z ^ q) (by fun_prop)
  rw [show (fun ω : ℕ → ℂ => ω 0) = coord 0 from rfl, map_coord] at h2
  rw [h2]; exact h

/-- The density `ρ_ε(z) = 1 + ε Re z (|z|² - 2/3)` (with respect to the uniform law on `D`). -/
noncomputable def nrDensity (ε : ℝ) (z : ℂ) : ℝ := 1 + ε * z.re * (‖z‖ ^ 2 - 2 / 3)

lemma nrDensity_nonneg {ε : ℝ} (hε : |ε| ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 1) : 0 ≤ nrDensity ε z := by
  have h1 : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hz
  have h2 : |‖z‖ ^ 2 - 2 / 3| ≤ 2 / 3 := by
    rw [abs_le]; constructor <;> nlinarith [norm_nonneg z]
  have h3 : |ε * z.re * (‖z‖ ^ 2 - 2 / 3)| ≤ 2 / 3 := by
    rw [abs_mul, abs_mul]
    calc |ε| * |z.re| * |‖z‖ ^ 2 - 2 / 3| ≤ 1 * 1 * (2 / 3) := by gcongr
      _ = 2 / 3 := by ring
  rw [nrDensity]; linarith [neg_abs_le (ε * z.re * (‖z‖ ^ 2 - 2 / 3))]

lemma nrDensity_complex (ε : ℝ) (z : ℂ) :
    (nrDensity ε z : ℂ) = 1 + ε / 2 * ((z + conj z) * (z * conj z - 2 / 3)) := by
  rw [nrDensity, Complex.mul_conj']
  have : (z.re : ℂ) = (z + conj z) / 2 := Complex.re_eq_add_conj z
  push_cast; rw [this]; ring

lemma continuous_nrDensity (ε : ℝ) : Continuous (nrDensity ε) := by
  unfold nrDensity; fun_prop

/-- The nonradial law `ρ_ε(z) dA(z)/π` on the unit disk. -/
noncomputable def nonradialLaw (ε : ℝ) : Measure ℂ :=
  diskLaw.withDensity fun z => ((nrDensity ε z).toNNReal : ℝ≥0∞)

lemma integral_nonradialLaw {ε : ℝ} (hε : |ε| ≤ 1) (g : ℂ → ℂ) :
    ∫ z, g z ∂nonradialLaw ε = ∫ z, (nrDensity ε z : ℂ) * g z ∂diskLaw := by
  rw [nonradialLaw, integral_withDensity_eq_integral_smul
    (continuous_nrDensity ε).measurable.real_toNNReal]
  refine integral_congr_ae ?_
  filter_upwards [diskLaw_ae_norm_le] with z hz
  rw [NNReal.smul_def, Real.coe_toNNReal _ (nrDensity_nonneg hε hz), Complex.real_smul]

/-- Mixed moments `E_0[z^p \bar z^q]` of the uniform law on the disk. -/
noncomputable def dmom (p q : ℕ) : ℂ := ∫ z, z ^ p * conj z ^ q ∂diskLaw

lemma dmom_eq (p q : ℕ) : dmom p q = if p = q then ((1 / (p + 1) : ℝ) : ℂ) else 0 :=
  diskLaw_mixed p q

/-- Moments against the density: `∫ ρ_ε z^p \bar z^q dE_0` in terms of disk moments. -/
lemma nr_mixed (ε : ℝ) (p q : ℕ) :
    ∫ z, (nrDensity ε z : ℂ) * (z ^ p * conj z ^ q) ∂diskLaw =
      dmom p q + ε / 2 * (dmom (p + 2) (q + 1) + dmom (p + 1) (q + 2)
        - 2 / 3 * dmom (p + 1) q - 2 / 3 * dmom p (q + 1)) := by
  have hI : ∀ a b : ℕ, Integrable (fun z : ℂ => z ^ a * conj z ^ b) diskLaw := fun a b =>
    diskLaw_integrable_of_continuous (by fun_prop)
  have e : ∀ z : ℂ, (nrDensity ε z : ℂ) * (z ^ p * conj z ^ q) = z ^ p * conj z ^ q +
      ε / 2 * (z ^ (p + 2) * conj z ^ (q + 1) + z ^ (p + 1) * conj z ^ (q + 2)
        - 2 / 3 * (z ^ (p + 1) * conj z ^ q) - 2 / 3 * (z ^ p * conj z ^ (q + 1))) := by
    intro z; rw [nrDensity_complex]; ring
  simp_rw [e]
  have h1 : Integrable (fun z : ℂ => z ^ (p + 2) * conj z ^ (q + 1) +
      z ^ (p + 1) * conj z ^ (q + 2)) diskLaw := (hI _ _).add (hI _ _)
  have h2 : Integrable (fun z : ℂ => z ^ (p + 2) * conj z ^ (q + 1) +
      z ^ (p + 1) * conj z ^ (q + 2) - 2 / 3 * (z ^ (p + 1) * conj z ^ q)) diskLaw :=
    h1.sub ((hI _ _).const_mul _)
  have h3 : Integrable (fun z : ℂ => z ^ (p + 2) * conj z ^ (q + 1) +
      z ^ (p + 1) * conj z ^ (q + 2) - 2 / 3 * (z ^ (p + 1) * conj z ^ q)
        - 2 / 3 * (z ^ p * conj z ^ (q + 1))) diskLaw :=
    h2.sub ((hI _ _).const_mul _)
  have h4 : Integrable (fun z : ℂ => (ε : ℂ) / 2 * (z ^ (p + 2) * conj z ^ (q + 1) +
      z ^ (p + 1) * conj z ^ (q + 2) - 2 / 3 * (z ^ (p + 1) * conj z ^ q)
        - 2 / 3 * (z ^ p * conj z ^ (q + 1)))) diskLaw := h3.const_mul _
  rw [integral_add (hI p q) h4, integral_const_mul, integral_sub h2 ((hI _ _).const_mul _),
    integral_sub h1 ((hI _ _).const_mul _), integral_add (hI _ _) (hI _ _), integral_const_mul,
    integral_const_mul]
  rfl

lemma nonradial_mass (ε : ℝ) : ∫ z, (nrDensity ε z : ℂ) ∂diskLaw = 1 := by
  have h := nr_mixed ε 0 0
  simp only [pow_zero, mul_one] at h
  rw [h]
  simp only [dmom_eq]
  norm_num

/-- The law `ρ_ε dA/π` is a probability measure for `|ε| ≤ 1`. -/
theorem nonradial_isProb {ε : ℝ} (hε : |ε| ≤ 1) : IsProbabilityMeasure (nonradialLaw ε) := by
  constructor
  rw [nonradialLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable (nrDensity ε) diskLaw := by
    have := diskLaw_integrable_of_continuous (g := fun z => (nrDensity ε z : ℂ))
      (Complex.continuous_ofReal.comp (continuous_nrDensity ε))
    exact this.re
  have hnn : 0 ≤ᵐ[diskLaw] nrDensity ε := by
    filter_upwards [diskLaw_ae_norm_le] with z hz using nrDensity_nonneg hε hz
  have e : ∫⁻ z, ((nrDensity ε z).toNNReal : ℝ≥0∞) ∂diskLaw =
      ENNReal.ofReal (∫ z, nrDensity ε z ∂diskLaw) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint hnn]; rfl
  rw [e]
  have hm := nonradial_mass ε
  rw [integral_complex_ofReal] at hm
  rw [Complex.ofReal_eq_one.1 hm, ENNReal.ofReal_one]

/-- **Example 7.3.** For `0 < |ε| ≤ 1` the law `ρ_ε dA/π` has all analytic moments zero,
`E X^n = 0` for `n ≥ 1`, but `E[X² \bar X] = ε/72 ≠ 0`. -/
theorem nonradial_moments {ε : ℝ} (hε : |ε| ≤ 1) :
    (∀ n, 1 ≤ n → ∫ z, z ^ n ∂nonradialLaw ε = 0) ∧
      ∫ z, z ^ 2 * conj z ∂nonradialLaw ε = ε / 72 := by
  constructor
  · intro n hn
    rw [integral_nonradialLaw hε]
    have h := nr_mixed ε n 0
    simp only [pow_zero, mul_one] at h
    rw [h]
    simp only [dmom_eq]
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have : n = 1 := by omega
      subst this; norm_num
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
      simp
  · rw [integral_nonradialLaw hε]
    have h := nr_mixed ε 2 1
    simp only [pow_one] at h
    rw [h]
    simp only [dmom_eq]
    norm_num
    ring

end Barycenter

namespace Barycenter

/-- The coordinates of an i.i.d. product of a law with finite moments form an i.i.d. sample. -/
theorem coord_iidSample (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hmom : ∀ p : ℕ, MemLp id p ν) : IIDSample coord (iidMeasure ν) where
  meas j := measurable_pi_apply j
  indep := by
    have := iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ x => x)
      (fun _ => measurable_id)
    exact this
  ident i j := ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply j).aemeasurable, by
    rw [map_coord, map_coord]⟩
  mom j p := by
    have h := hmom p
    rw [← map_coord ν j] at h
    exact (memLp_map_measure_iff (μ := iidMeasure ν) (f := coord j) h.1
      (measurable_pi_apply j).aemeasurable).1 h

lemma nonradial_memLp {ε : ℝ} (hε : |ε| ≤ 1) (p : ℕ) : MemLp id p (nonradialLaw ε) := by
  haveI := nonradial_isProb hε
  have hae : ∀ᵐ z ∂nonradialLaw ε, ‖z‖ ≤ 1 :=
    (withDensity_absolutelyContinuous _ _).ae_le diskLaw_ae_norm_le
  exact MemLp.of_bound measurable_id.aestronglyMeasurable 1 hae

/-- **Example 7.3, conclusion.** For `|ε| ≤ 1`, i.i.d. darts with law `ρ_ε dA/π` satisfy
`E P(a + S_m) = P(a)` for every polynomial `P` and every `m ≥ 1` (Theorem 7.2), although for
`ε ≠ 0` the law is not rotationally invariant. -/
theorem nonradial_example {ε : ℝ} (hε : |ε| ≤ 1) (a : ℂ) :
    letI := nonradial_isProb hε
    (∀ m, 1 ≤ m → ∀ Q : Polynomial ℂ,
      ∫ ω, Q.eval (a + Scen coord m ω) ∂iidMeasure (nonradialLaw ε) = Q.eval a) ∧
    (ε ≠ 0 → ¬ RotInvLaw (nonradialLaw ε)) := by
  letI := nonradial_isProb hε
  have hX := coord_iidSample (nonradialLaw ε) (nonradial_memLp hε)
  have hmom : ∀ n, 1 ≤ n → anMom (coord 0) (iidMeasure (nonradialLaw ε)) n = 0 := by
    intro n hn
    have h2 := integral_map (μ := iidMeasure (nonradialLaw ε)) (measurable_pi_apply 0).aemeasurable
      (f := fun z : ℂ => z ^ n) (by fun_prop)
    rw [show (fun ω : ℕ → ℂ => ω 0) = coord 0 from rfl, map_coord] at h2
    rw [anMom]
    exact h2.symm.trans ((nonradial_moments hε).1 n hn)
  constructor
  · have h := (hX.criterion a (m₀ := 1) le_rfl).out 0 3
    exact h.1 hmom
  · intro hε0 hrot
    have hR := coord_radialSample (nonradialLaw ε) hrot (nonradial_memLp hε)
    have h := (hR.rot 0).cmom_eq 2 1
    rw [if_neg (by norm_num), cmom] at h
    have h2 := integral_map (μ := iidMeasure (nonradialLaw ε)) (measurable_pi_apply 0).aemeasurable
      (f := fun z : ℂ => z ^ 2 * conj z ^ 1) (by fun_prop)
    rw [show (fun ω : ℕ → ℂ => ω 0) = coord 0 from rfl, map_coord] at h2
    have h3 := (nonradial_moments hε).2
    have h4 := h2.trans h
    simp only [pow_one] at h4
    rw [h3] at h4
    apply hε0
    have : (ε : ℂ) = 0 := by linear_combination 72 * h4
    exact_mod_cast this

end Barycenter

-- ============================================================================
-- Source part: Bary26.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 26. Monomial centers for general radial laws (Lemma 3.3) and the coefficient bound
(4.5) -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace RadialSample

variable {X : ℕ → Ω → ℂ} {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

/-- **Lemma 3.3, bounds.** `E|W_m^{(n)}| ≤ √(μ_n/m)`, `P(|W_m^{(n)}| ≥ ε) ≤ μ_n/(mε²)` and
`W_m^{(n)} → 0` almost surely. -/
theorem Wpow_bounds (hX : RadialSample X P) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ ω, ‖Wpow X m n ω‖ ∂P ≤ Real.sqrt (radMom (X 0) P n / m) ∧
      P.real {ω | ε ≤ ‖Wpow X m n ω‖} ≤ radMom (X 0) P n / m / ε ^ 2 := by
  have hs : Summable fun k => ‖monoCoef n k‖ ^ 2 * radMom (X 0) P k := summable_monoCoef n _
  have h := hX.deviation_A (f := fun z => z ^ n) (a := 0) hm (hasSum_monoCoef n) hs hε
  simpa [Aimg_monomial, zero_pow (by omega : n ≠ 0), Vf_monoCoef hn] using h

theorem Wpow_ae (hX : RadialSample X P) {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂P, Tendsto (fun m => Wpow X m n ω) atTop (𝓝 0) := by
  have h := hX.ae_tendsto_Aimg (f := fun z => z ^ n) (a := 0) (hasSum_monoCoef n)
    (summable_monoCoef n _)
  simpa [Aimg_monomial, zero_pow (by omega : n ≠ 0)] using h

/-- `E|S_m|^n ≤ √(q_{m,n})`. -/
lemma integral_norm_Scen_pow_le (hX : RadialSample X P) (m n : ℕ) :
    ∫ ω, ‖Scen X m ω‖ ^ n ∂P ≤ Real.sqrt (qmom (radMom (X 0) P) m n) := by
  have hmem : MemLp (fun ω => Scen X m ω ^ n) 2 P := (hX.allMoments_Scen m).memLp_pow n
  have h := integral_norm_le_sqrt hmem
  rw [hX.integral_norm_sq_Scen_pow] at h
  simpa [norm_pow] using h

/-- `q_{m,n} ≤ μ_n/m` for `m, n ≥ 1`. -/
lemma qmom_le_div (hX : RadialSample X P) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    qmom (radMom (X 0) P) m n ≤ radMom (X 0) P n / m := by
  have h1 := hX.qmom_le m n
  have h2 := kappa_le_inv hm hn
  have hμ := radMom_nonneg (X := X) (P := P) 0 n
  calc qmom (radMom (X 0) P) m n ≤ radMom (X 0) P n * kappa m n := h1
    _ ≤ radMom (X 0) P n * (1 / m) := mul_le_mul_of_nonneg_left h2 hμ
    _ = radMom (X 0) P n / m := by ring

/-- **Corollary 4.4, (4.5).** If `∑ |c_n| √μ_n < ∞`, then
`E|B_m(f) - f(a)| ≤ ∑_{n ≥ 1} |c_n| √(q_{m,n}) ≤ m^{-1/2} ∑_{n ≥ 1} |c_n| √μ_n`. -/
theorem coeff_bound (hX : RadialSample X P) {m : ℕ} (hm : 1 ≤ m)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hsum : Summable fun n => ‖c n‖ * Real.sqrt (radMom (X 0) P n)) :
    ∫ ω, ‖Bimg f a X m ω - f a‖ ∂P ≤
        ∑' n, ‖c (n + 1)‖ * Real.sqrt (qmom (radMom (X 0) P) m (n + 1)) ∧
      ∑' n, ‖c (n + 1)‖ * Real.sqrt (qmom (radMom (X 0) P) m (n + 1)) ≤
        1 / Real.sqrt m * ∑' n, ‖c (n + 1)‖ * Real.sqrt (radMom (X 0) P (n + 1)) := by
  set μ := radMom (X 0) P
  set q := qmom μ m
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : ∀ n, 1 ≤ n → Real.sqrt (q n) ≤ 1 / Real.sqrt m * Real.sqrt (μ n) := by
    intro n hn
    rw [one_div, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt ((hX.qmom_le_div hm hn).trans_eq (by ring))
  have hsum1 : Summable fun n => ‖c (n + 1)‖ * Real.sqrt (μ (n + 1)) :=
    (summable_nat_add_iff 1).2 hsum
  have hsum2 : Summable fun n => ‖c (n + 1)‖ * Real.sqrt (q (n + 1)) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => (mul_le_mul_of_nonneg_left (hsq (n + 1) (by omega)) (norm_nonneg _)).trans_eq
        (by ring)) (hsum1.mul_left (1 / Real.sqrt m))
  refine ⟨?_, ?_⟩
  · -- termwise integration
    set F : ℕ → Ω → ℝ := fun n ω => ‖c (n + 1)‖ * ‖Scen X m ω‖ ^ (n + 1)
    have hFint : ∀ n, Integrable (F n) P := fun n =>
      ((hX.allMoments_Scen m).integrable_norm_pow (n + 1)).const_mul _
    have hFnn : ∀ n ω, 0 ≤ F n ω := fun n ω => by positivity
    have hFle : ∀ n, ∫ ω, F n ω ∂P ≤ ‖c (n + 1)‖ * Real.sqrt (q (n + 1)) := by
      intro n
      simp only [F]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hX.integral_norm_Scen_pow_le m (n + 1)) (norm_nonneg _)
    have hsF : ∀ ω, Summable fun n => F n ω := fun ω => by
      have hs := summable_norm_mul_pow_of_hasSum hf ‖Scen X m ω‖ (norm_nonneg _)
      exact (summable_nat_add_iff 1).2 hs
    have hpt : ∀ ω, ‖Bimg f a X m ω - f a‖ ≤ ∑' n, F n ω := by
      intro ω
      have h := (hasSum_g hf (Scen X m ω))
      have hs := summable_norm_mul_pow_of_hasSum (hasSum_g hf) ‖Scen X m ω‖ (norm_nonneg _)
      have hs' : Summable fun n => ‖gcoef c n * Scen X m ω ^ n‖ := by
        simpa [norm_mul, norm_pow] using hs
      rw [Bimg, ← h.tsum_eq]
      refine (norm_tsum_le_tsum_norm hs').trans ?_
      rw [hs'.tsum_eq_zero_add]
      simp only [gcoef_zero, zero_mul, norm_zero, zero_add, gcoef_succ, norm_mul, norm_pow, F]
      rfl
    have hcont : Continuous fun z => f (a + z) := continuous_of_hasSum hf
    have hmeasB : AEStronglyMeasurable (fun ω => Bimg f a X m ω - f a) P :=
      ((hcont.measurable.comp (hX.measurable_Scen m)).sub measurable_const).aestronglyMeasurable
    have key : ∫⁻ ω, ‖Bimg f a X m ω - f a‖ₑ ∂P ≤
        ENNReal.ofReal (∑' n, ‖c (n + 1)‖ * Real.sqrt (q (n + 1))) := by
      calc ∫⁻ ω, ‖Bimg f a X m ω - f a‖ₑ ∂P ≤ ∫⁻ ω, ∑' n, ENNReal.ofReal (F n ω) ∂P := by
            refine lintegral_mono fun ω => ?_
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => hFnn n ω) (hsF ω),
              ← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal (hpt ω)
        _ = ∑' n, ∫⁻ ω, ENNReal.ofReal (F n ω) ∂P :=
            lintegral_tsum fun n => (hFint n).aemeasurable.ennreal_ofReal
        _ = ∑' n, ENNReal.ofReal (∫ ω, F n ω ∂P) := by
            congr 1; ext n
            rw [ofReal_integral_eq_lintegral_ofReal (hFint n)
              (Eventually.of_forall fun ω => hFnn n ω)]
        _ ≤ ∑' n, ENNReal.ofReal (‖c (n + 1)‖ * Real.sqrt (q (n + 1))) :=
            ENNReal.tsum_le_tsum fun n => ENNReal.ofReal_le_ofReal (hFle n)
        _ = ENNReal.ofReal (∑' n, ‖c (n + 1)‖ * Real.sqrt (q (n + 1))) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum2).symm
    rw [integral_norm_eq_lintegral_enorm hmeasB]
    exact ENNReal.toReal_le_of_le_ofReal (tsum_nonneg fun n => by positivity) key
  · rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun n => (mul_le_mul_of_nonneg_left (hsq (n + 1) (by omega))
      (norm_nonneg _)).trans_eq (by ring)) hsum2 (hsum1.mul_left _)

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary27.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 27. Numerical illustration of the roots-of-unity rule (after Proposition 8.3) -/

lemma factorial_ge_pow (n : ℕ) : (10 : ℕ).factorial * 11 ^ n ≤ (n + 10).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 10 = (n + 10) + 1 by ring, Nat.factorial_succ, pow_succ]
    calc (10 : ℕ).factorial * (11 ^ n * 11) = 11 * ((10 : ℕ).factorial * 11 ^ n) := by ring
      _ ≤ (n + 10 + 1) * (n + 10).factorial := Nat.mul_le_mul (by omega) ih

/-- **After Proposition 8.3.** For `f(z) = e^z`, `a = 0`, `r = 1`, `U = 1` and `m = 10`, the
roots-of-unity rule has error `∑_{k ≥ 1} 1/(10k)! ≈ 2.7557·10^{-7}`; precisely
`2.755·10^{-7} < |T_{10}(e^z) - 1| < 2.756·10^{-7}`. -/
theorem roots_exp_error :
    (2755 / 10 ^ 10 : ℝ) < ‖Trule (expShift 1 0) 0 10 1 - 1‖ ∧
      ‖Trule (expShift 1 0) 0 10 1 - 1‖ < 2756 / 10 ^ 10 := by
  set t : ℕ → ℝ := fun k => 1 / ((k + 1) * 10).factorial
  set ρ : ℝ := (11 ^ 10)⁻¹
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by norm_num [ρ]
  have ht0 : ∀ k, 0 ≤ t k := fun k => by positivity
  have htle : ∀ k, t k ≤ 1 / (10 : ℕ).factorial * ρ ^ k := by
    intro k
    have h := factorial_ge_pow (10 * k)
    rw [show 10 * k + 10 = (k + 1) * 10 by ring] at h
    have h' : ((10 : ℕ).factorial : ℝ) * (11 ^ 10) ^ k ≤ ((k + 1) * 10).factorial := by
      rw [← pow_mul]; exact_mod_cast h
    simp only [t, ρ, inv_pow]
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    rw [one_mul, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    linarith
  have hgeo := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_left (1 / ((10 : ℕ).factorial : ℝ))
  have hts : Summable t := Summable.of_nonneg_of_le ht0 htle hgeo.summable
  set s := ∑' k, t k
  -- identify the error with `s`
  have hT := Trule_sub (hasSum_expCoef 1 0) (m := 10) (by norm_num) 1
  have hfa : expShift 1 0 0 = 1 := by simp [expShift]
  rw [hfa] at hT
  have hC : HasSum (fun k => ((t k : ℝ) : ℂ)) (s : ℂ) := Complex.hasSum_ofReal.2 hts.hasSum
  have he : Trule (expShift 1 0) 0 10 1 - 1 = (s : ℂ) := by
    refine hT.unique ?_
    convert hC using 1
    ext k; simp [t, expCoef]
  rw [he, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg ht0)]
  constructor
  · have h1 : t 0 ≤ s := hts.le_tsum 0 fun k _ => ht0 k
    have h2 : t 0 = 1 / 3628800 := by simp [t, Nat.factorial]
    rw [h2] at h1
    linarith [show (2755 / 10 ^ 10 : ℝ) < 1 / 3628800 by norm_num]
  · have h1 : s ≤ 1 / (10 : ℕ).factorial * (1 - ρ)⁻¹ := hasSum_le htle hts.hasSum hgeo
    refine h1.trans_lt ?_
    norm_num [ρ, Nat.factorial]

end Barycenter

-- ============================================================================
-- Source part: Bary28.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal NNReal

namespace Barycenter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Part 28. The limit law (Theorem 6.1, (6.1)) and exponential tails (Remark 4.5)

Here Theorem 6.1, (6.1) is first proved *relative to* the central limit theorem
`√m S_m →d G`, which enters as a hypothesis; the Taylor remainder and Slutsky's lemma are proved
here. The central limit theorem itself is proved in Parts 32–35 (Lévy's continuity theorem and
the multivariate CLT), and the hypothesis is discharged in `tendstoInDistribution_Bimg_clt`
(Part 35) and `tendsto_law_Bimg` (Part 36). -/

/-- If `E|Y_m|² → 0` then `Y_m → 0` in probability (Chebyshev). -/
lemma tendstoInMeasure_zero_of_integral_norm_sq {Y : ℕ → Ω → ℂ}
    (hY : ∀ᶠ m in atTop, MemLp (Y m) 2 P)
    (h : Tendsto (fun m => ∫ ω, ‖Y m ω‖ ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P Y atTop 0 := by
  refine tendstoInMeasure_of_ne_top fun ε hε hεtop => ?_
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  have hset : ∀ m, {x | ε ≤ edist (Y m x) ((0 : Ω → ℂ) x)} = {x | ε.toReal ≤ ‖Y m x‖} := by
    intro m; ext x
    simp only [Set.mem_setOf_eq, Pi.zero_apply, edist_zero_right]
    rw [← ofReal_norm_eq_enorm, ENNReal.le_ofReal_iff_toReal_le hεtop (norm_nonneg _)]
  have hlim : Tendsto (fun m => ENNReal.ofReal ((∫ ω, ‖Y m ω‖ ^ 2 ∂P) / ε.toReal ^ 2)) atTop
      (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa using h.div_const (ε.toReal ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le _) ?_
  filter_upwards [hY] with m hm
  simp only [hset]
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (RadialSample.chebyshev_complex hm he)

/-- Two-sided Hoeffding inequality for the mean of independent, centred, bounded real variables:
`P(|m⁻¹ ∑_{j<m} R_j| ≥ t) ≤ 2 exp(-m t² / (2 L²))`. -/
lemma hoeffding_mean_two_sided {R : ℕ → Ω → ℝ} (hind : iIndepFun R P)
    (hmeas : ∀ j, AEMeasurable (R j) P) {L : ℝ} (hL : 0 < L) (hbd : ∀ j ω, |R j ω| ≤ L)
    (hmean : ∀ j, ∫ ω, R j ω ∂P = 0) {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ |(m : ℝ)⁻¹ * ∑ j ∈ range m, R j ω|} ≤
      2 * Real.exp (-(m * t ^ 2) / (2 * L ^ 2)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hIcc : ∀ j, ∀ᵐ ω ∂P, R j ω ∈ Set.Icc (-L) L := fun j =>
    Eventually.of_forall fun ω => abs_le.1 (hbd j ω)
  have hsub : ∀ j, HasSubgaussianMGF (R j) ((‖L - -L‖₊ / 2) ^ 2) P := fun j =>
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hmeas j) (hIcc j) (hmean j)
  have hc : (((‖L - -L‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = L ^ 2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, sub_neg_eq_add]
    rw [abs_of_pos (by linarith)]; norm_num
  have h1 := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind (fun i _ => hsub i)
    (ε := m * t) (by positivity) (n := m)
  have hindn : iIndepFun (fun j => -R j) P :=
    hind.comp (fun _ x => -x) (fun _ => measurable_neg)
  have h2 := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hindn (fun i _ => (hsub i).neg)
    (ε := m * t) (by positivity) (n := m)
  rw [hc] at h1 h2
  have hexp : Real.exp (-(m * t) ^ 2 / (2 * m * L ^ 2)) =
      Real.exp (-(m * t ^ 2) / (2 * L ^ 2)) := by
    congr 1; field_simp
  rw [hexp] at h1 h2
  have hincl : {ω | t ≤ |(m : ℝ)⁻¹ * ∑ j ∈ range m, R j ω|} ⊆
      {ω | m * t ≤ ∑ j ∈ range m, R j ω} ∪ {ω | m * t ≤ ∑ j ∈ range m, (-R j) ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, abs_mul, abs_inv, Nat.abs_cast] at hω
    have : m * t ≤ |∑ j ∈ range m, R j ω| := by
      rw [le_inv_mul_iff₀ hm'] at hω; exact hω
    rcases le_abs'.1 this with h | h
    · right; simp only [Set.mem_setOf_eq, Pi.neg_apply, sum_neg_distrib]; linarith
    · left; exact h
  calc P.real {ω | t ≤ |(m : ℝ)⁻¹ * ∑ j ∈ range m, R j ω|}
      ≤ P.real ({ω | m * t ≤ ∑ j ∈ range m, R j ω} ∪
          {ω | m * t ≤ ∑ j ∈ range m, (-R j) ω}) := measureReal_mono hincl
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

namespace RadialSample

variable {X : ℕ → Ω → ℂ} {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

/-- The Taylor remainder of order `> d` is negligible in `L²` at scale `m^{d/2}`:
`E|m^{d/2}(B_m(f) - f(a)) - c_d (√m S_m)^d|² → 0`. -/
theorem remainder_L2 (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {d : ℕ} (hd : 1 ≤ d)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) :
    (∀ᶠ m : ℕ in atTop, MemLp (fun ω => (Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a) -
      c d * ((Real.sqrt m : ℂ) * Scen X m ω) ^ d) 2 P) ∧
    Tendsto (fun m : ℕ => ∫ ω, ‖(Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a) -
      c d * ((Real.sqrt m : ℂ) * Scen X m ω) ^ d‖ ^ 2 ∂P) atTop (𝓝 0) := by
  classical
  set c' : ℕ → ℂ := Function.update c d 0 with hc'
  set g : ℂ → ℂ := fun w => f w - c d * (w - a) ^ d with hgdef
  have hg : ∀ z, HasSum (fun n => c' n * z ^ n) (g (a + z)) := by
    intro z
    have h2 : HasSum (fun n => (Pi.single d (c d * z ^ d) : ℕ → ℂ) n) (c d * z ^ d) :=
      hasSum_pi_single d _
    have h3 := (hf z).sub h2
    convert h3 using 1
    · funext n
      by_cases hn : n = d
      · subst hn; simp [c']
      · simp [c', hn]
    · simp [g]
  have hs' : Summable fun n => ‖c' n‖ ^ 2 * radMom (X 0) P n := by
    refine hs.of_nonneg_of_le (fun n => mul_nonneg (by positivity)
      (radMom_nonneg (X := X) 0 n)) (fun n => ?_)
    by_cases hn : n = d
    · subst hn; simp only [c', Function.update_self, norm_zero]
      have := radMom_nonneg (X := X) (P := P) 0 n
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      positivity
    · simp [c', Function.update_of_ne hn]
  have hlow' : ∀ n, 1 ≤ n → n < d → c' n = 0 := fun n h1 h2 => by
    simp [c', Function.update_of_ne (by omega : n ≠ d), hlow n h1 h2]
  have hmse := hX.tendsto_scaled_mse hg hs' hd hlow'
  have hc'd : c' d = 0 := by simp [c']
  rw [hc'd] at hmse
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    at hmse
  have hga : g a = f a := by simp [g, zero_pow (by omega : d ≠ 0)]
  have hid : ∀ (m : ℕ) ω, (Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a) -
      c d * ((Real.sqrt m : ℂ) * Scen X m ω) ^ d =
      (Real.sqrt m : ℂ) ^ d * (Bimg g a X m ω - g a) := by
    intro m ω
    rw [hga]; simp only [Bimg, g]; ring
  have hsq : ∀ m : ℕ, (Real.sqrt m ^ d) ^ 2 = (m : ℝ) ^ d := by
    intro m; rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hnormsq : ∀ m : ℕ, ∫ ω, ‖(Real.sqrt m : ℂ) ^ d * (Bimg g a X m ω - g a)‖ ^ 2 ∂P =
      (m : ℝ) ^ d * ∫ ω, ‖Bimg g a X m ω - g a‖ ^ 2 ∂P := by
    intro m
    simp_rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, hsq]
    exact integral_const_mul _ _
  simp_rw [hid]
  refine ⟨?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact (hX.memLp_comp_S hm hg hs').const_mul _
  · simp_rw [hnormsq]; exact hmse

/-- **Theorem 6.1, (6.1)** (relative to the central limit theorem). If `√m S_m → G` in
distribution, then `m^{d/2} (B_m(f) - f(a)) → c_d G^d` in distribution. -/
theorem tendstoInDistribution_Bimg (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {d : ℕ} (hd : 1 ≤ d)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) {G : Ω → ℂ}
    (hCLT : TendstoInDistribution (fun (m : ℕ) ω => (Real.sqrt m : ℂ) * Scen X m ω) atTop G P) :
    TendstoInDistribution (fun (m : ℕ) ω => (Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a))
      atTop (fun ω => c d * G ω ^ d) P := by
  obtain ⟨hmem, hlim⟩ := hX.remainder_L2 hf hs hd hlow
  have hX' := hCLT.continuous_comp (g := fun z => c d * z ^ d) (by fun_prop)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX' ?_ ?_
  · convert tendstoInMeasure_zero_of_integral_norm_sq hmem hlim using 1
  · intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : (fun ω => (Real.sqrt ((0 : ℕ) : ℝ) : ℂ) ^ d * (Bimg f a X 0 ω - f a)) =
          fun _ => 0 := by
        funext ω; simp [zero_pow (by omega : d ≠ 0)]
      rw [this]; exact aemeasurable_const
    · have h1 : MemLp (fun ω => f (a + Scen X m ω) - f a) 2 P := hX.memLp_comp_S hm hf hs
      exact (h1.aestronglyMeasurable.aemeasurable).const_mul _

/-- **Remark 4.5 (exponential tails for bounded sampling).** If `|f(a+X_j) - f(a)| ≤ L`, then
`P(|A_m(f) - f(a)| ≥ ε) ≤ 4 exp(-m ε² / (4 L²))`. -/
theorem hoeffding_Aimg (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {L : ℝ} (hL : 0 < L)
    (hbd : ∀ j ω, ‖f (a + X j ω) - f a‖ ≤ L) {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ ‖Aimg f a X m ω - f a‖} ≤ 4 * Real.exp (-(m * ε ^ 2) / (4 * L ^ 2)) := by
  classical
  set Yc : ℕ → Ω → ℂ := fun j ω => f (a + X j ω) - f a with hYc
  have hcont : Continuous (fun z => f (a + z)) := continuous_of_hasSum hf
  have hcont' : Continuous (fun z => f (a + z) - f a) := hcont.sub continuous_const
  have hν := radMom_nonneg (X := X) (P := P) 0
  have hzero : ∀ j, ∫ ω, Yc j ω ∂P = 0 := fun j =>
    integral_comp_eq_zero (hX.orthoMoments_X j) hν (g := fun z => f (a + z) - f a)
      (hasSum_g hf) (summable_gcoef hν hs) (gcoef_zero c)
      (fun p hp => hX.integral_pow_eq_zero j hp)
  have hint : ∀ j, Integrable (Yc j) P := fun j =>
    (hX.memLp_comp_X hf hs j).integrable one_le_two
  have hmeasY : ∀ j, Measurable (Yc j) := fun j => hcont'.measurable.comp (hX.meas j)
  set R : ℕ → Ω → ℝ := fun j ω => (Yc j ω).re with hRdef
  set I : ℕ → Ω → ℝ := fun j ω => (Yc j ω).im with hIdef
  have hindR : iIndepFun R P :=
    hX.indep.comp (fun _ z => (f (a + z) - f a).re)
      (fun _ => (Complex.continuous_re.comp hcont').measurable)
  have hindI : iIndepFun I P :=
    hX.indep.comp (fun _ z => (f (a + z) - f a).im)
      (fun _ => (Complex.continuous_im.comp hcont').measurable)
  have ht : 0 ≤ ε / Real.sqrt 2 := by positivity
  have hR := hoeffding_mean_two_sided hindR
    (fun j => (Complex.measurable_re.comp (hmeasY j)).aemeasurable) hL
    (fun j ω => (Complex.abs_re_le_norm _).trans (hbd j ω))
    (fun j => by have h := integral_re (hint j); rw [hzero j] at h; simpa using h) hm ht
  have hI := hoeffding_mean_two_sided hindI
    (fun j => (Complex.measurable_im.comp (hmeasY j)).aemeasurable) hL
    (fun j ω => (Complex.abs_im_le_norm _).trans (hbd j ω))
    (fun j => by have h := integral_im (hint j); rw [hzero j] at h; simpa using h) hm ht
  have hexp : -(m * (ε / Real.sqrt 2) ^ 2) / (2 * L ^ 2) = -(m * ε ^ 2) / (4 * L ^ 2) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  rw [hexp] at hR hI
  have hincl : {ω | ε ≤ ‖Aimg f a X m ω - f a‖} ⊆
      {ω | ε / Real.sqrt 2 ≤ |(m : ℝ)⁻¹ * ∑ j ∈ range m, R j ω|} ∪
        {ω | ε / Real.sqrt 2 ≤ |(m : ℝ)⁻¹ * ∑ j ∈ range m, I j ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hz : Aimg f a X m ω - f a = (((m : ℝ)⁻¹ : ℝ) : ℂ) * ∑ j ∈ range m, Yc j ω := by
      rw [Aimg_sub hm]; push_cast; rfl
    have hre : (Aimg f a X m ω - f a).re = (m : ℝ)⁻¹ * ∑ j ∈ range m, R j ω := by
      rw [hz, Complex.re_ofReal_mul, Complex.re_sum]
    have him : (Aimg f a X m ω - f a).im = (m : ℝ)⁻¹ * ∑ j ∈ range m, I j ω := by
      rw [hz, Complex.im_ofReal_mul, Complex.im_sum]
    rw [← hre] at h1; rw [← him] at h2
    have hsq2 : (ε / Real.sqrt 2) ^ 2 = ε ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have e1 : (Aimg f a X m ω - f a).re ^ 2 < ε ^ 2 / 2 := by
      rw [← hsq2, ← sq_abs]; exact pow_lt_pow_left₀ h1 (abs_nonneg _) two_ne_zero
    have e2 : (Aimg f a X m ω - f a).im ^ 2 < ε ^ 2 / 2 := by
      rw [← hsq2, ← sq_abs]; exact pow_lt_pow_left₀ h2 (abs_nonneg _) two_ne_zero
    have hn : ‖Aimg f a X m ω - f a‖ ^ 2 =
        (Aimg f a X m ω - f a).re ^ 2 + (Aimg f a X m ω - f a).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have : ε ^ 2 ≤ ‖Aimg f a X m ω - f a‖ ^ 2 := pow_le_pow_left₀ hε hω 2
    linarith
  calc P.real {ω | ε ≤ ‖Aimg f a X m ω - f a‖}
      ≤ P.real ({ω | ε / Real.sqrt 2 ≤ |(m : ℝ)⁻¹ * ∑ j ∈ range m, R j ω|} ∪
        {ω | ε / Real.sqrt 2 ≤ |(m : ℝ)⁻¹ * ∑ j ∈ range m, I j ω|}) := measureReal_mono hincl
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary29.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal NNReal BoundedContinuousFunction

namespace Barycenter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Part 29. Convergence of first absolute moments (Theorem 6.1, (6.3))

As in Part 28, the central limit theorem `√m S_m →d G` first enters as a hypothesis (it is
proved in Parts 32–35, and removed in `tendsto_scaled_abs_clt` and
`tendsto_scaled_abs_gamma_clt`). From it and the
uniform moment bound `E|√m S_m|^{2d} ≤ d! μ_d` we deduce, by a truncation (uniform
integrability) argument proved here, that `m^{d/2} E|B_m(f) - f(a)| → |c_d| E|G|^d`. -/

/-- Convergence in distribution gives convergence of expectations of bounded continuous
functions. -/
lemma TendstoInDistribution.tendsto_integral_bcf {Z : ℕ → Ω → ℂ} {G : Ω → ℂ}
    (h : TendstoInDistribution Z atTop G P) (φ : ℂ →ᵇ ℝ) :
    Tendsto (fun m => ∫ ω, φ (Z m ω) ∂P) atTop (𝓝 (∫ ω, φ (G ω) ∂P)) := by
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h.tendsto) φ
  simp only [ProbabilityMeasure.coe_mk] at this
  rw [integral_map h.aemeasurable_limit φ.continuous.aestronglyMeasurable] at this
  refine this.congr fun m => ?_
  rw [integral_map (h.forall_aemeasurable m) φ.continuous.aestronglyMeasurable]

/-- The truncation `z ↦ min(|z|^p, K)` as a bounded continuous function. -/
noncomputable def truncPow (p : ℕ) (K : ℝ) (hK : 0 ≤ K) : ℂ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun z => min (‖z‖ ^ p) K, by fun_prop⟩ K (by
    intro x y
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    have h1 : 0 ≤ min (‖x‖ ^ p) K := le_min (by positivity) hK
    have h2 : 0 ≤ min (‖y‖ ^ p) K := le_min (by positivity) hK
    have h3 := min_le_right (‖x‖ ^ p) K
    have h4 := min_le_right (‖y‖ ^ p) K
    rw [abs_le]; constructor <;> linarith)

lemma truncPow_apply (p : ℕ) (K : ℝ) (hK : 0 ≤ K) (z : ℂ) :
    truncPow p K hK z = min (‖z‖ ^ p) K := rfl

/-- `0 ≤ t - min(t, K) ≤ t²/K` for `t ≥ 0`, `K > 0`. -/
lemma sub_min_le_sq_div {t K : ℝ} (ht : 0 ≤ t) (hK : 0 < K) :
    0 ≤ t - min t K ∧ t - min t K ≤ t ^ 2 / K := by
  refine ⟨by linarith [min_le_left t K], ?_⟩
  rcases le_total t K with h | h
  · rw [min_eq_left h, sub_self]; positivity
  · rw [min_eq_right h, le_div_iff₀ hK]; nlinarith

/-- If `|W|^{2p}` is integrable, so is `|W|^p`. -/
lemma integrable_norm_pow_of_two_mul {W : Ω → ℂ} (hW : AEMeasurable W P) {p : ℕ}
    (hi : Integrable (fun ω => ‖W ω‖ ^ (2 * p)) P) : Integrable (fun ω => ‖W ω‖ ^ p) P := by
  have hm : AEStronglyMeasurable (fun ω => ‖W ω‖ ^ p) P :=
    (hW.norm.pow_const p).aestronglyMeasurable
  refine Integrable.mono' (hi.add (integrable_const 1)) hm (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h2 := pow_nonneg (norm_nonneg (W ω)) (2 * p)
  rcases le_total ‖W ω‖ 1 with h | h
  · have := pow_le_one₀ (norm_nonneg _) h (n := p); simp only [Pi.add_apply]; linarith
  · have := pow_le_pow_right₀ h (by omega : p ≤ 2 * p); simp only [Pi.add_apply]; linarith

/-- Tail estimate: `0 ≤ E|W|^p - E min(|W|^p, K) ≤ E|W|^{2p} / K`. -/
lemma tail_bound {W : Ω → ℂ} (hW : AEMeasurable W P) {p : ℕ}
    (hi : Integrable (fun ω => ‖W ω‖ ^ (2 * p)) P) {K : ℝ} (hK : 0 < K) :
    |(∫ ω, ‖W ω‖ ^ p ∂P) - ∫ ω, truncPow p K hK.le (W ω) ∂P| ≤
      (∫ ω, ‖W ω‖ ^ (2 * p) ∂P) / K := by
  have hip : Integrable (fun ω => ‖W ω‖ ^ p) P := integrable_norm_pow_of_two_mul hW hi
  have hit : Integrable (fun ω => truncPow p K hK.le (W ω)) P := by
    refine Integrable.of_bound
      ((truncPow p K hK.le).continuous.comp_aestronglyMeasurable hW.aestronglyMeasurable) K
      (Eventually.of_forall fun ω => ?_)
    rw [truncPow_apply, Real.norm_of_nonneg (le_min (by positivity) hK.le)]
    exact min_le_right _ _
  have hpt : ∀ ω, 0 ≤ ‖W ω‖ ^ p - truncPow p K hK.le (W ω) ∧
      ‖W ω‖ ^ p - truncPow p K hK.le (W ω) ≤ ‖W ω‖ ^ (2 * p) / K := by
    intro ω
    rw [truncPow_apply]
    have := sub_min_le_sq_div (pow_nonneg (norm_nonneg (W ω)) p) hK
    have e : (‖W ω‖ ^ p) ^ 2 = ‖W ω‖ ^ (2 * p) := by ring
    rwa [e] at this
  rw [← integral_sub hip hit, abs_of_nonneg (integral_nonneg fun ω => (hpt ω).1)]
  calc ∫ ω, (‖W ω‖ ^ p - truncPow p K hK.le (W ω)) ∂P
      ≤ ∫ ω, ‖W ω‖ ^ (2 * p) / K ∂P :=
        integral_mono (hip.sub hit) (hi.div_const K) (fun ω => (hpt ω).2)
    _ = _ := integral_div _ _

/-- A bound on all truncated moments gives integrability. -/
lemma integrable_of_trunc_bound {G : Ω → ℂ} (hG : AEMeasurable G P) {q : ℕ} {C : ℝ}
    (hb : ∀ K (hK : 0 ≤ K), ∫ ω, truncPow q K hK (G ω) ∂P ≤ C) :
    Integrable (fun ω => ‖G ω‖ ^ q) P ∧ ∫ ω, ‖G ω‖ ^ q ∂P ≤ C := by
  have hC0 : 0 ≤ C := by
    have := hb 0 le_rfl
    have e : ∀ ω, truncPow q 0 le_rfl (G ω) = 0 := fun ω => by
      rw [truncPow_apply]; exact min_eq_right (by positivity)
    simp only [e, integral_zero] at this; exact this
  have hint_n : ∀ n : ℕ, Integrable (fun ω => truncPow q n (Nat.cast_nonneg n) (G ω)) P := by
    intro n
    refine Integrable.of_bound
      ((truncPow q n _).continuous.comp_aestronglyMeasurable hG.aestronglyMeasurable) n
      (Eventually.of_forall fun ω => ?_)
    rw [truncPow_apply, Real.norm_of_nonneg (le_min (by positivity) (Nat.cast_nonneg n))]
    exact min_le_right _ _
  set F : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (truncPow q n (Nat.cast_nonneg n) (G ω))
    with hF
  have hFm : ∀ n, AEMeasurable (F n) P := fun n =>
    ((truncPow q n _).continuous.measurable.comp_aemeasurable hG).ennreal_ofReal
  have hmono : ∀ ω, Monotone (fun n => F n ω) := fun ω n k hnk =>
    ENNReal.ofReal_le_ofReal (by
      rw [truncPow_apply, truncPow_apply]; exact min_le_min_left _ (by exact_mod_cast hnk))
  have hsup : ∀ ω, ⨆ n, F n ω = ENNReal.ofReal (‖G ω‖ ^ q) := by
    intro ω
    refine iSup_eq_of_tendsto (hmono ω) ?_
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈‖G ω‖ ^ q⌉₊) fun n hn => ?_
    simp only [F, truncPow_apply]
    rw [min_eq_left]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hbound : ∀ n, ∫⁻ ω, F n ω ∂P ≤ ENNReal.ofReal C := fun n => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint_n n)
      (Eventually.of_forall fun ω => le_min (by positivity) (Nat.cast_nonneg n))]
    exact ENNReal.ofReal_le_ofReal (hb n _)
  have hlint : ∫⁻ ω, ENNReal.ofReal (‖G ω‖ ^ q) ∂P ≤ ENNReal.ofReal C := by
    simp_rw [← hsup]
    rw [lintegral_iSup' hFm (Eventually.of_forall hmono)]
    exact iSup_le hbound
  have hmeas : AEStronglyMeasurable (fun ω => ‖G ω‖ ^ q) P :=
    (hG.norm.pow_const q).aestronglyMeasurable
  have hInt : Integrable (fun ω => ‖G ω‖ ^ q) P := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => by positivity)]
    exact hlint.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => by positivity) hmeas]
  exact ENNReal.toReal_le_of_le_ofReal hC0 hlint

/-- **Uniform integrability.** If `Z_m → G` in distribution and `E|Z_m|^{2p} ≤ C`, then
`E|Z_m|^p → E|G|^p`. -/
theorem tendsto_integral_norm_pow_of_tendstoInDistribution {Z : ℕ → Ω → ℂ} {G : Ω → ℂ}
    (h : TendstoInDistribution Z atTop G P) {p : ℕ} {C : ℝ}
    (hint : ∀ m, Integrable (fun ω => ‖Z m ω‖ ^ (2 * p)) P)
    (hC : ∀ m, ∫ ω, ‖Z m ω‖ ^ (2 * p) ∂P ≤ C) :
    Tendsto (fun m => ∫ ω, ‖Z m ω‖ ^ p ∂P) atTop (𝓝 (∫ ω, ‖G ω‖ ^ p ∂P)) := by
  have hZm : ∀ m, AEMeasurable (Z m) P := h.forall_aemeasurable
  have hG : AEMeasurable G P := h.aemeasurable_limit
  have hC0 : 0 ≤ C := (integral_nonneg fun ω => by positivity).trans (hC 0)
  have hGb : ∀ K (hK : 0 ≤ K), ∫ ω, truncPow (2 * p) K hK (G ω) ∂P ≤ C := by
    intro K hK
    refine le_of_tendsto' (TendstoInDistribution.tendsto_integral_bcf h (truncPow (2 * p) K hK)) fun m => ?_
    have hit : Integrable (fun ω => truncPow (2 * p) K hK (Z m ω)) P := by
      refine Integrable.of_bound
        ((truncPow (2 * p) K hK).continuous.comp_aestronglyMeasurable
          (hZm m).aestronglyMeasurable) K (Eventually.of_forall fun ω => ?_)
      rw [truncPow_apply, Real.norm_of_nonneg (le_min (by positivity) hK)]
      exact min_le_right _ _
    refine (integral_mono hit (hint m) fun ω => ?_).trans (hC m)
    rw [truncPow_apply]; exact min_le_left _ _
  obtain ⟨hGi, hGC⟩ := integrable_of_trunc_bound hG hGb
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K : ℝ := 3 * (C + 1) / ε with hKdef
  have hK : 0 < K := by positivity
  have hCK : C / K < ε / 3 := by
    have e : C / K = ε / 3 * (C / (C + 1)) := by rw [hKdef]; field_simp
    rw [e]
    refine mul_lt_of_lt_one_right (by positivity) ?_
    rw [div_lt_one (by linarith)]; linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (TendstoInDistribution.tendsto_integral_bcf h (truncPow p K hK.le)) (ε / 3)
    (by positivity)
  refine ⟨N, fun m hm => ?_⟩
  have h1 := tail_bound (hZm m) (hint m) hK
  have h2 := tail_bound hG hGi hK
  have h3 := hN m hm
  rw [Real.dist_eq] at h3 ⊢
  have e1 : (∫ ω, ‖Z m ω‖ ^ (2 * p) ∂P) / K ≤ C / K := div_le_div_of_nonneg_right (hC m) hK.le
  have e2 : (∫ ω, ‖G ω‖ ^ (2 * p) ∂P) / K ≤ C / K := div_le_div_of_nonneg_right hGC hK.le
  rw [abs_le] at h1 h2
  rw [abs_lt] at h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

namespace RadialSample

variable {X : ℕ → Ω → ℂ} {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

/-- **Theorem 6.1, (6.3)** (relative to the central limit theorem). If `√m S_m → G` in
distribution, then `m^{d/2} E|B_m(f) - f(a)| → |c_d| E|G|^d`. -/
theorem tendsto_scaled_abs (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {d : ℕ} (hd : 1 ≤ d)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) {G : Ω → ℂ}
    (hCLT : TendstoInDistribution (fun (m : ℕ) ω => (Real.sqrt m : ℂ) * Scen X m ω) atTop G P) :
    Tendsto (fun m : ℕ => Real.sqrt m ^ d * ∫ ω, ‖Bimg f a X m ω - f a‖ ∂P) atTop
      (𝓝 (‖c d‖ * ∫ ω, ‖G ω‖ ^ d ∂P)) := by
  obtain ⟨hmem, hlim⟩ := hX.remainder_L2 hf hs hd hlow
  have hnormS : ∀ m n, ∫ ω, ‖Scen X m ω‖ ^ (2 * n) ∂P = qmom (radMom (X 0) P) m n := by
    intro m n
    have h := hX.cmom_Scen m n n
    rw [cmom_self, if_pos rfl] at h
    exact_mod_cast h
  have hsqrt : ∀ m k : ℕ, ‖(Real.sqrt m : ℂ)‖ ^ (2 * k) = (m : ℝ) ^ k := by
    intro m k
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), pow_mul,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have hUI := tendsto_integral_norm_pow_of_tendstoInDistribution (p := d)
    (C := d.factorial * radMom (X 0) P d) hCLT ?_ ?_
  rotate_left
  · intro m
    simp only [norm_mul, mul_pow]
    exact ((hX.allMoments_Scen m).integrable_norm_pow (2 * d)).const_mul _
  · intro m
    simp only [norm_mul, mul_pow]
    rw [integral_const_mul, hsqrt, hnormS]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [zero_pow (by omega : d ≠ 0)]
      exact mul_nonneg (by positivity) (radMom_nonneg (X := X) 0 d)
    · have h1 := hX.qmom_le m d
      have h3 := kappa_le_factorial_div (m := m) hm d
      have hm' : (0 : ℝ) < (m : ℝ) ^ d := by positivity
      have h4 : (m : ℝ) ^ d * kappa m d ≤ d.factorial := by
        rw [le_div_iff₀ hm'] at h3; linarith
      have hμ := radMom_nonneg (X := X) (P := P) 0 d
      calc (m : ℝ) ^ d * qmom (radMom (X 0) P) m d
          ≤ (m : ℝ) ^ d * (radMom (X 0) P d * kappa m d) := by gcongr
        _ = ((m : ℝ) ^ d * kappa m d) * radMom (X 0) P d := by ring
        _ ≤ d.factorial * radMom (X 0) P d := by gcongr
  have hlimX : Tendsto (fun m : ℕ => ∫ ω, ‖c d * ((Real.sqrt m : ℂ) * Scen X m ω) ^ d‖ ∂P)
      atTop (𝓝 (‖c d‖ * ∫ ω, ‖G ω‖ ^ d ∂P)) := by
    refine (hUI.const_mul ‖c d‖).congr fun m => ?_
    simp_rw [norm_mul (c d), norm_pow]
    rw [integral_const_mul]
  have hY : ∀ m : ℕ, ∫ ω, ‖(Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a)‖ ∂P =
      Real.sqrt m ^ d * ∫ ω, ‖Bimg f a X m ω - f a‖ ∂P := by
    intro m
    simp_rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact integral_const_mul _ _
  have hsq0 : Tendsto (fun m : ℕ => Real.sqrt (∫ ω, ‖(Real.sqrt m : ℂ) ^ d *
      (Bimg f a X m ω - f a) - c d * ((Real.sqrt m : ℂ) * Scen X m ω) ^ d‖ ^ 2 ∂P)) atTop
      (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    rwa [Real.sqrt_zero] at this
  have hdiff : Tendsto (fun m : ℕ =>
      (∫ ω, ‖(Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a)‖ ∂P) -
        ∫ ω, ‖c d * ((Real.sqrt m : ℂ) * Scen X m ω) ^ d‖ ∂P) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hsq0
    filter_upwards [hmem, eventually_ge_atTop 1] with m hD hm
    have hYi : Integrable (fun ω => (Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a)) P :=
      ((hX.memLp_comp_S hm hf hs).const_mul _).integrable one_le_two
    have hDi := hD.integrable one_le_two
    have hXi : Integrable (fun ω => c d * ((Real.sqrt m : ℂ) * Scen X m ω) ^ d) P := by
      have := hYi.sub hDi
      refine this.congr (Eventually.of_forall fun ω => ?_)
      simp only [Pi.sub_apply]; ring
    rw [Real.norm_eq_abs, ← integral_sub hYi.norm hXi.norm]
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono (hYi.norm.sub hXi.norm).abs hDi.norm fun ω => ?_).trans
      (integral_norm_le_sqrt hD)
    exact abs_norm_sub_norm_le _ _
  have := hlimX.add hdiff
  rw [add_zero] at this
  refine this.congr fun m => ?_
  rw [← hY]; ring

/-- **Proposition 6.2 (joint fluctuations)**, the joint limit law (relative to the
two-dimensional central limit theorem for the pair `(X, f(a+X))`). If
`√m (S_m, A_m(f) - f(a)) → (G, H)` in distribution, then
`(√m (A_m(f) - f(a)), m^{d/2} (B_m(f) - f(a))) → (H, c_d G^d)` in distribution. -/
theorem tendstoInDistribution_joint (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {d : ℕ} (hd : 1 ≤ d)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) {G H : Ω → ℂ}
    (hCLT : TendstoInDistribution (fun (m : ℕ) ω => ((Real.sqrt m : ℂ) * Scen X m ω,
      (Real.sqrt m : ℂ) * (Aimg f a X m ω - f a))) atTop (fun ω => (G ω, H ω)) P) :
    TendstoInDistribution (fun (m : ℕ) ω => ((Real.sqrt m : ℂ) * (Aimg f a X m ω - f a),
      (Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a))) atTop
      (fun ω => (H ω, c d * G ω ^ d)) P := by
  obtain ⟨hmem, hlim⟩ := hX.remainder_L2 hf hs hd hlow
  have hT := tendstoInMeasure_zero_of_integral_norm_sq hmem hlim
  have hcont : Continuous (fun z => f (a + z)) := continuous_of_hasSum hf
  have hX' := hCLT.continuous_comp (g := fun p : ℂ × ℂ => (p.2, c d * p.1 ^ d)) (by fun_prop)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX' ?_ ?_
  · intro ε hε
    refine (hT ε hε).congr fun m => ?_
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, Pi.sub_apply, Function.comp_apply, Pi.zero_apply,
      Prod.mk_sub_mk, sub_self, Prod.edist_eq, Prod.fst_zero, Prod.snd_zero, edist_self,
      zero_le, max_eq_right]
  · intro m
    have hB : Measurable (fun ω => Bimg f a X m ω) :=
      hcont.measurable.comp (hX.measurable_Scen m)
    have hA : Measurable (fun ω => Aimg f a X m ω) :=
      measurable_const.mul (Finset.measurable_sum _ fun j _ =>
        hcont.measurable.comp (hX.meas j))
    exact ((measurable_const.mul (hA.sub measurable_const)).prodMk
      (measurable_const.mul (hB.sub measurable_const))).aemeasurable

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary30.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal NNReal Real

namespace Barycenter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Part 30. Proper complex Gaussians and the constant in (6.3)

A proper complex Gaussian of variance `v > 0` has density `(π v)⁻¹ e^{-|z|²/v}` on `ℂ`
(equivalently, independent real and imaginary parts with law `N(0, v/2)`). We compute
`E|G|^d = v^{d/2} Γ(1 + d/2)` and obtain Theorem 6.1, (6.3) in the paper's closed form. -/

/-- The density `(π v)⁻¹ e^{-|z|²/v}` of a proper complex Gaussian of variance `v`. -/
noncomputable def cgaussDensity (v : ℝ) (z : ℂ) : ℝ := (π * v)⁻¹ * Real.exp (-‖z‖ ^ 2 / v)

/-- `G` is a proper complex Gaussian of variance `v`: its law has density `cgaussDensity v`. -/
structure IsProperComplexGaussian (G : Ω → ℂ) (v : ℝ) (P : Measure Ω) : Prop where
  aemeasurable : AEMeasurable G P
  law : P.map G = volume.withDensity (fun z => ENNReal.ofReal (cgaussDensity v z))

omit [IsProbabilityMeasure P] in
/-- Absolute moments of a proper complex Gaussian: `E|G|^d = v^{d/2} Γ(1 + d/2)`. -/
theorem IsProperComplexGaussian.integral_norm_pow {G : Ω → ℂ} {v : ℝ} (hv : 0 < v)
    (hG : IsProperComplexGaussian G v P) (d : ℕ) :
    ∫ ω, ‖G ω‖ ^ d ∂P = v ^ ((d : ℝ) / 2) * Real.Gamma (1 + (d : ℝ) / 2) := by
  have hmeasd : Measurable (fun z : ℂ => ENNReal.ofReal (cgaussDensity v z)) := by
    unfold cgaussDensity; fun_prop
  have hdens_nn : ∀ z, 0 ≤ cgaussDensity v z := fun z => by
    unfold cgaussDensity; have := Real.pi_pos; positivity
  rw [← integral_map (f := fun z : ℂ => ‖z‖ ^ d) hG.aemeasurable (by fun_prop), hG.law,
    integral_withDensity_eq_integral_toReal_smul hmeasd
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hdens_nn _), smul_eq_mul, cgaussDensity]
  have key := integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun y : ℝ => (π * v)⁻¹ * Real.exp (-y ^ 2 / v) * y ^ d)
  simp only at key
  rw [key, Complex.finrank_real_complex, Measure.real, Complex.volume_ball]
  have hI : ∫ y in Set.Ioi (0 : ℝ), y ^ (2 - 1) • ((π * v)⁻¹ * Real.exp (-y ^ 2 / v) * y ^ d) =
      (π * v)⁻¹ * ((1 / v) ^ (-(((d + 1 : ℕ) : ℝ) + 1) / 2) * (1 / 2) *
        Real.Gamma ((((d + 1 : ℕ) : ℝ) + 1) / 2)) := by
    rw [← integral_rpow_mul_exp_neg_mul_rpow (p := 2) two_pos
      (by have := (Nat.cast_nonneg (α := ℝ) (d + 1)); linarith : (-1 : ℝ) < ((d + 1 : ℕ) : ℝ)) (by positivity : (0 : ℝ) < 1 / v),
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    simp only [smul_eq_mul, Real.rpow_natCast]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have e : -y ^ 2 / v = -(1 / v) * y ^ 2 := by ring
    rw [e]; ring
  rw [hI]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.coe_toReal, NNReal.coe_real_pi,
    nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  push_cast
  have hg : ((d : ℝ) + 1 + 1) / 2 = 1 + d / 2 := by ring
  have hp : (1 / v) ^ (-((d : ℝ) + 1 + 1) / 2) = v ^ ((d : ℝ) / 2) * v := by
    rw [one_div, Real.inv_rpow hv.le, ← Real.rpow_neg hv.le, neg_div, neg_neg,
      show ((d : ℝ) + 1 + 1) / 2 = d / 2 + 1 by ring, Real.rpow_add hv, Real.rpow_one]
  rw [hg, hp]
  have := Real.pi_pos
  field_simp

omit [IsProbabilityMeasure P] in
/-- **Table 3.1, Gaussian row.** The radial moments of a proper complex Gaussian of variance
`v > 0` are `μ_n = E|G|^{2n} = n! vⁿ`. -/
theorem IsProperComplexGaussian.radMom_eq {G : Ω → ℂ} {v : ℝ} (hv : 0 < v)
    (hG : IsProperComplexGaussian G v P) (n : ℕ) :
    radMom G P n = n.factorial * v ^ n := by
  rw [radMom, hG.integral_norm_pow hv (2 * n)]
  push_cast
  rw [show (2 * (n : ℝ)) / 2 = n by ring, Real.rpow_natCast, add_comm,
    Real.Gamma_nat_eq_factorial]
  ring

/-- **Remark in Section 2 (where the `n`th power sends a dart).** For a uniform dart `Z` on the
unit disk, `P(|Zⁿ| ≤ s) = s^{2/n}` for `0 ≤ s ≤ 1`. -/
theorem disk_pow_cdf {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    diskLaw.real {z : ℂ | ‖z ^ n‖ ≤ s} = s ^ ((2 : ℝ) / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set t := s ^ ((n : ℝ)⁻¹) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hs0 _
  have ht1 : t ≤ 1 := Real.rpow_le_one hs0 hs1 (by positivity)
  have hset : {z : ℂ | ‖z ^ n‖ ≤ s} = Metric.closedBall (0 : ℂ) t := by
    ext z
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right, norm_pow]
    rw [ht, Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hs0 hnpos, Real.rpow_natCast]
  have hinter : Metric.closedBall (0 : ℂ) t ∩ Metric.closedBall (0 : ℂ) 1 =
      Metric.closedBall (0 : ℂ) t :=
    Set.inter_eq_left.2 (Metric.closedBall_subset_closedBall ht1)
  rw [hset, Measure.real, diskLaw, Measure.smul_apply,
    Measure.restrict_apply measurableSet_closedBall, hinter, Complex.volume_closedBall,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (inv_nonneg.2 Real.pi_pos.le), ENNReal.toReal_ofReal ht0,
    ENNReal.coe_toReal, NNReal.coe_real_pi]
  have htt : t ^ 2 = s ^ ((2 : ℝ) / n) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hs0]
    congr 1; push_cast; ring
  rw [htt]
  field_simp [Real.pi_ne_zero]

namespace RadialSample

variable {X : ℕ → Ω → ℂ} {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

/-- **Theorem 6.1, (6.3)** in closed form (relative to the central limit theorem): if
`√m S_m → G` in distribution with `G` a proper complex Gaussian of variance `μ₁ > 0`, then
`m^{d/2} E|B_m(f) - f(a)| → |c_d| μ₁^{d/2} Γ(1 + d/2)`. -/
theorem tendsto_scaled_abs_gamma (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {d : ℕ} (hd : 1 ≤ d)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) (hμ : 0 < radMom (X 0) P 1) {G : Ω → ℂ}
    (hG : IsProperComplexGaussian G (radMom (X 0) P 1) P)
    (hCLT : TendstoInDistribution (fun (m : ℕ) ω => (Real.sqrt m : ℂ) * Scen X m ω) atTop G P) :
    Tendsto (fun m : ℕ => Real.sqrt m ^ d * ∫ ω, ‖Bimg f a X m ω - f a‖ ∂P) atTop
      (𝓝 (‖c d‖ * radMom (X 0) P 1 ^ ((d : ℝ) / 2) * Real.Gamma (1 + (d : ℝ) / 2))) := by
  have h := hX.tendsto_scaled_abs hf hs hd hlow hCLT
  rwa [hG.integral_norm_pow hμ d, ← mul_assoc] at h

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary31.lean
-- ============================================================================

open Finset BigOperators Filter Topology MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

namespace Barycenter

/-! ## Part 31. The exponential map on the disk (Example 5.1) -/

/-- Terms `|c_{n+1}|²/(n+2) = 1/((n+2) ((n+1)!)²)` of `V_{e^z}` for unit-disk sampling. -/
noncomputable def expDiskTerm (n : ℕ) : ℝ := (1 / ((n + 1).factorial : ℝ)) ^ 2 / (n + 2)

/-- `V_{e^z} = ∑_{n ≥ 1} 1/((n+1)(n!)²)` for unit-disk sampling (equal to `I₁(2) - 1`). -/
noncomputable def expDiskV : ℝ := ∑' n : ℕ, expDiskTerm n

lemma expDiskTerm_nonneg (n : ℕ) : 0 ≤ expDiskTerm n := by
  unfold expDiskTerm; positivity

lemma expDiskTerm_succ_le (n : ℕ) : expDiskTerm (n + 1) ≤ expDiskTerm n / 6 := by
  unfold expDiskTerm
  rw [Nat.factorial_succ (n + 1)]
  push_cast
  have hf : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  field_simp
  nlinarith [sq_nonneg (n : ℝ), mul_pos hf hf]

lemma expDiskTerm_add_le (N k : ℕ) : expDiskTerm (k + N) ≤ expDiskTerm N * (1 / 6) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + N = (k + N) + 1 by ring, pow_succ]
    have := expDiskTerm_succ_le (k + N)
    nlinarith [expDiskTerm_nonneg (k + N)]

lemma summable_expDiskTerm : Summable expDiskTerm := by
  refine Summable.of_nonneg_of_le expDiskTerm_nonneg (fun n => ?_)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 6) (by norm_num)).mul_left
      (expDiskTerm 0))
  simpa using expDiskTerm_add_le 0 n

/-- **Example 5.1, the value of `V_f`.** `0.5906368 < V_{e^z} < 0.5906369` (the paper:
`V_f = I₁(2) - 1 = 0.590637…`). -/
theorem expDiskV_bounds : 0.5906368 < expDiskV ∧ expDiskV < 0.5906369 := by
  have hsplit := Summable.sum_add_tsum_nat_add 7 summable_expDiskTerm
  have hpart : ∑ i ∈ range 7, expDiskTerm i = 40008323 / 67737600 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, expDiskTerm, Nat.factorial]
    norm_num
  have htail_nn : 0 ≤ ∑' k, expDiskTerm (k + 7) :=
    tsum_nonneg fun k => expDiskTerm_nonneg _
  have htail_le : ∑' k, expDiskTerm (k + 7) ≤ expDiskTerm 7 * (6 / 5) := by
    have hg := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 6)
      (by norm_num)).mul_left (expDiskTerm 7)
    refine (Summable.tsum_le_tsum (fun k => expDiskTerm_add_le 7 k)
      ((summable_nat_add_iff 7).2 summable_expDiskTerm) hg).trans ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have h7 : expDiskTerm 7 = 1 / 14631321600 := by
    simp only [expDiskTerm, Nat.factorial]; norm_num
  rw [expDiskV, ← hsplit, hpart]
  rw [h7] at htail_le
  constructor <;> norm_num at htail_le ⊢ <;> linarith

/-- **Example 5.1.** For `f(z) = e^z` and unit-disk darts, `E|A_m(e^z) - 1|² = V_{e^z}/m`, with
`V_{e^z} = ∑_{n≥1} 1/((n+1)(n!)²) ∈ (0.5906368, 0.5906369)`. -/
theorem exp_disk_example {m : ℕ} (hm : 1 ≤ m) :
    ∫ ω, ‖Aimg (expShift 1 0) 0 coord m ω - 1‖ ^ 2 ∂diskP = expDiskV / m := by
  have h := disk_A (hasSum_expCoef 1 0) hm
  have e1 : expShift 1 0 0 = 1 := by simp [expShift]
  rw [e1] at h
  rw [h, expDiskV]
  congr 2
  ext n
  simp only [expDiskTerm, expCoef, one_pow, norm_div, norm_one, Complex.norm_natCast]

/-- Terms `|c_{n+1}|² q_{m,n+1}` of `E|B_m(e^z) - 1|²` for unit-disk sampling. -/
noncomputable def expDiskBTerm (m n : ℕ) : ℝ :=
  (1 / ((n + 1).factorial : ℝ)) ^ 2 * qmom diskMom m (n + 1)

lemma factorial_add_six_ge (k : ℕ) : (720 : ℝ) * 7 ^ k ≤ ((k + 6).factorial : ℝ) := by
  induction k with
  | zero => norm_num [Nat.factorial]
  | succ k ih =>
    rw [show k + 1 + 6 = (k + 6) + 1 by ring, Nat.factorial_succ, pow_succ]
    push_cast
    nlinarith

lemma expDiskBTerm_nonneg (m n : ℕ) : 0 ≤ expDiskBTerm m n :=
  mul_nonneg (by positivity) (qmom_nonneg _ diskMom_nonneg m _)

lemma expDiskBTerm_tail_le {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    expDiskBTerm m (k + 5) ≤ (1 / m) * (1 / 518400) * (1 / 49) ^ k := by
  have hq : qmom diskMom m (k + 5 + 1) ≤ 1 / m := by
    have h1 := disk_radialSample.qmom_le m (k + 5 + 1)
    rw [radMom_disk] at h1
    have h2 := kappa_le_inv hm (by omega : 1 ≤ k + 5 + 1)
    have h3 : diskMom (k + 5 + 1) ≤ 1 := by
      rw [diskMom, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg (α := ℝ) (k + 5 + 1))]
    have h4 := kappa_pos hm (k + 5 + 1)
    calc qmom diskMom m (k + 5 + 1) ≤ diskMom (k + 5 + 1) * kappa m (k + 5 + 1) := h1
      _ ≤ 1 * (1 / m) := by
        apply mul_le_mul h3 h2 h4.le (by norm_num)
      _ = 1 / m := one_mul _
  have hf := factorial_add_six_ge k
  have hf' : (1 / ((k + 5 + 1).factorial : ℝ)) ^ 2 ≤ (1 / 518400) * (1 / 49) ^ k := by
    rw [show k + 5 + 1 = k + 6 by ring]
    have hF : (0 : ℝ) < (k + 6).factorial := by exact_mod_cast Nat.factorial_pos _
    have e : (1 / 518400 : ℝ) * (1 / 49) ^ k = 1 / (720 * 7 ^ k) ^ 2 := by
      rw [mul_pow, ← pow_mul, one_div_pow, mul_comm k 2, pow_mul]; norm_num; ring
    rw [e, one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
    exact pow_le_pow_left₀ (by positivity) hf 2
  unfold expDiskBTerm
  calc (1 / ((k + 5 + 1).factorial : ℝ)) ^ 2 * qmom diskMom m (k + 5 + 1)
      ≤ ((1 / 518400) * (1 / 49) ^ k) * (1 / m) :=
        mul_le_mul hf' hq (qmom_nonneg _ diskMom_nonneg m _) (by positivity)
    _ = _ := by ring

lemma integral_expDisk_B {m : ℕ} (hm : 1 ≤ m) :
    ∫ ω, ‖Bimg (expShift 1 0) 0 coord m ω - 1‖ ^ 2 ∂diskP = ∑' n, expDiskBTerm m n := by
  have hf := hasSum_expCoef 1 0
  have h := disk_radialSample.integral_norm_sq_Bimg hm hf (disk_summable hf)
  have e1 : expShift 1 0 0 = 1 := by simp [expShift]
  rw [e1, radMom_disk] at h
  rw [h]
  congr 1; ext n
  simp only [expDiskBTerm, expCoef, one_pow, norm_div, norm_one, Complex.norm_natCast]

lemma expDisk_B_bounds {m : ℕ} (hm : 1 ≤ m) :
    ∑ n ∈ range 5, expDiskBTerm m n ≤
      ∫ ω, ‖Bimg (expShift 1 0) 0 coord m ω - 1‖ ^ 2 ∂diskP ∧
    ∫ ω, ‖Bimg (expShift 1 0) 0 coord m ω - 1‖ ^ 2 ∂diskP ≤
      ∑ n ∈ range 5, expDiskBTerm m n + (1 / m) * (1 / 518400) * (49 / 48) := by
  have hg := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 49)
    (by norm_num)).mul_left ((1 / (m : ℝ)) * (1 / 518400))
  have hsum_tail : Summable fun k => expDiskBTerm m (k + 5) :=
    Summable.of_nonneg_of_le (fun k => expDiskBTerm_nonneg m _) (expDiskBTerm_tail_le hm) hg
  have hsum : Summable (expDiskBTerm m) := (summable_nat_add_iff 5).1 hsum_tail
  have hsplit := Summable.sum_add_tsum_nat_add 5 hsum
  have htail_nn : 0 ≤ ∑' k, expDiskBTerm m (k + 5) :=
    tsum_nonneg fun k => expDiskBTerm_nonneg m _
  have htail_le : ∑' k, expDiskBTerm m (k + 5) ≤ (1 / m) * (1 / 518400) * (49 / 48) := by
    refine (Summable.tsum_le_tsum (expDiskBTerm_tail_le hm) hsum_tail hg).trans ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  rw [integral_expDisk_B hm, ← hsplit]
  constructor <;> linarith

/-- **Example 5.1, the image of the center.** For `f(z) = e^z` and unit-disk darts,
`E|B_{10}(e^z) - 1|² ≈ 0.05123` and `E|B_{100}(e^z) - 1|² ≈ 0.005012`; precisely
`0.051227 < E|B_{10} - 1|² < 0.051228` and `0.0050124 < E|B_{100} - 1|² < 0.0050125`. The
corresponding values for `A_m` are `V/10 ≈ 0.05906` and `V/100 ≈ 0.005906`
(`exp_disk_example`, `expDiskV_bounds`). -/
theorem exp_disk_B_values :
    (0.051227 < ∫ ω, ‖Bimg (expShift 1 0) 0 coord 10 ω - 1‖ ^ 2 ∂diskP ∧
      ∫ ω, ‖Bimg (expShift 1 0) 0 coord 10 ω - 1‖ ^ 2 ∂diskP < 0.051228) ∧
    (0.0050124 < ∫ ω, ‖Bimg (expShift 1 0) 0 coord 100 ω - 1‖ ^ 2 ∂diskP ∧
      ∫ ω, ‖Bimg (expShift 1 0) 0 coord 100 ω - 1‖ ^ 2 ∂diskP < 0.0050125) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := table_disk_m10
  obtain ⟨b1, b2, b3, b4, b5⟩ := table_disk_m100
  obtain ⟨l10, u10⟩ := expDisk_B_bounds (m := 10) (by norm_num)
  obtain ⟨l100, u100⟩ := expDisk_B_bounds (m := 100) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, expDiskBTerm, Nat.factorial,
    zero_add, Nat.reduceAdd, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5] at l10 u10 l100 u100
  norm_num at l10 u10 l100 u100
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num <;> linarith

end Barycenter

-- ============================================================================
-- Source part: Bary32.lean
-- ============================================================================

open Filter Topology MeasureTheory ProbabilityTheory Complex
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace Barycenter

/-! ## Part 32. Lévy's continuity theorem in finite-dimensional inner product spaces

If the characteristic functions of a sequence of probability measures on a finite-dimensional
real inner product space converge pointwise to the characteristic function of a probability
measure, then the measures converge weakly. This is the analytic engine of the central limit
theorem proved in Parts 33–34. -/

section Levy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
/-- The characteristic function at a fixed point is a continuous function of the measure
(for the topology of weak convergence). -/
lemma continuous_charFun_probabilityMeasure (t : E) :
    Continuous (fun μ : ProbabilityMeasure E => charFun (μ : Measure E) t) := by
  simp_rw [charFun_eq_integral_innerProbChar]
  exact continuous_iff_continuousAt.2 fun μ =>
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 tendsto_id
      (BoundedContinuousFunction.innerProbChar t)

/-- The characteristic function of a finite measure is continuous. -/
lemma continuous_charFun_of_finite (μ : Measure E) [IsFiniteMeasure μ] :
    Continuous (charFun μ) := by
  unfold charFun
  refine continuous_of_dominated (bound := fun _ => 1) (fun t => by fun_prop)
    (fun t => Eventually.of_forall fun x => ?_) (integrable_const _)
    (Eventually.of_forall fun x => by fun_prop)
  rw [Complex.norm_exp_ofReal_mul_I]

/-- A single probability measure puts vanishing mass far out in every direction. -/
lemma tendsto_measure_inner_gt_single (μ : Measure E) [IsProbabilityMeasure μ] (y : E) :
    Tendsto (fun r : ℝ => μ {x | r < ‖⟪y, x⟫‖}) atTop (𝓝 0) := by
  have h := (isTightMeasureSet_iff_inner_tendsto ℝ (S := {μ})).1
    (isTightMeasureSet_singleton) y
  simpa using h

/-- The key estimate behind tightness: if `φ_n(t y) → φ(t y)` then, uniformly in large `n`, the
mass `μ_n{r₀ < |⟪y,x⟫|}` is small for a suitable `r₀`. -/
lemma eventually_measure_inner_gt_le {μ : ℕ → ProbabilityMeasure E} {μ₀ : ProbabilityMeasure E}
    (h : ∀ t, Tendsto (fun n => charFun (μ n : Measure E) t) atTop
      (𝓝 (charFun (μ₀ : Measure E) t)))
    (y : E) {e : ℝ} (he : 0 < e) :
    ∃ r₀ > 0, ∃ N : ℕ, ∀ n ≥ N, (μ n : Measure E).real {x | r₀ < |⟪y, x⟫|} ≤ e := by
  -- continuity of `t ↦ φ(t y)` at `0`
  have hc : Continuous (fun t : ℝ => 1 - charFun (μ₀ : Measure E) (t • y)) :=
    continuous_const.sub ((continuous_charFun_of_finite _).comp (continuous_id.smul continuous_const))
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.1 hc 0 (e / 4) (by positivity)
  have hδ' : ∀ t ∈ Set.uIoc (-(δ / 2)) (δ / 2), ‖1 - charFun (μ₀ : Measure E) (t • y)‖ ≤ e / 4 := by
    intro t ht
    have : dist t 0 < δ := by
      rw [Set.uIoc_of_le (by linarith)] at ht
      rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith [ht.1, ht.2]
    have := hδc t this
    rw [zero_smul, charFun_zero, probReal_univ, ofReal_one, sub_self,
      dist_zero_right] at this
    exact this.le
  set r₀ : ℝ := 4 / δ with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  have hr₀inv : 2 * r₀⁻¹ = δ / 2 := by rw [hr₀]; field_simp; ring
  -- the limiting bound
  have hlimbd : 2⁻¹ * r₀ * ‖∫ t in (-2 * r₀⁻¹)..(2 * r₀⁻¹), 1 - charFun (μ₀ : Measure E) (t • y)‖
      ≤ e / 2 := by
    rw [neg_mul, hr₀inv]
    have := intervalIntegral.norm_integral_le_of_norm_le_const hδ'
    calc 2⁻¹ * r₀ * ‖∫ t in (-(δ / 2))..(δ / 2), 1 - charFun (μ₀ : Measure E) (t • y)‖
        ≤ 2⁻¹ * r₀ * (e / 4 * |δ / 2 - -(δ / 2)|) := by gcongr
      _ = e / 2 := by
        rw [show δ / 2 - -(δ / 2) = δ by ring, abs_of_pos hδ, hr₀]; field_simp
  -- convergence of the interval integrals
  have hconv : Tendsto (fun n => 2⁻¹ * r₀ *
      ‖∫ t in (-2 * r₀⁻¹)..(2 * r₀⁻¹), 1 - charFun (μ n : Measure E) (t • y)‖) atTop
      (𝓝 (2⁻¹ * r₀ *
        ‖∫ t in (-2 * r₀⁻¹)..(2 * r₀⁻¹), 1 - charFun (μ₀ : Measure E) (t • y)‖)) := by
    refine (Tendsto.norm ?_).const_mul _
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 2) ?_ ?_
      intervalIntegrable_const ?_
    · exact Eventually.of_forall fun n =>
        (continuous_const.sub ((continuous_charFun_of_finite _).comp
          (continuous_id.smul continuous_const))).aestronglyMeasurable
    · exact Eventually.of_forall fun n => Eventually.of_forall fun t _ =>
        norm_one_sub_charFun_le_two
    · exact Eventually.of_forall fun t _ => tendsto_const_nhds.sub (h (t • y))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hconv.eventually (gt_mem_nhds
    (show _ < e from lt_of_le_of_lt hlimbd (by linarith))))
  refine ⟨r₀, hr₀pos, N, fun n hn => ?_⟩
  exact (measureReal_abs_inner_gt_le_integral_charFun hr₀pos).trans (hN n hn).le

/-- **Tightness from convergence of characteristic functions.** -/
lemma isTightMeasureSet_of_tendsto_charFun {μ : ℕ → ProbabilityMeasure E}
    {μ₀ : ProbabilityMeasure E}
    (h : ∀ t, Tendsto (fun n => charFun (μ n : Measure E) t) atTop
      (𝓝 (charFun (μ₀ : Measure E) t))) :
    IsTightMeasureSet {((ν : ProbabilityMeasure E) : Measure E) | ν ∈ Set.range μ} := by
  refine isTightMeasureSet_of_inner_tendsto (𝕜 := ℝ) fun y => ?_
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  -- reduce to a real tolerance
  obtain ⟨e, he, heε⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ ε := by
    rcases eq_or_ne ε ⊤ with rfl | hne
    · exact ⟨1, one_pos, le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hne, by rw [ENNReal.ofReal_toReal hne]⟩
  obtain ⟨r₀, hr₀, N, hN⟩ := eventually_measure_inner_gt_le h y he
  -- finitely many initial measures
  have hfin : ∀ n, ∃ k : ℕ, ∀ r : ℝ, (k : ℝ) ≤ r → (μ n : Measure E) {x | r < ‖⟪y, x⟫‖} ≤ ε := by
    intro n
    have := (ENNReal.tendsto_atTop_zero.1 (tendsto_measure_inner_gt_single (μ n : Measure E) y))
      ε hε
    obtain ⟨R, hR⟩ := this
    obtain ⟨k, hk⟩ := exists_nat_ge R
    exact ⟨k, fun r hr => hR r (hk.trans hr)⟩
  choose K hK using hfin
  refine ⟨max r₀ ((Finset.range N).sup K : ℕ), fun r hr => ?_⟩
  refine iSup₂_le fun ν hν => ?_
  obtain ⟨_, ⟨n, rfl⟩, rfl⟩ := hν
  rcases lt_or_ge n N with hn | hn
  · refine hK n r (le_trans ?_ ((le_max_right _ _).trans hr))
    exact_mod_cast Finset.le_sup (f := K) (Finset.mem_range.2 hn)
  · calc (μ n : Measure E) {x | r < ‖⟪y, x⟫‖}
        ≤ (μ n : Measure E) {x | r₀ < |⟪y, x⟫|} := by
          refine measure_mono fun x hx => ?_
          simp only [Set.mem_setOf_eq, Real.norm_eq_abs] at hx ⊢
          exact lt_of_le_of_lt ((le_max_left _ _).trans hr) hx
      _ = ENNReal.ofReal ((μ n : Measure E).real {x | r₀ < |⟪y, x⟫|}) := by
          rw [ofReal_measureReal]
      _ ≤ ENNReal.ofReal e := ENNReal.ofReal_le_ofReal (hN n hn)
      _ ≤ ε := heε

/-- **Lévy's continuity theorem** (finite-dimensional real inner product spaces): if the
characteristic functions of probability measures `μ n` converge pointwise to the characteristic
function of a probability measure `μ₀`, then `μ n → μ₀` weakly. -/
theorem tendsto_of_tendsto_charFun {μ : ℕ → ProbabilityMeasure E} {μ₀ : ProbabilityMeasure E}
    (h : ∀ t, Tendsto (fun n => charFun (μ n : Measure E) t) atTop
      (𝓝 (charFun (μ₀ : Measure E) t))) :
    Tendsto μ atTop (𝓝 μ₀) := by
  have hcomp := isCompact_closure_of_isTightMeasureSet (isTightMeasureSet_of_tendsto_charFun h)
  refine hcomp.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n => subset_closure (Set.mem_range_self n)) fun ν _ hν => ?_
  -- a cluster point has the same characteristic function as `μ₀`
  have hchar : ∀ t, charFun (ν : Measure E) t = charFun (μ₀ : Measure E) t := by
    intro t
    have h1 : MapClusterPt (charFun (ν : Measure E) t) atTop
        (fun n => charFun (μ n : Measure E) t) :=
      hν.continuousAt_comp (continuous_charFun_probabilityMeasure t).continuousAt
    exact eq_of_nhds_neBot (Filter.NeBot.mono h1 (inf_le_inf_left _ (h t)))
  exact ProbabilityMeasure.toMeasure_injective (Measure.ext_of_charFun (funext hchar))

end Levy

end Barycenter

-- ============================================================================
-- Source part: Bary33.lean
-- ============================================================================

open Finset Filter Topology MeasureTheory ProbabilityTheory Complex
open scoped ENNReal

namespace Barycenter

/-! ## Part 33. Characteristic functions of normalised sums (one-dimensional CLT estimate)

For i.i.d. real random variables `Y j` with mean `0` and finite variance `σ²`,
`E exp(i (Y₀ + ⋯ + Y_{n-1}) / √n) → exp(-σ²/2)`. -/

/-- Second-order Taylor bound for `e^{ix}`: `|e^{ix} - (1 + ix - x²/2)| ≤ 4 min(|x|³, x²)`. -/
lemma norm_exp_mul_I_sub_taylor_le (x : ℝ) :
    ‖exp (x * I) - (1 + x * I - (x : ℂ) ^ 2 / 2)‖ ≤ 4 * min (|x| ^ 3) (x ^ 2) := by
  have hnI : ‖(x : ℂ) * I‖ = |x| := by simp
  rcases le_or_gt |x| 1 with hx | hx
  · have hb := Complex.exp_bound (x := x * I) (by rw [hnI]; exact hx) (n := 3) (by norm_num)
    have hs : ∑ m ∈ range 3, ((x : ℂ) * I) ^ m / m.factorial = 1 + x * I - (x : ℂ) ^ 2 / 2 := by
      simp [Finset.sum_range_succ, mul_pow, I_sq]; ring
    rw [hs, hnI] at hb
    have hmin : min (|x| ^ 3) (x ^ 2) = |x| ^ 3 := by
      apply min_eq_left
      rw [← sq_abs x]
      have := abs_nonneg x
      nlinarith [pow_le_pow_left₀ this hx 2]
    rw [hmin]
    refine hb.trans ?_
    have : (0:ℝ) ≤ |x| ^ 3 := by positivity
    norm_num
    nlinarith
  · have hmin : min (|x| ^ 3) (x ^ 2) = x ^ 2 := by
      apply min_eq_right
      rw [← sq_abs x]
      have := abs_nonneg x
      nlinarith
    rw [hmin]
    have h1 : ‖(1 : ℂ) + x * I - (x : ℂ) ^ 2 / 2‖ ≤ ‖(1:ℂ)‖ + ‖(x : ℂ) * I‖ + ‖(x : ℂ) ^ 2 / 2‖ :=
      (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    calc ‖exp (x * I) - (1 + x * I - (x : ℂ) ^ 2 / 2)‖
        ≤ ‖exp (x * I)‖ + (‖(1:ℂ)‖ + ‖(x : ℂ) * I‖ + ‖(x : ℂ) ^ 2 / 2‖) :=
          (norm_sub_le _ _).trans (by gcongr)
      _ = 1 + (1 + |x| + x ^ 2 / 2) := by
          rw [norm_exp_ofReal_mul_I, hnI]; simp [norm_pow]
      _ ≤ 4 * x ^ 2 := by
          rw [← sq_abs x]; nlinarith

section Sums

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The characteristic function of a centred square-integrable variable near `0`. -/
lemma norm_integral_exp_sub_le {Y : Ω → ℝ} (hY : MemLp Y 2 P) (hmean : ∫ ω, Y ω ∂P = 0)
    (s : ℝ) :
    ‖∫ ω, exp ((s * Y ω : ℝ) * I) ∂P - (1 - (s : ℂ) ^ 2 * (∫ ω, Y ω ^ 2 ∂P : ℝ) / 2)‖ ≤
      4 * ∫ ω, min (|s * Y ω| ^ 3) ((s * Y ω) ^ 2) ∂P := by
  have hY1 : Integrable Y P := hY.integrable one_le_two
  have hY2 : Integrable (fun ω => Y ω ^ 2) P := hY.integrable_sq
  have hm : AEStronglyMeasurable Y P := hY.1
  have hexp : Integrable (fun ω => exp ((s * Y ω : ℝ) * I)) P := by
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact (Complex.continuous_exp.comp ((continuous_ofReal.comp
        (continuous_const.mul continuous_id)).mul continuous_const)).comp_aestronglyMeasurable hm
    · rw [norm_exp_ofReal_mul_I]
  have hlin : Integrable (fun ω => ((s * Y ω : ℝ) : ℂ) * I) P :=
    ((hY1.const_mul s).ofReal).mul_const _
  have hquad : Integrable (fun ω => (((s * Y ω : ℝ) : ℂ)) ^ 2 / 2) P := by
    have : Integrable (fun ω => ((s ^ 2 / 2 * Y ω ^ 2 : ℝ) : ℂ)) P :=
      (hY2.const_mul (s ^ 2 / 2)).ofReal
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    push_cast; ring
  have hpoly : Integrable
      (fun ω => (1 : ℂ) + ((s * Y ω : ℝ) : ℂ) * I - ((s * Y ω : ℝ) : ℂ) ^ 2 / 2) P :=
    ((integrable_const _).add hlin).sub hquad
  have e1 : ∫ ω, ((s * Y ω : ℝ) : ℂ) * I ∂P = 0 := by
    rw [integral_mul_const, integral_complex_ofReal, integral_const_mul, hmean]; simp
  have e2 : ∫ ω, (((s * Y ω : ℝ) : ℂ)) ^ 2 / 2 ∂P =
      (s : ℂ) ^ 2 * (∫ ω, Y ω ^ 2 ∂P : ℝ) / 2 := by
    rw [integral_div]
    have : ∫ ω, (((s * Y ω : ℝ) : ℂ)) ^ 2 ∂P = ((∫ ω, (s ^ 2 * Y ω ^ 2) ∂P : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]; congr 1; ext ω; push_cast; ring
    rw [this, integral_const_mul]; push_cast; ring
  have hint : ∫ ω, ((1 : ℂ) + ((s * Y ω : ℝ) : ℂ) * I - ((s * Y ω : ℝ) : ℂ) ^ 2 / 2) ∂P =
      1 - (s : ℂ) ^ 2 * (∫ ω, Y ω ^ 2 ∂P : ℝ) / 2 := by
    rw [integral_sub (f := fun ω => (1 : ℂ) + ((s * Y ω : ℝ) : ℂ) * I)
      ((integrable_const _).add hlin) hquad,
      integral_add (f := fun _ => (1 : ℂ)) (integrable_const _) hlin, e1, e2]; simp
  rw [← hint, ← integral_sub hexp hpoly]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
    (Filter.Eventually.of_forall fun ω => norm_exp_mul_I_sub_taylor_le _)
  refine Integrable.const_mul ?_ _
  refine Integrable.mono' ((hY2.const_mul (s ^ 2))) ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (by fun_prop : Continuous fun y : ℝ => min (|s * y| ^ 3) ((s * y) ^ 2)
      ).comp_aestronglyMeasurable hm
  · rw [Real.norm_of_nonneg (by positivity)]
    exact (min_le_right _ _).trans (le_of_eq (by ring))

/-- `n (φ(1/√n) - 1) → -σ²/2`. -/
lemma tendsto_mul_integral_exp_sub_one {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    (hmean : ∫ ω, Y ω ∂P = 0) :
    Tendsto (fun n : ℕ => (n : ℂ) *
        (∫ ω, exp ((Y ω / Real.sqrt n : ℝ) * I) ∂P - 1)) atTop
      (𝓝 (-((∫ ω, Y ω ^ 2 ∂P : ℝ) : ℂ) / 2)) := by
  have hY2 : Integrable (fun ω => Y ω ^ 2) P := hY.integrable_sq
  have hm : AEStronglyMeasurable Y P := hY.1
  -- the error term tends to zero (dominated convergence)
  have hdom : Tendsto (fun n : ℕ => ∫ ω, min (|Y ω| ^ 3 / Real.sqrt n) (Y ω ^ 2) ∂P) atTop
      (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (fun ω => Y ω ^ 2)
      (F := fun (n : ℕ) ω => min (|Y ω| ^ 3 / Real.sqrt n) (Y ω ^ 2)) (f := fun _ => 0)
      (fun n => (by fun_prop : Continuous fun y : ℝ => min (|y| ^ 3 / Real.sqrt n) (y ^ 2)
        ).comp_aestronglyMeasurable hm)
      hY2 (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
    · simpa using this
    · have h0 : 0 ≤ min (|Y ω| ^ 3 / Real.sqrt n) (Y ω ^ 2) := by positivity
      rw [Real.norm_of_nonneg h0]; exact min_le_right _ _
    · have hs : Tendsto (fun n : ℕ => |Y ω| ^ 3 / Real.sqrt n) atTop (𝓝 0) := by
        have : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
          Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
        exact this.const_div_atTop _
      exact squeeze_zero (fun n => by positivity) (fun n => min_le_left _ _) hs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ (by simpa using hdom.const_mul 4)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
  have hb := norm_integral_exp_sub_le hY hmean (Real.sqrt n)⁻¹
  simp_rw [← div_eq_inv_mul] at hb
  have heq : (n : ℂ) * (∫ ω, exp ((Y ω / Real.sqrt n : ℝ) * I) ∂P - 1) -
      -((∫ ω, Y ω ^ 2 ∂P : ℝ) : ℂ) / 2 =
      (n : ℂ) * (∫ ω, exp ((Y ω / Real.sqrt n : ℝ) * I) ∂P -
        (1 - (((Real.sqrt n)⁻¹ : ℝ) : ℂ) ^ 2 * (∫ ω, Y ω ^ 2 ∂P : ℝ) / 2)) := by
    have : (n : ℂ) * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) ^ 2 = 1 := by
      rw [← ofReal_natCast, ← ofReal_pow, ← ofReal_mul, inv_pow, hsq, mul_inv_cancel₀ hn'.ne']
      simp
    linear_combination (-((∫ ω, Y ω ^ 2 ∂P : ℝ) : ℂ) / 2) * this
  rw [heq, norm_norm, norm_mul, Complex.norm_natCast]
  calc (n : ℝ) * ‖∫ ω, exp ((Y ω / Real.sqrt n : ℝ) * I) ∂P -
        (1 - (((Real.sqrt n)⁻¹ : ℝ) : ℂ) ^ 2 * (∫ ω, Y ω ^ 2 ∂P : ℝ) / 2)‖
      ≤ n * (4 * ∫ ω, min (|Y ω / Real.sqrt n| ^ 3) ((Y ω / Real.sqrt n) ^ 2) ∂P) := by gcongr
    _ = 4 * ∫ ω, min (|Y ω| ^ 3 / Real.sqrt n) (Y ω ^ 2) ∂P := by
      rw [mul_left_comm, ← integral_const_mul]
      congr 1; congr 1; ext ω
      rw [mul_min_of_nonneg _ _ hn'.le]
      congr 1
      · rw [abs_div, abs_of_pos hspos, div_pow]
        field_simp
        rw [hsq]; ring
      · rw [div_pow, hsq]; field_simp

omit [IsProbabilityMeasure P] in
/-- The characteristic function of an independent sum factorises. -/
lemma integral_exp_sum_eq_pow {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y P)
    (hmeas : ∀ j, Measurable (Y j)) (hident : ∀ j, IdentDistrib (Y j) (Y 0) P P) (n : ℕ)
    (s : ℝ) :
    ∫ ω, exp ((s * ∑ j ∈ range n, Y j ω : ℝ) * I) ∂P =
      (∫ ω, exp ((s * Y 0 ω : ℝ) * I) ∂P) ^ n := by
  have hind' : iIndepFun (fun i : Fin n => Y i) P := hind.precomp Fin.val_injective
  have hprod : ∀ ω, exp ((s * ∑ j ∈ range n, Y j ω : ℝ) * I) =
      ∏ i : Fin n, (fun x : ℝ => exp ((s * x : ℝ) * I)) (Y i ω) := by
    intro ω
    rw [← Complex.exp_sum, Fin.sum_univ_eq_sum_range (fun j => ((s * Y j ω : ℝ) : ℂ) * I),
      ← Finset.sum_mul, Finset.mul_sum]
    push_cast; rfl
  simp_rw [hprod]
  rw [hind'.integral_fun_prod_comp (fun i => (hmeas i).aemeasurable)
    (fun i => (by fun_prop : Continuous fun x : ℝ => exp ((s * x : ℝ) * I)).aestronglyMeasurable)]
  have : ∀ i : Fin n, ∫ ω, exp ((s * Y i ω : ℝ) * I) ∂P = ∫ ω, exp ((s * Y 0 ω : ℝ) * I) ∂P :=
    fun i => ((hident i).comp (u := fun x : ℝ => exp ((s * x : ℝ) * I)) (by fun_prop)).integral_eq
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **One-dimensional CLT, characteristic-function form.** -/
theorem tendsto_integral_exp_sum_div_sqrt {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y P)
    (hmeas : ∀ j, Measurable (Y j)) (hident : ∀ j, IdentDistrib (Y j) (Y 0) P P)
    (hY : MemLp (Y 0) 2 P) (hmean : ∫ ω, Y 0 ω ∂P = 0) :
    Tendsto (fun n : ℕ => ∫ ω, exp (((∑ j ∈ range n, Y j ω) / Real.sqrt n : ℝ) * I) ∂P)
      atTop (𝓝 (exp (-((∫ ω, Y 0 ω ^ 2 ∂P : ℝ) : ℂ) / 2))) := by
  have h := tendsto_one_add_pow_exp_of_tendsto (tendsto_mul_integral_exp_sub_one hY hmean)
  refine h.congr fun n => ?_
  rw [add_sub_cancel]
  have := integral_exp_sum_eq_pow hind hmeas hident n (Real.sqrt n)⁻¹
  simp_rw [div_eq_inv_mul]
  rw [this]

end Sums

end Barycenter

-- ============================================================================
-- Source part: Bary34.lean
-- ============================================================================

open Finset Filter Topology MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace Barycenter

/-! ## Part 34. The multivariate central limit theorem

For i.i.d. square-integrable centred random vectors `X j` in a finite-dimensional real normed
space, `(X₀ + ⋯ + X_{n-1}) / √n` converges in distribution to any random vector `G` which is
centred Gaussian with the same covariance as `X₀`, i.e. such that for every continuous linear
functional `L`, `L(G)` has law `N(0, Var L(X₀))`. -/

section CLT

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `G` is a centred Gaussian vector with the same covariance as `Y`: every continuous linear
functional `L` maps `G` to a real Gaussian `N(0, Var[L ∘ Y])`. -/
def IsGaussianLike {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (G Y : Ω → E) (P : Measure Ω) : Prop :=
  ∀ L : StrongDual ℝ E, P.map (fun ω => L (G ω)) = gaussianReal 0 (variance (fun ω => L (Y ω)) P).toNNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The characteristic-function computation behind the CLT: for every continuous linear
functional `L`, `E exp(i L(S_n/√n)) → exp(-E[L(X₀)²]/2)`. -/
lemma tendsto_integral_exp_dual_clt {X : ℕ → Ω → E} (hind : iIndepFun X P)
    (hmeas : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    (hL2 : MemLp (X 0) 2 P) (hmean : ∫ ω, X 0 ω ∂P = 0) (L : StrongDual ℝ E) :
    Tendsto (fun n : ℕ => ∫ ω, exp ((L ((Real.sqrt n)⁻¹ • ∑ j ∈ range n, X j ω) : ℝ) * I) ∂P)
      atTop (𝓝 (exp (-((∫ ω, L (X 0 ω) ^ 2 ∂P : ℝ) : ℂ) / 2))) := by
  have h := tendsto_integral_exp_sum_div_sqrt (Y := fun j ω => L (X j ω))
    (hind.comp (fun _ => L) (fun _ => L.continuous.measurable))
    (fun j => L.continuous.measurable.comp (hmeas j))
    (fun j => (hident j).comp L.continuous.measurable)
    (L.comp_memLp' hL2) (by rw [L.integral_comp_comm (hL2.integrable one_le_two), hmean, map_zero])
  refine h.congr fun n => ?_
  congr 1; ext ω
  rw [map_smul, map_sum, smul_eq_mul, inv_mul_eq_div]

/-- **Multivariate central limit theorem.** Let `X 0, X 1, …` be independent, identically
distributed, square-integrable random vectors with mean `0` in a finite-dimensional real
normed space `E`, and let `G` be a centred Gaussian vector with the same covariance as `X 0`.
Then `(X 0 + ⋯ + X (n-1)) / √n` converges in distribution to `G`. -/
theorem tendstoInDistribution_clt {X : ℕ → Ω → E} (hind : iIndepFun X P)
    (hmeas : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    (hL2 : MemLp (X 0) 2 P) (hmean : ∫ ω, X 0 ω ∂P = 0) {G : Ω → E} (hGm : AEMeasurable G P)
    (hG : IsGaussianLike G (X 0) P) :
    TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ • ∑ j ∈ range n, X j ω) atTop G P := by
  set d := Module.finrank ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin d) := ContinuousLinearEquiv.ofFinrankEq (by simp [d])
  set Z : ℕ → Ω → E := fun n ω => (Real.sqrt n)⁻¹ • ∑ j ∈ range n, X j ω with hZ
  have hZm : ∀ n, Measurable (Z n) := fun n =>
    (Finset.measurable_sum _ fun j _ => hmeas j).const_smul _
  have key : TendstoInDistribution (fun n => e ∘ Z n) atTop (e ∘ G) P := by
    refine ⟨fun n => (e.continuous.measurable.comp (hZm n)).aemeasurable,
      e.continuous.measurable.comp_aemeasurable hGm, ?_⟩
    refine tendsto_of_tendsto_charFun fun t => ?_
    set L : StrongDual ℝ E := (innerSL ℝ t).comp (e : E →L[ℝ] EuclideanSpace ℝ (Fin d)) with hLdef
    have hL : ∀ x, ⟪e x, t⟫ = L x := fun x => by simp [hLdef, real_inner_comm]
    have h1 : ∀ n, charFun (P.map (e ∘ Z n)) t = ∫ ω, exp ((L (Z n ω) : ℝ) * I) ∂P := by
      intro n
      rw [charFun_apply, integral_map (e.continuous.measurable.comp (hZm n)).aemeasurable
        (by fun_prop)]
      simp [hL]
    have h2 : charFun (P.map (e ∘ G)) t = exp (-((∫ ω, L (X 0 ω) ^ 2 ∂P : ℝ) : ℂ) / 2) := by
      have : charFun (P.map (e ∘ G)) t = charFun (P.map (fun ω => L (G ω))) 1 := by
        rw [charFun_apply, charFun_apply, integral_map (e.continuous.measurable.comp_aemeasurable hGm)
          (by fun_prop), integral_map (φ := fun ω => L (G ω))
          (L.continuous.measurable.comp_aemeasurable hGm) (by fun_prop)]
        simp [hL]
      have hmeanL : ∫ ω, L (X 0 ω) ∂P = 0 := by
        rw [L.integral_comp_comm (hL2.integrable one_le_two), hmean, map_zero]
      rw [this, hG L, charFun_gaussianReal,
        variance_of_integral_eq_zero (X := fun ω => L (X 0 ω)) (L.continuous.measurable.comp (hmeas 0)).aemeasurable hmeanL,
        Real.coe_toNNReal _ (integral_nonneg fun _ => sq_nonneg _)]
      congr 1; push_cast; ring
    show Tendsto (fun n => charFun (P.map (e ∘ Z n)) t) atTop (𝓝 (charFun (P.map (e ∘ G)) t))
    rw [h2]; simp_rw [h1]
    exact tendsto_integral_exp_dual_clt hind hmeas hident hL2 hmean L
  have := key.continuous_comp e.symm.continuous
  simpa [Function.comp_def] using this

/-- **Central limit theorem (real-valued case).** Let `X 0, X 1, …` be independent, identically
distributed, square-integrable real random variables with mean `0`, and let `Z` have law
`N(0, Var[X 0])`. Then `(X 0 + ⋯ + X (n-1)) / √n` converges in distribution to `Z`. -/
theorem tendstoInDistribution_clt_real {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hmeas : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) P P)
    (hL2 : MemLp (X 0) 2 P) (hmean : ∫ ω, X 0 ω ∂P = 0) {Z : Ω → ℝ} (hZm : AEMeasurable Z P)
    (hZ : P.map Z = gaussianReal 0 (variance (X 0) P).toNNReal) :
    TendstoInDistribution (fun (n : ℕ) ω => (∑ j ∈ range n, X j ω) / Real.sqrt n) atTop Z P := by
  have hG : IsGaussianLike Z (X 0) P := by
    intro L
    have hL : ∀ x : ℝ, L x = L 1 * x := fun x => by
      rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    have h1 : (fun ω => L (Z ω)) = fun ω => L 1 * Z ω := funext fun ω => hL _
    have h2 : (fun ω => L (X 0 ω)) = fun ω => L 1 * X 0 ω := funext fun ω => hL _
    have h3 : P.map (fun ω => L 1 * Z ω) = (P.map Z).map (fun x => L 1 * x) :=
      (AEMeasurable.map_map_of_aemeasurable (measurable_const_mul _).aemeasurable hZm).symm
    rw [h1, h2, variance_const_mul, h3, hZ,
      gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ (variance_nonneg _ _),
      Real.coe_toNNReal _ (mul_nonneg (sq_nonneg _) (variance_nonneg _ _))]
  have h := tendstoInDistribution_clt hind hmeas hident hL2 hmean hZm hG
  convert h using 3 with n ω
  rw [smul_eq_mul, div_eq_inv_mul]

end CLT

end Barycenter

-- ============================================================================
-- Source part: Bary35.lean
-- ============================================================================

open Finset Filter Topology MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace ComplexConjugate

namespace Barycenter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Part 35. The central limit theorem for the darts, and Theorem 6.1 / Proposition 6.2
without a CLT hypothesis

Using the multivariate central limit theorem of Part 34, we prove that the normalised
centre `√m S_m` of a rotationally invariant sample converges in distribution to a proper complex
Gaussian of variance `μ₁`, and derive Theorem 6.1, (6.1) and (6.3), and the joint limit law of
Proposition 6.2, with the CLT now proved rather than assumed. -/

omit [IsProbabilityMeasure P] in
/-- The characteristic function of a proper complex Gaussian of variance `v`:
`E exp(i⟪G, t⟫) = exp(-v|t|²/4)`. -/
theorem IsProperComplexGaussian.integral_exp_inner {G : Ω → ℂ} {v : ℝ} (hv : 0 < v)
    (hG : IsProperComplexGaussian G v P) (t : ℂ) :
    ∫ ω, exp ((⟪G ω, t⟫ : ℝ) * I) ∂P = exp (-((v * ‖t‖ ^ 2 / 4 : ℝ) : ℂ)) := by
  have hmeasd : Measurable (fun z : ℂ => ENNReal.ofReal (cgaussDensity v z)) := by
    unfold cgaussDensity; fun_prop
  have hdens_nn : ∀ z, 0 ≤ cgaussDensity v z := fun z => by
    unfold cgaussDensity; have := Real.pi_pos; positivity
  rw [← integral_map (φ := G) (f := fun z : ℂ => exp ((⟪z, t⟫ : ℝ) * I)) hG.aemeasurable
    (by fun_prop), hG.law, integral_withDensity_eq_integral_toReal_smul hmeasd
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hdens_nn _), cgaussDensity]
  have hpt : ∀ z : ℂ, ((Real.pi * v)⁻¹ * Real.exp (-‖z‖ ^ 2 / v)) • exp ((⟪z, t⟫ : ℝ) * I) =
      ((Real.pi * v : ℝ) : ℂ)⁻¹ * exp (-((1 / v : ℝ) : ℂ) * ‖z‖ ^ 2 + I * ⟪t, z⟫) := by
    intro z
    rw [Complex.real_smul, ofReal_mul, ofReal_exp, mul_assoc, ← Complex.exp_add, real_inner_comm]
    push_cast
    congr 2
    ring
  simp_rw [hpt]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simp; positivity),
    Complex.finrank_real_complex]
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  norm_num
  have e : -((‖t‖ : ℝ) : ℂ) ^ 2 / (4 * (v : ℂ)⁻¹) = -((v : ℂ) * ((‖t‖ : ℝ) : ℂ) ^ 2 / 4) := by
    field_simp
  rw [e]
  field_simp

omit [MeasurableSpace Ω] in
/-- `√m · m⁻¹ = (√m)⁻¹` (both sides vanish for `m = 0`). -/
lemma sqrt_mul_inv_natCast (m : ℕ) :
    (Real.sqrt m : ℂ) * (m : ℂ)⁻¹ = (((Real.sqrt m)⁻¹ : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hs : (Real.sqrt m : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hm').ne'
    have hmc : ((m : ℝ) : ℂ) = (Real.sqrt m : ℂ) ^ 2 := by
      rw [← ofReal_pow, Real.sq_sqrt hm'.le]
    rw [ofReal_inv, ← ofReal_natCast, hmc]
    field_simp

namespace RadialSample

variable {X : ℕ → Ω → ℂ}

omit [IsProbabilityMeasure P] in
lemma memLp_two (hX : RadialSample X P) (j : ℕ) : MemLp (X j) 2 P := by
  simpa using hX.mom j 2

omit [IsProbabilityMeasure P] in
lemma integral_eq_zero (hX : RadialSample X P) (j : ℕ) : ∫ ω, X j ω ∂P = 0 := by
  simpa using hX.integral_pow_eq_zero j (p := 1) le_rfl

/-- Second moments of a real linear functional of a rotationally invariant dart:
`E⟪w, X⟫² = |w|² μ₁ / 2`. -/
lemma integral_inner_sq (hX : RadialSample X P) (w : ℂ) :
    ∫ ω, ⟪w, X 0 ω⟫ ^ 2 ∂P = ‖w‖ ^ 2 * radMom (X 0) P 1 / 2 := by
  have hpt : ∀ z : ℂ, (((⟪w, z⟫ ^ 2 : ℝ)) : ℂ) =
      (conj w) ^ 2 / 4 * (z ^ 2 * conj z ^ 0) + w ^ 2 / 4 * (z ^ 0 * conj z ^ 2) +
        ((‖w‖ ^ 2 / 2 : ℝ) : ℂ) * (z ^ 1 * conj z ^ 1) := by
    intro z
    have h1 : ((⟪w, z⟫ : ℝ) : ℂ) = (conj w * z + w * conj z) / 2 := by
      rw [Complex.inner, Complex.re_eq_add_conj]; simp [mul_comm]
    have h2 : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * conj w := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rw [h1]
    push_cast at h2
    rw [h2]
    ring
  have e : ∀ p q, ∫ ω, X 0 ω ^ p * conj (X 0 ω) ^ q ∂P =
      if p = q then (radMom (X 0) P p : ℂ) else 0 := fun p q => (hX.rot 0).cmom_eq p q
  have hi := (hX.mom 0).integrable_pow_mul_conj_pow
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hpt]
  rw [integral_add (f := fun ω => conj w ^ 2 / 4 * (X 0 ω ^ 2 * conj (X 0 ω) ^ 0) +
      w ^ 2 / 4 * (X 0 ω ^ 0 * conj (X 0 ω) ^ 2))
      (((hi 2 0).const_mul _).add ((hi 0 2).const_mul _)) ((hi 1 1).const_mul _),
    integral_add ((hi 2 0).const_mul _) ((hi 0 2).const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, e, e, e]
  simp
  ring

/-- A proper complex Gaussian of variance `μ₁` has the covariance of the darts. -/
lemma isGaussianLike (hX : RadialSample X P) (hμ : 0 < radMom (X 0) P 1) {G : Ω → ℂ}
    (hG : IsProperComplexGaussian G (radMom (X 0) P 1) P) : IsGaussianLike G (X 0) P := by
  intro L
  set w : ℂ := (InnerProductSpace.toDual ℝ ℂ).symm L with hw
  have hLw : ∀ z, L z = ⟪w, z⟫ := fun z => by rw [hw, InnerProductSpace.toDual_symm_apply]
  have hmeanL : ∫ ω, L (X 0 ω) ∂P = 0 := by
    rw [L.integral_comp_comm ((hX.memLp_two 0).integrable one_le_two), hX.integral_eq_zero,
      map_zero]
  have hvar : ∫ ω, L (X 0 ω) ^ 2 ∂P = ‖w‖ ^ 2 * radMom (X 0) P 1 / 2 := by
    simp_rw [hLw]; exact hX.integral_inner_sq w
  rw [variance_of_integral_eq_zero (X := fun ω => L (X 0 ω))
    (L.continuous.measurable.comp (hX.meas 0)).aemeasurable hmeanL, hvar]
  haveI : IsProbabilityMeasure (P.map fun ω => L (G ω)) :=
    Measure.isProbabilityMeasure_map (L.continuous.measurable.comp_aemeasurable hG.aemeasurable)
  refine Measure.ext_of_charFun (funext fun s => ?_)
  rw [charFun_gaussianReal, charFun_apply, integral_map (φ := fun ω => L (G ω))
    (L.continuous.measurable.comp_aemeasurable hG.aemeasurable) (by fun_prop)]
  have hin : ∀ ω, ⟪L (G ω), s⟫ = ⟪G ω, s • w⟫ := by
    intro ω
    rw [hLw, inner_smul_right, real_inner_comm (G ω)]
    simp [mul_comm]
  simp_rw [hin]
  rw [hG.integral_exp_inner hμ (s • w), Real.coe_toNNReal _ (by positivity)]
  congr 1
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  push_cast
  ring

/-- **The central limit theorem for the darts.** If the darts are rotationally invariant with
`μ₁ > 0` and `G` is a proper complex Gaussian of variance `μ₁`, then `√m S_m → G` in
distribution. -/
theorem tendstoInDistribution_sqrt_mul_Scen (hX : RadialSample X P)
    (hμ : 0 < radMom (X 0) P 1) {G : Ω → ℂ}
    (hG : IsProperComplexGaussian G (radMom (X 0) P 1) P) :
    TendstoInDistribution (fun (m : ℕ) ω => (Real.sqrt m : ℂ) * Scen X m ω) atTop G P := by
  have h := tendstoInDistribution_clt (E := ℂ) hX.indep hX.meas (fun j => hX.ident j 0)
    (hX.memLp_two 0) (hX.integral_eq_zero 0) hG.aemeasurable (hX.isGaussianLike hμ hG)
  have heq : (fun (m : ℕ) ω => (Real.sqrt m : ℂ) * Scen X m ω) =
      fun (m : ℕ) ω => (Real.sqrt m)⁻¹ • ∑ j ∈ range m, X j ω := by
    funext m ω
    rw [Scen, Complex.real_smul, ← mul_assoc, sqrt_mul_inv_natCast]
  rw [heq]
  exact h

variable {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

/-- **Theorem 6.1, (6.1)** (central limit theorem now proved). If `μ₁ > 0` and `G` is a proper
complex Gaussian of variance `μ₁`, then `m^{d/2} (B_m(f) - f(a)) → c_d G^d` in distribution. -/
theorem tendstoInDistribution_Bimg_clt (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {d : ℕ} (hd : 1 ≤ d)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) (hμ : 0 < radMom (X 0) P 1) {G : Ω → ℂ}
    (hG : IsProperComplexGaussian G (radMom (X 0) P 1) P) :
    TendstoInDistribution (fun (m : ℕ) ω => (Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a))
      atTop (fun ω => c d * G ω ^ d) P :=
  hX.tendstoInDistribution_Bimg hf hs hd hlow (hX.tendstoInDistribution_sqrt_mul_Scen hμ hG)

/-- **Theorem 6.1, (6.3)** (central limit theorem now proved), with the limit written through
a proper complex Gaussian `G` of variance `μ₁`: `m^{d/2} E|B_m(f) - f(a)| → |c_d| E|G|^d`. -/
theorem tendsto_scaled_abs_clt (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {d : ℕ} (hd : 1 ≤ d)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) (hμ : 0 < radMom (X 0) P 1) {G : Ω → ℂ}
    (hG : IsProperComplexGaussian G (radMom (X 0) P 1) P) :
    Tendsto (fun m : ℕ => Real.sqrt m ^ d * ∫ ω, ‖Bimg f a X m ω - f a‖ ∂P) atTop
      (𝓝 (‖c d‖ * ∫ ω, ‖G ω‖ ^ d ∂P)) :=
  hX.tendsto_scaled_abs hf hs hd hlow (hX.tendstoInDistribution_sqrt_mul_Scen hμ hG)

/-- The two-dimensional central limit theorem for the pairs `(X_j, f(a + X_j) - f(a))`:
if `(G, H)` is a centred Gaussian vector with the covariance of `(X₀, f(a + X₀) - f(a))`, then
`√m (S_m, A_m(f) - f(a)) → (G, H)` in distribution. -/
theorem tendstoInDistribution_pair_clt (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {G H : Ω → ℂ}
    (hGHm : AEMeasurable (fun ω => (G ω, H ω)) P)
    (hGH : IsGaussianLike (fun ω => (G ω, H ω)) (fun ω => (X 0 ω, f (a + X 0 ω) - f a)) P) :
    TendstoInDistribution (fun (m : ℕ) ω => ((Real.sqrt m : ℂ) * Scen X m ω,
      (Real.sqrt m : ℂ) * (Aimg f a X m ω - f a))) atTop (fun ω => (G ω, H ω)) P := by
  have hcont : Continuous (fun z => f (a + z)) := continuous_of_hasSum hf
  set g : ℂ → ℂ × ℂ := fun z => (z, f (a + z) - f a) with hg
  have hgm : Measurable g := (continuous_id.prodMk (hcont.sub continuous_const)).measurable
  have hY1 : MemLp (fun ω => f (a + X 0 ω) - f a) 2 P := hX.memLp_comp_X hf hs 0
  have hL2 : MemLp (fun ω => g (X 0 ω)) 2 P := memLp_prod_iff.2 ⟨hX.memLp_two 0, hY1⟩
  have hmean : ∫ ω, g (X 0 ω) ∂P = 0 := by
    have h1 : ∫ ω, f (a + X 0 ω) ∂P = f a := by
      have := hX.integral_Aimg le_rfl hf hs
      simpa [Aimg_one] using this
    have hint : Integrable (fun ω => f (a + X 0 ω)) P := by
      refine ((hY1.integrable one_le_two).add (integrable_const (f a))).congr
        (Eventually.of_forall fun ω => ?_)
      simp
    rw [hg, integral_pair ((hX.memLp_two 0).integrable one_le_two) (hY1.integrable one_le_two),
      hX.integral_eq_zero 0, integral_sub hint (integrable_const _), h1]
    simp
  have h := tendstoInDistribution_clt (E := ℂ × ℂ) (X := fun j ω => g (X j ω))
    (hX.indep.comp (fun _ => g) (fun _ => hgm)) (fun j => hgm.comp (hX.meas j))
    (fun j => (hX.ident j 0).comp hgm) hL2 hmean hGHm hGH
  have heq : (fun (m : ℕ) ω => ((Real.sqrt m : ℂ) * Scen X m ω,
      (Real.sqrt m : ℂ) * (Aimg f a X m ω - f a))) =
      fun (m : ℕ) ω => (Real.sqrt m)⁻¹ • ∑ j ∈ range m, g (X j ω) := by
    funext m ω
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [Scen, Aimg]
    · rw [Aimg_sub hm, Scen, ← mul_assoc, ← mul_assoc, sqrt_mul_inv_natCast]
      ext <;> simp [hg, Prod.smul_fst, Prod.smul_snd, Prod.fst_sum, Prod.snd_sum,
        Complex.real_smul]
  rw [heq]
  exact h

/-- **Proposition 6.2 (joint fluctuations)** (central limit theorem now proved). If `(G, H)` is
a centred Gaussian vector with the covariance of `(X₀, f(a + X₀) - f(a))`, then
`(√m (A_m(f) - f(a)), m^{d/2} (B_m(f) - f(a))) → (H, c_d G^d)` in distribution. -/
theorem tendstoInDistribution_joint_clt (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {d : ℕ} (hd : 1 ≤ d)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) {G H : Ω → ℂ}
    (hGHm : AEMeasurable (fun ω => (G ω, H ω)) P)
    (hGH : IsGaussianLike (fun ω => (G ω, H ω)) (fun ω => (X 0 ω, f (a + X 0 ω) - f a)) P) :
    TendstoInDistribution (fun (m : ℕ) ω => ((Real.sqrt m : ℂ) * (Aimg f a X m ω - f a),
      (Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a))) atTop
      (fun ω => (H ω, c d * G ω ^ d)) P :=
  hX.tendstoInDistribution_joint hf hs hd hlow (hX.tendstoInDistribution_pair_clt hf hs hGHm hGH)

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary36.lean
-- ============================================================================

open Finset Filter Topology MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace ComplexConjugate

namespace Barycenter

/-! ## Part 36. Theorem 6.1 with no auxiliary Gaussian variable

Convergence in distribution only concerns laws, so the limit in Theorem 6.1 can be described by
an explicit measure on `ℂ`: the proper complex Gaussian law `cgaussLaw μ₁`. To apply the results
of Part 35 we enlarge the probability space to `Ω × ℂ`, where a Gaussian variable is available. -/

/-- The proper complex Gaussian law of variance `v`, with density `(π v)⁻¹ e^{-|z|²/v}`. -/
noncomputable def cgaussLaw (v : ℝ) : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (cgaussDensity v z))

lemma isProbabilityMeasure_cgaussLaw {v : ℝ} (hv : 0 < v) : IsProbabilityMeasure (cgaussLaw v) := by
  constructor
  have hexp : ∀ z : ℂ, Real.exp (-‖z‖ ^ 2 / v) = Real.exp (-(1 / v) * ‖z‖ ^ 2) := fun z => by
    congr 1; ring
  have hint : Integrable (fun z : ℂ => cgaussDensity v z) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ)
      (b := ((1 / v : ℝ) : ℂ)) (by simp; positivity) 0 0).norm
    refine (h.const_mul (Real.pi * v)⁻¹).congr (Eventually.of_forall fun z => ?_)
    simp only [cgaussDensity, hexp, zero_mul, add_zero, Complex.norm_exp]
    congr 2
    simp [← ofReal_pow]
  have hnn : ∀ z, 0 ≤ cgaussDensity v z := fun z => by
    unfold cgaussDensity; have := Real.pi_pos; positivity
  rw [cgaussLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn), ENNReal.ofReal_eq_one]
  simp only [cgaussDensity, hexp]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity),
    Complex.finrank_real_complex]
  norm_num
  field_simp

section Lift

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {β : Type*} [MeasurableSpace β] {ν : Measure β} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure P] in
lemma identDistrib_comp_fst {γ : Type*} [MeasurableSpace γ] {f g : Ω → γ} (hf : Measurable f)
    (hg : Measurable g) (h : IdentDistrib f g P P) :
    IdentDistrib (fun p : Ω × β => f p.1) (fun p : Ω × β => g p.1) (P.prod ν) (P.prod ν) := by
  refine ⟨(hf.comp measurable_fst).aemeasurable, (hg.comp measurable_fst).aemeasurable, ?_⟩
  have h1 : (P.prod ν).map (fun p : Ω × β => f p.1) = P.map f := by
    change (P.prod ν).map (f ∘ Prod.fst) = _
    rw [← Measure.map_map hf measurable_fst, (measurePreserving_fst (μ := P) (ν := ν)).map_eq]
  have h2 : (P.prod ν).map (fun p : Ω × β => g p.1) = P.map g := by
    change (P.prod ν).map (g ∘ Prod.fst) = _
    rw [← Measure.map_map hg measurable_fst, (measurePreserving_fst (μ := P) (ν := ν)).map_eq]
  rw [h1, h2, h.map_eq]

omit [IsProbabilityMeasure P] in
lemma RadialSample.comp_fst {X : ℕ → Ω → ℂ} (hX : RadialSample X P) :
    RadialSample (fun j (p : Ω × β) => X j p.1) (P.prod ν) := by
  have hmp : MeasurePreserving (Prod.fst : Ω × β → Ω) (P.prod ν) P := measurePreserving_fst
  refine ⟨fun j => (hX.meas j).comp measurable_fst, ?_,
    fun i j => identDistrib_comp_fst (hX.meas i) (hX.meas j) (hX.ident i j),
    fun j θ => identDistrib_comp_fst (measurable_const.mul (hX.meas j)) (hX.meas j) (hX.rot j θ),
    fun j p => (hX.mom j p).comp_measurePreserving hmp⟩
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  have hind := (iIndepFun_iff_measure_inter_preimage_eq_mul.1 hX.indep) S hsets
  have hinter : (⋂ i ∈ S, (fun p : Ω × β => X i p.1) ⁻¹' sets i) =
      Prod.fst ⁻¹' (⋂ i ∈ S, X i ⁻¹' sets i) := by
    ext; simp
  rw [hinter, hmp.measure_preimage (Finset.measurableSet_biInter S fun i hi =>
    (hX.meas i) (hsets i hi)).nullMeasurableSet, hind]
  refine Finset.prod_congr rfl fun i hi => ?_
  exact (hmp.measure_preimage ((hX.meas i) (hsets i hi)).nullMeasurableSet).symm

lemma radMom_comp_fst (Y : Ω → ℂ) :
    radMom (fun p : Ω × β => Y p.1) (P.prod ν) = radMom Y P := by
  funext n
  rw [radMom, radMom, integral_fun_fst (f := fun ω => ‖Y ω‖ ^ (2 * n))]
  simp

end Lift

namespace RadialSample

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℂ} {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

/-- **Theorem 6.1, (6.1)** (central limit theorem proved, no auxiliary variable). The laws of
`m^{d/2} (B_m(f) - f(a))` converge weakly to the law of `c_d G^d`, where `G` has the proper
complex Gaussian law of variance `μ₁`. -/
theorem tendsto_law_Bimg (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {d : ℕ} (hd : 1 ≤ d)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) (hμ : 0 < radMom (X 0) P 1) :
    haveI := isProbabilityMeasure_cgaussLaw hμ
    Tendsto (β := ProbabilityMeasure ℂ) (fun m : ℕ => (⟨P.map (fun ω => (Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a)),
        Measure.isProbabilityMeasure_map ((continuous_of_hasSum hf).measurable.comp
          (hX.measurable_Scen m) |>.sub_const _ |>.const_mul _).aemeasurable⟩ :
          ProbabilityMeasure ℂ)) atTop
      (𝓝 (⟨(cgaussLaw (radMom (X 0) P 1)).map (fun z => c d * z ^ d),
        Measure.isProbabilityMeasure_map (by fun_prop)⟩ : ProbabilityMeasure ℂ)) := by
  haveI := isProbabilityMeasure_cgaussLaw hμ
  set γ := cgaussLaw (radMom (X 0) P 1) with hγ
  set X' : ℕ → Ω × ℂ → ℂ := fun j p => X j p.1 with hX'def
  have hX' : RadialSample X' (P.prod γ) := hX.comp_fst
  have hrad : radMom (X' 0) (P.prod γ) = radMom (X 0) P := radMom_comp_fst (X 0)
  have hG : IsProperComplexGaussian (Prod.snd : Ω × ℂ → ℂ) (radMom (X' 0) (P.prod γ) 1)
      (P.prod γ) := ⟨measurable_snd.aemeasurable, by
        rw [hrad, (measurePreserving_snd (μ := P) (ν := γ)).map_eq]; rfl⟩
  have h := (hX'.tendstoInDistribution_Bimg_clt hf (by rw [hrad]; exact hs) hd hlow
    (by rw [hrad]; exact hμ) hG).tendsto
  have hYm : ∀ m : ℕ, Measurable (fun ω => (Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a)) :=
    fun m => ((continuous_of_hasSum hf).measurable.comp (hX.measurable_Scen m)
      |>.sub_const _ |>.const_mul _)
  have e1 : ∀ m : ℕ, (P.prod γ).map (fun p => (Real.sqrt m : ℂ) ^ d * (Bimg f a X' m p - f a)) =
      P.map (fun ω => (Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a)) := by
    intro m
    change (P.prod γ).map ((fun ω => (Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a)) ∘
      Prod.fst) = _
    rw [← Measure.map_map (hYm m) measurable_fst, (measurePreserving_fst (μ := P) (ν := γ)).map_eq]
  have e2 : (P.prod γ).map (fun p : Ω × ℂ => c d * p.2 ^ d) = γ.map (fun z => c d * z ^ d) := by
    change (P.prod γ).map ((fun z => c d * z ^ d) ∘ Prod.snd) = _
    rw [← Measure.map_map (by fun_prop) measurable_snd,
      (measurePreserving_snd (μ := P) (ν := γ)).map_eq]
  convert h using 2 with m
  · exact Subtype.ext (e1 m).symm
  · exact Subtype.ext e2.symm

/-- **Theorem 6.1, (6.3)** in the paper's closed form (central limit theorem proved, no
auxiliary variable): `m^{d/2} E|B_m(f) - f(a)| → |c_d| μ₁^{d/2} Γ(1 + d/2)`. -/
theorem tendsto_scaled_abs_gamma_clt (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {d : ℕ} (hd : 1 ≤ d)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) (hμ : 0 < radMom (X 0) P 1) :
    Tendsto (fun m : ℕ => Real.sqrt m ^ d * ∫ ω, ‖Bimg f a X m ω - f a‖ ∂P) atTop
      (𝓝 (‖c d‖ * radMom (X 0) P 1 ^ ((d : ℝ) / 2) * Real.Gamma (1 + (d : ℝ) / 2))) := by
  haveI := isProbabilityMeasure_cgaussLaw hμ
  set γ := cgaussLaw (radMom (X 0) P 1) with hγ
  set X' : ℕ → Ω × ℂ → ℂ := fun j p => X j p.1 with hX'def
  have hX' : RadialSample X' (P.prod γ) := hX.comp_fst
  have hrad : radMom (X' 0) (P.prod γ) = radMom (X 0) P := radMom_comp_fst (X 0)
  have hG : IsProperComplexGaussian (Prod.snd : Ω × ℂ → ℂ) (radMom (X' 0) (P.prod γ) 1)
      (P.prod γ) := ⟨measurable_snd.aemeasurable, by
        rw [hrad, (measurePreserving_snd (μ := P) (ν := γ)).map_eq]; rfl⟩
  have hμ' : 0 < radMom (X' 0) (P.prod γ) 1 := by rw [hrad]; exact hμ
  have h := hX'.tendsto_scaled_abs_gamma hf (by rw [hrad]; exact hs) hd hlow hμ' hG
    (hX'.tendstoInDistribution_sqrt_mul_Scen hμ' hG)
  rw [hrad] at h
  refine h.congr fun m => ?_
  congr 1
  exact (integral_fun_fst (μ := P) (ν := γ) (f := fun ω => ‖Bimg f a X m ω - f a‖)).trans
    (by simp)

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary37.lean
-- ============================================================================

open Finset Filter Topology MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace ComplexConjugate

namespace Barycenter

/-! ## Part 37. Proposition 6.2: the Gaussian remainder `R`

In the joint limit `(H, c_d G^d)` of Proposition 6.2, write `H = c₁ G + R`. We prove the paper's
description of `R`: it is a proper complex Gaussian of variance `V_f - |c₁|² μ₁`, independent
of `G`. Consequently the limit has the form `(c₁ G + R, c_d G^d)` stated in the paper, and for
`d = 1`, `√m (A_m(f) - B_m(f)) → R`. -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The characteristic functional of a centred Gaussian vector with the covariance of `Y`. -/
lemma IsGaussianLike.integral_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {G Y : Ω → E} (hG : IsGaussianLike G Y P)
    (hGm : AEMeasurable G P) (hYm : AEMeasurable Y P) (L : StrongDual ℝ E)
    (hmean : ∫ ω, L (Y ω) ∂P = 0) :
    ∫ ω, exp ((L (G ω) : ℝ) * I) ∂P = exp (-((∫ ω, L (Y ω) ^ 2 ∂P : ℝ) : ℂ) / 2) := by
  have h1 : ∫ ω, exp ((L (G ω) : ℝ) * I) ∂P = charFun (P.map (fun ω => L (G ω))) 1 := by
    rw [charFun_apply, integral_map (φ := fun ω => L (G ω))
      (L.continuous.measurable.comp_aemeasurable hGm) (by fun_prop)]
    simp
  rw [h1, hG L, charFun_gaussianReal,
    variance_of_integral_eq_zero (X := fun ω => L (Y ω))
      (L.continuous.measurable.comp_aemeasurable hYm) hmean,
    Real.coe_toNNReal _ (integral_nonneg fun _ => sq_nonneg _)]
  congr 1; push_cast; ring

omit [IsProbabilityMeasure P] in
/-- `E[⟪u, U⟫ ⟪w, V⟫] = Re(ū w̄ E[UV] + ū w E[U V̄]) / 2` for square-integrable complex `U, V`. -/
lemma integral_inner_mul_inner {U V : Ω → ℂ} (hU : MemLp U 2 P) (hV : MemLp V 2 P) (u w : ℂ) :
    ∫ ω, ⟪u, U ω⟫ * ⟪w, V ω⟫ ∂P =
      (conj u * conj w * ∫ ω, U ω * V ω ∂P + conj u * w * ∫ ω, U ω * conj (V ω) ∂P).re / 2 := by
  have hpt : ∀ x y : ℂ, ⟪u, x⟫ * ⟪w, y⟫ =
      (conj u * conj w * (x * y) + conj u * w * (x * conj y)).re / 2 := by
    intro x y
    simp only [Complex.inner, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im]
    ring
  simp_rw [hpt]
  have i1 : Integrable (fun ω => U ω * V ω) P := hU.integrable_mul hV (p := 2) (q := 2)
  have i2 : Integrable (fun ω => U ω * conj (V ω)) P :=
    hU.integrable_mul hV.star (p := 2) (q := 2)
  have i3 : Integrable (fun ω => conj u * conj w * (U ω * V ω) +
      conj u * w * (U ω * conj (V ω))) P := (i1.const_mul _).add (i2.const_mul _)
  rw [integral_div]
  congr 1
  have h := integral_re i3
  simp only [RCLike.re_to_complex] at h
  rw [h, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]

namespace RadialSample

variable {X : ℕ → Ω → ℂ} {f : ℂ → ℂ} {a : ℂ} {c : ℕ → ℂ}

/-- Second-order moments of `g(X) = f(a + X) - f(a)` against `X`. -/
lemma integral_g_mul_conj (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    ∫ ω, (f (a + X 0 ω) - f a) * conj (X 0 ω) ∂P = c 1 * radMom (X 0) P 1 := by
  have hν := radMom_nonneg (X := X) (P := P) 0
  have hW := hX.orthoMoments_X 0
  obtain ⟨hmg, hcg⟩ := hW.memLp_and_tendsto hν (hasSum_g hf) (summable_gcoef hν hs)
  have hX2 : MemLp (X 0) 2 P := hX.memLp_two 0
  have h := tendsto_integral_mul_conj hmg hX2 (fun N => hW.memLp_psum (gcoef c) (range N))
    (fun _ => hX2) hcg (by simp)
  have ho : ∀ n, ∫ ω, X 0 ω ^ n * conj (X 0 ω) ^ 1 ∂P =
      if n = 1 then (radMom (X 0) P n : ℂ) else 0 := fun n => (hX.rot 0).cmom_eq n 1
  have hN : ∀ N, 2 ≤ N → ∫ ω, psum (gcoef c) N (X 0 ω) * conj (X 0 ω) ∂P =
      c 1 * radMom (X 0) P 1 := by
    intro N hN
    have e : ∀ ω, psum (gcoef c) N (X 0 ω) * conj (X 0 ω) =
        ∑ n ∈ range N, gcoef c n * (X 0 ω ^ n * conj (X 0 ω) ^ 1) := by
      intro ω; simp [psum, Finset.sum_mul, mul_assoc]
    simp_rw [e]
    rw [integral_finset_sum _ fun n _ => ((hX.mom 0).integrable_pow_mul_conj_pow n 1).const_mul _]
    simp_rw [integral_const_mul, ho, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' (range N) 1, if_pos (Finset.mem_range.2 (by omega)), gcoef_succ c 0]
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr'
    (eventually_atTop.2 ⟨2, fun N hN' => (hN N hN').symm⟩))

lemma integral_g_mul (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    ∫ ω, (f (a + X 0 ω) - f a) * X 0 ω ∂P = 0 := by
  have hν := radMom_nonneg (X := X) (P := P) 0
  have hW := hX.orthoMoments_X 0
  obtain ⟨hmg, hcg⟩ := hW.memLp_and_tendsto hν (hasSum_g hf) (summable_gcoef hν hs)
  have hX2 : MemLp (fun ω => conj (X 0 ω)) 2 P := (hX.memLp_two 0).star
  have h := tendsto_integral_mul_conj hmg hX2 (fun N => hW.memLp_psum (gcoef c) (range N))
    (fun _ => hX2) hcg (by simp)
  simp only [Complex.conj_conj] at h
  have ho : ∀ n, ∫ ω, X 0 ω ^ (n + 1) * conj (X 0 ω) ^ 0 ∂P = 0 := fun n => by
    have := (hX.rot 0).cmom_eq (n + 1) 0
    rw [if_neg (by omega)] at this
    exact this
  have hN : ∀ N, ∫ ω, psum (gcoef c) N (X 0 ω) * X 0 ω ∂P = 0 := by
    intro N
    have e : ∀ ω, psum (gcoef c) N (X 0 ω) * X 0 ω =
        ∑ n ∈ range N, gcoef c n * (X 0 ω ^ (n + 1) * conj (X 0 ω) ^ 0) := by
      intro ω; simp [psum, Finset.sum_mul, mul_assoc, pow_succ]
    simp_rw [e]
    rw [integral_finset_sum _ fun n _ =>
      ((hX.mom 0).integrable_pow_mul_conj_pow (n + 1) 0).const_mul _]
    simp_rw [integral_const_mul, ho, mul_zero, Finset.sum_const_zero]
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr' (Eventually.of_forall fun N => (hN N).symm))

lemma integral_g_sq (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) :
    ∫ ω, (f (a + X 0 ω) - f a) * (f (a + X 0 ω) - f a) ∂P = 0 := by
  have hν := radMom_nonneg (X := X) (P := P) 0
  have hW := hX.orthoMoments_X 0
  obtain ⟨hmg, hcg⟩ := hW.memLp_and_tendsto hν (hasSum_g hf) (summable_gcoef hν hs)
  have hcg' : Tendsto (fun N => ∫ ω, ‖conj (f (a + X 0 ω) - f a) -
      conj (psum (gcoef c) N (X 0 ω))‖ ^ 2 ∂P) atTop (𝓝 0) := by
    simpa only [← map_sub, Complex.norm_conj] using hcg
  have hmgc : MemLp (fun ω => conj (f (a + X 0 ω) - f a)) 2 P := hmg.star
  have hpc : ∀ N, MemLp (fun ω => conj (psum (gcoef c) N (X 0 ω))) 2 P := fun N =>
    (hW.memLp_psum (gcoef c) (range N)).star
  have h := tendsto_integral_mul_conj hmg hmgc
    (fun N => hW.memLp_psum (gcoef c) (range N)) hpc hcg hcg'
  simp only [Complex.conj_conj] at h
  have ho : ∀ k, ∫ ω, X 0 ω ^ k * conj (X 0 ω) ^ 0 ∂P = if k = 0 then 1 else 0 := fun k => by
    have := (hX.rot 0).cmom_eq k 0
    split_ifs with hk
    · subst hk; simp
    · rw [if_neg hk] at this; exact this
  have hN : ∀ N, ∫ ω, psum (gcoef c) N (X 0 ω) * psum (gcoef c) N (X 0 ω) ∂P = 0 := by
    intro N
    have e : ∀ ω, psum (gcoef c) N (X 0 ω) * psum (gcoef c) N (X 0 ω) =
        ∑ p ∈ range N, ∑ q ∈ range N,
          (gcoef c p * gcoef c q) * (X 0 ω ^ (p + q) * conj (X 0 ω) ^ 0) := by
      intro ω
      simp only [psum, Finset.sum_mul_sum, pow_zero, mul_one, pow_add]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    simp_rw [e]
    rw [integral_finset_sum _ fun p _ => integrable_finset_sum _ fun q _ =>
      ((hX.mom 0).integrable_pow_mul_conj_pow (p + q) 0).const_mul _]
    simp_rw [integral_finset_sum _ fun q _ =>
      ((hX.mom 0).integrable_pow_mul_conj_pow (_ + q) 0).const_mul _, integral_const_mul, ho]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
    split_ifs with hpq
    · have hp : p = 0 := by omega
      subst hp; simp [gcoef_zero]
    · simp
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr' (Eventually.of_forall fun N => (hN N).symm))

/-- **Proposition 6.2, the remainder.** Let `(G, H)` be a centred Gaussian vector with the
covariance of `(X₀, f(a + X₀) - f(a))` and `R = H - c₁ G`. Then `G` is a proper complex Gaussian
of variance `μ₁`, `R` is a proper complex Gaussian of variance `V_f - |c₁|² μ₁` (in the sense
that `⟪w, R⟫ ~ N(0, |w|² (V_f - |c₁|² μ₁)/2)` for every `w`), and `R` is independent of `G`. -/
theorem remainder_gaussian_indep (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {G H : Ω → ℂ}
    (hGHm : AEMeasurable (fun ω => (G ω, H ω)) P)
    (hGH : IsGaussianLike (fun ω => (G ω, H ω)) (fun ω => (X 0 ω, f (a + X 0 ω) - f a)) P) :
    (∀ w : ℂ, P.map (fun ω => ⟪w, G ω⟫) =
        gaussianReal 0 (‖w‖ ^ 2 * radMom (X 0) P 1 / 2).toNNReal) ∧
    (∀ w : ℂ, P.map (fun ω => ⟪w, H ω - c 1 * G ω⟫) =
        gaussianReal 0 (‖w‖ ^ 2 * (Vf c (radMom (X 0) P) - ‖c 1‖ ^ 2 * radMom (X 0) P 1) / 2
          ).toNNReal) ∧
    IndepFun G (fun ω => H ω - c 1 * G ω) P := by
  classical
  set μ1 := radMom (X 0) P 1 with hμ1
  set V := Vf c (radMom (X 0) P) with hV
  set Y : Ω → ℂ × ℂ := fun ω => (X 0 ω, f (a + X 0 ω) - f a) with hYdef
  set Z : Ω → ℂ := fun ω => (f (a + X 0 ω) - f a) - c 1 * X 0 ω with hZdef
  have hcont : Continuous (fun z => f (a + z)) := continuous_of_hasSum hf
  have hX2 : MemLp (X 0) 2 P := hX.memLp_two 0
  have hg2 : MemLp (fun ω => f (a + X 0 ω) - f a) 2 P := hX.memLp_comp_X hf hs 0
  have hZ2 : MemLp Z 2 P := hg2.sub (hX2.const_mul _)
  have hYm : AEMeasurable Y P :=
    ((hX.meas 0).prodMk ((hcont.measurable.comp (hX.meas 0)).sub_const _)).aemeasurable
  have hY2 : MemLp Y 2 P := memLp_prod_iff.2 ⟨hX2, hg2⟩
  -- the mean of `Y` vanishes
  have hgmean : ∫ ω, (f (a + X 0 ω) - f a) ∂P = 0 := by
    have h1 : ∫ ω, f (a + X 0 ω) ∂P = f a := by
      have := hX.integral_Aimg le_rfl hf hs
      simpa [Aimg_one] using this
    have hint : Integrable (fun ω => f (a + X 0 ω)) P := by
      refine ((hg2.integrable one_le_two).add (integrable_const (f a))).congr
        (Eventually.of_forall fun ω => ?_)
      simp
    rw [integral_sub hint (integrable_const _), h1]; simp
  have hYmean : ∫ ω, Y ω ∂P = 0 := by
    rw [hYdef, integral_pair (hX2.integrable one_le_two) (hg2.integrable one_le_two),
      hX.integral_eq_zero 0, hgmean]
    rfl
  have hmeanM : ∀ M : StrongDual ℝ (ℂ × ℂ), ∫ ω, M (Y ω) ∂P = 0 := fun M => by
    rw [M.integral_comp_comm (hY2.integrable one_le_two), hYmean, map_zero]
  have hE : ∀ M : StrongDual ℝ (ℂ × ℂ), ∫ ω, exp ((M (G ω, H ω) : ℝ) * I) ∂P =
      exp (-((∫ ω, M (Y ω) ^ 2 ∂P : ℝ) : ℂ) / 2) := fun M =>
    hGH.integral_exp hGHm hYm M (hmeanM M)
  have hvar : ∀ M : StrongDual ℝ (ℂ × ℂ), variance (fun ω => M (Y ω)) P = ∫ ω, M (Y ω) ^ 2 ∂P :=
    fun M => variance_of_integral_eq_zero (M.continuous.measurable.comp_aemeasurable hYm)
      (hmeanM M)
  -- complex second moments
  have eXX : ∫ ω, X 0 ω * X 0 ω ∂P = 0 := by
    simpa [sq] using hX.integral_pow_eq_zero 0 (p := 2) (by norm_num)
  have eXcX : ∫ ω, X 0 ω * conj (X 0 ω) ∂P = μ1 := by
    have := (hX.rot 0).cmom_eq 1 1
    rw [if_pos rfl] at this
    simpa [cmom] using this
  have egcX := hX.integral_g_mul_conj hf hs
  have egX := hX.integral_g_mul hf hs
  have egg := hX.integral_g_sq hf hs
  have egcg : ∫ ω, (f (a + X 0 ω) - f a) * conj (f (a + X 0 ω) - f a) ∂P = V := by
    rw [hV, hX.Vf_eq_integral hf hs, ← integral_complex_ofReal]
    congr 1; ext ω
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have iXX : Integrable (fun ω => X 0 ω * X 0 ω) P := hX2.integrable_mul hX2 (p := 2) (q := 2)
  have iXcX : Integrable (fun ω => X 0 ω * conj (X 0 ω)) P :=
    hX2.integrable_mul hX2.star (p := 2) (q := 2)
  have igX : Integrable (fun ω => (f (a + X 0 ω) - f a) * X 0 ω) P :=
    hg2.integrable_mul hX2 (p := 2) (q := 2)
  have igcX : Integrable (fun ω => (f (a + X 0 ω) - f a) * conj (X 0 ω)) P :=
    hg2.integrable_mul hX2.star (p := 2) (q := 2)
  have igg : Integrable (fun ω => (f (a + X 0 ω) - f a) * (f (a + X 0 ω) - f a)) P :=
    hg2.integrable_mul hg2 (p := 2) (q := 2)
  have igcg : Integrable (fun ω => (f (a + X 0 ω) - f a) * conj (f (a + X 0 ω) - f a)) P :=
    hg2.integrable_mul hg2.star (p := 2) (q := 2)
  have iXcg : Integrable (fun ω => X 0 ω * conj (f (a + X 0 ω) - f a)) P :=
    hX2.integrable_mul hg2.star (p := 2) (q := 2)
  have eXcg : ∫ ω, X 0 ω * conj (f (a + X 0 ω) - f a) ∂P = conj (c 1) * μ1 := by
    have : ∫ ω, X 0 ω * conj (f (a + X 0 ω) - f a) ∂P =
        conj (∫ ω, (f (a + X 0 ω) - f a) * conj (X 0 ω) ∂P) := by
      rw [← integral_conj]; congr 1; ext ω; simp [mul_comm]
    rw [this, egcX, map_mul, Complex.conj_ofReal]
  have eXZ : ∫ ω, X 0 ω * Z ω ∂P = 0 := by
    have : (fun ω => X 0 ω * Z ω) = fun ω => (f (a + X 0 ω) - f a) * X 0 ω -
        c 1 * (X 0 ω * X 0 ω) := by funext ω; simp only [hZdef]; ring
    rw [this, integral_sub igX (iXX.const_mul _), integral_const_mul, egX, eXX]; simp
  have eXcZ : ∫ ω, X 0 ω * conj (Z ω) ∂P = 0 := by
    have : (fun ω => X 0 ω * conj (Z ω)) = fun ω => X 0 ω * conj (f (a + X 0 ω) - f a) -
        conj (c 1) * (X 0 ω * conj (X 0 ω)) := by
      funext ω; simp only [hZdef, map_sub, map_mul]; ring
    rw [this, integral_sub iXcg (iXcX.const_mul _), integral_const_mul, eXcg, eXcX]; ring
  have eZZ : ∫ ω, Z ω * Z ω ∂P = 0 := by
    have : (fun ω => Z ω * Z ω) = fun ω => (f (a + X 0 ω) - f a) * (f (a + X 0 ω) - f a) -
        2 * c 1 * ((f (a + X 0 ω) - f a) * X 0 ω) + c 1 ^ 2 * (X 0 ω * X 0 ω) := by
      funext ω; simp only [hZdef]; ring
    rw [this, integral_add (f := fun ω => (f (a + X 0 ω) - f a) * (f (a + X 0 ω) - f a) -
        2 * c 1 * ((f (a + X 0 ω) - f a) * X 0 ω)) (igg.sub (igX.const_mul _)) (iXX.const_mul _),
      integral_sub (f := fun ω => (f (a + X 0 ω) - f a) * (f (a + X 0 ω) - f a)) igg
        (igX.const_mul _), integral_const_mul, integral_const_mul, egg, egX, eXX]
    ring
  have eZcZ : ∫ ω, Z ω * conj (Z ω) ∂P = V - ‖c 1‖ ^ 2 * μ1 := by
    have : (fun ω => Z ω * conj (Z ω)) = fun ω =>
        (f (a + X 0 ω) - f a) * conj (f (a + X 0 ω) - f a) -
        conj (c 1) * ((f (a + X 0 ω) - f a) * conj (X 0 ω)) -
        c 1 * (X 0 ω * conj (f (a + X 0 ω) - f a)) +
        (c 1 * conj (c 1)) * (X 0 ω * conj (X 0 ω)) := by
      funext ω; simp only [hZdef, map_sub, map_mul]; ring
    rw [this, integral_add (f := fun ω =>
        (f (a + X 0 ω) - f a) * conj (f (a + X 0 ω) - f a) -
        conj (c 1) * ((f (a + X 0 ω) - f a) * conj (X 0 ω)) -
        c 1 * (X 0 ω * conj (f (a + X 0 ω) - f a)))
        ((igcg.sub (igcX.const_mul _)).sub (iXcg.const_mul _)) (iXcX.const_mul _),
      integral_sub (f := fun ω => (f (a + X 0 ω) - f a) * conj (f (a + X 0 ω) - f a) -
        conj (c 1) * ((f (a + X 0 ω) - f a) * conj (X 0 ω)))
        (igcg.sub (igcX.const_mul _)) (iXcg.const_mul _),
      integral_sub (f := fun ω => (f (a + X 0 ω) - f a) * conj (f (a + X 0 ω) - f a)) igcg
        (igcX.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, egcg, egcX, eXcg, eXcX, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← hμ1]
    have hcc : conj (c 1) * c 1 = ((‖c 1‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']; push_cast; ring
    push_cast at hcc ⊢
    linear_combination (-2 * (μ1 : ℂ)) * hcc
  -- real second moments
  have hXX : ∀ u : ℂ, ∫ ω, ⟪u, X 0 ω⟫ ^ 2 ∂P = ‖u‖ ^ 2 * μ1 / 2 := hX.integral_inner_sq
  have hZZ : ∀ w : ℂ, ∫ ω, ⟪w, Z ω⟫ ^ 2 ∂P = ‖w‖ ^ 2 * (V - ‖c 1‖ ^ 2 * μ1) / 2 := by
    intro w
    have h := integral_inner_mul_inner hZ2 hZ2 w w
    rw [eZZ, eZcZ, mul_zero, zero_add, Complex.conj_mul'] at h
    have e : ((‖w‖ : ℂ) ^ 2 * ((V : ℂ) - (‖c 1‖ : ℂ) ^ 2 * (μ1 : ℂ))) =
        ((‖w‖ ^ 2 * (V - ‖c 1‖ ^ 2 * μ1) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.ofReal_re] at h
    calc ∫ ω, ⟪w, Z ω⟫ ^ 2 ∂P = ∫ ω, ⟪w, Z ω⟫ * ⟪w, Z ω⟫ ∂P := by simp only [sq]
      _ = _ := h
  have hXZ : ∀ u w : ℂ, ∫ ω, ⟪u, X 0 ω⟫ * ⟪w, Z ω⟫ ∂P = 0 := by
    intro u w
    rw [integral_inner_mul_inner hX2 hZ2 u w, eXZ, eXcZ]; simp
  -- the two marginal laws
  refine ⟨fun w => ?_, fun w => ?_, ?_⟩
  · set L : StrongDual ℝ (ℂ × ℂ) := (innerSL ℝ w).comp (ContinuousLinearMap.fst ℝ ℂ ℂ) with hL
    have h := hGH L
    have e1 : (fun ω => L (G ω, H ω)) = fun ω => ⟪w, G ω⟫ := by funext ω; simp [hL]
    have e2 : ∀ ω, L (Y ω) = ⟪w, X 0 ω⟫ := fun ω => by simp [hL, hYdef]
    rw [e1, hvar L] at h
    simp_rw [e2] at h
    rw [hXX w] at h
    exact h
  · set L : StrongDual ℝ (ℂ × ℂ) := (innerSL ℝ w).comp (ContinuousLinearMap.snd ℝ ℂ ℂ -
      (ContinuousLinearMap.mul ℝ ℂ (c 1)).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) with hL
    have h := hGH L
    have e1 : (fun ω => L (G ω, H ω)) = fun ω => ⟪w, H ω - c 1 * G ω⟫ := by
      funext ω; simp [hL]; ring
    have e2 : ∀ ω, L (Y ω) = ⟪w, Z ω⟫ := fun ω => by simp [hL, hYdef, hZdef]; ring
    rw [e1, hvar L] at h
    simp_rw [e2] at h
    rw [hZZ w] at h
    exact h
  -- independence
  have hGm : AEMeasurable G P := measurable_fst.comp_aemeasurable hGHm
  have hHm : AEMeasurable H P := measurable_snd.comp_aemeasurable hGHm
  have hRm : AEMeasurable (fun ω => H ω - c 1 * G ω) P := hHm.sub (hGm.const_mul _)
  rw [indepFun_iff_charFunDual_prod hGm hRm]
  intro L
  set L1 : StrongDual ℝ ℂ := L.comp (ContinuousLinearMap.inl ℝ ℂ ℂ) with hL1
  set L2 : StrongDual ℝ ℂ := L.comp (ContinuousLinearMap.inr ℝ ℂ ℂ) with hL2
  have hLsplit : ∀ x z : ℂ, L (x, z) = L1 x + L2 z := fun x z => by
    rw [hL1, hL2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← map_add]
    simp
  set u := (InnerProductSpace.toDual ℝ ℂ).symm L1 with hu
  set w := (InnerProductSpace.toDual ℝ ℂ).symm L2 with hw
  have hL1u : ∀ x, L1 x = ⟪u, x⟫ := fun x => by rw [hu, InnerProductSpace.toDual_symm_apply]
  have hL2w : ∀ x, L2 x = ⟪w, x⟫ := fun x => by rw [hw, InnerProductSpace.toDual_symm_apply]
  -- the three characteristic functionals
  set A : StrongDual ℝ (ℂ × ℂ) := L.comp ((ContinuousLinearMap.fst ℝ ℂ ℂ).prod
    (ContinuousLinearMap.snd ℝ ℂ ℂ - (ContinuousLinearMap.mul ℝ ℂ (c 1)).comp
      (ContinuousLinearMap.fst ℝ ℂ ℂ))) with hA
  set B1 : StrongDual ℝ (ℂ × ℂ) := L1.comp (ContinuousLinearMap.fst ℝ ℂ ℂ) with hB1
  set B2 : StrongDual ℝ (ℂ × ℂ) := L2.comp (ContinuousLinearMap.snd ℝ ℂ ℂ -
    (ContinuousLinearMap.mul ℝ ℂ (c 1)).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) with hB2
  have hAY : ∀ ω, A (Y ω) = ⟪u, X 0 ω⟫ + ⟪w, Z ω⟫ := fun ω => by
    simp only [hA, hYdef, hZdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.mul_apply']
    rw [hLsplit, hL1u, hL2w]
  have hB1Y : ∀ ω, B1 (Y ω) = ⟪u, X 0 ω⟫ := fun ω => by
    simp only [hB1, hYdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst']
    rw [hL1u]
  have hB2Y : ∀ ω, B2 (Y ω) = ⟪w, Z ω⟫ := fun ω => by
    simp only [hB2, hYdef, hZdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.mul_apply']
    rw [hL2w]
  have hlhs : charFunDual (P.map (fun ω => (G ω, H ω - c 1 * G ω))) L =
      ∫ ω, exp ((A (G ω, H ω) : ℝ) * I) ∂P := by
    rw [charFunDual_apply, integral_map (hGm.prodMk hRm) (by fun_prop)]
    rfl
  have hr1 : charFunDual (P.map G) L1 = ∫ ω, exp ((B1 (G ω, H ω) : ℝ) * I) ∂P := by
    rw [charFunDual_apply, integral_map hGm (by fun_prop)]
    rfl
  have hr2 : charFunDual (P.map (fun ω => H ω - c 1 * G ω)) L2 =
      ∫ ω, exp ((B2 (G ω, H ω) : ℝ) * I) ∂P := by
    rw [charFunDual_apply, integral_map hRm (by fun_prop)]
    rfl
  have hsq : ∫ ω, A (Y ω) ^ 2 ∂P = ∫ ω, B1 (Y ω) ^ 2 ∂P + ∫ ω, B2 (Y ω) ^ 2 ∂P := by
    have iu : Integrable (fun ω => ⟪u, X 0 ω⟫ ^ 2) P :=
      ((innerSL ℝ u).comp_memLp' hX2).integrable_sq
    have iw : Integrable (fun ω => ⟪w, Z ω⟫ ^ 2) P :=
      ((innerSL ℝ w).comp_memLp' hZ2).integrable_sq
    have iuw : Integrable (fun ω => ⟪u, X 0 ω⟫ * ⟪w, Z ω⟫) P :=
      ((innerSL ℝ u).comp_memLp' hX2).integrable_mul ((innerSL ℝ w).comp_memLp' hZ2)
        (p := 2) (q := 2)
    have e : ∀ ω, (⟪u, X 0 ω⟫ + ⟪w, Z ω⟫) ^ 2 =
        ⟪u, X 0 ω⟫ ^ 2 + ⟪w, Z ω⟫ ^ 2 + 2 * (⟪u, X 0 ω⟫ * ⟪w, Z ω⟫) := fun ω => by ring
    simp_rw [hAY, hB1Y, hB2Y, e]
    rw [integral_add (f := fun ω => ⟪u, X 0 ω⟫ ^ 2 + ⟪w, Z ω⟫ ^ 2) (iu.add iw)
      (iuw.const_mul 2), integral_add iu iw, integral_const_mul, hXZ, mul_zero, add_zero]
  rw [hlhs, hr1, hr2, hE A, hE B1, hE B2, hsq, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- **Proposition 6.2** in the paper's form: with `R = H - c₁ G` (a proper complex Gaussian of
variance `V_f - |c₁|² μ₁`, independent of `G`, by `remainder_gaussian_indep`),
`(√m (A_m(f) - f(a)), m^{d/2} (B_m(f) - f(a))) → (c₁ G + R, c_d G^d)`. -/
theorem tendstoInDistribution_joint_paper (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {d : ℕ} (hd : 1 ≤ d)
    (hlow : ∀ n, 1 ≤ n → n < d → c n = 0) {G H : Ω → ℂ}
    (hGHm : AEMeasurable (fun ω => (G ω, H ω)) P)
    (hGH : IsGaussianLike (fun ω => (G ω, H ω)) (fun ω => (X 0 ω, f (a + X 0 ω) - f a)) P) :
    TendstoInDistribution (fun (m : ℕ) ω => ((Real.sqrt m : ℂ) * (Aimg f a X m ω - f a),
      (Real.sqrt m : ℂ) ^ d * (Bimg f a X m ω - f a))) atTop
      (fun ω => (c 1 * G ω + (H ω - c 1 * G ω), c d * G ω ^ d)) P := by
  have h := hX.tendstoInDistribution_joint_clt hf hs hd hlow hGHm hGH
  simpa using h

/-- **Proposition 6.2, case `d = 1`.** `√m (A_m(f) - B_m(f)) → R = H - c₁ G` in distribution. -/
theorem tendstoInDistribution_A_sub_B (hX : RadialSample X P)
    (hf : ∀ z, HasSum (fun n => c n * z ^ n) (f (a + z)))
    (hs : Summable fun n => ‖c n‖ ^ 2 * radMom (X 0) P n) {G H : Ω → ℂ}
    (hGHm : AEMeasurable (fun ω => (G ω, H ω)) P)
    (hGH : IsGaussianLike (fun ω => (G ω, H ω)) (fun ω => (X 0 ω, f (a + X 0 ω) - f a)) P) :
    TendstoInDistribution (fun (m : ℕ) ω => (Real.sqrt m : ℂ) * (Aimg f a X m ω - Bimg f a X m ω))
      atTop (fun ω => H ω - c 1 * G ω) P := by
  have h := (hX.tendstoInDistribution_joint_clt hf hs le_rfl (fun n h1 h2 => by omega) hGHm
    hGH).continuous_comp (g := fun p : ℂ × ℂ => p.1 - p.2) (by fun_prop)
  convert h using 2 with m
  · funext ω; simp only [Function.comp_apply, pow_one]; ring
  · simp

end RadialSample

end Barycenter

-- ============================================================================
-- Source part: Bary38.lean
-- ============================================================================

open Finset Filter Topology MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal ComplexConjugate

namespace Barycenter

/-! ## Part 38. Theorem 2.2: the central limit theorem for `W_m^{(n)}`

The powers `X_j^n` of a radial sample again form a radial sample, with `μ₁(X^n) = μ_n(X)`.
Applying the central limit theorem to them gives the last sentence of Theorem 2.2: for darts
uniform in the unit disk, `√m W_m^{(n)}` converges in distribution to a proper complex Gaussian
of variance `1/(n+1)`. -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace RadialSample

variable {X : ℕ → Ω → ℂ}

/-- The `n`th powers of a radial sample form a radial sample (`n ≥ 1`). -/
theorem pow (hX : RadialSample X P) {n : ℕ} (hn : 1 ≤ n) :
    RadialSample (fun j ω => X j ω ^ n) P := by
  have hpow : Measurable (fun z : ℂ => z ^ n) := by fun_prop
  refine ⟨fun j => (hX.meas j).pow_const n, ?_, fun i j => (hX.ident i j).comp hpow, ?_, ?_⟩
  · exact hX.indep.comp (fun _ z => z ^ n) (fun _ => hpow)
  · intro j θ
    have h := (hX.rot j (θ / n)).comp hpow
    have heq : (fun ω => Complex.exp (θ * Complex.I) * X j ω ^ n) =
        (fun z : ℂ => z ^ n) ∘ (fun ω => Complex.exp ((θ / n : ℝ) * Complex.I) * X j ω) := by
      funext ω
      simp only [Function.comp_apply, mul_pow, ← Complex.exp_nat_mul]
      congr 2
      have : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      push_cast
      field_simp
    rw [heq]; exact h
  · intro j p
    have hm := (hX.mom j).aestronglyMeasurable
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simpa using (hm.pow n)
    · rw [← integrable_norm_rpow_iff (f := fun ω => X j ω ^ n) (p := (p : ℝ≥0∞)) (hm.pow n)
        (by exact_mod_cast hp.ne') (by simp)]
      refine ((hX.mom j).integrable_norm_pow (n * p)).congr (Eventually.of_forall fun ω => ?_)
      simp [norm_pow, pow_mul]

omit [IsProbabilityMeasure P] in
lemma radMom_pow_one (Y : Ω → ℂ) (n : ℕ) :
    radMom (fun ω => Y ω ^ n) P 1 = radMom Y P n := by
  simp only [radMom, norm_pow, ← pow_mul]
  congr 1; funext ω; ring_nf

/-- **Central limit theorem for the centre, as weak convergence of laws** (no auxiliary
Gaussian variable): the laws of `√m S_m` converge weakly to the proper complex Gaussian law of
variance `μ₁`. -/
theorem tendsto_law_sqrt_mul_Scen (hX : RadialSample X P) (hμ : 0 < radMom (X 0) P 1) :
    haveI := isProbabilityMeasure_cgaussLaw hμ
    Tendsto (β := ProbabilityMeasure ℂ) (fun m : ℕ => (⟨P.map (fun ω => (Real.sqrt m : ℂ) *
        Scen X m ω), Measure.isProbabilityMeasure_map
          ((hX.measurable_Scen m).const_mul _).aemeasurable⟩ : ProbabilityMeasure ℂ)) atTop
      (𝓝 (⟨cgaussLaw (radMom (X 0) P 1), isProbabilityMeasure_cgaussLaw hμ⟩ :
        ProbabilityMeasure ℂ)) := by
  haveI := isProbabilityMeasure_cgaussLaw hμ
  set γ := cgaussLaw (radMom (X 0) P 1) with hγ
  set X' : ℕ → Ω × ℂ → ℂ := fun j p => X j p.1 with hX'def
  have hX' : RadialSample X' (P.prod γ) := hX.comp_fst
  have hrad : radMom (X' 0) (P.prod γ) = radMom (X 0) P := radMom_comp_fst (X 0)
  have hG : IsProperComplexGaussian (Prod.snd : Ω × ℂ → ℂ) (radMom (X' 0) (P.prod γ) 1)
      (P.prod γ) := ⟨measurable_snd.aemeasurable, by
        rw [hrad, (measurePreserving_snd (μ := P) (ν := γ)).map_eq]; rfl⟩
  have h := (hX'.tendstoInDistribution_sqrt_mul_Scen (by rw [hrad]; exact hμ) hG).tendsto
  have e1 : ∀ m : ℕ, (P.prod γ).map (fun p => (Real.sqrt m : ℂ) * Scen X' m p) =
      P.map (fun ω => (Real.sqrt m : ℂ) * Scen X m ω) := by
    intro m
    change (P.prod γ).map ((fun ω => (Real.sqrt m : ℂ) * Scen X m ω) ∘ Prod.fst) = _
    rw [← Measure.map_map ((hX.measurable_Scen m).const_mul _) measurable_fst,
      (measurePreserving_fst (μ := P) (ν := γ)).map_eq]
  have e2 : (P.prod γ).map (Prod.snd : Ω × ℂ → ℂ) = γ :=
    (measurePreserving_snd (μ := P) (ν := γ)).map_eq
  convert h using 2 with m
  · exact Subtype.ext (e1 m).symm
  · exact Subtype.ext e2.symm

/-- Central limit theorem for the means of `n`th powers of a radial sample: the laws of
`√m W_m^{(n)}` converge weakly to the proper complex Gaussian law of variance `μ_n`. -/
theorem tendsto_law_sqrt_mul_Wpow (hX : RadialSample X P) {n : ℕ} (hn : 1 ≤ n)
    (hμ : 0 < radMom (X 0) P n) :
    haveI := isProbabilityMeasure_cgaussLaw hμ
    Tendsto (β := ProbabilityMeasure ℂ) (fun m : ℕ => (⟨P.map (fun ω => (Real.sqrt m : ℂ) *
        Wpow X m n ω), Measure.isProbabilityMeasure_map
          (((hX.pow hn).measurable_Scen m).const_mul _).aemeasurable⟩ : ProbabilityMeasure ℂ))
      atTop (𝓝 (⟨cgaussLaw (radMom (X 0) P n), isProbabilityMeasure_cgaussLaw hμ⟩ :
        ProbabilityMeasure ℂ)) := by
  have hμ' : 0 < radMom (fun ω => X 0 ω ^ n) P 1 := by rwa [radMom_pow_one]
  have h := (hX.pow hn).tendsto_law_sqrt_mul_Scen hμ'
  convert h using 4
  rw [radMom_pow_one]

end RadialSample

/-- **Theorem 2.2, central limit theorem.** For darts uniform in the unit disk and `n ≥ 1`, the
laws of `√m W_m^{(n)}` converge weakly to the proper complex Gaussian law of variance
`1/(n+1)`. -/
theorem disk_Wpow_clt {n : ℕ} (hn : 1 ≤ n) :
    haveI := isProbabilityMeasure_cgaussLaw (v := 1 / (n + 1)) (by positivity)
    Tendsto (β := ProbabilityMeasure ℂ) (fun m : ℕ => (⟨diskP.map (fun ω => (Real.sqrt m : ℂ) *
        Wpow coord m n ω), Measure.isProbabilityMeasure_map
          (((disk_radialSample.pow hn).measurable_Scen m).const_mul _).aemeasurable⟩ :
          ProbabilityMeasure ℂ))
      atTop (𝓝 (⟨cgaussLaw (1 / (n + 1)), isProbabilityMeasure_cgaussLaw (by positivity)⟩ :
        ProbabilityMeasure ℂ)) := by
  have hμ : 0 < radMom (coord 0) diskP n := by
    rw [radMom_disk, diskMom]; positivity
  have h := disk_radialSample.tendsto_law_sqrt_mul_Wpow hn hμ
  convert h using 4
  rw [radMom_disk, diskMom]

end Barycenter
