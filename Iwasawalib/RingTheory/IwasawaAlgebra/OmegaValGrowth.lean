/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.DistinguishedRoots
public import Mathlib.Data.Nat.Choose.Dvd

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# The growth of `v(ω_n(α))`

Let `ℚ̄_p = PadicAlgCl p` be a fixed algebraic closure of `ℚ_p`, with its (unique) absolute
value extending the `p`-adic one. This file proves blueprint node `omega-val-growth` (ii):
if `α ∈ ℚ̄_p` satisfies `v(α) > 0` (i.e. `‖α‖ < 1`) and `(1 + α) ^ (p ^ n) ≠ 1` for every `n`,
then there are `N` and `c > 0` with
`‖ω_n(α)‖ = ‖(1 + α) ^ (p ^ n) - 1‖ = c * p ^ (-n)` for all `n ≥ N`,
which is exactly `v(ω_n(α)) = n + c_α` for `n ≥ N`.

## Main results

* `PadicAlgCl.one_add_pow_sub_one_eq`: the binomial expansion of `(1 + δ) ^ p - 1`.
* `PadicAlgCl.norm_one_add_pow_sub_one_le`: `‖(1 + δ) ^ p - 1‖ ≤ max (p⁻¹ ‖δ‖) (‖δ‖ ^ p)`.
* `PadicAlgCl.norm_one_add_pow_sub_one_eq`: if `‖δ‖ ^ (p - 1) < p⁻¹` and `δ ≠ 0` then
  `‖(1 + δ) ^ p - 1‖ = p⁻¹ * ‖δ‖`.
* `PadicAlgCl.exists_norm_delta_eq`: **blueprint node `omega-val-growth` (ii)**.
-/

namespace PadicAlgCl

open Finset

variable (p : ℕ) [hp : Fact p.Prime]

theorem one_add_pow_sub_one_eq (δ : PadicAlgCl p) :
    (1 + δ) ^ p - 1 = (p : PadicAlgCl p) * δ +
      ∑ i ∈ Finset.Ico 2 (p + 1), δ ^ i * (p.choose i : PadicAlgCl p) := by
  have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [add_comm (1 : PadicAlgCl p) δ, add_pow]
  simp only [one_pow, mul_one]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p + 1),
    Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < p + 1)]
  simp [Nat.choose_one_right]
  ring

theorem norm_p_eq : ‖(p : PadicAlgCl p)‖ = (p:ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), show
    (algebraMap ℚ_[p] (PadicAlgCl p)) (p:ℚ_[p]) = ((p:ℚ_[p]) : PadicAlgCl p) from rfl,
    PadicAlgCl.norm_extends, Padic.norm_p]

theorem norm_tail_le (δ : PadicAlgCl p) (hδ : ‖δ‖ ≤ 1) :
    ‖∑ i ∈ Finset.Ico 2 (p + 1), δ ^ i * (p.choose i : PadicAlgCl p)‖ ≤
      max ((p:ℝ)⁻¹ * ‖δ‖ ^ 2) (‖δ‖ ^ p) := by
  have hppos : (0:ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (le_max_of_le_right (by positivity)) ?_
  intro i hi
  rw [Finset.mem_Ico] at hi
  rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hi.2) with heq | hlt
  · rw [heq, Nat.choose_self, Nat.cast_one, mul_one, norm_pow]
    exact le_max_right _ _
  · obtain ⟨k, hk⟩ := Nat.Prime.dvd_choose_self (Fact.out : p.Prime) (by omega) hlt
    have hc : ‖((p.choose i : ℕ) : PadicAlgCl p)‖ ≤ (p:ℝ)⁻¹ := by
      rw [hk, Nat.cast_mul, norm_mul, norm_p_eq]
      calc (p:ℝ)⁻¹ * ‖((k : ℕ) : PadicAlgCl p)‖ ≤ (p:ℝ)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_natCast_le_one _ k) (by positivity)
        _ = (p:ℝ)⁻¹ := mul_one _
    refine le_max_of_le_left ?_
    rw [norm_mul, norm_pow]
    calc ‖δ‖ ^ i * ‖((p.choose i : ℕ) : PadicAlgCl p)‖ ≤ ‖δ‖ ^ 2 * (p:ℝ)⁻¹ := by
          refine mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hδ hi.1) hc
            (norm_nonneg _) (by positivity)
      _ = (p:ℝ)⁻¹ * ‖δ‖ ^ 2 := mul_comm _ _

theorem norm_one_add_pow_sub_one_le (δ : PadicAlgCl p) (hδ : ‖δ‖ ≤ 1) :
    ‖(1 + δ) ^ p - 1‖ ≤ max ((p:ℝ)⁻¹ * ‖δ‖) (‖δ‖ ^ p) := by
  have hppos : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [one_add_pow_sub_one_eq]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul, norm_p_eq]
    exact le_max_left _ _
  · refine (norm_tail_le p δ hδ).trans (max_le (le_max_of_le_left ?_) (le_max_right _ _))
    have : ‖δ‖ ^ 2 ≤ ‖δ‖ := by
      nlinarith [norm_nonneg δ]
    exact mul_le_mul_of_nonneg_left this (by positivity)

theorem norm_one_add_pow_sub_one_eq (δ : PadicAlgCl p) (hδ0 : δ ≠ 0)
    (h : ‖δ‖ ^ (p - 1) < (p:ℝ)⁻¹) : ‖(1 + δ) ^ p - 1‖ = (p:ℝ)⁻¹ * ‖δ‖ := by
  have hppos : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpos : 0 < ‖δ‖ := norm_pos_iff.2 hδ0
  have hpinv1 : (p:ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hlt1 : ‖δ‖ < 1 := by
    by_contra hcon
    rw [not_lt] at hcon
    have : (1:ℝ) ≤ ‖δ‖ ^ (p - 1) := one_le_pow₀ hcon
    linarith
  have htail : ‖∑ i ∈ Finset.Ico 2 (p + 1), δ ^ i * (p.choose i : PadicAlgCl p)‖ <
      ‖(p : PadicAlgCl p) * δ‖ := by
    rw [norm_mul, norm_p_eq]
    refine lt_of_le_of_lt (norm_tail_le p δ hlt1.le) (max_lt ?_ ?_)
    · have : ‖δ‖ ^ 2 < ‖δ‖ := by nlinarith
      have hinvpos : (0:ℝ) < (p:ℝ)⁻¹ := by positivity
      nlinarith
    · have hps : ‖δ‖ ^ p = ‖δ‖ ^ (p - 1) * ‖δ‖ := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hps]
      nlinarith
  rw [one_add_pow_sub_one_eq, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt htail),
    max_eq_left htail.le, norm_mul, norm_p_eq]

section Growth

variable {p}
variable {α : PadicAlgCl p} (hα : ‖α‖ < 1) (hne : ∀ n : ℕ, (1 + α) ^ (p ^ n) ≠ 1)

include hne

theorem delta_ne_zero (n : ℕ) : (1 + α) ^ (p ^ n) - 1 ≠ 0 :=
  fun h ↦ hne n (by linear_combination h)

theorem delta_succ (n : ℕ) :
    (1 + α) ^ (p ^ (n + 1)) - 1 = (1 + ((1 + α) ^ (p ^ n) - 1)) ^ p - 1 := by
  rw [show (1 : PadicAlgCl p) + ((1 + α) ^ (p ^ n) - 1) = (1 + α) ^ (p ^ n) by ring,
    ← pow_mul, ← pow_succ]

include hα

theorem norm_delta_le (n : ℕ) :
    ‖(1 + α) ^ (p ^ n) - 1‖ ≤ ‖α‖ * (max ((p:ℝ)⁻¹) (‖α‖ ^ (p - 1))) ^ n := by
  set c := max ((p:ℝ)⁻¹) (‖α‖ ^ (p - 1)) with hc
  have hppos : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcnn : 0 ≤ c := le_max_of_le_left (by positivity)
  have hc1 : c ≤ 1 := by
    refine max_le ?_ ?_
    · rw [inv_le_one_iff₀]; right; exact_mod_cast (Fact.out : p.Prime).one_le
    · exact pow_le_one₀ (norm_nonneg _) hα.le
  induction n with
  | zero => simp
  | succ n ih =>
    have hle : ‖(1 + α) ^ (p ^ n) - 1‖ ≤ ‖α‖ := by
      refine ih.trans ?_
      calc ‖α‖ * c ^ n ≤ ‖α‖ * 1 := by
            exact mul_le_mul_of_nonneg_left (pow_le_one₀ hcnn hc1) (norm_nonneg _)
        _ = ‖α‖ := mul_one _
    have hle1 : ‖(1 + α) ^ (p ^ n) - 1‖ ≤ 1 := hle.trans hα.le
    have hstep := norm_one_add_pow_sub_one_le p ((1 + α) ^ (p ^ n) - 1) hle1
    rw [← delta_succ hne n] at hstep
    have hkey : ‖(1 + α) ^ (p ^ (n + 1)) - 1‖ ≤ c * ‖(1 + α) ^ (p ^ n) - 1‖ := by
      refine hstep.trans (max_le ?_ ?_)
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      · have hps : ‖(1 + α) ^ (p ^ n) - 1‖ ^ p =
            ‖(1 + α) ^ (p ^ n) - 1‖ ^ (p - 1) * ‖(1 + α) ^ (p ^ n) - 1‖ := by
          rw [← pow_succ]; congr 1; omega
        rw [hps]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact le_max_of_le_right (pow_le_pow_left₀ (norm_nonneg _) hle _)
    calc ‖(1 + α) ^ (p ^ (n + 1)) - 1‖ ≤ c * ‖(1 + α) ^ (p ^ n) - 1‖ := hkey
      _ ≤ c * (‖α‖ * c ^ n) := mul_le_mul_of_nonneg_left ih hcnn
      _ = ‖α‖ * c ^ (n + 1) := by ring

/-- **Blueprint node `omega-val-growth` (ii)**: if `v(α) > 0` and `(1 + α) ^ (p ^ n) ≠ 1` for
all `n`, then `v(ω_n(α)) = n + c_α` for all sufficiently large `n`; multiplicatively,
`‖(1 + α) ^ (p ^ n) - 1‖ = c * p ^ (-n)`. -/
theorem exists_norm_delta_eq :
    ∃ (N : ℕ) (c : ℝ), 0 < c ∧ ∀ n, N ≤ n →
      ‖(1 + α) ^ (p ^ n) - 1‖ = c * ((p : ℝ)⁻¹) ^ n := by
  have hppos : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpne : (p:ℝ) ≠ 0 := ne_of_gt hppos
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpinv1 : (p:ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact_mod_cast (Fact.out : p.Prime).one_le
  set c₀ := max ((p:ℝ)⁻¹) (‖α‖ ^ (p - 1)) with hc₀
  have hc₀nn : 0 ≤ c₀ := le_max_of_le_left (by positivity)
  have hc₀lt : c₀ < 1 := by
    refine max_lt ?_ ?_
    · rw [inv_lt_one_iff₀]; right; exact_mod_cast (Fact.out : p.Prime).one_lt
    · exact pow_lt_one₀ (norm_nonneg _) hα (by omega)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < (p:ℝ)⁻¹ by positivity) hc₀lt
  have hδN : ‖(1 + α) ^ (p ^ N) - 1‖ < (p:ℝ)⁻¹ := by
    refine lt_of_le_of_lt ((norm_delta_le hα hne N).trans ?_) hN
    calc ‖α‖ * c₀ ^ N ≤ 1 * c₀ ^ N :=
          mul_le_mul_of_nonneg_right hα.le (by positivity)
      _ = c₀ ^ N := one_mul _
  have hbase : ‖(1 + α) ^ (p ^ N) - 1‖ ^ (p - 1) < (p:ℝ)⁻¹ :=
    lt_of_le_of_lt (pow_le_of_le_one (norm_nonneg _) (hδN.le.trans hpinv1) (by omega)) hδN
  have key : ∀ n, N ≤ n → ‖(1 + α) ^ (p ^ n) - 1‖ ^ (p - 1) < (p:ℝ)⁻¹ ∧
      ‖(1 + α) ^ (p ^ n) - 1‖ = ‖(1 + α) ^ (p ^ N) - 1‖ * ((p:ℝ)⁻¹) ^ (n - N) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact ⟨hbase, by simp⟩
    | succ n hn ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have heq := norm_one_add_pow_sub_one_eq p ((1 + α) ^ (p ^ n) - 1) (delta_ne_zero hne n) ih1
      rw [← delta_succ hne n] at heq
      refine ⟨?_, ?_⟩
      · rw [heq]
        refine lt_of_le_of_lt (pow_le_pow_left₀ (by positivity) ?_ _) ih1
        nlinarith [norm_nonneg ((1 + α) ^ (p ^ n) - 1)]
      · rw [heq, ih2, show n + 1 - N = (n - N) + 1 by omega, pow_succ]
        ring
  refine ⟨N, ‖(1 + α) ^ (p ^ N) - 1‖ * (p:ℝ) ^ N, ?_, ?_⟩
  · have : 0 < ‖(1 + α) ^ (p ^ N) - 1‖ := norm_pos_iff.2 (delta_ne_zero hne N)
    positivity
  · intro n hn
    rw [(key n hn).2]
    have hsplit : ((p:ℝ)⁻¹) ^ n = ((p:ℝ)⁻¹) ^ (n - N) * ((p:ℝ)⁻¹) ^ N := by
      rw [← pow_add]; congr 1; omega
    have hcancel : (p:ℝ) ^ N * ((p:ℝ)⁻¹) ^ N = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hpne, one_pow]
    rw [hsplit]
    calc ‖(1 + α) ^ (p ^ N) - 1‖ * ((p:ℝ)⁻¹) ^ (n - N)
        = ‖(1 + α) ^ (p ^ N) - 1‖ * ((p:ℝ)⁻¹) ^ (n - N) *
            ((p:ℝ) ^ N * ((p:ℝ)⁻¹) ^ N) := by rw [hcancel, mul_one]
      _ = ‖(1 + α) ^ (p ^ N) - 1‖ * (p:ℝ) ^ N * (((p:ℝ)⁻¹) ^ (n - N) * ((p:ℝ)⁻¹) ^ N) := by ring

end Growth

end PadicAlgCl
