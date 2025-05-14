/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Algebra.GeomSum
import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished

/-!

# Polynomial `(1 + X) ^ n - 1`

This file contains results on polynomial `(1 + X) ^ n - 1`. Mathematically, it is viewed as
the multiply-by-`n` map `[n]` of the formal multiplicative group $\widehat\mathbb{G}_m$.
In particular, `(1 + X) ^ p ^ n - 1` is a distinguished polynomial at `p`.

-/

namespace Polynomial

variable (R : Type*) (p : ℕ) [Fact p.Prime] (n : ℕ)

section Semiring

variable [Semiring R]

/-- The `Polynomial.oneAddXPowSubOne R n` is the polynomial `(1 + X) ^ n - 1` in `R[X]`
(`Polynomial.oneAddXPowSubOne_def`). Since we allow `R` to be a `Semiring`, its actual definition
is `∑ i ∈ [1, n + 1), X ^ i * n.choose i`. -/
noncomputable def oneAddXPowSubOne := ∑ i ∈ Finset.Ico 1 (n + 1), X ^ i * (n.choose i : R[X])

@[simp]
theorem oneAddXPowSubOne_zero : oneAddXPowSubOne R 0 = 0 := by
  simp [oneAddXPowSubOne]

@[simp]
theorem oneAddXPowSubOne_one : oneAddXPowSubOne R 1 = X := by
  simp [oneAddXPowSubOne]

theorem oneAddXPowSubOne_eq_map :
    oneAddXPowSubOne R n = (oneAddXPowSubOne ℕ n).map (algebraMap ℕ R) := by
  simp [oneAddXPowSubOne, Polynomial.map_sum]

theorem commute_oneAddXPowSubOne (p : R[X]) : Commute (oneAddXPowSubOne R n) p :=
  .sum_left _ _ _ fun _ _ ↦ .mul_left (commute_X_pow _ _) (Nat.cast_commute _ _)

theorem coeff_oneAddXPowSubOne_eq (i : ℕ) :
    (oneAddXPowSubOne R n).coeff i = if i = 0 then 0 else (n.choose i : R) := by
  simp_rw [oneAddXPowSubOne, finset_sum_coeff, ← C_eq_natCast, coeff_mul_C, coeff_X_pow,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_Ico]
  split_ifs with h1 h2 h2
  · linarith only [h1.1, h2]
  · rfl
  · rfl
  · rw [not_and, not_lt] at h1
    simp [Nat.choose_eq_zero_of_lt (h1 (Nat.pos_of_ne_zero h2))]

theorem coeff_oneAddXPowSubOne_eq_one_of_ne_zero (hn : n ≠ 0) :
    (oneAddXPowSubOne R n).coeff n = 1 := by
  simp [coeff_oneAddXPowSubOne_eq, if_neg hn]

theorem degree_oneAddXPowSubOne_of_ne_zero [Nontrivial R] (hn : n ≠ 0) :
    (oneAddXPowSubOne R n).degree = n := by
  refine degree_eq_of_le_of_coeff_ne_zero ?_
    (by simp [coeff_oneAddXPowSubOne_eq_one_of_ne_zero R n hn])
  have h1 : oneAddXPowSubOne R n = ∑ i : Fin (n + 1),
      C (if i.1 = 0 then 0 else (n.choose i.1 : R)) * X ^ i.1 := by
    rw [oneAddXPowSubOne]
    trans ∑ i ∈ Finset.range (n + 1), X ^ i * if i = 0 then 0 else (n.choose i : R[X])
    · simp_rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (show 0 < n + 1 by simp),
        if_pos, mul_zero, zero_add]
      congr! 3 with i hi
      rw [Finset.mem_Ico] at hi
      rw [if_neg (show i ≠ 0 by linarith only [hi.1])]
    rw [Finset.sum_range]
    congr! 1 with i
    rw [(commute_X_pow _ i.1).eq]
    congr 1
    split_ifs <;> simp
  have h2 : (oneAddXPowSubOne R n).degree < n + 1 := by
    rw [h1]
    exact degree_sum_fin_lt _
  have h3 (m : WithBot ℕ) (hm : m < n + 1) : m ≤ n := by
    rcases m with ⟨⟩ | m
    · nofun
    · have : m < n + 1 := WithBot.coe_lt_coe.1 hm
      exact WithBot.coe_le_coe.2 (Nat.lt_add_one_iff.1 this)
  exact h3 _ h2

theorem natDegree_oneAddXPowSubOne [Nontrivial R] : (oneAddXPowSubOne R n).natDegree = n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  exact natDegree_eq_of_degree_eq_some (degree_oneAddXPowSubOne_of_ne_zero R n hn)

theorem monic_oneAddXPowSubOne_of_ne_zero (hn : n ≠ 0) : (oneAddXPowSubOne R n).Monic := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact monic_of_subsingleton _
  rw [Monic, leadingCoeff, natDegree_oneAddXPowSubOne,
    coeff_oneAddXPowSubOne_eq_one_of_ne_zero _ _ hn]

end Semiring

section Ring

variable [Ring R]

theorem oneAddXPowSubOne_def : oneAddXPowSubOne R n = (1 + X) ^ n - 1 := by
  rw [add_comm, (commute_X 1).add_pow, oneAddXPowSubOne, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (show 0 < n + 1 by simp)]
  simp

end Ring

section Semiring

variable [Semiring R]

theorem oneAddXPowSubOne_mul_geom_sum (m : ℕ) :
    oneAddXPowSubOne R n * ∑ i ∈ Finset.range m, (1 + X) ^ (n * i) =
      oneAddXPowSubOne R (n * m) := by
  suffices oneAddXPowSubOne ℕ n * ∑ i ∈ Finset.range m, (1 + X) ^ (n * i) =
      oneAddXPowSubOne ℕ (n * m) by
    simp_rw [oneAddXPowSubOne_eq_map R, ← this, Polynomial.map_mul, Polynomial.map_sum,
      Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, Polynomial.map_X]
  suffices oneAddXPowSubOne ℤ n * ∑ i ∈ Finset.range m, (1 + X) ^ (n * i) =
      oneAddXPowSubOne ℤ (n * m) by
    apply_fun map (algebraMap ℕ ℤ) using map_injective _ CharZero.cast_injective
    simp_rw [Polynomial.map_mul, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_add,
      Polynomial.map_one, Polynomial.map_X, ← oneAddXPowSubOne_eq_map, this]
  simpa [oneAddXPowSubOne_def, pow_mul] using
    (Commute.one_right ((1 + X) ^ n : ℤ[X])).mul_geom_sum₂ m

theorem oneAddXPowSubOne_dvd_of_dvd (m : ℕ) (h : n ∣ m) :
    oneAddXPowSubOne R n ∣ oneAddXPowSubOne R m := by
  obtain ⟨m, rfl⟩ := h
  exact Dvd.intro _ (oneAddXPowSubOne_mul_geom_sum R n m)

theorem X_dvd_oneAddXPowSubOne : X ∣ oneAddXPowSubOne R n := by
  simpa using oneAddXPowSubOne_dvd_of_dvd R 1 n (by simp)

theorem dvd_coeff_oneAddXPowSubOne_of_ne (i : ℕ) (hi : i ≠ p ^ n) :
    (p : R) ∣ (oneAddXPowSubOne R (p ^ n)).coeff i := by
  rw [coeff_oneAddXPowSubOne_eq]
  split_ifs with h
  · simp
  obtain ⟨q, hq⟩ := (Fact.out : p.Prime).dvd_choose_pow h hi
  use q
  simp [hq]

end Semiring

section CommRing

variable [CommRing R]

theorem isDistinguishedAt_oneAddXPowSubOne :
    (oneAddXPowSubOne R (p ^ n)).IsDistinguishedAt (Ideal.span {(p : R)}) where
  mem {i} hi := by
    rcases subsingleton_or_nontrivial R with _ | _
    · simp [natDegree_of_subsingleton] at hi
    rw [natDegree_oneAddXPowSubOne] at hi
    rw [Ideal.mem_span_singleton]
    exact dvd_coeff_oneAddXPowSubOne_of_ne R _ _ _ hi.ne
  monic := monic_oneAddXPowSubOne_of_ne_zero R _ (by simp [(Fact.out : p.Prime).ne_zero])

end CommRing

end Polynomial
