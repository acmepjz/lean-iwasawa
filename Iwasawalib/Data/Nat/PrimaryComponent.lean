/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

/-!

# Primary and prime-to-`n` component of a natural number (TODO: should go mathlib ???)

-/

namespace Nat

variable (n m : ℕ) {k : ℕ}

/-- The `m`-primary component for a non-zero natural number `n` is the largest divisor of `n`
whose prime factors divide `m`. This number has explicit expression `gcd(n, m ^ n)`. -/
def primaryComponent : ℕ := n.gcd (m ^ n)

/-- The prime-to-`m` component for a non-zero natural number `n` is the largest divisor of `n`
which is coprime to `m`. -/
def primeToComponent : ℕ := n / n.primaryComponent m

@[simp]
theorem primaryComponent_zero_left : primaryComponent 0 m = 1 := by
  simp [primaryComponent]

variable {n} in
theorem primaryComponent_zero_right (hn : n ≠ 0) : primaryComponent n 0 = n := by
  simp [primaryComponent, zero_pow hn]

theorem primaryComponent_pos : 0 < primaryComponent n m := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [primaryComponent, Nat.pos_of_ne_zero hn]

@[simp]
theorem primeToComponent_zero_left : primeToComponent 0 m = 0 := by
  simp [primeToComponent]

variable {n} in
theorem primeToComponent_zero_right (hn : n ≠ 0) : primeToComponent n 0 = 1 := by
  simp [primeToComponent, primaryComponent_zero_right hn, Nat.div_self (Nat.pos_of_ne_zero hn)]

theorem primaryComponent_dvd_self : n.primaryComponent m ∣ n :=
  Nat.gcd_dvd_left ..

theorem primeToComponent_dvd_self : n.primeToComponent m ∣ n :=
  Nat.div_dvd_of_dvd (primaryComponent_dvd_self ..)

@[simp]
theorem primeToComponent_mul_primaryComponent :
    n.primeToComponent m * n.primaryComponent m = n := by
  rw [primeToComponent, Nat.div_mul_cancel (primaryComponent_dvd_self ..)]

variable {n} in
theorem primaryComponent_eq_div (hn : n ≠ 0) :
    n.primaryComponent m = n / n.primeToComponent m := by
  rw [primeToComponent, Nat.div_div_self (primaryComponent_dvd_self ..) hn]

@[simp]
theorem primeToComponent_eq_zero_iff : primeToComponent n m = 0 ↔ n = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [h] using primeToComponent_dvd_self n m
  · simp [h]

theorem primeToComponent_ne_zero_iff : primeToComponent n m ≠ 0 ↔ n ≠ 0 := by
  simp

variable {n m} in
theorem primeFactors_primaryComponent_subset (hn : n ≠ 0) (hm : m ≠ 0) :
    (n.primaryComponent m).primeFactors ⊆ m.primeFactors := by
  have := Nat.primeFactors_mono (Nat.gcd_dvd_right n (m ^ n)) (by simp [hm])
  rwa [Nat.primeFactors_pow _ hn, ← primaryComponent] at this

variable {n m} in
theorem dvd_primaryComponent_iff (hn : n ≠ 0) (hm : m ≠ 0) :
    k ∣ n.primaryComponent m ↔ k ∣ n ∧ k.primeFactors ⊆ m.primeFactors := by
  refine ⟨fun h ↦ ⟨h.trans (primaryComponent_dvd_self ..), ?_⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  · exact (Nat.primeFactors_mono h (primaryComponent_pos n m).ne').trans
      (primeFactors_primaryComponent_subset hn hm)
  · rcases eq_or_ne k 0 with rfl | hk
    · rw [zero_dvd_iff] at h1; contradiction
    rw [← Nat.dvd_pow_self_iff hk hm] at h2
    rw [primaryComponent, Nat.dvd_gcd_iff]
    exact ⟨h1, h2.trans (Nat.pow_dvd_pow m (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h1))⟩

variable {n} in
theorem coprime_primeToComponent_right (hn : n ≠ 0) : (n.primeToComponent m).Coprime m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [primeToComponent_zero_right hn]
  have h := Nat.gcd_dvd_left (n.primeToComponent m) m
  nth_rw 2 [primeToComponent] at h
  rw [Nat.dvd_div_iff_mul_dvd (primaryComponent_dvd_self ..)] at h
  have := (dvd_primaryComponent_iff hn hm).2 ⟨h, ?_⟩
  · obtain ⟨x, hx⟩ := this
    rw [mul_assoc, left_eq_mul₀ (primaryComponent_pos n m).ne', mul_eq_one] at hx
    exact hx.1
  · rw [Nat.primeFactors_mul (primaryComponent_pos n m).ne' (by simp [hm]),
      Finset.union_subset_iff]
    exact ⟨primeFactors_primaryComponent_subset hn hm, primeFactors_mono (Nat.gcd_dvd_right ..) hm⟩

theorem coprime_primeToComponent_primaryComponent :
    (n.primeToComponent m).Coprime (n.primaryComponent m) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [primaryComponent]
  exact ((coprime_primeToComponent_right m hn).pow_right n).coprime_dvd_right (Nat.gcd_dvd_right ..)

variable {n} in
theorem dvd_primeToComponent_iff (hn : n ≠ 0) :
    k ∣ n.primeToComponent m ↔ k ∣ n ∧ k.Coprime m := by
  refine ⟨fun h ↦ ⟨h.trans (primeToComponent_dvd_self ..), ?_⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  · exact (coprime_primeToComponent_right m hn).coprime_dvd_left h
  · rw [primeToComponent, Nat.dvd_div_iff_mul_dvd (primaryComponent_dvd_self ..)]
    have := (h2.pow_right n).symm.coprime_dvd_left (Nat.gcd_dvd_right n _)
    rw [← primaryComponent] at this
    exact this.mul_dvd_of_dvd_of_dvd (primaryComponent_dvd_self ..) h1

variable {m} in
theorem factorization_primaryComponent (hm : m ≠ 0) (p : ℕ) :
    (n.primaryComponent m).factorization p =
      if p ∈ m.primeFactors then n.factorization p else 0 := by
  rw [← Nat.support_factorization]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  by_cases hprime : p.Prime
  · rw [primaryComponent, factorization_gcd hn (by simp [hm]), factorization_pow,
      Finsupp.inf_apply, Finsupp.smul_apply, smul_eq_mul]
    split_ifs with hp
    · rw [inf_eq_left]
      trans n
      · exact Nat.factorization_le_of_le_pow (Nat.lt_pow_self hprime.one_lt).le
      · exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hp))
    · simp [Finsupp.notMem_support_iff.1 hp]
  simp [Nat.factorization_eq_zero_of_not_prime _ hprime]

variable {m} in
theorem factorization_primeToComponent (hm : m ≠ 0) (p : ℕ) :
    (n.primeToComponent m).factorization p =
      if p ∈ m.primeFactors then 0 else n.factorization p := by
  let x := ordProj[p] n
  rw [primeToComponent, Nat.factorization_div (primaryComponent_dvd_self ..), Finsupp.coe_tsub,
    Pi.sub_apply, factorization_primaryComponent _ hm]
  split_ifs <;> simp

variable {m} in
theorem primaryComponent_eq_prod' (hm : m ≠ 0) :
    n.primaryComponent m = ∏ p ∈ m.primeFactors, p ^ n.factorization p := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  refine Nat.factorization_inj ?_ ?_ ?_
  · simp [(primaryComponent_pos n m).ne']
  · rw [Set.mem_ofPred_eq, Finset.prod_ne_zero_iff]
    intro p hp
    simp [(Nat.prime_of_mem_primeFactors hp).ne_zero]
  · ext p
    by_cases hprime : p.Prime
    · rw [factorization_primaryComponent _ hm, Nat.factorization_prod_apply fun q hq ↦ by
        simp [(Nat.prime_of_mem_primeFactors hq).ne_zero], eq_comm]
      split_ifs with hp
      · rw [Finset.sum_eq_single_of_mem _ hp fun q hq hneq ↦ by
          have : ¬p ∣ q := by
            rw [Nat.prime_dvd_prime_iff_eq hprime (Nat.prime_of_mem_primeFactors hq)]
            exact hneq.symm
          simp [Nat.factorization_eq_zero_iff, this]]
        simp [hprime.factorization_self]
      · refine Finset.sum_eq_zero fun q hq ↦ ?_
        have : ¬p ∣ q := by
          rw [Nat.prime_dvd_prime_iff_eq hprime (Nat.prime_of_mem_primeFactors hq)]
          exact (ne_of_mem_of_not_mem hq hp).symm
        simp [Nat.factorization_eq_zero_iff, this]
    simp [Nat.factorization_eq_zero_of_not_prime _ hprime]

variable {m} in
theorem primaryComponent_eq_prod (hm : m ≠ 0) :
    n.primaryComponent m = ∏ p ∈ n.primeFactors ∩ m.primeFactors, p ^ n.factorization p := by
  rw [primaryComponent_eq_prod' _ hm, eq_comm]
  refine Finset.prod_subset (by simp) fun q h1 h2 ↦ ?_
  rw [Finset.mem_inter, not_and'] at h2
  simp [Finsupp.notMem_support_iff.1 (n.support_factorization ▸ h2 h1)]

variable {n m} in
theorem primeToComponent_eq_prod (hn : n ≠ 0) (hm : m ≠ 0) :
    n.primeToComponent m = ∏ p ∈ n.primeFactors \ m.primeFactors, p ^ n.factorization p := by
  rw [primeToComponent, primaryComponent_eq_prod _ hm]
  refine Nat.div_eq_of_eq_mul_right ?_ ?_
  · rw [Nat.pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro q hq
    rw [Finset.mem_inter] at hq
    simp [(Nat.prime_of_mem_primeFactors hq.1).ne_zero]
  · rw [Finset.prod_inter_mul_prod_sdiff, ← Nat.prod_primeFactors_pow_factorization hn]

section Prime

variable (p : ℕ) [Fact p.Prime]

theorem primaryComponent_eq_of_prime : n.primaryComponent p = p ^ n.factorization p := by
  simp [primaryComponent_eq_prod' _ ‹Fact p.Prime›.out.ne_zero, ‹Fact p.Prime›.out.primeFactors]

theorem primeToComponent_eq_of_prime : n.primeToComponent p = n / p ^ n.factorization p := by
  rw [primeToComponent, primaryComponent_eq_of_prime]

end Prime

end Nat
