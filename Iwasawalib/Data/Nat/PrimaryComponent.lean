/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

/-!

# `m`-primary and prime-to-`m` component of a natural number

TODO: should go mathlib ???

-/

namespace Nat

-- some results are needed to prove that the primary component map is multiplicative

private theorem primeFactors_primaryComponent_subset {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    (n.gcd (m ^ n)).primeFactors ⊆ m.primeFactors := by
  have := primeFactors_mono (gcd_dvd_right n (m ^ n)) (by simp [hm])
  rwa [primeFactors_pow _ hn] at this

private theorem dvd_primaryComponent_iff {n m k : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    k ∣ n.gcd (m ^ n) ↔ k ∣ n ∧ k.primeFactors ⊆ m.primeFactors := by
  refine ⟨fun h ↦ ⟨h.trans (gcd_dvd_left n (m ^ n)), ?_⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  · exact (primeFactors_mono h (by simp [hn])).trans
      (primeFactors_primaryComponent_subset hn hm)
  · rcases eq_or_ne k 0 with rfl | hk
    · rw [zero_dvd_iff] at h1; contradiction
    rw [← dvd_pow_self_iff hk hm] at h2
    rw [dvd_gcd_iff]
    exact ⟨h1, h2.trans (pow_dvd_pow m (le_of_dvd (pos_of_ne_zero hn) h1))⟩

private theorem primaryComponent_eq_gcd_of_le {n : ℕ} (m : ℕ) {k : ℕ} (hn : n ≠ 0) (hle : n ≤ k) :
    n.gcd (m ^ n) = n.gcd (m ^ k) := by
  have hk := ((pos_of_ne_zero hn).trans_le hle).ne'
  rcases eq_or_ne m 0 with rfl | hm
  · simp [hn, hk]
  apply dvd_antisymm
  · exact gcd_dvd_gcd_of_dvd_right n (pow_dvd_pow m hle)
  · rw [dvd_primaryComponent_iff hn hm]
    use gcd_dvd_left ..
    refine (primeFactors_mono (gcd_dvd_right ..) (by simp [hm])).trans ?_
    rw [primeFactors_pow _ hk]

variable (m n : ℕ)

/-! ### `m`-primary component -/

/-- `Nat.ordProj m` is the `m`-primary component map `ℕ →*₀ ℕ`, which maps `0` to `0`, and maps a
non-zero `n` to the largest divisor of `n` whose prime factors divide `m`, which has explicit
expression `gcd(n, m ^ n)`. -/
def ordProj : ℕ →*₀ ℕ where
  toFun n := if n = 0 then 0 else n.gcd (m ^ n)
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb]
    refine dvd_antisymm ?_ (dvd_gcd ?_ ?_)
    · rw [primaryComponent_eq_gcd_of_le m ha (Nat.le_mul_of_pos_right a (pos_of_ne_zero hb)),
        primaryComponent_eq_gcd_of_le m hb (Nat.le_mul_of_pos_left b (pos_of_ne_zero ha))]
      exact gcd_mul_left_dvd_mul_gcd ..
    · exact mul_dvd_mul (gcd_dvd_left ..) (gcd_dvd_left ..)
    · rcases eq_or_ne a 1 with rfl | ha1
      · simp [gcd_dvd_right]
      rcases eq_or_ne b 1 with rfl | hb1
      · simp [gcd_dvd_right]
      have h := add_le_mul (a.two_le_iff.2 ⟨ha, ha1⟩) (b.two_le_iff.2 ⟨hb, hb1⟩)
      trans m ^ a * m ^ b
      · exact mul_dvd_mul (gcd_dvd_right ..) (gcd_dvd_right ..)
      · simp only [← pow_add, pow_dvd_pow m h]

theorem ordProj_apply : m.ordProj n = if n = 0 then 0 else n.gcd (m ^ n) := rfl

@[simp]
theorem ordProj_zero : ordProj 0 = .id _ := by
  ext n hn
  simp [ordProj_apply, hn.ne']

theorem ordProj_zero_apply : ordProj 0 n = n := by
  simp

theorem ordProj_one : ordProj 1 = 1 := by
  ext n hn
  simp [ordProj_apply, hn.ne', MonoidWithZeroHom.one_apply_of_ne_zero hn.ne']

theorem ordProj_one_apply : ordProj 1 n = if n = 0 then 0 else 1 := by
  simp [ordProj_apply]

variable {n} in
theorem ordProj_apply_eq_gcd (hn : n ≠ 0) : m.ordProj n = n.gcd (m ^ n) := by
  rw [ordProj_apply, if_neg hn]

variable {n} in
theorem ordProj_apply_eq_gcd_of_le {k : ℕ} (hn : n ≠ 0) (hle : n ≤ k) :
    m.ordProj n = n.gcd (m ^ k) := by
  rw [ordProj_apply_eq_gcd _ hn, primaryComponent_eq_gcd_of_le _ hn hle]

theorem ordProj_apply_dvd_self : m.ordProj n ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ordProj_apply_eq_gcd _ hn]
  exact gcd_dvd_left ..

@[simp]
theorem ordProj_apply_eq_zero_iff : m.ordProj n = 0 ↔ n = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [h] using ordProj_apply_dvd_self m n
  · simp [h]

theorem ordProj_apply_ne_zero_iff : m.ordProj n ≠ 0 ↔ n ≠ 0 := by
  simp

variable {m} in
theorem primeFactors_ordProj_apply_subset (hm : m ≠ 0) :
    (m.ordProj n).primeFactors ⊆ m.primeFactors := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ordProj_apply_eq_gcd _ hn]
  exact primeFactors_primaryComponent_subset hn hm

variable {n} in
theorem primeFactors_ordProj_apply_subset' {p : ℕ} (hn : n ≠ 0)
    (hprime : p.Prime) (hp : p ∣ m.ordProj n) : p ∣ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have := mem_primeFactors.1 <| primeFactors_ordProj_apply_subset n hm <|
    mem_primeFactors.2 ⟨hprime, hp, (ordProj_apply_ne_zero_iff m n).2 hn⟩
  exact this.2.1

variable {m n} in
theorem dvd_ordProj_apply_iff {k : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    k ∣ m.ordProj n ↔ k ∣ n ∧ k.primeFactors ⊆ m.primeFactors := by
  rw [ordProj_apply_eq_gcd _ hn, dvd_primaryComponent_iff hn hm]

variable {n} in
theorem dvd_ordProj_apply_iff' {k : ℕ} (hn : n ≠ 0) :
    k ∣ m.ordProj n ↔ k ∣ n ∧ ∀ p : ℕ, p.Prime → p ∣ k → p ∣ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rw [dvd_ordProj_apply_iff hm hn, and_congr_right_iff]
  intro hk
  refine ⟨fun h p h1 h2 ↦ ?_, fun h p h1 ↦ ?_⟩
  · specialize @h p
    simp only [mem_primeFactors] at h
    exact (h ⟨h1, h2, ne_zero_of_dvd_ne_zero hn hk⟩).2.1
  · simp only [mem_primeFactors] at h1 ⊢
    exact ⟨h1.1, h p h1.1 h1.2.1, hm⟩

theorem factorization_ordProj_apply_eq_filter :
    (m.ordProj n).factorization = n.factorization.filter (· ∣ m) := by
  ext p
  rw [Finsupp.filter_apply]
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  by_cases hprime : p.Prime
  · rw [ordProj_apply_eq_gcd _ hn, factorization_gcd hn (by simp [hm]), factorization_pow,
      Finsupp.inf_apply, Finsupp.smul_apply, smul_eq_mul]
    split_ifs with hp
    · rw [inf_eq_left]
      trans n
      · exact factorization_le_of_le_pow (Nat.lt_pow_self hprime.one_lt).le
      · exact Nat.le_mul_of_pos_right _ (hprime.factorization_pos_of_dvd hm hp)
    · simp [factorization_eq_zero_iff, hp]
  simp [factorization_eq_zero_of_not_prime _ hprime]

theorem factorization_ordProj_apply_apply' (p : ℕ) :
    (m.ordProj n).factorization p = if p ∣ m then n.factorization p else 0 := by
  rw [factorization_ordProj_apply_eq_filter, Finsupp.filter_apply]

variable {m} in
theorem factorization_ordProj_apply_apply (hm : m ≠ 0) (p : ℕ) :
    (m.ordProj n).factorization p = if p ∈ m.primeFactors then n.factorization p else 0 := by
  rw [factorization_ordProj_apply_apply']
  by_cases hprime : p.Prime
  · congr! 1
    simp [hm, hprime]
  simp [factorization_eq_zero_of_not_prime _ hprime]

variable {m n} in
theorem ordProj_apply_eq_prod' (hm : m ≠ 0) (hn : n ≠ 0) :
    m.ordProj n = ∏ p ∈ m.primeFactors, p ^ n.factorization p := by
  refine factorization_inj ?_ ?_ ?_
  · simp [hn]
  · rw [Set.mem_ofPred_eq, Finset.prod_ne_zero_iff]
    intro p hp
    simp [(prime_of_mem_primeFactors hp).ne_zero]
  · ext p
    by_cases hprime : p.Prime
    · rw [factorization_ordProj_apply_apply _ hm, factorization_prod_apply fun q hq ↦ by
        simp [(prime_of_mem_primeFactors hq).ne_zero], eq_comm]
      split_ifs with hp
      · rw [Finset.sum_eq_single_of_mem _ hp fun q hq hneq ↦ by
          have : ¬p ∣ q := by
            rw [prime_dvd_prime_iff_eq hprime (prime_of_mem_primeFactors hq)]
            exact hneq.symm
          simp [factorization_eq_zero_iff, this]]
        simp [hprime.factorization_self]
      · refine Finset.sum_eq_zero fun q hq ↦ ?_
        have : ¬p ∣ q := by
          rw [prime_dvd_prime_iff_eq hprime (prime_of_mem_primeFactors hq)]
          exact (ne_of_mem_of_not_mem hq hp).symm
        simp [factorization_eq_zero_iff, this]
    simp [factorization_eq_zero_of_not_prime _ hprime]

variable {m n} in
theorem ordProj_apply_eq_prod (hm : m ≠ 0) (hn : n ≠ 0) :
    m.ordProj n = ∏ p ∈ n.primeFactors ∩ m.primeFactors, p ^ n.factorization p := by
  rw [ordProj_apply_eq_prod' hm hn, eq_comm]
  refine Finset.prod_subset (by simp) fun q h1 h2 ↦ ?_
  rw [Finset.mem_inter, not_and'] at h2
  simp [Finsupp.notMem_support_iff.1 (n.support_factorization ▸ h2 h1)]

variable {n} in
theorem ordProj_apply_eq_of_prime (hn : n ≠ 0) (p : ℕ) [Fact p.Prime] :
    p.ordProj n = p ^ n.factorization p := by
  simp [ordProj_apply_eq_prod' ‹Fact p.Prime›.out.ne_zero hn, ‹Fact p.Prime›.out.primeFactors]

/-! ### Prime-to-`m` component -/

/-- `Nat.ordCompl m` is the prime-to-`m` component map `ℕ →*₀ ℕ`, which maps `0` to `0`, and maps a
non-zero `n` to the the largest divisor of `n` which is coprime to `m`. -/
def ordCompl : ℕ →*₀ ℕ where
  toFun n := n / m.ordProj n
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, Nat.div_mul_div_comm (ordProj_apply_dvd_self m a) (ordProj_apply_dvd_self m b)]

theorem ordCompl_apply : m.ordCompl n = n / m.ordProj n := rfl

theorem ordCompl_zero : ordCompl 0 = 1 := by
  ext n hn
  simp [ordCompl_apply, Nat.div_self hn, MonoidWithZeroHom.one_apply_of_ne_zero hn.ne']

theorem ordCompl_zero_apply : ordCompl 0 n = if n = 0 then 0 else 1 := by
  rcases eq_zero_or_pos n with rfl | hn
  · simp
  rw [ordCompl_apply, ordProj_zero_apply, Nat.div_self hn, if_neg hn.ne']

@[simp]
theorem ordCompl_one : ordCompl 1 = .id _ := by
  ext n hn
  simp [ordCompl_apply, ordProj_one_apply, if_neg hn.ne']

theorem ordCompl_one_apply : ordCompl 1 n = n := by
  simp

theorem ordCompl_apply_dvd_self : m.ordCompl n ∣ n := by
  rw [ordCompl_apply]
  exact Nat.div_dvd_of_dvd (ordProj_apply_dvd_self ..)

@[simp]
theorem ordCompl_apply_eq_zero_iff : m.ordCompl n = 0 ↔ n = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [h] using ordCompl_apply_dvd_self m n
  · simp [h]

theorem ordCompl_apply_ne_zero_iff : m.ordCompl n ≠ 0 ↔ n ≠ 0 := by
  simp

@[simp]
theorem ordCompl_apply_mul_ordProj_apply :
    m.ordCompl n * m.ordProj n = n := by
  rw [ordCompl_apply, Nat.div_mul_cancel (ordProj_apply_dvd_self ..)]

theorem ordProj_apply_eq_div :
    m.ordProj n = n / m.ordCompl n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ordCompl_apply, Nat.div_div_self (ordProj_apply_dvd_self ..) hn]

variable {n} in
theorem coprime_ordCompl_apply (hn : n ≠ 0) : (m.ordCompl n).Coprime m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [ordCompl_zero_apply, hn]
  have h := Nat.gcd_dvd_left (m.ordCompl n) m
  nth_rw 2 [ordCompl_apply] at h
  rw [Nat.dvd_div_iff_mul_dvd (ordProj_apply_dvd_self ..)] at h
  have hn' := (ordProj_apply_ne_zero_iff m n).2 hn
  have := (dvd_ordProj_apply_iff hm hn).2 ⟨h, ?_⟩
  · obtain ⟨x, hx⟩ := this
    rw [mul_assoc, left_eq_mul₀ hn', mul_eq_one] at hx
    exact hx.1
  · rw [primeFactors_mul hn' (by simp [hm]), Finset.union_subset_iff]
    exact ⟨primeFactors_ordProj_apply_subset n hm, primeFactors_mono (gcd_dvd_right ..) hm⟩

variable {n} in
theorem coprime_ordCompl_apply_ordProj_apply (hn : n ≠ 0) :
    (m.ordCompl n).Coprime (m.ordProj n) := by
  rw [ordProj_apply_eq_gcd _ hn]
  exact ((coprime_ordCompl_apply m hn).pow_right n).coprime_dvd_right (gcd_dvd_right ..)

variable {n} in
theorem dvd_ordCompl_apply_iff {k : ℕ} (hn : n ≠ 0) :
    k ∣ m.ordCompl n ↔ k ∣ n ∧ k.Coprime m := by
  refine ⟨fun h ↦ ⟨h.trans (ordCompl_apply_dvd_self ..), ?_⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  · exact (coprime_ordCompl_apply m hn).coprime_dvd_left h
  · rw [ordCompl_apply, Nat.dvd_div_iff_mul_dvd (ordProj_apply_dvd_self ..)]
    have := (h2.pow_right n).symm.coprime_dvd_left (Nat.gcd_dvd_right n _)
    rw [← ordProj_apply_eq_gcd _ hn] at this
    exact this.mul_dvd_of_dvd_of_dvd (ordProj_apply_dvd_self ..) h1

theorem factorization_ordCompl_apply_eq_filter :
    (m.ordCompl n).factorization = n.factorization.filter (¬· ∣ m) := by
  ext p
  rw [Finsupp.filter_apply, ordCompl_apply, factorization_div (ordProj_apply_dvd_self ..),
    factorization_ordProj_apply_eq_filter, Finsupp.tsub_apply, Finsupp.filter_apply]
  split_ifs <;> simp

theorem factorization_ordCompl_apply_apply' (p : ℕ) :
    (m.ordCompl n).factorization p = if p ∣ m then 0 else n.factorization p := by
  rw [factorization_ordCompl_apply_eq_filter, Finsupp.filter_apply]
  split_ifs <;> simp

variable {m} in
theorem factorization_ordCompl_apply_apply (hm : m ≠ 0) (p : ℕ) :
    (m.ordCompl n).factorization p = if p ∈ m.primeFactors then 0 else n.factorization p := by
  rw [factorization_ordCompl_apply_apply']
  by_cases hprime : p.Prime
  · congr! 1
    simp [hm, hprime]
  simp [factorization_eq_zero_of_not_prime _ hprime]

variable {m n} in
theorem ordCompl_apply_eq_prod (hm : m ≠ 0) (hn : n ≠ 0) :
    m.ordCompl n = ∏ p ∈ n.primeFactors \ m.primeFactors, p ^ n.factorization p := by
  rw [ordCompl_apply, ordProj_apply_eq_prod hm hn]
  refine Nat.div_eq_of_eq_mul_right ?_ ?_
  · rw [Nat.pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro q hq
    rw [Finset.mem_inter] at hq
    simp [(Nat.prime_of_mem_primeFactors hq.1).ne_zero]
  · rw [Finset.prod_inter_mul_prod_sdiff, ← Nat.prod_primeFactors_pow_factorization hn]

theorem ordCompl_apply_eq_of_prime (p : ℕ) [Fact p.Prime] :
    p.ordCompl n = n / p ^ n.factorization p := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ordCompl_apply, ordProj_apply_eq_of_prime hn]

end Nat
