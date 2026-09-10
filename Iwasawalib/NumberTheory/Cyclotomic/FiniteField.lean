/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

/-!

# Cyclotomic extension of finite field

-/

open scoped IntermediateField in
/-- Any nonzero element of an algebraic extension of a finite field `K` is a root of unity
of some order which is nonzero in `K`. -/
private theorem FiniteField.exists_pow_eq_one_aux (K M : Type*) [Field K] [Finite K] [Field M]
    [Algebra K M] [Algebra.IsAlgebraic K M] {x : M} (hx : x ≠ 0) :
    ∃ n : ℕ, (n : K) ≠ 0 ∧ n ≠ 0 ∧ x ^ n = 1 := by
  classical
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hfd : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional hint
  have hfin : Finite K⟮x⟯ := Module.finite_of_finite K
  have := Fintype.ofFinite K⟮x⟯
  set q := Fintype.card K⟮x⟯ with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  refine ⟨q - 1, ?_, by omega, ?_⟩
  · intro h
    have h2 : ((q - 1 : ℕ) : K⟮x⟯) = 0 := by
      rw [show ((q - 1 : ℕ) : K⟮x⟯) = algebraMap K K⟮x⟯ ((q - 1 : ℕ) : K) by push_cast; ring, h,
        map_zero]
    rw [Nat.cast_sub hq1.le, FiniteField.cast_card_eq_zero, Nat.cast_one, zero_sub,
      neg_eq_zero] at h2
    exact one_ne_zero h2
  · have hx' : (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : K⟮x⟯) ≠ 0 := by
      simpa [Subtype.ext_iff] using hx
    exact congrArg Subtype.val (FiniteField.pow_card_sub_one_eq_one _ hx')

theorem FiniteField.isCyclotomicExtension_iff_isAlgClosure (K L : Type*) [Field K] [Field L]
    [Algebra K L] [Finite K] : IsCyclotomicExtension {n | (n : K) ≠ 0} K L ↔ IsAlgClosure K L := by
  constructor
  · intro h
    have hint : Algebra.IsIntegral K L := IsCyclotomicExtension.integral {m | (m : K) ≠ 0} K L
    have halg : Algebra.IsAlgebraic K L := inferInstance
    have hsurj : Function.Surjective (algebraMap L (AlgebraicClosure L)) := by
      intro y
      rcases eq_or_ne y 0 with rfl | hy
      · exact ⟨0, map_zero _⟩
      obtain ⟨n, hn1, hn2, hn3⟩ := FiniteField.exists_pow_eq_one_aux K (AlgebraicClosure L) hy
      have : NeZero n := ⟨hn2⟩
      obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot
        (S := {m : ℕ | (m : K) ≠ 0}) K L hn1 hn2
      have hζ' : IsPrimitiveRoot (algebraMap L (AlgebraicClosure L) ζ) n :=
        hζ.map_of_injective (algebraMap L (AlgebraicClosure L)).injective
      obtain ⟨k, -, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hn3
      exact ⟨ζ ^ k, by rw [map_pow]⟩
    have e : AlgebraicClosure L ≃+* L :=
      (RingEquiv.ofBijective (algebraMap L (AlgebraicClosure L))
        ⟨(algebraMap L (AlgebraicClosure L)).injective, hsurj⟩).symm
    exact ⟨IsAlgClosed.of_ringEquiv (AlgebraicClosure L) L e, halg⟩
  · intro h
    have := h.isAlgClosed
    have halg : Algebra.IsAlgebraic K L := h.isAlgebraic
    refine ⟨fun {n} hn hn0 ↦ ?_, fun x ↦ ?_⟩
    · have : NeZero ((n : ℕ) : L) := by
        refine ⟨?_⟩
        rw [show ((n : ℕ) : L) = algebraMap K L ((n : ℕ) : K) by push_cast; ring]
        exact fun hc ↦ hn ((map_eq_zero (algebraMap K L)).1 hc)
      have := IsSepClosed.isCyclotomicExtension {n} L
        (fun a ha _ ↦ Set.mem_singleton_iff.mp ha ▸ ‹NeZero ((n : ℕ) : L)›)
      exact IsCyclotomicExtension.exists_isPrimitiveRoot (S := {n}) L L rfl hn0
    · rcases eq_or_ne x 0 with rfl | hx
      · exact zero_mem _
      obtain ⟨n, hn1, hn2, hn3⟩ := FiniteField.exists_pow_eq_one_aux K L hx
      exact Algebra.subset_adjoin ⟨n, hn1, hn2, hn3⟩
