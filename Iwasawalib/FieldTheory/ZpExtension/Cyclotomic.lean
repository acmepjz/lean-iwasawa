/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Iwasawalib.FieldTheory.ZpExtension.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!

# Cyclotomic `ℤₚ`-extension

-/

variable (p : ℕ) (K : Type*) [Field K]

instance IsAlgClosed.hasEnoughRootsOfUnity_pow [IsAlgClosed K] [NeZero (p : K)] (n : ℕ) :
    HasEnoughRootsOfUnity K (p ^ n) :=
  have : NeZero ((p ^ n : ℕ) : K) := by exact_mod_cast ‹NeZero (p : K)›.pow (n := n)
  inferInstance

namespace AlgebraicClosure

instance hasEnoughRootsOfUnity [NeZero (p : K)] : HasEnoughRootsOfUnity (AlgebraicClosure K) p :=
  have : NeZero (p : AlgebraicClosure K) :=
    ‹NeZero (p : K)›.of_injective (algebraMap K (AlgebraicClosure K)).injective
  inferInstance

instance hasEnoughRootsOfUnity_pow [NeZero (p : K)] (n : ℕ) :
    HasEnoughRootsOfUnity (AlgebraicClosure K) (p ^ n) :=
  have : NeZero (p : AlgebraicClosure K) :=
    ‹NeZero (p : K)›.of_injective (algebraMap K (AlgebraicClosure K)).injective
  inferInstance

end AlgebraicClosure

namespace IsCyclotomicExtension

variable (S : Set ℕ) (A B : Type*) [Field A] [Field B] [Algebra A B] [IsCyclotomicExtension S A B]

theorem natCast_ne_zero (n : ℕ) (hn : n ∈ S) (hneq : n ≠ 0) : (n : A) ≠ 0 := by
  intro heq
  obtain ⟨p, _⟩ := CharP.exists A
  sorry

theorem isSeparable : Algebra.IsSeparable A B := by
  sorry

end IsCyclotomicExtension

theorem FiniteField.isCyclotomicExtension_iff_isAlgClosure (K L : Type*) [Field K] [Field L]
    [Algebra K L] [Finite K] : IsCyclotomicExtension {n | (n : K) ≠ 0} K L ↔ IsAlgClosure K L := by
  -- unused so just leave it as sorry
  sorry

/-- The field $K(\mu_{p^\infty})$. -/
def CyclotomicPinfField : Type _ :=
  IntermediateField.adjoin K {x : AlgebraicClosure K | ∃ n : ℕ, x ^ p ^ n = 1}

namespace CyclotomicPinfField

noncomputable instance instField : Field (CyclotomicPinfField p K) :=
  inferInstanceAs (Field (IntermediateField.adjoin K _))

noncomputable instance algebra : Algebra K (CyclotomicPinfField p K) :=
  inferInstanceAs (Algebra K (IntermediateField.adjoin K _))

noncomputable instance instInhabited : Inhabited (CyclotomicPinfField p K) := ⟨0⟩

instance instCharZero [CharZero K] : CharZero (CyclotomicPinfField p K) :=
  charZero_of_injective_algebraMap (algebraMap K _).injective

instance instCharP (p' : ℕ) [CharP K p'] : CharP (CyclotomicPinfField p K) p' :=
  charP_of_injective_algebraMap (algebraMap K _).injective p'

instance instExpChar (p' : ℕ) [ExpChar K p'] : ExpChar (CyclotomicPinfField p K) p' :=
  expChar_of_injective_algebraMap (algebraMap K _).injective p'

noncomputable instance algebra' (R : Type*) [CommRing R] [Algebra R K] :
    Algebra R (CyclotomicPinfField p K) :=
  inferInstanceAs (Algebra R (IntermediateField.adjoin K _))

instance instIsScalarTower (R : Type*) [CommRing R] [Algebra R K] :
    IsScalarTower R K (CyclotomicPinfField p K) :=
  inferInstanceAs (IsScalarTower R K (IntermediateField.adjoin K _))

instance instNoZeroSMulDivisors (R : Type*) [CommRing R] [Algebra R K] [IsFractionRing R K] :
    NoZeroSMulDivisors R (CyclotomicPinfField p K) := by
  rw [NoZeroSMulDivisors.iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective,
    IsScalarTower.algebraMap_eq R K (CyclotomicPinfField p K)]
  exact
    (Function.Injective.comp (FaithfulSMul.algebraMap_injective K (CyclotomicPinfField p K))
      (IsFractionRing.injective R K) :)

instance isAlgebraic : Algebra.IsAlgebraic K (CyclotomicPinfField p K) :=
  inferInstanceAs (Algebra.IsAlgebraic K (IntermediateField.adjoin K _))

theorem isCyclotomicExtension' [NeZero (p : K)] (s : Set ℕ) (h1 : s ⊆ {0} ∪ Set.range (p ^ ·))
    (h2 : ∀ N, ∃ n ≥ N, p ^ n ∈ s) : IsCyclotomicExtension s K (CyclotomicPinfField p K) where
  exists_isPrimitiveRoot {n} ha ha' := by
    specialize h1 ha
    rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at h1
    obtain ⟨n, rfl⟩ := h1.resolve_left ha'
    obtain ⟨x, hx⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) (p ^ n)
    refine ⟨⟨x, ?_⟩, Subtype.val_injective hx.1, fun l hl ↦ hx.2 l congr($hl.1)⟩
    apply IntermediateField.subset_adjoin
    rw [Set.mem_setOf_eq]
    exact ⟨n, hx.1⟩
  adjoin_roots x := by
    rw [← IntermediateField.adjoin_algebraic_toSubalgebra
      (fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x)]
    apply (IntermediateField.mem_lift x).1
    rw [IntermediateField.lift_adjoin]
    refine (?_ : IntermediateField.adjoin K _ ≤ IntermediateField.adjoin K _) x.2
    rw [IntermediateField.adjoin_le_iff]
    rintro y ⟨N, hN⟩
    change y ∈ IntermediateField.adjoin K _
    obtain ⟨n, hn, hn'⟩ := h2 N
    have hp : 0 < p := Nat.pos_of_ne_zero fun H ↦ by simpa [H] using ‹NeZero (p : K)›.out
    obtain ⟨z, rfl⟩ := IsAlgClosed.exists_pow_nat_eq y (Nat.pow_pos hp (n := n - N))
    refine pow_mem (IntermediateField.subset_adjoin _ _ ?_) _
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hn] at hN
    use ⟨z, IntermediateField.subset_adjoin _ _ ⟨n, hN⟩⟩
    exact ⟨⟨_, hn', (Nat.pow_pos hp).ne', Subtype.val_injective hN⟩, rfl⟩

instance isCyclotomicExtension [NeZero (p : K)] :
    IsCyclotomicExtension (Set.range (p ^ ·)) K (CyclotomicPinfField p K) :=
  isCyclotomicExtension' p K _ (by simp) fun N ↦ ⟨N, le_rfl, N, rfl⟩

noncomputable instance instAlgebraAlgebraicClosure :
    Algebra (CyclotomicPinfField p K) (AlgebraicClosure K) :=
  inferInstanceAs (Algebra (IntermediateField.adjoin K _) (AlgebraicClosure K))

instance instIsScalarTowerAlgebraicClosure :
    IsScalarTower K (CyclotomicPinfField p K) (AlgebraicClosure K) :=
  inferInstanceAs (IsScalarTower K (IntermediateField.adjoin K _) (AlgebraicClosure K))

end CyclotomicPinfField
