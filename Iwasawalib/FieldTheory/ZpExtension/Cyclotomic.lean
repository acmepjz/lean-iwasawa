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

/-! ### Preliminariy results on `HasEnoughRootsOfUnity` should go to mathlib -/

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

/-! ### Preliminariy results on `IsCyclotomicExtension` should go to mathlib -/

namespace IsCyclotomicExtension

variable (S : Set ℕ) (A B : Type*) [Field A] [Field B] [Algebra A B] [IsCyclotomicExtension S A B]

include S A B

theorem natCast_ne_zero (n : ℕ) (hn : n ∈ S) (hneq : n ≠ 0) : (n : A) ≠ 0 := by
  intro heq
  obtain ⟨p, _ | ⟨hp, _⟩⟩ := ExpChar.exists A
  · rw [Nat.cast_eq_zero] at heq
    contradiction
  have := hp.two_le
  replace hp := Fact.mk hp
  obtain ⟨x, hx1, hx2⟩ := exists_isPrimitiveRoot A B hn hneq
  have := charP_of_injective_algebraMap (algebraMap A B).injective p
  obtain ⟨n, rfl⟩ := (CharP.cast_eq_zero_iff A p n).1 heq
  replace hneq := Nat.pos_of_ne_zero (mul_ne_zero_iff.1 hneq).2
  rw [mul_comm, pow_mul, ← frobenius_def p, ← map_one (frobenius B p)] at hx1
  replace hx2 := Nat.le_of_dvd hneq (hx2 _ (frobenius_inj B p hx1))
  nth_rw 2 [← one_mul n] at hx2
  rw [Nat.mul_le_mul_right_iff hneq] at hx2
  linarith

theorem isSeparable : Algebra.IsSeparable A B := by
  have h := (IsCyclotomicExtension.iff_adjoin_eq_top S A B).1 ‹_› |>.2
  have key : ∀ b ∈ {b : B | ∃ n ∈ S, n ≠ 0 ∧ b ^ n = 1}, IsSeparable A b := fun b hb ↦ by
    obtain ⟨n, hn, h1, h2⟩ := hb
    have := Polynomial.X_pow_sub_one_separable_iff.2 (natCast_ne_zero S A B n hn h1)
    exact this.of_dvd <| minpoly.dvd A b <| by simp [h2]
  rw [← IntermediateField.adjoin_algebraic_toSubalgebra
    fun b hb ↦ (key b hb).isIntegral.isAlgebraic, ← IntermediateField.top_toSubalgebra] at h
  rwa [← AlgEquiv.Algebra.isSeparable_iff <|
    (IntermediateField.equivOfEq (IntermediateField.toSubalgebra_injective h)).trans
      IntermediateField.topEquiv, IntermediateField.isSeparable_adjoin_iff_isSeparable]

theorem nonempty_algEquiv_adjoin (L : Type*) [Field L] [Algebra A L] [IsSepClosed L] :
    Nonempty (B ≃ₐ[A] IntermediateField.adjoin A {x : L | ∃ n ∈ S, n ≠ 0 ∧ x ^ n = 1}) := by
  have := isSeparable S A B
  let i : B →ₐ[A] L := IsSepClosed.lift
  refine ⟨(show B ≃ₐ[A] i.fieldRange from AlgEquiv.ofInjectiveField i).trans
    (IntermediateField.equivOfEq (le_antisymm ?_ ?_))⟩
  · rintro x (hx : x ∈ i.range)
    let e := Subalgebra.equivOfEq _ _ ((IsCyclotomicExtension.iff_adjoin_eq_top S A B).1 ‹_›).2
      |>.trans Subalgebra.topEquiv
    have hrange : i.range = (i.comp (AlgHomClass.toAlgHom e)).range := by
      ext x
      simp only [AlgHom.mem_range, AlgHom.coe_comp, AlgHom.coe_coe, Function.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨e.symm y, by simp⟩
      · rintro ⟨y, rfl⟩; exact ⟨e y, rfl⟩
    rw [hrange, AlgHom.mem_range] at hx
    obtain ⟨⟨y, hy⟩, rfl⟩ := hx
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨n, hn, h1, h2⟩ := hx
      apply IntermediateField.subset_adjoin
      use n, hn, h1
      rw [← map_pow, ← map_one (i.comp (AlgHomClass.toAlgHom e))]
      congr 1
      apply_fun _ using Subtype.val_injective
      simpa
    | algebraMap x =>
      convert IntermediateField.algebraMap_mem _ x
      exact AlgHom.commutes _ x
    | add x y hx hy ihx ihy =>
      convert add_mem ihx ihy
      exact map_add (i.comp (AlgHomClass.toAlgHom e)) ⟨x, hx⟩ ⟨y, hy⟩
    | mul x y hx hy ihx ihy =>
      convert mul_mem ihx ihy
      exact map_mul (i.comp (AlgHomClass.toAlgHom e)) ⟨x, hx⟩ ⟨y, hy⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro x ⟨n, hn, h1, h2⟩
    have := NeZero.mk h1
    obtain ⟨y, hy⟩ := exists_isPrimitiveRoot A B hn h1
    obtain ⟨m, -, rfl⟩ := (hy.map_of_injective (f := i) i.injective).eq_pow_of_pow_eq_one h2
    exact ⟨y ^ m, by simp⟩

theorem isGalois!!! : IsGalois A B := by
  rw [isGalois_iff]
  use isSeparable S A B
  obtain ⟨i⟩ := nonempty_algEquiv_adjoin S A B (AlgebraicClosure A)
  rw [i.transfer_normal, IntermediateField.normal_iff_forall_map_le]
  intro f x hx
  change x ∈ IntermediateField.toSubalgebra _ at hx
  rw [IntermediateField.toSubalgebra_map, Subalgebra.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  change y ∈ IntermediateField.adjoin _ _ at hy
  induction hy using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨n, hn, h1, h2⟩ := hx
    apply IntermediateField.subset_adjoin
    use n, hn, h1
    rw [← map_pow, ← map_one f, h2]
  | algebraMap x =>
    convert IntermediateField.algebraMap_mem _ x
    exact AlgHom.commutes _ x
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    rw [map_mul]
    exact mul_mem ihx ihy
  | inv x hx ihx =>
    rw [map_inv₀]
    exact inv_mem ihx

end IsCyclotomicExtension

theorem FiniteField.isCyclotomicExtension_iff_isAlgClosure (K L : Type*) [Field K] [Field L]
    [Algebra K L] [Finite K] : IsCyclotomicExtension {n | (n : K) ≠ 0} K L ↔ IsAlgClosure K L := by
  -- unused so just leave it as sorry
  sorry

/-! ### The field $K(\mu_{p^\infty})$ -/

/-- The field $K(\mu_{p^\infty})$. Internally it is defined to be an
`IntermediateField K (AlgebraicClosure K)`, but please avoid using it in the public interface.
Instead, use `IsAlgClosed.lift` to construct a map of it to `AlgebraicClosure K`. -/
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

end CyclotomicPinfField
