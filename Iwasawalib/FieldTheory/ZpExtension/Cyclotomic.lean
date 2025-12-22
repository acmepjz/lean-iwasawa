/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.FieldTheory.ZpExtension.Basic
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

/-!

# Cyclotomic `ℤₚ`-extension

-/

variable (p : ℕ) (K : Type*) [Field K]

/-! ### The field $K(\mu_{p^\infty})$ -/

/-- The field $K(\mu_{p^\infty})$. Internally it is defined to be an
`IntermediateField K (SeparableClosure K)`, but please avoid using it in the public interface.
Instead, use `IsSepClosed.lift` to construct a map of it to `SeparableClosure K`. -/
def CyclotomicPinfField : Type _ :=
  IntermediateField.adjoin K {x : SeparableClosure K | ∃ n : ℕ, x ^ p ^ n = 1}

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

instance isSeparable : Algebra.IsSeparable K (CyclotomicPinfField p K) :=
  inferInstanceAs (Algebra.IsSeparable K (IntermediateField.adjoin K _))

theorem isCyclotomicExtension' [NeZero (p : K)] (s : Set ℕ) (h1 : s ⊆ {0} ∪ Set.range (p ^ ·))
    (h2 : ∀ N, ∃ n ≥ N, p ^ n ∈ s) : IsCyclotomicExtension s K (CyclotomicPinfField p K) where
  exists_isPrimitiveRoot {n} ha ha' := by
    specialize h1 ha
    rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at h1
    obtain ⟨n, rfl⟩ := h1.resolve_left ha'
    obtain ⟨x, hx⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (SeparableClosure K) (p ^ n)
    refine ⟨⟨x, ?_⟩, Subtype.val_injective hx.1, fun l hl ↦ hx.2 l congr($hl.1)⟩
    apply IntermediateField.subset_adjoin
    rw [Set.mem_setOf_eq]
    exact ⟨n, hx.1⟩
  adjoin_roots x := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x]
    apply (IntermediateField.mem_lift x).1
    rw [IntermediateField.lift_adjoin]
    refine (?_ : IntermediateField.adjoin K _ ≤ IntermediateField.adjoin K _) x.2
    rw [IntermediateField.adjoin_le_iff]
    rintro y ⟨N, hN⟩
    change y ∈ IntermediateField.adjoin K _
    obtain ⟨n, hn, hn'⟩ := h2 N
    have hp : 0 < p := Nat.pos_of_ne_zero fun H ↦ by simpa [H] using ‹NeZero (p : K)›.out
    have : NeZero (↑(p ^ (n - N)) : SeparableClosure K) := by
      simpa using (‹NeZero (p : K)›.pow (n := n - N)).of_injective
        (algebraMap K (SeparableClosure K)).injective
    obtain ⟨z, rfl⟩ := IsSepClosed.exists_pow_nat_eq y (p ^ (n - N))
    refine pow_mem (IntermediateField.subset_adjoin _ _ ?_) _
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hn] at hN
    use ⟨z, IntermediateField.subset_adjoin _ _ ⟨n, hN⟩⟩
    exact ⟨⟨_, hn', (Nat.pow_pos hp).ne', Subtype.val_injective hN⟩, rfl⟩

instance isCyclotomicExtension [NeZero (p : K)] :
    IsCyclotomicExtension (Set.range (p ^ ·)) K (CyclotomicPinfField p K) :=
  isCyclotomicExtension' p K _ (by simp) fun N ↦ ⟨N, le_rfl, N, rfl⟩

instance hasEnoughRootsOfUnity [NeZero (p : K)] (i : ℕ) :
    HasEnoughRootsOfUnity (CyclotomicPinfField p K) (p ^ i) :=
  have := (‹NeZero (p : K)›.of_map (algebraMap ℕ K)).pow (n := i)
  ⟨IsCyclotomicExtension.exists_isPrimitiveRoot K _
    (show p ^ i ∈ Set.range (p ^ ·) from ⟨i, rfl⟩) NeZero.out, inferInstance⟩

end CyclotomicPinfField

/-! ### Some complemenatry results on cyclotomic character -/

section CyclotomicCharacter

variable (L : Type*) [Field L] [Algebra K L] [Fact p.Prime]

/-- The restriction of `cyclotomicCharacter` to `L ≃ₐ[K] L` and which is continuous. -/
@[simps toMonoidHom]
noncomputable def continuousCyclotomicCharacter : (L ≃ₐ[K] L) →ₜ* ℤ_[p]ˣ where
  toMonoidHom := (cyclotomicCharacter L p).comp (MulSemiringAction.toRingAut (L ≃ₐ[K] L) L)
  continuous_toFun := cyclotomicCharacter.continuous p K L

@[simp]
theorem continuousCyclotomicCharacter_apply (f : L ≃ₐ[K] L) :
    continuousCyclotomicCharacter p K L f = cyclotomicCharacter L p f := rfl

theorem isClosed_ker_continuousCyclotomicCharacter :
    IsClosed ((continuousCyclotomicCharacter p K L).ker : Set (L ≃ₐ[K] L)) := by
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage (continuousCyclotomicCharacter p K L).continuous

theorem IntermediateField.adjoin_le_fixedField_ker_continuousCyclotomicCharacter
    [∀ i : ℕ, HasEnoughRootsOfUnity L (p ^ i)] :
    adjoin K {x : L | ∃ n : ℕ, x ^ p ^ n = 1} ≤
      fixedField (continuousCyclotomicCharacter p K L).ker := by
  intro x h
  simp only [ContinuousMonoidHom.coe_toMonoidHom, mem_fixedField_iff, MonoidHom.mem_ker,
    MonoidHom.coe_coe, continuousCyclotomicCharacter_apply]
  intro f hf
  induction h using adjoin_induction with
  | mem y hy =>
    obtain ⟨n, hy⟩ := hy
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [pow_zero, pow_one] at hy
      simp [hy]
    have : Fact (1 < p ^ n) := ⟨Nat.one_lt_pow hn ‹Fact p.Prime›.out.one_lt⟩
    simpa [hf, ZMod.val_one] using cyclotomicCharacter.spec p f y hy
  | algebraMap y => simp
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
  | mul x y hx hy ihx ihy => rw [map_mul, ihx, ihy]
  | inv x hx ihx => rw [map_inv₀, ihx]

theorem IntermediateField.adjoin_eq_fixedField_ker_continuousCyclotomicCharacter
    [∀ i : ℕ, HasEnoughRootsOfUnity L (p ^ i)] [IsGalois K L] :
    adjoin K {x : L | ∃ n : ℕ, x ^ p ^ n = 1} =
      fixedField (continuousCyclotomicCharacter p K L).ker := by
  refine (adjoin_le_fixedField_ker_continuousCyclotomicCharacter p K L).antisymm ?_
  rw [← map_le_map_iff InfiniteGalois.IntermediateFieldEquivClosedSubgroup]
  change (adjoin K _).fixingSubgroup ≤ (fixedField _).fixingSubgroup
  rw [show (fixedField (continuousCyclotomicCharacter p K L).ker).fixingSubgroup =
    (continuousCyclotomicCharacter p K L).ker from InfiniteGalois.fixingSubgroup_fixedField
      ⟨_, isClosed_ker_continuousCyclotomicCharacter p K L⟩]
  intro f h
  rw [mem_fixingSubgroup_iff] at h
  rw [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.mem_ker, MonoidHom.coe_coe,
    continuousCyclotomicCharacter_apply, Units.ext_iff, ← PadicInt.ext_of_toZModPow]
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.pow_zero]
    exact Subsingleton.elim _ _
  have : Fact (1 < p ^ n) := ⟨Nat.one_lt_pow hn ‹Fact p.Prime›.out.one_lt⟩
  have : NeZero (p ^ n) := NeZero.mk (zero_lt_one.trans this.out).ne'
  obtain ⟨r, hr⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (p ^ n)
  specialize h r (subset_adjoin _ _ ⟨n, hr.1⟩)
  have := cyclotomicCharacter.spec p f r hr.1
  rw [AlgEquiv.coe_ringEquiv, h] at this
  nth_rw 1 [← pow_one r] at this
  simpa using congr(($(hr.pow_inj (ZMod.val_lt _) Fact.out this.symm) : ZMod (p ^ n)))

theorem continuousCyclotomicCharacter_injective [IsCyclotomicExtension (Set.range (p ^ ·)) K L] :
    Function.Injective (continuousCyclotomicCharacter p K L) := by
  have := IsCyclotomicExtension.isGalois (Set.range (p ^ ·)) K L
  have : ∀ i : ℕ, HasEnoughRootsOfUnity L (p ^ i) := fun i ↦
    ⟨IsCyclotomicExtension.exists_isPrimitiveRoot K _
      (show p ^ i ∈ Set.range (p ^ ·) from ⟨i, rfl⟩) NeZero.out, inferInstance⟩
  apply (MonoidHom.ker_eq_bot_iff (continuousCyclotomicCharacter p K L).toMonoidHom).1
  suffices (⟨_, isClosed_ker_continuousCyclotomicCharacter p K L⟩ : ClosedSubgroup (L ≃ₐ[K] L)) =
    ⟨⊥, isClosed_singleton⟩ from congr($(this).toSubgroup)
  apply_fun _ using InfiniteGalois.IntermediateFieldEquivClosedSubgroup.symm.injective
  change IntermediateField.fixedField (continuousCyclotomicCharacter p K L).ker =
    IntermediateField.fixedField ⊥
  rw [← IntermediateField.adjoin_eq_fixedField_ker_continuousCyclotomicCharacter,
    IntermediateField.fixedField_bot]
  apply_fun _ using IntermediateField.toSubalgebra_injective
  rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x,
    IntermediateField.top_toSubalgebra]
  convert (IsCyclotomicExtension.iff_adjoin_eq_top (Set.range (p ^ ·)) K L).1 ‹_› |>.2 using 2
  simp [‹Fact p.Prime›.out.ne_zero]

end CyclotomicCharacter
