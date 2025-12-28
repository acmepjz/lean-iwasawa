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

universe u

variable (p : ℕ) (K : Type u) (Kinf Kinf' : Type*) [Field K]
  [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]
  [Field Kinf'] [Algebra K Kinf'] [IsGalois K Kinf']

/-! ### The assertion that a field extension is a cyclotomic $p^∞$-extension -/

/-- `IsCyclotomicPinfExtension p A B` is the assertion that `B / A` is a cyclotomic
$p^∞$-extension. See `IsCyclotomicExtension` for more details. -/
abbrev IsCyclotomicPinfExtension (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :=
  IsCyclotomicExtension (Set.range (p ^ ·)) A B

namespace IsCyclotomicPinfExtension

theorem equiv (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] {C : Type*} [CommRing C]
    [Algebra A C] [IsCyclotomicPinfExtension p A B] (f : B ≃ₐ[A] C) :
    IsCyclotomicPinfExtension p A C := IsCyclotomicExtension.equiv _ A B f

end IsCyclotomicPinfExtension

/-! ### The field $K(μ_{p^∞})$ -/

/-- The field $K(μ_{p^∞})$ inside the separable closure of `K`. Internally it is defined to be an
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

theorem isCyclotomicExtension [NeZero (p : K)] (s : Set ℕ) (h1 : s ⊆ {0} ∪ Set.range (p ^ ·))
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

instance isCyclotomicPinfExtension [NeZero (p : K)] :
    IsCyclotomicPinfExtension p K (CyclotomicPinfField p K) :=
  isCyclotomicExtension p K _ (by simp) fun N ↦ ⟨N, le_rfl, N, rfl⟩

instance hasEnoughRootsOfUnity [NeZero (p : K)] (i : ℕ) :
    HasEnoughRootsOfUnity (CyclotomicPinfField p K) (p ^ i) :=
  have := (‹NeZero (p : K)›.of_map (algebraMap ℕ K)).pow (n := i)
  ⟨IsCyclotomicExtension.exists_isPrimitiveRoot K _
    (show p ^ i ∈ Set.range (p ^ ·) from ⟨i, rfl⟩) NeZero.out, inferInstance⟩

theorem nonempty_algEquiv_prime_pow_mul (q k : ℕ) [ExpChar K q] :
    Nonempty (CyclotomicPinfField (q ^ k * p) K ≃ₐ[K] CyclotomicPinfField p K) := by
  refine ⟨IntermediateField.equivOfEq ?_⟩
  simp_rw [mul_pow, ← pow_mul q k, ExpChar.pow_prime_pow_mul_eq_one_iff]

instance isAbelianGalois [NeZero p] : IsAbelianGalois K (CyclotomicPinfField p K) := by
  obtain ⟨q, _ | hq⟩ := ExpChar.exists K
  · exact (isCyclotomicPinfExtension p K).isAbelianGalois ..
  have := Fact.mk hq
  obtain ⟨r, h1, h2⟩ :=
    (Nat.finiteMultiplicity_iff.2 ⟨hq.ne_one, Nat.pos_of_neZero p⟩).exists_eq_pow_mul_and_not_dvd
  rw [h1]
  refine @IsAbelianGalois.of_algHom _ _ _ _ _ _ _ _
    (nonempty_algEquiv_prime_pow_mul r K q (multiplicity q p)).some.toAlgHom ?_
  rw [← CharP.cast_eq_zero_iff K] at h2
  have := NeZero.mk h2
  exact (isCyclotomicPinfExtension r K).isAbelianGalois ..

/-- The intermediate field of $K(μ_{p^∞}) / K$ fixed by the torsion subgroup of the Galois group
of $K(μ_{p^∞}) / K$. -/
noncomputable def cyclotomicZpSubfield : IntermediateField K (CyclotomicPinfField p K) :=
  if h : p ≠ 0 then haveI := NeZero.mk h; .fixedField (CommGroup.torsion _) else ⊥

theorem cyclotomicZpSubfield_eq_fixedField [NeZero p] :
    cyclotomicZpSubfield p K = .fixedField (CommGroup.torsion _) := by
  rw [cyclotomicZpSubfield, dif_pos NeZero.out]

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

theorem continuousCyclotomicCharacter_injective [IsCyclotomicPinfExtension p K L] :
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

/-! ### The assertion that a field extension is a cyclotomic `ℤₚ`-extension -/

/-- `K∞ / K` is a cyclotomic `ℤₚ`-extension, if it is a `ℤₚ`-extension, and `K∞` can be realized as
an intermediate field of $K(μ_{p^∞}) / K$. -/
@[mk_iff]
structure IsCyclotomicZpExtension [Fact p.Prime] : Prop where
  isZpExtension : IsMvZpExtension p 1 K Kinf
  nonempty_algHom_cyclotomicPinfField : Nonempty (Kinf →ₐ[K] CyclotomicPinfField p K)

namespace IsCyclotomicZpExtension

variable {p K Kinf Kinf'} [Fact p.Prime] (H : IsCyclotomicZpExtension p K Kinf)
include H

theorem congr (f : Kinf ≃ₐ[K] Kinf') : IsCyclotomicZpExtension p K Kinf' where
  isZpExtension := H.1.congr _ f
  nonempty_algHom_cyclotomicPinfField := ⟨H.2.some.comp f.symm⟩

theorem infinite_dimensional : ¬FiniteDimensional K Kinf := H.1.infinite_dimensional

theorem infinite_dimensional_cyclotomicPinfField :
    ¬FiniteDimensional K (CyclotomicPinfField p K) := fun _ ↦
  H.infinite_dimensional (AlgEquiv.ofInjectiveField H.2.some).toLinearEquiv.symm.finiteDimensional

theorem neZero : NeZero (p : K) := by
  refine ⟨fun hp ↦ H.infinite_dimensional_cyclotomicPinfField ?_⟩
  rw [← CharP.charP_iff_prime_eq_zero Fact.out] at hp
  have := CyclotomicPinfField.nonempty_algEquiv_prime_pow_mul 1 K p 1
  rw [pow_one, mul_one] at this
  obtain ⟨i⟩ := this
  refine @LinearEquiv.finiteDimensional _ _ _ _ _ _ _ _ i.toLinearEquiv.symm ?_
  unfold CyclotomicPinfField
  suffices IntermediateField.adjoin K {x : SeparableClosure K | ∃ n : ℕ, x ^ 1 ^ n = 1} = ⊥ by
    have h : FiniteDimensional K (⊥ : IntermediateField K (SeparableClosure K)) := inferInstance
    rwa [← this] at h
  simp

/-- A random map from `K∞` to $K(μ_{p^∞})$. -/
noncomputable def algHomCyclotomicPinfField := H.2.some

theorem fieldRange_eq_cyclotomicZpSubfield (f : Kinf →ₐ[K] CyclotomicPinfField p K) :
    f.fieldRange = CyclotomicPinfField.cyclotomicZpSubfield p K := by
  sorry

theorem unique (H' : IsCyclotomicZpExtension p K Kinf') : Nonempty (Kinf ≃ₐ[K] Kinf') := by
  have h := H.fieldRange_eq_cyclotomicZpSubfield H.2.some
  rw [← H'.fieldRange_eq_cyclotomicZpSubfield H'.2.some] at h
  exact ⟨(AlgEquiv.ofInjectiveField H.2.some).trans (IntermediateField.equivOfEq h) |>.trans
    (AlgEquiv.ofInjectiveField H'.2.some).symm⟩

end IsCyclotomicZpExtension

-- theorem CyclotomicPinfField.isZpExtension_cyclotomicZpSubfield
--     [Fact p.Prime] [NeZero (p : K)] :
--     IsMvZpExtension p 1 K (CyclotomicPinfField.cyclotomicZpSubfield p K) := by
--   sorry

-- theorem CyclotomicPinfField.isCyclotomicZpExtension_cyclotomicZpSubfield
--     [Fact p.Prime] [NeZero (p : K)] :
--     IsCyclotomicZpExtension p K (CyclotomicPinfField.cyclotomicZpSubfield p K) where
--   isZpExtension := isZpExtension_cyclotomicZpSubfield p K
--   nonempty_algHom_cyclotomicPinfField := ⟨IntermediateField.val _⟩

-- variable {p K Kinf} in
-- theorem isCyclotomicZpExtension_iff_exists_fieldRange_eq_cyclotomicZpSubfield [Fact p.Prime] :
--     IsCyclotomicZpExtension p K Kinf ↔ (p : K) ≠ 0 ∧
--     ∃ (f : Kinf →ₐ[K] CyclotomicPinfField p K),
--     f.fieldRange = CyclotomicPinfField.cyclotomicZpSubfield p K := by
--   refine ⟨fun H ↦ ⟨H.neZero.out, H.2.some, H.fieldRange_eq_cyclotomicZpSubfield _⟩,
--     fun ⟨hp, f, hf⟩ ↦ ?_⟩
--   have := NeZero.mk hp
--   have := CyclotomicPinfField.isCyclotomicZpExtension_cyclotomicZpSubfield p K
--   rw [← hf] at this
--   exact this.congr (AlgEquiv.ofInjectiveField f).symm

/-! ### The assertion that a field have a cyclotomic `ℤₚ`-extension -/

/-- `HasCyclotomicZpExtension p K` is the assertion that the field `K` have a
cyclotomic `ℤₚ`-extension. -/
@[mk_iff]
class HasCyclotomicZpExtension [Fact p.Prime] : Prop where
  exists_isCyclotomicZpExtension :
    ∃ (Kinf : Type u) (_ : Field Kinf) (_ : Algebra K Kinf) (_ : IsGalois K Kinf),
    IsCyclotomicZpExtension p K Kinf

/-- `K` have a cyclotomic `ℤₚ`-extension if and only if $K(μ_{p^∞}) / K$
is an infinite extension. -/
theorem hasCyclotomicZpExtension_iff_infinite_dimensional [Fact p.Prime] :
    HasCyclotomicZpExtension p K ↔ ¬FiniteDimensional K (CyclotomicPinfField p K) := by
  sorry

variable {p K Kinf} in
theorem IsCyclotomicZpExtension.hasCyclotomicZpExtension [Fact p.Prime]
    (H : IsCyclotomicZpExtension p K Kinf) : HasCyclotomicZpExtension p K := by
  rw [hasCyclotomicZpExtension_iff_infinite_dimensional]
  sorry
