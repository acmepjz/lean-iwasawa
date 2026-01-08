/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Iwasawalib.FieldTheory.ZpExtension.Basic
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.Cyclotomic.Gal
-- public import Mathlib.NumberTheory.LocalField.Basic
public import Iwasawalib.NumberTheory.Padics.Units
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
of $K(μ_{p^∞}) / K$. `CyclotomicPinfField.isCyclotomicZpExtension_cyclotomicZpSubfield` shows that,
if $K(μ_{p^∞}) / K$ is an infinite extension,
then this field over `K` is a cyclotomic `ℤₚ`-extension. -/
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

theorem IsCyclotomicPinfExtension.finite_torsion_gal [IsCyclotomicPinfExtension p K L] :
    haveI := IsCyclotomicExtension.isAbelianGalois (Set.range (p ^ ·)) K L
    Finite (CommGroup.torsion Gal(L/K)) := by
  have := IsCyclotomicExtension.isAbelianGalois (Set.range (p ^ ·)) K L
  refine Set.Finite.subset ?_ <| CommGroup.torsion_le_comap_torsion <| MonoidHomClass.toMonoidHom
    <| continuousCyclotomicCharacter p K L
  refine Set.Finite.preimage (s := (CommGroup.torsion ℤ_[p]ˣ : Set ℤ_[p]ˣ))
    (continuousCyclotomicCharacter_injective p K L).injOn ?_
  rw [← PadicInt.torsionUnits_eq_torsion]
  exact PadicInt.finite_torsionUnits p

/-- The torsion subgroup of the Galois group of $K(μ_{p^∞}) / K$, which is a closed subgroup. -/
@[simps toSubgroup]
noncomputable def CyclotomicPinfField.torsionGal [NeZero (p : K)] :
    ClosedSubgroup Gal(CyclotomicPinfField p K/K) where
  toSubgroup := CommGroup.torsion Gal(CyclotomicPinfField p K/K)
  isClosed' := Set.Finite.isClosed
    (IsCyclotomicPinfExtension.finite_torsion_gal p K (CyclotomicPinfField p K))

theorem CyclotomicPinfField.fixingSubgroup_cyclotomicZpSubfield [NeZero (p : K)] :
    (cyclotomicZpSubfield p K).fixingSubgroup = CommGroup.torsion _ := by
  simpa only [cyclotomicZpSubfield_eq_fixedField] using
    InfiniteGalois.fixingSubgroup_fixedField (torsionGal p K)

instance CyclotomicPinfField.finite_torsionGal [NeZero (p : K)] : Finite (torsionGal p K) :=
  IsCyclotomicPinfExtension.finite_torsion_gal p K (CyclotomicPinfField p K)

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
  have := H.neZero
  replace H : IsCyclotomicZpExtension p K f.fieldRange := H.congr (AlgEquiv.ofInjectiveField f)
  suffices f.fieldRange.fixingSubgroup = CommGroup.torsion _ by
    simpa only [InfiniteGalois.fixedField_fixingSubgroup,
      CyclotomicPinfField.cyclotomicZpSubfield_eq_fixedField] using
        congr(IntermediateField.fixedField $(this))
  have hfin : Finite f.fieldRange.fixingSubgroup := by
    have hc : IsClosed ((f.fieldRange.fixingSubgroup.map <| MonoidHomClass.toMonoidHom <|
        continuousCyclotomicCharacter p K (CyclotomicPinfField p K)) : Set ℤ_[p]ˣ) :=
      (InfiniteGalois.fixingSubgroup_isClosed f.fieldRange).isCompact.image
        (continuousCyclotomicCharacter p K (CyclotomicPinfField p K)).continuous |>.isClosed
    rcases PadicInt.finite_or_finiteIndex_of_subgroup_units_of_isClosed p _ hc with ⟨h, -⟩ | ⟨-, h⟩
    · exact h.of_finite_image
        (continuousCyclotomicCharacter_injective p K (CyclotomicPinfField p K)).injOn
    suffices IsOpen (f.fieldRange.fixingSubgroup : Set Gal(CyclotomicPinfField p K/K)) from
      H.isZpExtension.infinite_dimensional ((InfiniteGalois.isOpen_iff_finite _).1 this) |>.elim
    simpa [(continuousCyclotomicCharacter_injective p K (CyclotomicPinfField p K)).preimage_image]
      using h.preimage (continuousCyclotomicCharacter p K (CyclotomicPinfField p K)).continuous
  refine le_antisymm (fun g hg ↦ ?_) (fun g hg ↦ ?_)
  · rw [CommGroup.mem_torsion, ← finite_zpowers]
    exact Set.Finite.subset hfin (Subgroup.zpowers_le_of_mem hg)
  suffices CommGroup.torsion Gal(f.fieldRange/K) = ⊥ by
    rw [CommGroup.mem_torsion] at hg
    replace hg := (AlgEquiv.restrictNormalHom f.fieldRange).isOfFinOrder hg
    rwa [← CommGroup.mem_torsion, this, Subgroup.mem_bot, ← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker] at hg
  suffices ht : AddCommGroup.torsion ℤ_[p] = ⊥ from eq_bot_iff.2 fun x hx ↦ by
    let i := H.isZpExtension.continuousMulEquiv₁
    rw [CommGroup.mem_torsion] at hx
    replace hx : IsOfFinAddOrder (i x).toAdd := i.toMonoidHom.isOfFinOrder hx
    rw [← AddCommGroup.mem_torsion, ht, AddSubgroup.mem_bot] at hx
    simpa using congr(i.symm $(show i x = 1 from hx))
  refine eq_bot_iff.2 fun x hx ↦ ?_
  rw [AddCommGroup.mem_torsion, isOfFinAddOrder_iff_nsmul_eq_zero] at hx
  obtain ⟨n, h1, h2⟩ := hx
  simpa [h1.ne'] using h2

theorem isCyclotomicZpExtension_cyclotomicZpSubfield :
    IsCyclotomicZpExtension p K (CyclotomicPinfField.cyclotomicZpSubfield p K) :=
  H.congr <| (AlgEquiv.ofInjectiveField H.2.some).trans <| IntermediateField.equivOfEq <|
    H.fieldRange_eq_cyclotomicZpSubfield H.2.some

theorem unique (H' : IsCyclotomicZpExtension p K Kinf') : Nonempty (Kinf ≃ₐ[K] Kinf') := by
  have h := H.fieldRange_eq_cyclotomicZpSubfield H.2.some
  rw [← H'.fieldRange_eq_cyclotomicZpSubfield H'.2.some] at h
  exact ⟨(AlgEquiv.ofInjectiveField H.2.some).trans (IntermediateField.equivOfEq h) |>.trans
    (AlgEquiv.ofInjectiveField H'.2.some).symm⟩

end IsCyclotomicZpExtension

/-- If `H` is a closed normal subgroup of `Gal(K / k)`,
then `Gal(fixedField H / k)` is isomorphic to `Gal(K / k) ⧸ H` as a topological group.

TODO: should go to mathlib -/
@[simps! toMulEquiv]
noncomputable def InfiniteGalois.normalAutContinuousEquivQuotient {k K : Type*} [Field k] [Field K]
    [Algebra k K] [IsGalois k K]  (H : ClosedSubgroup Gal(K/k)) [H.Normal] :
    Gal(K/k) ⧸ H.1 ≃ₜ* Gal(IntermediateField.fixedField H.1/k) :=
  letI f : Gal(K/k) ⧸ H.1 ≃* Gal(IntermediateField.fixedField H.1/k) := normalAutEquivQuotient H
  haveI hc : Continuous f := by simpa only [(QuotientGroup.isQuotientMap_mk H.1).continuous_iff]
    using InfiniteGalois.restrictNormalHom_continuous (IntermediateField.fixedField H.1)
  letI f1 : Gal(K/k) ⧸ H.1 ≃ₜ Gal(IntermediateField.fixedField H.1/k) :=
    hc.homeoOfEquivCompactToT2 (f := f)
  { f, f1 with }

/-- If $K(μ_{p^∞}) / K$ is an infinite extension, then $K(μ_{p^∞})^Δ / K$ is a cyclotomic
`ℤₚ`-extension, where `Δ` is the torsion subgroup of the Galois group of $K(μ_{p^∞}) / K$. -/
theorem CyclotomicPinfField.isCyclotomicZpExtension_cyclotomicZpSubfield
    [Fact p.Prime] [NeZero (p : K)] (H : ¬FiniteDimensional K (CyclotomicPinfField p K)) :
    IsCyclotomicZpExtension p K (cyclotomicZpSubfield p K) := by
  refine ⟨?_, ⟨IntermediateField.val _⟩⟩
  rw [isMvZpExtension₁_iff]
  have h : Nonempty _ := ⟨InfiniteGalois.normalAutContinuousEquivQuotient (torsionGal p K)⟩
  simp only [torsionGal_toSubgroup] at h
  rw [← cyclotomicZpSubfield_eq_fixedField] at h
  obtain ⟨f⟩ := h
  have : Infinite Gal(CyclotomicPinfField p K/K) := by
    contrapose! H
    exact IsGalois.finiteDimensional_of_finite ..
  obtain ⟨g⟩ := PadicInt.nonempty_continuousMulEquiv_of_continuousMonoidHom_units_of_injective p
    Gal(CyclotomicPinfField p K/K) _ (continuousCyclotomicCharacter_injective ..)
  exact ⟨f.symm.trans g⟩

theorem isCyclotomicZpExtension_iff_exists_fieldRange_eq_cyclotomicZpSubfield [Fact p.Prime] :
    IsCyclotomicZpExtension p K Kinf ↔
      (p : K) ≠ 0 ∧ ¬FiniteDimensional K (CyclotomicPinfField p K) ∧
      ∃ (f : Kinf →ₐ[K] CyclotomicPinfField p K),
        f.fieldRange = CyclotomicPinfField.cyclotomicZpSubfield p K := by
  refine ⟨fun H ↦ ⟨H.neZero.out, H.infinite_dimensional_cyclotomicPinfField, H.2.some,
    H.fieldRange_eq_cyclotomicZpSubfield _⟩, fun ⟨hp, hinf, f, hf⟩ ↦ ?_⟩
  have := NeZero.mk hp
  have := CyclotomicPinfField.isCyclotomicZpExtension_cyclotomicZpSubfield p K hinf
  rw [← hf] at this
  exact this.congr (AlgEquiv.ofInjectiveField f).symm

/-! ### The assertion that a field have a cyclotomic `ℤₚ`-extension -/

/-- `HasCyclotomicZpExtension p K` is the assertion that the field `K` have a
cyclotomic `ℤₚ`-extension. -/
@[mk_iff]
class HasCyclotomicZpExtension [Fact p.Prime] : Prop where
  exists_isCyclotomicZpExtension :
    ∃ (Kinf : Type u) (_ : Field Kinf) (_ : Algebra K Kinf) (_ : IsGalois K Kinf),
    IsCyclotomicZpExtension p K Kinf

theorem hasCyclotomicZpExtension_iff_isCyclotomicZpExtension_cyclotomicZpSubfield [Fact p.Prime] :
    HasCyclotomicZpExtension p K ↔
      IsCyclotomicZpExtension p K (CyclotomicPinfField.cyclotomicZpSubfield p K) :=
  ⟨fun ⟨_, _, _, _, H⟩ ↦ H.isCyclotomicZpExtension_cyclotomicZpSubfield, fun H ↦ ⟨_, _, _, _, H⟩⟩

variable {p K Kinf} in
theorem IsCyclotomicZpExtension.hasCyclotomicZpExtension
    [Fact p.Prime] (H : IsCyclotomicZpExtension p K Kinf) : HasCyclotomicZpExtension p K :=
  (hasCyclotomicZpExtension_iff_isCyclotomicZpExtension_cyclotomicZpSubfield p K).2
    H.isCyclotomicZpExtension_cyclotomicZpSubfield

/-- `K` have a cyclotomic `ℤₚ`-extension if and only if $K(μ_{p^∞}) / K$
is an infinite extension. -/
theorem hasCyclotomicZpExtension_iff_infinite_dimensional [Fact p.Prime] :
    HasCyclotomicZpExtension p K ↔ (p : K) ≠ 0 ∧ ¬FiniteDimensional K (CyclotomicPinfField p K) :=
  ⟨fun ⟨_, _, _, _, H⟩ ↦ ⟨H.neZero.out, H.infinite_dimensional_cyclotomicPinfField⟩, fun ⟨h, hi⟩ ↦
    have := NeZero.mk h
    ⟨_, _, _, _, CyclotomicPinfField.isCyclotomicZpExtension_cyclotomicZpSubfield p K hi⟩⟩

/-- Any number field has a cyclotomic `ℤₚ`-extension. -/
instance NumberField.hasCyclotomicZpExtension [Fact p.Prime] [NumberField K] :
    HasCyclotomicZpExtension p K := by
  rw [hasCyclotomicZpExtension_iff_infinite_dimensional]
  refine ⟨mod_cast ‹Fact p.Prime›.out.ne_zero, fun H ↦ ?_⟩
  have := algebraRat.charZero (CyclotomicPinfField p K)
  have := FiniteDimensional.trans ℚ K (CyclotomicPinfField p K)
  have : NumberField (CyclotomicPinfField p K) := ⟨⟩
  have h1 (m) : ∃ n, m < (p ^ n).totient := by
    use m + 1
    rw [Nat.totient_prime_pow_succ Fact.out]
    have h1 := ‹Fact p.Prime›.out.one_lt
    have h2 := Nat.lt_pow_self (n := m) h1
    conv_lhs => rw [← mul_one m]
    exact Nat.mul_lt_mul_of_lt_of_le' h2 (by omega) zero_lt_one
  obtain ⟨n, hn⟩ := h1 (Module.finrank ℚ (CyclotomicPinfField p K))
  have : IsCyclotomicExtension .. := CyclotomicPinfField.isCyclotomicPinfExtension p K
  have hpn : p ^ n ≠ 0 := by simp [‹Fact p.Prime›.out.ne_zero]
  obtain ⟨x, hx⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := (Set.range (p ^ ·))) K
    (CyclotomicPinfField p K) (n := p ^ n) (by simp) hpn
  have hi := Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hpn)
  have := Fact.mk hi
  have hroot := hx.isRoot_cyclotomic (Nat.pos_of_ne_zero hpn)
  let f := AdjoinRoot.liftAlgHom (Polynomial.cyclotomic (p ^ n) ℚ) (Algebra.ofId ℚ _) x <| by
    rwa [Polynomial.IsRoot.def, ← Polynomial.map_cyclotomic _
      (algebraMap ℚ (CyclotomicPinfField p K)), Polynomial.eval_map] at hroot
  have hle := LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) f.injective
  rw [show Module.finrank ℚ (AdjoinRoot (Polynomial.cyclotomic (p ^ n) ℚ)) = _ from
    finrank_quotient_span_eq_natDegree, Polynomial.natDegree_cyclotomic] at hle
  exact hn.not_ge hle

-- /-- Any local field has a cyclotomic `ℤₚ`-extension. -/
-- instance IsNonarchimedeanLocalField.hasCyclotomicZpExtension [Fact p.Prime] [NeZero (p : K)]
--     [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
--     HasCyclotomicZpExtension p K := by
--   sorry
