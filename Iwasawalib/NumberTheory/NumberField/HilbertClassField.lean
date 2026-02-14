/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Iwasawalib.NumberTheory.RamificationInertia.AbsoluteValue
public import Mathlib.RingTheory.Frobenius

@[expose] public section

/-!

# Hilbert class field (experimental)

-/

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

namespace NumberField

/-! ### Assertion that a field extension is unramified outside `S` -/

/-- A typeclass asserting that an algebraic extension `K / F` is unramified outside `S`, where `S`
is a set of places of a subfield `L` of `K`. -/
@[mk_iff]
class IsUnramifiedOutside (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K]
    [Algebra L K] [Algebra.IsAlgebraic F K] (S : Set (AbsoluteValue L ℝ)) : Prop where
  isUnramifiedIn (F K L S) (v : AbsoluteValue L ℝ) (h1 : v.IsNontrivial)
    (h2 : ∀ w ∈ S, ¬v ≈ w) : v.IsUnramifiedIn F K

theorem isUnramifiedOutside_of_isUnramifiedOutside_preimage [Algebra.IsAlgebraic F K]
    (L L' : Type*) [Field L] [Field L'] [Algebra L K]
    [Algebra L' L] [Algebra L' K] [IsScalarTower L' L K] (S : Set (AbsoluteValue L' ℝ))
    [H : IsUnramifiedOutside F K L ((AbsoluteValue.comp · (algebraMap L' L).injective) ⁻¹' S)] :
    IsUnramifiedOutside F K L' S := by
  simp_rw [isUnramifiedOutside_iff, AbsoluteValue.IsUnramifiedIn] at H ⊢
  rintro v h1 h2 w h3
  have hwv : (w.comp (algebraMap L K).injective).comp (algebraMap L' L).injective = v := by
    ext x
    simpa [← IsScalarTower.algebraMap_apply] using congr($(h3.comp_eq') x)
  refine H (w.comp (algebraMap L K).injective) ?_ (fun u hu ↦ ?_) w inferInstance
  · rw [← hwv] at h1
    exact AbsoluteValue.isNontrivial_of_isNontrivial_comp _ h1
  · simp only [Set.mem_preimage] at hu
    specialize h2 _ hu
    contrapose! h2
    simpa only [hwv] using AbsoluteValue.IsEquiv.comp h2 (algebraMap L' L).injective

/-- TODO: ... -/
@[simps apply]
noncomputable def _root_.AbsoluteValue.rpowOfLeOneOrIsNonarchimedean {R : Type*} [Semiring R]
    (v : AbsoluteValue R ℝ)
    (c : ℝ) (h1 : 0 < c) (h2 : c ≤ 1 ∨ IsNonarchimedean v) : AbsoluteValue R ℝ where
  toFun x := v x ^ c
  map_mul' x y := by rw [map_mul, Real.mul_rpow (v.nonneg x) (v.nonneg y)]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) c
  eq_zero' x := by rw [Real.rpow_eq_zero (v.nonneg x) h1.ne', v.eq_zero]
  add_le' x y := by
    rcases h2 with h2 | h2
    · exact (Real.rpow_le_rpow (v.nonneg _) (v.add_le x y) h1.le).trans
        (Real.rpow_add_le_add_rpow (v.nonneg x) (v.nonneg y) h1.le h2)
    · exact (Real.rpow_le_rpow (v.nonneg _) (h2 x y) h1.le).trans_eq
        (Real.rpow_max (v.nonneg x) (v.nonneg y) h1.le) |>.trans
        (max_le_add_of_nonneg (by positivity) (by positivity))

variable {F K} in
theorem _root_.AbsoluteValue.exists_equiv_and_liesOver_of_comp_equiv (v : AbsoluteValue K ℝ)
    (w : AbsoluteValue F ℝ) (h : v.comp (algebraMap F K).injective ≈ w) :
    ∃ v' : AbsoluteValue K ℝ, v' ≈ v ∧ v'.LiesOver w := by
  by_cases hn : IsNonarchimedean v
  · obtain ⟨c, hc, h1⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 h
    refine ⟨v.rpowOfLeOneOrIsNonarchimedean c hc (.inr hn),
      .symm (AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨c, hc, rfl⟩), ?_⟩
    rw [AbsoluteValue.liesOver_iff]
    ext x
    simpa using congr($h1 x)
  obtain ⟨φ, hφ⟩ := v.exists_ringHom_complex_of_not_isNonarchimedean hn
  obtain ⟨c, hc, h1⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 hφ
  have hφ' := (AbsoluteValue.IsEquiv.comp hφ (algebraMap F K).injective).trans h
  obtain ⟨c', hc', h2⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 hφ'
  have hc'1 : c' ≤ 1 := by
    have h3 : 2 ^ c' = w 2 := by simpa [map_ofNat] using congr($h2 2)
    have h4 : w 2 ≤ 2 := by simpa [one_add_one_eq_two] using w.add_le 1 1
    rw [← h3] at h4
    contrapose! h4
    exact Real.self_lt_rpow_of_one_lt one_lt_two h4
  refine ⟨(place φ).rpowOfLeOneOrIsNonarchimedean c' hc' (.inl hc'1),
    AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ?_, ?_⟩
  · refine ⟨c'⁻¹ * c, by positivity, ?_⟩
    ext x
    rw [← h1, AbsoluteValue.rpowOfLeOneOrIsNonarchimedean_apply,
      ← Real.rpow_mul ((place φ).nonneg x), ← mul_assoc, mul_inv_cancel₀ hc'.ne', one_mul]
  · rw [AbsoluteValue.liesOver_iff]
    ext x
    simpa using congr($h2 x)

theorem isUnramifiedOutside_preimage_iff [Algebra.IsAlgebraic F K]
    (L L' : Type*) [Field L] [Field L'] [Algebra L K] [Algebra L' L] [Algebra.IsAlgebraic L' L]
    [Algebra L' K] [IsScalarTower L' L K] (S : Set (AbsoluteValue L' ℝ)) :
    IsUnramifiedOutside F K L ((AbsoluteValue.comp · (algebraMap L' L).injective) ⁻¹' S) ↔
    IsUnramifiedOutside F K L' S := by
  refine ⟨fun _ ↦ isUnramifiedOutside_of_isUnramifiedOutside_preimage F K L L' S, ?_⟩
  simp_rw [isUnramifiedOutside_iff, AbsoluteValue.IsUnramifiedIn]
  rintro H v h1 h2 w _
  simp only [Set.mem_preimage] at h2
  refine H (v.comp (algebraMap L' L).injective) ?_ (fun u hu h' ↦ ?_) w (.trans w v _)
  · rwa [AbsoluteValue.isNontrivial_iff_of_liesOver _ v]
  · obtain ⟨v', h3, h4⟩ := AbsoluteValue.exists_equiv_and_liesOver_of_comp_equiv _ _ h'
    exact h2 v' (h4.comp_eq' ▸ hu) h3.symm

/-- A typeclass asserting that an algebraic extension `K / F` is unramified everywhere. -/
abbrev IsUnramifiedEverywhere [Algebra.IsAlgebraic F K] : Prop := IsUnramifiedOutside F K K ∅

theorem isUnramifiedEverywhere_iff [Algebra.IsAlgebraic F K] : IsUnramifiedEverywhere F K ↔
    ∀ v : AbsoluteValue K ℝ, v.IsNontrivial → v.IsUnramified F := by
  simp [isUnramifiedOutside_iff]

theorem isUnramifiedOutside_empty_iff (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K]
    [Algebra L K] [Algebra.IsAlgebraic F K] [Algebra.IsAlgebraic L K] :
    IsUnramifiedOutside F K L ∅ ↔ IsUnramifiedEverywhere F K := by
  rw [IsUnramifiedEverywhere, ← isUnramifiedOutside_preimage_iff F K K L ∅, Set.preimage_empty]

section IsScalarTower

variable (M : Type*) [Field M] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
  (L : Type*) [Field L] [Algebra L K] [Algebra L M] [IsScalarTower L K M]
  (S : Set (AbsoluteValue L ℝ))

theorem IsUnramifiedOutside.tower_top [Algebra.IsAlgebraic F M] [IsUnramifiedOutside F M L S] :
    haveI := Algebra.IsAlgebraic.tower_top (K := F) (L := K) (A := M)
    IsUnramifiedOutside K M L S := by
  sorry

theorem IsUnramifiedOutside.tower_bot [Algebra.IsAlgebraic F M] [IsUnramifiedOutside F M L S] :
    haveI := Algebra.IsAlgebraic.tower_bot (K := F) (L := K) (A := M)
    IsUnramifiedOutside F K L S := by
  sorry

theorem IsUnramifiedOutside.trans [Algebra.IsAlgebraic F K] [IsUnramifiedOutside F K L S]
    [Algebra.IsAlgebraic K M] [IsUnramifiedOutside K M L S] :
    haveI := Algebra.IsAlgebraic.trans F K M
    IsUnramifiedOutside F M L S := by
  sorry

theorem IsUnramifiedEverywhere.tower_top [Algebra.IsAlgebraic F M] [IsUnramifiedEverywhere F M] :
    haveI := Algebra.IsAlgebraic.tower_top (K := F) (L := K) (A := M)
    IsUnramifiedEverywhere K M := by
  have := Algebra.IsAlgebraic.tower_top (K := F) (L := K) (A := M)
  simp only [← isUnramifiedOutside_empty_iff _ _ F] at *
  exact .tower_top F K M F ∅

theorem IsUnramifiedEverywhere.tower_bot [Algebra.IsAlgebraic F M] [IsUnramifiedEverywhere F M] :
    haveI := Algebra.IsAlgebraic.tower_bot (K := F) (L := K) (A := M)
    IsUnramifiedEverywhere F K := by
  have := Algebra.IsAlgebraic.tower_bot (K := F) (L := K) (A := M)
  simp only [← isUnramifiedOutside_empty_iff _ _ F] at *
  exact .tower_bot F K M F ∅

theorem IsUnramifiedEverywhere.trans [Algebra.IsAlgebraic F K] [IsUnramifiedEverywhere F K]
    [Algebra.IsAlgebraic K M] [IsUnramifiedEverywhere K M] :
    haveI := Algebra.IsAlgebraic.trans F K M
    IsUnramifiedEverywhere F M := by
  have := Algebra.IsAlgebraic.trans F K M
  simp only [← isUnramifiedOutside_empty_iff _ _ F] at *
  exact .trans F K M F ∅

end IsScalarTower

/-! ### Maximal unramified algebra subextension -/

/-- The maximal algebra subextension of `K / F` unramified outside `S`, where `S` is a set of
places of a subfield `L` of `F`. -/
def maximalExtensionUnramifiedOutside (L : Type*) [Field L] [Algebra L F]
    (S : Set (AbsoluteValue L ℝ)) : IntermediateField F K :=
  sSup {E | ∃ (_ : Algebra.IsAlgebraic F E),
    IsUnramifiedOutside F E F ((AbsoluteValue.comp · (algebraMap L F).injective) ⁻¹' S)}

/-- The maximal unramified algebra subextension of `K / F`. -/
abbrev maximalUnramifiedExtension : IntermediateField F K :=
  maximalExtensionUnramifiedOutside F K F ∅

instance isAlgebraic_maximalExtensionUnramifiedOutside (L : Type*) [Field L] [Algebra L F]
    (S : Set (AbsoluteValue L ℝ)) :
    Algebra.IsAlgebraic F (maximalExtensionUnramifiedOutside F K L S) := by
  rw [maximalExtensionUnramifiedOutside, sSup_eq_iSup']
  have (E : {E : IntermediateField F K | ∃ (_ : Algebra.IsAlgebraic F E),
    IsUnramifiedOutside F E F ((AbsoluteValue.comp · (algebraMap L F).injective) ⁻¹' S)}) :
    Algebra.IsAlgebraic F E := E.2.choose
  exact IntermediateField.isAlgebraic_iSup this

instance isUnramifiedOutside_maximalExtensionUnramifiedOutside (L : Type*) [Field L] [Algebra L F]
    (S : Set (AbsoluteValue L ℝ)) :
    IsUnramifiedOutside F (maximalExtensionUnramifiedOutside F K L S)
      F ((AbsoluteValue.comp · (algebraMap L F).injective) ⁻¹' S) := by
  sorry

instance isUnramifiedOutside_maximalExtensionUnramifiedOutside' (L : Type*) [Field L] [Algebra L F]
    [Algebra L K] [IsScalarTower L F K] (S : Set (AbsoluteValue L ℝ)) :
    IsUnramifiedOutside F (maximalExtensionUnramifiedOutside F K L S) L S :=
  isUnramifiedOutside_of_isUnramifiedOutside_preimage F _ F L S

/-- Suppose `M / K / F` is a field extension tower, such that `M / F` and `K / F` are Galois.
Let `H / K` be the maximal algebra subextension of `M / K` unramified outside `S`, where `S` is a
set of places of a subfield `L` of `F`. Then `H / F` is also Galois. -/
theorem isGalois_maximalExtensionUnramifiedOutside_of_isGalois
    (M : Type*) [Field M] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
    [IsGalois F M] [IsGalois F K]
    (L : Type*) [Field L] [Algebra L F] [Algebra L K] [IsScalarTower L F K]
    (S : Set (AbsoluteValue L ℝ)) : IsGalois F (maximalExtensionUnramifiedOutside K M L S) := by
  sorry

/-- Suppose `M / K / F` is a field extension tower, such that `M / F` and `K / F` are Galois.
Let `H / K` be the maximal unramified algebra subextension of `M / K`.
Then `H / F` is also Galois. -/
theorem isGalois_maximalUnramifiedExtension_of_isGalois
    (M : Type*) [Field M] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
    [IsGalois F M] [IsGalois F K] : IsGalois F (maximalUnramifiedExtension K M) :=
  isGalois_maximalExtensionUnramifiedOutside_of_isGalois F K M F ∅

#exit

/-- The maximal unramified abelian subextension is a finite extension.
A result in global class field theory. We cannot prove it here. -/
instance finiteDimensional_maximalUnramifiedAbelianExtension [NumberField F] :
    FiniteDimensional F (maximalUnramifiedAbelianExtension F K) := sorry

/-- The maximal unramified abelian subextension is an abelian extension.
Because compositum of abelian Galois extensions is also abelian.
Proof: the group homomorphism `Gal(⨆ i, E_i/F) → Π i, Gal(E_i/F)` is injective.
Should go mathlib. -/
instance isAbelianGalois_maximalUnramifiedAbelianExtension :
    IsAbelianGalois F (maximalUnramifiedAbelianExtension F K) := sorry

/-- The maximal unramified abelian subextension is unramified everywhere.
Because when considering only one place,
compositum of unramified extensions is also unramified.
Should find a proof and submit to mathlib. -/
instance isUnramifiedEverywhere_maximalUnramifiedAbelianExtension :
    IsUnramifiedEverywhere F (maximalUnramifiedAbelianExtension F K) := sorry

instance numberField_maximalUnramifiedAbelianExtension [NumberField F] :
    NumberField (maximalUnramifiedAbelianExtension F K) where
  to_finiteDimensional := FiniteDimensional.trans ℚ F _

namespace IsUnramifiedEverywhere

/-- An unramified everywhere abelian extension of a number field must be finite. -/
instance (priority := low) finiteDimensional
    [NumberField F] [IsUnramifiedEverywhere F K] [IsAbelianGalois F K] :
    FiniteDimensional F K := sorry

/-- An unramified everywhere abelian extension of a number field must be a number field. -/
theorem numberField
    [NumberField F] [IsUnramifiedEverywhere F K] [IsAbelianGalois F K] :
    NumberField K := by
  have := charZero_of_injective_algebraMap (algebraMap F K).injective
  have := FiniteDimensional.trans ℚ F K
  exact ⟨⟩

/-! ### Artin map of an unramified abelian extension -/

/-- If `K / F` is an unramified abelian extension, then there is a natural map `Cl(F) → Gal(K/F)`
sending a prime ideal `p` to the Frobenius element `Frobₚ` in `Gal(K/F)`.
We cannot give the formal definition of it here, but use `sorry` instead. -/
noncomputable def artinMap [NumberField F] [IsUnramifiedEverywhere F K] [IsAbelianGalois F K] :
    ClassGroup (𝓞 F) →* Gal(K/F) := sorry

theorem artinMap_spec [NumberField F] [IsUnramifiedEverywhere F K] [IsAbelianGalois F K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h : P.asIdeal.under (𝓞 F) = p.asIdeal) :
    haveI := numberField F K
    artinMap F K (.mk0 ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩) =
      arithFrobAt (𝓞 F) Gal(K/F) P.asIdeal :=
  sorry

/-- The Artin map is `p ↦ Frobₚ` surjective. It is a consequence of a stronger result:
Chebotarev density theorem. -/
theorem surjective_artinMap [NumberField F] [IsUnramifiedEverywhere F K] [IsAbelianGalois F K] :
    Function.Surjective (artinMap F K) :=
  sorry

theorem finrank_dvd_classNumber [NumberField F] [IsUnramifiedEverywhere F K] [IsAbelianGalois F K] :
    Module.finrank F K ∣ classNumber F := by
  rw [classNumber, Fintype.card_eq_nat_card, ← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_dvd_of_surjective _ (surjective_artinMap F K)

end IsUnramifiedEverywhere

/-! ### Hilbert class field -/

/-- The Hilbert class field `H_F` of a number field `F`, defined as a `Type` corresponding to
the maximal unramified abelian extension of `F` inside its separable closure. -/
def HilbertClassField : Type _ := maximalUnramifiedAbelianExtension F (SeparableClosure F)

namespace HilbertClassField

noncomputable instance instField : Field (HilbertClassField F) :=
  inferInstanceAs (Field (maximalUnramifiedAbelianExtension ..))

noncomputable instance algebra : Algebra F (HilbertClassField F) :=
  inferInstanceAs (Algebra F (maximalUnramifiedAbelianExtension ..))

noncomputable instance instInhabited : Inhabited (HilbertClassField F) := ⟨0⟩

instance instCharZero [CharZero F] : CharZero (HilbertClassField F) :=
  charZero_of_injective_algebraMap (algebraMap F _).injective

instance instCharP (p : ℕ) [CharP F p] : CharP (HilbertClassField F) p :=
  charP_of_injective_algebraMap (algebraMap F _).injective p

instance instExpChar (p : ℕ) [ExpChar F p] : ExpChar (HilbertClassField F) p :=
  expChar_of_injective_algebraMap (algebraMap F _).injective p

noncomputable instance algebra' (R : Type*) [CommRing R] [Algebra R F] :
    Algebra R (HilbertClassField F) :=
  inferInstanceAs (Algebra R (maximalUnramifiedAbelianExtension ..))

instance instIsScalarTower (R : Type*) [CommRing R] [Algebra R F] :
    IsScalarTower R F (HilbertClassField F) :=
  inferInstanceAs (IsScalarTower R F (maximalUnramifiedAbelianExtension ..))

instance instNoZeroSMulDivisors (R : Type*) [CommRing R] [Algebra R F] [IsFractionRing R F] :
    NoZeroSMulDivisors R (HilbertClassField F) := by
  rw [NoZeroSMulDivisors.iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective,
    IsScalarTower.algebraMap_eq R F (HilbertClassField F)]
  exact
    (Function.Injective.comp (FaithfulSMul.algebraMap_injective F (HilbertClassField F))
      (IsFractionRing.injective R F) :)

instance isSeparable : Algebra.IsSeparable F (HilbertClassField F) :=
  inferInstanceAs (Algebra.IsSeparable F (maximalUnramifiedAbelianExtension ..))

/-- The Hilbert class field `H_F` is a finite extension of `F`. -/
instance finiteDimensional [NumberField F] : FiniteDimensional F (HilbertClassField F) :=
  inferInstanceAs (FiniteDimensional F (maximalUnramifiedAbelianExtension ..))

/-- The Hilbert class field `H_F` is an abelian extension of `F`. -/
instance isAbelianGalois : IsAbelianGalois F (HilbertClassField F) :=
  inferInstanceAs (IsAbelianGalois F (maximalUnramifiedAbelianExtension ..))

/-- The Hilbert class field `H_F` is unramified everywhere over `F`. -/
instance isUnramifiedEverywhere : IsUnramifiedEverywhere F (HilbertClassField F) :=
  inferInstanceAs (IsUnramifiedEverywhere F (maximalUnramifiedAbelianExtension ..))

/-- The Hilbert class field `H_F` is a number field. -/
instance numberField [NumberField F] : NumberField (HilbertClassField F) :=
  inferInstanceAs (NumberField (maximalUnramifiedAbelianExtension ..))

/-- If `K / F` is a Galois extension, then `H_K / F` is also Galois,
where `H_K` is the Hilbert class field of `K`. -/
theorem isGalois_of_isGalois [IsGalois F K] :
    IsGalois F (HilbertClassField K) := by
  have : IsSepClosure F (SeparableClosure K) := .mk inferInstance (.trans F K _)
  exact isGalois_maximalUnramifiedAbelianExtension_of_isGalois F K _

/-- The Artin map `Cl(F) → Gal(H_F / F)` is bijective. -/
theorem bijective_artinMap [NumberField F] :
    Function.Bijective (IsUnramifiedEverywhere.artinMap F (HilbertClassField F)) :=
  sorry

/-- The natural isomorphism `Cl(F) ≃ Gal(H_F / F)` given by Artin map. -/
noncomputable def artinEquiv [NumberField F] :
    ClassGroup (𝓞 F) ≃* Gal(HilbertClassField F/F) :=
  .ofBijective (IsUnramifiedEverywhere.artinMap F _) (bijective_artinMap F)

theorem artinEquiv_apply [NumberField F] (p) :
    artinEquiv F p = IsUnramifiedEverywhere.artinMap F _ p := rfl

theorem finrank_eq_classNumber [NumberField F] :
    Module.finrank F (HilbertClassField F) = classNumber F := by
  rw [classNumber, Fintype.card_eq_nat_card, ← IsGalois.card_aut_eq_finrank]
  exact Nat.card_congr (artinEquiv F).symm.toEquiv

/-- Any unramified abelian extension is a subfield of Hilbert class field. -/
noncomputable def lift
    [NumberField F] [IsUnramifiedEverywhere F K] [IsAbelianGalois F K] :
    K →ₐ[F] HilbertClassField F :=
  sorry

end HilbertClassField

end NumberField
