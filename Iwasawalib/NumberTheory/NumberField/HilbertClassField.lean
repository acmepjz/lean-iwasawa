/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.FieldTheory.IntermediateField.MaximalAbelian
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
    simpa [← IsScalarTower.algebraMap_apply] using congr($(h3.comp_eq) x)
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
    exact h2 v' (h4.comp_eq ▸ hu) h3.symm

/-- A typeclass asserting that an algebraic extension `K / F` is unramified everywhere. -/
abbrev IsUnramifiedEverywhere [Algebra.IsAlgebraic F K] : Prop := IsUnramifiedOutside F K K ∅

theorem isUnramifiedEverywhere_iff [Algebra.IsAlgebraic F K] : IsUnramifiedEverywhere F K ↔
    ∀ v : AbsoluteValue K ℝ, v.IsNontrivial → v.IsUnramified F := by
  simp [isUnramifiedOutside_iff]

theorem isUnramifiedOutside_empty_iff (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K]
    [Algebra L K] [Algebra.IsAlgebraic F K] [Algebra.IsAlgebraic L K] :
    IsUnramifiedOutside F K L ∅ ↔ IsUnramifiedEverywhere F K := by
  rw [IsUnramifiedEverywhere, ← isUnramifiedOutside_preimage_iff F K K L ∅, Set.preimage_empty]

instance (priority := low) isUnramifiedOutside_empty_of_isUnramifiedEverywhere
    (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K]
    [Algebra L K] [Algebra.IsAlgebraic F K] [Algebra.IsAlgebraic L K] [IsUnramifiedEverywhere F K] :
    IsUnramifiedOutside F K L ∅ :=
  (isUnramifiedOutside_empty_iff F K L).2 ‹_›

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
  rw [← isUnramifiedOutside_empty_iff _ _ F]
  exact .tower_top F K M F ∅

theorem IsUnramifiedEverywhere.tower_bot [Algebra.IsAlgebraic F M] [IsUnramifiedEverywhere F M] :
    haveI := Algebra.IsAlgebraic.tower_bot (K := F) (L := K) (A := M)
    IsUnramifiedEverywhere F K := by
  have := Algebra.IsAlgebraic.tower_bot (K := F) (L := K) (A := M)
  rw [← isUnramifiedOutside_empty_iff _ _ F]
  exact .tower_bot F K M F ∅

theorem IsUnramifiedEverywhere.trans [Algebra.IsAlgebraic F K] [IsUnramifiedEverywhere F K]
    [Algebra.IsAlgebraic K M] [IsUnramifiedEverywhere K M] :
    haveI := Algebra.IsAlgebraic.trans F K M
    IsUnramifiedEverywhere F M := by
  have := Algebra.IsAlgebraic.trans F K M
  rw [← isUnramifiedOutside_empty_iff _ _ F]
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

instance isUnramifiedEverywhere_maximalUnramifiedExtension :
    IsUnramifiedEverywhere F (maximalUnramifiedExtension F K) := by
  rw [← isUnramifiedOutside_empty_iff F _ F]
  exact isUnramifiedOutside_maximalExtensionUnramifiedOutside' F _ F ∅

theorem le_maximalExtensionUnramifiedOutside (L : Type*) [Field L] [Algebra L F]
    (S : Set (AbsoluteValue L ℝ)) (E : IntermediateField F K) [Algebra.IsAlgebraic F E]
    [IsUnramifiedOutside F E F ((AbsoluteValue.comp · (algebraMap L F).injective) ⁻¹' S)] :
    E ≤ maximalExtensionUnramifiedOutside F K L S :=
  le_sSup ⟨‹_›, ‹_›⟩

theorem le_maximalExtensionUnramifiedOutside_iff (L : Type*) [Field L] [Algebra L F]
    (S : Set (AbsoluteValue L ℝ)) (E : IntermediateField F K) :
    E ≤ maximalExtensionUnramifiedOutside F K L S ↔ ∃ (_ : Algebra.IsAlgebraic F E),
      IsUnramifiedOutside F E F ((AbsoluteValue.comp · (algebraMap L F).injective) ⁻¹' S) := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _⟩ ↦ le_maximalExtensionUnramifiedOutside F K L S E⟩
  have : Algebra.IsAlgebraic F (IntermediateField.extendScalars h) :=
    isAlgebraic_maximalExtensionUnramifiedOutside F K L S
  have : IsUnramifiedOutside F (IntermediateField.extendScalars h)
      F ((AbsoluteValue.comp · (algebraMap L F).injective) ⁻¹' S) :=
    isUnramifiedOutside_maximalExtensionUnramifiedOutside F K L S
  have h1 := Algebra.IsAlgebraic.tower_bot F E (IntermediateField.extendScalars h)
  have h2 := IsUnramifiedOutside.tower_bot F E (IntermediateField.extendScalars h)
    F ((AbsoluteValue.comp · (algebraMap L F).injective) ⁻¹' S)
  exact ⟨h1, h2⟩

theorem le_maximalExtensionUnramifiedOutside' (L : Type*) [Field L] [Algebra L F]
    [Algebra.IsAlgebraic L F] [Algebra L K] [IsScalarTower L F K] (S : Set (AbsoluteValue L ℝ))
    (E : IntermediateField F K) [Algebra.IsAlgebraic F E] [IsUnramifiedOutside F E L S] :
    E ≤ maximalExtensionUnramifiedOutside F K L S := by
  simp only [← isUnramifiedOutside_preimage_iff F E F L S] at *
  exact le_maximalExtensionUnramifiedOutside F K L S E

theorem le_maximalExtensionUnramifiedOutside_iff' (L : Type*) [Field L] [Algebra L F]
    [Algebra.IsAlgebraic L F] [Algebra L K] [IsScalarTower L F K] (S : Set (AbsoluteValue L ℝ))
    (E : IntermediateField F K) :
    E ≤ maximalExtensionUnramifiedOutside F K L S ↔ ∃ (_ : Algebra.IsAlgebraic F E),
      IsUnramifiedOutside F E L S := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _⟩ ↦ le_maximalExtensionUnramifiedOutside' F K L S E⟩
  obtain ⟨h1, h2⟩ := (le_maximalExtensionUnramifiedOutside_iff F K L S E).1 h
  rw [isUnramifiedOutside_preimage_iff] at h2
  exact ⟨h1, h2⟩

theorem le_maximalUnramifiedExtension (E : IntermediateField F K) [Algebra.IsAlgebraic F E]
    [IsUnramifiedEverywhere F E] : E ≤ maximalUnramifiedExtension F K :=
  le_maximalExtensionUnramifiedOutside' ..

theorem le_maximalUnramifiedExtension_iff (E : IntermediateField F K) :
    E ≤ maximalUnramifiedExtension F K ↔ ∃ (_ : Algebra.IsAlgebraic F E),
      IsUnramifiedEverywhere F E := by
  simp only [← isUnramifiedOutside_empty_iff _ _ F]
  exact le_maximalExtensionUnramifiedOutside_iff' ..

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

/-! ### Artin map of an unramified abelian extension -/

namespace IsUnramifiedEverywhere

/-- If `K / F` is an unramified abelian extension of number fields,
then there is a natural map `Cl(F) → Gal(K/F)`
sending a prime ideal `p` to the Frobenius element `Frobₚ` in `Gal(K/F)`.
Its definition should not involve class field theory.
We omit its formal definition here, but use `sorry` instead.

NOTE: a priori we don't know `K / F` is finite, so for `x : K` the `Frobₚ x`
should be defined by the Frobenius on `F(x) / F` instead, which is a finite extension. -/
noncomputable def artinMap
    [NumberField F] [IsAbelianGalois F K] [IsUnramifiedEverywhere F K] :
    ClassGroup (𝓞 F) →* Gal(K/F) := sorry

variable [NumberField F] [IsAbelianGalois F K] [IsUnramifiedEverywhere F K]

/-- The Artin map `p ↦ Frobₚ` is surjective. When `K / F` is finite, it could be proved by
Chebotarev density theorem. In general suppose there exists `σ : Gal(K/F)`
such that `Frobₚ ≠ σ` for all `p : Cl(K)`, then for each `p : Cl(K)` there is `x_p : K` such that
`Frobₚ x_p ≠ σ x_p`, hence the Artin map is not surjective on `F(x_p | p : Gal(K/F)) / F`,
which is a contradiction, since this is a finite extension. -/
theorem surjective_artinMap : Function.Surjective (artinMap F K) :=
  sorry

/-- An unramified abelian extension of a number field is a finite extension. -/
instance (priority := low) finiteDimensional : FiniteDimensional F K := by
  have := Finite.of_surjective _ (surjective_artinMap F K)
  exact IsGalois.finiteDimensional_of_finite F K

include F in
/-- An unramified abelian extension of a number field is a number field. -/
theorem numberField : NumberField K := by
  have := charZero_of_injective_algebraMap (algebraMap F K).injective
  have := FiniteDimensional.trans ℚ F K
  exact ⟨⟩

/-- The degree of an unramified abelian extension of a number field divides the class number of
the base field. -/
theorem finrank_dvd_classNumber : Module.finrank F K ∣ classNumber F := by
  rw [classNumber, Fintype.card_eq_nat_card, ← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_dvd_of_surjective _ (surjective_artinMap F K)

theorem artinMap_spec
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h : P.asIdeal.under (𝓞 F) = p.asIdeal) :
    haveI := numberField F K
    artinMap F K (.mk0 ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩) =
      arithFrobAt (𝓞 F) Gal(K/F) P.asIdeal :=
  sorry

end IsUnramifiedEverywhere

/-! ### Maximal unramified abelian subextension -/

/-- The maximal abelian subextension of `K / F` unramified outside `S`, where `S` is a set of
places of a subfield `L` of `F`, is defined to be the maximal abelian
subextension of the maximal algebraic subextension of `K / F` unramified outside `S`. -/
def maximalAbelianExtensionUnramifiedOutside (L : Type*) [Field L] [Algebra L F]
    (S : Set (AbsoluteValue L ℝ)) : IntermediateField F K :=
  .lift (.maximalAbelianExtension F (maximalExtensionUnramifiedOutside F K L S))

/-- The maximal unramified abelian subextension of `K / F`, is defined to be the maximal abelian
subextension of the maximal unramified algebraic subextension of `K / F`. -/
abbrev maximalUnramifiedAbelianExtension : IntermediateField F K :=
  maximalAbelianExtensionUnramifiedOutside F K F ∅

instance isAbelianGalois_maximalAbelianExtensionUnramifiedOutside
    (L : Type*) [Field L] [Algebra L F] (S : Set (AbsoluteValue L ℝ)) :
    IsAbelianGalois F (maximalAbelianExtensionUnramifiedOutside F K L S) :=
  .of_algEquiv (IntermediateField.liftAlgEquiv ..)

-- TODO: need IsUnramifiedEverywhere.of_algEquiv etc.
instance isUnramifiedOutside_maximalAbelianExtensionUnramifiedOutside
    (L : Type*) [Field L] [Algebra L F] (S : Set (AbsoluteValue L ℝ)) :
    IsUnramifiedOutside F (maximalAbelianExtensionUnramifiedOutside F K L S)
      F ((AbsoluteValue.comp · (algebraMap L F).injective) ⁻¹' S) := by
  sorry

instance isUnramifiedOutside_maximalAbelianExtensionUnramifiedOutside'
    (L : Type*) [Field L] [Algebra L F]
    [Algebra L K] [IsScalarTower L F K] (S : Set (AbsoluteValue L ℝ)) :
    IsUnramifiedOutside F (maximalAbelianExtensionUnramifiedOutside F K L S) L S :=
  isUnramifiedOutside_of_isUnramifiedOutside_preimage F _ F L S

instance isUnramifiedEverywhere_maximalUnramifiedAbelianExtension :
    IsUnramifiedEverywhere F (maximalUnramifiedAbelianExtension F K) := by
  rw [← isUnramifiedOutside_empty_iff F _ F]
  exact isUnramifiedOutside_maximalAbelianExtensionUnramifiedOutside' F _ F ∅

theorem le_maximalAbelianExtensionUnramifiedOutside (L : Type*) [Field L] [Algebra L F]
    (S : Set (AbsoluteValue L ℝ)) (E : IntermediateField F K) [IsAbelianGalois F E]
    [IsUnramifiedOutside F E F ((AbsoluteValue.comp · (algebraMap L F).injective) ⁻¹' S)] :
    E ≤ maximalAbelianExtensionUnramifiedOutside F K L S := by
  sorry

theorem le_maximalAbelianExtensionUnramifiedOutside_iff (L : Type*) [Field L] [Algebra L F]
    (S : Set (AbsoluteValue L ℝ)) (E : IntermediateField F K) :
    E ≤ maximalAbelianExtensionUnramifiedOutside F K L S ↔ ∃ (_ : IsAbelianGalois F E),
      IsUnramifiedOutside F E F ((AbsoluteValue.comp · (algebraMap L F).injective) ⁻¹' S) := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _⟩ ↦ le_maximalAbelianExtensionUnramifiedOutside F K L S E⟩
  have : IsAbelianGalois F (IntermediateField.extendScalars h) :=
    isAbelianGalois_maximalAbelianExtensionUnramifiedOutside F K L S
  have : IsUnramifiedOutside F (IntermediateField.extendScalars h)
      F ((AbsoluteValue.comp · (algebraMap L F).injective) ⁻¹' S) :=
    isUnramifiedOutside_maximalAbelianExtensionUnramifiedOutside F K L S
  have h1 := IsAbelianGalois.tower_bot F E (IntermediateField.extendScalars h)
  have h2 := IsUnramifiedOutside.tower_bot F E (IntermediateField.extendScalars h)
    F ((AbsoluteValue.comp · (algebraMap L F).injective) ⁻¹' S)
  exact ⟨h1, h2⟩

theorem le_maximalAbelianExtensionUnramifiedOutside' (L : Type*) [Field L] [Algebra L F]
    [Algebra.IsAlgebraic L F] [Algebra L K] [IsScalarTower L F K] (S : Set (AbsoluteValue L ℝ))
    (E : IntermediateField F K) [IsAbelianGalois F E] [IsUnramifiedOutside F E L S] :
    E ≤ maximalAbelianExtensionUnramifiedOutside F K L S := by
  simp only [← isUnramifiedOutside_preimage_iff F E F L S] at *
  exact le_maximalAbelianExtensionUnramifiedOutside F K L S E

theorem le_maximalAbelianExtensionUnramifiedOutside_iff' (L : Type*) [Field L] [Algebra L F]
    [Algebra.IsAlgebraic L F] [Algebra L K] [IsScalarTower L F K] (S : Set (AbsoluteValue L ℝ))
    (E : IntermediateField F K) :
    E ≤ maximalAbelianExtensionUnramifiedOutside F K L S ↔ ∃ (_ : IsAbelianGalois F E),
      IsUnramifiedOutside F E L S := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _⟩ ↦ le_maximalAbelianExtensionUnramifiedOutside' F K L S E⟩
  obtain ⟨h1, h2⟩ := (le_maximalAbelianExtensionUnramifiedOutside_iff F K L S E).1 h
  rw [isUnramifiedOutside_preimage_iff] at h2
  exact ⟨h1, h2⟩

theorem le_maximalUnramifiedAbelianExtension (E : IntermediateField F K) [IsAbelianGalois F E]
    [IsUnramifiedEverywhere F E] : E ≤ maximalUnramifiedAbelianExtension F K :=
  le_maximalAbelianExtensionUnramifiedOutside' ..

theorem le_maximalUnramifiedAbelianExtension_iff (E : IntermediateField F K) :
    E ≤ maximalUnramifiedAbelianExtension F K ↔ ∃ (_ : IsAbelianGalois F E),
      IsUnramifiedEverywhere F E := by
  simp only [← isUnramifiedOutside_empty_iff _ _ F]
  exact le_maximalAbelianExtensionUnramifiedOutside_iff' ..

/-- Suppose `M / K / F` is a field extension tower, such that `M / F` and `K / F` are Galois.
Let `H / K` be the maximal abelian subextension of `M / K` unramified outside `S`, where `S` is a
set of places of a subfield `L` of `F`. Then `H / F` is also Galois. -/
theorem isGalois_maximalAbelianExtensionUnramifiedOutside_of_isGalois
    (M : Type*) [Field M] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
    [IsGalois F M] [IsGalois F K]
    (L : Type*) [Field L] [Algebra L F] [Algebra L K] [IsScalarTower L F K]
    (S : Set (AbsoluteValue L ℝ)) :
    IsGalois F (maximalAbelianExtensionUnramifiedOutside K M L S) := by
  sorry

/-- Suppose `M / K / F` is a field extension tower, such that `M / F` and `K / F` are Galois.
Let `H / K` be the maximal unramified abelian subextension of `M / K`.
Then `H / F` is also Galois. -/
theorem isGalois_maximalUnramifiedAbelianExtension_of_isGalois
    (M : Type*) [Field M] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
    [IsGalois F M] [IsGalois F K] : IsGalois F (maximalUnramifiedAbelianExtension K M) :=
  isGalois_maximalAbelianExtensionUnramifiedOutside_of_isGalois F K M F ∅

/-- The maximal unramified abelian subextension is a finite extension. -/
instance finiteDimensional_maximalUnramifiedAbelianExtension [NumberField F] :
    FiniteDimensional F (maximalUnramifiedAbelianExtension F K) :=
  IsUnramifiedEverywhere.finiteDimensional F _

instance numberField_maximalUnramifiedAbelianExtension [NumberField F] :
    NumberField (maximalUnramifiedAbelianExtension F K) :=
  IsUnramifiedEverywhere.numberField F _

/-! ### Hilbert class field -/

namespace IsUnramifiedEverywhere

/-- The Artin map `Cl(F) → Gal(H / F)` is bijective, if `H` is the maximal unramified abelian
subextension of `K / F` and `K` is separably closed. -/
theorem bijective_artinMap_of_isSepClosed [NumberField F] [IsSepClosed K] :
    Function.Bijective (artinMap F (maximalUnramifiedAbelianExtension F K)) :=
  sorry

/-- The natural isomorphism `Cl(F) ≃ Gal(H / F)` given by Artin map, where `H` is the maximal
unramified abelian subextension of `K / F` and `K` is separably closed. -/
noncomputable def artinEquivOfIsSepClosed [NumberField F] [IsSepClosed K] :
    ClassGroup (𝓞 F) ≃* Gal(maximalUnramifiedAbelianExtension F K/F) :=
  .ofBijective (artinMap F _) (bijective_artinMap_of_isSepClosed F K)

theorem artinEquivOfIsSepClosed_apply [NumberField F] [IsSepClosed K] (p) :
    artinEquivOfIsSepClosed F K p = artinMap F _ p := rfl

theorem finrank_eq_classNumber_of_isSepClosed [NumberField F] [IsSepClosed K] :
    Module.finrank F (maximalUnramifiedAbelianExtension F K) = classNumber F := by
  rw [classNumber, Fintype.card_eq_nat_card, ← IsGalois.card_aut_eq_finrank]
  exact Nat.card_congr (artinEquivOfIsSepClosed F K).symm.toEquiv

/-- Any unramified abelian extension is a subfield of Hilbert class field. -/
noncomputable def liftOfIsSepClosed
    [NumberField F] [IsAbelianGalois F K] [IsUnramifiedEverywhere F K]
    (L : Type*) [Field L] [Algebra F L] [IsSepClosed L] :
    K →ₐ[F] maximalUnramifiedAbelianExtension F L :=
  sorry

end IsUnramifiedEverywhere

end NumberField
