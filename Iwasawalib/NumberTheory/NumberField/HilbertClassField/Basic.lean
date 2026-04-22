/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.FieldTheory.IntermediateField.MaximalAbelian
public import Iwasawalib.NumberTheory.AbsoluteValue.GelfandTornheim
public import Iwasawalib.NumberTheory.AbsoluteValue.RamificationIndex

@[expose] public section

/-!

# Hilbert class field (experimental) - basic definitions

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

omit [Algebra L K] [IsScalarTower L K M] in
theorem IsUnramifiedOutside.tower_top [Algebra.IsAlgebraic F M] [IsUnramifiedOutside F M L S] :
    haveI := Algebra.IsAlgebraic.tower_top (K := F) (L := K) (A := M)
    IsUnramifiedOutside K M L S := by
  use fun v hv hv' w hw ↦ (IsUnramifiedOutside.isUnramifiedIn F M L S v hv hv' w hw).tower_top K

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

end NumberField
