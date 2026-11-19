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

/-! ### Auxiliary results -/

/-- range of Gal(Ω/E) → Gal(Ω/F) is the fixing subgroup of (image of) E. -/
theorem IntermediateField.range_restrictRestrictAlgEquivMapHom_eq_fixingSubgroup
    (F E Ω : Type*) [Field F] [Field E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [Normal F Ω] :
    (IntermediateField.restrictRestrictAlgEquivMapHom F Ω E Ω).range =
      ((⊥ : IntermediateField E Ω).restrictScalars F).fixingSubgroup := by
  rw [IntermediateField.fixingSubgroup_restrictScalars, IntermediateField.fixingSubgroup_bot,
    ← MonoidHom.range_eq_map]

open AbsoluteValue IntermediateField in
theorem AbsoluteValue.isUnramified_iSup {F K : Type*} [Field F] [Field K] [Algebra F K]
    {ι : Type*} (E : ι → IntermediateField F K) (Es : IntermediateField F K)
    (hle : ∀ i, E i ≤ Es) (hEs : ⨆ i, E i = Es)
    [∀ i, Algebra.IsAlgebraic F (E i)] [Algebra.IsAlgebraic F Es]
    (u : AbsoluteValue Es ℝ)
    (H : ∀ i, (u.comp (f := (IntermediateField.inclusion (hle i) : E i →+* Es))
      (IntermediateField.inclusion_injective (hle i))).IsUnramified F) :
    u.IsUnramified F := by
  obtain ⟨w, hw⟩ := u.exists_liesOver (AlgebraicClosure Es)
  rw [AbsoluteValue.isUnramified_spec F u w, AbsoluteValue.IsUnramifiedOfIsScalarTower,
    IntermediateField.range_restrictRestrictAlgEquivMapHom_eq_fixingSubgroup,
    ← IntermediateField.le_iff_le]
  intro y hy
  rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_bot] at hy
  obtain ⟨x, rfl⟩ := hy
  have hCtop : (⊤ : IntermediateField F Es) ≤
      IntermediateField.comap (IsScalarTower.toAlgHom F Es (AlgebraicClosure Es))
        (IntermediateField.fixedField (AbsoluteValue.inertiaSubgroup F w)) := by
    have h1 : (⨆ i, IntermediateField.comap Es.val (E i)) = ⊤ := by
      apply IntermediateField.lift_injective Es
      rw [IntermediateField.lift_top, IntermediateField.lift, IntermediateField.map_iSup]
      calc (⨆ i, (IntermediateField.comap Es.val (E i)).map Es.val)
          = ⨆ i, E i := by
            refine iSup_congr fun i ↦ IntermediateField.map_comap_eq_self ?_
            rw [IntermediateField.fieldRange_val]; exact hle i
        _ = Es := hEs
    rw [← h1]
    refine iSup_le fun i z hz ↦ ?_
    letI : Algebra (E i) (AlgebraicClosure Es) :=
      ((algebraMap Es (AlgebraicClosure Es)).comp
        (IntermediateField.inclusion (hle i) : E i →+* Es)).toAlgebra
    have halg : ∀ t : E i, algebraMap (E i) (AlgebraicClosure Es) t =
        algebraMap Es (AlgebraicClosure Es) (IntermediateField.inclusion (hle i) t) := fun t ↦ rfl
    haveI : IsScalarTower F (E i) (AlgebraicClosure Es) := IsScalarTower.of_algebraMap_eq fun r ↦ by
      rw [halg]
      rw [IsScalarTower.algebraMap_apply F Es (AlgebraicClosure Es)]
      congr 1
    haveI : w.LiesOver (u.comp (f := (IntermediateField.inclusion (hle i) : E i →+* Es))
        (IntermediateField.inclusion_injective (hle i))) := by
      rw [AbsoluteValue.liesOver_iff]
      ext t
      rw [AbsoluteValue.comp_apply, AbsoluteValue.comp_apply, halg]
      exact congr($(AbsoluteValue.LiesOver.comp_eq w u) _)
    have h2 := (AbsoluteValue.isUnramified_spec F _ w).1 (H i)
    rw [AbsoluteValue.IsUnramifiedOfIsScalarTower,
      IntermediateField.range_restrictRestrictAlgEquivMapHom_eq_fixingSubgroup] at h2
    show (IsScalarTower.toAlgHom F Es (AlgebraicClosure Es)) z ∈
      IntermediateField.fixedField (AbsoluteValue.inertiaSubgroup F w)
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h3 := h2 hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at h3
    refine h3 _ ?_
    rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_bot]
    exact ⟨⟨z, hz⟩, rfl⟩
  exact hCtop IntermediateField.mem_top

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
    simpa [AbsoluteValue.under, ← IsScalarTower.algebraMap_apply] using congr($(h3.under_eq) x)
  refine H (w.comp (algebraMap L K).injective) ?_ (fun u hu ↦ ?_) w inferInstance
  · rw [← hwv] at h1
    exact AbsoluteValue.isNontrivial_of_isNontrivial_comp _ h1
  · simp only [Set.mem_preimage] at hu
    specialize h2 _ hu
    contrapose! h2
    change v.IsEquiv _
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
    exact h2 v' ((show v'.comp (algebraMap L' L).injective = u from h4.under_eq) ▸ hu) h3.symm

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
  use fun v hv hv' ↦ (IsUnramifiedOutside.isUnramifiedIn F M L S v hv hv').tower_bot K

theorem IsUnramifiedOutside.trans [Algebra.IsAlgebraic F K] [IsUnramifiedOutside F K L S]
    [Algebra.IsAlgebraic K M] [IsUnramifiedOutside K M L S] :
    haveI := Algebra.IsAlgebraic.trans F K M
    IsUnramifiedOutside F M L S := by
  use fun v hv hv' ↦ (IsUnramifiedOutside.isUnramifiedIn F K L S v hv hv').trans
    (IsUnramifiedOutside.isUnramifiedIn K M L S v hv hv')

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

/-- If `E / A` and `E' / A` are algebraic extensions which are isomorphic as rings, compatibly
with a ring automorphism `f` of `A` which preserves the set `T` of places, then `E / A` is
unramified outside `T` if and only if `E' / A` is. -/
theorem IsUnramifiedOutside.of_ringEquiv (A : Type*) [Field A]
    {E E' : Type*} [Field E] [Field E'] [Algebra A E] [Algebra A E']
    [Algebra.IsAlgebraic A E] [Algebra.IsAlgebraic A E'] (T : Set (AbsoluteValue A ℝ))
    {f : A ≃+* A} {g : E ≃+* E'}
    (hT : ∀ v : AbsoluteValue A ℝ, v.comp (f := (f : A →+* A)) f.injective ∈ T ↔ v ∈ T)
    (hcomp : (algebraMap A E').comp (f : A →+* A) = RingHom.comp (g : E →+* E') (algebraMap A E))
    [IsUnramifiedOutside A E A T] : IsUnramifiedOutside A E' A T := by
  refine ⟨fun v hv hv' ↦ ?_⟩
  refine (AbsoluteValue.isUnramifiedIn_comp_ringEquiv_iff (K' := A) (L' := E) v hcomp hcomp).1 ?_
  refine IsUnramifiedOutside.isUnramifiedIn A E A T (v.comp f.injective) ?_ ?_
  · obtain ⟨x, hx0, hx1⟩ := hv
    exact ⟨f.symm x, by simpa using hx0, by simpa [AbsoluteValue.comp_apply] using hx1⟩
  · intro w hw hcon
    refine hv' (w.comp (f := (f.symm : A →+* A)) f.symm.injective) ((hT _).1 ?_) ?_
    · have : (w.comp (f := (f.symm : A →+* A)) f.symm.injective).comp
          (f := (f : A →+* A)) f.injective = w := by
        ext x; simp [AbsoluteValue.comp_apply]
      rwa [this]
    · have h2 := AbsoluteValue.IsEquiv.comp (v := v.comp f.injective) (w := w) hcon
        (f := (f.symm : A →+* A)) f.symm.injective
      have h3 : (v.comp (f := (f : A →+* A)) f.injective).comp
          (f := (f.symm : A →+* A)) f.symm.injective = v := by
        ext x; simp [AbsoluteValue.comp_apply]
      rwa [h3] at h2

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
  set T := ((AbsoluteValue.comp · (algebraMap L F).injective) ⁻¹' S) with hT
  set 𝒮 : Set (IntermediateField F K) := {E | ∃ (_ : Algebra.IsAlgebraic F E),
    IsUnramifiedOutside F E F T} with h𝒮
  refine ⟨fun v hv hv' u hu ↦ ?_⟩
  have hEs : ⨆ i : 𝒮, (i : IntermediateField F K) = maximalExtensionUnramifiedOutside F K L S :=
    (sSup_eq_iSup' 𝒮).symm
  have hle : ∀ i : 𝒮, (i : IntermediateField F K) ≤ maximalExtensionUnramifiedOutside F K L S :=
    fun i ↦ le_sSup i.2
  haveI : ∀ i : 𝒮, Algebra.IsAlgebraic F (i : IntermediateField F K) := fun i ↦ i.2.choose
  refine AbsoluteValue.isUnramified_iSup (fun i : 𝒮 ↦ (i : IntermediateField F K)) _ hle hEs u
    fun i ↦ ?_
  haveI : IsUnramifiedOutside F (i : IntermediateField F K) F T := i.2.choose_spec
  haveI : (u.comp (f := (IntermediateField.inclusion (hle i) : (i : IntermediateField F K) →+* _))
      (IntermediateField.inclusion_injective (hle i))).LiesOver v := by
    rw [AbsoluteValue.liesOver_iff]
    ext t
    have := congr($(AbsoluteValue.LiesOver.comp_eq u v) t)
    simpa [AbsoluteValue.comp_apply, AbsoluteValue.under] using this
  exact IsUnramifiedOutside.isUnramifiedIn F (i : IntermediateField F K) F T v hv hv' _ this

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

open IntermediateField in
/-- Suppose `M / K / F` is a field extension tower, such that `M / F` and `K / F` are Galois.
Let `H / K` be the maximal algebra subextension of `M / K` unramified outside `S`, where `S` is a
set of places of a subfield `L` of `F`. Then `H / F` is also Galois. -/
theorem isGalois_maximalExtensionUnramifiedOutside_of_isGalois
    (M : Type*) [Field M] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
    [IsGalois F M] [IsGalois F K]
    (L : Type*) [Field L] [Algebra L F] [Algebra L K] [IsScalarTower L F K]
    (S : Set (AbsoluteValue L ℝ)) : IsGalois F (maximalExtensionUnramifiedOutside K M L S) := by
  have halgM : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.tower_top (K := F) (L := K) (A := M)
  set H := maximalExtensionUnramifiedOutside K M L S with hH
  suffices Normal F H by
    have := IsGalois.tower_top_of_isGalois F K M
    have := H.isSeparable_tower_bot
    have := Algebra.IsSeparable.trans F K H
    exact ⟨⟩
  change Normal F (restrictScalars F H)
  rw [normal_iff_forall_map_le']
  intro σ
  let σH := ((restrictScalars F H).map σ.toAlgHom).toSubfield.toIntermediateField
      fun (x : K) ↦ by
    simp only [toSubfield_map, AlgHomClass.toRingHom_toAlgHom, restrictScalars_toSubfield,
      Subfield.mem_map, mem_toSubfield, RingHom.coe_coe]
    use algebraMap K M (σ.symm.restrictNormal K x), _root_.algebraMap_mem ..
    simp
  suffices σH ≤ H from fun x hx ↦ this hx
  let f := (σ.restrictNormal K).toRingEquiv
  let g : H ≃+* σH := ((restrictScalars F H).equivMap σ.toAlgHom).toRingEquiv
  have hcomp : (algebraMap K σH).comp f = RingHom.comp g (algebraMap K H) := by
    ext x
    simp only [AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, SubalgebraClass.coe_algebraMap,
      AlgEquiv.restrictNormal_commutes, f, g]
    rfl
  have hfL : ∀ x : L, f (algebraMap L K x) = algebraMap L K x := by
    intro x
    rw [IsScalarTower.algebraMap_apply L F K]
    exact (σ.restrictNormal K).commutes _
  have hT : ∀ v : AbsoluteValue K ℝ,
      v.comp (f := (f : K →+* K)) f.injective ∈
        ((AbsoluteValue.comp · (algebraMap L K).injective) ⁻¹' S) ↔
      v ∈ ((AbsoluteValue.comp · (algebraMap L K).injective) ⁻¹' S) := by
    intro v
    simp only [Set.mem_preimage]
    have : (v.comp (f := (f : K →+* K)) f.injective).comp (algebraMap L K).injective =
        v.comp (algebraMap L K).injective := by
      ext x
      simp [AbsoluteValue.comp_apply, hfL x]
    rw [this]
  haveI : Algebra.IsAlgebraic K σH := Algebra.IsAlgebraic.tower_bot K σH M
  haveI : IsUnramifiedOutside K σH K
      ((AbsoluteValue.comp · (algebraMap L K).injective) ⁻¹' S) :=
    IsUnramifiedOutside.of_ringEquiv K _ hT hcomp
  exact le_maximalExtensionUnramifiedOutside K M L S σH

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
  have h : maximalAbelianExtensionUnramifiedOutside F K L S ≤
      maximalExtensionUnramifiedOutside F K L S := IntermediateField.lift_le _
  have : Algebra.IsAlgebraic F (IntermediateField.extendScalars h) :=
    isAlgebraic_maximalExtensionUnramifiedOutside F K L S
  have : IsUnramifiedOutside F (IntermediateField.extendScalars h)
      F ((AbsoluteValue.comp · (algebraMap L F).injective) ⁻¹' S) :=
    isUnramifiedOutside_maximalExtensionUnramifiedOutside F K L S
  exact IsUnramifiedOutside.tower_bot F _ (IntermediateField.extendScalars h) F _

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
  rw [maximalAbelianExtensionUnramifiedOutside,
    IntermediateField.le_lift_maximalAbelianExtension_iff]
  exact ⟨le_maximalExtensionUnramifiedOutside F K L S E, ‹_›⟩

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
  haveI : IsGalois F (maximalExtensionUnramifiedOutside K M L S) :=
    isGalois_maximalExtensionUnramifiedOutside_of_isGalois F K M L S
  haveI := IntermediateField.isGalois_maximalAbelianExtension_of_isGalois F K
    (maximalExtensionUnramifiedOutside K M L S)
  exact IsGalois.of_algEquiv ((IntermediateField.liftAlgEquiv _).restrictScalars F)

/-- Suppose `M / K / F` is a field extension tower, such that `M / F` and `K / F` are Galois.
Let `H / K` be the maximal unramified abelian subextension of `M / K`.
Then `H / F` is also Galois. -/
theorem isGalois_maximalUnramifiedAbelianExtension_of_isGalois
    (M : Type*) [Field M] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
    [IsGalois F M] [IsGalois F K] : IsGalois F (maximalUnramifiedAbelianExtension K M) :=
  isGalois_maximalAbelianExtensionUnramifiedOutside_of_isGalois F K M F ∅

end NumberField
