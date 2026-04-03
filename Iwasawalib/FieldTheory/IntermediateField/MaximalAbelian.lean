/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.FieldTheory.Galois.Abelian
public import Iwasawalib.FieldTheory.IntermediateField.MaximalGaloisSExtension

@[expose] public section

/-!

# Maximal abelian subextension

- `IntermediateField.maximalAbelianExtension F K`, being an `IntermediateField F K`,
  is the maximal abelian subextension of `K / F`, which is defined to be
  the compositum of all abelian subextension of `K / F`.

- `IntermediateField.maximalAbelianSExtension F K S`, being an `IntermediateField F K`,
  is the maximal abelian `S`-subextension of `K / F`, which is defined to be
  the maximal Galois `S`-subextension of the maximal abelian subextension of `K / F`.

"le_lift_XXX_iff" and "lift_XXX_le_iff" are useful results since we often chain these constuctions
with `IntermediateField.lift`.

-/

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

namespace IntermediateField

/-- Unused result. TODO: go mathlib -/
theorem fixingSubgroup_restrictScalars
    (K : Type*) {L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L]
    [Algebra K L'] [Algebra L' L] [IsScalarTower K L' L] [Normal K L] (E : IntermediateField L' L) :
    (E.restrictScalars K).fixingSubgroup =
    E.fixingSubgroup.map (restrictRestrictAlgEquivMapHom K L L' L) := by
  ext f
  simp only [mem_fixingSubgroup_iff, mem_restrictScalars, restrictRestrictAlgEquivMapHom,
    AlgEquiv.restrictNormalHom_id, MonoidHom.CompTriple.comp_eq, Subgroup.mem_map,
    MulSemiringAction.toAlgAut_apply]
  refine ⟨fun h ↦ ?_, fun ⟨g, h1, h2⟩ ↦ by simpa [← h2]⟩
  let g : Gal(L/L') := {
    toRingEquiv := f.toRingEquiv
    commutes' := fun x ↦ h _ (algebraMap_mem E x)
  }
  exact ⟨g, by simpa [g], by ext; simp [g]⟩

/-! ### Maximal abelian subextension -/

/-- The maximal abelian subextension of `K / F` is the compositum of all
abelian subextension of `K / F`. -/
def maximalAbelianExtension : IntermediateField F K := sSup {E | IsAbelianGalois F E}

instance isAbelianGalois_maximalAbelianExtension :
    IsAbelianGalois F (maximalAbelianExtension F K) := by
  rw [maximalAbelianExtension, sSup_eq_iSup']
  have (E : {E : IntermediateField F K | IsAbelianGalois F E}) : IsAbelianGalois F E.1 := E.2
  infer_instance

variable {F K} in
theorem le_maximalAbelianExtension (E : IntermediateField F K) [IsAbelianGalois F E] :
    E ≤ maximalAbelianExtension F K :=
  le_sSup ‹_›

variable {F K} in
theorem le_maximalAbelianExtension_iff (E : IntermediateField F K) :
    E ≤ maximalAbelianExtension F K ↔ IsAbelianGalois F E := by
  refine ⟨fun h ↦ ?_, fun _ ↦ E.le_maximalAbelianExtension⟩
  have : IsAbelianGalois F (extendScalars h) := isAbelianGalois_maximalAbelianExtension F K
  exact .tower_bot F E (extendScalars h)

variable {F K} in
theorem maximalAbelianExtension_le_iff (E : IntermediateField F K) :
    maximalAbelianExtension F K ≤ E ↔
      ∀ E' : IntermediateField F K, IsAbelianGalois F E' → E' ≤ E :=
  ⟨fun h E' _ ↦ E'.le_maximalAbelianExtension.trans h, sSup_le⟩

variable {F K} in
theorem le_lift_maximalAbelianExtension_iff (L E : IntermediateField F K) :
    E ≤ lift (maximalAbelianExtension F L) ↔ E ≤ L ∧ IsAbelianGalois F E := by
  refine ⟨fun h ↦ ⟨h.trans (lift_le _), ?_⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  · have := IsAbelianGalois.of_algEquiv (liftAlgEquiv (maximalAbelianExtension F L))
    exact .of_algEquiv (restrict_algEquiv h).symm
  · have := IsAbelianGalois.of_algEquiv (restrict_algEquiv h1)
    have := le_maximalAbelianExtension (restrict h1)
    intro x h
    have := @this ⟨x, h1 h⟩ ((mem_restrict h1 _).2 h)
    rwa [← mem_lift] at this

variable {F K} in
theorem lift_maximalAbelianExtension_le_iff (L E : IntermediateField F K) :
    lift (maximalAbelianExtension F L) ≤ E ↔
      ∀ E' : IntermediateField F K, E' ≤ L → IsAbelianGalois F E' → E' ≤ E :=
  ⟨fun h _ h2 h3 ↦ ((le_lift_maximalAbelianExtension_iff L _).2 ⟨h2, h3⟩).trans h,
    fun h ↦ h _ (lift_le ..) (.of_algEquiv (liftAlgEquiv _))⟩

theorem maximalAbelianExtension_eq_top [IsAbelianGalois F K] : maximalAbelianExtension F K = ⊤ := by
  simpa only [eq_top_iff] using le_maximalAbelianExtension (⊤ : IntermediateField F K)

variable {F K} in
theorem maximalAbelianExtension_eq_top_iff :
    maximalAbelianExtension F K = ⊤ ↔ IsAbelianGalois F K :=
  ⟨fun h ↦ @IsAbelianGalois.of_algEquiv F _ _ _ K _ _ _
    (h ▸ isAbelianGalois_maximalAbelianExtension F K) topEquiv,
      fun _ ↦ maximalAbelianExtension_eq_top ..⟩

variable {F K} in
theorem sup_le_maximalAbelianExtension {E1 E2 : IntermediateField F K}
    (h1 : E1 ≤ maximalAbelianExtension F K) (h2 : E2 ≤ maximalAbelianExtension F K) :
    E1 ⊔ E2 ≤ maximalAbelianExtension F K := by
  rw [le_maximalAbelianExtension_iff] at h1 h2 ⊢
  infer_instance

variable {F K} in
theorem iSup_le_maximalAbelianExtension {ι : Type*} {E : ι → IntermediateField F K}
    (h : ∀ i, E i ≤ maximalAbelianExtension F K) : ⨆ i, E i ≤ maximalAbelianExtension F K := by
  simp_rw [le_maximalAbelianExtension_iff] at h ⊢
  infer_instance

private theorem commutator_le_fixingSubgroup_maximalAbelianExtension [IsGalois F K] :
    commutator Gal(K/F) ≤ (maximalAbelianExtension F K).fixingSubgroup := by
  have h1 : (maximalAbelianExtension F K).fixingSubgroup =
      ⨅ (E : IntermediateField F K) (_ : IsAbelianGalois F E), E.fixingSubgroup :=
    le_antisymm (le_iInf₂ fun E _ ↦ (fixingSubgroup_le (le_maximalAbelianExtension E)))
      (iInf₂_le _ (by exact isAbelianGalois_maximalAbelianExtension F K))
  have h2 (E : IntermediateField F K) (_ : IsAbelianGalois F E) :
      commutator Gal(K/F) ≤ E.fixingSubgroup := by
    rw [← restrictNormalHom_ker, commutator_eq_normalClosure]
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨_, _, rfl⟩
    simp [commutatorElement_def]
  simpa only [h1] using le_iInf₂ h2

private theorem isAbelianGalois_fixedField_topologicalClosure_commutator [IsGalois F K] :
    IsAbelianGalois F (fixedField (commutator Gal(K/F)).topologicalClosure) := by
  set G := (commutator Gal(K/F)).topologicalClosure
  have : G.Normal := Subgroup.is_normal_topologicalClosure _
  have h_surjective := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := fixedField G) K
  have h_ker := (fixedField G).restrictNormalHom_ker
  simp only [InfiniteGalois.fixingSubgroup_fixedField ⟨G, isClosed_closure⟩] at h_ker
  have := IsGalois.of_fixedField_normal_subgroup G
  have : IsMulCommutative Gal(fixedField G/F) := by
    refine ⟨⟨fun x y ↦ ?_⟩⟩
    obtain ⟨x', hx'⟩ := h_surjective x
    obtain ⟨y', hy'⟩ := h_surjective y
    have : x' * y' * x'⁻¹ * y'⁻¹ ∈ G :=
      Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator (by simp) (by simp))
    simpa [← h_ker, hx', hy', ← commutatorElement_eq_one_iff_mul_comm] using this
  exact ⟨⟩

theorem fixingSubgroup_maximalAbelianExtension [IsGalois F K] :
    (maximalAbelianExtension F K).fixingSubgroup = (commutator Gal(K/F)).topologicalClosure := by
  refine le_antisymm ?_ (closure_minimal (commutator_le_fixingSubgroup_maximalAbelianExtension F K)
    (InfiniteGalois.fixingSubgroup_isClosed _))
  set G := (commutator Gal(K/F)).topologicalClosure
  have := isAbelianGalois_fixedField_topologicalClosure_commutator F K
  simpa only [InfiniteGalois.fixingSubgroup_fixedField ⟨G, isClosed_closure⟩] using
    fixingSubgroup_antitone (le_maximalAbelianExtension (fixedField G))

theorem fixingSubgroup_maximalAbelianExtension_of_finiteDimensional
    [IsGalois F K] [FiniteDimensional F K] :
    (maximalAbelianExtension F K).fixingSubgroup = commutator Gal(K/F) := by
  rw [fixingSubgroup_maximalAbelianExtension]
  exact SetLike.coe_injective (by simp)

/-- Suppose `L / K / F` is a field extension tower, such that `L / F` and `K / F` are Galois.
Let `H / K` be the maximal abelian subextension of `L / K`. Then `H / F` is also Galois. -/
theorem isGalois_maximalAbelianExtension_of_isGalois
    (L : Type*) [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
    [IsGalois F L] [IsGalois F K] : IsGalois F (maximalAbelianExtension K L) := by
  set H := maximalAbelianExtension K L
  suffices Normal F H by
    have := IsGalois.tower_top_of_isGalois F K L
    have := H.isSeparable_tower_bot
    have := Algebra.IsSeparable.trans F K H
    exact ⟨⟩
  change Normal F (restrictScalars F H)
  rw [normal_iff_forall_map_le']
  intro σ
  let σH := ((restrictScalars F H).map (AlgHomClass.toAlgHom σ)).toSubfield.toIntermediateField
      fun (x : K) ↦ by
    simp only [toSubfield_map, AlgHomClass.toRingHom_toAlgHom, restrictScalars_toSubfield,
      Subfield.mem_map, mem_toSubfield, RingHom.coe_coe]
    use algebraMap K L (σ.symm.restrictNormal K x), algebraMap_mem ..
    simp
  suffices σH ≤ H from fun x hx ↦ this hx
  let f := (σ.restrictNormal K).toRingEquiv
  let g : H ≃+* σH := ((restrictScalars F H).equivMap (AlgHomClass.toAlgHom σ)).toRingEquiv
  have hcomp : (algebraMap K σH).comp f = RingHom.comp g (algebraMap K H) := by
    ext x
    simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, SubalgebraClass.coe_algebraMap,
      AlgEquiv.restrictNormal_commutes, f, g]
    rfl
  have : IsAbelianGalois K σH := .of_equiv_equiv hcomp
  exact le_maximalAbelianExtension ..

/-! ### Maximal abelian `S`-subextension -/

variable (S : Set ℕ) (p : ℕ) [Fact p.Prime]

/-- The maximal abelian `S`-subextension of `K / F` is defined to be the maximal Galois
`S`-subextension of the maximal abelian subextension of `K / F`. -/
def maximalAbelianSExtension : IntermediateField F K :=
  lift (maximalGaloisSExtension F (maximalAbelianExtension F K) S)

instance isAbelianGalois_maximalAbelianSExtension :
    IsAbelianGalois F (maximalAbelianSExtension F K S) :=
  .of_algEquiv (liftAlgEquiv _)

instance isSExtension_maximalAbelianSExtension :
    IsSExtension F (maximalAbelianSExtension F K S) S :=
  .of_algEquiv S (liftAlgEquiv _)

/-- The maximal abelian `S`-subextension of `K / F` is equal to
the compositum of all abelian subextensions `E` of `K / F` which are `S`-extensions. -/
theorem maximalAbelianSExtension_eq_sSup : maximalAbelianSExtension F K S =
    sSup {E : IntermediateField F K | IsAbelianGalois F E ∧ IsSExtension F E S} := by
  refine le_antisymm (le_sSup ⟨inferInstance, inferInstance⟩) (sSup_le fun E ⟨_, _⟩ ↦ ?_)
  rw [maximalAbelianSExtension]
  apply le_lift_maximalGaloisSExtension
  apply le_maximalAbelianExtension

/-- The maximal abelian `S`-subextension of `K / F` is equal to
the compositum of all finite abelian subextensions `E` of `K / F` which are `S`-extensions. -/
theorem maximalAbelianSExtension_eq_sSup_finiteDimensional :
    maximalAbelianSExtension F K S = sSup {E : IntermediateField F K |
      FiniteDimensional F E ∧ IsAbelianGalois F E ∧ IsSExtension F E S} := by
  rw [maximalAbelianSExtension_eq_sSup]
  refine le_antisymm (sSup_le fun E ⟨_, _⟩ ↦ ?_) (sSup_le fun E ⟨_, h⟩ ↦ le_sSup h)
  rw [E.eq_sSup_of_isGalois_of_isSExtension S]
  refine sSup_le fun E' ⟨h, h1, h2, h3⟩ ↦ le_sSup ⟨h1, ?_, h3⟩
  have := IsAbelianGalois.tower_bot F (restrict h) E
  exact .of_algEquiv (restrict_algEquiv h).symm

variable {F K} in
theorem le_maximalAbelianSExtension (E : IntermediateField F K) [IsAbelianGalois F E]
    [IsSExtension F E S] : E ≤ maximalAbelianSExtension F K S := by
  rw [maximalAbelianSExtension_eq_sSup]
  exact le_sSup ⟨‹_›, ‹_›⟩

variable {F K p} in
theorem le_maximalAbelianSExtension_singleton (E : IntermediateField F K) [IsAbelianGalois F E]
    (h : ∃ n, Module.finrank F E = p ^ n) : E ≤ maximalAbelianSExtension F K {p} := by
  have := isSExtension_singleton_of_exists_finrank_eq_pow _ _ _ h
  exact le_maximalAbelianSExtension _ E

variable {F K S} in
theorem le_maximalAbelianSExtension_iff (E : IntermediateField F K) :
    E ≤ maximalAbelianSExtension F K S ↔ IsAbelianGalois F E ∧ IsSExtension F E S := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _⟩ ↦ E.le_maximalAbelianSExtension S⟩
  have := IsAbelianGalois.tower_bot F (restrict h) (maximalAbelianSExtension F K S)
  have := IsSExtension.tower_bot F (restrict h) S (maximalAbelianSExtension F K S)
  exact ⟨.of_algEquiv (restrict_algEquiv h).symm, .of_algEquiv S (restrict_algEquiv h).symm⟩

variable {F K S} in
theorem maximalAbelianSExtension_le_iff (E : IntermediateField F K) :
    maximalAbelianSExtension F K S ≤ E ↔
      ∀ E' : IntermediateField F K, IsAbelianGalois F E' → IsSExtension F E' S → E' ≤ E := by
  refine ⟨fun h E' _ _ ↦ (E'.le_maximalAbelianSExtension S).trans h, fun h ↦ ?_⟩
  rw [maximalAbelianSExtension_eq_sSup]
  exact sSup_le fun _ ⟨h1, h2⟩ ↦ h _ h1 h2

variable {F K} in
theorem le_lift_maximalAbelianSExtension {L E : IntermediateField F K} (h : E ≤ L)
    [IsAbelianGalois F E] [IsSExtension F E S] : E ≤ lift (maximalAbelianSExtension F L S) := by
  have := IsAbelianGalois.of_algEquiv (restrict_algEquiv h)
  have := IsSExtension.of_algEquiv S (restrict_algEquiv h)
  have := le_maximalAbelianSExtension S (restrict h)
  intro x h'
  have := @this ⟨x, h h'⟩ ((mem_restrict h _).2 h')
  rwa [← mem_lift] at this

variable {F K S} in
theorem le_lift_maximalAbelianSExtension_iff (L E : IntermediateField F K) :
    E ≤ lift (maximalAbelianSExtension F L S) ↔
      E ≤ L ∧ IsAbelianGalois F E ∧ IsSExtension F E S := by
  refine ⟨fun h ↦ ⟨h.trans (lift_le _), ?_⟩, fun ⟨h, _, _⟩ ↦ le_lift_maximalAbelianSExtension S h⟩
  have := IsSExtension.of_algEquiv S (liftAlgEquiv (maximalAbelianSExtension F L S))
  have := IsSExtension.tower_bot F (restrict h) S (lift (maximalAbelianSExtension F L S))
  have := IsAbelianGalois.of_algEquiv (liftAlgEquiv (maximalAbelianSExtension F L S))
  have := IsAbelianGalois.tower_bot F (restrict h) (lift (maximalAbelianSExtension F L S))
  exact ⟨.of_algEquiv (restrict_algEquiv h).symm, .of_algEquiv S (restrict_algEquiv h).symm⟩

variable {F K S} in
theorem lift_maximalAbelianSExtension_le_iff (L E : IntermediateField F K) :
    lift (maximalAbelianSExtension F L S) ≤ E ↔
      ∀ E' : IntermediateField F K, E' ≤ L → IsAbelianGalois F E' → IsSExtension F E' S → E' ≤ E :=
  ⟨fun h _ h2 _ _ ↦ (le_lift_maximalAbelianSExtension S h2).trans h,
    fun h ↦ h _ (lift_le ..) (.of_algEquiv (liftAlgEquiv _)) (.of_algEquiv S (liftAlgEquiv _))⟩

variable {F K} in
theorem lift_maximalAbelianSExtension_eq_sSup (L : IntermediateField F K) :
    lift (maximalAbelianSExtension F L S) = sSup {E : IntermediateField F K |
      E ≤ L ∧ IsAbelianGalois F E ∧ IsSExtension F E S} := by
  refine le_antisymm ?_ (sSup_le fun E ⟨h, _, _⟩ ↦ le_lift_maximalAbelianSExtension S h)
  rw [lift_maximalAbelianSExtension_le_iff]
  exact fun E' h1 h2 h3 ↦ le_sSup ⟨h1, h2, h3⟩

variable {F K} in
theorem lift_maximalAbelianSExtension_eq_sSup_finiteDimensional (L : IntermediateField F K) :
    lift (maximalAbelianSExtension F L S) = sSup {E : IntermediateField F K |
      E ≤ L ∧ FiniteDimensional F E ∧ IsAbelianGalois F E ∧ IsSExtension F E S} := by
  rw [lift_maximalAbelianSExtension_eq_sSup]
  refine le_antisymm (sSup_le fun E ⟨h, _, _⟩ ↦ ?_) (sSup_le fun E ⟨h, _, h2⟩ ↦ le_sSup ⟨h, h2⟩)
  rw [E.eq_sSup_of_isGalois_of_isSExtension S]
  refine sSup_le fun _ ⟨h1, h2, _, h4⟩ ↦ le_sSup ⟨h1.trans h, h2, ?_, h4⟩
  have := IsAbelianGalois.tower_bot F (restrict h1) E
  exact .of_algEquiv (restrict_algEquiv h1).symm

theorem maximalAbelianSExtension_le_maximalAbelianExtension :
    maximalAbelianSExtension F K S ≤ maximalAbelianExtension F K := lift_le ..

theorem maximalAbelianSExtension_le_maximalGaloisSExtension :
    maximalAbelianSExtension F K S ≤ maximalGaloisSExtension F K S := by
  rw [maximalAbelianSExtension_eq_sSup, maximalGaloisSExtension, sSup_le_iff]
  exact fun E ⟨_, h⟩ ↦ le_sSup ⟨inferInstance, h⟩

theorem maximalAbelianSExtension_eq_maximalGaloisSExtension [IsAbelianGalois F K] :
    maximalAbelianSExtension F K S = maximalGaloisSExtension F K S := by
  have h1 (E : IntermediateField F K) : IsAbelianGalois F E := inferInstance
  have h2 (E : IntermediateField F K) : IsGalois F E := inferInstance
  simp only [maximalAbelianSExtension_eq_sSup, maximalGaloisSExtension, h1, h2]

/-- Suppose `L / K / F` is a field extension tower, such that `L / F` and `K / F` are Galois.
Let `H / K` be the maximal abelian `S`-subextension of `L / K`. Then `H / F` is also Galois. -/
theorem isGalois_maximalAbelianSExtension_of_isGalois
    (L : Type*) [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
    [IsGalois F L] [IsGalois F K] : IsGalois F (maximalAbelianSExtension K L S) := by
  have := isGalois_maximalAbelianExtension_of_isGalois F K L
  have := isGalois_maximalGaloisSExtension_of_isGalois F K S (maximalAbelianExtension K L)
  exact .of_algEquiv ((liftAlgEquiv _).restrictScalars F)

section FiniteDimensional

variable [FiniteDimensional F K]

theorem exists_finrank_maximalAbelianSExtension_singleton_eq_pow :
    ∃ n, Module.finrank F (maximalAbelianSExtension F K {p}) = p ^ n :=
  exists_finrank_eq_pow_of_le_maximalGaloisSExtension_singleton
    (maximalAbelianSExtension_le_maximalGaloisSExtension ..)

end FiniteDimensional

end IntermediateField
