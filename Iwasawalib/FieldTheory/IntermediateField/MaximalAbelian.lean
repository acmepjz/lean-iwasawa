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

-/

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

namespace IntermediateField

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

theorem fixingSubgroup_maximalAbelianExtension_of_finiteDimensional
    [IsGalois F K] [FiniteDimensional F K] :
    (maximalAbelianExtension F K).fixingSubgroup = commutator Gal(K/F) := by
  sorry

theorem fixingSubgroup_maximalAbelianExtension [IsGalois F K] :
    (maximalAbelianExtension F K).fixingSubgroup = (commutator Gal(K/F)).topologicalClosure := by
  sorry

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

/-- The maximal abelian `S`-subextension of `K / F` is equal to
the compositum of all finite abelian subextensions `E` of `K / F` such that the prime factors of
`[E : F]` is contained in `S`. -/
theorem maximalAbelianSExtension_eq_sSup : maximalAbelianSExtension F K S =
    sSup {E : IntermediateField F K | FiniteDimensional F E ∧ IsAbelianGalois F E ∧
      ↑(Module.finrank F E).primeFactors ⊆ S} := by
  apply le_antisymm
  · simp_rw [maximalAbelianSExtension, maximalGaloisSExtension, sSup_eq_iSup', iSup_eq_adjoin,
      lift_adjoin]
    apply adjoin.mono
    intro x hx
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_image, Set.mem_iUnion, SetLike.mem_coe,
      Subtype.exists, exists_prop, exists_and_right, exists_eq_right] at hx ⊢
    obtain ⟨_, E, ⟨_, _, hS⟩, h⟩ := hx
    use lift E, ⟨(liftAlgEquiv E).toLinearEquiv.finiteDimensional, .of_algEquiv (liftAlgEquiv E), by
      rwa [(liftAlgEquiv E).toLinearEquiv.finrank_eq] at hS⟩
    rwa [← mem_lift] at h
  · rw [sSup_le_iff]
    rintro E ⟨_, _, hS⟩
    have h1 := E.le_maximalAbelianExtension
    let E' := restrict h1
    suffices E' ≤ maximalGaloisSExtension F _ S by
      intro x hx
      rw [maximalAbelianSExtension]
      exact (mem_lift _).2 <| this <| (mem_restrict h1 ⟨x, h1 hx⟩).2 hx
    have : FiniteDimensional F E' := (restrict_algEquiv h1).toLinearEquiv.finiteDimensional
    have : IsAbelianGalois F E' := .of_algEquiv (restrict_algEquiv h1)
    rw [(restrict_algEquiv h1).toLinearEquiv.finrank_eq] at hS
    exact le_maximalGaloisSExtension E' hS

instance isAbelianGalois_maximalAbelianSExtension :
    IsAbelianGalois F (maximalAbelianSExtension F K S) :=
  .of_algEquiv (liftAlgEquiv _)

variable {F K S} in
theorem le_maximalAbelianSExtension (E : IntermediateField F K) [FiniteDimensional F E]
    [IsAbelianGalois F E] (h : ↑(Module.finrank F E).primeFactors ⊆ S) :
    E ≤ maximalAbelianSExtension F K S := by
  rw [maximalAbelianSExtension_eq_sSup]
  exact le_sSup ⟨‹_›, ‹_›, h⟩

variable {F K p} in
theorem le_maximalAbelianSExtension_singleton (E : IntermediateField F K) [IsAbelianGalois F E]
    (h : ∃ n, Module.finrank F E = p ^ n) : E ≤ maximalAbelianSExtension F K {p} := by
  rw [maximalAbelianSExtension_eq_sSup]
  obtain ⟨n, hn⟩ := h
  refine le_sSup ⟨.of_finrank_pos (by simp [hn, ‹Fact p.Prime›.out.pos]), ‹_›, ?_⟩
  rcases eq_or_ne n 0 with rfl | hne
  · simp [hn]
  · simp [hn, Nat.primeFactors_prime_pow hne Fact.out]

theorem maximalAbelianSExtension_le_maximalAbelianExtension :
    maximalAbelianSExtension F K S ≤ maximalAbelianExtension F K := lift_le ..

theorem maximalAbelianSExtension_le_maximalGaloisSExtension :
    maximalAbelianSExtension F K S ≤ maximalGaloisSExtension F K S := by
  rw [maximalAbelianSExtension_eq_sSup, maximalGaloisSExtension, sSup_le_iff]
  rintro E ⟨_, _, hS⟩
  exact le_sSup ⟨inferInstance, inferInstance, hS⟩

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
