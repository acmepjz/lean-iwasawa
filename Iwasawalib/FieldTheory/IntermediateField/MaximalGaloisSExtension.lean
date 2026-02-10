/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Data.Nat.Factorization.PrimePow
public import Iwasawalib.FieldTheory.Galois.Abelian
public import Iwasawalib.GroupTheory.Torsion

@[expose] public section

/-!

# Maximal Galois `S`-subextension

Let `S` be a set of prime numbers. The maximal Galois `S`-subextension of `K / F` is defined to be
the compositum of all finite Galois subextensions `E` of `K / F` such that the prime factors of
`[E : F]` is contained in `S`.

-/

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

namespace IntermediateField

variable (S : Set ℕ) (p : ℕ) [Fact p.Prime]

/-- The maximal Galois `S`-subextension of `K / F` is defined to be
the compositum of all finite Galois subextensions `E` of `K / F` such that the prime factors of
`[E : F]` is contained in `S`. -/
def maximalGaloisSExtension : IntermediateField F K :=
  sSup {E | FiniteDimensional F E ∧ IsGalois F E ∧ ↑(Module.finrank F E).primeFactors ⊆ S}

instance isGalois_maximalGaloisSExtension : IsGalois F (maximalGaloisSExtension F K S) := by
  rw [maximalGaloisSExtension, sSup_eq_iSup']
  have (E : {E : IntermediateField F K | FiniteDimensional F E ∧ IsGalois F E ∧
    ↑(Module.finrank F E).primeFactors ⊆ S}) : IsGalois F E.1 := E.2.2.1
  exact ⟨⟩

variable {F K S} in
theorem le_maximalGaloisSExtension (E : IntermediateField F K) [FiniteDimensional F E]
    [IsGalois F E] (h : ↑(Module.finrank F E).primeFactors ⊆ S) :
    E ≤ maximalGaloisSExtension F K S :=
  le_sSup ⟨‹_›, ‹_›, h⟩

variable {F K p} in
theorem le_maximalGaloisSExtension_singleton (E : IntermediateField F K) [IsGalois F E]
    (h : ∃ n, Module.finrank F E = p ^ n) : E ≤ maximalGaloisSExtension F K {p} := by
  obtain ⟨n, hn⟩ := h
  refine le_sSup ⟨.of_finrank_pos (by simp [hn, ‹Fact p.Prime›.out.pos]), ‹_›, ?_⟩
  rcases eq_or_ne n 0 with rfl | hne
  · simp [hn]
  · simp [hn, Nat.primeFactors_prime_pow hne Fact.out]

variable {S} in
theorem maximalGaloisSExtension_maximalGaloisSExtension_eq_top_of_subset
    {S' : Set ℕ} (hS : S ⊆ S') :
    maximalGaloisSExtension F (maximalGaloisSExtension F K S) S' = ⊤ := by
  rw [← lift_inj, lift_top]
  refine (lift_le _).antisymm ?_
  change adjoin .. ≤ lift (adjoin ..)
  rw [lift_adjoin]
  refine adjoin.mono _ _ _ fun x hx ↦ ?_
  simp only [Set.sSup_eq_sUnion, Set.sUnion_image, Set.mem_setOf_eq, Set.mem_image, Set.mem_iUnion,
    SetLike.mem_coe, exists_prop, Subtype.exists, exists_and_right, exists_eq_right] at hx ⊢
  obtain ⟨E, ⟨_, _, hE⟩, hx⟩ := hx
  have hE' := E.le_maximalGaloisSExtension hE
  refine ⟨hE' hx, restrict hE', ⟨?_, ?_, ?_⟩, by simp only [mem_restrict, hx]⟩
  · exact (restrict_algEquiv hE').toLinearEquiv.finiteDimensional
  · exact .of_algEquiv (restrict_algEquiv hE')
  · rw [← (restrict_algEquiv hE').toLinearEquiv.finrank_eq]
    exact hE.trans hS

/-- TODO: go mathlib below `exists_finset_of_mem_iSup` -/
theorem exists_finset_of_le_iSup {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
    {ι : Type*} {f : ι → IntermediateField F E} {x : IntermediateField F E} [FiniteDimensional F x]
    (hx : x ≤ ⨆ i, f i) : ∃ (s : Finset ι), x ≤ ⨆ i ∈ s, f i := by
  obtain ⟨n, t, ht⟩ := Module.Finite.exists_fin (R := F) (M := x)
  replace ht : Submodule.span F (x.val '' Set.range t) = x.toSubmodule := by
    convert ← congr(Submodule.map x.val.toLinearMap $(ht))
    · exact LinearMap.map_span x.val.toLinearMap _
    · exact x.toSubmodule.map_subtype_top
  choose k hk using fun i ↦ exists_finset_of_mem_iSup (hx (t i).2)
  classical
  refine ⟨Finset.biUnion .univ k, fun y hy ↦ ?_⟩
  change y ∈ x.toSubmodule at hy
  rw [← ht] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    simp only [coe_val, Set.mem_image, Set.mem_range, exists_exists_eq_and] at hz
    obtain ⟨j, hj⟩ := hz
    exact (biSup_mono (f := f) (Finset.subset_biUnion_of_mem k (by simp))) (hj ▸ hk j)
  | zero => exact zero_mem _
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | smul _ _ _ h => exact smul_mem _ h

/-- TODO: go mathlib -/
theorem _root_.Nat.primeFactors_prod {ι : Type*} {f : ι → ℕ} {s : Finset ι} (h : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).primeFactors = s.biUnion fun i ↦ (f i).primeFactors := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert i t ht ih =>
    have h1 : f i ≠ 0 := by simpa using h i
    have h2 : ∀ i ∈ t, f i ≠ 0 := fun j hj ↦ by simpa [hj] using h j
    rw [Finset.biUnion_insert, Finset.prod_insert ht,
      Nat.primeFactors_mul h1 (by rwa [Finset.prod_ne_zero_iff]), ih h2]

variable {F K S} in
theorem primeFactors_finrank_subset_of_le_maximalGaloisSExtension
    {E : IntermediateField F K} (h : E ≤ maximalGaloisSExtension F K S) :
    ↑(Module.finrank F E).primeFactors ⊆ S := by
  by_cases hfin : FiniteDimensional F E
  · rw [maximalGaloisSExtension, sSup_eq_iSup'] at h
    obtain ⟨s, hs⟩ := exists_finset_of_le_iSup h
    rw [iSup_subtype' (p := fun i ↦ i ∈ s) (f := fun i _ ↦ i.1)] at hs
    set E' : IntermediateField F K := ⨆ x : { x // x ∈ s }, x.1.1
    have : Finite { x // x ∈ s } := s.finite_toSet
    have (x : { x // x ∈ s }) : FiniteDimensional F x.1.1 := x.1.2.1
    have (x : { x // x ∈ s }) : IsGalois F x.1.1 := x.1.2.2.1
    have : IsGalois F E' := ⟨⟩
    have h1 := finrank_dvd_of_le_right hs
    rw [← IsGalois.card_aut_eq_finrank F E'] at h1
    replace h1 := h1.trans <| Subgroup.card_dvd_of_injective (f := piRestrictNormalHom'
      (fun x : { x // x ∈ s } ↦ x.1.1) E' rfl) (injective_piRestrictNormalHom' ..)
    simp_rw [Nat.card_pi, IsGalois.card_aut_eq_finrank F _] at h1
    have h2 := Nat.primeFactors_mono h1 (by simp [Finset.prod_ne_zero_iff, Module.finrank_pos.ne'])
    rw [Nat.primeFactors_prod (by simp [Module.finrank_pos.ne'])] at h2
    grind
  simp [Module.finrank_of_infinite_dimensional hfin]

/-- TODO: go mathlib -/
theorem _root_.Nat.primeFactors_subset_singleton_iff_of_prime {p n : ℕ} (hp : p.Prime) :
    n.primeFactors ⊆ {p} ↔ n = 0 ∨ ∃ k, n = p ^ k := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · simp only [Finset.subset_singleton_iff, Nat.primeFactors_eq_empty] at h
    obtain (rfl | rfl) | hn := h
    · simp
    · exact .inr ⟨0, by simp⟩
    · obtain ⟨q, k, hq, hk, hn'⟩ := (isPrimePow_nat_iff n).1
        (isPrimePow_iff_card_primeFactors_eq_one.2 (by simp [hn]))
      rw [← hn', Nat.primeFactors_prime_pow hk.ne' hq, Finset.singleton_inj] at hn
      exact .inr ⟨k, by rw [← hn', hn]⟩
  · rintro (rfl | ⟨k, rfl⟩)
    · simp
    · rcases eq_or_ne k 0 with rfl | hne
      · simp
      · simp [Nat.primeFactors_prime_pow hne hp]

variable {F K p} in
theorem exists_finrank_eq_pow_of_le_maximalGaloisSExtension_singleton
    {E : IntermediateField F K} (h : E ≤ maximalGaloisSExtension F K {p}) [FiniteDimensional F E] :
    ∃ n, Module.finrank F E = p ^ n := by
  have := primeFactors_finrank_subset_of_le_maximalGaloisSExtension h
  norm_cast at this
  rw [Nat.primeFactors_subset_singleton_iff_of_prime Fact.out] at this
  simpa [Module.finrank_pos.ne'] using this

variable {F K S} in
theorem le_maximalGaloisSExtension_iff_of_finiteDimensional_of_isGalois
    (E : IntermediateField F K) [FiniteDimensional F E] [IsGalois F E] :
    E ≤ maximalGaloisSExtension F K S ↔ ↑(Module.finrank F E).primeFactors ⊆ S :=
  ⟨fun h ↦ E.primeFactors_finrank_subset_of_le_maximalGaloisSExtension h,
    fun h ↦ E.le_maximalGaloisSExtension h⟩

/-- Suppose `L / K / F` is a field extension tower, such that `L / F` and `K / F` are Galois.
Let `H / K` be the maximal Galois `S`-subextension of `L / K`. Then `H / F` is also Galois. -/
theorem isGalois_maximalGaloisSExtension_of_isGalois
    (L : Type*) [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
    [IsGalois F L] [IsGalois F K] : IsGalois F (maximalGaloisSExtension K L S) := by
  set H := maximalGaloisSExtension K L S
  suffices Normal F H by
    have := IsGalois.tower_top_of_isGalois F K L
    have := H.isSeparable_tower_bot
    have := Algebra.IsSeparable.trans F K H
    exact ⟨⟩
  change Normal F (restrictScalars F H)
  rw [normal_iff_forall_map_le']
  intro σ
  have h1 : (restrictScalars F H).map (AlgHomClass.toAlgHom σ) =
      ⨆ E : {E : IntermediateField K L | FiniteDimensional K E ∧ IsGalois K E ∧
        ↑(Module.finrank K E).primeFactors ⊆ S},
          (E.1.restrictScalars F).map (AlgHomClass.toAlgHom σ) := by
    apply toSubfield_injective
    simp only [maximalGaloisSExtension, sSup_eq_iSup', Set.coe_setOf, Set.mem_setOf_eq,
      iSup_eq_adjoin, toSubfield_map, AlgHomClass.toRingHom_toAlgHom, restrictScalars_toSubfield,
      adjoin_toSubfield, RingHom.map_field_closure, RingHom.coe_coe, coe_map, AlgHom.coe_coe,
      coe_restrictScalars, H]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_union, Set.mem_range, Set.mem_iUnion]
    refine ⟨fun ⟨y, h1, h2⟩ ↦ .inr ?_, ?_⟩
    · rcases h1 with (⟨z, rfl⟩ | ⟨E, h1⟩)
      · use ⟨⊥, inferInstance, inferInstance, by simp⟩, (algebraMap K L) z, by simp
      · use E, y
    · rintro (⟨y, rfl⟩ | ⟨E, y, h1, h2⟩)
      · use algebraMap F L y,
          .inl ⟨algebraMap F K y, by rw [← IsScalarTower.algebraMap_apply]⟩, by simp
      · use y, .inr ⟨E, h1⟩
  simp only [h1, iSup_le_iff, Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall, and_imp]
  intro E _ _ h2
  let σE := ((restrictScalars F E).map (AlgHomClass.toAlgHom σ)).toSubfield.toIntermediateField
      fun (x : K) ↦ by
    simp only [toSubfield_map, AlgHomClass.toRingHom_toAlgHom, restrictScalars_toSubfield,
      Subfield.mem_map, mem_toSubfield, RingHom.coe_coe]
    use algebraMap K L (σ.symm.restrictNormal K x), algebraMap_mem ..
    simp
  suffices σE ≤ H from fun x hx ↦ this hx
  let f := (σ.restrictNormal K).toRingEquiv
  let g : E ≃+* σE := ((restrictScalars F E).equivMap (AlgHomClass.toAlgHom σ)).toRingEquiv
  have hcomp : (algebraMap K σE).comp f = RingHom.comp g (algebraMap K E) := by
    ext x
    simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, SubalgebraClass.coe_algebraMap,
      AlgEquiv.restrictNormal_commutes, f, g]
    rfl
  have : IsGalois K σE := .of_equiv_equiv hcomp
  have : FiniteDimensional K σE := Module.rank_lt_aleph0_iff.1 <| by
    rw [← Algebra.rank_eq_of_equiv_equiv f g hcomp]
    exact Module.rank_lt_aleph0_iff.2 ‹_›
  apply le_maximalGaloisSExtension
  have := Nat.card_congr (AlgEquiv.autCongrOfSurjective f.surjective hcomp).toEquiv
  simp_rw [IsGalois.card_aut_eq_finrank] at this
  rwa [← this]

section FiniteDimensional

variable [FiniteDimensional F K]

theorem exists_finrank_maximalGaloisSExtension_singleton_eq_pow :
    ∃ n, Module.finrank F (maximalGaloisSExtension F K {p}) = p ^ n :=
  exists_finrank_eq_pow_of_le_maximalGaloisSExtension_singleton le_rfl

end FiniteDimensional

section FiniteAbelian

variable [FiniteDimensional F K] [IsAbelianGalois F K]

theorem fixingSubgroup_maximalGaloisSExtension_singleton :
    (maximalGaloisSExtension F K {p}).fixingSubgroup = CommGroup.primeToComponent Gal(K/F) p := by
  sorry

theorem finrank_maximalGaloisSExtension_singleton_top :
    Module.finrank (maximalGaloisSExtension F K {p}) K =
    Module.finrank F K / p ^ (Module.finrank F K).factorization p := by
  simp_rw [← IsGalois.card_fixingSubgroup_eq_finrank,
    fixingSubgroup_maximalGaloisSExtension_singleton,
    CommGroup.card_primeToComponent, IsGalois.card_aut_eq_finrank]

theorem finrank_maximalGaloisSExtension_singleton_bot :
    Module.finrank F (maximalGaloisSExtension F K {p}) =
    p ^ (Module.finrank F K).factorization p := by
  have h := (Nat.div_eq_of_eq_mul_left Module.finrank_pos
    (Module.finrank_mul_finrank F (maximalGaloisSExtension F K {p}) K).symm).symm
  rwa [finrank_maximalGaloisSExtension_singleton_top,
    Nat.div_div_self (Nat.ordProj_dvd ..) Module.finrank_pos.ne'] at h

theorem maximalGaloisSExtension_singleton_eq_bot_iff :
    maximalGaloisSExtension F K {p} = ⊥ ↔ ¬p ∣ Module.finrank F K := by
  simp [← finrank_eq_one_iff, finrank_maximalGaloisSExtension_singleton_bot, Module.finrank_pos.ne',
    Nat.factorization_eq_zero_iff, ‹Fact p.Prime›.out, ‹Fact p.Prime›.out.ne_one]

theorem not_dvd_finrank_maximalGaloisSExtension_singleton_top :
    ¬p ∣ Module.finrank (maximalGaloisSExtension F K {p}) K := by
  rw [finrank_maximalGaloisSExtension_singleton_top]
  exact Nat.not_dvd_ordCompl Fact.out Module.finrank_pos.ne'

end FiniteAbelian

end IntermediateField
