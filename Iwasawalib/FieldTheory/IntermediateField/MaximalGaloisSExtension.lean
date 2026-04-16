/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Data.Nat.Factorization.PrimePow
public import Iwasawalib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Iwasawalib.GroupTheory.Torsion

@[expose] public section

/-!

# Maximal Galois `S`-subextension

Let `S` be a set of prime numbers. The maximal Galois `S`-subextension of `K / F`
(`IntermediateField.maximalGaloisSExtension F K S`) is defined to be
the compositum of all finite Galois subextensions `E` of `K / F` such that the prime factors of
`[E : F]` is contained in `S`.

-/

variable (F K : Type*) [Field F] [Field K] [Algebra F K] (S : Set ℕ) (p : ℕ) [Fact p.Prime]

/-- TODO: go mathlib below `IntermediateField.exists_finset_of_mem_iSup` -/
theorem IntermediateField.exists_finset_of_le_iSup
    {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
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
theorem Nat.primeFactors_prod_eq_biUnion {ι : Type*} {f : ι → ℕ} {s : Finset ι}
    (h : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).primeFactors = s.biUnion fun i ↦ (f i).primeFactors := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert i t ht ih =>
    have h1 : f i ≠ 0 := by simpa using h i
    have h2 : ∀ i ∈ t, f i ≠ 0 := fun j hj ↦ by simpa [hj] using h j
    rw [Finset.biUnion_insert, Finset.prod_insert ht,
      Nat.primeFactors_mul h1 (by rwa [Finset.prod_ne_zero_iff]), ih h2]

/-- TODO: go mathlib -/
theorem Nat.primeFactors_subset_singleton_iff_of_prime {p n : ℕ} (hp : p.Prime) :
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

/-! ### Assertion that a field extension is `S`-extension -/

/-- `IsSExtension F K S` is a typeclass asserting that `K / F` is an `S`-extension, which means that
for any finite subextension `E / F` of `K / F`, the prime factors of `[E : F]` is contained in `S`.

Note that this does not exclude the case that `K / F` is a purely transcendental extension,
which is mathematically not interesting. -/
@[mk_iff]
class IsSExtension (S : Set ℕ) : Prop where
  primeFactors_subset_of_intermediateField_of_finiteDimensional (S) (E : IntermediateField F K)
    [FiniteDimensional F E] : ↑(Module.finrank F E).primeFactors ⊆ S

variable {F K} in
theorem IsSExtension.primeFactors_subset_of_intermediateField (E : IntermediateField F K)
    [IsSExtension F K S] : ↑(Module.finrank F E).primeFactors ⊆ S := by
  by_cases hfd : FiniteDimensional F E
  · exact primeFactors_subset_of_intermediateField_of_finiteDimensional S E
  · simp [Module.finrank_of_infinite_dimensional hfd]

theorem IsSExtension.primeFactors_subset [IsSExtension F K S] :
    ↑(Module.finrank F K).primeFactors ⊆ S := by
  simpa only [IntermediateField.topEquiv.toLinearEquiv.finrank_eq] using
    primeFactors_subset_of_intermediateField S (⊤ : IntermediateField F K)

theorem isSExtension_iff_of_finiteDimensional [FiniteDimensional F K] :
    IsSExtension F K S ↔ ↑(Module.finrank F K).primeFactors ⊆ S := by
  refine ⟨fun _ ↦ IsSExtension.primeFactors_subset F K S, fun H ↦ ⟨fun E _ ↦ ?_⟩⟩
  rw [← Module.finrank_mul_finrank F E K,
    Nat.primeFactors_mul Module.finrank_pos.ne' Module.finrank_pos.ne', Finset.coe_union,
    Set.union_subset_iff] at H
  exact H.1

theorem isSExtension_singleton_iff_of_finiteDimensional [FiniteDimensional F K] :
    IsSExtension F K {p} ↔ ∃ n, Module.finrank F K = p ^ n := by
  rw [isSExtension_iff_of_finiteDimensional]
  norm_cast
  simp [Nat.primeFactors_subset_singleton_iff_of_prime Fact.out, Module.finrank_pos.ne']

theorem isSExtension_singleton_of_exists_finrank_eq_pow
    (h : ∃ n, Module.finrank F K = p ^ n) : IsSExtension F K {p} := by
  have : FiniteDimensional F K := .of_finrank_pos <| by
    obtain ⟨n, hn⟩ := h
    simp [hn, ‹Fact p.Prime›.out.pos]
  rwa [isSExtension_singleton_iff_of_finiteDimensional]

open scoped IntermediateField in
/-- `K / F` is an `S`-extension if and only if for any `x` in `K`, `F⟮x⟯ / F` is
(either an infinite extension or) of prime factors of degree contained in `S`. -/
theorem isSExtension_iff_primeFactors_adjoin_simple_subset :
    IsSExtension F K S ↔ ∀ x : K, ↑(Module.finrank F F⟮x⟯).primeFactors ⊆ S := by
  refine ⟨fun _ _ ↦ IsSExtension.primeFactors_subset_of_intermediateField S _,
    fun H ↦ ⟨fun E _ ↦ ?_⟩⟩
  let L := IntermediateField.lift (separableClosure F E)
  have : FiniteDimensional F L :=
    (IntermediateField.liftAlgEquiv (separableClosure F E)).toLinearEquiv.finiteDimensional
  have : Algebra.IsSeparable F L := AlgEquiv.Algebra.isSeparable
    (IntermediateField.liftAlgEquiv (separableClosure F E))
  obtain ⟨x, hx⟩ := Field.exists_primitive_element F L
  replace hx : F⟮x.1⟯ = L := by simpa using congr(IntermediateField.lift $(hx))
  have H2 := H x
  rw [hx, ← (IntermediateField.liftAlgEquiv (separableClosure F E)).toLinearEquiv.finrank_eq] at H2
  rw [← Module.finrank_mul_finrank F (separableClosure F E) E,
    Nat.primeFactors_mul Module.finrank_pos.ne' Module.finrank_pos.ne', Finset.coe_union]
  refine Set.union_subset H2 ?_
  change ↑(Field.finInsepDegree F E).primeFactors ⊆ S
  by_cases hsep : Field.finInsepDegree F E = 1
  · simp [hsep]
  obtain ⟨q, hq⟩ := ExpChar.exists F
  have hq : q.Prime := by
    rcases hq with _ | _
    · simp [Algebra.IsSeparable.finInsepDegree_eq] at hsep
    · assumption
  suffices q ∈ S by
    obtain ⟨n, hn⟩ := finInsepDegree_eq_pow F E q
    rw [hn, Nat.primeFactors_prime_pow (fun h' ↦ by simp [hn, h'] at hsep) hq]
    simpa
  rw [← isSeparable_iff_finInsepDegree_eq_one, ← IntermediateField.adjoin_self F E,
    IntermediateField.isSeparable_adjoin_iff_isSeparable] at hsep
  push Not at hsep
  obtain ⟨y, hy, hnsep⟩ := hsep
  rw [← IntermediateField.isSeparable_adjoin_simple_iff_isSeparable,
    isSeparable_iff_finInsepDegree_eq_one] at hnsep
  have : FiniteDimensional F F⟮y⟯ := by
    have : F⟮y⟯.toSubmodule ≤ E.toSubmodule := IntermediateField.adjoin_simple_le_iff.2 hy
    exact Submodule.finiteDimensional_of_le this
  obtain ⟨n, hn⟩ := finInsepDegree_eq_pow F F⟮y⟯ q
  have H3 := H y
  rw [← Field.finSepDegree_mul_finInsepDegree, hn,
    Nat.primeFactors_mul NeZero.out (by simp [hq.ne_zero]), Finset.coe_union, Set.union_subset_iff,
    Nat.primeFactors_prime_pow (fun h' ↦ by simp [hn, h'] at hnsep) hq] at H3
  simpa using H3.2

instance isSExtension_self : IsSExtension F F S := by
  refine ⟨fun E _ ↦ ?_⟩
  rw [Subsingleton.elim E ⊥]
  simp

namespace IsSExtension

variable {F K} in
theorem of_algEquiv {K' : Type*} [Field K'] [Algebra F K'] (f : K ≃ₐ[F] K')
    [IsSExtension F K S] : IsSExtension F K' S := by
  refine ⟨fun E _ ↦ ?_⟩
  simpa only [(E.equivMap f.symm.toAlgHom).toLinearEquiv.finrank_eq] using
    primeFactors_subset_of_intermediateField S (E.map f.symm.toAlgHom)

theorem of_equiv_equiv
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {M N : Type*} [Field M] [Field N] [Algebra M N]
    {f : F ≃+* M} {g : E ≃+* N}
    (hcomp : (algebraMap M N).comp f = RingHom.comp g (algebraMap F E)) [IsSExtension F E S] :
    IsSExtension M N S := by
  refine ⟨fun L _ ↦ ?_⟩
  let K : IntermediateField F E := {
    __ := L.toSubfield.comap g.toRingHom
    algebraMap_mem' r := by
      have := congr($(hcomp) r)
      simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at this
      simp [← this]
  }
  let g' : K ≃+* L := (g.subringMap (s := K.toSubfield.toSubring)).trans <|
    RingEquiv.subringCongr <| Subring.map_comap_eq_self_of_surjective (f := g.toRingHom)
      g.surjective L.toSubfield.toSubring
  have := Algebra.finrank_eq_of_equiv_equiv f g' <| by
    ext x
    have := congr($(hcomp) x)
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at this
    simpa
  simpa only [this] using primeFactors_subset_of_intermediateField S K

section Tower

variable (L : Type*) [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L]

/-- If `L / K / F` is a field extension tower, `L / F` is an `S`-extension,
then `K / F` is an `S`-extension. -/
theorem tower_bot [IsSExtension F L S] : IsSExtension F K S := by
  refine ⟨fun E _ ↦ ?_⟩
  simpa only [(E.equivMap (IsScalarTower.toAlgHom F K L)).toLinearEquiv.finrank_eq] using
    primeFactors_subset_of_intermediateField S (E.map (IsScalarTower.toAlgHom F K L))

open scoped IntermediateField in
/-- If `L / K / F` is a field extension tower, `L / F` is an `S`-extension, `K / F` is algebraic,
then `L / K` is an `S`-extension. -/
theorem tower_top_of_isAlgebraic
    [IsSExtension F L S] [Algebra.IsAlgebraic F K] : IsSExtension K L S := by
  rw [isSExtension_iff_primeFactors_adjoin_simple_subset]
  intro x
  by_cases hfd : FiniteDimensional K K⟮x⟯
  · have halg : Algebra.IsAlgebraic K K⟮x⟯ := inferInstance
    simp only [IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic, Set.mem_singleton_iff,
      forall_eq] at halg
    let E := IntermediateField.adjoin F ((minpoly K x).coeffs : Set K)
    have hmp := minpoly.map_algebraMap (F := E) (E := K) (halg.restrictScalars E).isIntegral <| by
      rw [Polynomial.lifts_iff_coeff_lifts]
      refine fun n ↦ ⟨⟨(minpoly K x).coeff n, ?_⟩, rfl⟩
      by_cases hn : (minpoly K x).coeff n = 0
      · simp [hn]
      apply IntermediateField.subset_adjoin
      exact Polynomial.coeff_mem_coeffs hn
    replace hmp := congr(($hmp).natDegree)
    rw [Polynomial.natDegree_map, ← IntermediateField.adjoin.finrank halg.isIntegral,
      ← IntermediateField.adjoin.finrank (halg.restrictScalars E).isIntegral] at hmp
    have : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin <| by
      simp [Algebra.IsAlgebraic.isAlgebraic (R := F) (A := K), IsAlgebraic.isIntegral]
    have : FiniteDimensional E E⟮x⟯ := IntermediateField.finiteDimensional_adjoin <| by
      simpa using (halg.restrictScalars E).isIntegral
    have h : ↑(Module.finrank F E⟮x⟯).primeFactors ⊆ S :=
      IsSExtension.primeFactors_subset_of_intermediateField S (E⟮x⟯.restrictScalars F)
    rw [← Module.finrank_mul_finrank F E E⟮x⟯,
      Nat.primeFactors_mul Module.finrank_pos.ne' Module.finrank_pos.ne', Finset.coe_union,
      Set.union_subset_iff, hmp] at h
    exact h.2
  simp [Module.finrank_of_infinite_dimensional hfd]

open scoped IntermediateField in
/-- If `L / K / F` is a field extension tower, `L / K` and `K / F` are `S`-extensions,
`K / F` is algebraic, then `L / F` is an `S`-extension. -/
theorem trans_of_isAlgebraic
    [IsSExtension F K S] [IsSExtension K L S] [Algebra.IsAlgebraic F K] : IsSExtension F L S := by
  rw [isSExtension_iff_primeFactors_adjoin_simple_subset]
  intro x
  by_cases hfd : FiniteDimensional F F⟮x⟯
  · have halg : Algebra.IsAlgebraic F F⟮x⟯ := inferInstance
    simp only [IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic, Set.mem_singleton_iff,
      forall_eq] at halg
    -- partially copied from the proof of the previous theorem
    let E := IntermediateField.adjoin F ((minpoly K x).coeffs : Set K)
    have hmp := minpoly.map_algebraMap (F := E) (E := K) (halg.tower_top E).isIntegral <| by
      rw [Polynomial.lifts_iff_coeff_lifts]
      refine fun n ↦ ⟨⟨(minpoly K x).coeff n, ?_⟩, rfl⟩
      by_cases hn : (minpoly K x).coeff n = 0
      · simp [hn]
      apply IntermediateField.subset_adjoin
      exact Polynomial.coeff_mem_coeffs hn
    replace hmp := congr(($hmp).natDegree)
    rw [Polynomial.natDegree_map, ← IntermediateField.adjoin.finrank (halg.tower_top K).isIntegral,
      ← IntermediateField.adjoin.finrank (halg.tower_top E).isIntegral] at hmp
    have : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin <| by
      simp [Algebra.IsAlgebraic.isAlgebraic (R := F) (A := K), IsAlgebraic.isIntegral]
    have : FiniteDimensional K K⟮x⟯ := IntermediateField.finiteDimensional_adjoin <| by
      simpa using (halg.tower_top K).isIntegral
    have h3 : F⟮x⟯ ≤ E⟮x⟯.restrictScalars F := by simp [IntermediateField.adjoin_le_iff]
    have h4 := Nat.primeFactors_mono (IntermediateField.finrank_dvd_of_le_right h3) <| by
      have : FiniteDimensional E E⟮x⟯ := IntermediateField.finiteDimensional_adjoin <| by
        simpa using (halg.tower_top E).isIntegral
      have : FiniteDimensional F (E⟮x⟯.restrictScalars F) := .trans F E E⟮x⟯
      exact Module.finrank_pos.ne'
    change _ ⊆ (Module.finrank F E⟮x⟯).primeFactors at h4
    rw [← Module.finrank_mul_finrank F E E⟮x⟯, hmp,
      Nat.primeFactors_mul Module.finrank_pos.ne' Module.finrank_pos.ne', ← Finset.coe_subset,
      Finset.coe_union] at h4
    simpa using h4.trans <| Set.union_subset_union (primeFactors_subset_of_intermediateField S E)
      (primeFactors_subset_of_intermediateField S K⟮x⟯)
  simp [Module.finrank_of_infinite_dimensional hfd]

end Tower

variable {S} in
theorem of_subset [IsSExtension F K S] {S' : Set ℕ} (h : S ⊆ S') : IsSExtension F K S' :=
  ⟨fun E _ ↦ (primeFactors_subset_of_intermediateField S E).trans h⟩

end IsSExtension

open scoped IntermediateField in
variable {F K} in
/-- If `L / F` is an algebraic `S`-extension, then it is the compositum of all
finite `S`-extensions inside `L`. -/
theorem IntermediateField.eq_sSup_of_isAlgebraic_of_isSExtension (L : IntermediateField F K)
    [Algebra.IsAlgebraic F L] [IsSExtension F L S] :
    L = sSup {E | E ≤ L ∧ FiniteDimensional F E ∧ IsSExtension F E S} := by
  apply le_antisymm
  · intro x hx
    have halg : IsAlgebraic F (⟨x, hx⟩ : L) := Algebra.IsAlgebraic.isAlgebraic ..
    replace halg : IsAlgebraic F x := IntermediateField.isAlgebraic_iff.1 halg
    refine le_sSup (a := F⟮x⟯) ?_ (mem_adjoin_simple_self F x)
    replace hx : F⟮x⟯ ≤ L := by simpa
    refine ⟨hx, adjoin.finiteDimensional halg.isIntegral, ?_⟩
    have := IsSExtension.tower_bot F (restrict hx) S L
    exact .of_algEquiv S (restrict_algEquiv hx).symm
  · rw [sSup_le_iff]
    exact fun _ h ↦ h.1

open scoped IntermediateField in
variable {F K} in
/-- If `L / F` is a Galois `S`-extension, then it is the compositum of all
finite Galois `S`-extensions inside `L`. -/
theorem IntermediateField.eq_sSup_of_isGalois_of_isSExtension (L : IntermediateField F K)
    [IsGalois F L] [IsSExtension F L S] :
    L = sSup {E | E ≤ L ∧ FiniteDimensional F E ∧ IsGalois F E ∧ IsSExtension F E S} := by
  apply le_antisymm
  · intro x hx
    have halg : IsAlgebraic F (⟨x, hx⟩ : L) := Algebra.IsAlgebraic.isAlgebraic ..
    replace halg : IsAlgebraic F x := IntermediateField.isAlgebraic_iff.1 halg
    have := adjoin.finiteDimensional halg.isIntegral
    refine le_sSup (a := lift (normalClosure F F⟮x⟯ L)) ?_ ?_
    · refine ⟨lift_le _, (liftAlgEquiv _).toLinearEquiv.finiteDimensional,
        .of_algEquiv (liftAlgEquiv _), ?_⟩
      refine @IsSExtension.of_algEquiv _ _ _ _ _ S _ _ _ (liftAlgEquiv _) ?_
      exact .tower_bot F _ S L
    · apply (mem_lift ⟨x, hx⟩).2
      apply (inclusion (show F⟮x⟯ ≤ L by simpa)).fieldRange_le_normalClosure
      use ⟨x, mem_adjoin_simple_self F x⟩
      rfl
  · rw [sSup_le_iff]
    exact fun _ h ↦ h.1

variable {F K} in
/-- Compositum of a family of Galois `S`-extensions is also an `S`-extension.
Note that this is not true for non-Galois case. -/
instance isSExtension_iSup_of_isGalois {ι : Type*} (L : ι → IntermediateField F K)
    [∀ i, IsGalois F (L i)] [∀ i, IsSExtension F (L i) S] : IsSExtension F (⨆ i, L i :) S := by
  refine ⟨fun E _ ↦ ?_⟩
  have := (IntermediateField.liftAlgEquiv E).toLinearEquiv.finiteDimensional
  have hle := IntermediateField.lift_le E
  nth_rw 2 [iSup_congr fun i ↦ (L i).eq_sSup_of_isGalois_of_isSExtension S] at hle
  simp only [sSup_eq_iSup', iSup_sigma'] at hle
  obtain ⟨s, hs⟩ := IntermediateField.exists_finset_of_le_iSup hle
  rw [iSup_subtype'] at hs
  set E' : IntermediateField F K := ⨆ x : { x // x ∈ s }, x.1.2.1
  have : Finite { x // x ∈ s } := s.finite_toSet
  have (x : { x // x ∈ s }) : FiniteDimensional F x.1.2.1 := x.1.2.2.2.1
  have (x : { x // x ∈ s }) : IsGalois F x.1.2.1 := x.1.2.2.2.2.1
  have : IsGalois F E' := ⟨⟩
  have h1 := IntermediateField.finrank_dvd_of_le_right hs
  rw [← IsGalois.card_aut_eq_finrank F E',
    ← (IntermediateField.liftAlgEquiv E).toLinearEquiv.finrank_eq] at h1
  replace h1 := h1.trans <| Subgroup.card_dvd_of_injective
    (f := IntermediateField.piRestrictNormalHom' (fun x : { x // x ∈ s } ↦ x.1.2.1) E' rfl)
    (IntermediateField.injective_piRestrictNormalHom' ..)
  simp_rw [Nat.card_pi, IsGalois.card_aut_eq_finrank F _] at h1
  have h2 := Nat.primeFactors_mono h1 (by simp [Finset.prod_ne_zero_iff, Module.finrank_pos.ne'])
  rw [Nat.primeFactors_prod_eq_biUnion (by simp [Module.finrank_pos.ne'])] at h2
  refine (Finset.coe_subset.2 h2).trans ?_
  have (x : { x // x ∈ s }) : IsSExtension F x.1.2.1 S := x.1.2.2.2.2.2
  simp only [isSExtension_iff_of_finiteDimensional] at this
  simp only [Finset.coe_biUnion, Set.iUnion_subset_iff, this, implies_true]

variable {F K} in
/-- Compositum of a two Galois `S`-extensions is also an `S`-extension.
Note that this is not true for non-Galois case. -/
instance isSExtension_sup_of_isGalois (E1 E2 : IntermediateField F K) [IsGalois F E1]
    [IsGalois F E2] [IsSExtension F E1 S] [IsSExtension F E2 S] :
    IsSExtension F (E1 ⊔ E2 :) S := by
  let E : Fin 2 → _ := ![E1, E2]
  have : (i : Fin 2) → IsGalois F (E i)
    | 0 => inferInstanceAs (IsGalois F E1)
    | 1 => inferInstanceAs (IsGalois F E2)
  have : (i : Fin 2) → IsSExtension F (E i) S
    | 0 => inferInstanceAs (IsSExtension F E1 S)
    | 1 => inferInstanceAs (IsSExtension F E2 S)
  have : E1 ⊔ E2 = ⨆ i, E i := by apply le_antisymm <;> simp [le_iSup_iff, iSup_le_iff, E]
  convert isSExtension_iSup_of_isGalois S E

/-! ### Maximal Galois `S`-subextension -/

namespace IntermediateField

/-- The maximal Galois `S`-subextension of `K / F` is defined to be the compositum of all
Galois subextensions `E` of `K / F` which are `S`-extensions (`IsSExtension`). -/
def maximalGaloisSExtension : IntermediateField F K :=
  sSup {E | IsGalois F E ∧ IsSExtension F E S}

/-- The maximal Galois `S`-subextension of `K / F` is also equal to the compositum of all
finite Galois subextensions `E` of `K / F` which are `S`-extensions (`IsSExtension`). -/
theorem maximalGaloisSExtension_eq_sSup_finiteDimensional :
    maximalGaloisSExtension F K S = sSup {E : IntermediateField F K |
      FiniteDimensional F E ∧ IsGalois F E ∧ IsSExtension F E S} := by
  refine le_antisymm (sSup_le fun E ⟨_, _⟩ ↦ ?_) (sSup_le fun E ⟨_, h⟩ ↦ le_sSup h)
  rw [E.eq_sSup_of_isGalois_of_isSExtension S]
  exact sSup_le fun _ ⟨_, h⟩ ↦ le_sSup h

instance isGalois_maximalGaloisSExtension : IsGalois F (maximalGaloisSExtension F K S) := by
  rw [maximalGaloisSExtension, sSup_eq_iSup']
  have (E : {E : IntermediateField F K | IsGalois F E ∧ IsSExtension F E S}) : IsGalois F E.1 :=
    E.2.1
  exact ⟨⟩

instance isSExtension_maximalGaloisSExtension :
    IsSExtension F (maximalGaloisSExtension F K S) S := by
  rw [maximalGaloisSExtension, sSup_eq_iSup']
  have (E : {E : IntermediateField F K | IsGalois F E ∧ IsSExtension F E S}) :
    IsGalois F E.1 := E.2.1
  have (E : {E : IntermediateField F K | IsGalois F E ∧ IsSExtension F E S}) :
    IsSExtension F E.1 S := E.2.2
  exact isSExtension_iSup_of_isGalois ..

variable {F K} in
theorem le_maximalGaloisSExtension (E : IntermediateField F K) [IsGalois F E] [IsSExtension F E S] :
    E ≤ maximalGaloisSExtension F K S :=
  le_sSup ⟨‹_›, ‹_›⟩

variable {F K p} in
theorem le_maximalGaloisSExtension_singleton (E : IntermediateField F K) [IsGalois F E]
    (h : ∃ n, Module.finrank F E = p ^ n) : E ≤ maximalGaloisSExtension F K {p} :=
  le_sSup ⟨‹_›, isSExtension_singleton_of_exists_finrank_eq_pow F E p h⟩

variable {F K S} in
theorem le_maximalGaloisSExtension_iff_of_isGalois (E : IntermediateField F K) [IsGalois F E] :
    E ≤ maximalGaloisSExtension F K S ↔ IsSExtension F E S := by
  refine ⟨fun h ↦ ?_, fun _ ↦ E.le_maximalGaloisSExtension S⟩
  have := IsSExtension.tower_bot F (IntermediateField.restrict h) S (maximalGaloisSExtension F K S)
  exact .of_algEquiv S (IntermediateField.restrict_algEquiv h).symm

variable {F K S} in
theorem maximalGaloisSExtension_le_iff (E : IntermediateField F K) :
    maximalGaloisSExtension F K S ≤ E ↔
      ∀ E' : IntermediateField F K, IsGalois F E' → IsSExtension F E' S → E' ≤ E :=
  ⟨fun h E' _ _ ↦ (E'.le_maximalGaloisSExtension S).trans h,
    fun h ↦ sSup_le fun _ ⟨h1, h2⟩ ↦ h _ h1 h2⟩

variable {F K} in
theorem le_lift_maximalGaloisSExtension {L E : IntermediateField F K} (h : E ≤ L)
    [IsGalois F E] [IsSExtension F E S] : E ≤ lift (maximalGaloisSExtension F L S) := by
  have := IsGalois.of_algEquiv (restrict_algEquiv h)
  have := IsSExtension.of_algEquiv S (restrict_algEquiv h)
  have := le_maximalGaloisSExtension S (restrict h)
  intro x h'
  have := @this ⟨x, h h'⟩ ((mem_restrict h _).2 h')
  rwa [← mem_lift] at this

variable {F K S} in
theorem le_lift_maximalGaloisSExtension_iff_of_isGalois
    (L E : IntermediateField F K) [IsGalois F E] :
    E ≤ lift (maximalGaloisSExtension F L S) ↔ E ≤ L ∧ IsSExtension F E S := by
  refine ⟨fun h ↦ ⟨h.trans (lift_le _), ?_⟩, fun ⟨h, _⟩ ↦ le_lift_maximalGaloisSExtension S h⟩
  have := IsSExtension.of_algEquiv S (liftAlgEquiv (maximalGaloisSExtension F L S))
  have := IsSExtension.tower_bot F (restrict h) S (lift (maximalGaloisSExtension F L S))
  exact .of_algEquiv S (restrict_algEquiv h).symm

variable {F K S} in
theorem lift_maximalGaloisSExtension_le_iff (L E : IntermediateField F K) :
    lift (maximalGaloisSExtension F L S) ≤ E ↔
      ∀ E' : IntermediateField F K, E' ≤ L → IsGalois F E' → IsSExtension F E' S → E' ≤ E :=
  ⟨fun h _ h2 _ _ ↦ (le_lift_maximalGaloisSExtension S h2).trans h,
    fun h ↦ h _ (lift_le ..) (.of_algEquiv (liftAlgEquiv _)) (.of_algEquiv S (liftAlgEquiv _))⟩

variable {F K} in
theorem lift_maximalGaloisSExtension_eq_sSup (L : IntermediateField F K) :
    lift (maximalGaloisSExtension F L S) = sSup {E : IntermediateField F K |
      E ≤ L ∧ IsGalois F E ∧ IsSExtension F E S} := by
  refine le_antisymm ?_ (sSup_le fun E ⟨h, _, _⟩ ↦ le_lift_maximalGaloisSExtension S h)
  rw [lift_maximalGaloisSExtension_le_iff]
  exact fun E' h1 h2 h3 ↦ le_sSup ⟨h1, h2, h3⟩

variable {F K} in
theorem lift_maximalGaloisSExtension_eq_sSup_finiteDimensional (L : IntermediateField F K) :
    lift (maximalGaloisSExtension F L S) = sSup {E : IntermediateField F K |
      E ≤ L ∧ FiniteDimensional F E ∧ IsGalois F E ∧ IsSExtension F E S} := by
  rw [lift_maximalGaloisSExtension_eq_sSup]
  refine le_antisymm (sSup_le fun E ⟨h, _, _⟩ ↦ ?_) (sSup_le fun E ⟨h, _, h2⟩ ↦ le_sSup ⟨h, h2⟩)
  rw [E.eq_sSup_of_isGalois_of_isSExtension S]
  exact sSup_le fun _ ⟨h1, h2⟩ ↦ le_sSup ⟨h1.trans h, h2⟩

variable {S} in
theorem maximalGaloisSExtension_maximalGaloisSExtension_eq_top_of_subset
    {S' : Set ℕ} (hS : S ⊆ S') :
    maximalGaloisSExtension F (maximalGaloisSExtension F K S) S' = ⊤ := by
  rw [← lift_inj, lift_top]
  refine (lift_le _).antisymm ?_
  have : IsSExtension F (maximalGaloisSExtension F K S) S' := .of_subset _ _ hS
  exact le_lift_maximalGaloisSExtension _ le_rfl

variable {F K S} in
theorem primeFactors_finrank_subset_of_le_maximalGaloisSExtension
    {E : IntermediateField F K} (h : E ≤ maximalGaloisSExtension F K S) :
    ↑(Module.finrank F E).primeFactors ⊆ S := by
  have := IsSExtension.tower_bot F (restrict h) S (maximalGaloisSExtension F K S)
  have := IsSExtension.of_algEquiv S (restrict_algEquiv h).symm
  exact IsSExtension.primeFactors_subset ..

variable {F K p} in
theorem exists_finrank_eq_pow_of_le_maximalGaloisSExtension_singleton
    {E : IntermediateField F K} (h : E ≤ maximalGaloisSExtension F K {p}) [FiniteDimensional F E] :
    ∃ n, Module.finrank F E = p ^ n := by
  have := IsSExtension.tower_bot F (restrict h) {p} (maximalGaloisSExtension F K {p})
  have := IsSExtension.of_algEquiv {p} (restrict_algEquiv h).symm
  rwa [isSExtension_singleton_iff_of_finiteDimensional] at this

variable {F K S} in
theorem le_maximalGaloisSExtension_iff_of_finiteDimensional_of_isGalois
    (E : IntermediateField F K) [FiniteDimensional F E] [IsGalois F E] :
    E ≤ maximalGaloisSExtension F K S ↔ ↑(Module.finrank F E).primeFactors ⊆ S := by
  rw [le_maximalGaloisSExtension_iff_of_isGalois, isSExtension_iff_of_finiteDimensional]

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
    simp only [AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, SubalgebraClass.coe_algebraMap,
      AlgEquiv.restrictNormal_commutes, f, g]
    rfl
  have : IsGalois K σH := .of_equiv_equiv hcomp
  have : IsSExtension K σH S := .of_equiv_equiv S hcomp
  exact le_maximalGaloisSExtension ..

section FiniteDimensional

variable [FiniteDimensional F K]

theorem exists_finrank_maximalGaloisSExtension_singleton_eq_pow :
    ∃ n, Module.finrank F (maximalGaloisSExtension F K {p}) = p ^ n :=
  exists_finrank_eq_pow_of_le_maximalGaloisSExtension_singleton le_rfl

end FiniteDimensional

section FiniteAbelian

variable [FiniteDimensional F K] [IsAbelianGalois F K]

theorem fixingSubgroup_maximalGaloisSExtension_singleton :
    open scoped IsMulCommutative in
    (maximalGaloisSExtension F K {p}).fixingSubgroup = CommGroup.primeToComponent Gal(K/F) p := by
  sorry

theorem finrank_maximalGaloisSExtension_singleton_top :
    Module.finrank (maximalGaloisSExtension F K {p}) K =
    Module.finrank F K / p ^ (Module.finrank F K).factorization p := by
  open scoped IsMulCommutative in
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
