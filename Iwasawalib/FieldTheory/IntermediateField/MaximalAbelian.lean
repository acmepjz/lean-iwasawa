/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.FieldTheory.Galois.Abelian
public import Iwasawalib.GroupTheory.Torsion

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
  exact IntermediateField.isAbelianGalois_iSup Subtype.val

theorem le_maximalAbelianExtension (E : IntermediateField F K) [IsAbelianGalois F E] :
    E ≤ maximalAbelianExtension F K :=
  le_sSup ‹_›

theorem fixingSubgroup_maximalAbelianExtension_of_finiteDimensional
    [IsGalois F K] [FiniteDimensional F K] :
    (maximalAbelianExtension F K).fixingSubgroup = commutator Gal(K/F) := by
  sorry

theorem fixingSubgroup_maximalAbelianExtension [IsGalois F K] :
    (maximalAbelianExtension F K).fixingSubgroup = (commutator Gal(K/F)).topologicalClosure := by
  sorry

section Adhoc

variable {F} {K} {L : Type*} [Field L] [Algebra F L] [Algebra K L]
  (E : IntermediateField F L) (algebra_map_mem : ∀ x : K, (algebraMap K L) x ∈ E)
include algebra_map_mem

section

omit [Algebra F K]

/-- TODO: adhoc -/
def extendScalars' : IntermediateField K L := E.toSubfield.toIntermediateField algebra_map_mem

@[simp]
theorem coe_extendScalars' : (extendScalars' E algebra_map_mem : Set L) = (E : Set L) := rfl

@[simp]
theorem extendScalars'_toSubfield :
  (extendScalars' E algebra_map_mem).toSubfield = E.toSubfield := rfl

@[simp]
theorem mem_extendScalars' (x) : x ∈ extendScalars' E algebra_map_mem ↔ x ∈ E := Iff.rfl

end

@[simp]
theorem extendScalars'_restrictScalars [IsScalarTower F K L] :
    (extendScalars' E algebra_map_mem).restrictScalars F = E := rfl

end Adhoc

/-- ... Similar to `IsGalois.normalAutEquivQuotient`. -/
noncomputable def autQuotientEquivAutOfIsGalois {F L : Type*} [Field F] [Field L] [Algebra F L]
    (K : IntermediateField F L) [IsGalois F K] [IsGalois F L] :
    Gal(L/F) ⧸ K.fixingSubgroup ≃* Gal(K/F) := by
  refine MulEquiv.ofBijective (QuotientGroup.lift _ (AlgEquiv.restrictNormalHom K)
    (restrictNormalHom_ker K).ge) ⟨?_, QuotientGroup.lift_surjective_of_surjective _ _
      (AlgEquiv.restrictNormalHom_surjective _) _⟩
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift, restrictNormalHom_ker,
    QuotientGroup.map_mk'_self]

theorem autQuotientEquivAutOfIsGalois_apply {F L : Type*} [Field F] [Field L] [Algebra F L]
    (K : IntermediateField F L) [IsGalois F K] [IsGalois F L] (σ : Gal(L/F)) :
    K.autQuotientEquivAutOfIsGalois σ = AlgEquiv.restrictNormalHom K σ := rfl

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

-- /-- ... -/
-- noncomputable def quotientFixingSubgroupEquivQuotientFixingSubgroup
--     {F L : Type*} [Field F] [Field L] [Algebra F L]
--     {K H : IntermediateField F L} (hle : K ≤ H) [IsGalois F L] [IsGalois K (extendScalars hle)] :
--     Gal(L/K) ⧸ (extendScalars hle).fixingSubgroup ≃* Gal(L/F) ⧸ H.fixingSubgroup :=
--   sorry

/-- If `K ≤ H` are intermediate fields of `L / F`, `σ ∈ Gal(L/F)`, then there is a
natural isomorphism between `Gal(H/K)` and `Gal(σ(H)/σ(K))` given by conjugation by `σ`. -/
noncomputable def autEquivAutMapMap
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    {K H : IntermediateField F L} (hle : K ≤ H) [IsGalois F L] [IsGalois K (extendScalars hle)]
    (σ : Gal(L/F)) :
    Gal(extendScalars hle/K) ≃*
    Gal(extendScalars (map_mono (AlgHomClass.toAlgHom σ) hle)/map (AlgHomClass.toAlgHom σ) K) :=
  let K' := map (AlgHomClass.toAlgHom σ) K
  have hle' := map_mono (AlgHomClass.toAlgHom σ) hle
  let i4 := K.fixingSubgroupEquiv.symm.trans ((MulAut.conj σ).subgroupMap _) |>.trans
    (MulEquiv.subgroupCongr (IsGalois.map_fixingSubgroup K σ).symm) |>.trans K'.fixingSubgroupEquiv
  have hfix : (extendScalars hle').fixingSubgroup = (extendScalars hle).fixingSubgroup.map i4 := by
    apply le_antisymm
    · intro g
      simp only [mem_fixingSubgroup_iff, Subgroup.mem_map, mem_extendScalars]
      refine fun h ↦ ⟨i4.symm g, fun x hx ↦ ?_, EquivLike.apply_coe_symm_apply i4 g⟩
      simp [i4, fixingSubgroupEquiv, h (σ x) ⟨x, hx, rfl⟩]
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_equiv_eq_map_symm]
      intro g
      simp only [mem_fixingSubgroup_iff, Subgroup.mem_map, mem_extendScalars]
      refine fun h ↦ ⟨i4 g, fun x ⟨y, h1, h2⟩ ↦ ?_, EquivLike.coe_symm_apply_apply i4 g⟩
      simp [← h2, h y h1, i4, fixingSubgroupEquiv]
  have : IsGalois K' (extendScalars hle') := by
    have : (extendScalars hle).fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois _).2 ‹_›
    rw [← InfiniteGalois.normal_iff_isGalois, hfix]
    exact this.map (MonoidHomClass.toMonoidHom i4) i4.surjective
  (extendScalars hle).autQuotientEquivAutOfIsGalois.symm.trans
    (QuotientGroup.congr _ _ i4 hfix.symm) |>.trans
      (extendScalars hle').autQuotientEquivAutOfIsGalois

/-- Version of `autEquivAutMapMap` with `K / F` Galois. -/
noncomputable def autEquivAutMapOfIsGalois
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    {K H : IntermediateField F L} (hle : K ≤ H) [IsGalois F L] [IsGalois K (extendScalars hle)]
    [IsGalois F K] (σ : Gal(L/F)) :
    haveI : K ≤ map (AlgHomClass.toAlgHom σ) H :=
      (normal_iff_forall_map_eq' (K := K)).1 inferInstance σ ▸ map_mono (AlgHomClass.toAlgHom σ) hle
    Gal(extendScalars hle/K) ≃* Gal(extendScalars this/K) :=
  have hle' : K ≤ map (AlgHomClass.toAlgHom σ) H :=
    (normal_iff_forall_map_eq' (K := K)).1 inferInstance σ ▸ map_mono (AlgHomClass.toAlgHom σ) hle
  let i4 := K.fixingSubgroupEquiv.symm.trans ((MulAut.conj σ).subgroupMap _) |>.trans
    (MulEquiv.subgroupCongr (by
      nth_rw 2 [← (normal_iff_forall_map_eq' (K := K)).1 inferInstance σ]
      rw [IsGalois.map_fixingSubgroup]
      rfl)) |>.trans K.fixingSubgroupEquiv
  have hfix : (extendScalars hle').fixingSubgroup = (extendScalars hle).fixingSubgroup.map i4 := by
    apply le_antisymm
    · intro g
      simp only [mem_fixingSubgroup_iff, Subgroup.mem_map, mem_extendScalars]
      refine fun h ↦ ⟨i4.symm g, fun x hx ↦ ?_, EquivLike.apply_coe_symm_apply i4 g⟩
      simp [i4, fixingSubgroupEquiv, h (σ x) ⟨x, hx, rfl⟩]
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_equiv_eq_map_symm]
      intro g
      simp only [mem_fixingSubgroup_iff, Subgroup.mem_map, mem_extendScalars]
      refine fun h ↦ ⟨i4 g, fun x ⟨y, h1, h2⟩ ↦ ?_, EquivLike.coe_symm_apply_apply i4 g⟩
      simp [← h2, h y h1, i4, fixingSubgroupEquiv]
  have : IsGalois K (extendScalars hle') := by
    have : (extendScalars hle).fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois _).2 ‹_›
    rw [← InfiniteGalois.normal_iff_isGalois, hfix]
    exact this.map (MonoidHomClass.toMonoidHom i4) i4.surjective
  (extendScalars hle).autQuotientEquivAutOfIsGalois.symm.trans
    (QuotientGroup.congr _ _ i4 hfix.symm) |>.trans
      (extendScalars hle').autQuotientEquivAutOfIsGalois

/-- If `L / K / F` is a field extension tower, such that `L / F` and `K / F` are Galois,
then `H / F` is also Galois, where `H` is the maximal abelian subextension of `L / K`. -/
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
  let K' := (IsScalarTower.toAlgHom F K L).fieldRange
  have hle : K' ≤ restrictScalars F H := by
    rintro _ ⟨x, rfl⟩
    exact algebraMap_mem _ x
  let i1 : K ≃+* K' := (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F K L)).toRingEquiv
  let i2 : H ≃+* extendScalars hle := RingEquiv.refl H
  have hcomp : (algebraMap K' (extendScalars hle)).comp (RingHomClass.toRingHom i1) =
      (RingHomClass.toRingHom i2).comp (algebraMap K H) := by
    ext; rfl
  have : IsGalois K' (extendScalars hle) := {
    to_isSeparable := .of_equiv_equiv i1 i2 hcomp
    to_normal := .of_equiv_equiv hcomp
  }
  -- let i := autEquivAutMapMap hle σ
  have hle' := map_mono (AlgHomClass.toAlgHom σ) hle
  have hK' : IsGalois F K' := .of_algEquiv
    (show K ≃ₐ[F] K' from .ofInjectiveField (IsScalarTower.toAlgHom F K L))
  -- rw [normal_iff_forall_map_eq'] at hK'
  let i := autEquivAutMapOfIsGalois hle σ
  sorry
  -- let σH := (map (AlgHomClass.toAlgHom σ) (restrictScalars F H)).extendScalars' (K := K) fun x ↦ by
  --   apply hle'
  --   rw [hK']
  --   exact ⟨x, rfl⟩
  -- suffices σH ≤ H from fun x hx ↦ this hx
  -- suffices IsAbelianGalois K σH from le_maximalAbelianExtension ..
  -- sorry

/-! ### Maximal abelian `p`-subextension -/

variable (p : ℕ)

/-- The maximal abelian `p`-subextension of `K / F` is the compositum of all
abelian subextension of `K / F` whose degree is a power of `p`. -/
def maximalAbelianPExtension : IntermediateField F K :=
  sSup {E | IsAbelianGalois F E ∧ ∃ n, Module.finrank F E = p ^ n}

instance isAbelianGalois_maximalAbelianPExtension :
    IsAbelianGalois F (maximalAbelianPExtension F K p) := by
  rw [maximalAbelianPExtension, sSup_eq_iSup']
  have (E : {E : IntermediateField F K | IsAbelianGalois F E ∧
    ∃ n, Module.finrank F E = p ^ n}) : IsAbelianGalois F E.1 := E.2.1
  exact IntermediateField.isAbelianGalois_iSup Subtype.val

theorem le_maximalAbelianPExtension (E : IntermediateField F K) [IsAbelianGalois F E]
    (h : ∃ n, Module.finrank F E = p ^ n) : E ≤ maximalAbelianPExtension F K p :=
  le_sSup ⟨‹_›, h⟩

/-- If `L / K / F` is a field extension tower, such that `L / F` and `K / F` are Galois,
then `H / F` is also Galois, where `H` is the maximal abelian `p`-subextension of `L / K`. -/
theorem isGalois_maximalAbelianPExtension_of_isGalois
    (L : Type*) [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
    [IsGalois F L] [IsGalois F K] (p : ℕ) : IsGalois F (maximalAbelianPExtension K L p) := by
  sorry

variable [Fact p.Prime] [FiniteDimensional F K]

theorem exists_finrank_maximalAbelianPExtension_eq :
    ∃ n, Module.finrank F (maximalAbelianPExtension F K p) = p ^ n := by
  simp_rw [← IsGalois.card_aut_eq_finrank, ← IsPGroup.iff_card, maximalAbelianPExtension]
  rw [sSup_eq_iSup']
  refine fun g ↦ ⟨orderOf g, ?_⟩
  have (E : {E : IntermediateField F K | IsAbelianGalois F E ∧
    ∃ n, Module.finrank F E = p ^ n}) : IsAbelianGalois F E.1 := E.2.1
  let f := IntermediateField.piRestrictNormalHom' fun E : {E : IntermediateField F K |
    IsAbelianGalois F E ∧ ∃ n, Module.finrank F E = p ^ n} ↦ E.1
  have hf : Function.Injective f := IntermediateField.injective_piRestrictNormalHom' _
  apply_fun f using hf
  ext1 E
  simp only [map_pow, Pi.pow_apply, map_one, Pi.one_apply, ← orderOf_dvd_iff_pow_eq_one]
  have h1 : orderOf (f g E) ≤ orderOf g := Nat.le_of_dvd (Nat.pos_of_ne_zero <|
    orderOf_ne_zero_iff.2 <| isOfFinOrder_of_finite g) <| by rw [orderOf_dvd_iff_pow_eq_one,
      ← orderOf_injective f hf g, ← Pi.pow_apply, pow_orderOf_eq_one, Pi.one_apply]
  replace h1 := h1.trans (Nat.lt_pow_self ‹Fact p.Prime›.out.one_lt).le
  obtain ⟨n, hn⟩ := E.2.2
  rw [← IsGalois.card_aut_eq_finrank] at hn
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Fact.out).1 (hn ▸ orderOf_dvd_natCard (f g E))
  rw [hm] at h1 ⊢
  rwa [Nat.pow_dvd_pow_iff_pow_le_pow ‹Fact p.Prime›.out.pos]

variable [IsAbelianGalois F K]

theorem fixingSubgroup_maximalAbelianPExtension :
    (maximalAbelianPExtension F K p).fixingSubgroup = CommGroup.primeToComponent Gal(K/F) p := by
  sorry

theorem finrank_maximalAbelianPExtension_top : Module.finrank (maximalAbelianPExtension F K p) K =
    Module.finrank F K / p ^ (Module.finrank F K).factorization p := by
  simp_rw [← IsGalois.card_fixingSubgroup_eq_finrank, fixingSubgroup_maximalAbelianPExtension,
    CommGroup.card_primeToComponent, IsGalois.card_aut_eq_finrank]

theorem finrank_maximalAbelianPExtension_bot : Module.finrank F (maximalAbelianPExtension F K p) =
    p ^ (Module.finrank F K).factorization p := by
  have h := (Nat.div_eq_of_eq_mul_left Module.finrank_pos
    (Module.finrank_mul_finrank F (maximalAbelianPExtension F K p) K).symm).symm
  rwa [finrank_maximalAbelianPExtension_top,
    Nat.div_div_self (Nat.ordProj_dvd ..) Module.finrank_pos.ne'] at h

theorem maximalAbelianPExtension_eq_bot_iff :
    maximalAbelianPExtension F K p = ⊥ ↔ ¬p ∣ Module.finrank F K := by
  simp [← finrank_eq_one_iff, finrank_maximalAbelianPExtension_bot, Module.finrank_pos.ne',
    Nat.factorization_eq_zero_iff, ‹Fact p.Prime›.out, ‹Fact p.Prime›.out.ne_one]

theorem not_dvd_finrank_maximalAbelianPExtension_top :
    ¬p ∣ Module.finrank (maximalAbelianPExtension F K p) K := by
  rw [finrank_maximalAbelianPExtension_top]
  exact Nat.not_dvd_ordCompl Fact.out Module.finrank_pos.ne'

end IntermediateField
