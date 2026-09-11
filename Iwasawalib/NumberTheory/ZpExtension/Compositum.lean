/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.Basic
public import Iwasawalib.FieldTheory.IntermediateField.MaximalGaloisSExtension

@[expose] public section

/-!

# Base change of a Galois subextension along a compositum

Let `Ω / F' / F` be a tower of fields with `Ω / F` normal, and let `A` be an intermediate field
of `Ω / F`. This file studies the compositum `F'A = IntermediateField.adjoin F' A`, viewed as an
intermediate field of `Ω / F'`, and shows that it inherits from `A / F` the properties needed in
Iwasawa theory:

* `IntermediateField.normal_adjoin`: `F'A / F'` is normal if `A / F` is;
* `IntermediateField.galAdjoinMulEquivRange`: `Gal(F'A/F')` is isomorphic to a subgroup of
  `Gal(A/F)`, via restriction;
* `IntermediateField.isAbelianGalois_adjoin`,
  `IntermediateField.finiteDimensional_adjoin_of_isGalois`,
  `IntermediateField.finrank_adjoin_dvd`: consequences of the previous item;
* `AbsoluteValue.isUnramifiedOfIsScalarTower_adjoin` and
  `NumberField.isUnramifiedEverywhere_adjoin`: `F'A / F'` is unramified everywhere if `A / F` is.

These combine into `IntermediateField.adjoin_le_lift_maximalGaloisSExtension`, which is the
key ingredient of `MvZpExtension.Ln_mono`.

-/

open IntermediateField

namespace IntermediateField

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

theorem restrictScalars_bot (A : IntermediateField F Ω) :
    (⊥ : IntermediateField (↥A) Ω).restrictScalars F = A := by
  ext x; simp

theorem mem_fixingSubgroup_adjoin_iff (S : Set Ω) (σ : Ω ≃ₐ[F] Ω) :
    σ ∈ (IntermediateField.adjoin F S).fixingSubgroup ↔ ∀ x ∈ S, σ x = x := by
  refine ⟨fun h x hx ↦ h ⟨x, IntermediateField.subset_adjoin F S hx⟩, fun h ↦ ?_⟩
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]
  intro x hx
  rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  exact Subgroup.zpowers_le.2 (show σ ∈ MulAction.stabilizer Gal(Ω/F) x from h x hx) hτ

section Compositum

variable {F F' Ω : Type*} [Field F] [Field F'] [Field Ω]
  [Algebra F F'] [Algebra F Ω] [Algebra F' Ω] [IsScalarTower F F' Ω]
  [Normal F Ω] [Normal F' Ω] (A : IntermediateField F Ω)

local notation "ι" => IntermediateField.restrictRestrictAlgEquivMapHom F Ω F' Ω

/-- Applying the natural injection `Gal(Ω/F') → Gal(Ω/F)` does not change the action on `Ω`. -/
theorem restrictRestrictAlgEquivMapHom_self_apply (σ : Gal(Ω/F')) (x : Ω) : (ι σ) x = σ x := by
  simpa using IntermediateField.alrebraMap_restrictRestrictAlgEquivMapHom_apply F Ω F' Ω σ x

/-- `σ ∈ Gal(Ω/F')` fixes `F'A` pointwise iff it fixes `A` pointwise. -/
theorem mem_fixingSubgroup_adjoin_iff' (σ : Gal(Ω/F')) :
    σ ∈ (IntermediateField.adjoin F' (A : Set Ω)).fixingSubgroup ↔ ι σ ∈ A.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_adjoin_iff]
  simp only [IntermediateField.mem_fixingSubgroup_iff, restrictRestrictAlgEquivMapHom_self_apply]
  exact ⟨fun h x hx ↦ h x hx, fun h x hx ↦ h x hx⟩

end Compositum

section Unram

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [Normal F Ω]

theorem _root_.AbsoluteValue.isUnramifiedOfIsScalarTower_iff_inertiaSubgroup_le
    (E : IntermediateField F Ω) (w : AbsoluteValue Ω ℝ) :
    w.IsUnramifiedOfIsScalarTower F ↥E ↔ w.inertiaSubgroup F ≤ E.fixingSubgroup := by
  rw [AbsoluteValue.IsUnramifiedOfIsScalarTower,
    IntermediateField.range_restrictRestrictAlgEquivMapHom_eq_fixingSubgroup,
    IntermediateField.restrictScalars_bot]

end Unram

section Compositum2

variable {F F' Ω : Type*} [Field F] [Field F'] [Field Ω]
  [Algebra F F'] [Algebra F Ω] [Algebra F' Ω] [IsScalarTower F F' Ω]
  [Normal F Ω] [Normal F' Ω] (A : IntermediateField F Ω)

theorem _root_.AbsoluteValue.isUnramifiedOfIsScalarTower_adjoin (w : AbsoluteValue Ω ℝ)
    (h : w.IsUnramifiedOfIsScalarTower F ↥A) :
    w.IsUnramifiedOfIsScalarTower F' ↥(IntermediateField.adjoin F' (A : Set Ω)) := by
  rw [AbsoluteValue.isUnramifiedOfIsScalarTower_iff_inertiaSubgroup_le] at h ⊢
  intro σ hσ
  rw [mem_fixingSubgroup_adjoin_iff']
  refine h ?_
  rw [AbsoluteValue.inertiaSubgroup_eq_comap F F'] at hσ
  exact hσ

end Compositum2

section Compositum3

open IntermediateField AlgEquiv

variable {F F' Ω : Type*} [Field F] [Field F'] [Field Ω]
  [Algebra F F'] [Algebra F Ω] [Algebra F' Ω] [IsScalarTower F F' Ω]
  [Normal F Ω] [Normal F' Ω] (A : IntermediateField F Ω)

instance normal_adjoin [Normal F A] : Normal F' ↥(adjoin F' (A : Set Ω)) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro σ
  rw [IntermediateField.adjoin_map]
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  have h := (IntermediateField.normal_iff_forall_map_le' (K := A)).1 ‹Normal F A›
    (IntermediateField.restrictRestrictAlgEquivMapHom F Ω F' Ω σ)
  have hx' := h ⟨x, hx, rfl⟩
  replace hx' : σ x ∈ A := by
    rw [← restrictRestrictAlgEquivMapHom_self_apply (F := F) σ x]; exact hx'
  exact IntermediateField.subset_adjoin F' _ hx'

theorem ker_restrictRestrictAlgEquivMapHom_eq_fixingSubgroup_adjoin [Normal F A] :
    (IntermediateField.restrictRestrictAlgEquivMapHom F (↥A) F' Ω).ker =
      (IntermediateField.adjoin F' (A : Set Ω)).fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_adjoin_iff]
  constructor
  · intro h x hx
    have h1 := IntermediateField.alrebraMap_restrictRestrictAlgEquivMapHom_apply F (↥A) F' Ω σ
      ⟨x, hx⟩
    rw [h, AlgEquiv.one_apply] at h1
    exact h1.symm
  · intro h
    refine AlgEquiv.ext fun x ↦ ?_
    apply_fun (algebraMap (↥A) Ω) using (algebraMap (↥A) Ω).injective
    rw [IntermediateField.alrebraMap_restrictRestrictAlgEquivMapHom_apply, AlgEquiv.one_apply]
    exact h _ x.2

theorem _root_.AlgEquiv.ker_restrictNormalHom_eq_fixingSubgroup {F Ω : Type*} [Field F]
    [Field Ω] [Algebra F Ω] [Normal F Ω] (E : IntermediateField F Ω) [Normal F E] :
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) (↥E)).ker = E.fixingSubgroup := by
  rw [AlgEquiv.restrictNormalHom_ker_eq_range,
    IntermediateField.range_restrictRestrictAlgEquivMapHom_eq_fixingSubgroup,
    IntermediateField.restrictScalars_bot]

/-- `Gal(F'A/F')` is isomorphic to a subgroup of `Gal(A/F)`. -/
noncomputable def galAdjoinMulEquivRange [Normal F A] :
    Gal(↥(IntermediateField.adjoin F' (A : Set Ω))/F') ≃*
      (IntermediateField.restrictRestrictAlgEquivMapHom F (↥A) F' Ω).range := by
  have hker : (AlgEquiv.restrictNormalHom (F := F') (K₁ := Ω)
      (↥(IntermediateField.adjoin F' (A : Set Ω)))).ker =
      (IntermediateField.restrictRestrictAlgEquivMapHom F (↥A) F' Ω).ker := by
    rw [AlgEquiv.ker_restrictNormalHom_eq_fixingSubgroup,
      ker_restrictRestrictAlgEquivMapHom_eq_fixingSubgroup_adjoin]
  exact (QuotientGroup.quotientKerEquivOfSurjective _
    (AlgEquiv.restrictNormalHom_surjective (F := F') (E := Ω)
      (K₁ := ↥(IntermediateField.adjoin F' (A : Set Ω))))).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange _))

theorem finite_gal_adjoin [Normal F A] [Finite Gal(↥A/F)] :
    Finite Gal(↥(IntermediateField.adjoin F' (A : Set Ω))/F') :=
  Finite.of_equiv _ (galAdjoinMulEquivRange (F' := F') A).symm.toEquiv

theorem card_gal_adjoin_dvd [Normal F A] :
    Nat.card Gal(↥(IntermediateField.adjoin F' (A : Set Ω))/F') ∣ Nat.card Gal(↥A/F) := by
  rw [Nat.card_congr (galAdjoinMulEquivRange (F' := F') A).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

theorem mul_comm_gal_adjoin [Normal F A] (h : ∀ x y : Gal(↥A/F), x * y = y * x)
    (x y : Gal(↥(IntermediateField.adjoin F' (A : Set Ω))/F')) : x * y = y * x := by
  apply (galAdjoinMulEquivRange (F' := F') A).injective
  rw [map_mul, map_mul]
  exact Subtype.ext (h _ _)

end Compositum3

section Final

open IntermediateField

variable {F F' Ω : Type*} [Field F] [Field F'] [Field Ω]
  [Algebra F F'] [Algebra F Ω] [Algebra F' Ω] [IsScalarTower F F' Ω]
  [IsGalois F Ω] [IsGalois F' Ω] (A : IntermediateField F Ω)

theorem isGalois_adjoin [Normal F A] : IsGalois F' ↥(adjoin F' (A : Set Ω)) := ⟨⟩

theorem isAbelianGalois_adjoin [IsAbelianGalois F A] :
    IsAbelianGalois F' ↥(adjoin F' (A : Set Ω)) :=
  haveI := isGalois_adjoin (F' := F') A
  { is_comm.comm x y := mul_comm_gal_adjoin A (fun a b ↦ IsMulCommutative.is_comm.comm a b) x y }

theorem finiteDimensional_adjoin_of_isGalois [IsGalois F A] [FiniteDimensional F A] :
    FiniteDimensional F' ↥(adjoin F' (A : Set Ω)) :=
  haveI := isGalois_adjoin (F' := F') A
  haveI := finite_gal_adjoin (F' := F') A
  IsGalois.finiteDimensional_of_finite F' _

theorem finrank_adjoin_dvd [IsGalois F A] [FiniteDimensional F A] :
    Module.finrank F' ↥(adjoin F' (A : Set Ω)) ∣ Module.finrank F A := by
  haveI := isGalois_adjoin (F' := F') A
  haveI := finiteDimensional_adjoin_of_isGalois (F' := F') A
  rw [← IsGalois.card_aut_eq_finrank F' ↥(adjoin F' (A : Set Ω)),
    ← IsGalois.card_aut_eq_finrank F A]
  exact card_gal_adjoin_dvd A

end Final

section Unram2

open IntermediateField NumberField

variable {F F' Ω : Type*} [Field F] [Field F'] [Field Ω]
  [Algebra F F'] [Algebra F Ω] [Algebra F' Ω] [IsScalarTower F F' Ω]
  [IsGalois F Ω] [IsGalois F' Ω] [Algebra.IsAlgebraic F Ω] (A : IntermediateField F Ω)

theorem _root_.NumberField.isUnramifiedEverywhere_adjoin [Normal F A]
    [NumberField.IsUnramifiedEverywhere F ↥A] :
    NumberField.IsUnramifiedEverywhere F' ↥(adjoin F' (A : Set Ω)) := by
  haveI : Algebra.IsAlgebraic F' Ω := Algebra.IsAlgebraic.tower_top (K := F) (L := F') (A := Ω)
  haveI : Algebra.IsAlgebraic (↥A) Ω := Algebra.IsAlgebraic.tower_top (K := F) (A := Ω) (L := ↥A)
  haveI : Algebra.IsAlgebraic ↥(adjoin F' (A : Set Ω)) Ω :=
    Algebra.IsAlgebraic.tower_top (K := F') (A := Ω) (L := ↥(adjoin F' (A : Set Ω)))
  rw [NumberField.isUnramifiedEverywhere_iff]
  intro v hv
  obtain ⟨w, hw⟩ := v.exists_liesOver Ω
  rw [AbsoluteValue.isUnramified_spec F' v w]
  refine AbsoluteValue.isUnramifiedOfIsScalarTower_adjoin A w ?_
  rw [← AbsoluteValue.isUnramified_spec F (w.comp (algebraMap (↥A) Ω).injective) w]
  refine (NumberField.isUnramifiedEverywhere_iff F ↥A).1 ‹_› _ ?_
  rw [AbsoluteValue.isNontrivial_iff_of_liesOver (w.comp (algebraMap (↥A) Ω).injective) w]
  rw [← AbsoluteValue.isNontrivial_iff_of_liesOver v w]
  exact hv

end Unram2

section Pack

open IntermediateField NumberField

variable {F F' Ω : Type*} [Field F] [Field F'] [Field Ω]
  [Algebra F F'] [Algebra F Ω] [Algebra F' Ω] [IsScalarTower F F' Ω]
  [IsGalois F Ω] [IsGalois F' Ω] [Algebra.IsAlgebraic F Ω] (A : IntermediateField F Ω)
variable {p : ℕ} [Fact p.Prime]

/-- If `A / F` is a Galois `{p}`-extension, then so is `F'A / F'`.

Note that no finiteness of `A / F` is needed: `A` is the compositum of its finite Galois
`{p}`-subextensions, and the compositum with `F'` is taken factor by factor. -/
theorem isSExtension_singleton_adjoin {p : ℕ} [Fact p.Prime]
    [IsGalois F A] [IsSExtension F A {p}] :
    IsSExtension F' (adjoin F' (A : Set Ω)) {p} := by
  set 𝒮 : Set (IntermediateField F Ω) :=
    {E | E ≤ A ∧ FiniteDimensional F E ∧ IsGalois F E ∧ IsSExtension F E {p}} with h𝒮
  set T : IntermediateField F' Ω :=
    ⨆ E : 𝒮, adjoin F' ((E : IntermediateField F Ω) : Set Ω) with hT
  have hle (E : IntermediateField F Ω) (hE : E ∈ 𝒮) :
      ((E : IntermediateField F Ω) : Set Ω) ⊆ (T : Set Ω) := fun x hx ↦
    le_iSup (fun E : 𝒮 ↦ adjoin F' ((E : IntermediateField F Ω) : Set Ω)) ⟨E, hE⟩
      (subset_adjoin F' _ hx)
  have hmem : ∀ x : F, algebraMap F Ω x ∈ T.toSubfield := fun x ↦ by
    rw [IsScalarTower.algebraMap_apply F F' Ω]
    exact T.algebraMap_mem _
  have key : adjoin F' (A : Set Ω) = T := by
    refine le_antisymm (adjoin_le_iff.2 ?_) (iSup_le fun E ↦ adjoin_le_iff.2 fun x hx ↦
      subset_adjoin F' _ (E.2.1 hx))
    have : A ≤ T.toSubfield.toIntermediateField hmem := by
      rw [A.eq_sSup_of_isGalois_of_isSExtension {p}]
      exact sSup_le fun E hE ↦ hle E hE
    exact this
  rw [key, hT]
  have h1 (E : 𝒮) : IsGalois F ((E : IntermediateField F Ω)) := E.2.2.2.1
  have h2 (E : 𝒮) : FiniteDimensional F ((E : IntermediateField F Ω)) := E.2.2.1
  have h3 (E : 𝒮) : IsSExtension F ((E : IntermediateField F Ω)) {p} := E.2.2.2.2
  have hG (E : 𝒮) : IsGalois F' ↥(adjoin F' ((E : IntermediateField F Ω) : Set Ω)) :=
    isGalois_adjoin _
  have hS (E : 𝒮) : IsSExtension F' (adjoin F' ((E : IntermediateField F Ω) : Set Ω)) {p} := by
    refine isSExtension_singleton_of_exists_finrank_eq_pow F' _ p ?_
    obtain ⟨k, hk⟩ :=
      (isSExtension_singleton_iff_of_finiteDimensional F ((E : IntermediateField F Ω)) p).1 (h3 E)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).1
      (hk ▸ finrank_adjoin_dvd (F' := F') ((E : IntermediateField F Ω)))
    exact ⟨j, hj⟩
  exact isSExtension_iSup_of_isGalois {p} _

theorem adjoin_le_lift_maximalGaloisSExtension
    [IsAbelianGalois F A] [IsSExtension F A {p}] [NumberField.IsUnramifiedEverywhere F ↥A] :
    adjoin F' (A : Set Ω) ≤
      lift (maximalGaloisSExtension F'
        (NumberField.maximalUnramifiedAbelianExtension F' Ω) {p}) := by
  haveI := isAbelianGalois_adjoin (F' := F') A
  haveI := isSExtension_singleton_adjoin (F' := F') (p := p) A
  haveI := NumberField.isUnramifiedEverywhere_adjoin (F' := F') A
  exact le_lift_maximalGaloisSExtension {p}
    (NumberField.le_maximalUnramifiedAbelianExtension F' Ω _)

/-- If `E ≤ F` are intermediate fields of `L / K` and `Ω / L` is a further extension, then the
inclusion `E → F` is compatible with the structure maps into `Ω`.

This is stated for abstract intermediate fields on purpose: the corresponding `rfl` at a concrete
intermediate field forces the kernel to unfold that field's definition, which is prohibitively
expensive. -/
theorem algebraMap_inclusion {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] {E F : IntermediateField K L} (hEF : E ≤ F)
    [Algebra (↥E) Ω] [Algebra (↥F) Ω]
    (hE : ∀ y : ↥E, algebraMap (↥E) Ω y = algebraMap L Ω (algebraMap (↥E) L y))
    (hF : ∀ y : ↥F, algebraMap (↥F) Ω y = algebraMap L Ω (algebraMap (↥F) L y))
    (x : ↥E) : algebraMap (↥E) Ω x = algebraMap (↥F) Ω (inclusion hEF x) := by
  rw [hE, hF]
  rfl

/-- Version of `IntermediateField.adjoin_le_lift_maximalGaloisSExtension` taking the embedding
`F → F'` as an explicit ring homomorphism instead of as an `Algebra` instance. This is the form
which is usable at a concrete instantiation: it takes no instance argument that the caller would
have to build by hand. -/
theorem adjoin_le_lift_maximalGaloisSExtension_of_ringHom {F F' Ω : Type*}
    [Field F] [Field F'] [Field Ω] [Algebra F Ω] [Algebra F' Ω]
    [IsGalois F Ω] [IsGalois F' Ω] [Algebra.IsAlgebraic F Ω]
    (f : F →+* F') (hf : ∀ x, algebraMap F Ω x = algebraMap F' Ω (f x))
    (A : IntermediateField F Ω) {p : ℕ} [Fact p.Prime]
    [IsAbelianGalois F A] [IsSExtension F A {p}] [NumberField.IsUnramifiedEverywhere F ↥A] :
    adjoin F' (A : Set Ω) ≤
      lift (maximalGaloisSExtension F'
        (NumberField.maximalUnramifiedAbelianExtension F' Ω) {p}) := by
  letI : Algebra F F' := f.toAlgebra
  haveI : IsScalarTower F F' Ω := IsScalarTower.of_algebraMap_eq hf
  exact adjoin_le_lift_maximalGaloisSExtension A

end Pack

end IntermediateField
