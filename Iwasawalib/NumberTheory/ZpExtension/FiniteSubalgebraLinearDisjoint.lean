module

public import Iwasawalib.NumberTheory.ZpExtension.RamifiedFamily
public import Iwasawalib.NumberTheory.ZpExtension.Ln
public import Iwasawalib.NumberTheory.ZpExtension.LinearDisjoint

@[expose] public section

open IntermediateField

namespace IntermediateField

universe u v

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- An unramified Galois extension which is totally ramified at one place is trivial. -/
theorem eq_bot_of_isUnramifiedEverywhere_of_inertiaSubgroup_eq_top
    (A : IntermediateField F E) [IsGalois F A] [FiniteDimensional F A]
    [NumberField.IsUnramifiedEverywhere F A]
    (w : AbsoluteValue A ℝ) (hw : w.inertiaSubgroup F = ⊤) : A = ⊥ := by
  have hbot := AbsoluteValue.inertiaSubgroup_eq_bot_of_isUnramifiedEverywhere F w
  have hgal : (⊤ : Subgroup (Gal(↥A / F))) = ⊥ := hw.symm.trans hbot
  haveI : Subsingleton (Gal(↥A / F)) := by
    constructor
    intro σ τ
    have hσ : σ ∈ (⊥ : Subgroup (Gal(↥A / F))) := by rw [← hgal]; trivial
    have hτ : τ ∈ (⊥ : Subgroup (Gal(↥A / F))) := by rw [← hgal]; trivial
    exact (Subgroup.mem_bot.mp hσ).trans (Subgroup.mem_bot.mp hτ).symm
  apply finrank_eq_one_iff.mp
  rw [← IsGalois.card_aut_eq_finrank F A]
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩

/-- A finite Galois extension totally ramified at one place is linearly disjoint from an
everywhere-unramified Galois extension in the same ambient field. -/
theorem linearDisjoint_of_isUnramifiedEverywhere_of_inertiaSubgroup_eq_top
    (A B : IntermediateField F E)
    [IsGalois F A] [FiniteDimensional F A]
    [NumberField.IsUnramifiedEverywhere F A]
    [IsGalois F B] [FiniteDimensional F B]
    (w : AbsoluteValue B ℝ) (hw : w.inertiaSubgroup F = ⊤) :
    A.LinearDisjoint B := by
  let C : IntermediateField F E := A ⊓ B
  letI : Algebra C A := RingHom.toAlgebra (IntermediateField.inclusion inf_le_left).toRingHom
  letI : Algebra C B := RingHom.toAlgebra (IntermediateField.inclusion inf_le_right).toRingHom
  haveI : IsScalarTower F C A := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower F C B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsGalois F C := inferInstance
  haveI : FiniteDimensional F C :=
    Module.Finite.of_injective (IntermediateField.inclusion inf_le_left).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  haveI : NumberField.IsUnramifiedEverywhere F C :=
    NumberField.IsUnramifiedEverywhere.tower_bot F C A
  let wC : AbsoluteValue C ℝ := w.comp (algebraMap C B).injective
  have hmap : (w.inertiaSubgroup F).map (AlgEquiv.restrictNormalHom C) =
      wC.inertiaSubgroup F := by
    exact AbsoluteValue.map_inertiaSubgroup_eq_of_liesOver F wC w
  have hwC : wC.inertiaSubgroup F = ⊤ := by
    rw [← hmap, hw]
    exact Subgroup.map_top_of_surjective _ (AlgEquiv.restrictNormalHom_surjective B)
  have hC : C = ⊥ := eq_bot_of_isUnramifiedEverywhere_of_inertiaSubgroup_eq_top C wC hwC
  exact IntermediateField.LinearDisjoint.iff_inf_eq_bot.mpr hC

/-- Passing through all finite subalgebras removes the finite-dimensional hypothesis on the
totally ramified extension. -/
theorem linearDisjoint_of_isUnramifiedEverywhere_of_inertiaSubgroup_eq_top'
    (A : IntermediateField F E) [IsGalois F A] [FiniteDimensional F A]
    [NumberField.IsUnramifiedEverywhere F A]
    (L : Type*) [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]
    [IsAbelianGalois F L] [Algebra.IsAlgebraic F E]
    (w : AbsoluteValue L ℝ) (hw : w.inertiaSubgroup F = ⊤) :
    A.LinearDisjoint L := by
  rw [IntermediateField.linearDisjoint_iff]
  let i : L →ₐ[F] E := IsScalarTower.toAlgHom F L E
  letI : Algebra.IsIntegral F i.range :=
    Algebra.IsIntegral.of_surjective i.rangeRestrict (AlgHom.rangeRestrict_surjective i)
  change A.toSubalgebra.LinearDisjoint i.range
  apply Subalgebra.LinearDisjoint.of_linearDisjoint_finite_right
  intro B' hB' hfin
  let B : IntermediateField F E := Algebra.IsAlgebraic.toIntermediateField B'
  have hB_range : B ≤ i.fieldRange := by
    intro x hx
    exact hB' hx
  let e : L ≃ₐ[F] i.fieldRange := AlgEquiv.ofInjectiveField i
  let f : B →ₐ[F] L := e.symm.toAlgHom.comp (IntermediateField.inclusion hB_range)
  haveI : IsAbelianGalois F B := IsAbelianGalois.of_algHom f
  haveI : FiniteDimensional F B := hfin
  let R := i.fieldRange
  haveI : IsAbelianGalois F R := IsAbelianGalois.of_algHom e.symm.toAlgHom
  letI : Algebra B R := RingHom.toAlgebra (IntermediateField.inclusion hB_range).toRingHom
  haveI : IsScalarTower F B R := IsScalarTower.of_algebraMap_eq' rfl
  let wR : AbsoluteValue R ℝ := w.comp (f := (e.symm : R →+* L)) e.symm.injective
  let wB : AbsoluteValue B ℝ := wR.comp (algebraMap B R).injective
  have hwR : wR.inertiaSubgroup F = ⊤ := by
    rw [show wR = w.comp (f := (e.symm : R →+* L)) e.symm.injective from rfl,
      AbsoluteValue.inertiaSubgroup_comp_algEquiv_eq_comap, hw]
    exact Subgroup.comap_top _
  have hmap : (wR.inertiaSubgroup F).map (AlgEquiv.restrictNormalHom B) =
      wB.inertiaSubgroup F := by
    exact AbsoluteValue.map_inertiaSubgroup_eq_of_liesOver F wB wR
  have hwB : wB.inertiaSubgroup F = ⊤ := by
    rw [← hmap, hwR]
    exact Subgroup.map_top_of_surjective _ (AlgEquiv.restrictNormalHom_surjective R)
  have hld : A.LinearDisjoint B :=
    linearDisjoint_of_isUnramifiedEverywhere_of_inertiaSubgroup_eq_top A B wB hwB
  rw [IntermediateField.linearDisjoint_iff'] at hld
  simpa only [B, Algebra.IsAlgebraic.toIntermediateField,
    Subalgebra.IsAlgebraic.toIntermediateField] using hld

end IntermediateField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- A ramified place and finiteness of the unramified layers make `Lₙ` and `K∞` linearly
disjoint over `Kₙ` above some layer. -/
theorem exists_eventually_linearDisjoint_Ln_Kinf_of_ramified_of_finite [Unique ι]
    (hfinite : ∀ n, Module.Finite ↥(H.Kn n) ↥(H.Ln n))
    (w : AbsoluteValue Kinf ℝ) (hw : w.inertiaSubgroup K ≠ ⊥) :
    ∃ e : ℕ, ∀ n, e ≤ n → (H.Ln n).LinearDisjoint Kinf := by
  obtain ⟨e, he⟩ := H.exists_totally_ramified (s := Unit) (fun _ ↦ w) (fun _ ↦ hw)
  refine ⟨e, fun n hn ↦ ?_⟩
  letI : FiniteDimensional ↥(H.Kn n) ↥(H.Ln n) := hfinite n
  have htot : w.inertiaSubgroup ↥(H.Kn n) = ⊤ := he n hn ()
  letI : IsAbelianGalois ↥(H.Kn n) Kinf := (H.shift n).isAbelianGalois_Kinf
  haveI : Algebra.IsAlgebraic ↥(H.Kn n) (SeparableClosure Kinf) :=
    Algebra.IsAlgebraic.trans ↥(H.Kn n) Kinf (SeparableClosure Kinf)
  exact IntermediateField.linearDisjoint_of_isUnramifiedEverywhere_of_inertiaSubgroup_eq_top'
    (H.Ln n) Kinf w htot

end MvZpExtension
