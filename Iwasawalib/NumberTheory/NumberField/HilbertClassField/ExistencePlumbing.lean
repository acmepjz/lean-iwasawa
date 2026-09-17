/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.UnramifiedTransport

@[expose] public section

/-!
# Hilbert class-field existence transport plumbing

This file transports a supplied finite unramified abelian model into the maximal unramified
abelian extension. It does not provide the deep arithmetic existence theorem for that model.
-/

noncomputable section

namespace NumberField

/-- An embedded copy of a supplied finite unramified abelian extension. -/
structure EmbeddedFiniteUnramifiedAbelianModel
    (F L Ω : Type*) [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] where
  field : IntermediateField F Ω
  equiv : L ≃ₐ[F] field
  [isAbelianGalois : IsAbelianGalois F field]
  [isUnramifiedEverywhere : NumberField.IsUnramifiedEverywhere F field]
  [finiteDimensional : FiniteDimensional F field]

/-- Embed a supplied finite unramified abelian extension into a separably closed overfield. -/
noncomputable def embeddedFiniteUnramifiedAbelianModel
    (F L Ω : Type*) [Field F] [NumberField F] [Field L] [Field Ω]
    [Algebra F L] [Algebra F Ω] [IsSepClosed Ω]
    [IsAbelianGalois F L] [NumberField.IsUnramifiedEverywhere F L]
    [FiniteDimensional F L] :
    EmbeddedFiniteUnramifiedAbelianModel F L Ω := by
  let φ : L →ₐ[F] Ω := IsSepClosed.lift
  let E0 : IntermediateField F Ω := φ.fieldRange
  let e0 : L ≃ₐ[F] E0 := φ.equivFieldRange
  letI : IsAbelianGalois F E0 := IsAbelianGalois.of_algEquiv e0
  letI : NumberField.IsUnramifiedEverywhere F E0 :=
    NumberField.IsUnramifiedEverywhere.of_algEquiv e0
  letI : FiniteDimensional F E0 := e0.toLinearEquiv.finiteDimensional
  exact { field := E0, equiv := e0 }

/-- A finite unramified abelian layer inside the maximal unramified abelian extension. -/
structure FiniteUnramifiedAbelianLayerInMaximal
    (F L Ω : Type*) [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] where
  field : IntermediateField F (maximalUnramifiedAbelianExtension F Ω)
  equiv : L ≃ₐ[F] field
  [isAbelianGalois : IsAbelianGalois F field]
  [isUnramifiedEverywhere : NumberField.IsUnramifiedEverywhere F field]
  [finiteDimensional : FiniteDimensional F field]

/-- Place an embedded finite unramified abelian model inside the maximal extension. -/
noncomputable def EmbeddedFiniteUnramifiedAbelianModel.layerInMaximal
    {F L Ω : Type*} [Field F] [NumberField F] [Field L] [Field Ω]
    [Algebra F L] [Algebra F Ω] [IsSepClosed Ω]
    (model : EmbeddedFiniteUnramifiedAbelianModel F L Ω) :
    FiniteUnramifiedAbelianLayerInMaximal F L Ω := by
  letI : IsAbelianGalois F model.field := model.isAbelianGalois
  letI : NumberField.IsUnramifiedEverywhere F model.field := model.isUnramifiedEverywhere
  letI : FiniteDimensional F model.field := model.finiteDimensional
  have hE0 : model.field ≤ maximalUnramifiedAbelianExtension F Ω :=
    le_maximalUnramifiedAbelianExtension F Ω model.field
  let E : IntermediateField F (maximalUnramifiedAbelianExtension F Ω) :=
    IntermediateField.restrict hE0
  let e1 : model.field ≃ₐ[F] E := IntermediateField.restrict_algEquiv hE0
  let eLE : L ≃ₐ[F] E := model.equiv.trans e1
  letI : IsAbelianGalois F E := IsAbelianGalois.of_algEquiv e1
  letI : NumberField.IsUnramifiedEverywhere F E :=
    NumberField.IsUnramifiedEverywhere.of_algEquiv e1
  letI : FiniteDimensional F E := e1.toLinearEquiv.finiteDimensional
  exact { field := E, equiv := eLE }

/-- Transport a supplied class-group/Galois-group equivalence to the layer in the maximal
extension. -/
def FiniteUnramifiedAbelianLayerInMaximal.classGroupEquivGal
    {F L Ω : Type*} [Field F] [NumberField F] [Field L] [Field Ω]
    [Algebra F L] [Algebra F Ω]
    (model : FiniteUnramifiedAbelianLayerInMaximal F L Ω)
    (hilbertEquivL : ClassGroup (𝓞 F) ≃* Gal(L/F)) :
    ClassGroup (𝓞 F) ≃* Gal(model.field/F) :=
  hilbertEquivL.trans (AlgEquiv.autCongr model.equiv)

/-- A supplied finite unramified abelian model with a class-group equivalence has an equivalent
finite normal layer inside the maximal unramified abelian extension. -/
theorem exists_classGroupEquivalentLayerInMaximal_of_model
    (F L Ω : Type*) [Field F] [NumberField F] [Field L] [Field Ω]
    [Algebra F L] [Algebra F Ω] [IsSepClosed Ω]
    [IsAbelianGalois F L] [NumberField.IsUnramifiedEverywhere F L]
    [FiniteDimensional F L]
    (hilbertEquivL : ClassGroup (𝓞 F) ≃* Gal(L/F)) :
    ∃ E : IntermediateField F (maximalUnramifiedAbelianExtension F Ω),
      ∃ (_ : Normal F E) (_ : FiniteDimensional F E),
        Nonempty (ClassGroup (𝓞 F) ≃* Gal(E/F)) := by
  let embedded := embeddedFiniteUnramifiedAbelianModel F L Ω
  let layer := embedded.layerInMaximal
  letI : IsAbelianGalois F layer.field := layer.isAbelianGalois
  letI : NumberField.IsUnramifiedEverywhere F layer.field := layer.isUnramifiedEverywhere
  letI : FiniteDimensional F layer.field := layer.finiteDimensional
  exact ⟨layer.field, inferInstance, inferInstance,
    ⟨layer.classGroupEquivGal hilbertEquivL⟩⟩

end NumberField
