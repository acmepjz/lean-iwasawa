/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber

@[expose] public section

noncomputable section

namespace NumberField

/-- The formal Galois-theoretic shell of the Hilbert-class-field lower bound. -/
theorem card_classGroup_le_card_gal_maximalUnramifiedAbelianExtension_of_intermediate
    (F Omega : Type*) [Field F] [NumberField F] [Field Omega]
    [Algebra F Omega] [IsSepClosed Omega]
    [Finite Gal(maximalUnramifiedAbelianExtension F Omega/F)]
    (E : IntermediateField F (maximalUnramifiedAbelianExtension F Omega))
    [Normal F E]
    (hE : Nat.card (ClassGroup (𝓞 F)) <= Nat.card Gal(E/F)) :
    Nat.card (ClassGroup (𝓞 F)) <=
      Nat.card Gal(maximalUnramifiedAbelianExtension F Omega/F) := by
  exact hE.trans (Nat.card_le_card_of_surjective _
    (AlgEquiv.restrictNormalHom_surjective
      (F := F) (K₁ := E) (E := maximalUnramifiedAbelianExtension F Omega)))

/-- A wiring form of the lower bound suited to the global-CFT dependency graph. -/
theorem card_classGroup_le_card_gal_maximalUnramifiedAbelianExtension_of_artin_and_hilbert
    (F Omega : Type*) [Field F] [NumberField F] [Field Omega]
    [Algebra F Omega] [IsSepClosed Omega]
    (artin : ClassGroup (𝓞 F) →* Gal(maximalUnramifiedAbelianExtension F Omega/F))
    (hartin : Function.Surjective artin)
    (E : IntermediateField F (maximalUnramifiedAbelianExtension F Omega))
    [Normal F E]
    (hilbertEquiv : ClassGroup (𝓞 F) ≃* Gal(E/F)) :
    Nat.card (ClassGroup (𝓞 F)) <=
      Nat.card Gal(maximalUnramifiedAbelianExtension F Omega/F) := by
  letI : Finite Gal(maximalUnramifiedAbelianExtension F Omega/F) :=
    Finite.of_surjective artin hartin
  apply card_classGroup_le_card_gal_maximalUnramifiedAbelianExtension_of_intermediate
    F Omega E
  exact (Nat.card_congr hilbertEquiv.toEquiv).le

end NumberField
