/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.FieldTheory.IntermediateField.MaximalAbelian
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.ClassFieldTheory
public import Iwasawalib.NumberTheory.ZpExtension.Basic

@[expose] public section

/-!

# Maximal unramified abelian `p`-extension `Lₙ / Kₙ` in a `ℤₚ`-extension tower `K∞ / K`

-/

universe u v

variable {p : ℕ} [Fact p.Prime] {d : ℕ} {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- The maximal unramified abelian `p`-extension `Lₙ / Kₙ` of `Kₙ`, defined to be an
intermediate field of `Kₙ` and the separable closure of `K∞`. -/
noncomputable def Ln (n : ℕ) :=
  IntermediateField.lift <| IntermediateField.maximalGaloisSExtension (H.Kn n)
    (NumberField.maximalUnramifiedAbelianExtension (H.Kn n) (SeparableClosure Kinf)) {p}

instance isAbelianGalois_Ln (n : ℕ) : IsAbelianGalois (H.Kn n) (H.Ln n) :=
  .of_algEquiv (IntermediateField.liftAlgEquiv ..)

-- TODO: need IsUnramifiedEverywhere.of_algEquiv, etc.
instance isUnramifiedEverywhere_Ln (n : ℕ) :
    NumberField.IsUnramifiedEverywhere (H.Kn n) (H.Ln n) :=
  sorry

instance finiteDimensional_Ln (n : ℕ) : FiniteDimensional (H.Kn n) (H.Ln n) :=
  (IntermediateField.liftAlgEquiv <| IntermediateField.maximalGaloisSExtension (H.Kn n)
    (NumberField.maximalUnramifiedAbelianExtension (H.Kn n) (SeparableClosure Kinf))
      {p}).toLinearEquiv.finiteDimensional

instance numberField_Ln (n : ℕ) : NumberField (H.Ln n) where
  to_finiteDimensional := .trans ℚ (H.Kn n) (H.Ln n)

theorem finrank_Ln (n : ℕ) : Module.finrank (H.Kn n) (H.Ln n) =
    p ^ multiplicity p (NumberField.classNumber (H.Kn n)) := by
  rw [Ln, ← (IntermediateField.liftAlgEquiv <| IntermediateField.maximalGaloisSExtension (H.Kn n)
    (NumberField.maximalUnramifiedAbelianExtension (H.Kn n) (SeparableClosure Kinf))
      {p}).toLinearEquiv.finrank_eq,
    IntermediateField.finrank_maximalGaloisSExtension_singleton_bot,
    NumberField.IsUnramifiedEverywhere.finrank_eq_classNumber_of_isSepClosed,
    Nat.multiplicity_eq_factorization Fact.out (NumberField.classNumber_ne_zero _)]

/-- TODO: go mathlib -/
theorem _root_.IsSepClosure.ofSeparable
    (K J L : Type*) [Field K] [Field J] [Field L] [Algebra K J] [Algebra J L] [IsSepClosure J L]
    [Algebra K L] [IsScalarTower K J L] [Algebra.IsSeparable K J] : IsSepClosure K L :=
  .mk (‹IsSepClosure J L›.sep_closed) (.trans K J L)

instance isGalois_K_Ln (n : ℕ) : IsGalois K (H.Ln n) := by
  rw [Ln, ← ((IntermediateField.liftAlgEquiv <| IntermediateField.maximalGaloisSExtension (H.Kn n)
    (NumberField.maximalUnramifiedAbelianExtension (H.Kn n) (SeparableClosure Kinf))
      {p}).restrictScalars K).transfer_galois]
  have := IsSepClosure.ofSeparable K Kinf (SeparableClosure Kinf)
  have := NumberField.isGalois_maximalUnramifiedAbelianExtension_of_isGalois K (H.Kn n)
    (SeparableClosure Kinf)
  exact IntermediateField.isGalois_maximalGaloisSExtension_of_isGalois ..

end MvZpExtension
