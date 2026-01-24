/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.FieldTheory.IntermediateField.MaximalAbelian
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField
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

/-- The maximal unramified abelian `p`-extension `Lₙ / Kₙ` of `Kₙ`, defined as an intermediate field
of `Hₙ / Kₙ` where `Hₙ` is the Hilbert class field (`NumberField.HilbertClassField`) of `Kₙ`. -/
noncomputable def Ln (n : ℕ) :=
  IntermediateField.maximalAbelianPExtension (H.Kn n) (NumberField.HilbertClassField (H.Kn n)) p

instance isAbelianGalois_Ln (n : ℕ) : IsAbelianGalois (H.Kn n) (H.Ln n) :=
  IntermediateField.isAbelianGalois_maximalAbelianPExtension _ _ p

instance isUnramifiedEverywhere_Ln (n : ℕ) :
    NumberField.IsUnramifiedEverywhere (H.Kn n) (H.Ln n) :=
  .tower_bot (H.Kn n) (H.Ln n) (NumberField.HilbertClassField (H.Kn n))

instance finiteDimensional_Ln (n : ℕ) : FiniteDimensional (H.Kn n) (H.Ln n) := by
  rw [Ln]
  have := NumberField.HilbertClassField.finiteDimensional (H.Kn n)
  infer_instance

instance numberField_Ln (n : ℕ) : NumberField (H.Ln n) := by
  rw [Ln]
  infer_instance

theorem finrank_Ln (n : ℕ) : Module.finrank (H.Kn n) (H.Ln n) =
    p ^ multiplicity p (NumberField.classNumber (H.Kn n)) := by
  rw [Ln, IntermediateField.finrank_maximalAbelianPExtension_bot,
    NumberField.HilbertClassField.finrank_eq_classNumber,
    Nat.multiplicity_eq_factorization Fact.out (NumberField.classNumber_ne_zero _)]

instance isGalois_K_Ln (n : ℕ) : IsGalois K (H.Ln n) := by
  have := NumberField.HilbertClassField.isGalois_of_isGalois K (H.Kn n)
  exact IntermediateField.isGalois_maximalAbelianPExtension_of_isGalois K _ _ p

end MvZpExtension
