import Iwasawalib.FieldTheory.ZpExtension.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!

# `ℤₚ`-extension of number fields

-/

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} {Kinf : Type v} [Field K]
  [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace IsZpExtension

variable (H : IsZpExtension p K Kinf)

instance charZero_intermediateField [CharZero K] (n : ℕ) :
    CharZero (H.intermediateField n) :=
  charZero_of_injective_algebraMap (algebraMap K _).injective

instance numberField_intermediateField [NumberField K] (n : ℕ) :
    NumberField (H.intermediateField n) where
  to_finiteDimensional := .trans ℚ K _

end IsZpExtension
