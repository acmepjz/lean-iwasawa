import Iwasawalib.FieldTheory.ZpExtension.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!

# `ℤₚ`-extension of number fields

-/

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] [IsGalois k K]

namespace IsZpExtension

variable (H : IsZpExtension p k K)

instance charZero_kn [CharZero k] (n : ℕ) : CharZero (H.kn n) :=
  charZero_of_injective_algebraMap (algebraMap k _).injective

instance numberField_kn [NumberField k] (n : ℕ) : NumberField (H.kn n) where
  to_finiteDimensional := .trans ℚ k _

end IsZpExtension
