import Iwasawalib.NumberTheory.ZpExtension.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!

# Growth of class group of `ℤₚ`-extension of number fields

-/

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} {Kinf : Type v} [Field K] [NumberField K]
  [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace IsZpExtension

variable (H : IsZpExtension p K Kinf)

/-- **Iwasawa's theorem** on growth of class groups of `ℤₚ`-extension
of number fields. -/
theorem multiplicity_classNumber_intermediateField_eq :
    ∃ (muInv lambdaInv nuInv N : ℕ), ∀ n > N,
      multiplicity (NumberField.classNumber (H.intermediateField n)) p =
        muInv * p ^ n + lambdaInv * p + nuInv := by
  sorry

end IsZpExtension
