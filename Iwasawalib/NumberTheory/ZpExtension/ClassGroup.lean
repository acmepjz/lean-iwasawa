import Iwasawalib.NumberTheory.ZpExtension.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!

# Growth of class group of `ℤₚ`-extension of number fields

-/

universe u v

variable {p : ℕ} [Fact p.Prime] {K : Type u} {Kinf : Type v}
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace IsZpExtension

variable (H : IsZpExtension p K Kinf)

/-- **Iwasawa's theorem** on growth of class groups of `ℤₚ`-extension
of number fields. -/
theorem multiplicity_classNumber_Kn_eq :
    ∃ (mu lambda nu N : ℕ), ∀ n > N,
      multiplicity (NumberField.classNumber (H.Kn n)) p = mu * p ^ n + lambda * p + nu := by
  sorry

end IsZpExtension
