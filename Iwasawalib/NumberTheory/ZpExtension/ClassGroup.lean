import Iwasawalib.NumberTheory.ZpExtension.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!

# Growth of class group of `ℤₚ`-extension of number fields

-/

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {k : Type u} {K : Type v} [Field k] [NumberField k] [Field K] [Algebra k K] [IsGalois k K]

namespace IsZpExtension

variable (H : IsZpExtension p k K)

/-- **Iwasawa's theorem** on growth of class groups of `ℤₚ`-extension
of number fields. -/
theorem multiplicity_classNumber_kn_eq :
    ∃ (mu lambda nu N : ℕ), ∀ n > N,
      multiplicity (NumberField.classNumber (H.kn n)) p = mu * p ^ n + lambda * p + nu := by
  sorry

end IsZpExtension
