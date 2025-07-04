/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Iwasawalib.NumberTheory.ZpExtension.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!

# Growth of class group of `ℤₚ`-extension of number fields

-/

universe u v

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*}
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- **Iwasawa's theorem** on growth of class groups of `ℤₚ`-extension
of number fields. -/
theorem multiplicity_classNumber_Kn_eq₁ [Unique ι] :
    ∃ (mu lambda nu N : ℕ), ∀ n > N,
      multiplicity (NumberField.classNumber (H.Kn n)) p = mu * p ^ n + lambda * p + nu := by
  sorry

end MvZpExtension

namespace IsMvZpExtension

variable (H : IsMvZpExtension p 1 K Kinf)

/-- **Iwasawa's theorem** on growth of class groups of `ℤₚ`-extension
of number fields. -/
theorem multiplicity_classNumber_Kn_eq₁ :
    ∃ (mu lambda nu N : ℕ), ∀ n > N,
      multiplicity (NumberField.classNumber (H.Kn n)) p = mu * p ^ n + lambda * p + nu :=
  H.mvZpExtension.multiplicity_classNumber_Kn_eq₁

end IsMvZpExtension
