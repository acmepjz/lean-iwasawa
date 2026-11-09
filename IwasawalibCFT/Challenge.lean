/-
Comparator specification: the two deliberate `sorry` placeholders are not library proofs.
This module imports only the root library, never the CFT solution.
-/
import Iwasawalib.NumberTheory.ZpExtension.CyclotomicIwasawa
import Iwasawalib.NumberTheory.ZpExtension.IwasawaTheoremOfHCF

universe u

section Main

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*}
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

theorem multiplicity_classNumber_Kn_eq₁ [Unique ι] :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n > N,
      multiplicity p (NumberField.classNumber (H.Kn n)) = mu * p ^ n + lambda * n + nu := by
  sorry

end MvZpExtension

end Main

namespace NumberField

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]

theorem exists_cyclotomic_multiplicity_classNumber_eq :
    ∃ (Kinf : Type u) (_ : Field Kinf) (_ : Algebra K Kinf) (_ : IsGalois K Kinf)
      (H : MvZpExtension p (Fin 1) K Kinf), IsCyclotomicZpExtension p K Kinf ∧
      ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n > N,
        (multiplicity p (NumberField.classNumber (H.Kn n)) : ℤ) =
          mu * p ^ n + lambda * n + nu := by
  sorry

end NumberField
