/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber

@[expose] public section

/-!

# Growth of class group of `ℤₚ`-extension of number fields

-/

universe u v

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*}
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- **Iwasawa's theorem** on growth of class groups of `ℤₚ`-extension of number fields. -/
theorem multiplicity_classNumber_Kn_eq₁ [Unique ι] :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n > N,
      multiplicity p (NumberField.classNumber (H.Kn n)) = mu * p ^ n + lambda * n + nu := by
  sorry

end MvZpExtension

/-- **Iwasawa's theorem** on growth of class groups of `ℤₚ`-extension of number fields. This is an
alternative statement which depends only on the concepts in Mathlib. Note: the assumption
`∀ n, NumberField (Kn n)` can be derived from other assumptions, but we keep it here to avoid
`haveI` in the statement of the conclusion. -/
theorem NumberField.multiplicity_classNumber_eq_of_finrank_eq_pow {L : Type*} [Field L]
    [Algebra K L] (Kn : ℕ → IntermediateField K L) [∀ n, NumberField (Kn n)]
    [∀ n, IsGalois K (Kn n)] [∀ n, IsCyclic Gal(Kn n/K)]
    (hle : ∀ n, Kn n ≤ Kn (n + 1)) (hfinrank : ∀ n, Module.finrank K (Kn n) = p ^ n) :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n > N,
      multiplicity p (NumberField.classNumber (Kn n)) = mu * p ^ n + lambda * n + nu := by
  sorry
