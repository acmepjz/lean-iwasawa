/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Iwasawalib.FieldTheory.ZpExtension.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!

# `ℤₚ`-extension of number fields

-/

universe u v

variable {p : ℕ} [Fact p.Prime] {d : ℕ} {K : Type u} {Kinf : Type v}
variable [Field K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace IsMvZpExtension

variable (H : IsMvZpExtension p d K Kinf)

instance charZero_Kn [CharZero K] (n : ℕ) : CharZero (H.Kn n) :=
  charZero_of_injective_algebraMap (algebraMap K _).injective

instance numberField_Kn [NumberField K] (n : ℕ) : NumberField (H.Kn n) where
  to_finiteDimensional := .trans ℚ K _

end IsMvZpExtension
