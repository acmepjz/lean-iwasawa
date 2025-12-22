/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.CharP.IntermediateField
public import Iwasawalib.FieldTheory.ZpExtension.Basic
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

/-!

# `ℤₚ`-extension of number fields

-/

universe u v

variable {p : ℕ} [Fact p.Prime] {d : ℕ} {ι K Kinf : Type*} [Finite ι]
variable [Field K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

instance numberField_Kn [NumberField K] (n : ℕ) : NumberField (H.Kn n) where
  to_finiteDimensional := .trans ℚ K _

end MvZpExtension

namespace IsMvZpExtension

variable (H : IsMvZpExtension p d K Kinf)

instance numberField_Kn [NumberField K] (n : ℕ) : NumberField (H.Kn n) where
  to_finiteDimensional := .trans ℚ K _

end IsMvZpExtension
