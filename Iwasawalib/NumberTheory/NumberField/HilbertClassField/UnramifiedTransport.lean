/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.Basic

@[expose] public section

namespace NumberField

/-- `IsUnramifiedEverywhere` can be transferred along an `F`-algebra isomorphism. -/
theorem IsUnramifiedEverywhere.of_algEquiv
    {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K']
    [Algebra.IsAlgebraic F K] [Algebra.IsAlgebraic F K'] [IsUnramifiedEverywhere F K]
    (f : K ≃ₐ[F] K') : IsUnramifiedEverywhere F K' := by
  have H := (isUnramifiedOutside_empty_iff F K F).2 ‹IsUnramifiedEverywhere F K›
  rw [← isUnramifiedOutside_empty_iff F K' F]
  rw [isUnramifiedOutside_iff] at H ⊢
  exact fun v h1 h2 => (AbsoluteValue.isUnramifiedIn_iff_of_algEquiv v f).1 (H v h1 h2)

end NumberField
