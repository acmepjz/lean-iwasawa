/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.Basic
public import Iwasawalib.NumberTheory.ZpExtension.IwasawaTheorem
public import Mathlib.NumberTheory.NumberField.ClassNumber

@[expose] public section

/-!

# Growth of class group of `ℤₚ`-extension of number fields

This file states **Iwasawa's theorem** on the growth of class numbers in a `ℤₚ`-extension
`K∞ / K` of a number field (Washington, *Introduction to cyclotomic fields*, Theorem 13.13):
`ord_p #Cl(Kₙ) = μ pⁿ + λ n + ν` for all sufficiently large `n`.

The proof is `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_cft`
(`Iwasawalib/NumberTheory/ZpExtension/IwasawaTheorem.lean`).  It is **conditional on class
field theory**: `#print axioms MvZpExtension.multiplicity_classNumber_Kn_eq₁` shows `sorryAx`,
which enters only through the class field theory `sorry`s of
`Iwasawalib/NumberTheory/NumberField/HilbertClassField/ClassFieldTheory.lean`.

## Main statements

* `MvZpExtension.multiplicity_classNumber_Kn_eq₁`: **Iwasawa's theorem**.  Not unconditional,
  see its docstring.

-/

universe u v

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*}
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- **Iwasawa's theorem** on growth of class groups of `ℤₚ`-extension of number fields
(Washington, *Introduction to cyclotomic fields*, Theorem 13.13): for a `ℤₚ`-extension
`K∞ / K` of a number field with layers `Kₙ` there are natural numbers `μ`, `λ`, an integer `ν`
and a bound `N` such that `ord_p #Cl(Kₙ) = μ pⁿ + λ n + ν` for all `n > N`.

It is proved by `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_cft`, which has the same
statement.

**Warning**: this theorem is *not* unconditional.  `#print axioms` shows `sorryAx`, which
enters only through the class field theory `sorry`s of
`Iwasawalib/NumberTheory/NumberField/HilbertClassField/ClassFieldTheory.lean`:
`NumberField.IsUnramifiedEverywhere.artinMap` (a definition by `sorry`),
`NumberField.IsUnramifiedEverywhere.surjective_artinMap` and
`NumberField.IsUnramifiedEverywhere.bijective_artinMap_of_isSepClosed`.  It becomes
unconditional as soon as those are proved. -/
theorem multiplicity_classNumber_Kn_eq₁ [Unique ι] :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n > N,
      multiplicity p (NumberField.classNumber (H.Kn n)) = mu * p ^ n + lambda * n + nu := by
  exact H.multiplicity_classNumber_Kn_eq₁_of_cft

end MvZpExtension
