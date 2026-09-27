/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.UnramifiedTransport
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Frobenius

@[expose] public section

/-!

# Hilbert class field (experimental) - lifting unramified abelian extensions

This file contains `NumberField.IsUnramifiedEverywhere.liftOfIsSepClosed`: an unramified abelian
extension `K / F` of a number field embeds over `F` into the maximal unramified abelian extension
`NumberField.maximalUnramifiedAbelianExtension F L` of `F` inside any separably closed field `L`.

No class field theory is proved or assumed here. The class field theory input of Iwasawa's
theorem is isolated in `Iwasawalib/NumberTheory/NumberField/HilbertClassField/Hypothesis.lean`,
as the two explicit hypotheses `NumberField.HilbertClassFieldUpperBound` and
`NumberField.HilbertClassFieldExistence` of `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf`.

-/

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

namespace NumberField

namespace IsUnramifiedEverywhere

/-- Any unramified abelian extension is a subfield of Hilbert class field. -/
noncomputable def liftOfIsSepClosed
    [NumberField F] [IsAbelianGalois F K] [IsUnramifiedEverywhere F K]
    (L : Type*) [Field L] [Algebra F L] [IsSepClosed L] :
    K →ₐ[F] maximalUnramifiedAbelianExtension F L :=
  letI φ : K →ₐ[F] L := IsSepClosed.lift
  letI e : K ≃ₐ[F] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  haveI : IsAbelianGalois F φ.fieldRange := IsAbelianGalois.of_algEquiv e
  haveI : IsUnramifiedEverywhere F φ.fieldRange := IsUnramifiedEverywhere.of_algEquiv e
  (IntermediateField.inclusion
    (le_maximalUnramifiedAbelianExtension F L φ.fieldRange)).comp e.toAlgHom

end IsUnramifiedEverywhere

end NumberField
