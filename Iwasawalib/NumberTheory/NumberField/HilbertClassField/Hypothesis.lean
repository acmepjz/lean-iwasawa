/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.Basic

@[expose] public section

/-!
# Hilbert class field theorems as explicit hypotheses

This file states the two classical Hilbert class field theorems needed downstream as explicit,
universe-polymorphic propositions, and derives their standard consequences for the maximal
unramified abelian extension. Nothing here is proved about class field theory itself: the
hypotheses are meant to be discharged by an external class field theory library.

This file deliberately does not import
`Iwasawalib.NumberTheory.NumberField.HilbertClassField.ClassFieldTheory`, so none of the
instances declared there are in scope.

## Main definitions

* `NumberField.HilbertClassFieldUpperBound`: every finite abelian everywhere unramified extension
  of a number field `F` has degree at most the class number of `F`.
* `NumberField.HilbertClassFieldExistence`: inside any separably closed extension of a number
  field `F` there is a finite abelian everywhere unramified extension of `F` whose degree is the
  class number of `F`.

## Main statements

* `NumberField.finiteDimensional_of_hilbertClassFieldUpperBound`: under the upper bound, every
  (a priori infinite) abelian everywhere unramified extension of `F` is finite.
* `NumberField.finrank_le_classNumber_of_hilbertClassFieldUpperBound`: under the upper bound, every
  abelian everywhere unramified extension of `F` has degree at most the class number.
* `NumberField.finiteDimensional_maximalUnramifiedAbelianExtension_of_hcf`: under the upper bound,
  the maximal unramified abelian extension is finite.
* `NumberField.finrank_maximalUnramifiedAbelianExtension_eq_classNumber_of_hcf`: under both
  hypotheses, the maximal unramified abelian extension inside a separably closed field has degree
  equal to the class number.
-/

universe u v

open IntermediateField

namespace NumberField

/-- The upper-bound half of the Hilbert class field theorem: if `E / F` is a finite abelian
extension of a number field `F` which is unramified at every place (finite and infinite), then
`[E : F]` is at most the class number `h_F` of `F`. (Classically `Gal(E/F)` is a quotient of the
class group of `F` via the Artin map.) -/
def HilbertClassFieldUpperBound : Prop :=
  ∀ (F : Type u) (E : Type v) [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E] [IsUnramifiedEverywhere F E],
    Module.finrank F E ≤ classNumber F

/-- The existence half of the Hilbert class field theorem: for a number field `F` and any
separably closed field `Ω` containing `F`, there is a finite abelian everywhere unramified
extension `E / F` inside `Ω` (so `E` lies in the maximal unramified abelian extension of `F` in
`Ω`) whose degree `[E : F]` equals the class number `h_F` of `F`; namely the Hilbert class field
of `F`. -/
def HilbertClassFieldExistence : Prop :=
  ∀ (F : Type u) (Ω : Type v) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsSepClosed Ω],
    ∃ E : IntermediateField F Ω, E ≤ maximalUnramifiedAbelianExtension F Ω ∧
      FiniteDimensional F E ∧ Module.finrank F E = classNumber F

/-- Assuming the upper-bound half of the Hilbert class field theorem, every abelian everywhere
unramified extension `K / F` of a number field `F` is finite, although `K` is not assumed to be
finite over `F`. -/
theorem finiteDimensional_of_hilbertClassFieldUpperBound
    (hU : HilbertClassFieldUpperBound.{u, v}) (F : Type u) (K : Type v) [Field F] [NumberField F]
    [Field K] [Algebra F K] [IsAbelianGalois F K] [IsUnramifiedEverywhere F K] :
    FiniteDimensional F K := by
  classical
  -- Every finite subextension is abelian and unramified, hence of degree at most `h_F`.
  have hbound : ∀ E : IntermediateField F K, FiniteDimensional F E →
      Module.finrank F E ≤ classNumber F := by
    intro E hE
    have : IsUnramifiedEverywhere F E := IsUnramifiedEverywhere.tower_bot F E K
    exact hU F E
  let P : ℕ → Prop := fun n ↦
    ∃ E : IntermediateField F K, FiniteDimensional F E ∧ Module.finrank F E = n
  have hP : P (Module.finrank F (⊥ : IntermediateField F K)) := ⟨⊥, inferInstance, rfl⟩
  -- Pick a finite subextension `E` of maximal degree.
  obtain ⟨E, hEfin, hEn⟩ : P (Nat.findGreatest P (classNumber F)) :=
    Nat.findGreatest_spec (hbound ⊥ inferInstance) hP
  have hmax : ∀ E' : IntermediateField F K, FiniteDimensional F E' →
      Module.finrank F E' ≤ Module.finrank F E := fun E' hE' ↦
    hEn ▸ Nat.le_findGreatest (hbound E' hE') ⟨E', hE', rfl⟩
  -- Every element of `K` lies in `E`.
  have htop : E = ⊤ := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    have : FiniteDimensional F F⟮x⟯ :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have hle : E ≤ E ⊔ F⟮x⟯ := le_sup_left
    have heq : E = E ⊔ F⟮x⟯ :=
      IntermediateField.eq_of_le_of_finrank_le hle (hmax _ inferInstance)
    rw [heq]
    exact (le_sup_right : F⟮x⟯ ≤ E ⊔ F⟮x⟯) (IntermediateField.mem_adjoin_simple_self F x)
  subst htop
  exact (IntermediateField.topEquiv : (⊤ : IntermediateField F K) ≃ₐ[F] K).toLinearEquiv
    |>.finiteDimensional

/-- Assuming the upper-bound half of the Hilbert class field theorem, every abelian everywhere
unramified extension `K / F` of a number field `F` has degree at most the class number of `F`. -/
theorem finrank_le_classNumber_of_hilbertClassFieldUpperBound
    (hU : HilbertClassFieldUpperBound.{u, v}) (F : Type u) (K : Type v) [Field F] [NumberField F]
    [Field K] [Algebra F K] [IsAbelianGalois F K] [IsUnramifiedEverywhere F K] :
    Module.finrank F K ≤ classNumber F :=
  haveI := finiteDimensional_of_hilbertClassFieldUpperBound hU F K
  hU F K

/-- Assuming the upper-bound half of the Hilbert class field theorem, the maximal unramified
abelian extension of a number field `F` inside any field `Ω` is finite over `F`. -/
theorem finiteDimensional_maximalUnramifiedAbelianExtension_of_hcf
    (hU : HilbertClassFieldUpperBound.{u, v}) (F : Type u) (Ω : Type v) [Field F] [NumberField F]
    [Field Ω] [Algebra F Ω] :
    FiniteDimensional F (maximalUnramifiedAbelianExtension F Ω) :=
  finiteDimensional_of_hilbertClassFieldUpperBound hU F (maximalUnramifiedAbelianExtension F Ω)

/-- Assuming both halves of the Hilbert class field theorem, the maximal unramified abelian
extension of a number field `F` inside a separably closed field `Ω` has degree over `F` equal to
the class number of `F`. -/
theorem finrank_maximalUnramifiedAbelianExtension_eq_classNumber_of_hcf
    (hU : HilbertClassFieldUpperBound.{u, v}) (hE : HilbertClassFieldExistence.{u, v})
    (F : Type u) (Ω : Type v) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsSepClosed Ω] :
    Module.finrank F (maximalUnramifiedAbelianExtension F Ω) = classNumber F := by
  refine le_antisymm
    (finrank_le_classNumber_of_hilbertClassFieldUpperBound hU F
      (maximalUnramifiedAbelianExtension F Ω)) ?_
  obtain ⟨E, hEle, -, hEn⟩ := hE F Ω
  have := finiteDimensional_maximalUnramifiedAbelianExtension_of_hcf hU F Ω
  exact hEn ▸ IntermediateField.finrank_le_of_le_right hEle

end NumberField
