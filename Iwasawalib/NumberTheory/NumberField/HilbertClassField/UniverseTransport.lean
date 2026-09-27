/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.Finiteness.Small
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.ExistencePlumbing
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.Hypothesis

@[expose] public section

/-!
# Universe transport for the Hilbert class field hypotheses

The propositions `NumberField.HilbertClassFieldUpperBound` and
`NumberField.HilbertClassFieldExistence` are universe polymorphic. An external class field theory
library may only prove them for fields in `Type`. This file shows that the `Type` versions imply
the versions in arbitrary universes. A number field is countable, hence `Small.{0}`, so it can be
replaced by an isomorphic copy `Shrink.{0} F` in `Type`, and all the relevant data (number field
structure, finiteness and degree, abelian Galois property, unramifiedness at every place, class
number) is invariant under compatible ring isomorphisms.

## Main statements

* `NumberField.classNumber_eq_of_ringEquiv`: isomorphic number fields have the same class number.
* `NumberField.IsUnramifiedEverywhere.of_equiv_equiv`: being unramified everywhere is transported
  along compatible ring isomorphisms of the base and the extension.
* `NumberField.hilbertClassFieldUpperBound_of_zero`: the upper-bound half of the Hilbert class
  field theorem for fields in `Type` implies it in all universes.
* `NumberField.hilbertClassFieldExistence_of_zero`: the existence half of the Hilbert class field
  theorem for fields in `Type` implies it in all universes.
-/

universe u v

namespace NumberField

/-- Isomorphic number fields have the same class number. -/
theorem classNumber_eq_of_ringEquiv {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] (e : K ≃+* L) : classNumber K = classNumber L :=
  Fintype.card_congr (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv e)).toEquiv

/-- If `K / F` and `K' / F'` are algebraic extensions and `f : F ≃+* F'`, `g : K ≃+* K'` are ring
isomorphisms compatible with the algebra maps, then `K' / F'` is unramified everywhere if
`K / F` is. -/
theorem IsUnramifiedEverywhere.of_equiv_equiv {F K F' K' : Type*} [Field F] [Field K]
    [Algebra F K] [Algebra.IsAlgebraic F K] [Field F'] [Field K'] [Algebra F' K']
    [Algebra.IsAlgebraic F' K'] {f : F ≃+* F'} {g : K ≃+* K'}
    (hcomp : (algebraMap F' K').comp (f : F →+* F') = (g : K →+* K').comp (algebraMap F K))
    [H : IsUnramifiedEverywhere F K] : IsUnramifiedEverywhere F' K' := by
  rw [isUnramifiedEverywhere_iff] at H ⊢
  intro v hv
  refine (AbsoluteValue.isUnramified_comp_ringEquiv_iff v f.surjective hcomp).1 (H _ ?_)
  obtain ⟨x, hx0, hx1⟩ := hv
  exact ⟨g.symm x, by simpa using hx0, by simpa [AbsoluteValue.comp_apply] using hx1⟩

/-- The upper-bound half of the Hilbert class field theorem for number fields and extensions
in `Type` implies it in arbitrary universes. -/
theorem hilbertClassFieldUpperBound_of_zero (h : HilbertClassFieldUpperBound.{0, 0}) :
    HilbertClassFieldUpperBound.{u, v} := by
  intro F E _ _ _ _ _ _ _
  have : Small.{0} F := Module.Finite.small ℚ F
  have : Small.{0} E := Module.Finite.small F E
  let e : F ≃+* Shrink.{0} F := (Shrink.ringEquiv F).symm
  let g : E ≃+* Shrink.{0} E := (Shrink.ringEquiv E).symm
  -- The algebra structure on the shrunk copies, transported along `e` and `g`.
  let _ : Algebra (Shrink.{0} F) (Shrink.{0} E) :=
    ((g : E →+* Shrink.{0} E).comp ((algebraMap F E).comp (e.symm : Shrink.{0} F →+* F))).toAlgebra
  have hcomp : (algebraMap (Shrink.{0} F) (Shrink.{0} E)).comp (e : F →+* Shrink.{0} F) =
      (g : E →+* Shrink.{0} E).comp (algebraMap F E) := by
    ext x
    simp [RingHom.algebraMap_toAlgebra]
  have : NumberField (Shrink.{0} F) := .of_ringEquiv F _ e
  have : FiniteDimensional (Shrink.{0} F) (Shrink.{0} E) := .of_equiv_equiv e g hcomp
  have : IsAbelianGalois (Shrink.{0} F) (Shrink.{0} E) := .of_equiv_equiv hcomp
  have : IsUnramifiedEverywhere (Shrink.{0} F) (Shrink.{0} E) := .of_equiv_equiv hcomp
  rw [Algebra.finrank_eq_of_equiv_equiv e g hcomp, classNumber_eq_of_ringEquiv e]
  exact h _ _

/-- The existence half of the Hilbert class field theorem for number fields and separably closed
fields in `Type` implies it in arbitrary universes. -/
theorem hilbertClassFieldExistence_of_zero (h : HilbertClassFieldExistence.{0, 0}) :
    HilbertClassFieldExistence.{u, v} := by
  intro F Ω _ _ _ _ _
  have : Small.{0} F := Module.Finite.small ℚ F
  let e : F ≃+* Shrink.{0} F := (Shrink.algEquiv F F).symm.toRingEquiv
  have he : ∀ y : F, algebraMap F (Shrink.{0} F) y = e y := fun y ↦
    ((Shrink.algEquiv F F).symm.commutes y).symm
  have : NumberField (Shrink.{0} F) := .of_ringEquiv F _ e
  -- A Hilbert class field `E₀` of the copy `Shrink.{0} F` inside its algebraic closure.
  obtain ⟨E₀, hE₀, hfin, hrank⟩ := h (Shrink.{0} F) (AlgebraicClosure (Shrink.{0} F))
  obtain ⟨_, _⟩ := (le_maximalUnramifiedAbelianExtension_iff _ _ E₀).1 hE₀
  -- `E₀` is also an extension of `F`, through `F ≃+* Shrink.{0} F`.
  have hcomp : (algebraMap F E₀).comp (e.symm : Shrink.{0} F →+* F) =
      ((RingEquiv.refl E₀ : E₀ ≃+* E₀) : E₀ →+* E₀).comp (algebraMap (Shrink.{0} F) E₀) := by
    ext x
    simp [IsScalarTower.algebraMap_apply F (Shrink.{0} F) E₀, he]
  have : FiniteDimensional F E₀ := .of_equiv_equiv e.symm (.refl _) hcomp
  have : IsAbelianGalois F E₀ := .of_equiv_equiv hcomp
  have : IsUnramifiedEverywhere F E₀ := .of_equiv_equiv hcomp
  -- Embed `E₀` into `Ω` over `F`.
  let model := embeddedFiniteUnramifiedAbelianModel F E₀ Ω
  have := model.isAbelianGalois
  have := model.isUnramifiedEverywhere
  refine ⟨model.field, le_maximalUnramifiedAbelianExtension F Ω model.field,
    model.finiteDimensional, ?_⟩
  rw [← model.equiv.toLinearEquiv.finrank_eq,
    ← Algebra.finrank_eq_of_equiv_equiv e.symm (.refl _) hcomp, hrank,
    classNumber_eq_of_ringEquiv e]

end NumberField
