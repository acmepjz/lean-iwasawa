/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldMaximalSubextension
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldOverOriginalBase
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.DedekindBridge
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.Hypothesis
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.UniverseTransport

@[expose] public section

/-!
# The Hilbert class field hypotheses, discharged by external class field theory

This module belongs to the nested Lake package `IwasawalibCFT`. It imports the
external class field theory package `Nyll` from
<https://github.com/n-yamaguchi-0729/ClassFieldTheory>, pinned at
`b9a2dddbf076eb96b768c333fd828d339ab3d9eb` for Lean 4.35.0.
It proves `NumberField.HilbertClassFieldUpperBound` and
`NumberField.HilbertClassFieldExistence` using the upstream module-based proof chain.

The external library constructs, for a number field `K : Type`, the small Hilbert class field
`GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K`: a finite abelian extension of
`K` of degree `classNumber K`, unramified at every finite prime and at every infinite place, into
which every finite abelian everywhere unramified extension of `K` embeds over `K`. Its notion of
unramifiedness is the Dedekind one (every height-one prime of the top ring of integers is
unramified over the base ring of integers, plus Mathlib's `IsUnramifiedAtInfinitePlaces`); the
comparison with Iwasawalib's `NumberField.IsUnramifiedEverywhere` (defined with absolute values)
is `Iwasawalib/NumberTheory/NumberField/HilbertClassField/DedekindBridge.lean`.

External declarations relied on (all in the namespace
`GlobalClassFieldTheory.GlobalClassFields` unless marked `_root_`):
`smallHilbertClassField`, its instances `smallHilbertClassFieldAlgebraOverOriginal`,
`smallHilbertClassFieldIsAbelianGaloisOverOriginal` and
`smallHilbertClassFieldFiniteDimensionalOverOriginal` and its `NumberField` instance,
`smallHilbertClassField_finrank_over_original_eq_classNumber`,
`smallHilbertClassField_isEverywhereUnramified`,
`finiteAbelianExtension_nonempty_algHom_to_smallHilbertClassField_of_everywhereUnramified`, and
`_root_.ramifiedBaseFinitePlaces` with `_root_.mem_ramifiedBaseFinitePlaces_iff`.  Their proofs
are checked by the Lean kernel like everything else; only their statements matter here, and the
statements used are exactly the ones quoted in this docstring.

The external library works with fields in `Type`, so the hypotheses are first proved in universe
`0` and then transported to all universes with
`Iwasawalib/NumberTheory/NumberField/HilbertClassField/UniverseTransport.lean`.

## Main statements

* `NumberField.hilbertClassFieldUpperBound_zero`: `NumberField.HilbertClassFieldUpperBound.{0, 0}`.
* `NumberField.hilbertClassFieldExistence_zero`: `NumberField.HilbertClassFieldExistence.{0, 0}`.
* `NumberField.hilbertClassFieldUpperBound`: `NumberField.HilbertClassFieldUpperBound.{u, v}`.
* `NumberField.hilbertClassFieldExistence`: `NumberField.HilbertClassFieldExistence.{u, v}`.
-/

universe u v

open GlobalClassFieldTheory.GlobalClassFields

namespace NumberField

/-- The upper-bound half of the Hilbert class field theorem for fields in `Type`: a finite
abelian everywhere unramified extension `E / F` embeds over `F` into the small Hilbert class field
of `F`, whose degree is the class number of `F`. -/
theorem hilbertClassFieldUpperBound_zero : HilbertClassFieldUpperBound.{0, 0} := by
  intro F E _ _ _ _ _ _ _
  have : NumberField E := NumberField.of_module_finite F E
  -- Translate unramifiedness into the Dedekind formalism of the external library.
  have hfin := isUnramifiedAt_of_isUnramifiedEverywhere F E
  have : IsUnramifiedAtInfinitePlaces F E :=
    isUnramifiedAtInfinitePlaces_of_isUnramifiedEverywhere F E
  have hram : _root_.ramifiedBaseFinitePlaces (K := F) (L := E) = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.2 fun v hv ↦ ?_
    obtain ⟨P, -, hP⟩ := (_root_.mem_ramifiedBaseFinitePlaces_iff (K := F) (L := E) v).1 hv
    exact hP (hfin P)
  -- Embed `E` into the small Hilbert class field of `F`.
  obtain ⟨φ⟩ :=
    finiteAbelianExtension_nonempty_algHom_to_smallHilbertClassField_of_everywhereUnramified hram
  rw [← smallHilbertClassField_finrank_over_original_eq_classNumber F]
  exact LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) φ.injective

/-- The existence half of the Hilbert class field theorem for fields in `Type`: the small Hilbert
class field of `F`, embedded into a separably closed field `Ω`, lies in the maximal unramified
abelian extension of `F` in `Ω` and has degree the class number of `F`. -/
theorem hilbertClassFieldExistence_zero : HilbertClassFieldExistence.{0, 0} := by
  intro F Ω _ _ _ _ _
  -- The small Hilbert class field is finite, abelian and everywhere unramified over `F`.
  have hEU := smallHilbertClassField_isEverywhereUnramified F
  have : IsUnramifiedAtInfinitePlaces F (smallHilbertClassField F) := hEU.infinitePlaces
  have : IsUnramifiedEverywhere F (smallHilbertClassField F) :=
    isUnramifiedEverywhere_of_isUnramifiedAt F _ hEU.finitePlaces
  -- Embed it into `Ω` over `F`.
  let model := embeddedFiniteUnramifiedAbelianModel F (smallHilbertClassField F) Ω
  have := model.isAbelianGalois
  have := model.isUnramifiedEverywhere
  refine ⟨model.field, le_maximalUnramifiedAbelianExtension F Ω model.field,
    model.finiteDimensional, ?_⟩
  rw [← model.equiv.toLinearEquiv.finrank_eq,
    smallHilbertClassField_finrank_over_original_eq_classNumber F]

/-- The upper-bound half of the Hilbert class field theorem, in arbitrary universes. -/
theorem hilbertClassFieldUpperBound : HilbertClassFieldUpperBound.{u, v} :=
  hilbertClassFieldUpperBound_of_zero hilbertClassFieldUpperBound_zero

/-- The existence half of the Hilbert class field theorem, in arbitrary universes. -/
theorem hilbertClassFieldExistence : HilbertClassFieldExistence.{u, v} :=
  hilbertClassFieldExistence_of_zero hilbertClassFieldExistence_zero

end NumberField
