/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.PrimitiveElement

@[expose] public section

/-!
# Fixing subgroups of simple subextensions

Two small facts used to compare Krull topologies coming from different base fields.

* `IntermediateField.exists_adjoin_simple_eq`: a finite subextension of a separable extension is
  simple (the primitive element theorem, transported from `Field.exists_primitive_element`,
  which states it for the extension itself rather than for a subextension).
* `IntermediateField.mem_fixingSubgroup_adjoin_simple`: an automorphism fixing `α` fixes all of
  `F⟮α⟯`.  Mathlib has `IntermediateField.mem_fixingSubgroup_iff` but nothing reducing the
  check to generators.
-/

namespace IntermediateField

variable (F L : Type*) [Field F] [Field L] [Algebra F L]

/-- A finite subextension of a separable extension is simple. -/
theorem exists_adjoin_simple_eq [Algebra.IsSeparable F L] (E : IntermediateField F L)
    [FiniteDimensional F E] : ∃ α : L, F⟮α⟯ = E := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  exact ⟨α.1, by rw [← IntermediateField.lift_adjoin_simple, hα]; simp⟩

variable {F L}

/-- An automorphism of `L / F` fixing `α` fixes all of `F⟮α⟯`. -/
theorem mem_fixingSubgroup_adjoin_simple {τ : Gal(L/F)} {α : L} (h : τ α = α) :
    τ ∈ (F⟮α⟯).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hle : (F⟮α⟯ : IntermediateField F L)
      ≤ IntermediateField.fixedField (Subgroup.closure {τ}) := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y rfl
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    induction hf using Subgroup.closure_induction with
    | mem x hx => simpa [Set.mem_singleton_iff.1 hx] using h
    | one => rfl
    | mul a b ha hb iha ihb => rw [AlgEquiv.mul_apply, ihb, iha]
    | inv a ha iha =>
        have hinv : a⁻¹ (a y) = y := by
          show (a⁻¹ * a) y = y
          simp
        rw [iha] at hinv
        exact hinv
  exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) τ (Subgroup.subset_closure rfl)

end IntermediateField
