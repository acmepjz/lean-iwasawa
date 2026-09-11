/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.FinitePlaceFibre
public import Iwasawalib.NumberTheory.CFT.FiniteAdeleCongr

@[expose] public section

/-!
# The three names of the decomposition group

The fibre of finite places of `L` above a finite place `v` of `K` is described in this
repository in two different ways, which are *equal as sets of places* but are different Lean
types:

* `NumberField.FinitePlaceFibre L v = {w // w.under (𝓞 K) = v}`, a `Gal(L/K)`-set
  (`Iwasawalib/NumberTheory/CFT/FinitePlaceFibre.lean`), used to state the value of the
  Herbrand quotient of the `S`-units;
* `↥(NumberField.placesOver K L v) = {w // w.asIdeal.under (𝓞 K) = v.asIdeal}`, the index set
  of the semilocal factor `∏_{w ∣ v} L_w`
  (`Iwasawalib/NumberTheory/CFT/FiniteAdeleCongr.lean`), used to state Shapiro's lemma.

Accordingly the decomposition group at a place above `v` appears as
`MulAction.stabilizer (L ≃ₐ[K] L) (w : FinitePlaceFibre L v)` on the `S`-unit side and as
`NumberField.decompositionGroup K L w₀` on the idele side.  This file proves that all of these
are **the same subgroup of `Gal(L/K)`**, which is what lets the two halves of the computation
of `h(C_L)` be joined.

## Main definitions

* `NumberField.placesOverMulAction` : the `Gal(L/K)`-action on `↥(placesOver K L v)`.

## Main statements

* `NumberField.stabilizer_placesOver_eq` : `Stab_G(w) = D_w` for `w : ↥(placesOver K L v)`.
* `NumberField.stabilizer_finitePlaceFibre_eq` : `Stab_G(w) = D_w` for
  `w : FinitePlaceFibre L v`.
* `NumberField.coe_finitePlaceFibre_mem_placesOver` : a point of the fibre is a place above
  `v`.
* `NumberField.card_stabilizer_finitePlaceFibre_eq` : the two cardinalities agree — the
  bookkeeping identity actually consumed by the assembly of `h(C_L)`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MulAction

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L] {v : HeightOneSpectrum (𝓞 K)}

/-! ## `placesOver` as a `Gal(L/K)`-set -/

variable (K L v) in
/-- The `Gal(L/K)`-action on the set of finite places of `L` above a finite place `v` of `K`.
The action on `HeightOneSpectrum (𝓞 L)` preserves the place below
(`NumberField.under_smul_heightOneSpectrum`), so it restricts to the fibre. -/
instance placesOverMulAction : MulAction (L ≃ₐ[K] L) ↥(placesOver K L v) where
  smul σ w := ⟨σ • (w : HeightOneSpectrum (𝓞 L)), smul_mem_placesOver w.2 σ⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)

omit [NumberField K] [NumberField L] in
@[simp]
theorem coe_smul_placesOver (σ : L ≃ₐ[K] L) (w : ↥(placesOver K L v)) :
    ((σ • w : ↥(placesOver K L v)) : HeightOneSpectrum (𝓞 L))
      = σ • (w : HeightOneSpectrum (𝓞 L)) := rfl

omit [NumberField K] [NumberField L] in
/-- **The stabiliser of a place in the fibre is its decomposition group.** -/
theorem stabilizer_placesOver_eq (w : ↥(placesOver K L v)) :
    stabilizer (L ≃ₐ[K] L) w = decompositionGroup K L (w : HeightOneSpectrum (𝓞 L)) := by
  ext σ
  rw [mem_stabilizer_iff, mem_decompositionGroup]
  exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩

instance [IsGalois K L] : IsPretransitive (L ≃ₐ[K] L) ↥(placesOver K L v) :=
  ⟨fun w w' ↦ by
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_under_eq (w : HeightOneSpectrum (𝓞 L))
      (w' : HeightOneSpectrum (𝓞 L)) (w.2.trans w'.2.symm)
    exact ⟨σ, Subtype.ext hσ⟩⟩

/-! ## `FinitePlaceFibre` and `placesOver` name the same places -/

omit [NumberField K] [NumberField L] in
/-- A point of `FinitePlaceFibre L v` is a finite place above `v`. -/
theorem coe_finitePlaceFibre_mem_placesOver (w : FinitePlaceFibre L v) :
    (w : HeightOneSpectrum (𝓞 L)) ∈ placesOver K L v :=
  congrArg HeightOneSpectrum.asIdeal w.2

omit [NumberField K] [NumberField L] in
/-- The action on `FinitePlaceFibre L v` is the action on `HeightOneSpectrum (𝓞 L)`. -/
theorem coe_smul_finitePlaceFibre (σ : L ≃ₐ[K] L) (w : FinitePlaceFibre L v) :
    ((σ • w : FinitePlaceFibre L v) : HeightOneSpectrum (𝓞 L))
      = σ • (w : HeightOneSpectrum (𝓞 L)) := by
  rw [FinitePlaceFibre.coe_smul, HeightOneSpectrum.smul_def,
    show RingOfIntegers.mapRingEquiv ((σ : L ≃ₐ[K] L) : L ≃+* L)
      = MulSemiringAction.toRingAut (L ≃ₐ[K] L) (𝓞 L) σ from
      RingEquiv.ext fun x ↦ RingOfIntegers.ext rfl]

omit [NumberField K] [NumberField L] in
/-- **The stabiliser of a point of `FinitePlaceFibre L v` is its decomposition group.**  This
is the bookkeeping identity joining the `S`-unit side of the computation of `h(C_L)`, which is
stated with `FinitePlaceFibre`, to the idele side, which is stated with
`NumberField.decompositionGroup`. -/
theorem stabilizer_finitePlaceFibre_eq (w : FinitePlaceFibre L v) :
    stabilizer (L ≃ₐ[K] L) w = decompositionGroup K L (w : HeightOneSpectrum (𝓞 L)) := by
  ext σ
  rw [mem_stabilizer_iff, mem_decompositionGroup, ← coe_smul_finitePlaceFibre]
  exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩

omit [NumberField K] [NumberField L] in
/-- **The two names of the decomposition group have the same order.** -/
theorem card_stabilizer_finitePlaceFibre_eq (w : FinitePlaceFibre L v) :
    Nat.card (stabilizer (L ≃ₐ[K] L) w)
      = Nat.card (decompositionGroup K L (w : HeightOneSpectrum (𝓞 L))) := by
  rw [stabilizer_finitePlaceFibre_eq]

/-- The point of `FinitePlaceFibre L v` attached to a place above `v`. -/
def placesOverToFibre (w : ↥(placesOver K L v)) : FinitePlaceFibre L v :=
  ⟨(w : HeightOneSpectrum (𝓞 L)), HeightOneSpectrum.ext w.2⟩

omit [NumberField K] [NumberField L] in
@[simp]
theorem coe_placesOverToFibre (w : ↥(placesOver K L v)) :
    (placesOverToFibre w : HeightOneSpectrum (𝓞 L)) = (w : HeightOneSpectrum (𝓞 L)) := rfl

omit [NumberField K] [NumberField L] in
theorem stabilizer_placesOverToFibre_eq (w : ↥(placesOver K L v)) :
    stabilizer (L ≃ₐ[K] L) (placesOverToFibre w) = stabilizer (L ≃ₐ[K] L) w := by
  rw [stabilizer_finitePlaceFibre_eq, coe_placesOverToFibre, stabilizer_placesOver_eq]

end NumberField
