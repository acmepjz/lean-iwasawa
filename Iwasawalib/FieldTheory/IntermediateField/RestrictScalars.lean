/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.FieldTheory.IntermediateField.MaximalGaloisSExtension
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section

/-!
# An honest bridge across `IntermediateField.restrictScalars`

Let `L / L' / K` be a tower of fields and let `E : IntermediateField L' L`.  Mathlib's
`IntermediateField.restrictScalars K E : IntermediateField K L` has, by construction, the
*same carrier set* as `E`, so `↥(E.restrictScalars K)` and `↥E` are definitionally equal
types.  Mathlib supplies the lattice-theoretic API for this (`coe_restrictScalars`,
`restrictScalars_toSubalgebra`, `restrictScalars_toSubfield`, `mem_restrictScalars`,
`restrictScalars_injective`, `restrictScalars_top`, `restrictScalars_adjoin`, …) but as of
2026-09 it supplies **no** algebra instances for `↥(E.restrictScalars K)` over the middle
field `L'`, and **no** isomorphism relating the two coercions.  Grepping
`Mathlib/FieldTheory/IntermediateField/` for `restrictScalars` turns up only statements about
the intermediate fields themselves, never about their coercions to types.

That gap is a real obstruction and not a cosmetic one.  Transporting an instance by hand at a
*concrete* intermediate field, as in
```
haveI : IsScalarTower K Kinf ↥(H.Linf.restrictScalars K) := inferInstanceAs (IsScalarTower K Kinf ↥H.Linf)
```
elaborates, because the elaborator unfolds `restrictScalars` happily, and then fails in the
kernel with
```
(kernel) declaration type mismatch
```
or diverges.  The fix is to do the unfolding **once, for an abstract `E`**, where it is
instant, and to package the result as ordinary declarations which can then be instantiated by
substitution alone.  That is what this file does.

## Main definitions

* `IntermediateField.algebraRestrictScalars`, `IntermediateField.isScalarTowerRestrictScalars`:
  the missing instances `Algebra L' ↥(E.restrictScalars K)` and
  `IsScalarTower K L' ↥(E.restrictScalars K)`.
* `IntermediateField.restrictScalarsAlgEquiv`: the `K`-algebra isomorphism
  `↥(E.restrictScalars K) ≃ₐ[K] ↥E`.
* `IntermediateField.restrictScalarsAlgEquiv'`: the same map, as an `L'`-algebra isomorphism.
* `IntermediateField.restrictScalarsAutEquiv`: `Gal(↥(E.restrictScalars K)/K) ≃* Gal(↥E/K)`.

## Main results

* `IntermediateField.isSExtension_restrictScalars`, `IntermediateField.isGalois_restrictScalars`,
  `IntermediateField.finiteDimensional_restrictScalars`: instances transported across the
  bridge, in the direction that is actually needed (from `↥E` to `↥(E.restrictScalars K)`).
-/

namespace IntermediateField

variable (K : Type*) {L' L : Type*} [Field K] [Field L'] [Field L]
  [Algebra K L'] [Algebra L' L] [Algebra K L] [IsScalarTower K L' L]
  (E : IntermediateField L' L)

/-- The `L'`-algebra structure on `↥(E.restrictScalars K)`.  This is the instance Mathlib is
missing; proved once here for an abstract `E`, where the definitional unfolding of
`restrictScalars` is instant, so that instantiating it at a concrete intermediate field never
makes the kernel unfold anything. -/
instance (priority := 100) algebraRestrictScalars : Algebra L' ↥(E.restrictScalars K) :=
  inferInstanceAs (Algebra L' ↥E)

/-- `↥(E.restrictScalars K)` is an `L'`-algebra over `K`. -/
instance (priority := 100) isScalarTowerRestrictScalars :
    IsScalarTower K L' ↥(E.restrictScalars K) :=
  inferInstanceAs (IsScalarTower K L' ↥E)

@[simp]
theorem algebraMap_restrictScalars_apply (x : L') :
    (algebraMap L' ↥(E.restrictScalars K) x : L) = algebraMap L' ↥E x :=
  rfl

/-- **The bridge.**  `↥(E.restrictScalars K)` and `↥E` are isomorphic as `K`-algebras, by the
identity on the underlying set. -/
def restrictScalarsAlgEquiv : ↥(E.restrictScalars K) ≃ₐ[K] ↥E where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The bridge, as an `L'`-algebra isomorphism. -/
def restrictScalarsAlgEquiv' : ↥(E.restrictScalars K) ≃ₐ[L'] ↥E where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable {K E}

@[simp]
theorem coe_restrictScalarsAlgEquiv (x : ↥(E.restrictScalars K)) :
    (restrictScalarsAlgEquiv K E x : L) = (x : L) :=
  rfl

@[simp]
theorem coe_restrictScalarsAlgEquiv_symm (x : ↥E) :
    ((restrictScalarsAlgEquiv K E).symm x : L) = (x : L) :=
  rfl

@[simp]
theorem coe_restrictScalarsAlgEquiv' (x : ↥(E.restrictScalars K)) :
    (restrictScalarsAlgEquiv' K E x : L) = (x : L) :=
  rfl

@[simp]
theorem coe_restrictScalarsAlgEquiv'_symm (x : ↥E) :
    ((restrictScalarsAlgEquiv' K E).symm x : L) = (x : L) :=
  rfl

theorem restrictScalarsAlgEquiv'_toAlgEquiv :
    (restrictScalarsAlgEquiv' K E).restrictScalars K = restrictScalarsAlgEquiv K E :=
  rfl

variable (K E)

/-- The bridge on Galois groups: `Gal(↥(E.restrictScalars K)/K) ≃* Gal(↥E/K)`. -/
noncomputable def restrictScalarsAutEquiv :
    (↥(E.restrictScalars K) ≃ₐ[K] ↥(E.restrictScalars K)) ≃* (↥E ≃ₐ[K] ↥E) :=
  AlgEquiv.autCongr (restrictScalarsAlgEquiv K E)

@[simp]
theorem coe_restrictScalarsAutEquiv_apply (σ : ↥(E.restrictScalars K) ≃ₐ[K] ↥(E.restrictScalars K))
    (x : ↥(E.restrictScalars K)) :
    ((restrictScalarsAutEquiv K E σ ⟨x.1, x.2⟩ : ↥E) : L) = (σ x : L) :=
  rfl

/-! ### Transport of instances -/

/-- `E / K` is a `S`-extension as soon as `↥E` is, in the `K`-algebra structure coming from the
tower. -/
theorem isSExtension_restrictScalars (S : Set ℕ) [IsSExtension K ↥E S] :
    IsSExtension K ↥(E.restrictScalars K) S :=
  IsSExtension.of_algEquiv S (restrictScalarsAlgEquiv K E).symm

theorem isGalois_restrictScalars [IsGalois K ↥E] : IsGalois K ↥(E.restrictScalars K) :=
  ((restrictScalarsAlgEquiv K E).transfer_galois).2 inferInstance

theorem finiteDimensional_restrictScalars [FiniteDimensional K ↥E] :
    FiniteDimensional K ↥(E.restrictScalars K) :=
  (restrictScalarsAlgEquiv K E).symm.toLinearEquiv.finiteDimensional

end IntermediateField
