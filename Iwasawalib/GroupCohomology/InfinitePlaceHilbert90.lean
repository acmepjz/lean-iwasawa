/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.Hilbert90
public import Iwasawalib.GroupCohomology.InfinitePlaceShapiro

@[expose] public section

/-!
# Hilbert 90 for the infinite local factors of the ideles

The decomposition group of an infinite place `w₀` of `L` acts faithfully on the completion
`L_{w₀}` (an element acting trivially on `L_{w₀}` acts trivially on the image of `L`, which is
embedded in `L_{w₀}`), so `Iwasawalib/GroupCohomology/Hilbert90.lean` applies and gives
`H¹(D_{w₀}, L_{w₀}^×) = 0`.  With Shapiro's lemma
(`NumberField.InfiniteAdeleRing.infiniteLocalUnitsShapiro`) this gives

`H¹(Gal(L/K), ∏_{w ∣ v} L_w^×) = 0`

at every infinite place `v` of `K`: the archimedean counterpart of
`Iwasawalib/GroupCohomology/LocalHilbert90.lean`.
-/

noncomputable section

open MulAction NumberField.InfinitePlace CategoryTheory

attribute [local instance] Units.mulDistribMulActionRight

namespace NumberField.InfiniteAdeleRing

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois K L] {v : InfinitePlace K}

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- The decomposition group acts on the image of `L` in the completion through its action
on `L`. -/
theorem infiniteDecomposition_smul_algebraMap {w₀ : Fibre L v}
    (d : stabilizer (L ≃ₐ[K] L) w₀) (y : L) :
    d • (algebraMap L ((w₀ : InfinitePlace L).Completion) y)
      = algebraMap L ((w₀ : InfinitePlace L).Completion) ((d : L ≃ₐ[K] L) y) := by
  rw [infiniteDecomposition_smul_def, infiniteFamily_push]
  exact Completion.congr_algebraMap _ _ _ _ y

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- The decomposition group of an infinite place `w₀` acts faithfully on the completion
`L_{w₀}`. -/
theorem infiniteDecomposition_smul_injective (w₀ : Fibre L v) :
    Function.Injective fun (d : stabilizer (L ≃ₐ[K] L) w₀) ↦
      (fun z : (w₀ : InfinitePlace L).Completion ↦ d • z) := by
  intro d d' h
  refine Subtype.ext (AlgEquiv.ext fun y ↦ ?_)
  have hy : (d : stabilizer (L ≃ₐ[K] L) w₀) •
      (algebraMap L ((w₀ : InfinitePlace L).Completion) y)
      = (d' : stabilizer (L ≃ₐ[K] L) w₀) •
        (algebraMap L ((w₀ : InfinitePlace L).Completion) y) := congrFun h _
  rw [infiniteDecomposition_smul_algebraMap, infiniteDecomposition_smul_algebraMap] at hy
  exact (algebraMap L ((w₀ : InfinitePlace L).Completion)).injective hy

omit [IsGalois K L] in
/-- **Hilbert 90 at an infinite place**: `H¹(D_{w₀}, L_{w₀}^×) = 0`. -/
theorem H1_infiniteCompletionUnits_eq_zero (w₀ : Fibre L v)
    (x : groupCohomology (EquivariantFamily.repFactorUnits (L ≃ₐ[K] L)
      (fun w : Fibre L v ↦ (w : InfinitePlace L).Completion) w₀) 1) : x = 0 :=
  groupCohomology.H1_units_eq_zero (infiniteDecomposition_smul_injective w₀) x

/-- **The infinite local factor of the ideles at `v` has trivial `H¹`**:
`H¹(Gal(L/K), ∏_{w ∣ v} L_w^×) = 0`. -/
theorem H1_infiniteLocalUnits_eq_zero (w₀ : Fibre L v)
    (x : groupCohomology (EquivariantFamily.repPiUnits (L ≃ₐ[K] L)
      (fun w : Fibre L v ↦ (w : InfinitePlace L).Completion)) 1) : x = 0 := by
  set e := infiniteLocalUnitsShapiro w₀ 1 with he
  have hx : e.hom.hom x = 0 := H1_infiniteCompletionUnits_eq_zero w₀ _
  have hinv : e.inv.hom (e.hom.hom x) = x := Iso.hom_inv_id_apply e x
  rw [← hinv, hx, map_zero]

end NumberField.InfiniteAdeleRing
