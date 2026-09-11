/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.FamilyShapiro
public import Iwasawalib.NumberTheory.CFT.InfiniteAdeleBaseChange

@[expose] public section

/-!
# The infinite local factor of the adeles is an induced module

Let `L / K` be a finite Galois extension of number fields and `v` an infinite place of `K`.
`Iwasawalib/NumberTheory/CFT/InfiniteAdeleBaseChange.lean` provides the fibre `Fibre L v` of
infinite places of `L` above `v`, the transitive `Gal(L/K)`-action on it, and the semilocal
decomposition of the infinite adeles into the factors `∏_{w ∣ v} L_w`.  What was missing is the
induced-module structure of a factor; this file supplies it, by exhibiting the family
`w ↦ L_w` over the fibre as an `EquivariantFamily` and applying
`EquivariantFamily.equivRcoind` and `EquivariantFamily.shapiro`.

This is the archimedean counterpart of `Iwasawalib/GroupCohomology/LocalShapiro.lean`.

## Main definitions

* `NumberField.InfiniteAdeleRing.InfiniteLocalProduct L v` : the factor `∏_{w ∣ v} L_w`.
* `NumberField.InfiniteAdeleRing.infiniteFamily` : the equivariant family `w ↦ L_w`.
* `NumberField.InfiniteAdeleRing.infiniteLocalEquivRcoind` : the `Gal(L/K)`-equivariant ring
  isomorphism `∏_{w ∣ v} L_w ≃ Ind_{D_{w₀}}^{Gal(L/K)} L_{w₀}`.
* `NumberField.InfiniteAdeleRing.infiniteLocalShapiro` :
  `Hⁿ(Gal(L/K), ∏_{w ∣ v} L_w) ≅ Hⁿ(D_{w₀}, L_{w₀})`.
* `NumberField.InfiniteAdeleRing.infiniteLocalUnitsShapiro` :
  `Hⁿ(Gal(L/K), ∏_{w ∣ v} L_w^×) ≅ Hⁿ(D_{w₀}, L_{w₀}^×)`.
-/

noncomputable section

open MulAction NumberField.InfinitePlace CategoryTheory

attribute [local instance] Units.mulDistribMulActionRight

namespace NumberField.InfinitePlace.Completion

variable {K L : Type*} [Field K] [Field L] {v : InfinitePlace K} {w : InfinitePlace L}

/-- `Completion.congr` depends only on the underlying function of the isomorphism. -/
theorem congr_congr_equiv {f f' : K ≃+* L} (hff : ∀ x : K, f x = f' x)
    (hf : ∀ x : K, w (f x) = v x) (hf' : ∀ x : K, w (f' x) = v x) (z : v.Completion) :
    congr f v w hf z = congr f' v w hf' z := by
  have h : f = f' := RingEquiv.ext hff
  subst h; rfl

end NumberField.InfinitePlace.Completion

namespace NumberField.InfiniteAdeleRing

variable {K L : Type} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K}

variable (L v) in
/-- The semilocal factor `∏_{w ∣ v} L_w` of the infinite adeles of `L` at an infinite place
`v` of `K`. -/
abbrev InfiniteLocalProduct : Type := ∀ w : Fibre L v, (w : InfinitePlace L).Completion

/-- If `σ` carries the place `w` to `w'`, then `w' ∘ σ = w`. -/
theorem place_comp_of_smul_eq {w w' : Fibre L v} {σ : L ≃ₐ[K] L} (h : σ • w = w') (x : L) :
    (w' : InfinitePlace L) ((σ : L ≃ₐ[K] L) x) = (w : InfinitePlace L) x := by
  have hw : ((w' : InfinitePlace L)) = σ • (w : InfinitePlace L) := by
    rw [← Fibre.coe_smul, h]
  rw [hw, InfinitePlace.smul_apply]
  simp

variable (L v) in
/-- **The completions at the infinite places above `v` form an equivariant family** over the
fibre `Fibre L v`, with `σ : Gal(L/K)` carrying `L_w` to `L_{σ • w}` by continuity from
`σ : L → L`. -/
def infiniteFamily :
    EquivariantFamily (L ≃ₐ[K] L) (Fibre L v) (fun w ↦ (w : InfinitePlace L).Completion) where
  push := fun {w w'} σ h ↦ Completion.congr ((σ : L ≃ₐ[K] L) : L ≃+* L)
    (w : InfinitePlace L) (w' : InfinitePlace L) (place_comp_of_smul_eq h)
  push_one := fun {w} h z ↦ by
    refine (Completion.congr_congr_equiv (f' := RingEquiv.refl L) (fun x ↦ rfl) _ ?_ z).trans ?_
    · exact fun x ↦ rfl
    · exact Completion.congr_refl _ _ z
  push_mul := fun {w w' w''} σ τ h h' h'' z ↦ by
    refine (Completion.congr_trans ((τ : L ≃ₐ[K] L) : L ≃+* L) ((σ : L ≃ₐ[K] L) : L ≃+* L)
      (w : InfinitePlace L) (w' : InfinitePlace L) (w'' : InfinitePlace L) _ _ ?_ z).trans ?_
    · intro x
      show (w'' : InfinitePlace L) ((σ : L ≃ₐ[K] L) ((τ : L ≃ₐ[K] L) x)) = _
      have h1 : ∀ y : L, (w'' : InfinitePlace L) ((σ : L ≃ₐ[K] L) y) = (w' : InfinitePlace L) y := by
        have hw : ((w'' : InfinitePlace L)) = σ • (w' : InfinitePlace L) := by
          rw [← Fibre.coe_smul, h']
        intro y; rw [hw, InfinitePlace.smul_apply]; simp
      have h2 : ∀ y : L, (w' : InfinitePlace L) ((τ : L ≃ₐ[K] L) y) = (w : InfinitePlace L) y := by
        have hw : ((w' : InfinitePlace L)) = τ • (w : InfinitePlace L) := by
          rw [← Fibre.coe_smul, h]
        intro y; rw [hw, InfinitePlace.smul_apply]; simp
      rw [h1, h2]
    · exact Completion.congr_congr_equiv (fun x ↦ rfl) _ _ z

theorem infiniteFamily_push {w w' : Fibre L v} (σ : L ≃ₐ[K] L) (h : σ • w = w')
    (z : (w : InfinitePlace L).Completion) :
    (infiniteFamily L v).push σ h z =
      Completion.congr ((σ : L ≃ₐ[K] L) : L ≃+* L) (w : InfinitePlace L) (w' : InfinitePlace L)
        (place_comp_of_smul_eq h) z := rfl

/-- The `Gal(L/K)`-action on the semilocal factor `∏_{w ∣ v} L_w`, permuting the factors. -/
instance : MulSemiringAction (L ≃ₐ[K] L) (InfiniteLocalProduct L v) :=
  (infiniteFamily L v).piMulSemiringAction

theorem infiniteLocalProduct_smul_apply (σ : L ≃ₐ[K] L) (x : InfiniteLocalProduct L v)
    (w : Fibre L v) :
    (σ • x) w = (infiniteFamily L v).push σ (smul_inv_smul σ w) (x (σ⁻¹ • w)) := rfl

/-- The action of the decomposition group of `w₀` on the completion `L_{w₀}`. -/
instance infiniteDecompositionAction (w₀ : Fibre L v) :
    MulSemiringAction (stabilizer (L ≃ₐ[K] L) w₀) ((w₀ : InfinitePlace L).Completion) :=
  (infiniteFamily L v).stabilizerMulSemiringAction w₀

theorem infiniteDecomposition_smul_def {w₀ : Fibre L v}
    (d : stabilizer (L ≃ₐ[K] L) w₀) (z : (w₀ : InfinitePlace L).Completion) :
    d • z = (infiniteFamily L v).push (d : L ≃ₐ[K] L) (mem_stabilizer_iff.1 d.2) z := rfl

theorem infiniteFamily_isPiAction :
    (infiniteFamily L v).IsPiAction := fun _ _ _ ↦ rfl

theorem infiniteFamily_isStabilizerAction (w₀ : Fibre L v) :
    (infiniteFamily L v).IsStabilizerAction (w₀ := w₀) := fun _ _ ↦ rfl

variable [NumberField K] [NumberField L] [IsGalois K L]

/-- **The infinite local factor is an induced module.**  For a finite Galois extension of
number fields, an infinite place `v` of `K` and a place `w₀` of `L` above `v`, the product
`∏_{w ∣ v} L_w` is `Gal(L/K)`-equivariantly isomorphic to `Ind_{D_{w₀}}^{Gal(L/K)} L_{w₀}`. -/
def infiniteLocalEquivRcoind (w₀ : Fibre L v) :
    InfiniteLocalProduct L v ≃+*
      Subring.rcoind (stabilizer (L ≃ₐ[K] L) w₀) ((w₀ : InfinitePlace L).Completion) :=
  (infiniteFamily L v).equivRcoind (infiniteFamily_isStabilizerAction w₀)

omit [NumberField K] [NumberField L] in
theorem infiniteLocalEquivRcoind_smul (w₀ : Fibre L v) (σ : L ≃ₐ[K] L)
    (x : InfiniteLocalProduct L v) :
    infiniteLocalEquivRcoind w₀ (σ • x) = σ • infiniteLocalEquivRcoind w₀ x :=
  (infiniteFamily L v).equivRcoind_smul _ infiniteFamily_isPiAction σ x

/-- **Shapiro's lemma at an infinite place**:
`Hⁿ(Gal(L/K), ∏_{w ∣ v} L_w) ≅ Hⁿ(D_{w₀}, L_{w₀})`. -/
def infiniteLocalShapiro (w₀ : Fibre L v) (n : ℕ) :
    groupCohomology (EquivariantFamily.repPi (L ≃ₐ[K] L)
      (fun w : Fibre L v ↦ (w : InfinitePlace L).Completion)) n ≅
    groupCohomology (EquivariantFamily.repFactor (L ≃ₐ[K] L)
      (fun w : Fibre L v ↦ (w : InfinitePlace L).Completion) w₀) n :=
  (infiniteFamily L v).shapiro (infiniteFamily_isStabilizerAction w₀)
    infiniteFamily_isPiAction n

/-- **Shapiro's lemma at an infinite place, for the units**:
`Hⁿ(Gal(L/K), ∏_{w ∣ v} L_w^×) ≅ Hⁿ(D_{w₀}, L_{w₀}^×)`. -/
def infiniteLocalUnitsShapiro (w₀ : Fibre L v) (n : ℕ) :
    groupCohomology (EquivariantFamily.repPiUnits (L ≃ₐ[K] L)
      (fun w : Fibre L v ↦ (w : InfinitePlace L).Completion)) n ≅
    groupCohomology (EquivariantFamily.repFactorUnits (L ≃ₐ[K] L)
      (fun w : Fibre L v ↦ (w : InfinitePlace L).Completion) w₀) n :=
  (infiniteFamily L v).shapiroUnits (infiniteFamily_isStabilizerAction w₀)
    infiniteFamily_isPiAction n

end NumberField.InfiniteAdeleRing
