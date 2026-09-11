/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic

@[expose] public section

/-!
# A restricted product, cut down outside a finite set, is a plain product

Let `X i` be commutative groups and `N i ≤ X i` subgroups, and form the restricted product
`Πʳ i, [X i, N i]`.  For a set `S` of indices, the elements whose `i`-th component lies in
`N i` for **every** `i ∉ S` form a subgroup `RestrictedProduct.outsideSubgroup N S`.  When `S`
is finite that subgroup carries no restriction at all:

`RestrictedProduct.outsideSubgroup N S ≃* (∀ i : S, X i) × (∀ i : ↥Sᶜ, N i)`

(`RestrictedProduct.outsideSubgroupEquiv`), because the defining condition of the restricted
product — membership in `N i` for cofinitely many `i` — is implied by membership in `N i` for
all `i ∉ S`.

This is the shape in which the `S`-ideles are a *product*, not a restricted product: the group
`𝕀_{L,S}` of `S`-ideles is `∏_{v ∈ S} (∏_{w ∣ v} L_w)ˣ × ∏_{v ∉ S} (∏_{w ∣ v} O_w)ˣ`, and it is
in that form that the Herbrand quotient can be computed factor by factor with Shapiro's lemma.

The group `G` acting is assumed to act on each `X i` **separately**, i.e. to fix each index.
That is exactly the situation for the ideles: `Gal(L/K)` permutes the places of `L` but fixes
each place of `K`, and the restricted product is taken over the places of `K`.

## Main definitions

* `RestrictedProduct.outsideSubgroup` : the subgroup.
* `RestrictedProduct.outsideSubgroupEquiv` : the splitting, for finite `S`.

## Main statements

* `RestrictedProduct.mem_outsideSubgroup`, `RestrictedProduct.coe_outsideMerge`,
  `RestrictedProduct.outsideSubgroupEquiv_apply_fst`,
  `RestrictedProduct.outsideSubgroupEquiv_apply_snd` : the splitting, componentwise.

Equivariance is not stated here in the abstract: the group acting on the ideles acts on each
factor separately only because it fixes each index, and that is a fact about the concrete
situation, proved as `NumberField.finiteSIdeleSemilocalEquiv_smul` in
`Iwasawalib/NumberTheory/CFT/SIdeleSemilocal.lean`.
-/

noncomputable section

open Filter
open scoped RestrictedProduct
open scoped Classical

namespace RestrictedProduct

variable {ι : Type*} {X : ι → Type*} [∀ i, CommGroup (X i)] (N : ∀ i, Subgroup (X i))
  (S : Set ι)

/-- The subgroup of `Πʳ i, [X i, N i]` consisting of the elements whose `i`-th component lies
in `N i` for every index `i ∉ S`. -/
def outsideSubgroup : Subgroup (Πʳ i, [X i, N i]) where
  carrier := {y | ∀ i ∉ S, y i ∈ N i}
  one_mem' i _ := by rw [one_apply]; exact one_mem _
  mul_mem' hy hz i hi := by rw [mul_apply]; exact mul_mem (hy i hi) (hz i hi)
  inv_mem' hy i hi := by rw [inv_apply]; exact inv_mem (hy i hi)

variable {N S}

theorem mem_outsideSubgroup {y : Πʳ i, [X i, N i]} :
    y ∈ outsideSubgroup N S ↔ ∀ i ∉ S, y i ∈ N i := Iff.rfl

variable (N S)

/-- The forward map of `RestrictedProduct.outsideSubgroupEquiv`. -/
def outsideSplit (y : outsideSubgroup N S) : (∀ i : S, X i) × (∀ i : ↥(Sᶜ), N i) :=
  (fun i ↦ (y : Πʳ i, [X i, N i]) (i : ι),
    fun i ↦ ⟨(y : Πʳ i, [X i, N i]) (i : ι), y.2 (i : ι) i.2⟩)

/-- The underlying family of `RestrictedProduct.outsideMerge`. -/
def outsideMergeFun (z : (∀ i : S, X i) × (∀ i : ↥(Sᶜ), N i)) (i : ι) : X i :=
  if h : i ∈ S then z.1 ⟨i, h⟩ else (z.2 ⟨i, h⟩ : X i)

variable {N S}

theorem outsideMergeFun_mem (z : (∀ i : S, X i) × (∀ i : ↥(Sᶜ), N i)) {i : ι} (hi : i ∉ S) :
    outsideMergeFun N S z i ∈ N i := by
  rw [outsideMergeFun, dif_neg hi]
  exact (z.2 ⟨i, hi⟩).2

variable (hS : S.Finite)

include hS

/-- The inverse map of `RestrictedProduct.outsideSubgroupEquiv`: an arbitrary family whose
components lie in `N i` off the finite set `S` is an element of the restricted product, and it
lies in `RestrictedProduct.outsideSubgroup`. -/
def outsideMerge (z : (∀ i : S, X i) × (∀ i : ↥(Sᶜ), N i)) : outsideSubgroup N S :=
  ⟨⟨outsideMergeFun N S z, by
    rw [eventually_cofinite]
    exact hS.subset fun i hi ↦ by
      by_contra h
      exact hi (outsideMergeFun_mem z h)⟩,
   fun i hi ↦ outsideMergeFun_mem z hi⟩

theorem coe_outsideMerge (z : (∀ i : S, X i) × (∀ i : ↥(Sᶜ), N i)) (i : ι) :
    ((outsideMerge hS z : outsideSubgroup N S) : Πʳ i, [X i, N i]) i
      = outsideMergeFun N S z i := rfl

/-- **A restricted product, constrained outside a finite set `S`, is a plain product.**
`{y ∈ Πʳ i, [X i, N i] | ∀ i ∉ S, y i ∈ N i} ≃ (∏_{i ∈ S} X i) × (∏_{i ∉ S} N i)`. -/
def outsideSubgroupEquiv :
    outsideSubgroup N S ≃* (∀ i : S, X i) × (∀ i : ↥(Sᶜ), N i) where
  toFun := outsideSplit N S
  invFun := outsideMerge hS
  left_inv y := by
    refine Subtype.ext (Subtype.ext (funext fun i ↦ ?_))
    show outsideMergeFun N S (outsideSplit N S y) i = _
    rw [outsideMergeFun]
    by_cases h : i ∈ S
    · rw [dif_pos h]; rfl
    · rw [dif_neg h]; rfl
  right_inv z := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ Subtype.ext ?_)
    · show outsideMergeFun N S z (i : ι) = _
      rw [outsideMergeFun, dif_pos i.2]
    · show outsideMergeFun N S z (i : ι) = _
      rw [outsideMergeFun, dif_neg i.2]
  map_mul' y z := rfl

@[simp]
theorem outsideSubgroupEquiv_apply_fst (y : outsideSubgroup N S) (i : S) :
    (outsideSubgroupEquiv hS y).1 i = (y : Πʳ i, [X i, N i]) (i : ι) := rfl

@[simp]
theorem outsideSubgroupEquiv_apply_snd (y : outsideSubgroup N S) (i : ↥(Sᶜ)) :
    ((outsideSubgroupEquiv hS y).2 i : X (i : ι)) = (y : Πʳ i, [X i, N i]) (i : ι) := rfl

end RestrictedProduct
