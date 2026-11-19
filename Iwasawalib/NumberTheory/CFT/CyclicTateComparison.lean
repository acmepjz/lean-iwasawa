/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.Herbrand
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

@[expose] public section

/-!
# The explicit Tate groups are Mathlib's group cohomology

`Iwasawalib/GroupCohomology/CyclicTate.lean` defines, for a finite cyclic group `G = ⟨σ⟩` and
a `G`-module `M`, two explicit quotient groups

`TateH0 G M σ = M^σ / N M`  and  `TateH1 G M σ = ker N / (σ - 1) M`,

and records that no comparison with Mathlib's `groupCohomology` had been proved, so that every
statement about `CyclicTate.herbrand` was a statement about that model alone.  This file
supplies the comparison:

* `CyclicTate.tateH0EquivGroupCohomology` : `TateH0 G M σ ≃+ Hⁱ(G, M)` for every nonzero
  **even** `i`;
* `CyclicTate.tateH1EquivGroupCohomology` : `TateH1 G M σ ≃+ Hⁱ(G, M)` for every **odd** `i`.

Consequently `CyclicTate.herbrand G M σ = #H²(G, M) / #H¹(G, M)`
(`CyclicTate.herbrand_eq_card_groupCohomology`), so all of the Herbrand computations in this
library are statements about honest group cohomology.

Note that `Hⁱ(G, M)` for even `i ≥ 2` is `Ĥ⁰`, the *Tate* group `M^G / N M`, not `H⁰ = M^G`;
the periodicity of the cohomology of a finite cyclic group is what identifies them.

## Implementation

Mathlib's `Rep.FiniteCyclicGroup.groupCohomologyπEven` and `groupCohomologyπOdd` are maps from
the kernels of `ρ(σ) - 1` and of the norm onto `Hⁱ(G, M)`, together with the exact criteria
`groupCohomologyπEven_eq_zero_iff` and `groupCohomologyπOdd_eq_zero_iff` for a class to vanish.
They are epimorphisms in `ModuleCat ℤ`, hence surjective, so each is the quotient map of its
kernel — and its kernel is exactly the subgroup that `TateH0`/`TateH1` divides out.

Mathlib's finite-cyclic file requires `G` to be a `CommGroup` in the same universe as the
coefficient ring, so this comparison is stated for `G M : Type` with `G` commutative.
-/

noncomputable section

open CategoryTheory Rep.FiniteCyclicGroup

namespace CyclicTate

variable (G : Type) [CommGroup G] [Fintype G] (M : Type) [AddCommGroup M]
  [DistribMulAction G M]

/-- A `G`-module, viewed as a `ℤ`-linear representation of `G`. -/
abbrev rep : Rep ℤ G := Rep.ofDistribMulAction ℤ G M

variable {G M}

omit [Fintype G] in
theorem rep_sub_apply (σ : G) (x : M) :
    (Rep.applyAsHom (rep G M) σ - 𝟙 _).hom.toLinearMap x = σ • x - x := by
  simp [Rep.sub_hom, Rep.applyAsHom]

theorem rep_norm_apply (x : M) : (rep G M).norm.asHom.hom.toLinearMap x = normHom G M x := by
  show (∑ g : G, (rep G M).ρ g) x = normHom G M x
  rw [LinearMap.sum_apply, normHom_apply]
  rfl

/-! ## The two kernels -/

variable (σ : G)

/-- The kernel of `ρ(σ) - 1` is the group of `σ`-invariants. -/
def kerSubEquivKer :
    kerSub G M σ ≃+ LinearMap.ker (Rep.applyAsHom (rep G M) σ - 𝟙 _).hom.toLinearMap where
  toFun x := ⟨x.1, by
    show (Rep.applyAsHom (rep G M) σ - 𝟙 _).hom.toLinearMap x.1 = 0
    rw [rep_sub_apply, mem_kerSub.1 x.2, sub_self]⟩
  invFun x := ⟨x.1, mem_kerSub.2 (by
    have h : (Rep.applyAsHom (rep G M) σ - 𝟙 _).hom.toLinearMap x.1 = 0 := x.2
    rw [rep_sub_apply, sub_eq_zero] at h
    exact h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The kernel of the norm endomorphism of the representation is `kerNorm`. -/
def kerNormEquivKer : kerNorm G M ≃+ LinearMap.ker (rep G M).norm.asHom.hom.toLinearMap where
  toFun x := ⟨x.1, by
    show (rep G M).norm.asHom.hom.toLinearMap x.1 = 0
    rw [rep_norm_apply, mem_kerNorm.1 x.2]⟩
  invFun x := ⟨x.1, mem_kerNorm.2 (by
    have h : (rep G M).norm.asHom.hom.toLinearMap x.1 = 0 := x.2
    rwa [rep_norm_apply] at h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-! ## The comparison maps -/

variable (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)

include hσ

/-- The composite `M^σ → Hⁱ(G, M)` for even `i`, as an additive map. -/
def tateH0Hom (i : ℕ) [NeZero i] (hi : Even i) :
    kerSub G M σ →+ (groupCohomology (rep G M) i : ModuleCat ℤ) where
  toFun x := groupCohomologyπEven (rep G M) σ hσ i hi (kerSubEquivKer σ x)
  map_zero' := by
    show groupCohomologyπEven (rep G M) σ hσ i hi (kerSubEquivKer σ 0) = 0
    rw [map_zero, map_zero]
  map_add' x y := by
    show groupCohomologyπEven (rep G M) σ hσ i hi (kerSubEquivKer σ (x + y)) = _
    rw [map_add, map_add]

/-- The composite `ker N → Hⁱ(G, M)` for odd `i`, as an additive map. -/
def tateH1Hom (i : ℕ) (hi : Odd i) :
    kerNorm G M →+ (groupCohomology (rep G M) i : ModuleCat ℤ) where
  toFun x := groupCohomologyπOdd (rep G M) σ hσ i hi (kerNormEquivKer x)
  map_zero' := by
    show groupCohomologyπOdd (rep G M) σ hσ i hi (kerNormEquivKer 0) = 0
    rw [map_zero, map_zero]
  map_add' x y := by
    show groupCohomologyπOdd (rep G M) σ hσ i hi (kerNormEquivKer (x + y)) = _
    rw [map_add, map_add]

theorem tateH0Hom_surjective (i : ℕ) [NeZero i] (hi : Even i) :
    Function.Surjective (tateH0Hom (M := M) σ hσ i hi) := by
  have hπ : Function.Surjective (groupCohomologyπEven (rep G M) σ hσ i hi) := by
    rw [← ModuleCat.epi_iff_surjective]
    unfold groupCohomologyπEven
    haveI : IsIso ((normHomCompSub (rep G M) σ).moduleCatCyclesIso.inv) :=
      Iso.isIso_inv _
    haveI : IsIso ((groupCohomologyIsoEven (rep G M) σ hσ i hi).inv) :=
      Iso.isIso_inv _
    apply epi_comp
  intro y
  obtain ⟨x, hx⟩ := hπ y
  refine ⟨(kerSubEquivKer σ).symm x, ?_⟩
  show groupCohomologyπEven (rep G M) σ hσ i hi (kerSubEquivKer σ ((kerSubEquivKer σ).symm x)) = y
  rw [AddEquiv.apply_symm_apply]
  exact hx

theorem tateH1Hom_surjective (i : ℕ) (hi : Odd i) :
    Function.Surjective (tateH1Hom (M := M) σ hσ i hi) := by
  have hπ : Function.Surjective (groupCohomologyπOdd (rep G M) σ hσ i hi) := by
    rw [← ModuleCat.epi_iff_surjective]
    unfold groupCohomologyπOdd
    haveI : IsIso ((subCompNormHom (rep G M) σ).moduleCatCyclesIso.inv) :=
      Iso.isIso_inv _
    haveI : IsIso ((groupCohomologyIsoOdd (rep G M) σ hσ i hi).inv) :=
      Iso.isIso_inv _
    apply epi_comp
  intro y
  obtain ⟨x, hx⟩ := hπ y
  refine ⟨(kerNormEquivKer (G := G) (M := M)).symm x, ?_⟩
  show groupCohomologyπOdd (rep G M) σ hσ i hi
    (kerNormEquivKer ((kerNormEquivKer (G := G) (M := M)).symm x)) = y
  rw [AddEquiv.apply_symm_apply]
  exact hx

theorem ker_tateH0Hom (i : ℕ) [NeZero i] (hi : Even i) :
    (tateH0Hom (M := M) σ hσ i hi).ker = (rangeNorm G M).addSubgroupOf (kerSub G M σ) := by
  ext x
  constructor
  · intro hx
    have h0 : groupCohomologyπEven (rep G M) σ hσ i hi (kerSubEquivKer σ x) = 0 := hx
    obtain ⟨y, hy⟩ := (groupCohomologyπEven_eq_zero_iff (rep G M) σ hσ i hi _).1 h0
    refine AddSubgroup.mem_addSubgroupOf.2 (mem_rangeNorm.2 ⟨y, ?_⟩)
    rw [← rep_norm_apply]
    exact hy
  · intro hx
    obtain ⟨y, hy⟩ := mem_rangeNorm.1 (AddSubgroup.mem_addSubgroupOf.1 hx)
    show groupCohomologyπEven (rep G M) σ hσ i hi (kerSubEquivKer σ x) = 0
    refine (groupCohomologyπEven_eq_zero_iff (rep G M) σ hσ i hi _).2 ⟨y, ?_⟩
    rw [rep_norm_apply]
    exact hy

theorem ker_tateH1Hom (i : ℕ) (hi : Odd i) :
    (tateH1Hom (M := M) σ hσ i hi).ker = (rangeSub G M σ).addSubgroupOf (kerNorm G M) := by
  ext x
  constructor
  · intro hx
    have h0 : groupCohomologyπOdd (rep G M) σ hσ i hi (kerNormEquivKer x) = 0 := hx
    obtain ⟨y, hy⟩ := (groupCohomologyπOdd_eq_zero_iff (rep G M) σ hσ i hi _).1 h0
    refine AddSubgroup.mem_addSubgroupOf.2 (mem_rangeSub.2 ⟨y, ?_⟩)
    rw [← rep_sub_apply]
    exact hy
  · intro hx
    obtain ⟨y, hy⟩ := mem_rangeSub.1 (AddSubgroup.mem_addSubgroupOf.1 hx)
    show groupCohomologyπOdd (rep G M) σ hσ i hi (kerNormEquivKer x) = 0
    refine (groupCohomologyπOdd_eq_zero_iff (rep G M) σ hσ i hi _).2 ⟨y, ?_⟩
    rw [rep_sub_apply]
    exact hy

/-! ## The comparison isomorphisms -/

/-- **The explicit `Ĥ⁰` is group cohomology in even degrees.**  For a finite cyclic group
`G = ⟨σ⟩` and a `G`-module `M`, the explicit quotient `M^σ / N M` is `Hⁱ(G, M)` for every
nonzero even `i`. -/
def tateH0EquivGroupCohomology (i : ℕ) [NeZero i] (hi : Even i) :
    TateH0 G M σ ≃+ (groupCohomology (rep G M) i : ModuleCat ℤ) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_tateH0Hom (M := M) σ hσ i hi).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (tateH0Hom_surjective (M := M) σ hσ i hi))

/-- **The explicit `Ĥ¹` is group cohomology in odd degrees.** -/
def tateH1EquivGroupCohomology (i : ℕ) (hi : Odd i) :
    TateH1 G M σ ≃+ (groupCohomology (rep G M) i : ModuleCat ℤ) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_tateH1Hom (M := M) σ hσ i hi).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (tateH1Hom_surjective (M := M) σ hσ i hi))

theorem card_tateH0_eq (i : ℕ) [NeZero i] (hi : Even i) :
    Nat.card (TateH0 G M σ) = Nat.card (groupCohomology (rep G M) i : ModuleCat ℤ) :=
  Nat.card_congr (tateH0EquivGroupCohomology (M := M) σ hσ i hi).toEquiv

theorem card_tateH1_eq (i : ℕ) (hi : Odd i) :
    Nat.card (TateH1 G M σ) = Nat.card (groupCohomology (rep G M) i : ModuleCat ℤ) :=
  Nat.card_congr (tateH1EquivGroupCohomology (M := M) σ hσ i hi).toEquiv

/-- **The Herbrand quotient is a ratio of orders of group cohomology groups.** -/
theorem herbrand_eq_card_groupCohomology :
    herbrand G M σ = (Nat.card (groupCohomology (rep G M) 2 : ModuleCat ℤ) : ℚ)
      / (Nat.card (groupCohomology (rep G M) 1 : ModuleCat ℤ) : ℚ) := by
  rw [herbrand_def, card_tateH0_eq (M := M) σ hσ 2 (by decide), card_tateH1_eq (M := M) σ hσ 1 ⟨0, by ring⟩]

end CyclicTate
