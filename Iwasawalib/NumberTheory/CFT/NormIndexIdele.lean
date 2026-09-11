/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.IdeleClassNormIndex
public import Iwasawalib.NumberTheory.CFT.SIdeleClassEnlarged

@[expose] public section

/-!
# Bounding the norm index `[C_K : N C_L]` by an index of ideles

`Iwasawalib/NumberTheory/CFT/IdeleClassNormIndex.lean` identifies the number bounded by the
first fundamental inequality with the norm index `[C_K : N_{L/K} C_L]`.  Chevalley's proof
bounds that index by exhibiting an explicit subgroup `D ≤ 𝕀_K` consisting of ideles that are
*local* norms everywhere, and then computing the index `[𝕀_K : K^× · D]`.  This file supplies
the two purely formal steps of that reduction, unconditionally and with no hypothesis on the
degree of `L / K`.

The first is elementary group theory: if `f : G → Q` is surjective and `D` maps into `H ≤ Q`,
then `[Q : H] ∣ [G : ker f · D]`.  Applied to `𝕀_K → C_K` it gives
`[C_K : N C_L] ∣ [𝕀_K : K^× · D]` for any `D` whose classes are norms.

The second replaces `𝕀_K` by `𝕀_{K,S}`:  since `𝕀_K = K^× · 𝕀_{K,S}`
(`NumberField.IdeleGroup.principalSubgroup_sup_sIdeleSubgroup_of_subset`) and
`K^× ∩ 𝕀_{K,S} = O_{K,S}^×`
(`NumberField.IdeleGroup.principalSubgroup_inf_sIdeleSubgroup`), for `D ≤ 𝕀_{K,S}` the index
`[𝕀_K : K^× · D]` equals the relative index `[𝕀_{K,S} : O_{K,S}^× · D]` — the index that the
local power-index product of
`Iwasawalib/NumberTheory/CFT/LocalPowerIndexProduct.lean` and the `S`-unit index of
`Iwasawalib/NumberTheory/CFT/SUnitPowerIndex.lean` are there to compute.

## Main statements

* `Subgroup.index_eq_relIndex_inf_of_sup_eq_top`, `Subgroup.inf_sup_eq_of_le`,
  `Subgroup.index_sup_eq_relIndex_of_sup_eq_top`, `Subgroup.index_dvd_index_sup_ker` : the
  group-theoretic input.
* `NumberField.IdeleClassGroup.normSubgroupMul` : `N_{L/K} C_L` written multiplicatively, with
  `mem_normSubgroupMul_iff` and `index_normSubgroupMul`.
* `NumberField.IdeleClassGroup.index_normSubgroup_dvd_index_sup` :
  **`[C_K : N C_L] ∣ [𝕀_K : K^× · D]`** for every subgroup `D` of ideles whose classes are
  norms from `C_L`.
* `NumberField.IdeleClassGroup.index_normSubgroup_dvd_relIndex_sIdele` :
  **`[C_K : N C_L] ∣ [𝕀_{K,S} : O_{K,S}^× · D]`** for such a `D` inside `𝕀_{K,S}`, for any
  `S ⊇ classPlaces K`.

## What is *not* here

Nothing in this file produces such a `D`; that is the local-norm input (`(K_v^×)^ℓ` and, at
places outside `S`, the local units are norms), and it is not proved here.
-/

noncomputable section

open IsDedekindDomain CyclicTate

namespace Subgroup

variable {G : Type*} [Group G]

/-- If `A ⊔ N = ⊤` then the index of `N` in `G` is its relative index inside `A`. -/
theorem index_eq_relIndex_inf_of_sup_eq_top {N A : Subgroup G} [N.Normal] (h : A ⊔ N = ⊤) :
    N.index = (N ⊓ A).relIndex A := by
  rw [inf_relIndex_right, ← relIndex_sup_right A N, h, relIndex_top_right]

variable {G : Type*} [CommGroup G]

/-- In a commutative group, `A ⊓ (P · D) = (P ⊓ A) · D` as soon as `D ≤ A`. -/
theorem inf_sup_eq_of_le {P A D : Subgroup G} (hDA : D ≤ A) :
    A ⊓ (P ⊔ D) = (P ⊓ A) ⊔ D := by
  refine le_antisymm ?_ (le_inf (sup_le inf_le_right hDA)
    (sup_le (le_sup_of_le_left inf_le_left) le_sup_right))
  rintro x ⟨hxA, hxPD⟩
  obtain ⟨p, hp, d, hd, rfl⟩ := Subgroup.mem_sup.1 hxPD
  have hpA : p ∈ A := by
    have hrw : p = (p * d) * d⁻¹ := by group
    rw [hrw]
    exact A.mul_mem hxA (A.inv_mem (hDA hd))
  exact Subgroup.mem_sup.2 ⟨p, ⟨hp, hpA⟩, d, hd, rfl⟩

/-- **The index of `P · D` in `G` is the relative index of `(P ⊓ A) · D` in `A`**, whenever
`P ⊔ A = ⊤` and `D ≤ A`.  With `G = 𝕀_K`, `P = K^×`, `A = 𝕀_{K,S}` and `D` a subgroup of
`S`-ideles this is the passage from the full idele group to the `S`-ideles. -/
theorem index_sup_eq_relIndex_of_sup_eq_top {P A D : Subgroup G} (hPA : P ⊔ A = ⊤)
    (hDA : D ≤ A) : (P ⊔ D).index = ((P ⊓ A) ⊔ D).relIndex A := by
  have htop : A ⊔ (P ⊔ D) = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← hPA]
    exact sup_le (le_sup_of_le_right le_sup_left) le_sup_left
  rw [index_eq_relIndex_inf_of_sup_eq_top htop, inf_comm, inf_sup_eq_of_le hDA]

/-- **The index of a subgroup of the target divides the index of the subgroup it comes from.**

If `f : G → Q` is surjective and every element of `D ≤ G` is carried into `H ≤ Q`, then
`[Q : H]` divides `[G : ker f · D]`. -/
theorem index_dvd_index_sup_ker {Q : Type*} [Group Q] (f : G →* Q) (hf : Function.Surjective f)
    (H : Subgroup Q) (D : Subgroup G) (hD : ∀ u ∈ D, f u ∈ H) :
    H.index ∣ (f.ker ⊔ D).index := by
  have hle : f.ker ⊔ D ≤ H.comap f :=
    sup_le (fun x hx ↦ by simp [MonoidHom.mem_ker.1 hx]) fun x hx ↦ hD x hx
  have := Subgroup.index_dvd_of_le hle
  rwa [H.index_comap_of_surjective hf] at this

end Subgroup

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.galIdeleMulDistribMulAction NumberField.galIdeleClassMulDistribMulAction
  CyclicTate.Additive.distribMulActionOfMulDistrib

namespace NumberField.IdeleClassGroup

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **`N_{L/K} C_L` as a subgroup of `C_K`, in multiplicative notation.** -/
def normSubgroupMul : Subgroup (IdeleClassGroup (𝓞 K) K) :=
  AddSubgroup.toSubgroup' (normSubgroup K L)

variable {K L}

omit [IsGalois K L] in
@[simp] theorem mem_normSubgroupMul_iff (c : IdeleClassGroup (𝓞 K) K) :
    c ∈ normSubgroupMul K L ↔ ∃ d : IdeleClassGroup (𝓞 L) L,
      ∏ g : L ≃ₐ[K] L, g • d = baseChange K L c := by
  rw [normSubgroupMul, AddSubgroup.mem_toSubgroup', mem_normSubgroup_iff_prod]
  rfl

variable (K L)

omit [IsGalois K L] in
@[simp] theorem index_normSubgroupMul :
    (normSubgroupMul K L).index = (normSubgroup K L).index := by
  rw [← Subgroup.index_toAddSubgroup]
  rfl

variable {K L}

omit [IsGalois K L] in
/-- **The norm index is bounded by an index of ideles.**

If every idele in `D` has a class in `C_K` that is a norm from `C_L`, then
`[C_K : N_{L/K} C_L]` divides `[𝕀_K : K^× · D]`. -/
theorem index_normSubgroup_dvd_index_sup (D : Subgroup (IdeleGroup (𝓞 K) K))
    (hD : ∀ u ∈ D, ∃ d : IdeleClassGroup (𝓞 L) L,
      ∏ g : L ≃ₐ[K] L, g • d = baseChange K L (IdeleClassGroup.mk (𝓞 K) K u)) :
    (normSubgroup K L).index ∣ (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ D).index := by
  rw [← index_normSubgroupMul]
  have h := Subgroup.index_dvd_index_sup_ker (IdeleClassGroup.mk (𝓞 K) K)
    (IdeleClassGroup.mk_surjective (𝓞 K) K) (normSubgroupMul K L) D
    fun u hu ↦ (mem_normSubgroupMul_iff _).2 (hD u hu)
  rwa [IdeleClassGroup.ker_mk] at h

omit [IsGalois K L] in
/-- **The class of a norm of ideles is a norm of classes.** -/
theorem mk_mem_normSubgroupMul_of_prod_smul (u : IdeleGroup (𝓞 K) K)
    (b : IdeleGroup (𝓞 L) L) (hb : ∏ g : L ≃ₐ[K] L, g • b = IdeleGroup.baseChange K L u) :
    ∃ d : IdeleClassGroup (𝓞 L) L,
      ∏ g : L ≃ₐ[K] L, g • d = baseChange K L (IdeleClassGroup.mk (𝓞 K) K u) := by
  refine ⟨IdeleClassGroup.mk (𝓞 L) L b, ?_⟩
  rw [baseChange_mk, ← hb, map_prod]
  exact Finset.prod_congr rfl fun g _ ↦ (galIdeleClassAut_mk g b).symm

omit [IsGalois K L] in
/-- **The norm index is bounded by an index of ideles, from norms of ideles.**

The convenient form of `index_normSubgroup_dvd_index_sup`: it suffices that every `u ∈ D` be
the norm `∏_{g ∈ Gal(L/K)} g · b` of an *idele* `b ∈ 𝕀_L`, which is what a construction from
local norms produces. -/
theorem index_normSubgroup_dvd_index_sup_of_idele (D : Subgroup (IdeleGroup (𝓞 K) K))
    (hD : ∀ u ∈ D, ∃ b : IdeleGroup (𝓞 L) L,
      ∏ g : L ≃ₐ[K] L, g • b = IdeleGroup.baseChange K L u) :
    (normSubgroup K L).index ∣ (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ D).index :=
  index_normSubgroup_dvd_index_sup D fun u hu ↦
    let ⟨b, hb⟩ := hD u hu
    mk_mem_normSubgroupMul_of_prod_smul u b hb

omit [IsGalois K L] in
/-- **The norm index is bounded by an index of `S`-ideles.**

For `S ⊇ classPlaces K` and a subgroup `D` of `S`-ideles all of whose classes are norms,
`[C_K : N_{L/K} C_L]` divides the index of `O_{K,S}^× · D` inside `𝕀_{K,S}`. -/
theorem index_normSubgroup_dvd_relIndex_sIdele {S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))}
    (hS : classPlaces K ⊆ S) (D : Subgroup (IdeleGroup (𝓞 K) K))
    (hDS : D ≤ IdeleGroup.sIdeleSubgroup K S)
    (hD : ∀ u ∈ D, ∃ d : IdeleClassGroup (𝓞 L) L,
      ∏ g : L ≃ₐ[K] L, g • d = baseChange K L (IdeleClassGroup.mk (𝓞 K) K u)) :
    (normSubgroup K L).index ∣
      (((S.unit K).map (IdeleGroup.principalEmbedding (𝓞 K) K) ⊔ D).relIndex
        (IdeleGroup.sIdeleSubgroup K S)) := by
  have hsup := IdeleGroup.principalSubgroup_sup_sIdeleSubgroup_of_subset hS
  have h := index_normSubgroup_dvd_index_sup (L := L) D hD
  rwa [Subgroup.index_sup_eq_relIndex_of_sup_eq_top hsup hDS,
    IdeleGroup.principalSubgroup_inf_sIdeleSubgroup] at h

end NumberField.IdeleClassGroup

end
