/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.IdeleClassFixedPoints

@[expose] public section

/-!
# `Ĥ⁰(Gal(L/K), C_L)` is the norm quotient `C_K / N_{L/K} C_L`

`Iwasawalib/NumberTheory/CFT/IdeleClassFixedPoints.lean` identifies the numerator of
`Ĥ⁰(Gal(L/K), C_L) = ker(σ - 1) / N C_L` with `C_K`.  This file draws the consequence at the
level of *orders*: the number that the two fundamental inequalities bound is literally the norm
index

`#Ĥ⁰(Gal(L/K), C_L) = [C_K : N_{L/K} C_L]`.

## Main definitions and statements

* `NumberField.IdeleClassGroup.normSubgroup` : the subgroup `N_{L/K} C_L` of `C_K`, defined as
  the preimage under `C_K → C_L` of the image of the norm `c ↦ ∏ σ, σ • c`.  Because `C_K → C_L`
  is injective (`NumberField.IdeleClassGroup.baseChange_injective`) and the norms are
  `Gal(L/K)`-invariant, this preimage really is the group of norms.
* `NumberField.IdeleClassGroup.mem_normSubgroup_iff` : membership is `∃ d : C_L, N d = c`.
* `NumberField.IdeleClassGroup.card_tateH0_eq_index_normSubgroup` :
  `#Ĥ⁰(Gal(L/K), C_L) = [C_K : N_{L/K} C_L]`.
-/

noncomputable section

open IsDedekindDomain CyclicTate

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.galIdeleMulDistribMulAction NumberField.galIdeleClassMulDistribMulAction
  CyclicTate.Additive.distribMulActionOfMulDistrib

namespace NumberField.IdeleClassGroup

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- The base change `C_K → C_L`, read additively. -/
def baseChangeAdd :
    Additive (IdeleClassGroup (𝓞 K) K) →+ Additive (IdeleClassGroup (𝓞 L) L) :=
  (baseChange K L).toAdditive

omit [IsGalois K L] in
@[simp] theorem baseChangeAdd_apply (c : Additive (IdeleClassGroup (𝓞 K) K)) :
    Additive.toMul (baseChangeAdd K L c) = baseChange K L (Additive.toMul c) := rfl

/-- **The group of norms `N_{L/K} C_L`, as a subgroup of `C_K`.** -/
def normSubgroup : AddSubgroup (Additive (IdeleClassGroup (𝓞 K) K)) :=
  (rangeNorm (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L))).comap (baseChangeAdd K L)

variable {K L}

omit [IsGalois K L] in
theorem mem_normSubgroup_iff (c : Additive (IdeleClassGroup (𝓞 K) K)) :
    c ∈ normSubgroup K L ↔ ∃ d : Additive (IdeleClassGroup (𝓞 L) L),
      ∑ g : L ≃ₐ[K] L, g • d = baseChangeAdd K L c := by
  rw [normSubgroup, AddSubgroup.mem_comap, mem_rangeNorm]
  simp only [CyclicTate.normHom_apply]

omit [IsGalois K L] in
/-- The same, in multiplicative notation on the idele class groups: `c ∈ C_K` is a norm exactly
when its image in `C_L` is `∏ σ, σ • d` for some `d ∈ C_L`. -/
theorem mem_normSubgroup_iff_prod (c : Additive (IdeleClassGroup (𝓞 K) K)) :
    c ∈ normSubgroup K L ↔ ∃ d : IdeleClassGroup (𝓞 L) L,
      ∏ g : L ≃ₐ[K] L, g • d = baseChange K L (Additive.toMul c) := by
  rw [mem_normSubgroup_iff]
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨Additive.toMul d, ?_⟩
    have := congrArg Additive.toMul hd
    rwa [_root_.toMul_sum] at this
  · rintro ⟨d, hd⟩
    refine ⟨Additive.ofMul d, ?_⟩
    refine Additive.toMul.injective ?_
    rwa [_root_.toMul_sum]

variable {σ : L ≃ₐ[K] L}

/-- The image of `C_K` in `C_L` is the numerator of `Ĥ⁰`. -/
theorem range_baseChangeAdd_eq_kerSub (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g) :
    (baseChangeAdd K L).range
      = kerSub (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ := by
  ext c
  rw [mem_kerSub_iff_mem_range_baseChange hgen]
  exact ⟨by rintro ⟨d, rfl⟩; exact ⟨Additive.toMul d, rfl⟩,
    by rintro ⟨d, hd⟩; exact ⟨Additive.ofMul d, Additive.toMul.injective hd⟩⟩

/-- **`#Ĥ⁰(Gal(L/K), C_L) = [C_K : N_{L/K} C_L]`.**

The Tate group whose order the first and second fundamental inequalities bound is the honest
norm quotient of the classical statement `[C_K : N_{L/K} C_L] ≤ [L : K]`. -/
theorem card_tateH0_eq_index_normSubgroup (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g) :
    Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      = (normSubgroup K L).index := by
  rw [normSubgroup, AddSubgroup.index_comap, range_baseChangeAdd_eq_kerSub hgen]
  rfl

end NumberField.IdeleClassGroup
