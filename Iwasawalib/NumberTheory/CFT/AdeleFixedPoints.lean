/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.AdeleBaseChange
public import Iwasawalib.NumberTheory.CFT.InfiniteLocalGalois
public import Iwasawalib.NumberTheory.CFT.LocalGalois

@[expose] public section

/-!
# `(𝔸_L)^{Gal(L/K)} = 𝔸_K`

For a finite Galois extension of number fields `L / K`, the `Gal(L/K)`-invariants of the adele
ring of `L` are exactly the image of the adele ring of `K`, and likewise for the idele group.
-/

noncomputable section

open IsDedekindDomain NumberField.InfinitePlace

namespace NumberField.AdeleRing

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **`(𝔸_L)^{Gal(L/K)} ⊆ 𝔸_K`.** -/
theorem mem_range_baseChange_of_fixed {a : AdeleRing (𝓞 L) L}
    (ha : ∀ σ : L ≃ₐ[K] L, adeleMap (σ : L ≃+* L) a = a) :
    a ∈ (baseChange K L).range := by
  have h₁ : ∀ σ : L ≃ₐ[K] L,
      infiniteAdeleMap (σ : L ≃+* L) (AdeleRing.prodEquiv (𝓞 L) L a).1
        = (AdeleRing.prodEquiv (𝓞 L) L a).1 := fun σ ↦ by
    rw [← adeleMap_fst (σ : L ≃+* L) a, ha σ]
  have h₂ : ∀ σ : L ≃ₐ[K] L, σ • (AdeleRing.prodEquiv (𝓞 L) L a).2
      = (AdeleRing.prodEquiv (𝓞 L) L a).2 := fun σ ↦ by
    rw [finiteAdele_smul_def, ← adeleMap_snd (σ : L ≃+* L) a, ha σ]
  obtain ⟨b₁, hb₁⟩ := mem_range_infiniteAdeleBaseChange_of_fixed h₁
  obtain ⟨b₂, hb₂⟩ := mem_range_finiteAdeleBaseChange_of_fixed h₂
  refine ⟨(AdeleRing.prodEquiv (𝓞 K) K).symm (b₁, b₂), ?_⟩
  refine (AdeleRing.prodEquiv (𝓞 L) L).injective (Prod.ext ?_ ?_)
  · exact (baseChange_fst _).trans hb₁
  · exact (baseChange_snd _).trans hb₂

/-- **`(𝔸_L)^{Gal(L/K)} = 𝔸_K`.**  The set of `Gal(L/K)`-invariant adeles of `L` is exactly
the image of the adele ring of `K`. -/
theorem range_baseChange_eq_setOf_fixed :
    Set.range (baseChange K L)
      = {a : AdeleRing (𝓞 L) L | ∀ σ : L ≃ₐ[K] L, adeleMap (σ : L ≃+* L) a = a} := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩ σ
    exact adeleMap_baseChange σ x
  · intro ha
    exact mem_range_baseChange_of_fixed ha

/-- **`(𝕀_L)^{Gal(L/K)} = 𝕀_K`.** -/
theorem _root_.NumberField.IdeleGroup.range_baseChange_eq_setOf_fixed :
    Set.range (IdeleGroup.baseChange K L)
      = {u : IdeleGroup (𝓞 L) L | ∀ σ : L ≃ₐ[K] L,
          adeleRingAut (σ : L ≃+* L) (u : AdeleRing (𝓞 L) L) = (u : AdeleRing (𝓞 L) L)} := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩ σ
    rw [IdeleGroup.coe_baseChange]
    exact adeleMap_baseChange σ x
  · intro hu
    obtain ⟨b, hb⟩ := mem_range_baseChange_of_fixed (a := (u : AdeleRing (𝓞 L) L)) hu
    have hu' : ∀ σ : L ≃ₐ[K] L,
        adeleMap (σ : L ≃+* L) ((u⁻¹ : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L)
          = ((u⁻¹ : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L) := by
      intro σ
      have h1 : (adeleRingAut (σ : L ≃+* L)) ((u⁻¹ : IdeleGroup (𝓞 L) L) :
          AdeleRing (𝓞 L) L) * (u : AdeleRing (𝓞 L) L) = 1 := by
        rw [← hu σ, ← map_mul]
        rw [show ((u⁻¹ : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L)
            * (u : AdeleRing (𝓞 L) L) = 1 from by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
        exact map_one _
      have h2 := congrArg (fun z ↦ z * ((u⁻¹ : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L)) h1
      simpa [mul_assoc, ← Units.val_mul] using h2
    obtain ⟨b', hb'⟩ := mem_range_baseChange_of_fixed hu'
    have hbb' : baseChange K L (b * b') = 1 := by
      rw [map_mul, hb, hb', ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hbb'1 : b * b' = 1 :=
      baseChange_injective K L (by rw [hbb', map_one])
    have hb'b : b' * b = 1 := by rw [mul_comm]; exact hbb'1
    refine ⟨⟨b, b', hbb'1, hb'b⟩, ?_⟩
    exact Units.ext hb

end NumberField.AdeleRing
