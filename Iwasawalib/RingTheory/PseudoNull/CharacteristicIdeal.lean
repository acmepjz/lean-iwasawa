/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.RingTheory.CharacteristicIdeal.Basic
public import Iwasawalib.RingTheory.PseudoNull.Basic

@[expose] public section

/-!

# Pseudo-null modules, characteristic ideals, and height one localizations

-/

variable (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
  (N : Type*) [AddCommGroup N] [Module A N] (f : M →ₗ[A] N)

theorem Module.charIdeal_eq_one_of_isPseudoNull [IsPseudoNull A M] :
    charIdeal A M = 1 := by
  simp [Module.charIdeal_eq_prod_of_support_subset A M ∅ (by simp) (fun p hp ↦ False.elim <| by
    have := ENat.coe_le_coe.1 (hp.2 ▸ IsPseudoNull.two_le_primeHeight p hp.1)
    contradiction)]

variable {A M N f}

theorem LinearMap.IsPseudoIsomorphism.charIdeal_eq (H : f.IsPseudoIsomorphism) :
    Module.charIdeal A M = Module.charIdeal A N := by
  simp_rw [Module.charIdeal]
  congr! 4 with p hp
  rw [(LinearEquiv.ofBijective _ (H.bijective_of_primeHeight_le_one hp.le)).length_eq]

theorem Module.IsPseudoIsomorphic.charIdeal_eq (H : M ∼ₚᵢₛ[A] N) :
    Module.charIdeal A M = Module.charIdeal A N := by
  obtain ⟨_, H⟩ := H
  exact H.charIdeal_eq
