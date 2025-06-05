/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Support

/-!

# Supplementary results on torsion modules

-/

theorem Module.IsTorsion.not_disjoint_nonZeroDivisors_of_mem_support
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    (H : Module.IsTorsion A M) :
    ∀ p ∈ Module.support A M, ¬Disjoint (p.1 : Set A) (nonZeroDivisors A : Set A) := by
  intro p
  contrapose!
  rw [Module.notMem_support_iff, LocalizedModule.subsingleton_iff,
    ← Set.subset_compl_iff_disjoint_left]
  intro h x
  obtain ⟨t, ht⟩ := @H x
  exact ⟨t.1, h t.2, ht⟩

theorem Module.IsTorsion.one_le_primeHeight_of_mem_support
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    (H : Module.IsTorsion A M) : ∀ p ∈ Module.support A M, 1 ≤ p.1.primeHeight := by
  intro p hp
  replace H := H.not_disjoint_nonZeroDivisors_of_mem_support p hp
  contrapose! H
  rw [ENat.lt_one_iff_eq_zero, Ideal.primeHeight_eq_zero_iff] at H
  exact Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes H

theorem Module.isTorsion_iff_subsingleton_localizedModule_nonZeroDivisors
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] :
    Module.IsTorsion A M ↔ Subsingleton (LocalizedModule (nonZeroDivisors A) M) := by
  simp only [IsTorsion, Subtype.exists, Submonoid.mk_smul, exists_prop,
    LocalizedModule.subsingleton_iff]

alias ⟨Module.IsTorsion.subsingleton_localizedModule_nonZeroDivisors, _⟩ :=
  Module.isTorsion_iff_subsingleton_localizedModule_nonZeroDivisors

theorem Module.IsTorsion.injective
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {M' : Type*} [AddCommGroup M'] [Module A M'] (H : Module.IsTorsion A M')
    {f : M →ₗ[A] M'} (hf : Function.Injective f) : Module.IsTorsion A M := fun x ↦ by
  obtain ⟨a, ha⟩ := @H (f x)
  exact ⟨a, hf (by rwa [map_zero, LinearMap.map_smul_of_tower])⟩

theorem Module.IsTorsion.surjective
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {M' : Type*} [AddCommGroup M'] [Module A M'] (H : Module.IsTorsion A M)
    {f : M →ₗ[A] M'} (hf : Function.Surjective f) : Module.IsTorsion A M' := fun x ↦ by
  obtain ⟨y, rfl⟩ := hf x
  obtain ⟨a, ha⟩ := @H y
  exact ⟨a, by rw [← LinearMap.map_smul_of_tower, ha, map_zero]⟩

theorem LinearEquiv.isTorsion
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {M' : Type*} [AddCommGroup M'] [Module A M']
    (f : M ≃ₗ[A] M') : Module.IsTorsion A M ↔ Module.IsTorsion A M' :=
  ⟨fun H ↦ H.surjective f.surjective, fun H ↦ H.injective f.injective⟩

theorem Function.Exact.subsingleton
    {M N P : Type*} {f : M → N} {g : N → P} [Zero P]
    (H : Function.Exact f g) [Subsingleton M] [Subsingleton P] : Subsingleton N where
  allEq x y := by
    simp_rw [Function.Exact, Subsingleton.elim _ (0 : P), Set.mem_range, true_iff] at H
    obtain ⟨a, ha⟩ := H x
    obtain ⟨b, hb⟩ := H y
    rw [← ha, ← hb, Subsingleton.elim a b]

theorem Module.IsTorsion.exact
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {M' : Type*} [AddCommGroup M'] [Module A M'] {M'' : Type*} [AddCommGroup M''] [Module A M'']
    (h1 : Module.IsTorsion A M) (h2 : Module.IsTorsion A M'')
    (f : M →ₗ[A] M') (g : M' →ₗ[A] M'') (hfg : Function.Exact f g) : Module.IsTorsion A M' := by
  rw [Module.isTorsion_iff_subsingleton_localizedModule_nonZeroDivisors] at h1 h2 ⊢
  exact (LocalizedModule.map_exact (nonZeroDivisors A) f g hfg).subsingleton

theorem Module.IsTorsion.prod
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {M'' : Type*} [AddCommGroup M''] [Module A M'']
    (h1 : Module.IsTorsion A M) (h2 : Module.IsTorsion A M'') : Module.IsTorsion A (M × M'') :=
  h1.exact h2 (.inl A M M'') (.snd A M M'') .inl_snd
