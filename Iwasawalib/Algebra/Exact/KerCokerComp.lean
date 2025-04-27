/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Exact

/-!

# Long exact sequence for the kernel and cokernel of a composition

If `f : M →ₗ[A] N` and `g : N →ₗ[A] P` are `A`-module homomorphisms, then there is a natural
long exact sequence
`0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 0`.

This is the same as in `Mathlib/CategoryTheory/Abelian/DiagramLemmas/KernelCokernelComp.lean`
but we don't import category theory in this file.

-/

universe u v w x

variable {A : Type u} [Ring A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N]
variable {P : Type x} [AddCommGroup P] [Module A P]
variable (f : M →ₗ[A] N) (g : N →ₗ[A] P)

open LinearMap

namespace Module.KerCokerComp

/-- The map `ker f → ker (g ∘ f)` given by inclusion. -/
abbrev f₁ : ker f →ₗ[A] ker (g ∘ₗ f) := Submodule.inclusion (ker_le_ker_comp f g)

/-- The map `ker (g ∘ f) → ker g` induced by `f`. -/
abbrev f₂ : ker (g ∘ₗ f) →ₗ[A] ker g := f.restrict fun _ ↦ id

/-- The map `ker g → coker f` given by `ker g ↪ N ↠ coker f`. -/
abbrev f₃ : ker g →ₗ[A] N ⧸ range f := (range f).mkQ ∘ₗ (ker g).subtype

/-- The map `coker f → coker (g ∘ f)` induced by `g`. -/
abbrev f₄ : N ⧸ range f →ₗ[A] P ⧸ range (g ∘ₗ f) := (range f).mapQ (range (g ∘ₗ f)) g fun _ h ↦ by
  obtain ⟨_, rfl⟩ := h
  simp

/-- The map `coker (g ∘ f) → coker g` given by projection. -/
abbrev f₅ : P ⧸ range (g ∘ₗ f) →ₗ[A] P ⧸ range g := Submodule.factor (range_comp_le_range f g)

theorem injective_f₁ : Function.Injective (f₁ f g) := Submodule.inclusion_injective _

theorem exact_f₁_f₂ : Function.Exact (f₁ f g) (f₂ f g) := by
  rw [LinearMap.exact_iff, LinearMap.ker_restrict]
  apply Submodule.map_injective_of_injective (ker (g ∘ₗ f)).subtype_injective
  simp only [Submodule.map_comap_subtype, ker_le_ker_comp f g, inf_of_le_right,
    Submodule.map_subtype_range_inclusion]

theorem exact_f₂_f₃ : Function.Exact (f₂ f g) (f₃ f g) := by
  rw [LinearMap.exact_iff]
  ext ⟨x, hx⟩
  simp only [mem_ker, coe_comp, Submodule.coe_subtype, Function.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, mem_range, Subtype.exists]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, hx, rfl⟩
  · rintro ⟨y, _, h⟩
    exact ⟨y, congr($h.1)⟩

theorem exact_f₃_f₄ : Function.Exact (f₃ f g) (f₄ f g) := by
  rw [LinearMap.exact_iff]
  apply Submodule.comap_injective_of_surjective (range f).mkQ_surjective
  ext x
  simp only [Submodule.mem_comap, Submodule.mkQ_apply, mem_ker, Submodule.mapQ_apply,
    Submodule.Quotient.mk_eq_zero, mem_range, coe_comp, Function.comp_apply, Submodule.coe_subtype,
    Subtype.exists, exists_prop]
  simp_rw [← Submodule.mkQ_apply, ← sub_eq_zero (b := Submodule.mkQ _ _), ← map_sub,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨x - f y, by simp [hy], -y, by simp⟩
  · rintro ⟨a, ha, y, hy⟩
    exact ⟨-y, by simp [hy, ha]⟩

theorem exact_f₄_f₅ : Function.Exact (f₄ f g) (f₅ f g) := by
  rw [LinearMap.exact_iff]
  apply Submodule.comap_injective_of_surjective (range (g ∘ₗ f)).mkQ_surjective
  ext x
  simp only [Submodule.mem_comap, Submodule.mkQ_apply, mem_ker, Submodule.mapQ_apply,
    id_coe, id_eq, Submodule.Quotient.mk_eq_zero, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(range f).mkQ y, rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := (range f).mkQ_surjective y
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, ← sub_eq_zero, ← Submodule.mkQ_apply,
      ← Submodule.mkQ_apply, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    simp only [mem_range, coe_comp, Function.comp_apply] at hy
    obtain ⟨y, hy⟩ := hy
    exact ⟨z - f y, by simp [hy]⟩

theorem surjective_f₅ : Function.Surjective (f₅ f g) := Submodule.factor_surjective _

end Module.KerCokerComp
