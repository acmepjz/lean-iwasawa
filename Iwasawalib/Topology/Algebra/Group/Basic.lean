/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Topology.Algebra.Group.Basic

/-!

# Supplementary results for continuous group homomorphisms

-/

@[to_additive]
theorem MonoidHom.continuous_iff {G H : Type*} [Group G] [Monoid H]
    [TopologicalSpace G] [TopologicalSpace H] [ContinuousMul G] [ContinuousMul H] (f : G →* H) :
    Continuous f ↔ ∀ s : Set H, 1 ∈ s → IsOpen s →
      ∃ t : Set G, 1 ∈ t ∧ IsOpen t ∧ t ⊆ f ⁻¹' s := by
  refine ⟨fun h s h1 hs ↦ ⟨_, by simp [h1], h.1 s hs, by simp⟩, fun h ↦ ⟨fun s hs ↦ ?_⟩⟩
  simp_rw [isOpen_iff_mem_nhds, mem_nhds_iff]
  intro x hx
  obtain ⟨t, h1, ht, ht'⟩ :=
    h _ (by simpa using hx) ((show Continuous (· * f x) by fun_prop).1 s hs)
  refine ⟨_, fun y hy ↦ ?_, (show Continuous (· * x⁻¹) by fun_prop).1 _ ht, by simp [h1]⟩
  rw [Set.mem_preimage] at hy
  specialize ht' hy
  simpa [mul_assoc, ← map_mul f x⁻¹ x] using ht'
