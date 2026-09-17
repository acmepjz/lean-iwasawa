/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section

namespace MvZpExtension

/-- I3: a closed subgroup topologically isomorphic to a group with dense cyclic generator
is the closure of the corresponding cyclic subgroup.  The continuous equivalence bundles the
injectivity, surjectivity, and inverse-continuity required by the blueprint. -/
theorem Subgroup.eq_topologicalClosure_zpowers_of_map_dense
    {G Q : Type*} [Group G] [Group Q]
    [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace Q] [IsTopologicalGroup Q]
    (I : Subgroup G) (hI : IsClosed (I : Set G))
    (equiv : I ≃ₜ* Q) (sigma : I)
    (hdense : Dense (Subgroup.zpowers (equiv sigma) : Set Q)) :
    I = (Subgroup.zpowers (sigma : G)).topologicalClosure := by
  apply le_antisymm
  · intro x hx
    let xI : I := ⟨x, hx⟩
    have hdenseI : Dense (Subgroup.zpowers sigma : Set I) := by
      have himage : equiv.symm '' (Subgroup.zpowers (equiv sigma) : Set Q) =
          (Subgroup.zpowers sigma : Set I) := by
        ext y
        simp only [Set.mem_image, SetLike.mem_coe, Subgroup.mem_zpowers_iff]
        constructor
        · rintro ⟨z, ⟨n, rfl⟩, rfl⟩
          exact ⟨n, by simp⟩
        · rintro ⟨n, rfl⟩
          exact ⟨(equiv sigma) ^ n, ⟨n, rfl⟩, by simp⟩
      rw [← himage]
      exact equiv.symm.surjective.denseRange.dense_image equiv.symm.continuous hdense
    have hxI : xI ∈ closure (Subgroup.zpowers sigma : Set I) := hdenseI xI
    refine map_mem_closure continuous_subtype_val hxI ?_
    rintro y ⟨n, rfl⟩
    exact ⟨n, rfl⟩
  · apply Subgroup.topologicalClosure_minimal
    · rintro x ⟨n, rfl⟩
      exact I.zpow_mem sigma.property n
    · exact hI

end MvZpExtension
