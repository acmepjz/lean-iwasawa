/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

/-!
# Open submodules of a compact-ring module are cofinal among open subgroups

Blueprint node `profinite-module-cofinal-submodules`, first half, and Step 1 of blueprint node
`profinite-Gamma-module-is-Lambda-module`.

Let `R` be a compact topological ring and `Z` a topological `R`-module.  For an open subgroup
`U ⊆ Z` the *core*

`V = {z ∈ Z | R • z ⊆ U} = ⋂_{r ∈ R} r⁻¹(U)`

is an `R`-submodule contained in `U`, and it is **open**: the action map `R × Z → Z/U` is
continuous with discrete target, so `R × {0}` has a tube `R × N` inside its zero fibre by the
tube lemma, and a subgroup containing a neighbourhood of `0` is open.

The same argument with a compact group `Γ` acting continuously by additive automorphisms shows
that the `Γ`-stable open subgroups are cofinal among the open subgroups.

Note the warning recorded in the blueprint: an earlier draft deduced the cofinality from
"a profinite group has finitely many open subgroups of a given index", which is **false**
(consider `∏ ℤ/2`).  The tube lemma argument below is the correct one.
-/

open Topology Set

section Module

variable (R : Type*) {Z : Type*} [Ring R] [AddCommGroup Z] [Module R Z]

/-- The largest `R`-submodule of `Z` contained in the subgroup `U`, namely
`{z | ∀ r : R, r • z ∈ U}`. -/
def AddSubgroup.moduleCore (U : AddSubgroup Z) : Submodule R Z where
  carrier := {z | ∀ r : R, r • z ∈ U}
  zero_mem' r := by simp
  add_mem' {a b} ha hb r := by simpa [smul_add] using U.add_mem (ha r) (hb r)
  smul_mem' c z hz r := by simpa [smul_smul] using hz (r * c)

variable {R}

variable [TopologicalSpace R] [TopologicalSpace Z]

omit [TopologicalSpace R] [TopologicalSpace Z] in
theorem AddSubgroup.mem_moduleCore {U : AddSubgroup Z} {z : Z} :
    z ∈ U.moduleCore R ↔ ∀ r : R, r • z ∈ U := Iff.rfl

omit [TopologicalSpace R] [TopologicalSpace Z] in
theorem AddSubgroup.moduleCore_le (U : AddSubgroup Z) :
    (U.moduleCore R : Set Z) ⊆ (U : Set Z) := fun z hz ↦ by
  have := hz 1
  rwa [one_smul] at this

/-- **Blueprint node `profinite-module-cofinal-submodules`** (cofinality half).  If `R` is a
compact topological ring acting continuously on a topological abelian group `Z`, then every
open subgroup of `Z` contains an open `R`-submodule. -/
theorem AddSubgroup.isOpen_moduleCore [CompactSpace R] [IsTopologicalAddGroup Z]
    [ContinuousSMul R Z] (U : AddSubgroup Z) (hU : IsOpen (U : Set Z)) :
    IsOpen ((U.moduleCore R : Submodule R Z) : Set Z) := by
  -- the action map, followed by the (continuous, since `U` is open) quotient `Z → Z ⧸ U`
  have hpre : IsOpen {p : R × Z | p.1 • p.2 ∈ U} :=
    hU.preimage (continuous_smul (M := R) (X := Z))
  have hsub : (univ : Set R) ×ˢ ({0} : Set Z) ⊆ {p : R × Z | p.1 • p.2 ∈ U} := by
    rintro ⟨r, z⟩ ⟨-, hz⟩
    simp only [mem_singleton_iff] at hz
    simp [hz]
  obtain ⟨u, v, -, hvo, hsu, hv0, huv⟩ :=
    generalized_tube_lemma (isCompact_univ (X := R)) isCompact_singleton hpre hsub
  refine AddSubgroup.isOpen_of_mem_nhds (g := (0 : Z)) (U.moduleCore R).toAddSubgroup ?_
  refine Filter.mem_of_superset (hvo.mem_nhds (hv0 rfl)) fun z hz r ↦ ?_
  exact huv (show ((r, z) : R × Z) ∈ u ×ˢ v from ⟨hsu (mem_univ r), hz⟩)

theorem exists_isOpen_submodule_subset [CompactSpace R] [IsTopologicalAddGroup Z]
    [ContinuousSMul R Z] (U : AddSubgroup Z) (hU : IsOpen (U : Set Z)) :
    ∃ V : Submodule R Z, IsOpen (V : Set Z) ∧ (V : Set Z) ⊆ (U : Set Z) :=
  ⟨U.moduleCore R, U.isOpen_moduleCore hU, U.moduleCore_le⟩

end Module

section GroupAction

variable (Γ : Type*) {Z : Type*} [Group Γ] [AddCommGroup Z] [DistribMulAction Γ Z]

/-- The largest `Γ`-stable subgroup of `Z` contained in the subgroup `U`. -/
def AddSubgroup.gammaCore (U : AddSubgroup Z) : AddSubgroup Z where
  carrier := {z | ∀ σ : Γ, σ • z ∈ U}
  zero_mem' σ := by simp
  add_mem' {a b} ha hb σ := by simpa [smul_add] using U.add_mem (ha σ) (hb σ)
  neg_mem' {a} ha σ := by simpa [smul_neg] using U.neg_mem (ha σ)

variable {Γ}

variable [TopologicalSpace Γ] [TopologicalSpace Z]

omit [TopologicalSpace Γ] [TopologicalSpace Z] in
theorem AddSubgroup.mem_gammaCore {U : AddSubgroup Z} {z : Z} :
    z ∈ U.gammaCore Γ ↔ ∀ σ : Γ, σ • z ∈ U := Iff.rfl

omit [TopologicalSpace Γ] [TopologicalSpace Z] in
theorem AddSubgroup.gammaCore_le (U : AddSubgroup Z) :
    (U.gammaCore Γ : Set Z) ⊆ (U : Set Z) := fun z hz ↦ by
  have := hz 1
  rwa [one_smul] at this

omit [TopologicalSpace Γ] [TopologicalSpace Z] in
/-- `U.gammaCore Γ` is stable under the action of `Γ`. -/
theorem AddSubgroup.smul_mem_gammaCore (U : AddSubgroup Z) {z : Z}
    (hz : z ∈ U.gammaCore Γ) (τ : Γ) : τ • z ∈ U.gammaCore Γ := by
  intro σ
  rw [smul_smul]
  exact hz _

/-- **Step 1 of blueprint node `profinite-Gamma-module-is-Lambda-module`.**  If a compact
group `Γ` acts continuously on a topological abelian group `Z`, then the `Γ`-stable open
subgroups are cofinal among the open subgroups. -/
theorem AddSubgroup.isOpen_gammaCore [CompactSpace Γ] [IsTopologicalAddGroup Z]
    [ContinuousSMul Γ Z] (U : AddSubgroup Z) (hU : IsOpen (U : Set Z)) :
    IsOpen (U.gammaCore Γ : Set Z) := by
  have hpre : IsOpen {p : Γ × Z | p.1 • p.2 ∈ U} :=
    hU.preimage (continuous_smul (M := Γ) (X := Z))
  have hsub : (univ : Set Γ) ×ˢ ({0} : Set Z) ⊆ {p : Γ × Z | p.1 • p.2 ∈ U} := by
    rintro ⟨σ, z⟩ ⟨-, hz⟩
    simp only [mem_singleton_iff] at hz
    simp [hz]
  obtain ⟨u, v, -, hvo, hsu, hv0, huv⟩ :=
    generalized_tube_lemma (isCompact_univ (X := Γ)) isCompact_singleton hpre hsub
  refine AddSubgroup.isOpen_of_mem_nhds (g := (0 : Z)) (U.gammaCore Γ) ?_
  refine Filter.mem_of_superset (hvo.mem_nhds (hv0 rfl)) fun z hz σ ↦ ?_
  exact huv (show ((σ, z) : Γ × Z) ∈ u ×ˢ v from ⟨hsu (mem_univ σ), hz⟩)

theorem exists_isOpen_gammaStable_subset [CompactSpace Γ] [IsTopologicalAddGroup Z]
    [ContinuousSMul Γ Z] (U : AddSubgroup Z) (hU : IsOpen (U : Set Z)) :
    ∃ V : AddSubgroup Z, IsOpen (V : Set Z) ∧ (V : Set Z) ⊆ (U : Set Z) ∧
      ∀ z ∈ V, ∀ σ : Γ, σ • z ∈ V :=
  ⟨U.gammaCore Γ, U.isOpen_gammaCore hU, U.gammaCore_le,
    fun _ hz σ ↦ U.smul_mem_gammaCore hz σ⟩

end GroupAction
