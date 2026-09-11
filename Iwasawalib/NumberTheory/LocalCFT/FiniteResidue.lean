/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.FiniteFieldTate
public import Mathlib.FieldTheory.Fixed

@[expose] public section

/-!
# A finite field with a faithful action is cohomologically trivial

If a finite cyclic group `G = ⟨σ⟩` acts *faithfully* on a finite field `k`, then by Artin's
theorem `k / k^G` is a Galois extension whose Galois group is `G`, so the vanishing theorems of
`Iwasawalib/GroupCohomology/FiniteFieldTate.lean` apply verbatim: both `kˣ` and `k⁺` are
cohomologically trivial.  This is the form in which the residue field enters the computation of
the cohomology of the units of a local field, where `G` is the decomposition group acting on the
residue field through the (injective, at an unramified place) reduction map.

## Main statements

* `LocalCFT.mulNorm_congr`, `LocalCFT.normHom_congr`: transport of the norm along a group
  isomorphism compatible with the actions.
* `LocalCFT.exists_smul_div_units_of_faithful`, `LocalCFT.exists_mulNorm_units_of_faithful`,
  `LocalCFT.exists_smul_sub_of_faithful`, `LocalCFT.exists_normHom_of_faithful`.
-/

noncomputable section

open CyclicCocycle

namespace LocalCFT

/-! ## Transport of the norms along a group isomorphism -/

section Transport

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]

theorem mulNorm_congr {M : Type*} [CommGroup M] [MulDistribMulAction G M]
    [MulDistribMulAction H M] (e : G ≃* H) (he : ∀ (g : G) (x : M), g • x = e g • x) (x : M) :
    mulNorm (G := G) x = mulNorm (G := H) x := by
  rw [mulNorm_def, mulNorm_def]
  exact Fintype.prod_equiv e.toEquiv _ _ fun g ↦ he g x

theorem normHom_congr {A : Type*} [AddCommGroup A] [DistribMulAction G A]
    [DistribMulAction H A] (e : G ≃* H) (he : ∀ (g : G) (x : A), g • x = e g • x) (x : A) :
    CyclicTate.normHom G A x = CyclicTate.normHom H A x := by
  rw [CyclicTate.normHom_apply, CyclicTate.normHom_apply]
  exact Fintype.sum_equiv e.toEquiv _ _ fun g ↦ he g x

end Transport

/-! ## Faithful actions on a finite field -/

section FiniteField

variable {k : Type} [Field k] [Finite k] {G : Type} [Group G] [Fintype G]
  [MulSemiringAction G k] [FaithfulSMul G k] {σ : G}

attribute [local instance] Units.mulDistribMulActionRight

/-- The isomorphism of `G` with the Galois group of `k` over its fixed field. -/
abbrev galEquiv : G ≃* (k ≃ₐ[FixedPoints.subfield G k] k) := FixedPoints.toAlgAutMulEquiv G k

omit [Finite k] in
theorem galEquiv_apply (g : G) (x : k) : galEquiv (k := k) g x = g • x := rfl

omit [Finite k] in
theorem galEquiv_smul (g : G) (x : k) : g • x = galEquiv (k := k) g • x := rfl

omit [Finite k] in
theorem galEquiv_smul_units (g : G) (x : kˣ) : g • x = galEquiv (k := k) g • x :=
  Units.ext rfl

omit [Finite k] in
theorem forall_mem_zpowers_galEquiv (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (τ : k ≃ₐ[FixedPoints.subfield G k] k) : τ ∈ Subgroup.zpowers (galEquiv (k := k) σ) := by
  obtain ⟨g, rfl⟩ := (galEquiv (k := k)).surjective τ
  obtain ⟨n, hn⟩ := hσ g
  exact ⟨n, by rw [← hn, map_zpow]⟩

omit [Finite k] in
/-- **Hilbert 90 for a faithful action on a field.** -/
theorem exists_smul_div_units_of_faithful (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ) {x : kˣ}
    (hx : mulNorm (G := G) x = 1) : ∃ y : kˣ, σ • y / y = x := by
  have hx' : mulNorm (G := k ≃ₐ[FixedPoints.subfield G k] k) x = 1 := by
    rw [← mulNorm_congr (galEquiv (k := k)) (galEquiv_smul_units (k := k)) x]
    exact hx
  obtain ⟨y, hy⟩ := CyclicTate.exists_smul_div_of_mulNorm_eq_one
    (forall_mem_zpowers_galEquiv hσ) hx'
  exact ⟨y, by rw [galEquiv_smul_units (k := k)]; exact hy⟩

/-- **Surjectivity of the norm of a finite field, for a faithful action.** -/
theorem exists_mulNorm_units_of_faithful (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ) {x : kˣ}
    (hx : σ • x = x) : ∃ y : kˣ, mulNorm (G := G) y = x := by
  have hx' : galEquiv (k := k) σ • x = x := by rw [← galEquiv_smul_units (k := k)]; exact hx
  obtain ⟨y, hy⟩ := CyclicTate.exists_mulNorm_eq_of_smul_eq
    (forall_mem_zpowers_galEquiv hσ) hx'
  exact ⟨y, by rw [mulNorm_congr (galEquiv (k := k)) (galEquiv_smul_units (k := k)) y]; exact hy⟩

omit [Finite k] in
/-- **Additive Hilbert 90 for a faithful action.** -/
theorem exists_smul_sub_of_faithful (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ) {x : k}
    (hx : CyclicTate.normHom G k x = 0) : ∃ y : k, σ • y - y = x := by
  have hx' : CyclicTate.normHom (k ≃ₐ[FixedPoints.subfield G k] k) k x = 0 := by
    rw [← normHom_congr (galEquiv (k := k)) (galEquiv_smul (k := k)) x]
    exact hx
  obtain ⟨y, hy⟩ := CyclicTate.exists_smul_sub_eq_of_normHom_eq_zero_galois
    (forall_mem_zpowers_galEquiv hσ) hx'
  exact ⟨y, by rw [galEquiv_smul (k := k)]; exact hy⟩

omit [Finite k] in
/-- **Surjectivity of the trace for a faithful action.** -/
theorem exists_normHom_of_faithful (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ) {x : k}
    (hx : σ • x = x) : ∃ y : k, CyclicTate.normHom G k y = x := by
  have hx' : galEquiv (k := k) σ • x = x := by rw [← galEquiv_smul (k := k)]; exact hx
  obtain ⟨y, hy⟩ := CyclicTate.exists_normHom_eq_of_smul_eq_galois
    (forall_mem_zpowers_galEquiv hσ) hx'
  exact ⟨y, by rw [normHom_congr (galEquiv (k := k)) (galEquiv_smul (k := k)) y]; exact hy⟩

end FiniteField

end LocalCFT
