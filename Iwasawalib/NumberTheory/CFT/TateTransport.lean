/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.HerbrandShapiro

@[expose] public section

/-!
# Transporting the vanishing of Tate cohomology

The computation of `h(𝕀_{L,S})` in
`Iwasawalib/NumberTheory/CFT/SIdeleHerbrand.lean` takes the vanishing of `Ĥ⁰` and `Ĥ¹` of the
semilocal unit groups `∏_{w ∣ v} O_w^×` at the places `v ∉ S` as an instance hypothesis, while
what local class field theory supplies (in `Iwasawalib/NumberTheory/LocalCFT/Unramified.lean`)
is the vanishing for the single group `O_{w₀}^×` under the decomposition group `D_{w₀}`.  Three
different moves are needed to get from the second statement to the first, and this file makes
each of them available on its own:

* **changing the acting group** along a multiplicative isomorphism that acts the same way
  (`CyclicTate.subsingleton_tateH0_of_groupEquiv`) — this is what turns a statement about
  `D_{w₀} = decompositionGroup K L w₀` into one about `Stab_G(w₀)`, two *equal* subgroups of
  `Gal(L/K)` carrying different Lean types;
* **changing the module** along an equivariant isomorphism
  (`CyclicTate.subsingleton_tateH0_of_moduleEquiv`);
* **Shapiro's lemma**, `Ĥⁱ(G, (∏_{w : Ω} M w)^×) ≅ Ĥⁱ(Stab_G(w₀), (M w₀)^×)` for a transitive
  equivariant family, in the form of a transfer of vanishing
  (`EquivariantFamily.subsingleton_tateH0_piUnits`).

The Shapiro transfer is stated as a transfer of `Subsingleton` and not of cardinalities on
purpose: the product over `v ∉ S` is infinite, so what
`CyclicTate.subsingleton_tateH0_mulPi` needs from each factor is genuine vanishing, and no
finiteness is available a priori.

A fourth, degenerate case is recorded here as well: the Tate cohomology of a **trivial** group
vanishes (`CyclicTate.subsingleton_tateH0_of_subsingleton_group`).  That is the archimedean
input in the everywhere-unramified case, where every decomposition group at an infinite place
is trivial.

## Main statements

* `CyclicTate.subsingleton_tateH0_of_groupEquiv`, `CyclicTate.subsingleton_tateH1_of_groupEquiv` :
  change of acting group.
* `CyclicTate.subsingleton_tateH0_of_moduleEquiv`,
  `CyclicTate.subsingleton_tateH1_of_moduleEquiv` : change of module.
* `CyclicTate.subsingleton_tateH0_of_subsingleton_group`,
  `CyclicTate.subsingleton_tateH1_of_subsingleton_group` : the trivial group.
* `CyclicTate.herbrand_eq_one_of_subsingleton_group` : `h = 1` for the trivial group.
* `EquivariantFamily.subsingleton_tateH0_piUnits`,
  `EquivariantFamily.subsingleton_tateH1_piUnits` : Shapiro.
-/

noncomputable section

open CategoryTheory MulAction

namespace CyclicTate

/-! ## Changing the acting group -/

section ChangeGroup

variable {G G' M : Type*} [Group G] [Fintype G] [Group G'] [Fintype G'] [AddCommGroup M]
  [DistribMulAction G M] [DistribMulAction G' M]

/-- If two finite groups acting on the same module are identified by a multiplicative
isomorphism under which the two actions agree, their norm endomorphisms agree. -/
theorem normHom_eq_of_groupEquiv (e : G ≃* G') (he : ∀ (g : G) (x : M), e g • x = g • x) (x : M) :
    normHom G' M x = normHom G M x := by
  rw [normHom_apply, normHom_apply]
  refine (Fintype.sum_equiv e.toEquiv _ _ fun g ↦ ?_).symm
  exact (he g x).symm

/-- **`Ĥ⁰` does not depend on the name of the acting group.** -/
theorem subsingleton_tateH0_of_groupEquiv (e : G ≃* G')
    (he : ∀ (g : G) (x : M), e g • x = g • x) {σ : G}
    [h : Subsingleton (TateH0 G M σ)] : Subsingleton (TateH0 G' M (e σ)) := by
  rw [tateH0_subsingleton_iff] at h ⊢
  intro x hx
  obtain ⟨y, hy⟩ := h x ((he σ x).symm.trans hx)
  exact ⟨y, (normHom_eq_of_groupEquiv e he y).trans hy⟩

/-- **`Ĥ¹` does not depend on the name of the acting group.** -/
theorem subsingleton_tateH1_of_groupEquiv (e : G ≃* G')
    (he : ∀ (g : G) (x : M), e g • x = g • x) {σ : G}
    [h : Subsingleton (TateH1 G M σ)] : Subsingleton (TateH1 G' M (e σ)) := by
  rw [tateH1_subsingleton_iff] at h ⊢
  intro x hx
  obtain ⟨y, hy⟩ := h x ((normHom_eq_of_groupEquiv e he x).symm.trans hx)
  exact ⟨y, ((he σ y).symm ▸ hy : (e σ) • y - y = x)⟩

/-- The two norm subgroups coincide. -/
theorem rangeNorm_eq_of_groupEquiv (e : G ≃* G') (he : ∀ (g : G) (x : M), e g • x = g • x) :
    rangeNorm G M = rangeNorm G' M := by
  ext x
  simp only [mem_rangeNorm]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, (normHom_eq_of_groupEquiv e he y).trans hy⟩,
    fun ⟨y, hy⟩ ↦ ⟨y, (normHom_eq_of_groupEquiv e he y).symm.trans hy⟩⟩

/-- The two norm kernels coincide. -/
theorem kerNorm_eq_of_groupEquiv (e : G ≃* G') (he : ∀ (g : G) (x : M), e g • x = g • x) :
    kerNorm G M = kerNorm G' M := by
  ext x
  simp only [mem_kerNorm]
  rw [normHom_eq_of_groupEquiv e he x]

/-- The two invariant subgroups coincide. -/
theorem kerSub_eq_of_groupEquiv (e : G ≃* G') (he : ∀ (g : G) (x : M), e g • x = g • x) (σ : G) :
    kerSub G M σ = kerSub G' M (e σ) := by
  ext x
  simp only [mem_kerSub]
  rw [he σ x]

/-- The two coboundary subgroups coincide. -/
theorem rangeSub_eq_of_groupEquiv (e : G ≃* G') (he : ∀ (g : G) (x : M), e g • x = g • x)
    (σ : G) : rangeSub G M σ = rangeSub G' M (e σ) := by
  ext x
  simp only [mem_rangeSub]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, by rw [he σ y]; exact hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, by rw [← he σ y]; exact hy⟩⟩

end ChangeGroup

/-! ## Changing the module -/

section ChangeModule

variable {G A B : Type*} [Group G] [Fintype G] [CommGroup A] [CommGroup B]
  [MulDistribMulAction G A] [MulDistribMulAction G B]

attribute [local instance] Additive.distribMulActionOfMulDistrib

/-- **`Ĥ⁰` transfers along an equivariant isomorphism of modules.** -/
theorem subsingleton_tateH0_of_moduleEquiv (e : A ≃* B) (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    {σ : G} [h : Subsingleton (TateH0 G (Additive A) σ)] :
    Subsingleton (TateH0 G (Additive B) σ) := by
  have hadd : ∀ (g : G) (a : Additive A),
      Additive.ofMul (e a.toMul) = g⁻¹ • Additive.ofMul (e (g • a).toMul) := by
    intro g a
    show Additive.ofMul (e a.toMul) = Additive.ofMul (g⁻¹ • e ((g • a).toMul))
    refine congrArg Additive.ofMul ?_
    rw [show ((g • a : Additive A)).toMul = g • a.toMul from rfl, he, inv_smul_smul]
  let E : Additive A ≃+ Additive B := MulEquiv.toAdditive e
  have hE : ∀ (g : G) (a : Additive A), E (g • a) = g • E a := fun g a ↦
    congrArg Additive.ofMul (he g a.toMul)
  rw [tateH0_subsingleton_iff] at h ⊢
  intro x hx
  obtain ⟨y, hy⟩ := h (E.symm x) (E.injective (by rw [hE, E.apply_symm_apply, hx]))
  refine ⟨E y, ?_⟩
  rw [normHom_apply]
  calc ∑ g : G, g • E y = ∑ g : G, E (g • y) := Finset.sum_congr rfl fun g _ ↦ (hE g y).symm
    _ = E (∑ g : G, g • y) := (map_sum E _ _).symm
    _ = E (normHom G (Additive A) y) := by rw [normHom_apply]
    _ = x := by rw [hy, E.apply_symm_apply]

/-- **`Ĥ¹` transfers along an equivariant isomorphism of modules.** -/
theorem subsingleton_tateH1_of_moduleEquiv (e : A ≃* B) (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    {σ : G} [h : Subsingleton (TateH1 G (Additive A) σ)] :
    Subsingleton (TateH1 G (Additive B) σ) := by
  let E : Additive A ≃+ Additive B := MulEquiv.toAdditive e
  have hE : ∀ (g : G) (a : Additive A), E (g • a) = g • E a := fun g a ↦
    congrArg Additive.ofMul (he g a.toMul)
  have hN : ∀ a : Additive A, E (normHom G (Additive A) a) = normHom G (Additive B) (E a) := by
    intro a
    rw [normHom_apply, normHom_apply, map_sum]
    exact Finset.sum_congr rfl fun g _ ↦ hE g a
  rw [tateH1_subsingleton_iff] at h ⊢
  intro x hx
  obtain ⟨y, hy⟩ := h (E.symm x) (E.injective (by rw [hN, E.apply_symm_apply, hx, map_zero]))
  exact ⟨E y, by rw [← hE σ y, ← map_sub, hy, E.apply_symm_apply]⟩

end ChangeModule

/-! ## The trivial group -/

section TrivialGroup

variable {G M : Type*} [Group G] [Fintype G] [Subsingleton G] [AddCommGroup M]
  [DistribMulAction G M]

theorem normHom_eq_id_of_subsingleton_group (x : M) : normHom G M x = x := by
  rw [normHom_apply, Finset.sum_eq_single (1 : G) (fun g _ hg ↦ absurd (Subsingleton.elim g 1) hg)
    (fun h ↦ absurd (Finset.mem_univ (1 : G)) h), one_smul]

/-- **`Ĥ⁰` of the trivial group vanishes**: the norm is the identity. -/
theorem subsingleton_tateH0_of_subsingleton_group {σ : G} : Subsingleton (TateH0 G M σ) := by
  rw [tateH0_subsingleton_iff]
  exact fun x _ ↦ ⟨x, normHom_eq_id_of_subsingleton_group x⟩

/-- **`Ĥ¹` of the trivial group vanishes**: the norm is injective. -/
theorem subsingleton_tateH1_of_subsingleton_group {σ : G} : Subsingleton (TateH1 G M σ) := by
  rw [tateH1_subsingleton_iff]
  intro x hx
  refine ⟨0, ?_⟩
  rw [smul_zero, sub_zero, ← normHom_eq_id_of_subsingleton_group (G := G) x, hx]

theorem finite_tateH0_of_subsingleton_group {σ : G} : Finite (TateH0 G M σ) :=
  haveI := subsingleton_tateH0_of_subsingleton_group (G := G) (M := M) (σ := σ)
  Finite.of_subsingleton

theorem finite_tateH1_of_subsingleton_group {σ : G} : Finite (TateH1 G M σ) :=
  haveI := subsingleton_tateH1_of_subsingleton_group (G := G) (M := M) (σ := σ)
  Finite.of_subsingleton

/-- **The Herbrand quotient of the trivial group is `1`.** -/
theorem herbrand_eq_one_of_subsingleton_group {σ : G} : herbrand G M σ = 1 := by
  haveI : Subsingleton (TateH0 G M σ) := subsingleton_tateH0_of_subsingleton_group
  haveI : Subsingleton (TateH1 G M σ) := subsingleton_tateH1_of_subsingleton_group
  haveI : Finite (TateH0 G M σ) := Finite.of_subsingleton
  haveI : Finite (TateH1 G M σ) := Finite.of_subsingleton
  exact herbrand_eq_one_of_subsingleton σ

end TrivialGroup

end CyclicTate

/-! ## Shapiro's lemma as a transfer of vanishing -/

namespace EquivariantFamily

open CyclicTate

attribute [local instance] Units.mulDistribMulActionRight

variable {G Ω : Type} [CommGroup G] [Fintype G] [MulAction G Ω] {M : Ω → Type}
  [∀ w, CommRing (M w)] (F : EquivariantFamily G Ω M) {w₀ : Ω}
  [MulSemiringAction G (∀ w : Ω, M w)] [MulSemiringAction (stabilizer G w₀) (M w₀)]
  [IsPretransitive G Ω] [Fintype (stabilizer G w₀)]

/-- **Shapiro's lemma for `Ĥ⁰` of the units of a transitive equivariant family**, as a transfer
of vanishing: if `Ĥ⁰(Stab_G(w₀), (M w₀)^×) = 0` then `Ĥ⁰(G, (∏ w : Ω, M w)^×) = 0`. -/
theorem subsingleton_tateH0_piUnits (hstab : F.IsStabilizerAction (w₀ := w₀))
    (hpi : F.IsPiAction) {σ : G} (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {τ : stabilizer G w₀} (hτ : ∀ d : stabilizer G w₀, d ∈ Subgroup.zpowers τ)
    [Subsingleton (TateH0 (stabilizer G w₀) (Additive (M w₀)ˣ) τ)] :
    Subsingleton (TateH0 G (Additive (∀ w : Ω, M w)ˣ) σ) := by
  exact Equiv.subsingleton
    ((tateH0EquivGroupCohomology (M := Additive (∀ w : Ω, M w)ˣ) σ hσ 2 (by decide)).toEquiv.trans
      (((F.shapiroUnits hstab hpi 2).toLinearEquiv.toEquiv).trans
        (tateH0EquivGroupCohomology (M := Additive (M w₀)ˣ) τ hτ 2 (by decide)).symm.toEquiv))

/-- **Shapiro's lemma for `Ĥ¹` of the units of a transitive equivariant family**, as a transfer
of vanishing: if `Ĥ¹(Stab_G(w₀), (M w₀)^×) = 0` then `Ĥ¹(G, (∏ w : Ω, M w)^×) = 0`. -/
theorem subsingleton_tateH1_piUnits (hstab : F.IsStabilizerAction (w₀ := w₀))
    (hpi : F.IsPiAction) {σ : G} (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {τ : stabilizer G w₀} (hτ : ∀ d : stabilizer G w₀, d ∈ Subgroup.zpowers τ)
    [Subsingleton (TateH1 (stabilizer G w₀) (Additive (M w₀)ˣ) τ)] :
    Subsingleton (TateH1 G (Additive (∀ w : Ω, M w)ˣ) σ) := by
  exact Equiv.subsingleton
    ((tateH1EquivGroupCohomology (M := Additive (∀ w : Ω, M w)ˣ) σ hσ 1 ⟨0, by ring⟩).toEquiv.trans
      (((F.shapiroUnits hstab hpi 1).toLinearEquiv.toEquiv).trans
        (tateH1EquivGroupCohomology (M := Additive (M w₀)ˣ) τ hτ 1 ⟨0, by ring⟩).symm.toEquiv))

/-- **Shapiro's lemma for `Ĥ⁰` of the units of a transitive equivariant family**, as a transfer
of finiteness. -/
theorem finite_tateH0_piUnits (hstab : F.IsStabilizerAction (w₀ := w₀))
    (hpi : F.IsPiAction) {σ : G} (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {τ : stabilizer G w₀} (hτ : ∀ d : stabilizer G w₀, d ∈ Subgroup.zpowers τ)
    [Finite (TateH0 (stabilizer G w₀) (Additive (M w₀)ˣ) τ)] :
    Finite (TateH0 G (Additive (∀ w : Ω, M w)ˣ) σ) :=
  Finite.of_equiv _
    ((tateH0EquivGroupCohomology (M := Additive (∀ w : Ω, M w)ˣ) σ hσ 2 (by decide)).toEquiv.trans
      (((F.shapiroUnits hstab hpi 2).toLinearEquiv.toEquiv).trans
        (tateH0EquivGroupCohomology (M := Additive (M w₀)ˣ) τ hτ 2 (by decide)).symm.toEquiv)).symm

/-- **Shapiro's lemma for `Ĥ¹` of the units of a transitive equivariant family**, as a transfer
of finiteness. -/
theorem finite_tateH1_piUnits (hstab : F.IsStabilizerAction (w₀ := w₀))
    (hpi : F.IsPiAction) {σ : G} (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {τ : stabilizer G w₀} (hτ : ∀ d : stabilizer G w₀, d ∈ Subgroup.zpowers τ)
    [Finite (TateH1 (stabilizer G w₀) (Additive (M w₀)ˣ) τ)] :
    Finite (TateH1 G (Additive (∀ w : Ω, M w)ˣ) σ) :=
  Finite.of_equiv _
    ((tateH1EquivGroupCohomology (M := Additive (∀ w : Ω, M w)ˣ) σ hσ 1 ⟨0, by ring⟩).toEquiv.trans
      (((F.shapiroUnits hstab hpi 1).toLinearEquiv.toEquiv).trans
        (tateH1EquivGroupCohomology (M := Additive (M w₀)ˣ) τ hτ 1 ⟨0, by ring⟩).symm.toEquiv)).symm

end EquivariantFamily
