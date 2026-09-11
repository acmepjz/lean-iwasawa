/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.Herbrand
public import Iwasawalib.NumberTheory.CFT.FiniteAdeleCongr
public import Iwasawalib.NumberTheory.CFT.FinitePlaceFibre

@[expose] public section

/-!
# Transporting Tate cohomology along an isomorphism of the acting group

`Iwasawalib/NumberTheory/CFT/HerbrandProduct.lean` transports `Ĥ⁰`, `Ĥ¹` and the Herbrand
quotient along an equivariant isomorphism of *modules*, for a fixed acting group.  This file
supplies the missing transport along an isomorphism of the acting *group*, for a fixed module:
if `e : G₁ ≃* G₂` and the two actions of `G₁` and `G₂` on `M` agree through `e`, then the norm
maps, the difference maps, and hence the Tate groups and the Herbrand quotient, agree.

The intended use is a subgroup that has been written in two different ways.  In the adelic
computation the decomposition group at a finite place appears both as
`NumberField.decompositionGroup K L w` — the stabiliser of `w : HeightOneSpectrum (𝓞 L)` — and
as `MulAction.stabilizer (L ≃ₐ[K] L) w` for `w : NumberField.FinitePlaceFibre L v`, a place
packaged together with the place of `K` below it.  The two are the same subgroup, but not the
same term, and nothing transported cohomology across the difference.
`NumberField.stabilizer_finitePlaceFibre_eq_decompositionGroup` identifies them.

## Main statements

* `CyclicTate.normHom_eq_of_group_mulEquiv`, `CyclicTate.subHom_eq_of_group_mulEquiv`.
* `CyclicTate.herbrand_eq_of_group_mulEquiv`: `h(G₁, M, σ) = h(G₂, M, e σ)`.
* `CyclicTate.subsingleton_tateH0_of_group_mulEquiv`,
  `CyclicTate.subsingleton_tateH1_of_group_mulEquiv`.
* `NumberField.FinitePlaceFibre.coe_smul'`: the coercion `FinitePlaceFibre L v →
  HeightOneSpectrum (𝓞 L)` is `Gal(L/K)`-equivariant.
* `NumberField.stabilizer_finitePlaceFibre_eq_decompositionGroup`,
  `NumberField.card_stabilizer_eq_card_decompositionGroup`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace CyclicTate

section GroupTransport

variable {G₁ G₂ M : Type*} [Group G₁] [Group G₂] [Fintype G₁] [Fintype G₂]
  [AddCommGroup M] [DistribMulAction G₁ M] [DistribMulAction G₂ M]
  (e : G₁ ≃* G₂) (he : ∀ (g : G₁) (m : M), e g • m = g • m)

include he

/-- The norm map only depends on the group up to an action-preserving isomorphism. -/
theorem normHom_eq_of_group_mulEquiv : normHom G₁ M = normHom G₂ M := by
  ext m
  rw [normHom_apply, normHom_apply]
  exact Fintype.sum_equiv e.toEquiv _ _ fun g ↦ (he g m).symm

theorem rangeNorm_eq_of_group_mulEquiv : rangeNorm G₁ M = rangeNorm G₂ M := by
  rw [rangeNorm, rangeNorm, normHom_eq_of_group_mulEquiv e he]

theorem kerNorm_eq_of_group_mulEquiv : kerNorm G₁ M = kerNorm G₂ M := by
  rw [kerNorm, kerNorm, normHom_eq_of_group_mulEquiv e he]

omit [Fintype G₁] [Fintype G₂] in
/-- The difference map only depends on the group element through its action. -/
theorem subHom_eq_of_group_mulEquiv (σ : G₁) :
    subHom (M := M) σ = subHom (M := M) (e σ) := by
  ext m
  show σ • m - m = e σ • m - m
  rw [he σ m]

theorem kerSub_eq_of_group_mulEquiv (σ : G₁) :
    kerSub G₁ M σ = kerSub G₂ M (e σ) := by
  rw [kerSub, kerSub, subHom_eq_of_group_mulEquiv e he σ]

theorem rangeSub_eq_of_group_mulEquiv (σ : G₁) :
    rangeSub G₁ M σ = rangeSub G₂ M (e σ) := by
  rw [rangeSub, rangeSub, subHom_eq_of_group_mulEquiv e he σ]

/-- **`Ĥ⁰` vanishes for `G₁` exactly when it vanishes for `G₂`.** -/
theorem subsingleton_tateH0_of_group_mulEquiv (σ : G₁)
    [Subsingleton (TateH0 G₁ M σ)] : Subsingleton (TateH0 G₂ M (e σ)) := by
  rw [tateH0_subsingleton_iff]
  intro x hx
  obtain ⟨y, hy⟩ := (tateH0_subsingleton_iff (M := M) σ).1 ‹_› x (by rw [← he σ x]; exact hx)
  exact ⟨y, by rw [← normHom_eq_of_group_mulEquiv e he]; exact hy⟩

/-- **`Ĥ¹` vanishes for `G₁` exactly when it vanishes for `G₂`.** -/
theorem subsingleton_tateH1_of_group_mulEquiv (σ : G₁)
    [Subsingleton (TateH1 G₁ M σ)] : Subsingleton (TateH1 G₂ M (e σ)) := by
  rw [tateH1_subsingleton_iff]
  intro x hx
  obtain ⟨y, hy⟩ := (tateH1_subsingleton_iff (M := M) σ).1 ‹_› x
    (by rw [normHom_eq_of_group_mulEquiv e he]; exact hx)
  exact ⟨y, by rw [he σ y]; exact hy⟩

/-- **The Herbrand quotient only depends on the acting group up to an action-preserving
isomorphism.** -/
theorem herbrand_eq_of_group_mulEquiv (σ : G₁) :
    herbrand G₁ M σ = herbrand G₂ M (e σ) := by
  have h1 := kerSub_eq_of_group_mulEquiv e he σ
  have h2 := rangeNorm_eq_of_group_mulEquiv e he
  have h3 := kerNorm_eq_of_group_mulEquiv e he
  have h4 := rangeSub_eq_of_group_mulEquiv e he σ
  unfold herbrand TateH0 TateH1
  rw [h1, h2, h3, h4]

end GroupTransport

end CyclicTate

/-! ## The decomposition group, twice -/

namespace NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

namespace FinitePlaceFibre

omit [NumberField K] [NumberField L] in
/-- **The coercion `FinitePlaceFibre L v → HeightOneSpectrum (𝓞 L)` is `Gal(L/K)`-equivariant.**
The two actions are defined through `RingOfIntegers.mapRingEquiv` and through
`MulSemiringAction.toRingAut`, which agree by `NumberField.galRestrict_eq_mapRingEquiv`. -/
theorem coe_smul' (σ : L ≃ₐ[K] L) (w : FinitePlaceFibre L v) :
    ((σ • w : FinitePlaceFibre L v) : HeightOneSpectrum (𝓞 L))
      = σ • (w : HeightOneSpectrum (𝓞 L)) := by
  rw [coe_smul, HeightOneSpectrum.smul_def]
  congr 1

end FinitePlaceFibre

omit [NumberField K] [NumberField L] in
/-- **The stabiliser of a place in the fibre is the decomposition group of that place.**  The
first is the subgroup that `Iwasawalib/NumberTheory/CFT/PlaceLattice.lean` uses to index the
finite places; the second is the subgroup that Shapiro's lemma produces. -/
theorem stabilizer_finitePlaceFibre_eq_decompositionGroup (w : FinitePlaceFibre L v) :
    MulAction.stabilizer (L ≃ₐ[K] L) w
      = decompositionGroup K L (w : HeightOneSpectrum (𝓞 L)) := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, mem_decompositionGroup, ← FinitePlaceFibre.coe_smul' σ w]
  exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩

omit [NumberField K] [NumberField L] in
/-- The two presentations of the decomposition group have the same order. -/
theorem card_stabilizer_eq_card_decompositionGroup (w : FinitePlaceFibre L v) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w)
      = Nat.card (decompositionGroup K L (w : HeightOneSpectrum (𝓞 L))) := by
  rw [stabilizer_finitePlaceFibre_eq_decompositionGroup]

end NumberField
