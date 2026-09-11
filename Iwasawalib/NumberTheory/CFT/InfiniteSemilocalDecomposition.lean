/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.SemilocalTateIso
public import Iwasawalib.NumberTheory.CFT.SemilocalFieldUnits
public import Iwasawalib.NumberTheory.LocalCFT.ArchimedeanInvariantMap

@[expose] public section

/-!
# The semilocal decomposition of the Tate cohomology at an archimedean place

The companion of `Iwasawalib/NumberTheory/CFT/SemilocalDecomposition.lean` at the infinite
places:

`Ĥ⁰(Gal(L/K), (∏_{w ∣ v} L_w)^×) ≅ Ĥ⁰(D_{w₀}, L_{w₀}^×)`

for `v` an infinite place of `K`, with **no hypothesis on the ramification**.  Previously
`Iwasawalib/NumberTheory/CFT/SemilocalFieldUnits.lean` handled only the case of a *trivial*
decomposition group, and only as a vanishing statement.

Two identifications are needed and are proved here:

* `NumberField.InfiniteAdeleRing.stabilizer_fibre_eq`, that the stabiliser of `w₀` in the fibre
  `Fibre L v` is the stabiliser of `w₀` as a place of `L` — two *equal* subgroups of `Gal(L/K)`
  carrying different Lean types, exactly as at the finite places;
* `NumberField.InfiniteAdeleRing.infiniteDecomposition_smul_eq_stabilizer_smul`, that the two
  actions on `L_{w₀}` that the repository defines — one from
  `NumberField.InfiniteAdeleRing.infiniteFamily`, one from
  `NumberField.InfinitePlace.stabilizerRingAut` — are the same action.

## Anti-vacuity

`NumberField.InfiniteAdeleRing.card_tateH0_infiniteLocalProductUnits_eq_two_of_isRamified`
computes the left-hand side to be `2` at a real place of `K` that becomes complex in `L`.  Both
sides of the decomposition are therefore pinned to a value that is *not* the trivial group, and
the value agrees with the independent computation in
`Iwasawalib/NumberTheory/LocalCFT/ArchimedeanLocalNormIndex.lean`.  A decomposition that
matched two copies of an opaque object, or that silently produced the zero group, would fail
this check.

## Main statements

* `NumberField.InfiniteAdeleRing.tateH0InfiniteLocalProductUnitsEquiv`,
  `NumberField.InfiniteAdeleRing.tateH1InfiniteLocalProductUnitsEquiv` : the decomposition.
* `NumberField.InfiniteAdeleRing.card_tateH0_infiniteLocalProductUnits` :
  `#Ĥ⁰(Gal(L/K), (∏_{w ∣ v} L_w)^×) = #D_{w₀}`, the semilocal archimedean norm index.
* `NumberField.InfiniteAdeleRing.invInfiniteLocalProductUnits` : the semilocal invariant map
  `Ĥ⁰(Gal(L/K), (∏_{w ∣ v} L_w)^×) ≃+ ZMod #D_{w₀}`.
-/

noncomputable section

open CyclicTate MulAction NumberField.InfinitePlace

namespace NumberField.InfiniteAdeleRing

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.InfinitePlace.stabilizerCompletionMulSemiringAction

variable {v : InfinitePlace K}

omit [NumberField K] [NumberField L] in
/-- **The stabiliser of a place in the fibre is its decomposition group.**  The archimedean
analogue of `NumberField.stabilizer_placesOver_eq`. -/
theorem stabilizer_fibre_eq (w₀ : Fibre L v) :
    stabilizer (L ≃ₐ[K] L) w₀ = stabilizer (L ≃ₐ[K] L) (w₀ : InfinitePlace L) := by
  ext σ
  rw [mem_stabilizer_iff, mem_stabilizer_iff]
  exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩

/-- The identification `D_{w₀} ≃* Stab_{Gal(L/K)}(w₀)` of the decomposition group of `w₀` as a
place of `L` with its stabiliser in the fibre. -/
def stabilizerPlaceEquivFibre (w₀ : Fibre L v) :
    stabilizer (L ≃ₐ[K] L) (w₀ : InfinitePlace L) ≃* stabilizer (L ≃ₐ[K] L) w₀ :=
  MulEquiv.subgroupCongr (stabilizer_fibre_eq w₀).symm

omit [NumberField K] [NumberField L] in
@[simp] theorem coe_stabilizerPlaceEquivFibre (w₀ : Fibre L v)
    (d : stabilizer (L ≃ₐ[K] L) (w₀ : InfinitePlace L)) :
    (stabilizerPlaceEquivFibre w₀ d : L ≃ₐ[K] L) = (d : L ≃ₐ[K] L) := rfl

omit [NumberField K] [NumberField L] in
/-- **The two archimedean local actions agree.**  `NumberField.InfiniteAdeleRing.infiniteFamily`
makes the stabiliser of `w₀` in the fibre act on `L_{w₀}` by `Completion.congr`, and
`NumberField.InfinitePlace.stabilizerRingAut` makes the decomposition group act on `L_{w₀}` by
`Completion.congr` as well; under `stabilizerPlaceEquivFibre` these are the same. -/
theorem infiniteDecomposition_smul_eq_stabilizer_smul (w₀ : Fibre L v)
    (d : stabilizer (L ≃ₐ[K] L) (w₀ : InfinitePlace L)) (z : (w₀ : InfinitePlace L).Completion) :
    (stabilizerPlaceEquivFibre w₀ d) • z = d • z := rfl

omit [NumberField K] [NumberField L] in
/-- A generator of the decomposition group is carried to a generator of the fibre stabiliser. -/
theorem forall_mem_zpowers_stabilizerPlaceEquivFibre (w₀ : Fibre L v)
    {τ : stabilizer (L ≃ₐ[K] L) (w₀ : InfinitePlace L)}
    (hτ : ∀ d : stabilizer (L ≃ₐ[K] L) (w₀ : InfinitePlace L), d ∈ Subgroup.zpowers τ)
    (d : stabilizer (L ≃ₐ[K] L) w₀) :
    d ∈ Subgroup.zpowers (stabilizerPlaceEquivFibre w₀ τ) := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hτ ((stabilizerPlaceEquivFibre w₀).symm d))
  refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
  rw [← map_zpow (stabilizerPlaceEquivFibre w₀) τ m, hm,
    (stabilizerPlaceEquivFibre w₀).apply_symm_apply]

omit [NumberField K] [NumberField L] in
/-- A point of the fibre lies over `v`. -/
theorem fibre_liesOver (w₀ : Fibre L v) : (w₀ : InfinitePlace L).LiesOver v := by
  have h : (w₀ : InfinitePlace L).LiesOver ((w₀ : InfinitePlace L).comap (algebraMap K L)) :=
    ⟨rfl⟩
  rwa [w₀.2] at h

variable [IsGalois K L] (w₀ : Fibre L v)
  [Fintype (L ≃ₐ[K] L)] [Fintype (stabilizer (L ≃ₐ[K] L) w₀)]
  [Fintype (stabilizer (L ≃ₐ[K] L) (w₀ : InfinitePlace L))]

variable {σ : L ≃ₐ[K] L} (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
  {τ : stabilizer (L ≃ₐ[K] L) (w₀ : InfinitePlace L)}
  (hτ : ∀ d : stabilizer (L ≃ₐ[K] L) (w₀ : InfinitePlace L), d ∈ Subgroup.zpowers τ)

include hgen hτ

/-- **The semilocal decomposition of `Ĥ⁰` at an infinite place**:
`Ĥ⁰(Gal(L/K), (∏_{w ∣ v} L_w)^×) ≅ Ĥ⁰(D_{w₀}, L_{w₀}^×)`.  No ramification hypothesis. -/
def tateH0InfiniteLocalProductUnitsEquiv :
    TateH0 (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v)ˣ) σ
      ≃+ TateH0 (stabilizer (L ≃ₐ[K] L) (w₀ : InfinitePlace L))
          (Additive ((w₀ : InfinitePlace L).Completion)ˣ) τ :=
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  ((infiniteFamily L v).tateH0EquivPiUnits (infiniteFamily_isStabilizerAction w₀)
      infiniteFamily_isPiAction hσ
      (forall_mem_zpowers_stabilizerPlaceEquivFibre w₀ hτ)).trans
    (tateH0EquivOfGroupEquiv (stabilizerPlaceEquivFibre w₀) (fun _ _ ↦ rfl) τ).symm

/-- **The semilocal decomposition of `Ĥ¹` at an infinite place.** -/
def tateH1InfiniteLocalProductUnitsEquiv :
    TateH1 (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v)ˣ) σ
      ≃+ TateH1 (stabilizer (L ≃ₐ[K] L) (w₀ : InfinitePlace L))
          (Additive ((w₀ : InfinitePlace L).Completion)ˣ) τ :=
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  ((infiniteFamily L v).tateH1EquivPiUnits (infiniteFamily_isStabilizerAction w₀)
      infiniteFamily_isPiAction hσ
      (forall_mem_zpowers_stabilizerPlaceEquivFibre w₀ hτ)).trans
    (tateH1EquivOfGroupEquiv (stabilizerPlaceEquivFibre w₀) (fun _ _ ↦ rfl) τ).symm

/-- **The semilocal archimedean norm index**:
`#Ĥ⁰(Gal(L/K), (∏_{w ∣ v} L_w)^×) = #D_{w₀} = [L_{w₀} : K_v]`, at every infinite place. -/
theorem card_tateH0_infiniteLocalProductUnits :
    Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v)ˣ) σ)
      = Nat.card (stabilizer (L ≃ₐ[K] L) (w₀ : InfinitePlace L)) := by
  haveI := fibre_liesOver w₀
  rw [Nat.card_congr (tateH0InfiniteLocalProductUnitsEquiv w₀ hgen hτ).toEquiv]
  exact card_tateH0_completion_units v (w₀ : InfinitePlace L) hτ

/-- **Anti-vacuity control.**  At a place of `L` that is ramified over `K` — a complex place
above a real one — the semilocal `Ĥ⁰` has order exactly `2`, not `1`.  The value is forced by
the decomposition together with
`NumberField.InfinitePlace.card_tateH0_completion_units_eq_two_of_isReal_of_isComplex`, which is
proved independently through the identification of `L_w` with `ℂ`. -/
theorem card_tateH0_infiniteLocalProductUnits_eq_two_of_isRamified
    (h : (w₀ : InfinitePlace L).IsRamified K) :
    Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v)ˣ) σ) = 2 := by
  haveI := fibre_liesOver w₀
  rw [card_tateH0_infiniteLocalProductUnits w₀ hgen hτ]
  exact card_stabilizer_eq_two_of_isRamified v (w₀ : InfinitePlace L) h

/-- **Anti-vacuity control, the split case.**  At a place unramified over `K` the decomposition
group is trivial and the semilocal `Ĥ⁰` has order `1`. -/
theorem card_tateH0_infiniteLocalProductUnits_eq_one_of_isUnramified
    (h : (w₀ : InfinitePlace L).IsUnramified K) :
    Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v)ˣ) σ) = 1 := by
  haveI := fibre_liesOver w₀
  rw [card_tateH0_infiniteLocalProductUnits w₀ hgen hτ]
  exact card_stabilizer_eq_one_of_isUnramified v (w₀ : InfinitePlace L) h

/-- **The semilocal invariant map at an infinite place**:
`Ĥ⁰(Gal(L/K), (∏_{w ∣ v} L_w)^×) ≃+ ℤ/#D_{w₀}`.  The composite of the semilocal decomposition
with the archimedean local invariant map `NumberField.InfinitePlace.invCompletionUnits`. -/
def invInfiniteLocalProductUnits :
    TateH0 (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v)ˣ) σ
      ≃+ ZMod (Nat.card (stabilizer (L ≃ₐ[K] L) (w₀ : InfinitePlace L))) :=
  haveI := fibre_liesOver w₀
  (tateH0InfiniteLocalProductUnitsEquiv w₀ hgen hτ).trans
    (invCompletionUnits v (w₀ : InfinitePlace L) hτ)

end NumberField.InfiniteAdeleRing
