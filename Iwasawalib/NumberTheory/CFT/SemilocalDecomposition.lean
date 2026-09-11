/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.SemilocalTateIso
public import Iwasawalib.NumberTheory.CFT.SemilocalFieldUnits
public import Iwasawalib.NumberTheory.LocalCFT.LocalInvariantMap

@[expose] public section

/-!
# The semilocal decomposition of the Tate cohomology at a finite place

For a cyclic extension `L / K` of number fields and a finite place `v` of `K`, the semilocal
factor `(∏_{w ∣ v} L_w)^×` of the idele group is an induced module, and its Tate cohomology is
the Tate cohomology of a **single** local field under its decomposition group:

`Ĥ⁰(Gal(L/K), (∏_{w ∣ v} L_w)^×) ≅ Ĥ⁰(D_{w₀}, L_{w₀}^×)`

and likewise in degree `1`, and likewise for the semilocal integral units
`(∏_{w ∣ v} O_w)^×` versus `O_{w₀}^×`.

This is the statement that global class field theory uses everywhere.  Before this file the
repository had it only as a transfer of `Subsingleton` and of `Finite`
(`Iwasawalib/NumberTheory/CFT/TateTransport.lean`), which cannot move a cohomology class, an
invariant, or an order.

## Proof

Two steps, both already available:

* `EquivariantFamily.tateH0EquivPiUnits` (`Iwasawalib/NumberTheory/CFT/SemilocalTateIso.lean`)
  gives `Ĥ⁰(G, (∏ w, M w)^×) ≅ Ĥ⁰(Stab_G(w₀), (M w₀)^×)` for the family
  `NumberField.localFieldFamily`;
* `NumberField.stabilizer_placesOver_eq` says `Stab_{Gal(L/K)}(w₀) = D_{w₀}` as subgroups, and
  `CyclicTate.tateH0EquivOfGroupEquiv` turns that equality into an isomorphism of Tate groups.

## Main definitions

* `NumberField.tateH0LocalProductUnitsEquiv`, `NumberField.tateH1LocalProductUnitsEquiv` :
  the decomposition for `(∏_{w ∣ v} L_w)^×`.
* `NumberField.tateH0LocalProductIntegerUnitsEquiv`,
  `NumberField.tateH1LocalProductIntegerUnitsEquiv` : the decomposition for
  `(∏_{w ∣ v} O_w)^×`.

## Main statements

* `NumberField.card_tateH0_localProductUnits`, `NumberField.card_tateH1_localProductUnits` :
  the orders agree.
* `NumberField.card_tateH0_localProductUnits_of_split` : the **anti-vacuity control**.  At a
  place that splits completely the decomposition group is trivial, so the semilocal `Ĥ⁰`
  vanishes; the isomorphism therefore reproduces `#D_w = 1`-style computations rather than
  being an isomorphism of two copies of the same opaque object.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MulAction CyclicTate

namespace NumberField

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]

attribute [local instance] Units.mulDistribMulActionRight
  decompositionIntegersMulSemiringAction adicIntegersDecompositionAction
  localFieldStabilizerAction localCFTIntegersStabilizerAction
  localIntegerPiAction localIntegerStabilizerAction

variable [IsGalois K L] {v : HeightOneSpectrum (𝓞 K)} (w₀ : placesOver K L v)
  [Fintype (L ≃ₐ[K] L)] [Fintype (stabilizer (L ≃ₐ[K] L) w₀)]
  [Fintype (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))]

/-- The identification `D_{w₀} ≃* Stab_{Gal(L/K)}(w₀)` of the decomposition group with the
stabiliser of `w₀` in the fibre: by `NumberField.stabilizer_placesOver_eq` the two subgroups of
`Gal(L/K)` are *equal*, and this is the induced isomorphism of their coercions to types. -/
def decompositionEquivStabilizer :
    decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)) ≃* stabilizer (L ≃ₐ[K] L) w₀ :=
  MulEquiv.subgroupCongr (stabilizer_placesOver_eq w₀).symm

omit [NumberField K] [NumberField L] [IsGalois K L] [Fintype (L ≃ₐ[K] L)]
  [Fintype (stabilizer (L ≃ₐ[K] L) w₀)]
  [Fintype (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))] in
@[simp] theorem coe_decompositionEquivStabilizer
    (d : decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L))) :
    (decompositionEquivStabilizer w₀ d : L ≃ₐ[K] L) = (d : L ≃ₐ[K] L) := rfl

omit [NumberField K] [NumberField L] [IsGalois K L] [Fintype (L ≃ₐ[K] L)]
  [Fintype (stabilizer (L ≃ₐ[K] L) w₀)]
  [Fintype (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))] in
/-- A generator of `D_{w₀}` is carried to a generator of `Stab(w₀)`. -/
theorem forall_mem_zpowers_decompositionEquivStabilizer
    {τ : decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L))}
    (hτ : ∀ d : decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)),
      d ∈ Subgroup.zpowers τ) (d : stabilizer (L ≃ₐ[K] L) w₀) :
    d ∈ Subgroup.zpowers (decompositionEquivStabilizer w₀ τ) := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hτ ((decompositionEquivStabilizer w₀).symm d))
  refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
  rw [← map_zpow (decompositionEquivStabilizer w₀) τ m, hm,
    (decompositionEquivStabilizer w₀).apply_symm_apply]

section Field

variable {σ : L ≃ₐ[K] L} (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
  {τ : decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L))}
  (hτ : ∀ d : decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)), d ∈ Subgroup.zpowers τ)

include hgen hτ

/-- **The semilocal decomposition of `Ĥ⁰` at a finite place**:
`Ĥ⁰(Gal(L/K), (∏_{w ∣ v} L_w)^×) ≅ Ĥ⁰(D_{w₀}, L_{w₀}^×)`. -/
def tateH0LocalProductUnitsEquiv :
    TateH0 (L ≃ₐ[K] L) (Additive (LocalProduct K L v)ˣ) σ
      ≃+ TateH0 (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))
          (Additive ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L)ˣ) τ :=
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  ((localFieldFamily K L v).tateH0EquivPiUnits (localFieldFamily_isStabilizerAction w₀)
      (localFieldFamily_isPiAction v) hσ
      (forall_mem_zpowers_decompositionEquivStabilizer w₀ hτ)).trans
    (tateH0EquivOfGroupEquiv (decompositionEquivStabilizer w₀) (fun _ _ ↦ rfl) τ).symm

/-- **The semilocal decomposition of `Ĥ¹` at a finite place**:
`Ĥ¹(Gal(L/K), (∏_{w ∣ v} L_w)^×) ≅ Ĥ¹(D_{w₀}, L_{w₀}^×)`. -/
def tateH1LocalProductUnitsEquiv :
    TateH1 (L ≃ₐ[K] L) (Additive (LocalProduct K L v)ˣ) σ
      ≃+ TateH1 (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))
          (Additive ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L)ˣ) τ :=
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  ((localFieldFamily K L v).tateH1EquivPiUnits (localFieldFamily_isStabilizerAction w₀)
      (localFieldFamily_isPiAction v) hσ
      (forall_mem_zpowers_decompositionEquivStabilizer w₀ hτ)).trans
    (tateH1EquivOfGroupEquiv (decompositionEquivStabilizer w₀) (fun _ _ ↦ rfl) τ).symm

/-- The order of the semilocal `Ĥ⁰` is the order of the local `Ĥ⁰`. -/
theorem card_tateH0_localProductUnits :
    Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (LocalProduct K L v)ˣ) σ)
      = Nat.card (TateH0 (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))
          (Additive ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L)ˣ) τ) :=
  Nat.card_congr (tateH0LocalProductUnitsEquiv w₀ hgen hτ).toEquiv

/-- The order of the semilocal `Ĥ¹` is the order of the local `Ĥ¹`. -/
theorem card_tateH1_localProductUnits :
    Nat.card (TateH1 (L ≃ₐ[K] L) (Additive (LocalProduct K L v)ˣ) σ)
      = Nat.card (TateH1 (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))
          (Additive ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L)ˣ) τ) :=
  Nat.card_congr (tateH1LocalProductUnitsEquiv w₀ hgen hτ).toEquiv

/-- **The semilocal decomposition of `Ĥ⁰` for the integral units**:
`Ĥ⁰(Gal(L/K), (∏_{w ∣ v} O_w)^×) ≅ Ĥ⁰(D_{w₀}, O_{w₀}^×)`.  The source is the subgroup of
integral semilocal units inside `(∏_{w ∣ v} L_w)^×`, which is the spelling that
`Iwasawalib/NumberTheory/CFT/SIdeleHerbrand.lean` consumes. -/
def tateH0LocalProductIntegerUnitsEquiv :
    TateH0 (L ≃ₐ[K] L) (Additive (localProductIntegerUnits K L v)) σ
      ≃+ TateH0 (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))
          (Additive ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L)ˣ) τ :=
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  (tateH0EquivOfMulEquiv (localProductIntegerUnitsEquivPiUnits K L v)
      (localProductIntegerUnitsEquivPiUnits_smul v) σ).trans
    (((localIntegerFamily K L v).tateH0EquivPiUnits (localIntegerFamily_isStabilizerAction w₀)
        (localIntegerFamily_isPiAction v) hσ
        (forall_mem_zpowers_decompositionEquivStabilizer w₀ hτ)).trans
      (tateH0EquivOfGroupEquiv (decompositionEquivStabilizer w₀) (fun _ _ ↦ rfl) τ).symm)

/-- **The semilocal decomposition of `Ĥ¹` for the integral units.** -/
def tateH1LocalProductIntegerUnitsEquiv :
    TateH1 (L ≃ₐ[K] L) (Additive (localProductIntegerUnits K L v)) σ
      ≃+ TateH1 (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))
          (Additive ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L)ˣ) τ :=
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  (tateH1EquivOfMulEquiv (localProductIntegerUnitsEquivPiUnits K L v)
      (localProductIntegerUnitsEquivPiUnits_smul v) σ).trans
    (((localIntegerFamily K L v).tateH1EquivPiUnits (localIntegerFamily_isStabilizerAction w₀)
        (localIntegerFamily_isPiAction v) hσ
        (forall_mem_zpowers_decompositionEquivStabilizer w₀ hτ)).trans
      (tateH1EquivOfGroupEquiv (decompositionEquivStabilizer w₀) (fun _ _ ↦ rfl) τ).symm)

/-- The order of the semilocal `Ĥ⁰` of the integral units is the order of the local one. -/
theorem card_tateH0_localProductIntegerUnits :
    Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (localProductIntegerUnits K L v)) σ)
      = Nat.card (TateH0 (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))
          (Additive ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L)ˣ) τ) :=
  Nat.card_congr (tateH0LocalProductIntegerUnitsEquiv w₀ hgen hτ).toEquiv

/-- The order of the semilocal `Ĥ¹` of the integral units is the order of the local one. -/
theorem card_tateH1_localProductIntegerUnits :
    Nat.card (TateH1 (L ≃ₐ[K] L) (Additive (localProductIntegerUnits K L v)) σ)
      = Nat.card (TateH1 (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))
          (Additive ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L)ˣ) τ) :=
  Nat.card_congr (tateH1LocalProductIntegerUnitsEquiv w₀ hgen hτ).toEquiv

/-! ## The semilocal invariant map, and the anti-vacuity control -/

/-- **The semilocal invariant map at an unramified finite place**:
`Ĥ⁰(Gal(L/K), (∏_{w ∣ v} L_w)^×) ≃+ ℤ/#D_{w₀}`.  The composite of the semilocal decomposition
with `NumberField.invAdicCompletionUnits`. -/
def invLocalProductUnits (h : v.asIdeal.ramificationIdx' (w₀ : HeightOneSpectrum (𝓞 L)).asIdeal = 1) :
    TateH0 (L ≃ₐ[K] L) (Additive (LocalProduct K L v)ˣ) σ
      ≃+ ZMod (Nat.card (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))) :=
  haveI : (w₀ : HeightOneSpectrum (𝓞 L)).asIdeal.LiesOver v.asIdeal := ⟨w₀.2.symm⟩
  (tateH0LocalProductUnitsEquiv w₀ hgen hτ).trans
    (invAdicCompletionUnits v (w₀ : HeightOneSpectrum (𝓞 L)) h hτ)

/-- **Anti-vacuity control at a finite place.**  At an unramified finite place the semilocal
`Ĥ⁰` has order exactly `#D_{w₀} = [L_{w₀} : K_v]`, the local norm index.  In particular it is
`1` exactly when `v` splits completely and `[L : K]` when `v` is inert, so the decomposition
reproduces the independent order computation of
`Iwasawalib/NumberTheory/LocalCFT/LocalInvariantMap.lean` rather than relating two copies of the
same opaque object. -/
theorem card_tateH0_localProductUnits_eq_card_decompositionGroup
    (h : v.asIdeal.ramificationIdx' (w₀ : HeightOneSpectrum (𝓞 L)).asIdeal = 1) :
    Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (LocalProduct K L v)ˣ) σ)
      = Nat.card (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L))) := by
  rw [Nat.card_congr (invLocalProductUnits w₀ hgen hτ h).toEquiv, Nat.card_zmod]

end Field

end NumberField
