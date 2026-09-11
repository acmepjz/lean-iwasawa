/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.SemilocalIntegerUnits

@[expose] public section

/-!
# Finiteness of the Tate cohomology of the semilocal unit groups

The computation of `h(𝕀_{L,S})` in `Iwasawalib/NumberTheory/CFT/SIdeleHerbrand.lean` carries,
besides the vanishing hypotheses at the places outside `S` (supplied by
`Iwasawalib/NumberTheory/CFT/SemilocalIntegerUnits.lean`), a **finiteness** hypothesis on the
Tate cohomology of each semilocal factor `(∏_{w ∣ v} L_w)^×` with `v ∈ S`, and of each
archimedean factor.  This file discharges both at the unramified places.

* At a finite place `v` unramified in `L`, the valuation sequence `0 → O_w^× → L_w^× → ℤ → 0`
  gives the finiteness of `Ĥ⁰(D_w, L_w^×)` and `Ĥ¹(D_w, L_w^×)` from the *vanishing* of the
  Tate cohomology of `O_w^×` (`Iwasawalib/NumberTheory/LocalCFT/Unramified.lean`) and the
  finiteness for the permutation lattice `ℤ` (`Iwasawalib/NumberTheory/CFT/PermutationLattice.lean`).
  Shapiro's lemma then carries it to the semilocal group.
* At an archimedean place `v` whose decomposition group is trivial — which is the case when
  `L / K` is unramified at the infinite places — the semilocal Tate cohomology **vanishes**,
  by the same Shapiro argument applied to `CyclicTate.subsingleton_tateH0_of_subsingleton_group`.

## Main definitions

* `NumberField.localFieldFamily` : the family `w ↦ L_w` over `{w ∣ v}` as an
  `EquivariantFamily`; the `Gal(L/K)`-action it induces on `∏_{w ∣ v} L_w` is the existing
  `NumberField.localProductMulSemiringAction`.

## Main statements

* `NumberField.finite_tateH0_adicCompletion_units`,
  `NumberField.finite_tateH1_adicCompletion_units` : the local finiteness at an unramified
  place.
* `NumberField.finite_tateH0_localProductUnits`,
  `NumberField.finite_tateH1_localProductUnits` : the semilocal finiteness.
* `NumberField.InfiniteAdeleRing.subsingleton_tateH0_infiniteLocalProductUnits`,
  `NumberField.InfiniteAdeleRing.subsingleton_tateH1_infiniteLocalProductUnits` : the
  archimedean vanishing when the decomposition group is trivial.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MulAction CyclicTate WithZero
open scoped WithZero

namespace NumberField

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]

attribute [local instance] Units.mulDistribMulActionRight
  decompositionIntegersMulSemiringAction

/-! ## Local finiteness at an unramified finite place -/

section Local

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal] [IsGalois K L] [Fintype (decompositionGroup K L w)]
  {σ : decompositionGroup K L w}

/-- **`Ĥ⁰(D_w, L_w^×)` is finite at an unramified place.**  The valuation sequence
`0 → O_w^× → L_w^× → ℤ → 0` has vanishing `Ĥ⁰` on the left and finite `Ĥ⁰` on the right. -/
theorem finite_tateH0_adicCompletion_units (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) :
    Finite (TateH0 (decompositionGroup K L w) (Additive (w.adicCompletion L)ˣ) σ) := by
  haveI := subsingleton_tateH0_units v w h hσ
  haveI : Finite (TateH0 (decompositionGroup K L w)
    (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ) := Finite.of_subsingleton
  have hgen : ∀ d : decompositionGroup K L w, ∃ k : ℕ, σ ^ k = d := fun d ↦ by
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff d σ).1 (mem_powers_iff_mem_zpowers.2 (hσ d))
    exact ⟨k, hk⟩
  haveI := PermLattice.finite_tateH0_of_finite
    (G := decompositionGroup K L w) (Ω := Unit) (σ := σ) hgen
  have hπ : ∃ π : w.adicCompletion L, (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ) :=
    valuedAdicCompletion_surjective (K := L) w (exp (-1 : ℤ))
  exact (LocalCFT.isShortExact_valHom (F := w.adicCompletion L)
    (G := decompositionGroup K L w) (valued_decomposition_smul w)
    (fun _ _ ↦ rfl) hπ).finite_tateH0_mid σ

/-- **`Ĥ¹(D_w, L_w^×)` is finite at an unramified place.** -/
theorem finite_tateH1_adicCompletion_units (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) :
    Finite (TateH1 (decompositionGroup K L w) (Additive (w.adicCompletion L)ˣ) σ) := by
  haveI := subsingleton_tateH1_units v w h hσ
  haveI : Finite (TateH1 (decompositionGroup K L w)
    (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ) := Finite.of_subsingleton
  have hgen : ∀ d : decompositionGroup K L w, ∃ k : ℕ, σ ^ k = d := fun d ↦ by
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff d σ).1 (mem_powers_iff_mem_zpowers.2 (hσ d))
    exact ⟨k, hk⟩
  haveI := PermLattice.finite_tateH1_of_finite
    (G := decompositionGroup K L w) (Ω := Unit) (σ := σ) hgen
  have hπ : ∃ π : w.adicCompletion L, (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ) :=
    valuedAdicCompletion_surjective (K := L) w (exp (-1 : ℤ))
  exact (LocalCFT.isShortExact_valHom (F := w.adicCompletion L)
    (G := decompositionGroup K L w) (valued_decomposition_smul w)
    (fun _ _ ↦ rfl) hπ).finite_tateH1_mid σ

end Local

/-! ## The family of local fields over the fibre -/

variable (K L)

/-- **The family `w ↦ L_w` over the places above `v`, as an `EquivariantFamily`.**  The action
it induces on `∏_{w ∣ v} L_w` is the existing `NumberField.localProductMulSemiringAction`
(`NumberField.localFieldFamily_isPiAction`). -/
def localFieldFamily (v : HeightOneSpectrum (𝓞 K)) :
    EquivariantFamily (L ≃ₐ[K] L) ↥(placesOver K L v)
      (fun w ↦ (w : HeightOneSpectrum (𝓞 L)).adicCompletion L) where
  push σ h := pushAdicCompletion σ (congrArg Subtype.val h)
  push_one _ _ := adicCompletionCongr_id _ _ _ (fun _ ↦ rfl) _
  push_mul _ _ h h' h'' _ :=
    adicCompletionCongr_comp _ _ _ _ _ (valuation_of_push_smul (congrArg Subtype.val h))
      (valuation_of_push_smul (congrArg Subtype.val h'))
      (valuation_of_push_smul (congrArg Subtype.val h'')) _

/-- The action of the stabiliser of `w₀` on `L_{w₀}` coming from the family. -/
@[instance_reducible] def localFieldStabilizerAction {v : HeightOneSpectrum (𝓞 K)}
    (w₀ : placesOver K L v) :
    MulSemiringAction (stabilizer (L ≃ₐ[K] L) w₀)
      ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L) :=
  (localFieldFamily K L v).stabilizerMulSemiringAction w₀

/-- The action of the stabiliser of `w₀` on `O_{w₀}`, in the `LocalCFT.integers` spelling that
`LocalCFT.isShortExact_valHom` expects. -/
@[instance_reducible] def localCFTIntegersStabilizerAction {v : HeightOneSpectrum (𝓞 K)}
    (w₀ : placesOver K L v) :
    MulSemiringAction (stabilizer (L ≃ₐ[K] L) w₀)
      (LocalCFT.integers (F := (w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L)) :=
  localIntegerStabilizerAction K L w₀

attribute [local instance] localFieldStabilizerAction localCFTIntegersStabilizerAction

variable {K L}

theorem localFieldFamily_isPiAction (v : HeightOneSpectrum (𝓞 K)) :
    (localFieldFamily K L v).IsPiAction := fun _ _ _ ↦ rfl

theorem localFieldFamily_isStabilizerAction {v : HeightOneSpectrum (𝓞 K)}
    (w₀ : placesOver K L v) :
    (localFieldFamily K L v).IsStabilizerAction (w₀ := w₀) := fun _ _ ↦ rfl

/-! ## Semilocal finiteness at an unramified finite place -/

variable [IsGalois K L] {v : HeightOneSpectrum (𝓞 K)} (w₀ : placesOver K L v)
  [Fintype (stabilizer (L ≃ₐ[K] L) w₀)]
  [Fintype (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))]

/-- **`Ĥ⁰(Gal(L/K), (∏_{w ∣ v} L_w)^×)` is finite at an unramified place.** -/
theorem finite_tateH0_localProductUnits
    (hram : v.asIdeal.ramificationIdx' (w₀ : HeightOneSpectrum (𝓞 L)).asIdeal = 1)
    {σ : L ≃ₐ[K] L} (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    {τ : decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L))}
    (hτ : ∀ d : decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)),
      d ∈ Subgroup.zpowers τ) :
    Finite (TateH0 (L ≃ₐ[K] L) (Additive (LocalProduct K L v)ˣ) σ) := by
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  haveI : (w₀ : HeightOneSpectrum (𝓞 L)).asIdeal.LiesOver v.asIdeal := ⟨w₀.2.symm⟩
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  set e := MulEquiv.subgroupCongr (stabilizer_placesOver_eq w₀).symm with he_def
  have hτ' : ∀ d : stabilizer (L ≃ₐ[K] L) w₀, d ∈ Subgroup.zpowers (e τ) := fun d ↦ by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hτ (e.symm d))
    refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
    rw [← map_zpow e τ m, hm, e.apply_symm_apply]
  have hgen' : ∀ d : stabilizer (L ≃ₐ[K] L) w₀, ∃ k : ℕ, (e τ) ^ k = d := fun d ↦ by
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff d (e τ)).1
      (mem_powers_iff_mem_zpowers.2 (hτ' d))
    exact ⟨k, hk⟩
  haveI hloc : Subsingleton (TateH0 (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))
      (Additive (LocalCFT.integers
        (F := (w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L))ˣ) τ) :=
    subsingleton_tateH0_units v (w₀ : HeightOneSpectrum (𝓞 L)) hram hτ
  haveI : Subsingleton (TateH0 (stabilizer (L ≃ₐ[K] L) w₀)
      (Additive (LocalCFT.integers
        (F := (w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L))ˣ) (e τ)) :=
    subsingleton_tateH0_of_groupEquiv e (fun _ _ ↦ rfl)
  haveI : Finite (TateH0 (stabilizer (L ≃ₐ[K] L) w₀)
      (Additive (LocalCFT.integers
        (F := (w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L))ˣ) (e τ)) :=
    Finite.of_subsingleton
  haveI := PermLattice.finite_tateH0_of_finite (G := stabilizer (L ≃ₐ[K] L) w₀)
    (Ω := Unit) (σ := e τ) hgen'
  have hπ : ∃ π : (w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L,
      (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ) :=
    valuedAdicCompletion_surjective (K := L) _ (exp (-1 : ℤ))
  have hvalG : ∀ (g : stabilizer (L ≃ₐ[K] L) w₀)
      (x : (w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L),
      (Valued.v (g • x) : ℤᵐ⁰) = Valued.v x := fun g x ↦
    valued_pushAdicCompletion (g : L ≃ₐ[K] L)
      (congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 g.2)) x
  haveI : Finite (TateH0 (stabilizer (L ≃ₐ[K] L) w₀)
      (Additive ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L)ˣ) (e τ)) :=
    (LocalCFT.isShortExact_valHom
      (F := (w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L)
      (G := stabilizer (L ≃ₐ[K] L) w₀)
      hvalG (fun _ _ ↦ rfl) hπ).finite_tateH0_mid (e τ)
  exact (localFieldFamily K L v).finite_tateH0_piUnits
    (localFieldFamily_isStabilizerAction w₀) (localFieldFamily_isPiAction v) hσ hτ'

/-- **`Ĥ¹(Gal(L/K), (∏_{w ∣ v} L_w)^×)` is finite at an unramified place.** -/
theorem finite_tateH1_localProductUnits
    (hram : v.asIdeal.ramificationIdx' (w₀ : HeightOneSpectrum (𝓞 L)).asIdeal = 1)
    {σ : L ≃ₐ[K] L} (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    {τ : decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L))}
    (hτ : ∀ d : decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)),
      d ∈ Subgroup.zpowers τ) :
    Finite (TateH1 (L ≃ₐ[K] L) (Additive (LocalProduct K L v)ˣ) σ) := by
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  haveI : (w₀ : HeightOneSpectrum (𝓞 L)).asIdeal.LiesOver v.asIdeal := ⟨w₀.2.symm⟩
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  set e := MulEquiv.subgroupCongr (stabilizer_placesOver_eq w₀).symm with he_def
  have hτ' : ∀ d : stabilizer (L ≃ₐ[K] L) w₀, d ∈ Subgroup.zpowers (e τ) := fun d ↦ by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hτ (e.symm d))
    refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
    rw [← map_zpow e τ m, hm, e.apply_symm_apply]
  have hgen' : ∀ d : stabilizer (L ≃ₐ[K] L) w₀, ∃ k : ℕ, (e τ) ^ k = d := fun d ↦ by
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff d (e τ)).1
      (mem_powers_iff_mem_zpowers.2 (hτ' d))
    exact ⟨k, hk⟩
  haveI hloc : Subsingleton (TateH1 (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))
      (Additive (LocalCFT.integers
        (F := (w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L))ˣ) τ) :=
    subsingleton_tateH1_units v (w₀ : HeightOneSpectrum (𝓞 L)) hram hτ
  haveI : Subsingleton (TateH1 (stabilizer (L ≃ₐ[K] L) w₀)
      (Additive (LocalCFT.integers
        (F := (w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L))ˣ) (e τ)) :=
    subsingleton_tateH1_of_groupEquiv e (fun _ _ ↦ rfl)
  haveI : Finite (TateH1 (stabilizer (L ≃ₐ[K] L) w₀)
      (Additive (LocalCFT.integers
        (F := (w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L))ˣ) (e τ)) :=
    Finite.of_subsingleton
  haveI := PermLattice.finite_tateH1_of_finite (G := stabilizer (L ≃ₐ[K] L) w₀)
    (Ω := Unit) (σ := e τ) hgen'
  have hπ : ∃ π : (w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L,
      (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ) :=
    valuedAdicCompletion_surjective (K := L) _ (exp (-1 : ℤ))
  have hvalG : ∀ (g : stabilizer (L ≃ₐ[K] L) w₀)
      (x : (w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L),
      (Valued.v (g • x) : ℤᵐ⁰) = Valued.v x := fun g x ↦
    valued_pushAdicCompletion (g : L ≃ₐ[K] L)
      (congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 g.2)) x
  haveI : Finite (TateH1 (stabilizer (L ≃ₐ[K] L) w₀)
      (Additive ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L)ˣ) (e τ)) :=
    (LocalCFT.isShortExact_valHom
      (F := (w₀ : HeightOneSpectrum (𝓞 L)).adicCompletion L)
      (G := stabilizer (L ≃ₐ[K] L) w₀)
      hvalG (fun _ _ ↦ rfl) hπ).finite_tateH1_mid (e τ)
  exact (localFieldFamily K L v).finite_tateH1_piUnits
    (localFieldFamily_isStabilizerAction w₀) (localFieldFamily_isPiAction v) hσ hτ'

/-! ## The archimedean places with trivial decomposition group -/

namespace InfiniteAdeleRing

open NumberField.InfiniteAdeleRing

variable {v' : InfinitePlace K}

/-- **`Ĥ⁰(Gal(L/K), (∏_{w ∣ v} L_w)^×) = 0` at an archimedean place with trivial decomposition
group.**  Shapiro's lemma reduces it to the Tate cohomology of the trivial group. -/
theorem subsingleton_tateH0_infiniteLocalProductUnits (w₁ : Fibre L v')
    [Subsingleton (stabilizer (L ≃ₐ[K] L) w₁)]
    {σ : L ≃ₐ[K] L} (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g) :
    Subsingleton (TateH0 (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v')ˣ) σ) := by
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  haveI : Unique (stabilizer (L ≃ₐ[K] L) w₁) := uniqueOfSubsingleton 1
  haveI : Fintype (stabilizer (L ≃ₐ[K] L) w₁) := Unique.fintype
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  haveI : Subsingleton (TateH0 (stabilizer (L ≃ₐ[K] L) w₁)
      (Additive ((w₁ : InfinitePlace L).Completion)ˣ) 1) :=
    subsingleton_tateH0_of_subsingleton_group
  have hτ : ∀ d : stabilizer (L ≃ₐ[K] L) w₁,
      d ∈ Subgroup.zpowers (1 : stabilizer (L ≃ₐ[K] L) w₁) := fun d ↦ by
    rw [Subsingleton.elim d 1]
    exact Subgroup.one_mem _
  exact (infiniteFamily L v').subsingleton_tateH0_piUnits
    (infiniteFamily_isStabilizerAction w₁) infiniteFamily_isPiAction hσ hτ

/-- **`Ĥ¹(Gal(L/K), (∏_{w ∣ v} L_w)^×) = 0` at an archimedean place with trivial decomposition
group.** -/
theorem subsingleton_tateH1_infiniteLocalProductUnits (w₁ : Fibre L v')
    [Subsingleton (stabilizer (L ≃ₐ[K] L) w₁)]
    {σ : L ≃ₐ[K] L} (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g) :
    Subsingleton (TateH1 (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v')ˣ) σ) := by
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  haveI : Unique (stabilizer (L ≃ₐ[K] L) w₁) := uniqueOfSubsingleton 1
  haveI : Fintype (stabilizer (L ≃ₐ[K] L) w₁) := Unique.fintype
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  haveI : Subsingleton (TateH1 (stabilizer (L ≃ₐ[K] L) w₁)
      (Additive ((w₁ : InfinitePlace L).Completion)ˣ) 1) :=
    subsingleton_tateH1_of_subsingleton_group
  have hτ : ∀ d : stabilizer (L ≃ₐ[K] L) w₁,
      d ∈ Subgroup.zpowers (1 : stabilizer (L ≃ₐ[K] L) w₁) := fun d ↦ by
    rw [Subsingleton.elim d 1]
    exact Subgroup.one_mem _
  exact (infiniteFamily L v').subsingleton_tateH1_piUnits
    (infiniteFamily_isStabilizerAction w₁) infiniteFamily_isPiAction hσ hτ

end InfiniteAdeleRing

end NumberField
