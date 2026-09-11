/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.SemilocalFieldUnits
public import Iwasawalib.NumberTheory.CFT.SIdeleHerbrand
public import Iwasawalib.NumberTheory.CFT.IdeleClassHerbrand

@[expose] public section

/-!
# `h(C_L) = [L : K]`

Let `L / K` be a cyclic extension of number fields which is **unramified at every place**.
This file proves

`h(Gal(L/K), C_L) = [L : K]`

(`NumberField.herbrand_ideleClassGroup_eq_card_of_unramified`), with no hypothesis left over.

The two halves of the computation were already in place:

* `NumberField.herbrand_ideleClassGroup_of_herbrand_sIdele` reduces `h(C_L)` to the value of
  `h(𝕀_{L,S})`, using the short exact sequence `1 → O_{L,S}^× → 𝕀_{L,S} → C_L → 1` and the
  `S`-unit computation `h(O_{L,S}^×) = (∏_v n_v) / n`;
* `NumberField.herbrand_sIdele` reduces `h(𝕀_{L,S})` to the semilocal Herbrand quotients.

What was missing, and is supplied here, is the join:

* the **vanishing** at the places `v ∉ S`, from
  `Iwasawalib/NumberTheory/CFT/SemilocalIntegerUnits.lean`;
* the **finiteness** at the places `v ∈ S` and at the archimedean places, from
  `Iwasawalib/NumberTheory/CFT/SemilocalFieldUnits.lean`;
* the **local value** `h(D_w, L_w^×) = #D_w`
  (`NumberField.herbrand_adicCompletion_units_eq_card`), transported to the semilocal factor by
  Shapiro (`NumberField.herbrand_localProductUnits`);
* the **bookkeeping** identification of `Stab_{Gal(L/K)}(w)` for `w` in the fibre
  `NumberField.FinitePlaceFibre L v`, which is how the `S`-unit side names the decomposition
  group, with `NumberField.decompositionGroup K L w`, which is how the idele side names it
  (`NumberField.card_stabilizer_finitePlaceFibre_eq`).

## The ramification hypotheses

`h(D_w, L_w^×) = #D_w` is proved in this repository only at the **unramified** finite places,
and no value at all is available for an archimedean place whose decomposition group is
nontrivial.  Accordingly the hypotheses here are: every finite place of `K` is unramified in
`L`, and every archimedean decomposition group is trivial.  That is exactly the situation of
the Hilbert class field.  The general case needs two further local inputs — `h(O_w^×) = 1` at
a ramified finite place, and `h(Gal(ℂ/ℝ), ℂ^×) = 2` — and nothing else: the global half of the
argument below is insensitive to them.

## Main statements

* `NumberField.finite_tateH0_sIdele`, `NumberField.finite_tateH1_sIdele` : the Tate cohomology
  of `𝕀_{L,S}` is finite.
* `NumberField.finite_tateH0_ideleClassGroup` : the Tate cohomology of `C_L` is finite.
* `NumberField.herbrand_ideleClassGroup_eq_card_of_unramified`,
  `NumberField.herbrand_ideleClassGroup_eq_card_of_unramified_everywhere` :
  **`h(C_L) = [L : K]`.**
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MulAction CyclicTate
open NumberField.InfiniteAdeleRing

namespace NumberField

attribute [local instance] NumberField.galInfiniteAdeleMulSemiringAction
  NumberField.galIdeleMulDistribMulAction Units.mulDistribMulActionRight
  NumberField.galIdeleClassMulDistribMulAction

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {S : Set (HeightOneSpectrum (𝓞 K))} {σ : L ≃ₐ[K] L}

/-! ## Finiteness of the Tate cohomology of the `S`-ideles -/

/-- **`Ĥ⁰(Gal(L/K), 𝕀_{L,S})` is finite**, under the same hypotheses that make
`NumberField.herbrand_sIdele` available.  This is the instance hypothesis of
`NumberField.herbrand_ideleClassGroup_of_herbrand_sIdele`. -/
theorem finite_tateH0_sIdele [IsGalois K L] [Fintype S]
    [∀ v : InfinitePlace K, Finite (TateH0 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ)]
    [∀ v : S, Finite (TateH0 (L ≃ₐ[K] L)
      (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)]
    [∀ v : ↥(Sᶜ), Subsingleton (TateH0 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ)] :
    Finite (TateH0 (L ≃ₐ[K] L)
      (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ) := by
  haveI := CyclicTate.finite_tateH0_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : InfinitePlace K ↦ (InfiniteLocalProduct L v)ˣ)
  haveI : Finite (TateH0 (L ≃ₐ[K] L) (Additive (InfiniteAdeleRing L)ˣ) σ) :=
    CyclicTate.finite_tateH0_of_mulEquiv σ (infiniteIdeleEquivPi K L).symm
      (fun g u ↦ ((infiniteIdeleEquivPi K L).eq_symm_apply.2
        (by rw [infiniteIdeleEquivPi_smul, MulEquiv.apply_symm_apply])).symm)
  haveI := CyclicTate.subsingleton_tateH0_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : ↥(Sᶜ) ↦ localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))
  haveI : Finite (TateH0 (L ≃ₐ[K] L)
      (Additive (∀ v : ↥(Sᶜ), localProductIntegerUnits K L
        (v : HeightOneSpectrum (𝓞 K)))) σ) := Finite.of_subsingleton
  haveI := CyclicTate.finite_tateH0_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : S ↦ (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ)
  haveI := CyclicTate.finite_tateH0_mulProd (G := L ≃ₐ[K] L) (σ := σ)
    (A := ∀ v : S, (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ)
    (B := ∀ v : ↥(Sᶜ), localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))
  haveI : Finite (TateH0 (L ≃ₐ[K] L)
      (Additive (FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S))) σ) :=
    CyclicTate.finite_tateH0_of_mulEquiv σ (finiteSIdeleSemilocalEquiv (Set.toFinite S)).symm
      (fun g u ↦ ((finiteSIdeleSemilocalEquiv (Set.toFinite S)).eq_symm_apply.2
        (by rw [finiteSIdeleSemilocalEquiv_smul, MulEquiv.apply_symm_apply])).symm)
  haveI := CyclicTate.finite_tateH0_mulProd (G := L ≃ₐ[K] L) (σ := σ)
    (A := (InfiniteAdeleRing L)ˣ)
    (B := FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S))
  exact CyclicTate.finite_tateH0_of_mulEquiv σ (sIdeleProdEquiv K L S).symm
    (fun g u ↦ ((sIdeleProdEquiv K L S).eq_symm_apply.2
      (by rw [sIdeleProdEquiv_smul, MulEquiv.apply_symm_apply])).symm)

/-- **`Ĥ¹(Gal(L/K), 𝕀_{L,S})` is finite.** -/
theorem finite_tateH1_sIdele [IsGalois K L] [Fintype S]
    [∀ v : InfinitePlace K, Finite (TateH1 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ)]
    [∀ v : S, Finite (TateH1 (L ≃ₐ[K] L)
      (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)]
    [∀ v : ↥(Sᶜ), Subsingleton (TateH1 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ)] :
    Finite (TateH1 (L ≃ₐ[K] L)
      (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ) := by
  haveI := CyclicTate.finite_tateH1_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : InfinitePlace K ↦ (InfiniteLocalProduct L v)ˣ)
  haveI : Finite (TateH1 (L ≃ₐ[K] L) (Additive (InfiniteAdeleRing L)ˣ) σ) :=
    CyclicTate.finite_tateH1_of_mulEquiv σ (infiniteIdeleEquivPi K L).symm
      (fun g u ↦ ((infiniteIdeleEquivPi K L).eq_symm_apply.2
        (by rw [infiniteIdeleEquivPi_smul, MulEquiv.apply_symm_apply])).symm)
  haveI := CyclicTate.subsingleton_tateH1_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : ↥(Sᶜ) ↦ localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))
  haveI : Finite (TateH1 (L ≃ₐ[K] L)
      (Additive (∀ v : ↥(Sᶜ), localProductIntegerUnits K L
        (v : HeightOneSpectrum (𝓞 K)))) σ) := Finite.of_subsingleton
  haveI := CyclicTate.finite_tateH1_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : S ↦ (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ)
  haveI := CyclicTate.finite_tateH1_mulProd (G := L ≃ₐ[K] L) (σ := σ)
    (A := ∀ v : S, (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ)
    (B := ∀ v : ↥(Sᶜ), localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))
  haveI : Finite (TateH1 (L ≃ₐ[K] L)
      (Additive (FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S))) σ) :=
    CyclicTate.finite_tateH1_of_mulEquiv σ (finiteSIdeleSemilocalEquiv (Set.toFinite S)).symm
      (fun g u ↦ ((finiteSIdeleSemilocalEquiv (Set.toFinite S)).eq_symm_apply.2
        (by rw [finiteSIdeleSemilocalEquiv_smul, MulEquiv.apply_symm_apply])).symm)
  haveI := CyclicTate.finite_tateH1_mulProd (G := L ≃ₐ[K] L) (σ := σ)
    (A := (InfiniteAdeleRing L)ˣ)
    (B := FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S))
  exact CyclicTate.finite_tateH1_of_mulEquiv σ (sIdeleProdEquiv K L S).symm
    (fun g u ↦ ((sIdeleProdEquiv K L S).eq_symm_apply.2
      (by rw [sIdeleProdEquiv_smul, MulEquiv.apply_symm_apply])).symm)

/-! ## `h(C_L) = [L : K]` -/

section Value

variable [IsGalois K L] [Fintype S] [Fintype (placesOverSet K L S)]

/-- **`h(C_L) = [L : K]` for a cyclic extension unramified at every place.**

The hypotheses are: `L / K` is cyclic with generator `σ`; `S` is a finite set of finite places
of `K` large enough that `𝕀_L = L^× · 𝕀_{L,S}` (`hsup`, available from
`NumberField.exists_galois_stable_sIdeleSubgroup_sup`); a place `w₁ v` of `L` is chosen above
each archimedean place `v` of `K`, with trivial decomposition group; a place `w₂ v` of `L` is
chosen above each finite place `v` of `K`, with cyclic decomposition group generated by `τ₂ v`,
and `v` is unramified in `L`.

Nothing else is assumed.  In particular the value of every local Herbrand quotient that enters
is *proved*, not hypothesised: `#D_w` at the finite places
(`NumberField.herbrand_adicCompletion_units_eq_card`) and `1` at the archimedean ones. -/
theorem herbrand_ideleClassGroup_eq_card_of_unramified
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (hsup : IdeleGroup.principalSubgroup (𝓞 L) L
      ⊔ IdeleGroup.sIdeleSubgroup L (placesOverSet K L S) = ⊤)
    (w₁ : ∀ v : InfinitePlace K, Fibre L v)
    [∀ v : InfinitePlace K, Subsingleton (stabilizer (L ≃ₐ[K] L) (w₁ v))]
    (w₂ : ∀ v : HeightOneSpectrum (𝓞 K), placesOver K L v)
    [∀ v : HeightOneSpectrum (𝓞 K), Fintype (stabilizer (L ≃ₐ[K] L) (w₂ v))]
    [∀ v : HeightOneSpectrum (𝓞 K),
      Fintype (decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L)))]
    (τ₂ : ∀ v : HeightOneSpectrum (𝓞 K),
      decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L)))
    (hτ₂ : ∀ (v : HeightOneSpectrum (𝓞 K))
      (d : decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L))),
      d ∈ Subgroup.zpowers (τ₂ v))
    (hram : ∀ v : HeightOneSpectrum (𝓞 K),
      v.asIdeal.ramificationIdx' (w₂ v : HeightOneSpectrum (𝓞 L)).asIdeal = 1) :
    CyclicTate.herbrand (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ
      = (Nat.card (L ≃ₐ[K] L) : ℚ) := by
  haveI hli : ∀ v : HeightOneSpectrum (𝓞 K),
      (w₂ v : HeightOneSpectrum (𝓞 L)).asIdeal.LiesOver v.asIdeal := fun v ↦ ⟨(w₂ v).2.symm⟩
  have hτ₂' : ∀ (v : HeightOneSpectrum (𝓞 K))
      (d : decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L))), ∃ m : ℕ, (τ₂ v) ^ m = d :=
    fun v d ↦ by
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff d (τ₂ v)).1
        (mem_powers_iff_mem_zpowers.2 (hτ₂ v d))
      exact ⟨k, hk⟩
  -- the archimedean semilocal factors have vanishing Tate cohomology
  haveI hi0 : ∀ v : InfinitePlace K, Subsingleton (TateH0 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ) := fun v ↦
    subsingleton_tateH0_infiniteLocalProductUnits (w₁ v) hgen
  haveI hi1 : ∀ v : InfinitePlace K, Subsingleton (TateH1 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ) := fun v ↦
    subsingleton_tateH1_infiniteLocalProductUnits (w₁ v) hgen
  haveI : ∀ v : InfinitePlace K, Finite (TateH0 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ) := fun _ ↦ Finite.of_subsingleton
  haveI : ∀ v : InfinitePlace K, Finite (TateH1 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ) := fun _ ↦ Finite.of_subsingleton
  -- the finite semilocal factors in `S` have finite Tate cohomology
  haveI : ∀ v : S, Finite (TateH0 (L ≃ₐ[K] L)
      (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ) := fun v ↦
    finite_tateH0_localProductUnits (w₂ (v : HeightOneSpectrum (𝓞 K)))
      (hram (v : HeightOneSpectrum (𝓞 K))) hgen (hτ₂ (v : HeightOneSpectrum (𝓞 K)))
  haveI : ∀ v : S, Finite (TateH1 (L ≃ₐ[K] L)
      (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ) := fun v ↦
    finite_tateH1_localProductUnits (w₂ (v : HeightOneSpectrum (𝓞 K)))
      (hram (v : HeightOneSpectrum (𝓞 K))) hgen (hτ₂ (v : HeightOneSpectrum (𝓞 K)))
  -- the factors outside `S` have vanishing Tate cohomology
  haveI : ∀ v : ↥(Sᶜ), Subsingleton (TateH0 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ) := fun v ↦
    subsingleton_tateH0_localProductIntegerUnits (w₂ (v : HeightOneSpectrum (𝓞 K)))
      (hram (v : HeightOneSpectrum (𝓞 K))) hgen (hτ₂ (v : HeightOneSpectrum (𝓞 K)))
  haveI : ∀ v : ↥(Sᶜ), Subsingleton (TateH1 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ) := fun v ↦
    subsingleton_tateH1_localProductIntegerUnits (w₂ (v : HeightOneSpectrum (𝓞 K)))
      (hram (v : HeightOneSpectrum (𝓞 K))) hgen (hτ₂ (v : HeightOneSpectrum (𝓞 K)))
  haveI := finite_tateH0_sIdele (S := S) (σ := σ)
  haveI := finite_tateH1_sIdele (S := S) (σ := σ)
  have hidele : CyclicTate.herbrand (L ≃ₐ[K] L)
        (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ
      = (∏ v : InfinitePlace K, (Nat.card (stabilizer (L ≃ₐ[K] L) (w₁ v)) : ℚ))
        * ∏ v : S, (Nat.card (stabilizer (L ≃ₐ[K] L)
            (placesOverToFibre (w₂ (v : HeightOneSpectrum (𝓞 K))))) : ℚ) := by
    rw [herbrand_sIdele]
    congr 1
    · refine Finset.prod_congr rfl fun v _ ↦ ?_
      haveI : Unique (stabilizer (L ≃ₐ[K] L) (w₁ v)) := uniqueOfSubsingleton 1
      rw [CyclicTate.herbrand_eq_one_of_subsingleton σ, Nat.card_unique, Nat.cast_one]
    · refine Finset.prod_congr rfl fun v _ ↦ ?_
      rw [herbrand_localProductUnits (w₂ (v : HeightOneSpectrum (𝓞 K))).2 hgen
          (hτ₂' (v : HeightOneSpectrum (𝓞 K))),
        herbrand_adicCompletion_units_eq_card (v : HeightOneSpectrum (𝓞 K))
          (w₂ (v : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 L))
          (hram (v : HeightOneSpectrum (𝓞 K))) (hτ₂ (v : HeightOneSpectrum (𝓞 K)))]
      congr 1
      rw [stabilizer_placesOverToFibre_eq, stabilizer_placesOver_eq]
  exact herbrand_ideleClassGroup_of_herbrand_sIdele S hgen hsup w₁
    (fun v : S ↦ placesOverToFibre (w₂ (v : HeightOneSpectrum (𝓞 K)))) hidele

/-- `Ĥ⁰(Gal(L/K), C_L)` is finite as soon as `Ĥ⁰(Gal(L/K), 𝕀_{L,S})` is, by the same argument
as `NumberField.finite_tateH1_ideleClassGroup`. -/
theorem finite_tateH0_ideleClassGroup
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (hsup : IdeleGroup.principalSubgroup (𝓞 L) L
      ⊔ IdeleGroup.sIdeleSubgroup L (placesOverSet K L S) = ⊤)
    [Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ)] :
    Finite (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ) := by
  haveI : Finite (CyclicTate.TateH1 (L ≃ₐ[K] L) (Additive (SUnitGroup K L S)) σ) :=
    CyclicTate.finite_tateH1_of_moduleFinite hgen
  exact (isShortExact_sUnit_sIdele S hsup).finite_tateH0_right σ

end Value

/-! ## The statement with no auxiliary set of places -/

section Everywhere

variable [IsGalois K L]

/-- **`h(C_L) = [L : K]`, with no auxiliary data beyond the choice of places.**

For a cyclic extension `L / K` of number fields in which every finite place of `K` is
unramified and every archimedean decomposition group is trivial,
`h(Gal(L/K), C_L) = [L : K]`.

The finite set `S` of `NumberField.herbrand_ideleClassGroup_eq_card_of_unramified` is supplied
here by `NumberField.exists_galois_stable_sIdeleSubgroup_sup`, i.e. by the finiteness of the
class group. -/
theorem herbrand_ideleClassGroup_eq_card_of_unramified_everywhere
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (w₁ : ∀ v : InfinitePlace K, Fibre L v)
    [∀ v : InfinitePlace K, Subsingleton (stabilizer (L ≃ₐ[K] L) (w₁ v))]
    (w₂ : ∀ v : HeightOneSpectrum (𝓞 K), placesOver K L v)
    (τ₂ : ∀ v : HeightOneSpectrum (𝓞 K),
      decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L)))
    (hτ₂ : ∀ (v : HeightOneSpectrum (𝓞 K))
      (d : decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L))),
      d ∈ Subgroup.zpowers (τ₂ v))
    (hram : ∀ v : HeightOneSpectrum (𝓞 K),
      v.asIdeal.ramificationIdx' (w₂ v : HeightOneSpectrum (𝓞 L)).asIdeal = 1) :
    CyclicTate.herbrand (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ
      = (Nat.card (L ≃ₐ[K] L) : ℚ) := by
  obtain ⟨T, hT, hTfin, hsup⟩ := exists_galois_stable_sIdeleSubgroup_sup (K := K) (L := L)
  haveI : Fintype T := hT.fintype
  haveI : Fintype (placesOverSet K L T) := hTfin.fintype
  haveI : ∀ v : HeightOneSpectrum (𝓞 K), Fintype (stabilizer (L ≃ₐ[K] L) (w₂ v)) := fun _ ↦
    Fintype.ofFinite _
  haveI : ∀ v : HeightOneSpectrum (𝓞 K),
      Fintype (decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L))) := fun _ ↦
    Fintype.ofFinite _
  exact herbrand_ideleClassGroup_eq_card_of_unramified hgen hsup w₁ w₂ τ₂ hτ₂ hram

/-- **The Tate cohomology of `C_L` is finite** for a cyclic extension unramified everywhere. -/
theorem finite_tateH0_ideleClassGroup_of_unramified_everywhere
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (w₁ : ∀ v : InfinitePlace K, Fibre L v)
    [∀ v : InfinitePlace K, Subsingleton (stabilizer (L ≃ₐ[K] L) (w₁ v))]
    (w₂ : ∀ v : HeightOneSpectrum (𝓞 K), placesOver K L v)
    (τ₂ : ∀ v : HeightOneSpectrum (𝓞 K),
      decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L)))
    (hτ₂ : ∀ (v : HeightOneSpectrum (𝓞 K))
      (d : decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L))),
      d ∈ Subgroup.zpowers (τ₂ v))
    (hram : ∀ v : HeightOneSpectrum (𝓞 K),
      v.asIdeal.ramificationIdx' (w₂ v : HeightOneSpectrum (𝓞 L)).asIdeal = 1) :
    Finite (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ) := by
  obtain ⟨T, hT, hTfin, hsup⟩ := exists_galois_stable_sIdeleSubgroup_sup (K := K) (L := L)
  haveI : Fintype T := hT.fintype
  haveI : Fintype (placesOverSet K L T) := hTfin.fintype
  haveI : ∀ v : HeightOneSpectrum (𝓞 K), Fintype (stabilizer (L ≃ₐ[K] L) (w₂ v)) := fun _ ↦
    Fintype.ofFinite _
  haveI : ∀ v : HeightOneSpectrum (𝓞 K),
      Fintype (decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L))) := fun _ ↦
    Fintype.ofFinite _
  haveI : ∀ v : InfinitePlace K, Subsingleton (TateH0 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ) := fun v ↦
    subsingleton_tateH0_infiniteLocalProductUnits (w₁ v) hgen
  haveI : ∀ v : InfinitePlace K, Finite (TateH0 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ) := fun _ ↦ Finite.of_subsingleton
  haveI : ∀ v : T, Finite (TateH0 (L ≃ₐ[K] L)
      (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ) := fun v ↦
    finite_tateH0_localProductUnits (w₂ (v : HeightOneSpectrum (𝓞 K)))
      (hram (v : HeightOneSpectrum (𝓞 K))) hgen (hτ₂ (v : HeightOneSpectrum (𝓞 K)))
  haveI : ∀ v : ↥(Tᶜ), Subsingleton (TateH0 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ) := fun v ↦
    subsingleton_tateH0_localProductIntegerUnits (w₂ (v : HeightOneSpectrum (𝓞 K)))
      (hram (v : HeightOneSpectrum (𝓞 K))) hgen (hτ₂ (v : HeightOneSpectrum (𝓞 K)))
  haveI := finite_tateH0_sIdele (S := T) (σ := σ)
  exact finite_tateH0_ideleClassGroup (S := T) hgen hsup

/-- **`Ĥ¹(Gal(L/K), C_L)` is finite** for a cyclic extension unramified everywhere. -/
theorem finite_tateH1_ideleClassGroup_of_unramified_everywhere
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (w₁ : ∀ v : InfinitePlace K, Fibre L v)
    [∀ v : InfinitePlace K, Subsingleton (stabilizer (L ≃ₐ[K] L) (w₁ v))]
    (w₂ : ∀ v : HeightOneSpectrum (𝓞 K), placesOver K L v)
    (τ₂ : ∀ v : HeightOneSpectrum (𝓞 K),
      decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L)))
    (hτ₂ : ∀ (v : HeightOneSpectrum (𝓞 K))
      (d : decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L))),
      d ∈ Subgroup.zpowers (τ₂ v))
    (hram : ∀ v : HeightOneSpectrum (𝓞 K),
      v.asIdeal.ramificationIdx' (w₂ v : HeightOneSpectrum (𝓞 L)).asIdeal = 1) :
    Finite (CyclicTate.TateH1 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ) := by
  obtain ⟨T, hT, hTfin, hsup⟩ := exists_galois_stable_sIdeleSubgroup_sup (K := K) (L := L)
  haveI : Fintype T := hT.fintype
  haveI : Fintype (placesOverSet K L T) := hTfin.fintype
  haveI : ∀ v : HeightOneSpectrum (𝓞 K), Fintype (stabilizer (L ≃ₐ[K] L) (w₂ v)) := fun _ ↦
    Fintype.ofFinite _
  haveI : ∀ v : HeightOneSpectrum (𝓞 K),
      Fintype (decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L))) := fun _ ↦
    Fintype.ofFinite _
  haveI : ∀ v : InfinitePlace K, Subsingleton (TateH1 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ) := fun v ↦
    subsingleton_tateH1_infiniteLocalProductUnits (w₁ v) hgen
  haveI : ∀ v : InfinitePlace K, Finite (TateH1 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ) := fun _ ↦ Finite.of_subsingleton
  haveI : ∀ v : T, Finite (TateH1 (L ≃ₐ[K] L)
      (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ) := fun v ↦
    finite_tateH1_localProductUnits (w₂ (v : HeightOneSpectrum (𝓞 K)))
      (hram (v : HeightOneSpectrum (𝓞 K))) hgen (hτ₂ (v : HeightOneSpectrum (𝓞 K)))
  haveI : ∀ v : ↥(Tᶜ), Subsingleton (TateH1 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ) := fun v ↦
    subsingleton_tateH1_localProductIntegerUnits (w₂ (v : HeightOneSpectrum (𝓞 K)))
      (hram (v : HeightOneSpectrum (𝓞 K))) hgen (hτ₂ (v : HeightOneSpectrum (𝓞 K)))
  haveI := finite_tateH1_sIdele (S := T) (σ := σ)
  exact finite_tateH1_ideleClassGroup T hgen hsup

end Everywhere

end NumberField
