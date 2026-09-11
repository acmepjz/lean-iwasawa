/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.AdeleCongr
public import Mathlib.RingTheory.Invariant.Galois

@[expose] public section

/-!
# The Galois action on the finite places of a number field

The Galois group of `L / K` permutes the finite places of `L`, and it preserves the finite
place of `K` below.  This file proves that, packages the fibres
`{w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}` as `Gal(L/K)`-sets, and shows that the
action on each fibre is transitive when `L / K` is Galois.  Together with
`Iwasawalib.NumberTheory.CFT.InfiniteAdeleBaseChange` (the archimedean counterpart), this is
the combinatorial input for Shapiro's lemma.

## Main definitions

* `NumberField.FinitePlaceFibre L v` : the finite places of `L` above the finite place `v`
  of `K`, with its `Gal(L/K)`-action.

## Main results

* `NumberField.under_equivOfRingEquiv_symm` : the Galois action preserves the place below.
* `NumberField.exists_algEquiv_map_eq`, `NumberField.FinitePlaceFibre.exists_smul_eq` :
  transitivity of `Gal(L/K)` on the fibre.
* `NumberField.galRestrict_eq_mapRingEquiv` : the `AKLB` Galois restriction agrees with
  `NumberField.RingOfIntegers.mapRingEquiv`.
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
theorem coe_smul_ringOfIntegers (σ : L ≃ₐ[K] L) (x : 𝓞 L) : ((σ • x : 𝓞 L) : L) = σ (x : L) :=
  rfl

instance : SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) where
  smul_comm σ a b := by
    apply RingOfIntegers.ext_iff.2
    have h1 : ∀ c : 𝓞 L, ((a • c : 𝓞 L) : L) = algebraMap (𝓞 K) L a * (c : L) := by
      intro c
      rw [Algebra.smul_def]
      push_cast
      congr 1
    rw [coe_smul_ringOfIntegers, h1, h1, coe_smul_ringOfIntegers, map_mul]
    congr 1
    · rw [IsScalarTower.algebraMap_apply (𝓞 K) K L]
      exact σ.commutes _

/-- The restriction of `σ : Gal(L/K)` to the ring of integers agrees with
`NumberField.RingOfIntegers.mapRingEquiv`. -/
theorem galRestrict_eq_mapRingEquiv (g : L ≃ₐ[K] L) (b : 𝓞 L) :
    galRestrict (𝓞 K) K L (𝓞 L) g b = RingOfIntegers.mapRingEquiv (g : L ≃+* L) b := by
  apply RingOfIntegers.ext_iff.2
  show (algebraMap (𝓞 L) L) (galRestrict (𝓞 K) K L (𝓞 L) g b) = _
  rw [algebraMap_galRestrict_apply]
  rfl

omit [NumberField K] [NumberField L] in
theorem mapRingEquiv_comp_algebraMap (σ : L ≃ₐ[K] L) :
    ((RingOfIntegers.mapRingEquiv (σ : L ≃+* L) : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L).comp
        (algebraMap (𝓞 K) (𝓞 L)) = algebraMap (𝓞 K) (𝓞 L) := by
  refine RingHom.ext fun x ↦ ?_
  apply RingOfIntegers.ext_iff.2
  have h : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (algebraMap (𝓞 K) K x) := by
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) K L]
    exact (IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L x).symm
  show ((RingOfIntegers.mapRingEquiv (σ : L ≃+* L) (algebraMap (𝓞 K) (𝓞 L) x) : 𝓞 L) : L) = _
  rw [RingOfIntegers.mapRingEquiv_apply, h]
  exact σ.commutes _

omit [NumberField K] [NumberField L] in
/-- The Galois action on the finite places of `L` preserves the finite place of `K` below. -/
theorem under_equivOfRingEquiv_symm (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    ((equivOfRingEquiv (RingOfIntegers.mapRingEquiv (σ : L ≃+* L))).symm w).under (𝓞 K) =
      w.under (𝓞 K) := by
  refine HeightOneSpectrum.ext ?_
  show (w.asIdeal.comap
      ((RingOfIntegers.mapRingEquiv (σ : L ≃+* L) : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L)).comap
      (algebraMap (𝓞 K) (𝓞 L)) = w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L))
  rw [Ideal.comap_comap, mapRingEquiv_comp_algebraMap σ]

omit [NumberField K] [NumberField L] in
theorem smul_ideal_eq_map (I : Ideal (𝓞 L)) (g : 𝓞 L ≃ₐ[𝓞 K] 𝓞 L) :
    g • I = I.map (g : 𝓞 L →+* 𝓞 L) := rfl

/-- `Gal(L/K)` acts transitively on the finite places of `L` above a fixed finite place
of `K`. -/
theorem exists_algEquiv_map_eq [IsGalois K L] (w w' : HeightOneSpectrum (𝓞 L))
    (h : w.under (𝓞 K) = w'.under (𝓞 K)) :
    ∃ σ : L ≃ₐ[K] L, equivOfRingEquiv (RingOfIntegers.mapRingEquiv (σ : L ≃+* L)) w = w' := by
  haveI := w.isPrime
  haveI := w'.isPrime
  haveI : Algebra.IsInvariant (𝓞 K) (𝓞 L) (𝓞 L ≃ₐ[𝓞 K] 𝓞 L) :=
    Algebra.isInvariant_of_isGalois' (𝓞 K) K L (𝓞 L)
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L)
    (𝓞 L ≃ₐ[𝓞 K] 𝓞 L) w.asIdeal w'.asIdeal (congrArg HeightOneSpectrum.asIdeal h)
  refine ⟨(galRestrict (𝓞 K) K L (𝓞 L)).symm g, HeightOneSpectrum.ext ?_⟩
  have hσ : RingOfIntegers.mapRingEquiv
      ((((galRestrict (𝓞 K) K L (𝓞 L)).symm g : L ≃ₐ[K] L) : L ≃+* L)) = (g : 𝓞 L ≃+* 𝓞 L) := by
    refine RingEquiv.ext fun b ↦ ?_
    rw [← galRestrict_eq_mapRingEquiv, MulEquiv.apply_symm_apply]
    rfl
  show w.asIdeal.comap
    ((RingOfIntegers.mapRingEquiv
      ((((galRestrict (𝓞 K) K L (𝓞 L)).symm g : L ≃ₐ[K] L) : L ≃+* L))).symm :
        𝓞 L →+* 𝓞 L) = w'.asIdeal
  rw [hσ, hg, smul_ideal_eq_map]
  exact Ideal.comap_symm _

/-! ## The fibre of finite places -/

variable (L)

/-- The finite places of `L` lying above a finite place `v` of `K`. -/
abbrev FinitePlaceFibre (v : HeightOneSpectrum (𝓞 K)) : Type _ :=
  {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}

variable {L} {v : HeightOneSpectrum (𝓞 K)}

namespace FinitePlaceFibre

instance : MulAction (L ≃ₐ[K] L) (FinitePlaceFibre L v) where
  smul σ w := ⟨(equivOfRingEquiv
      (RingOfIntegers.mapRingEquiv ((σ⁻¹ : L ≃ₐ[K] L) : L ≃+* L))).symm (w : _),
    (under_equivOfRingEquiv_symm σ⁻¹ _).trans w.2⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

omit [NumberField K] [NumberField L] in
theorem coe_smul (σ : L ≃ₐ[K] L) (w : FinitePlaceFibre L v) :
    ((σ • w : FinitePlaceFibre L v) : HeightOneSpectrum (𝓞 L)) =
      equivOfRingEquiv (RingOfIntegers.mapRingEquiv (σ : L ≃+* L)) w := rfl

/-- `Gal(L/K)` acts transitively on the finite places above a fixed finite place of `K`. -/
theorem exists_smul_eq [IsGalois K L] (w w' : FinitePlaceFibre L v) :
    ∃ σ : L ≃ₐ[K] L, σ • w = w' := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_map_eq (w : HeightOneSpectrum (𝓞 L)) w'
    (w.2.trans w'.2.symm)
  exact ⟨σ, Subtype.ext ((coe_smul σ w).trans hσ)⟩

instance [IsGalois K L] : MulAction.IsPretransitive (L ≃ₐ[K] L) (FinitePlaceFibre L v) :=
  ⟨fun w w' ↦ exists_smul_eq w w'⟩

/-- Orbit-stabiliser for finite places: as a `Gal(L/K)`-set the fibre above `v` is the coset
space `Gal(L/K) ⧸ D_w`. -/
def equivQuotientStabilizer [IsGalois K L] (w : FinitePlaceFibre L v) :
    FinitePlaceFibre L v ≃ (L ≃ₐ[K] L) ⧸ MulAction.stabilizer (L ≃ₐ[K] L) w :=
  ((Equiv.Set.univ (FinitePlaceFibre L v)).symm.trans
    (Equiv.setCongr (MulAction.orbit_eq_univ (L ≃ₐ[K] L) w).symm)).trans
      (MulAction.orbitEquivQuotientStabilizer (L ≃ₐ[K] L) w)

@[simp]
theorem equivQuotientStabilizer_symm_apply [IsGalois K L] (w : FinitePlaceFibre L v)
    (g : L ≃ₐ[K] L) :
    (equivQuotientStabilizer w).symm (QuotientGroup.mk g) = g • w :=
  MulAction.orbitEquivQuotientStabilizer_symm_apply (L ≃ₐ[K] L) w g

end FinitePlaceFibre

end NumberField
