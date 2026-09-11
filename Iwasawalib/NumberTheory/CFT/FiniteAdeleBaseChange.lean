/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.AdicCompletionBaseChange
public import Iwasawalib.NumberTheory.CFT.FinitePlaceFibre

@[expose] public section

/-!
# Base change of the finite adele ring

Let `A ⊆ B` be an extension of Dedekind domains with fraction fields `K ⊆ L`.  Assembling the
local base change maps `K_v →+* L_w` of
`Iwasawalib.NumberTheory.CFT.AdicCompletionBaseChange` over all height one primes `w` of `B`
gives the base change map

`IsDedekindDomain.FiniteAdeleRing.baseChange : FiniteAdeleRing A K →+* FiniteAdeleRing B L`.

The restricted product is taken along the map `w ↦ w.under A`, which tends to `cofinite`
along `cofinite` because the fibres — the primes of `B` above a fixed prime of `A` — are
finite.

For a Galois extension of number fields the image of `𝔸_K^f` consists of `Gal(L/K)`-invariant
finite adeles; this is the easy inclusion `𝔸_K^f ⊆ (𝔸_L^f)^{Gal(L/K)}`.

## Main definitions

* `IsDedekindDomain.FiniteAdeleRing.baseChange` : the ring homomorphism `𝔸_K^f →+* 𝔸_L^f`.
* `IsDedekindDomain.FiniteAdeleRing.baseChangeAlgebra` : the induced `𝔸_K^f`-algebra structure
  on `𝔸_L^f`.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.finite_setOf_under_eq`,
  `IsDedekindDomain.FiniteAdeleRing.tendsto_under` : the fibres of `w ↦ w.under A` are finite.
* `IsDedekindDomain.FiniteAdeleRing.continuous_baseChange`,
  `IsDedekindDomain.FiniteAdeleRing.baseChange_injective`.
* `NumberField.finiteAdeleMap_baseChange`, `NumberField.finiteAdele_smul_baseChange`,
  `NumberField.range_finiteAdeleBaseChange_le_fixedPoints` : the finite adeles coming from the
  base field are fixed by `Gal(L/K)`.
* `IsDedekindDomain.FiniteAdeleRing.baseChange_trans`,
  `NumberField.finiteAdeleBaseChange_trans` : functoriality in a tower `K ⊆ L ⊆ M`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct

namespace IsDedekindDomain.FiniteAdeleRing

/-! ## Finiteness of the fibres -/

section Fibre

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]

/-- There are only finitely many height one primes of `B` above a given height one prime
of `A`. -/
theorem finite_setOf_under_eq (v : HeightOneSpectrum A) :
    {w : HeightOneSpectrum B | w.under A = v}.Finite := by
  refine Set.Finite.of_finite_image (f := fun w : HeightOneSpectrum B ↦ w.asIdeal) ?_
    (fun w _ w' _ h ↦ HeightOneSpectrum.ext h)
  refine (IsDedekindDomain.primesOver_finite v.asIdeal B).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, ⟨by rw [← hw]; rfl⟩⟩

/-- The map `w ↦ w.under A` on height one spectra has finite fibres, hence is continuous for
the cofinite filters. -/
theorem tendsto_under :
    Tendsto (fun w : HeightOneSpectrum B ↦ w.under A) cofinite cofinite :=
  Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v ↦
    (finite_setOf_under_eq v).to_subtype

end Fibre

/-! ## The base change map -/

section BaseChange

variable {A B : Type*} (K L : Type*)
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]

/-- The base change map `𝔸_K^f →+* 𝔸_L^f` on finite adele rings: the `w`-component of
`baseChange x` is the image of the component of `x` at the prime `w.under A` of `A` under the
local base change map `K_{w.under A} →+* L_w`. -/
def baseChange : FiniteAdeleRing A K →+* FiniteAdeleRing B L :=
  RestrictedProduct.mapAlongRingHom
    (fun v : HeightOneSpectrum A ↦ v.adicCompletion K)
    (fun w : HeightOneSpectrum B ↦ w.adicCompletion L)
    (fun w ↦ w.under A) tendsto_under
    (fun w ↦ adicCompletionComap K L (w.under A) w)
    (Eventually.of_forall fun w ↦ adicCompletionComap_mapsTo_integers K L (w.under A) w)

@[simp]
theorem baseChange_apply (x : FiniteAdeleRing A K) (w : HeightOneSpectrum B) :
    baseChange K L x w = adicCompletionComap K L (w.under A) w (x (w.under A)) := rfl

theorem continuous_baseChange : Continuous (baseChange (A := A) (B := B) K L) :=
  RestrictedProduct.mapAlong_continuous _ _ _ tendsto_under _
    (Eventually.of_forall fun w ↦ adicCompletionComap_mapsTo_integers K L (w.under A) w)
    fun w ↦ continuous_adicCompletionComap K L (w.under A) w

@[simp]
theorem baseChange_algebraMap (k : K) :
    baseChange K L (algebraMap K (FiniteAdeleRing A K) k) =
      algebraMap L (FiniteAdeleRing B L) (algebraMap K L k) := by
  refine FiniteAdeleRing.ext L fun w ↦ ?_
  rw [baseChange_apply]
  simp only [FiniteAdeleRing.algebraMap_apply]
  exact adicCompletionComap_coe K L (w.under A) w k

/-- The `𝔸_K^f`-algebra structure on `𝔸_L^f` given by base change. -/
@[instance_reducible]
def baseChangeAlgebra : Algebra (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
  (baseChange K L).toAlgebra

theorem baseChange_injective [FaithfulSMul A B] :
    Function.Injective (baseChange (A := A) (B := B) K L) := by
  intro x y hxy
  refine FiniteAdeleRing.ext K fun v ↦ ?_
  haveI : v.asIdeal.IsPrime := v.isPrime
  obtain ⟨⟨Q, hQp, hQo⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver B))
  haveI := hQp
  haveI := hQo
  have hQbot : Q ≠ ⊥ := by
    intro h
    refine v.ne_bot ?_
    have hv : v.asIdeal = Q.under A := Ideal.over_def Q v.asIdeal
    rw [hv, h, Ideal.under_bot]
  set w : HeightOneSpectrum B := ⟨Q, hQp, hQbot⟩ with hw
  have hwv : w.under A = v :=
    HeightOneSpectrum.ext (Ideal.over_def Q v.asIdeal).symm
  have h := congrArg (fun z : FiniteAdeleRing B L ↦ z w) hxy
  simp only [baseChange_apply] at h
  haveI : w.asIdeal.LiesOver v.asIdeal := hQo
  haveI : w.asIdeal.LiesOver (w.under A).asIdeal := ⟨rfl⟩
  rw [adicCompletionComap_index_congr K L hwv w (fun t ↦ x t),
    adicCompletionComap_index_congr K L hwv w (fun t ↦ y t)] at h
  exact adicCompletionComap_injective K L v w h

end BaseChange

end IsDedekindDomain.FiniteAdeleRing

/-! ## Compatibility of the base change with an automorphism of `L` over `K` -/

namespace IsDedekindDomain.FiniteAdeleRing

section Invariance

variable {A B : Type*} (K L : Type*)
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]

/-- An automorphism `σ` of `L` fixing `K` pointwise carries the base change at a prime `u`
above `v` to the base change at the prime `σ • u`. -/
theorem adicCompletionCongr_adicCompletionComap (σ : L ≃+* L)
    (hσ : ∀ k : K, σ (algebraMap K L k) = algebraMap K L k)
    (v : HeightOneSpectrum A) (u w : HeightOneSpectrum B)
    [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
    (h : ∀ y : L, w.valuation L (σ y) = u.valuation L y) (z : v.adicCompletion K) :
    adicCompletionCongr σ u w h (adicCompletionComap K L v u z) =
      adicCompletionComap K L v w z := by
  have hcont₁ : Continuous fun z : v.adicCompletion K ↦
      adicCompletionCongr σ u w h (adicCompletionComap K L v u z) :=
    (continuous_adicCompletionCongr σ u w h).comp (continuous_adicCompletionComap K L v u)
  have hcont₂ : Continuous (adicCompletionComap K L v w) :=
    continuous_adicCompletionComap K L v w
  have := Continuous.ext_on (denseRange_algebraMap (R := A) (K := K) (v := v))
    hcont₁ hcont₂ ?_
  · exact congrFun this z
  · rintro _ ⟨k, rfl⟩
    show adicCompletionCongr σ u w h (adicCompletionComap K L v u ((k : K) : v.adicCompletion K))
        = adicCompletionComap K L v w ((k : K) : v.adicCompletion K)
    rw [adicCompletionComap_coe, adicCompletionCongr_coe, adicCompletionComap_coe, hσ]

end Invariance

end IsDedekindDomain.FiniteAdeleRing

/-! ## The finite adeles of the base field are Galois invariant -/

namespace NumberField

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing

variable (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]

/-- The base change map `𝔸_K^f →+* 𝔸_L^f` for an extension of number fields. -/
abbrev finiteAdeleBaseChange : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L :=
  baseChange K L

/-- The `𝔸_K^f`-algebra structure on `𝔸_L^f` for an extension of number fields. -/
@[instance_reducible]
def finiteAdeleBaseChangeAlgebra :
    Algebra (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L) :=
  (finiteAdeleBaseChange K L).toAlgebra

theorem finiteAdeleBaseChange_injective :
    Function.Injective (finiteAdeleBaseChange K L) :=
  baseChange_injective K L

theorem continuous_finiteAdeleBaseChange : Continuous (finiteAdeleBaseChange K L) :=
  continuous_baseChange K L

variable {K L}

/-- **The easy inclusion `𝔸_K^f ⊆ (𝔸_L^f)^{Gal(L/K)}`.**  A finite adele of `L` coming from
the base field `K` is fixed by every `K`-automorphism of `L`. -/
theorem finiteAdeleMap_baseChange (σ : L ≃ₐ[K] L) (x : FiniteAdeleRing (𝓞 K) K) :
    finiteAdeleMap (σ : L ≃+* L) (finiteAdeleBaseChange K L x) =
      finiteAdeleBaseChange K L x := by
  refine FiniteAdeleRing.ext L fun w ↦ ?_
  set u : HeightOneSpectrum (𝓞 L) :=
    (equivOfRingEquiv (RingOfIntegers.mapRingEquiv (σ : L ≃+* L))).symm w with hu
  have huw : u.under (𝓞 K) = w.under (𝓞 K) := under_equivOfRingEquiv_symm σ w
  haveI : u.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := huw ▸ liesOver_under (A := 𝓞 K) u
  have hcongr := adicCompletionCongr_adicCompletionComap K L (σ : L ≃+* L)
    (fun k ↦ σ.commutes k) (w.under (𝓞 K)) u w
    (valuation_symm_equivOfRingEquiv (RingOfIntegers.mapRingEquiv (σ : L ≃+* L))
      (σ : L ≃+* L) (mapRingEquiv_compat (σ : L ≃+* L)) w)
    (x (w.under (𝓞 K)))
  simp only [finiteAdeleMap, FiniteAdeleRing.congrRingHom_apply, baseChange_apply]
  rw [adicCompletionComap_index_congr K L huw u (fun t ↦ x t)]
  exact hcongr

/-- The `Gal(L/K)`-action on `𝔸_L^f` fixes the image of `𝔸_K^f`. -/
@[simp]
theorem finiteAdele_smul_baseChange (σ : L ≃ₐ[K] L) (x : FiniteAdeleRing (𝓞 K) K) :
    σ • finiteAdeleBaseChange K L x = finiteAdeleBaseChange K L x :=
  finiteAdeleMap_baseChange σ x

variable (K L)

/-- **`𝔸_K^f ⊆ (𝔸_L^f)^{Gal(L/K)}`**, stated as an inclusion of subrings of `𝔸_L^f`. -/
theorem range_finiteAdeleBaseChange_le_fixedPoints :
    (finiteAdeleBaseChange K L).range ≤
      FixedPoints.subring (FiniteAdeleRing (𝓞 L) L) (L ≃ₐ[K] L) := by
  rintro _ ⟨x, rfl⟩ σ
  exact finiteAdele_smul_baseChange σ x

end NumberField

/-! ## Functoriality in a tower -/

namespace IsDedekindDomain.FiniteAdeleRing

section Tower

variable {A B C : Type*} (K L M : Type*)
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [CommRing C] [IsDedekindDomain C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [Module.IsTorsionFree A B] [Module.IsTorsionFree B C] [Module.IsTorsionFree A C]
  [Algebra.IsIntegral A B] [Algebra.IsIntegral B C] [Algebra.IsIntegral A C]
variable [Field K] [Field L] [Field M] [Algebra K L] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M]
variable [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
  [Algebra C M] [IsFractionRing C M]
variable [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
variable [Algebra B M] [IsScalarTower B L M] [IsScalarTower B C M]
variable [Algebra A M] [IsScalarTower A K M] [IsScalarTower A C M]

omit [Module.IsTorsionFree A B] [Module.IsTorsionFree B C] [Module.IsTorsionFree A C] in
theorem under_under' (u : HeightOneSpectrum C) : (u.under B).under A = u.under A :=
  HeightOneSpectrum.ext (Ideal.under_under u.asIdeal)

/-- The base change maps on finite adele rings compose in a tower `K ⊆ L ⊆ M`. -/
theorem baseChange_trans (x : FiniteAdeleRing A K) :
    baseChange (A := B) (B := C) L M (baseChange (A := A) (B := B) K L x) =
      baseChange (A := A) (B := C) K M x := by
  refine FiniteAdeleRing.ext M fun u ↦ ?_
  haveI : u.asIdeal.LiesOver ((u.under B).under A).asIdeal :=
    ⟨Ideal.under_under u.asIdeal⟩
  rw [baseChange_apply, baseChange_apply, baseChange_apply,
    adicCompletionComap_trans K L M ((u.under B).under A) (u.under B) u]
  exact adicCompletionComap_index_congr K M (under_under' (A := A) (B := B) u) u (fun t ↦ x t)

end Tower

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField

open IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  (M : Type*) [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M]

/-- Base change of finite adeles is functorial in a tower of number fields `K ⊆ L ⊆ M`. -/
theorem finiteAdeleBaseChange_trans (x : FiniteAdeleRing (𝓞 K) K) :
    finiteAdeleBaseChange L M (finiteAdeleBaseChange K L x) = finiteAdeleBaseChange K M x :=
  IsDedekindDomain.FiniteAdeleRing.baseChange_trans K L M x

end NumberField
