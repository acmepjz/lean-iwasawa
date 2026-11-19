/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.AdicCompletionCongr
public import Mathlib.NumberTheory.RamificationInertia.Valuation

@[expose] public section

/-!
# Base change of adic completions

Let `A ⊆ B` be an extension of Dedekind domains with fraction fields `K ⊆ L`, let `v` be a
height one prime of `A` and let `w` be a height one prime of `B` lying over `v`.  The
inclusion `K → L` is *not* an isometry from the `v`-adic valuation to the `w`-adic valuation:
by `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver` it raises valuations to the power
`e = e(w|v)`, the ramification index.  It is nevertheless uniformly continuous
(`IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver`), hence extends
to a ring homomorphism of completions

`IsDedekindDomain.HeightOneSpectrum.adicCompletionComap : K_v →+* L_w`.

This is the local input for the base change map on finite adele rings.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionComap` : the map `K_v →+* L_w`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionComapAlgebra` : the induced `K_v`-algebra
  structure on `L_w` (not an instance, to avoid diamonds).

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valued_adicCompletionComap` :
  `v(f x) = v(x) ^ e(w|v)`, the completed form of `valuation_liesOver`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionComap_mapsTo_integers` : the map carries
  `O_v` into `O_w`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionComap_trans` : functoriality in a tower
  `K ⊆ L ⊆ M`.
-/

noncomputable section

open IsDedekindDomain WithZeroTopology
open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

/-! ## The `LiesOver` instance coming from `HeightOneSpectrum.under` -/

section Under

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  [Algebra.IsIntegral A B]

/-- A height one prime of `B` lies over the height one prime of `A` beneath it. -/
instance liesOver_under (w : HeightOneSpectrum B) :
    w.asIdeal.LiesOver (w.under A).asIdeal :=
  ⟨rfl⟩

theorem under_asIdeal' (w : HeightOneSpectrum B) :
    (w.under A).asIdeal = w.asIdeal.under A := rfl

end Under

/-! ## The base change map on completions -/

section BaseChange

variable {A B : Type*} (K L : Type*)
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

/-- The base change map `K_v →+* L_w` on adic completions, for `w` a height one prime of `B`
lying over the height one prime `v` of `A`.  Unlike the archimedean case this is *not* an
isometry: it multiplies valuations by the ramification index. -/
def adicCompletionComap : v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
        (uniformContinuous_algebraMap_liesOver K L v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom)

theorem adicCompletionComap_apply (x : v.adicCompletion K) :
    adicCompletionComap K L v w x =
      adicCompletion.ofCompletion (UniformSpace.Completion.map
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) x.toCompletion) := rfl

theorem continuous_adicCompletionComap : Continuous (adicCompletionComap K L v w) :=
  (adicCompletion.continuous_ofCompletion L w).comp
    (UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v))

@[simp]
theorem adicCompletionComap_coe (k : K) :
    adicCompletionComap K L v w (k : v.adicCompletion K) =
      ((algebraMap K L k : L) : w.adicCompletion L) := by
  rw [adicCompletionComap_apply]
  congr 1
  exact UniformSpace.Completion.map_coe (uniformContinuous_algebraMap_liesOver K L v w) _

@[simp]
theorem adicCompletionComap_algebraMap (k : K) :
    adicCompletionComap K L v w (algebraMap K (v.adicCompletion K) k) =
      algebraMap L (w.adicCompletion L) (algebraMap K L k) :=
  adicCompletionComap_coe K L v w k

/-- **The completed ramification comparison.**  The base change map raises the `v`-adic
valuation to the power `e(w|v)`. -/
theorem valued_adicCompletionComap (x : v.adicCompletion K) :
    (Valued.v (adicCompletionComap K L v w x) : ℤᵐ⁰) =
      (Valued.v x : ℤᵐ⁰) ^ (v.asIdeal.ramificationIdx' w.asIdeal) := by
  have hcont₁ : Continuous fun x : v.adicCompletion K ↦
      (Valued.v (adicCompletionComap K L v w x) : ℤᵐ⁰) :=
    (Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective L w)).comp
      (continuous_adicCompletionComap K L v w)
  have hcont₂ : Continuous fun x : v.adicCompletion K ↦
      (Valued.v x : ℤᵐ⁰) ^ (v.asIdeal.ramificationIdx' w.asIdeal) :=
    (continuous_pow _).comp
      (Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective K v))
  have := Continuous.ext_on (denseRange_algebraMap (R := A) (K := K) (v := v))
    hcont₁ hcont₂ ?_
  · exact congrFun this x
  · rintro _ ⟨k, rfl⟩
    show (Valued.v (adicCompletionComap K L v w ((k : K) : v.adicCompletion K)) : ℤᵐ⁰)
        = (Valued.v ((k : K) : v.adicCompletion K) : ℤᵐ⁰) ^ _
    rw [adicCompletionComap_coe, adicCompletion.valued_coe, adicCompletion.valued_coe,
      Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
      valuation_liesOver L v w k]

/-- The base change map carries the ring of integers of `K_v` into that of `L_w`. -/
theorem adicCompletionComap_mapsTo_integers :
    Set.MapsTo (adicCompletionComap K L v w) (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) := by
  intro x hx
  rw [SetLike.mem_coe, mem_adicCompletionIntegers, valued_adicCompletionComap]
  exact pow_le_one₀ zero_le hx

theorem adicCompletionComap_injective : Function.Injective (adicCompletionComap K L v w) :=
  (adicCompletionComap K L v w).injective

/-- The `K_v`-algebra structure on `L_w` given by base change.  This is not an instance: it
depends on the choice of `v` and on the `LiesOver` hypothesis. -/
@[instance_reducible]
def adicCompletionComapAlgebra : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (adicCompletionComap K L v w).toAlgebra

end BaseChange

/-! ## Transport along an equality of places, and functoriality -/

section Congr

variable {A B : Type*} (K L : Type*)
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]

/-- Transporting the source index of `adicCompletionComap` along an equality of places. -/
theorem adicCompletionComap_index_congr {v v' : HeightOneSpectrum A} (hv : v = v')
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v'.asIdeal]
    (x : ∀ t : HeightOneSpectrum A, t.adicCompletion K) :
    adicCompletionComap K L v w (x v) = adicCompletionComap K L v' w (x v') := by
  subst hv
  congr!

end Congr

/-! ## Functoriality in a tower -/

section Tower

variable {A B C : Type*} (K L M : Type*)
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [CommRing C] [IsDedekindDomain C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [Module.IsTorsionFree A B] [Module.IsTorsionFree B C] [Module.IsTorsionFree A C]
variable [Field K] [Field L] [Field M] [Algebra K L] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M]
variable [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
  [Algebra C M] [IsFractionRing C M]
variable [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
variable [Algebra B M] [IsScalarTower B L M] [IsScalarTower B C M]
variable [Algebra A M] [IsScalarTower A K M] [IsScalarTower A C M]
variable (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (u : HeightOneSpectrum C)
  [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal]
  [u.asIdeal.LiesOver v.asIdeal]

omit [IsScalarTower A B C] in
/-- The local base change maps compose in a tower `K ⊆ L ⊆ M`. -/
theorem adicCompletionComap_trans (z : v.adicCompletion K) :
    adicCompletionComap L M w u (adicCompletionComap K L v w z) =
      adicCompletionComap K M v u z := by
  have hcont₁ : Continuous fun z : v.adicCompletion K ↦
      adicCompletionComap L M w u (adicCompletionComap K L v w z) :=
    (continuous_adicCompletionComap L M w u).comp (continuous_adicCompletionComap K L v w)
  have hcont₂ : Continuous (adicCompletionComap K M v u) :=
    continuous_adicCompletionComap K M v u
  have := Continuous.ext_on (denseRange_algebraMap (R := A) (K := K) (v := v))
    hcont₁ hcont₂ ?_
  · exact congrFun this z
  · rintro _ ⟨k, rfl⟩
    show adicCompletionComap L M w u (adicCompletionComap K L v w ((k : K) : v.adicCompletion K))
        = adicCompletionComap K M v u ((k : K) : v.adicCompletion K)
    rw [adicCompletionComap_coe, adicCompletionComap_coe, adicCompletionComap_coe,
      ← IsScalarTower.algebraMap_apply K L M]

end Tower

end IsDedekindDomain.HeightOneSpectrum
