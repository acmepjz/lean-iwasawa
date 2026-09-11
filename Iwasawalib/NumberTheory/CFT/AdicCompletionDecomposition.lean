/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.FiniteAdeleBaseChange

@[expose] public section

/-!
# The decomposition group acts `K_v`-linearly on `L_w`

For a finite place `w` of `L` lying over the finite place `v` of `K`, the decomposition group
`D_w = Stab_{Gal(L/K)}(w)` acts on the completion `L_w` by
`NumberField.decompositionRingAut`.  This file proves that this action fixes the image of
`K_v` under the local base change map, i.e. that `K_v ⊆ L_w^{D_w}`.

This is the local shadow of the inclusion `𝔸_K ⊆ (𝔸_L)^{Gal(L/K)}`.  The *reverse* inclusion
`L_w^{D_w} ⊆ K_v` is not proved here: for a Galois extension it is the statement that
`Gal(L_w/K_v)` is the image of `D_w`, which is Galois theory of complete discretely valued
fields and is not available in Mathlib at the time of writing.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.exists_under_eq` : every height one prime of `A` has a
  height one prime of `B` above it.
* `IsDedekindDomain.HeightOneSpectrum.valued_adicCompletionComap_of_ramificationIdx_eq_one` :
  at an unramified place the local base change preserves valuations exactly.
* `NumberField.decomposition_smul_adicCompletionComap`,
  `NumberField.range_adicCompletionComap_le_fixedPoints` : `K_v ⊆ L_w^{D_w}`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

/-! ## Existence of a prime above a given prime -/

section Exists

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Algebra.IsIntegral A B] [FaithfulSMul A B]

/-- Every height one prime of `A` has a height one prime of `B` above it. -/
theorem exists_under_eq (v : HeightOneSpectrum A) : ∃ w : HeightOneSpectrum B, w.under A = v := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  obtain ⟨⟨Q, hQp, hQo⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver B))
  haveI := hQp
  haveI := hQo
  have hQbot : Q ≠ ⊥ := by
    intro h
    refine v.ne_bot ?_
    have hv : v.asIdeal = Q.under A := Ideal.over_def Q v.asIdeal
    rw [hv, h, Ideal.under_bot]
  exact ⟨⟨Q, hQp, hQbot⟩, HeightOneSpectrum.ext (Ideal.over_def Q v.asIdeal).symm⟩

theorem under_surjective : Function.Surjective (fun w : HeightOneSpectrum B ↦ w.under A) :=
  fun v ↦ exists_under_eq v

end Exists

/-! ## The unramified case -/

section Unramified

variable {A B : Type*} (K L : Type*)
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

/-- At a place with ramification index one the local base change preserves the valuation
exactly, so it is an isometric embedding `K_v → L_w`. -/
theorem valued_adicCompletionComap_of_ramificationIdx_eq_one
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1) (x : v.adicCompletion K) :
    (Valued.v (adicCompletionComap K L v w x) : ℤᵐ⁰) = Valued.v x := by
  rw [valued_adicCompletionComap, h, pow_one]

/-- The local base change carries the maximal ideal of `O_v` into the maximal ideal
of `O_w`. -/
theorem valued_adicCompletionComap_lt_one {x : v.adicCompletion K}
    (hx : (Valued.v x : ℤᵐ⁰) < 1)
    (he : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0) :
    (Valued.v (adicCompletionComap K L v w x) : ℤᵐ⁰) < 1 := by
  rw [valued_adicCompletionComap]
  exact pow_lt_one₀ zero_le hx he

end Unramified

end IsDedekindDomain.HeightOneSpectrum

/-! ## `K_v` lies in the `D_w`-invariants of `L_w` -/

namespace NumberField

open IsDedekindDomain.FiniteAdeleRing

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- **The decomposition group acts `K_v`-linearly.**  Every element of `D_w` fixes the image
of `K_v` in `L_w` pointwise. -/
theorem decomposition_smul_adicCompletionComap (d : decompositionGroup K L w)
    (z : v.adicCompletion K) :
    d • adicCompletionComap K L v w z = adicCompletionComap K L v w z := by
  rw [decomposition_smul_def]
  exact adicCompletionCongr_adicCompletionComap K L ((d : L ≃ₐ[K] L) : L ≃+* L)
    (fun k ↦ (d : L ≃ₐ[K] L).commutes k) v w w (valuation_of_mem_decompositionGroup d) z

/-- **`K_v ⊆ L_w^{D_w}`.**  The image of the local base change lies in the subring of `L_w`
fixed by the decomposition group of `w`.

The reverse inclusion is local class field theory / Galois theory of complete local fields,
and is not proved here. -/
theorem range_adicCompletionComap_le_fixedPoints :
    (adicCompletionComap K L v w).range ≤
      FixedPoints.subring (w.adicCompletion L) (decompositionGroup K L w) := by
  rintro _ ⟨z, rfl⟩ d
  exact decomposition_smul_adicCompletionComap v w d z

end NumberField
