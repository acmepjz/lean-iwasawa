/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.Group.Units

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

/-!
# The idele group and the idele class group of a number field

This file defines the idele group `𝕀_K = (𝔸_K)ˣ` of a number field `K` (more generally, of
the fraction field of a Dedekind domain `R`), the embedding of the principal ideles
`Kˣ → 𝕀_K`, and the idele class group `C_K = 𝕀_K / Kˣ`.

Mathlib's `NumberField.AdeleRing.principalSubgroup` is the *additive* subgroup of principal
adeles; here we build the multiplicative analogue, which is what class field theory needs.

## Main definitions

* `NumberField.IdeleGroup R K` : the group of ideles, `(AdeleRing R K)ˣ`.
* `NumberField.IdeleGroup.principalEmbedding R K : Kˣ →* IdeleGroup R K`.
* `NumberField.IdeleGroup.principalSubgroup R K : Subgroup (IdeleGroup R K)`.
* `NumberField.IdeleClassGroup R K` : the idele class group `𝕀_K ⧸ Kˣ`.
-/

noncomputable section

namespace NumberField

open IsDedekindDomain

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-! ## The idele group -/


namespace IdeleGroup

instance : CommGroup (IdeleGroup R K) := inferInstance

instance : IsTopologicalGroup (IdeleGroup R K) := inferInstance

/-- The embedding of the principal ideles `Kˣ → 𝕀_K`, `x ↦ (x)ᵥ`. -/
abbrev principalEmbedding : Kˣ →* IdeleGroup R K := unitEmbedding R K

@[simp]
theorem coe_principalEmbedding (x : Kˣ) :
    (principalEmbedding R K x : AdeleRing R K) = algebraMap K (AdeleRing R K) (x : K) := rfl

@[simp]
theorem principalEmbedding_apply_fst_apply (x : Kˣ) (v : InfinitePlace K) :
    ((principalEmbedding R K x : AdeleRing R K)).1 v = (x : K) := rfl

@[simp]
theorem principalEmbedding_apply_snd_apply (x : Kˣ) (v : HeightOneSpectrum R) :
    ((principalEmbedding R K x : AdeleRing R K)).2 v = (x : K) := rfl

theorem principalEmbedding_injective [NumberField K] :
    Function.Injective (principalEmbedding R K) := by
  intro x y h
  have : algebraMap K (AdeleRing R K) (x : K) = algebraMap K (AdeleRing R K) (y : K) := by
    simpa using congrArg (fun u : IdeleGroup R K ↦ (u : AdeleRing R K)) h
  exact Units.ext (AdeleRing.algebraMap_injective R K this)


theorem mem_principalSubgroup {u : IdeleGroup R K} :
    u ∈ principalSubgroup R K ↔ ∃ x : Kˣ, principalEmbedding R K x = u := Iff.rfl

instance : (principalSubgroup R K).Normal := Subgroup.normal_of_isMulCommutative _

/-- `Kˣ` is isomorphic to the group of principal ideles. -/
def principalEmbeddingRangeEquiv [NumberField K] : Kˣ ≃* principalSubgroup R K :=
  MonoidHom.ofInjective (principalEmbedding_injective R K)

end IdeleGroup

/-! ## The idele class group -/


namespace IdeleClassGroup

instance : CommGroup (IdeleClassGroup R K) := inferInstance

/-- The quotient map from the ideles to the idele class group. -/
abbrev mk : IdeleGroup R K →* IdeleClassGroup R K := QuotientGroup.mk' _

theorem mk_surjective : Function.Surjective (mk R K) := Quotient.mk_surjective

@[simp]
theorem ker_mk : (mk R K).ker = IdeleGroup.principalSubgroup R K :=
  QuotientGroup.ker_mk' _

theorem mk_eq_one_iff {u : IdeleGroup R K} :
    mk R K u = 1 ↔ u ∈ IdeleGroup.principalSubgroup R K := by
  rw [← MonoidHom.mem_ker, ker_mk]

@[simp]
theorem mk_principalEmbedding (x : Kˣ) : mk R K (IdeleGroup.principalEmbedding R K x) = 1 :=
  (mk_eq_one_iff R K).2 ⟨x, rfl⟩

/-- The defining exact sequence `Kˣ → 𝕀_K → C_K`. -/
theorem range_principalEmbedding_eq_ker_mk :
    (IdeleGroup.principalEmbedding R K).range = (mk R K).ker := (ker_mk R K).symm

theorem mk_eq_mk_iff {u w : IdeleGroup R K} :
    mk R K u = mk R K w ↔ ∃ x : Kˣ, IdeleGroup.principalEmbedding R K x * u = w := by
  rw [QuotientGroup.mk'_eq_mk']
  simp only [IdeleGroup.principalSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, mul_comm _ _⟩
  · rintro ⟨x, rfl⟩; exact ⟨_, ⟨x, rfl⟩, mul_comm _ _⟩

end IdeleClassGroup

end NumberField
