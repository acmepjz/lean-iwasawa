/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.IdeleClassNormQuotient
public import Iwasawalib.NumberTheory.CFT.SecondInequality

@[expose] public section

/-!
# Artin reciprocity for a cyclic extension: from an order to the canonical isomorphism

For a **cyclic** extension `L / K` of number fields, Tate cohomology is two-periodic and
`Ĥ⁰(Gal(L/K), C_L)` *is* `Ĥ²(Gal(L/K), C_L)` — in the model of
`Iwasawalib/GroupCohomology/CyclicTate.lean` they are literally the same group, so the
periodicity isomorphism of Tate's theorem costs nothing here and no cup product is needed.
What Tate's theorem still has to provide is a **canonical map**

`C_K / N_{L/K} C_L = Ĥ⁰(Gal(L/K), C_L) ⟶ Gal(L/K)`.

This file shows that once such a map exists as a homomorphism `ρ : C_K → Gal(L/K)` killing
norms, the *order* computations this library already contains promote it to an isomorphism, and
that this needs only one of the two fundamental inequalities — whichever one points against the
direction in which `ρ` is known to be one-sided:

* if `ρ` is **surjective** (global class field theory: the Frobenius elements generate the
  Galois group), then `#Ĥ⁰ ≥ [L : K]` is automatic and the *first* inequality `#Ĥ⁰ ≤ [L : K]`
  finishes — `NumberField.reciprocityEquivOfSurjective`;
* if the induced map is **injective** (the Hasse norm theorem: a global element that is a local
  norm everywhere is a norm), then the *second* inequality
  `NumberField.card_tateH0_ideleClassGroup_ge`, which this repository proves, finishes —
  `NumberField.reciprocityEquivOfInjective`.

The module docstring of `Iwasawalib/NumberTheory/GlobalCFT/ArtinMap.lean` says that passing
from the cardinality to the canonical isomorphism "is Tate's theorem, which needs the
fundamental class and cup products".  For a cyclic extension that is not so: the content below
is the two-line argument that a surjection between finite groups of the same order is
bijective, applied to the norm quotient.  What genuinely remains missing is the *existence* of
`ρ`, i.e. the reciprocity law itself, which is the hypothesis of every statement here.

## Main definitions and statements

* `NumberField.artinTateH0` : the map `Ĥ⁰(Gal(L/K), C_L) → Gal(L/K)` induced by a homomorphism
  `ρ : C_K → Gal(L/K)` that kills `N_{L/K} C_L`, with `NumberField.artinTateH0_toTateH0`
  computing it on the class of an element of `C_K`.
* `NumberField.reciprocityEquivOfSurjective`, `NumberField.reciprocityEquivOfInjective` :
  `Ĥ⁰(Gal(L/K), C_L) ≃+ Additive Gal(L/K)`.
* `NumberField.quotientNormEquivGalOfSurjective` : the same isomorphism read as
  `C_K / N_{L/K} C_L ≅ Gal(L/K)`.
* `NumberField.reciprocityEquivOfSurjective` : the version whose only analytic
  input is `Ĥ¹(Gal(L/K), C_L) = 0`, packaged against
  `NumberField.card_tateH0_ideleClassGroup_eq_of_subsingleton`.
-/

noncomputable section

open IsDedekindDomain CyclicTate NumberField.IdeleClassGroup

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.galIdeleMulDistribMulAction NumberField.galIdeleClassMulDistribMulAction
  CyclicTate.Additive.distribMulActionOfMulDistrib

namespace NumberField

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L] {σ : L ≃ₐ[K] L}
  (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
  (ρ : IdeleClassGroup (𝓞 K) K →* (L ≃ₐ[K] L))

/-- **A reciprocity map kills norms**: the hypothesis under which `ρ : C_K → Gal(L/K)` descends
to the norm quotient.  It is stated additively because `Ĥ⁰` is an additive quotient. -/
def KillsNorms : Prop :=
  ∀ c ∈ normSubgroup K L, ρ (Additive.toMul c) = 1

variable (hnorm : KillsNorms ρ (L := L))

include hgen hnorm

/-- **The map `Ĥ⁰(Gal(L/K), C_L) → Gal(L/K)` induced by a reciprocity map on `C_K`.**

`Iwasawalib/NumberTheory/CFT/IdeleClassNormQuotient.lean` identifies `Ĥ⁰(Gal(L/K), C_L)` with
`C_K / N_{L/K} C_L`, so a homomorphism on `C_K` killing norms descends to it, uniquely. -/
def artinTateH0 : TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ →+
    Additive (L ≃ₐ[K] L) :=
  (QuotientAddGroup.lift (normSubgroup K L) ρ.toAdditive hnorm).comp
    (quotientNormEquivTateH0 hgen).symm.toAddMonoidHom

/-- **The induced map sends the class of `c ∈ C_K` to `ρ c`.** -/
@[simp] theorem artinTateH0_toTateH0 (c : Additive (IdeleClassGroup (𝓞 K) K)) :
    artinTateH0 hgen ρ hnorm (toTateH0 hgen c) = Additive.ofMul (ρ (Additive.toMul c)) := by
  rw [artinTateH0, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    show (quotientNormEquivTateH0 hgen).symm (toTateH0 hgen c) = QuotientAddGroup.mk c from
      (AddEquiv.symm_apply_eq _).2 (quotientNormEquivTateH0_mk hgen c).symm]
  rfl

/-- **The induced map is surjective as soon as `ρ` is.** -/
theorem surjective_artinTateH0 (hsurj : Function.Surjective ρ) :
    Function.Surjective (artinTateH0 hgen ρ hnorm) := by
  intro g
  obtain ⟨c, hc⟩ := hsurj (Additive.toMul g)
  exact ⟨toTateH0 hgen (Additive.ofMul c), by rw [artinTateH0_toTateH0]; exact congrArg _ hc⟩

/-- **A surjective reciprocity map is an isomorphism once `#Ĥ⁰(Gal(L/K), C_L) = [L : K]`.**

This is the whole of Tate's theorem in the cyclic case: no cup product, no fundamental class,
no Brauer–Hasse–Noether.  The count is the first fundamental inequality
(`NumberField.card_tateH0_ideleClassGroup_eq_of_subsingleton`); the surjectivity is the
statement that the Frobenius elements generate `Gal(L/K)`. -/
def reciprocityEquivOfSurjective (hsurj : Function.Surjective ρ)
    (hcard : Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      = Nat.card (L ≃ₐ[K] L)) :
    TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ ≃+ Additive (L ≃ₐ[K] L) :=
  AddEquiv.ofSurjectiveOfCardEq _ (surjective_artinTateH0 hgen ρ hnorm hsurj)
    (hcard.trans (Nat.card_eq_of_bijective _ (Additive.ofMul (α := L ≃ₐ[K] L)).bijective))

@[simp] theorem reciprocityEquivOfSurjective_apply (hsurj : Function.Surjective ρ)
    (hcard : Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      = Nat.card (L ≃ₐ[K] L))
    (t : TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ) :
    reciprocityEquivOfSurjective hgen ρ hnorm hsurj hcard t = artinTateH0 hgen ρ hnorm t := rfl

/-- **An injective reciprocity map is an isomorphism once `#Ĥ⁰(Gal(L/K), C_L) = [L : K]`.**  The
count here may be supplied by the *second* fundamental inequality
`NumberField.card_tateH0_ideleClassGroup_ge` together with the injectivity, which is the Hasse
norm theorem. -/
def reciprocityEquivOfInjective (hinj : Function.Injective (artinTateH0 hgen ρ hnorm))
    (hcard : Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      = Nat.card (L ≃ₐ[K] L)) :
    TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ ≃+ Additive (L ≃ₐ[K] L) :=
  AddEquiv.ofInjectiveOfCardEq _ hinj
    (hcard.trans (Nat.card_eq_of_bijective _ (Additive.ofMul (α := L ≃ₐ[K] L)).bijective))

@[simp] theorem reciprocityEquivOfInjective_apply
    (hinj : Function.Injective (artinTateH0 hgen ρ hnorm))
    (hcard : Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      = Nat.card (L ≃ₐ[K] L))
    (t : TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ) :
    reciprocityEquivOfInjective hgen ρ hnorm hinj hcard t = artinTateH0 hgen ρ hnorm t := rfl

/-- **An injective reciprocity map is an isomorphism once `#Ĥ⁰(Gal(L/K), C_L) ≥ [L : K]`.**

Injectivity gives `#Ĥ⁰ ≤ [L : K]`, so the *second* fundamental inequality — which this
repository proves, `NumberField.card_tateH0_ideleClassGroup_ge` — is enough, and the first
inequality is not needed at all. -/
def reciprocityEquivOfInjectiveOfGe (hinj : Function.Injective (artinTateH0 hgen ρ hnorm))
    (hge : Nat.card (L ≃ₐ[K] L)
      ≤ Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)) :
    TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ ≃+ Additive (L ≃ₐ[K] L) :=
  reciprocityEquivOfInjective hgen ρ hnorm hinj (le_antisymm
    (by
      exact (Nat.card_le_card_of_injective _ hinj).trans_eq
        (Nat.card_eq_of_bijective _ (Additive.toMul (α := L ≃ₐ[K] L)).bijective))
    hge)

/-- **`C_K / N_{L/K} C_L ≅ Gal(L/K)`**, the reciprocity isomorphism in its classical form,
granted a surjective reciprocity map and the order computation. -/
def quotientNormEquivGalOfSurjective (hsurj : Function.Surjective ρ)
    (hcard : Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      = Nat.card (L ≃ₐ[K] L)) :
    (Additive (IdeleClassGroup (𝓞 K) K) ⧸ normSubgroup K L) ≃+ Additive (L ≃ₐ[K] L) :=
  (quotientNormEquivTateH0 hgen).trans (reciprocityEquivOfSurjective hgen ρ hnorm hsurj hcard)

@[simp] theorem quotientNormEquivGalOfSurjective_mk (hsurj : Function.Surjective ρ)
    (hcard : Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      = Nat.card (L ≃ₐ[K] L)) (c : Additive (IdeleClassGroup (𝓞 K) K)) :
    quotientNormEquivGalOfSurjective hgen ρ hnorm hsurj hcard (QuotientAddGroup.mk c)
      = Additive.ofMul (ρ (Additive.toMul c)) := by
  rw [quotientNormEquivGalOfSurjective, AddEquiv.trans_apply, quotientNormEquivTateH0_mk,
    reciprocityEquivOfSurjective_apply, artinTateH0_toTateH0]

/-- **`C_K / N_{L/K} C_L ≅ Gal(L/K)` as multiplicative groups.** -/
def quotientNormMulEquivGalOfSurjective (hsurj : Function.Surjective ρ)
    (hcard : Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      = Nat.card (L ≃ₐ[K] L)) :
    Multiplicative (Additive (IdeleClassGroup (𝓞 K) K) ⧸ normSubgroup K L) ≃* (L ≃ₐ[K] L) :=
  AddEquiv.toMultiplicativeLeft (quotientNormEquivGalOfSurjective hgen ρ hnorm hsurj hcard)

end NumberField
