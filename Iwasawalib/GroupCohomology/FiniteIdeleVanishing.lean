/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.IdeleVanishing
public import Iwasawalib.GroupCohomology.SubgroupIdele
public import Iwasawalib.GroupCohomology.LocalHilbert90
public import Iwasawalib.GroupCohomology.RestrictedProductVanishing
public import Iwasawalib.NumberTheory.CFT.FiniteAdeleSemilocal
public import Mathlib.Topology.Algebra.RestrictedProduct.Units

@[expose] public section

/-!
# The finite ideles as a restricted product, and `H¹`

The finite adele ring of `L` is, `Gal(L/K)`-equivariantly, the restricted product over the
finite places `v` of `K` of the semilocal factors `∏_{w ∣ v} L_w` with respect to
`∏_{w ∣ v} O_w` (`NumberField.semilocalFiniteEquiv`).  Taking units, the finite ideles are the
restricted product of the `(∏_{w ∣ v} L_w)^×` with respect to the `(∏_{w ∣ v} O_w)^×`.

`Iwasawalib/GroupCohomology/RestrictedProductVanishing.lean` computes `H¹` of such a restricted
product, and `Iwasawalib/GroupCohomology/LocalHilbert90.lean` supplies the vanishing for every
individual factor.  What remains is the statement at almost every place
(`NumberField.IsUnramifiedAlmostEverywhere`): a 1-cocycle with values in `(∏_{w ∣ v} O_w)^×`
must be trivialised inside `(∏_{w ∣ v} O_w)^×`.  By Shapiro this is `H¹(D_w, O_w^×) = 0` at the
unramified places.  This file takes that statement as a hypothesis; it is proved, for every
finite Galois extension `L / K`, in `Iwasawalib/GroupCohomology/UnramifiedIdele.lean`
(`NumberField.isUnramifiedAlmostEverywhere`), which also records the resulting unconditional
`H¹(Gal(L/K), 𝕀_L) = 0` (`NumberField.isZero_H1_repIdele`).

## Main definitions

* `NumberField.SemilocalIdeleGroup`: the restricted product
  `Πʳ v, [(∏_{w ∣ v} L_w)^×, (∏_{w ∣ v} O_w)^×]`.
* `NumberField.finiteIdeleEquivSemilocal`: `(𝔸_L^f)^× ≃* SemilocalIdeleGroup`.

## Main statements

* `NumberField.nonempty_placesOver`: every finite place of `K` has a place of `L` above it.
* `NumberField.smul_mem_localProductIntegers`: the Galois action preserves `∏_{w ∣ v} O_w`.
* `NumberField.isZero_H1_finiteIdele_of`: `H¹(Gal(L/K), (𝔸_L^f)^×) = 0` given the local
  statement at almost every place.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Filter
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.galIdeleMulDistribMulAction NumberField.galIdeleClassMulDistribMulAction

namespace NumberField

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-! ## Every finite place of `K` has a place above it -/

omit [NumberField K] [NumberField L] in
theorem algebraMap_ringOfIntegers_injective :
    Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
  FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)

omit [NumberField K] [NumberField L] in
/-- Every finite place of `K` has at least one finite place of `L` above it. -/
theorem nonempty_placesOver (v : HeightOneSpectrum (𝓞 K)) : (placesOver K L v).Nonempty := by
  have hker : RingHom.ker (algebraMap (𝓞 K) (𝓞 L)) ≤ v.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap_ringOfIntegers_injective (K := K)
      (L := L))]
    exact bot_le
  obtain ⟨Q, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := 𝓞 L) v.asIdeal hker
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    rw [Ideal.comap_bot_of_injective _ (algebraMap_ringOfIntegers_injective (K := K) (L := L))]
      at hQ
    exact v.ne_bot hQ.symm
  exact ⟨⟨Q, hQp, hQ0⟩, hQ⟩

/-! ## The Galois action preserves the local integers -/

omit [NumberField K] in
/-- The Galois action on `∏_{w ∣ v} L_w` preserves the subring `∏_{w ∣ v} O_w`. -/
theorem smul_mem_localProductIntegers {v : HeightOneSpectrum (𝓞 K)} (σ : L ≃ₐ[K] L)
    {x : LocalProduct K L v} (hx : x ∈ localProductIntegers K L v) :
    σ • x ∈ localProductIntegers K L v := by
  intro w
  rw [localProduct_smul_apply]
  exact adicCompletionCongr_mapsTo_integers _ _ _ _ (hx (invSmulPlace σ w))

variable (K L)

/-- The subgroup `(∏_{w ∣ v} O_w)^×` of `(∏_{w ∣ v} L_w)^×`. -/
abbrev localProductIntegerUnits (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (LocalProduct K L v)ˣ :=
  (Submonoid.ofClass (localProductIntegers K L v)).units

variable {K L}

omit [NumberField K] in
/-- The Galois action preserves the local integral units. -/
theorem smul_mem_localProductIntegerUnits {v : HeightOneSpectrum (𝓞 K)} (σ : L ≃ₐ[K] L)
    {u : (LocalProduct K L v)ˣ} (hu : u ∈ localProductIntegerUnits K L v) :
    σ • u ∈ localProductIntegerUnits K L v :=
  ⟨smul_mem_localProductIntegers σ hu.1, smul_mem_localProductIntegers σ hu.2⟩

variable (K L)

/-- The finite ideles in the semilocal picture: the restricted product over the finite places
`v` of `K` of `(∏_{w ∣ v} L_w)^×` with respect to `(∏_{w ∣ v} O_w)^×`. -/
abbrev SemilocalIdeleGroup : Type :=
  Πʳ v : HeightOneSpectrum (𝓞 K),
    [(LocalProduct K L v)ˣ, localProductIntegerUnits K L v]

/-- The factorwise `Gal(L/K)`-action on the semilocal ideles. -/
@[instance_reducible] def semilocalIdeleMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (SemilocalIdeleGroup K L) :=
  RestrictedProduct.mulDistribMulAction fun _ σ {_} hu ↦
    smul_mem_localProductIntegerUnits σ hu

attribute [local instance] semilocalIdeleMulDistribMulAction

omit [NumberField K] in
theorem semilocalIdele_isFactorwise :
    RestrictedProduct.IsFactorwise (G := L ≃ₐ[K] L)
      (N := localProductIntegerUnits K L) :=
  fun _ _ _ ↦ rfl

/-! ## The remaining local input -/


/-- **The local input at almost every place.**  For almost every finite place `v` of `K`, a
multiplicative 1-cocycle `Gal(L/K) → (∏_{w ∣ v} L_w)^×` whose values are integral units is a
1-coboundary *with an integral unit as witness*.

By Shapiro's lemma this says `H¹(D_w, O_w^×) = 0` for almost every `w`, which is the standard
statement that `H¹` of the units of the ring of integers vanishes at the unramified places.
It is the one arithmetic ingredient of `H¹(Gal(L/K), 𝕀_L) = 0` which is not proved in this
file.  It is proved, for every finite Galois extension `L / K`, as
`NumberField.isUnramifiedAlmostEverywhere` in `Iwasawalib/GroupCohomology/UnramifiedIdele.lean`,
a file which imports this one. -/
def IsUnramifiedAlmostEverywhere : Prop :=
  ∀ᶠ v in cofinite, ∀ f : (L ≃ₐ[K] L) → (LocalProduct K L v)ˣ,
    groupCohomology.IsMulCocycle₁ f → (∀ g, f g ∈ localProductIntegerUnits K L v) →
    ∃ b ∈ localProductIntegerUnits K L v, ∀ g, g • b / b = f g


/-! ## The finite ideles are the semilocal restricted product -/

variable [IsGalois K L]

/-- `H¹(Gal(L/K), (∏_{w ∣ v} L_w)^×) = 0`, as an `IsZero` statement. -/
theorem isZero_H1_repLocalProductUnits (v : HeightOneSpectrum (𝓞 K)) :
    IsZero (groupCohomology (repLocalProductUnits K L v) 1) := by
  obtain ⟨w₀, hw₀⟩ := nonempty_placesOver (K := K) (L := L) v
  have : Subsingleton (groupCohomology (repLocalProductUnits K L v) 1) :=
    ⟨fun x y ↦ by
      rw [H1_localProductUnits_eq_zero hw₀ x, H1_localProductUnits_eq_zero hw₀ y]⟩
  exact ModuleCat.isZero_of_subsingleton _

omit [IsGalois K L] in
/-- **The finite ideles are the restricted product of the semilocal unit groups.** -/
def finiteIdeleEquivSemilocal :
    (FiniteAdeleRing (𝓞 L) L)ˣ ≃* SemilocalIdeleGroup K L :=
  (Units.mapEquiv (semilocalFiniteEquiv K L).toMulEquiv).trans
    (RestrictedProduct.unitsEquiv (LocalProduct K L))

omit [IsGalois K L] in
theorem finiteIdeleEquivSemilocal_smul (σ : L ≃ₐ[K] L) (u : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    finiteIdeleEquivSemilocal K L (σ • u) = σ • finiteIdeleEquivSemilocal K L u := by
  refine Subtype.ext (funext fun v ↦ Units.ext ?_)
  exact semilocalFiniteEquiv_smul σ _ v

/-- **`H¹` of the finite ideles**, given the local statement at almost every place.  Together
with `NumberField.isZero_H1_infiniteIdele` this is `H¹(Gal(L/K), 𝕀_L) = 0`.

The hypothesis is the arithmetic input which is not proved in this file: for almost every
finite place `v` of `K`, a 1-cocycle with values in the integral units `(∏_{w ∣ v} O_w)^×` is
trivialised by an integral unit.  By Shapiro's lemma this is `H¹(D_w, O_w^×) = 0`, which holds
at the unramified places, i.e. at all but finitely many.  It is discharged by
`NumberField.isUnramifiedAlmostEverywhere`, giving the unconditional
`NumberField.isZero_H1_finiteIdele` (both in `Iwasawalib/GroupCohomology/UnramifiedIdele.lean`). -/
theorem isZero_H1_finiteIdele_of (hb : IsUnramifiedAlmostEverywhere K L) :
    IsZero (groupCohomology
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (FiniteAdeleRing (𝓞 L) L)ˣ) 1) :=
  groupCohomology.isZero_H1_of_mulEquiv (finiteIdeleEquivSemilocal K L)
    (finiteIdeleEquivSemilocal_smul K L)
    (RestrictedProduct.isZero_H1 (semilocalIdele_isFactorwise K L)
      (isZero_H1_repLocalProductUnits K L) hb)

/-- **`H¹(Gal(L/K), 𝕀_L) = 0`**, given the local statement at almost every place. -/
theorem isZero_H1_repIdele_of (hb : IsUnramifiedAlmostEverywhere K L) :
    IsZero (groupCohomology (repIdele K L) 1) :=
  (isZero_H1_repIdele_iff K L).2 (isZero_H1_finiteIdele_of K L hb)

/-! ## The first axiom of a class formation -/

/-- **`H¹(Gal(L/K), C_L) = 0`**, given two inputs of global class field theory: the local
statement at almost every place, and the injectivity of
`H²(Gal(L/K), Lˣ) ⟶ H²(Gal(L/K), 𝕀_L)`.

The first input is proved (`NumberField.isUnramifiedAlmostEverywhere`), and
`NumberField.isZero_H1_repIdeleClass` is this statement with it discharged.  The second is the
Hasse principle for the Brauer group (`NumberField.BrauerHassePrinciple`), which is not proved
in this repository. -/
theorem isZero_H1_repIdeleClass_of' (hb : IsUnramifiedAlmostEverywhere K L)
    (hmono : Mono ((groupCohomology.functor ℤ (L ≃ₐ[K] L) 2).map
      (ideleShortComplex K L).f)) :
    IsZero (groupCohomology (repIdeleClass K L) 1) :=
  isZero_H1_repIdeleClass_of K L (isZero_H1_repIdele_of K L hb) hmono

/-- **`H¹(H, 𝕀_L) = 0` for a subgroup `H ≤ Gal(L/K)`**, given the local statement at almost
every place of the fixed field `L^H`. -/
theorem isZero_H1_subgroup_repIdele_of (H : Subgroup (L ≃ₐ[K] L))
    (hb : IsUnramifiedAlmostEverywhere (IntermediateField.fixedField H) L) :
    IsZero (groupCohomology
      (Rep.ofMulDistribMulAction H (IdeleGroup (𝓞 L) L)) 1) :=
  (isZero_H1_repIdele_of _ _ hb).of_iso (subgroupIdeleIso H 1)

/-- **`H¹(H, C_L) = 0` for a subgroup `H ≤ Gal(L/K)`**, given the same two inputs taken over
the fixed field `L^H`.  As for `NumberField.isZero_H1_repIdeleClass_of'`, the first is proved
(`NumberField.isUnramifiedAlmostEverywhere`) and only the injectivity on `H²` is still
unproved. -/
theorem isZero_H1_subgroup_repIdeleClass_of' (H : Subgroup (L ≃ₐ[K] L))
    (hb : IsUnramifiedAlmostEverywhere (IntermediateField.fixedField H) L)
    (hmono : Mono ((groupCohomology.functor ℤ
      (L ≃ₐ[IntermediateField.fixedField H] L) 2).map
        (ideleShortComplex (IntermediateField.fixedField H) L).f)) :
    IsZero (groupCohomology
      (Rep.ofMulDistribMulAction H (IdeleClassGroup (𝓞 L) L)) 1) :=
  isZero_H1_subgroup_repIdeleClass_of H (isZero_H1_repIdele_of _ _ hb) hmono

end NumberField
