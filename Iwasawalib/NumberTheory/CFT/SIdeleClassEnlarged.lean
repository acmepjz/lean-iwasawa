/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.SIdeleClass

@[expose] public section

/-!
# Enlarging `S`: triviality of the `S`-class group, and `𝕀_L = L^× · 𝕀_{L,S}`

`Iwasawalib/NumberTheory/CFT/SIdeleClass.lean` proves `𝕀_L = L^× · 𝕀_{L,S}` for one particular
finite set of finite places, `S = NumberField.classPlaces L`, the support of a chosen family of
integral ideals representing the ideal classes.  Chevalley's proof of the first fundamental
inequality does not get to choose `S`: it must contain the places above `ℓ`, the places ramified
in `L/K`, and (after a base change) a `Gal(L/K)`-stable set — and *then* be enlarged until the
`S`-class group dies.

Everything in this file is the observation that `classPlaces` was never special: the only
property used is that the class of every divisor can be corrected, modulo principal divisors, to
one supported on `S`, and that property is inherited by every superset.  So all of the
`classPlaces`-statements upgrade, verbatim, to an arbitrary `S ⊇ classPlaces L`, and any finite
set of places may be enlarged to such an `S` while staying finite and (over a base field `K`)
`Gal(L/K)`-stable.

## Main statements

* `IsDedekindDomain.HeightOneSpectrum.exists_ord_eq_of_notMem_of_classRepSupport_subset` :
  **the `S`-class group is trivial**, in divisorial form — for `S ⊇ classRepSupport`, every
  finitely-supported divisor agrees off `S` with a principal one.
* `NumberField.exists_ord_eq_count_of_notMem` : the same in ideal-theoretic form — every nonzero
  fractional ideal agrees off `S` with a principal one, i.e. `Cl_S(L) = 1`.
* `NumberField.IdeleGroup.principalSubgroup_sup_sIdeleSubgroup_of_subset` :
  **`𝕀_L = L^× · 𝕀_{L,S}`** for every `S ⊇ classPlaces L`.
* `NumberField.sIdeleToClassOf_surjective`, `NumberField.mem_ker_sIdeleToClassOf_iff`,
  `NumberField.sIdeleQuotientEquivOf` : **`C_L ≅ 𝕀_{L,S} / O_{L,S}^×`** for every such `S`.
* `NumberField.exists_finite_superset_sIdeleSubgroup_sup` : every finite set of finite places of
  `L` is contained in a finite `S` with `𝕀_L = L^× · 𝕀_{L,S}`.
* `NumberField.exists_galois_stable_sIdeleSubgroup_sup_of_subset` : the same with `S` of the
  form `placesOverSet K L S₀` for a finite set `S₀` of places of `K`, hence `Gal(L/K)`-stable.
  This is the set `S` with which Chevalley's count starts.

## What is *not* here

Nothing in this file says anything about `n`-th powers; it only supplies the set `S`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] [Finite (ClassGroup R)]

/-- **Triviality of the `S`-class group, in divisorial form.**

If `S` contains the support `classRepSupport` of the chosen ideal class representatives, then
every finitely supported divisor agrees, outside `S`, with the divisor of a principal ideal.
Equivalently: the classes of the primes in `S` generate the ideal class group. -/
theorem exists_ord_eq_of_notMem_of_classRepSupport_subset
    {S : Set (HeightOneSpectrum R)} (hS : classRepSupport K (R := R) ⊆ S)
    (d : HeightOneSpectrum R → ℤ)
    (hd : ∀ᶠ w : HeightOneSpectrum R in Filter.cofinite, d w = 0) :
    ∃ x : Kˣ, ∀ w : HeightOneSpectrum R, w ∉ S → w.ord K (x : K) = d w := by
  obtain ⟨x, hx⟩ := exists_ord_eq_of_notMem_classRepSupport K d hd
  exact ⟨x, fun w hw ↦ hx w fun h ↦ hw (hS h)⟩

/-- **Triviality of the `S`-class group, in ideal-theoretic form.**

If `S ⊇ classRepSupport`, then every fractional ideal `I` agrees outside `S` with a principal
fractional ideal.  This is `Cl_S(R) = 1`. -/
theorem exists_ord_eq_count_of_notMem
    {S : Set (HeightOneSpectrum R)} (hS : classRepSupport K (R := R) ⊆ S)
    (I : FractionalIdeal R⁰ K) :
    ∃ x : Kˣ, ∀ w : HeightOneSpectrum R, w ∉ S →
      w.ord K (x : K) = FractionalIdeal.count K w I :=
  exists_ord_eq_of_notMem_of_classRepSupport_subset K hS _
    (Filter.eventually_cofinite.2 (by
      simpa using (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (K := K) I))))

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- **Triviality of the `S`-class group of a number field**, for any set `S` of finite places
containing `NumberField.classPlaces L`. -/
theorem exists_ord_eq_count_of_notMem {S : Set (HeightOneSpectrum (𝓞 L))}
    (hS : classPlaces L ⊆ S) (I : FractionalIdeal (𝓞 L)⁰ L) :
    ∃ x : Lˣ, ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      w.ord L (x : L) = FractionalIdeal.count L w I :=
  IsDedekindDomain.HeightOneSpectrum.exists_ord_eq_count_of_notMem L hS I

namespace FiniteAdeleRing

/-- **Every finite idele becomes an `S`-idele after multiplication by a principal idele**, for
any `S ⊇ classPlaces L`. -/
theorem exists_mul_unitEmbedding_mem_sIdeleSubgroup_of_subset
    {S : Set (HeightOneSpectrum (𝓞 L))} (hS : classPlaces L ⊆ S)
    (u : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    ∃ x : Lˣ, u * FiniteAdeleRing.unitEmbedding (𝓞 L) L x ∈ sIdeleSubgroup L S := by
  obtain ⟨x, hx⟩ := exists_mul_unitEmbedding_mem_sIdeleSubgroup u
  exact ⟨x, FiniteAdeleRing.sIdeleSubgroup_mono hS hx⟩

end FiniteAdeleRing

namespace IdeleGroup

/-- **Every idele becomes an `S`-idele after multiplication by a principal idele**, for any
`S ⊇ classPlaces L`. -/
theorem exists_mul_principalEmbedding_mem_sIdeleSubgroup_of_subset
    {S : Set (HeightOneSpectrum (𝓞 L))} (hS : classPlaces L ⊆ S) (u : IdeleGroup (𝓞 L) L) :
    ∃ x : Lˣ, u * IdeleGroup.principalEmbedding (𝓞 L) L x
      ∈ IdeleGroup.sIdeleSubgroup L S := by
  obtain ⟨x, hx⟩ := exists_mul_principalEmbedding_mem_sIdeleSubgroup u
  exact ⟨x, IdeleGroup.sIdeleSubgroup_mono hS hx⟩

/-- **`𝕀_L = L^× · 𝕀_{L,S}`** for every set `S` of finite places containing
`NumberField.classPlaces L`. -/
theorem principalSubgroup_sup_sIdeleSubgroup_of_subset
    {S : Set (HeightOneSpectrum (𝓞 L))} (hS : classPlaces L ⊆ S) :
    IdeleGroup.principalSubgroup (𝓞 L) L ⊔ IdeleGroup.sIdeleSubgroup L S = ⊤ :=
  eq_top_iff.2 (le_trans (le_of_eq principalSubgroup_sup_sIdeleSubgroup.symm)
    (sup_le_sup_left (IdeleGroup.sIdeleSubgroup_mono hS) _))

end IdeleGroup

/-! ## `C_L = 𝕀_{L,S} / O_{L,S}^×` for an arbitrary large `S` -/

variable (L) in
/-- The natural map `𝕀_{L,S} → C_L`, for an arbitrary set `S` of finite places. -/
def sIdeleToClassOf (S : Set (HeightOneSpectrum (𝓞 L))) :
    IdeleGroup.sIdeleSubgroup L S →* IdeleClassGroup (𝓞 L) L :=
  (IdeleClassGroup.mk (𝓞 L) L).comp (IdeleGroup.sIdeleSubgroup L S).subtype

@[simp]
theorem sIdeleToClassOf_apply {S : Set (HeightOneSpectrum (𝓞 L))}
    (u : IdeleGroup.sIdeleSubgroup L S) :
    sIdeleToClassOf L S u = IdeleClassGroup.mk (𝓞 L) L (u : IdeleGroup (𝓞 L) L) := rfl

/-- **`C_L = 𝕀_{L,S} / O_{L,S}^×`, surjectivity half**, for every `S ⊇ classPlaces L`. -/
theorem sIdeleToClassOf_surjective {S : Set (HeightOneSpectrum (𝓞 L))}
    (hS : classPlaces L ⊆ S) : Function.Surjective (sIdeleToClassOf L S) := by
  intro c
  obtain ⟨u, rfl⟩ := IdeleClassGroup.mk_surjective (𝓞 L) L c
  obtain ⟨x, hx⟩ :=
    IdeleGroup.exists_mul_principalEmbedding_mem_sIdeleSubgroup_of_subset hS u
  refine ⟨⟨u * IdeleGroup.principalEmbedding (𝓞 L) L x, hx⟩, ?_⟩
  rw [sIdeleToClassOf_apply, map_mul, IdeleClassGroup.mk_principalEmbedding, mul_one]

/-- **`C_L = 𝕀_{L,S} / O_{L,S}^×`, kernel half.**  Note that this half needs no hypothesis on
`S` at all: it is `L^× ∩ 𝕀_{L,S} = O_{L,S}^×`. -/
theorem mem_ker_sIdeleToClassOf_iff {S : Set (HeightOneSpectrum (𝓞 L))}
    (u : IdeleGroup.sIdeleSubgroup L S) :
    u ∈ (sIdeleToClassOf L S).ker ↔
      ∃ x : Lˣ, x ∈ S.unit L ∧
        IdeleGroup.principalEmbedding (𝓞 L) L x = (u : IdeleGroup (𝓞 L) L) := by
  rw [MonoidHom.mem_ker, sIdeleToClassOf_apply, IdeleClassGroup.mk_eq_one_iff]
  constructor
  · intro h
    have hmem : (u : IdeleGroup (𝓞 L) L) ∈
        IdeleGroup.principalSubgroup (𝓞 L) L ⊓ IdeleGroup.sIdeleSubgroup L S := ⟨h, u.2⟩
    rw [IdeleGroup.principalSubgroup_inf_sIdeleSubgroup] at hmem
    obtain ⟨x, hx, hxu⟩ := hmem
    exact ⟨x, hx, hxu⟩
  · rintro ⟨x, -, hxu⟩
    exact ⟨x, hxu⟩

/-- The kernel of `𝕀_{L,S} → C_L` is exactly the image of the `S`-units. -/
theorem ker_sIdeleToClassOf (S : Set (HeightOneSpectrum (𝓞 L))) :
    (sIdeleToClassOf L S).ker
      = ((S.unit L).map (IdeleGroup.principalEmbedding (𝓞 L) L)).comap
          (IdeleGroup.sIdeleSubgroup L S).subtype := by
  ext u
  rw [mem_ker_sIdeleToClassOf_iff, Subgroup.mem_comap]
  exact ⟨fun ⟨x, hx, hxu⟩ ↦ ⟨x, hx, hxu⟩, fun ⟨x, hx, hxu⟩ ↦ ⟨x, hx, hxu⟩⟩

variable (L) in
/-- **`C_L ≅ 𝕀_{L,S} / O_{L,S}^×`** for every `S ⊇ classPlaces L`. -/
def sIdeleQuotientEquivOf {S : Set (HeightOneSpectrum (𝓞 L))} (hS : classPlaces L ⊆ S) :
    (IdeleGroup.sIdeleSubgroup L S ⧸ (sIdeleToClassOf L S).ker)
      ≃* IdeleClassGroup (𝓞 L) L :=
  QuotientGroup.quotientKerEquivOfSurjective _ (sIdeleToClassOf_surjective hS)

/-! ## Choosing `S` -/

/-- **Any finite set of finite places may be enlarged, keeping it finite, until the `S`-ideles
surject onto the idele class group.**  The enlargement is by the finitely many places
`classPlaces L` supporting the chosen ideal class representatives. -/
theorem exists_finite_superset_sIdeleSubgroup_sup {S₀ : Set (HeightOneSpectrum (𝓞 L))}
    (hS₀ : S₀.Finite) :
    ∃ S : Set (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧ classPlaces L ⊆ S ∧ S.Finite ∧
      IdeleGroup.principalSubgroup (𝓞 L) L ⊔ IdeleGroup.sIdeleSubgroup L S = ⊤ :=
  ⟨S₀ ∪ classPlaces L, Set.subset_union_left, Set.subset_union_right,
    hS₀.union finite_classPlaces,
    IdeleGroup.principalSubgroup_sup_sIdeleSubgroup_of_subset Set.subset_union_right⟩

section GaloisStable

variable {K : Type*} [Field K] [NumberField K] [Algebra K L]

variable (K L) in
/-- **The set `S` with which Chevalley's count starts.**

Any finite set `S₀` of finite places of `L` is contained in a set of the form
`placesOverSet K L S` for a finite set `S` of finite places of `K` — hence in a finite,
`Gal(L/K)`-stable set of places of `L` — which moreover contains `classPlaces L`, so that
`𝕀_L = L^× · 𝕀_{L, placesOverSet K L S}`.

In the application, `S₀` is the set of places above `ℓ` together with the places ramified in the
extension; the conclusion supplies the enlargement that kills the `S`-class group. -/
theorem exists_galois_stable_sIdeleSubgroup_sup_of_subset
    {S₀ : Set (HeightOneSpectrum (𝓞 L))} (hS₀ : S₀.Finite) :
    ∃ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite ∧ (placesOverSet K L S).Finite ∧
      S₀ ⊆ placesOverSet K L S ∧ classPlaces L ⊆ placesOverSet K L S ∧
      IdeleGroup.principalSubgroup (𝓞 L) L ⊔
        IdeleGroup.sIdeleSubgroup L (placesOverSet K L S) = ⊤ := by
  obtain ⟨S, hSfin, hsub, hfin⟩ :=
    exists_finite_subset_placesOverSet (K := K) (L := L) (hS₀.union finite_classPlaces)
  refine ⟨S, hSfin, hfin, (Set.subset_union_left).trans hsub,
    (Set.subset_union_right).trans hsub, ?_⟩
  exact IdeleGroup.principalSubgroup_sup_sIdeleSubgroup_of_subset
    ((Set.subset_union_right).trans hsub)

end GaloisStable

end NumberField
