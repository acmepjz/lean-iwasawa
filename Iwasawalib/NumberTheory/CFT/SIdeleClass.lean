/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.SUnitDivisor

@[expose] public section

/-!
# `S`-ideles and the idele class group

This file proves the statement `𝕀_L = L^× · 𝕀_{L,S}` for a suitable finite set `S` of finite
places of `L`, and deduces `C_L ≅ 𝕀_{L,S} / O_{L,S}^×`.

The set `S` is `NumberField.classPlaces L`: the (finite) set of finite places dividing one of a
chosen family of integral ideals representing the ideal classes of `L`.  Every idele can be
multiplied by a principal idele so as to become an `S`-idele, because the divisor of the idele
can be corrected, modulo principal divisors, to one supported on `S`; this is exactly the
finiteness of the ideal class group.

## Main definitions

* `NumberField.FiniteAdeleRing.ordIdele` : the `ℤ`-valued divisor of a finite idele.
* `NumberField.classPlaces` : the finite set of places carrying the chosen class
  representatives.
* `NumberField.sIdeleToClass` : the natural map `𝕀_{L,S} → C_L`.
* `NumberField.sIdeleQuotientEquiv` : the isomorphism `𝕀_{L,S} / (ker) ≃* C_L`.

## Main results

* `NumberField.IdeleGroup.exists_mul_principalEmbedding_mem_sIdeleSubgroup` and
  `NumberField.IdeleGroup.principalSubgroup_sup_sIdeleSubgroup` : **`𝕀_L = L^× · 𝕀_{L,S}`**.
* `NumberField.sIdeleToClass_surjective` and `NumberField.mem_ker_sIdeleToClass_iff` :
  **`C_L ≅ 𝕀_{L,S}/O_{L,S}^×`**, the shape in which the Herbrand quotient of `C_L` is computed.
* `NumberField.exists_galois_stable_sIdeleSubgroup_sup` : the same with `S` replaced by a
  `Gal(L/K)`-stable finite set of places, which is what the cohomological computation needs.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors

variable {L : Type*} [Field L] [NumberField L]

namespace NumberField.FiniteAdeleRing

theorem valued_ne_zero (u : (FiniteAdeleRing (𝓞 L) L)ˣ) (w : HeightOneSpectrum (𝓞 L)) :
    Valued.v ((u : FiniteAdeleRing (𝓞 L) L) w) ≠ 0 := by
  intro h
  have h1 : (u : FiniteAdeleRing (𝓞 L) L) *
      ((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) = 1 := u.mul_inv
  have h' := congrArg (fun x : FiniteAdeleRing (𝓞 L) L ↦ Valued.v (x w)) h1
  simp only [mul_apply', map_mul, one_apply' L w, map_one, h, zero_mul] at h'
  exact zero_ne_one h'

variable (L) in
/-- The `ℤ`-valued order of vanishing of a finite idele at a finite place. -/
def ordIdele (u : (FiniteAdeleRing (𝓞 L) L)ˣ) (w : HeightOneSpectrum (𝓞 L)) : ℤ :=
  - WithZero.log (Valued.v ((u : FiniteAdeleRing (𝓞 L) L) w))

theorem ordIdele_eq_zero_iff (u : (FiniteAdeleRing (𝓞 L) L)ˣ) (w : HeightOneSpectrum (𝓞 L)) :
    ordIdele L u w = 0 ↔ Valued.v ((u : FiniteAdeleRing (𝓞 L) L) w) = 1 := by
  rw [ordIdele, neg_eq_zero]
  constructor
  · intro h
    rw [← WithZero.exp_log (valued_ne_zero u w), h, WithZero.exp_zero]
  · intro h; rw [h]; simp

theorem ordIdele_mul (u v : (FiniteAdeleRing (𝓞 L) L)ˣ) (w : HeightOneSpectrum (𝓞 L)) :
    ordIdele L (u * v) w = ordIdele L u w + ordIdele L v w := by
  rw [ordIdele, ordIdele, ordIdele, Units.val_mul, mul_apply', map_mul,
    WithZero.log_mul (valued_ne_zero u w) (valued_ne_zero v w), neg_add]

theorem mem_sIdeleSubgroup_iff_ordIdele {T : Set (HeightOneSpectrum (𝓞 L))}
    (u : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    u ∈ sIdeleSubgroup L T ↔ ∀ w : HeightOneSpectrum (𝓞 L), w ∉ T → ordIdele L u w = 0 := by
  simp only [mem_sIdeleSubgroup, ordIdele_eq_zero_iff]

/-- The order of a principal finite idele is the order of the element. -/
theorem ordIdele_unitEmbedding (x : Lˣ) (w : HeightOneSpectrum (𝓞 L)) :
    ordIdele L (FiniteAdeleRing.unitEmbedding (𝓞 L) L x) w = w.ord L (x : L) := by
  rw [ordIdele, IsDedekindDomain.HeightOneSpectrum.ord]
  congr 1
  congr 1
  rw [show ((FiniteAdeleRing.unitEmbedding (𝓞 L) L x : (FiniteAdeleRing (𝓞 L) L)ˣ) :
      FiniteAdeleRing (𝓞 L) L) w = ((x : L) : w.adicCompletion L) from
    FiniteAdeleRing.algebraMap_apply (𝓞 L) L (x : L) w]
  exact valuedAdicCompletion_eq_valuation' w (x : L)

/-- The divisor of a finite idele is finitely supported. -/
theorem ordIdele_eventually_eq_zero (u : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, ordIdele L u w = 0 := by
  obtain ⟨T, hT, hu⟩ := exists_mem_sIdeleSubgroup u
  rw [Filter.eventually_cofinite]
  refine hT.subset fun w hw ↦ ?_
  by_contra hwT
  exact hw ((mem_sIdeleSubgroup_iff_ordIdele u).1 hu w hwT)

end NumberField.FiniteAdeleRing

namespace NumberField

variable (L) in
/-- The finite set of finite places of `L` supporting a chosen representative of every ideal
class of `L`. -/
abbrev classPlaces : Set (HeightOneSpectrum (𝓞 L)) :=
  IsDedekindDomain.HeightOneSpectrum.classRepSupport (R := 𝓞 L) L

theorem finite_classPlaces : (classPlaces L).Finite :=
  IsDedekindDomain.HeightOneSpectrum.finite_classRepSupport (R := 𝓞 L) L

namespace FiniteAdeleRing

/-- **Every finite idele becomes a `classPlaces`-idele after multiplication by a principal
idele.** -/
theorem exists_mul_unitEmbedding_mem_sIdeleSubgroup (u : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    ∃ x : Lˣ, u * FiniteAdeleRing.unitEmbedding (𝓞 L) L x ∈ sIdeleSubgroup L (classPlaces L) := by
  obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.exists_ord_eq_of_notMem_classRepSupport
    L (ordIdele L u) (ordIdele_eventually_eq_zero u)
  refine ⟨y⁻¹, ?_⟩
  rw [mem_sIdeleSubgroup_iff_ordIdele]
  intro w hw
  rw [ordIdele_mul, ordIdele_unitEmbedding,
    show ((y⁻¹ : Lˣ) : L) = ((y : L))⁻¹ from Units.val_inv_eq_inv_val y,
    IsDedekindDomain.HeightOneSpectrum.ord_inv, hy w hw]
  ring

end FiniteAdeleRing

namespace IdeleGroup

/-- **Every idele becomes a `classPlaces`-idele after multiplication by a principal idele**:
`𝕀_L = L^× · 𝕀_{L,S}` for `S = classPlaces L`. -/
theorem exists_mul_principalEmbedding_mem_sIdeleSubgroup (u : IdeleGroup (𝓞 L) L) :
    ∃ x : Lˣ, u * IdeleGroup.principalEmbedding (𝓞 L) L x
      ∈ IdeleGroup.sIdeleSubgroup L (classPlaces L) := by
  obtain ⟨x, hx⟩ :=
    FiniteAdeleRing.exists_mul_unitEmbedding_mem_sIdeleSubgroup (finiteUnits L u)
  refine ⟨x, ?_⟩
  rw [IdeleGroup.sIdeleSubgroup, Subgroup.mem_comap, map_mul, finiteUnits_principalEmbedding]
  exact hx

/-- **`𝕀_L = L^× · 𝕀_{L,S}`**, as a supremum of subgroups. -/
theorem principalSubgroup_sup_sIdeleSubgroup :
    IdeleGroup.principalSubgroup (𝓞 L) L ⊔ IdeleGroup.sIdeleSubgroup L (classPlaces L) = ⊤ := by
  refine eq_top_iff.2 fun u _ ↦ ?_
  obtain ⟨x, hx⟩ := exists_mul_principalEmbedding_mem_sIdeleSubgroup u
  have h1 : u * IdeleGroup.principalEmbedding (𝓞 L) L x ∈
      IdeleGroup.principalSubgroup (𝓞 L) L ⊔ IdeleGroup.sIdeleSubgroup L (classPlaces L) :=
    Subgroup.mem_sup_right hx
  have h2 : (IdeleGroup.principalEmbedding (𝓞 L) L x)⁻¹ ∈
      IdeleGroup.principalSubgroup (𝓞 L) L ⊔ IdeleGroup.sIdeleSubgroup L (classPlaces L) :=
    Subgroup.mem_sup_left (inv_mem ⟨x, rfl⟩)
  simpa using mul_mem h1 h2

end IdeleGroup

end NumberField

namespace NumberField

variable (L) in
/-- The natural map `𝕀_{L,S} → C_L` from the `S`-ideles to the idele class group, for
`S = classPlaces L`. -/
def sIdeleToClass :
    IdeleGroup.sIdeleSubgroup L (classPlaces L) →* IdeleClassGroup (𝓞 L) L :=
  (IdeleClassGroup.mk (𝓞 L) L).comp
    (IdeleGroup.sIdeleSubgroup L (classPlaces L)).subtype

@[simp]
theorem sIdeleToClass_apply (u : IdeleGroup.sIdeleSubgroup L (classPlaces L)) :
    sIdeleToClass L u = IdeleClassGroup.mk (𝓞 L) L (u : IdeleGroup (𝓞 L) L) := rfl

/-- **`C_L = 𝕀_{L,S} / O_{L,S}^×`, surjectivity half.**  Every idele class is represented by an
`S`-idele, for `S = classPlaces L`. -/
theorem sIdeleToClass_surjective : Function.Surjective (sIdeleToClass L) := by
  intro c
  obtain ⟨u, rfl⟩ := IdeleClassGroup.mk_surjective (𝓞 L) L c
  obtain ⟨x, hx⟩ := IdeleGroup.exists_mul_principalEmbedding_mem_sIdeleSubgroup u
  refine ⟨⟨u * IdeleGroup.principalEmbedding (𝓞 L) L x, hx⟩, ?_⟩
  rw [sIdeleToClass_apply, map_mul, IdeleClassGroup.mk_principalEmbedding, mul_one]

/-- **`C_L = 𝕀_{L,S} / O_{L,S}^×`, kernel half.**  The kernel of `𝕀_{L,S} → C_L` consists of
the principal ideles attached to the `S`-units. -/
theorem mem_ker_sIdeleToClass_iff (u : IdeleGroup.sIdeleSubgroup L (classPlaces L)) :
    u ∈ (sIdeleToClass L).ker ↔
      ∃ x : Lˣ, x ∈ (classPlaces L).unit L ∧
        IdeleGroup.principalEmbedding (𝓞 L) L x = (u : IdeleGroup (𝓞 L) L) := by
  rw [MonoidHom.mem_ker, sIdeleToClass_apply, IdeleClassGroup.mk_eq_one_iff]
  constructor
  · intro h
    have hmem : (u : IdeleGroup (𝓞 L) L) ∈
        IdeleGroup.principalSubgroup (𝓞 L) L ⊓
          IdeleGroup.sIdeleSubgroup L (classPlaces L) := ⟨h, u.2⟩
    rw [IdeleGroup.principalSubgroup_inf_sIdeleSubgroup] at hmem
    obtain ⟨x, hx, hxu⟩ := hmem
    exact ⟨x, hx, hxu⟩
  · rintro ⟨x, -, hxu⟩
    exact ⟨x, hxu⟩

variable (L) in
/-- **`C_L ≅ 𝕀_{L,S} / O_{L,S}^×`.**  The idele class group of `L` is the quotient of the
`S`-ideles by the `S`-units, for `S = classPlaces L` a finite set of finite places carrying
representatives of every ideal class.  This is the reduction used to compute the Herbrand
quotient of the idele class group. -/
def sIdeleQuotientEquiv :
    (IdeleGroup.sIdeleSubgroup L (classPlaces L) ⧸ (sIdeleToClass L).ker)
      ≃* IdeleClassGroup (𝓞 L) L :=
  QuotientGroup.quotientKerEquivOfSurjective _ sIdeleToClass_surjective

end NumberField

namespace NumberField

section GaloisStable

variable {K : Type*} [Field K] [NumberField K] [Algebra K L]

variable (K L) in
/-- Any finite set of finite places of `L` is contained in a `Gal(L/K)`-stable finite set,
namely the set of all places above the places of `K` that it covers. -/
theorem exists_finite_subset_placesOverSet {T : Set (HeightOneSpectrum (𝓞 L))} (hT : T.Finite) :
    ∃ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite ∧ T ⊆ placesOverSet K L S ∧
      (placesOverSet K L S).Finite := by
  refine ⟨(fun w : HeightOneSpectrum (𝓞 L) ↦ w.under (𝓞 K)) '' T, hT.image _, ?_, ?_⟩
  · exact fun w hw ↦ ⟨w, hw, rfl⟩
  · exact finite_placesOverSet (hT.image _)

variable (K L) in
/-- **`𝕀_L = L^× · 𝕀_{L,S}` for a `Gal(L/K)`-stable finite set `S` of places.**  This is the
choice of `S` made at the start of the computation of the Herbrand quotient of `C_L`: it is
finite, stable under the Galois action, and large enough that the `S`-ideles already surject
onto the idele class group. -/
theorem exists_galois_stable_sIdeleSubgroup_sup :
    ∃ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite ∧ (placesOverSet K L S).Finite ∧
      IdeleGroup.principalSubgroup (𝓞 L) L ⊔
        IdeleGroup.sIdeleSubgroup L (placesOverSet K L S) = ⊤ := by
  obtain ⟨S, hS, hsub, hfin⟩ := exists_finite_subset_placesOverSet (K := K) (L := L) (finite_classPlaces (L := L))
  refine ⟨S, hS, hfin, ?_⟩
  refine eq_top_iff.2 (le_trans (le_of_eq IdeleGroup.principalSubgroup_sup_sIdeleSubgroup.symm) ?_)
  exact sup_le_sup_left (IdeleGroup.sIdeleSubgroup_mono hsub) _

end GaloisStable

end NumberField
