/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.FiniteAdeleBaseChange

@[expose] public section

/-!
# The semilocal decomposition of the finite adele ring

Let `L / K` be an extension of number fields.  Grouping the finite places of `L` by the finite
place of `K` they lie over decomposes the finite adele ring of `L` as a restricted product,
over the finite places `v` of `K`, of the semilocal factors `∏_{w ∣ v} L_w`, restricted with
respect to `∏_{w ∣ v} O_w`.

Unlike the archimedean case (`NumberField.InfiniteAdeleRing.semilocalEquiv`), which is a plain
regrouping of a `Pi` type, this is a genuine reindexing of a *restricted* product: it is true
because the fibres of `w ↦ w.under (𝓞 K)` are finite, so that a finite exceptional set of
places `v` of `K` pulls back to a finite exceptional set of places `w` of `L`.

## Main definitions

* `Subring.pi` : the product of a family of subrings, as a subring of the product ring.
* `NumberField.localProductIntegers` : the subring `∏_{w ∣ v} O_w` of `∏_{w ∣ v} L_w`.
* `NumberField.SemilocalFiniteAdeleRing K L` : the restricted product
  `Πʳ v, [∏_{w ∣ v} L_w, ∏_{w ∣ v} O_w]`.
* `NumberField.semilocalFiniteEquiv` : the ring isomorphism `𝔸_L^f ≃+* Πʳ v, ∏_{w ∣ v} L_w`.

## Main results

* `NumberField.finite_placesOver` : there are finitely many places of `L` above a place of `K`.
* `NumberField.semilocalFiniteEquiv_finiteAdeleMap` : the decomposition is
  `Gal(L/K)`-equivariant, each semilocal factor `∏_{w ∣ v} L_w` being preserved.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct

/-! ## The product of a family of subrings -/

/-- The product of a family of subrings, as a subring of the product ring. -/
def Subring.pi {ι : Type*} {R : ι → Type*} [∀ i, Ring (R i)] (S : ∀ i, Subring (R i)) :
    Subring (∀ i, R i) where
  carrier := {x | ∀ i, x i ∈ S i}
  mul_mem' hx hy i := mul_mem (hx i) (hy i)
  one_mem' _ := one_mem _
  add_mem' hx hy i := add_mem (hx i) (hy i)
  zero_mem' _ := zero_mem _
  neg_mem' hx i := neg_mem (hx i)

@[simp]
theorem Subring.mem_pi {ι : Type*} {R : ι → Type*} [∀ i, Ring (R i)] (S : ∀ i, Subring (R i))
    (x : ∀ i, R i) : x ∈ Subring.pi S ↔ ∀ i, x i ∈ S i := Iff.rfl

namespace NumberField

variable (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]

/-! ## Finiteness of the fibres of finite places -/

omit [NumberField K] [NumberField L] in
theorem placesOver_eq_setOf_under_eq (v : HeightOneSpectrum (𝓞 K)) :
    placesOver K L v = {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v} := by
  ext w
  exact ⟨fun h ↦ HeightOneSpectrum.ext h, fun h ↦ congrArg HeightOneSpectrum.asIdeal h⟩

/-- There are only finitely many finite places of `L` above a finite place of `K`. -/
theorem finite_placesOver (v : HeightOneSpectrum (𝓞 K)) : (placesOver K L v).Finite := by
  rw [placesOver_eq_setOf_under_eq]
  exact IsDedekindDomain.FiniteAdeleRing.finite_setOf_under_eq v

instance (v : HeightOneSpectrum (𝓞 K)) : Finite (placesOver K L v) :=
  (finite_placesOver K L v).to_subtype

omit [NumberField K] [NumberField L] in
theorem under_coe_placesOver {v : HeightOneSpectrum (𝓞 K)} (w : placesOver K L v) :
    (w : HeightOneSpectrum (𝓞 L)).under (𝓞 K) = v :=
  HeightOneSpectrum.ext w.2

/-! ## The semilocal restricted product -/

/-- The subring `∏_{w ∣ v} O_w` of the semilocal factor `∏_{w ∣ v} L_w`. -/
def localProductIntegers (v : HeightOneSpectrum (𝓞 K)) : Subring (LocalProduct K L v) :=
  Subring.pi fun w ↦ ((w : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L).toSubring

omit [NumberField K] in
@[simp]
theorem mem_localProductIntegers {v : HeightOneSpectrum (𝓞 K)} (x : LocalProduct K L v) :
    x ∈ localProductIntegers K L v ↔
      ∀ w : placesOver K L v, x w ∈ (w : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L :=
  Iff.rfl

/-- The finite adele ring of `L`, written as a restricted product of the semilocal factors
`∏_{w ∣ v} L_w` over the finite places `v` of `K`. -/
abbrev SemilocalFiniteAdeleRing : Type _ :=
  Πʳ v : HeightOneSpectrum (𝓞 K), [LocalProduct K L v, localProductIntegers K L v]

/-! ## The decomposition -/

/-- **The finite semilocal decomposition.**  The finite adele ring of `L` is the restricted
product over the finite places `v` of `K` of the semilocal factors `∏_{w ∣ v} L_w`. -/
def semilocalFiniteEquiv :
    FiniteAdeleRing (𝓞 L) L ≃+* SemilocalFiniteAdeleRing K L where
  toFun x := ⟨fun _ w ↦ x (w : HeightOneSpectrum (𝓞 L)), by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset
      ((Filter.eventually_cofinite.1 x.2).image fun w ↦ w.under (𝓞 K)) ?_
    intro v hv
    have hex : ∃ w : placesOver K L v, x (w : HeightOneSpectrum (𝓞 L)) ∉
        (w : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L := by
      by_contra hcon
      exact hv fun w ↦ not_not.1 fun h ↦ hcon ⟨w, h⟩
    obtain ⟨w, hw⟩ := hex
    exact ⟨(w : HeightOneSpectrum (𝓞 L)), hw, under_coe_placesOver K L w⟩⟩
  invFun y := ⟨fun w ↦ y (w.under (𝓞 K)) ⟨w, rfl⟩, by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset
      (Set.Finite.biUnion (Filter.eventually_cofinite.1 y.2)
        (fun v _ ↦ finite_placesOver K L v)) ?_
    intro w hw
    have hbad : ¬ (y (w.under (𝓞 K)) ∈ localProductIntegers K L (w.under (𝓞 K))) := by
      intro hcon
      exact hw (hcon ⟨w, rfl⟩)
    exact Set.mem_biUnion hbad rfl⟩
  left_inv x := by ext w; rfl
  right_inv y := by
    ext v w
    obtain ⟨w, hw⟩ := w
    have h : w.under (𝓞 K) = v := HeightOneSpectrum.ext hw
    subst h
    rfl
  map_mul' x y := rfl
  map_add' x y := rfl

variable {K L}

@[simp]
theorem semilocalFiniteEquiv_apply (x : FiniteAdeleRing (𝓞 L) L)
    (v : HeightOneSpectrum (𝓞 K)) (w : placesOver K L v) :
    semilocalFiniteEquiv K L x v w = x (w : HeightOneSpectrum (𝓞 L)) := by rfl

@[simp]
theorem semilocalFiniteEquiv_symm_apply (y : SemilocalFiniteAdeleRing K L)
    (w : HeightOneSpectrum (𝓞 L)) :
    (semilocalFiniteEquiv K L).symm y w = y (w.under (𝓞 K)) ⟨w, rfl⟩ := by rfl

/-! ## Equivariance of the decomposition -/

/-- The finite semilocal decomposition is `Gal(L/K)`-equivariant: each semilocal factor
`∏_{w ∣ v} L_w` is preserved by the Galois action. -/
theorem semilocalFiniteEquiv_smul (σ : L ≃ₐ[K] L) (x : FiniteAdeleRing (𝓞 L) L)
    (v : HeightOneSpectrum (𝓞 K)) :
    semilocalFiniteEquiv K L (σ • x) v = σ • semilocalFiniteEquiv K L x v := by
  funext w
  rw [semilocalFiniteEquiv_apply, localProduct_smul_apply, finiteAdele_smul_apply,
    semilocalFiniteEquiv_apply]
  refine adicCompletionCongr_index_congr ?_ (w : HeightOneSpectrum (𝓞 L)) (σ : L ≃+* L) _ _
    (fun t ↦ x t)
  rw [invSmulPlace_coe, inv_smul_heightOneSpectrum]

/-! ## The base change in the semilocal picture -/

instance liesOver_coe_placesOver {v : HeightOneSpectrum (𝓞 K)} (w : placesOver K L v) :
    (w : HeightOneSpectrum (𝓞 L)).asIdeal.LiesOver v.asIdeal :=
  ⟨w.2.symm⟩

/-- In the semilocal picture, the base change of a finite adele of `K` is, in the factor at
`v`, the diagonal image of its `v`-component under the local base change maps
`K_v →+* L_w`. -/
theorem semilocalFiniteEquiv_baseChange (x : FiniteAdeleRing (𝓞 K) K)
    (v : HeightOneSpectrum (𝓞 K)) (w : placesOver K L v) :
    semilocalFiniteEquiv K L (finiteAdeleBaseChange K L x) v w =
      adicCompletionComap K L v (w : HeightOneSpectrum (𝓞 L)) (x v) :=
  adicCompletionComap_index_congr K L (under_coe_placesOver K L w)
    (w : HeightOneSpectrum (𝓞 L)) (fun t ↦ x t)

/-! ## The base change in the induced-module picture -/

/-- **The base change lands in the constant functions of the induced module.**  Under the
isomorphism `∏_{w ∣ v} L_w ≅ Ind_{D_{w₀}}^{Gal(L/K)} L_{w₀}`, the semilocal component at `v`
of a finite adele coming from `K` is the constant function with value the image of its
`v`-component in `L_{w₀}`.

This is the induced-module form of the inclusion `𝔸_K^f ⊆ (𝔸_L^f)^{Gal(L/K)}`. -/
theorem toIndLocal_semilocalFiniteEquiv_baseChange {v : HeightOneSpectrum (𝓞 K)}
    {w₀ : HeightOneSpectrum (𝓞 L)} (hw₀ : w₀ ∈ placesOver K L v)
    (x : FiniteAdeleRing (𝓞 K) K) (g : L ≃ₐ[K] L) :
    (toIndLocal hw₀ (semilocalFiniteEquiv K L (finiteAdeleBaseChange K L x) v) :
        (L ≃ₐ[K] L) → w₀.adicCompletion L) g =
      adicCompletionComap K L (w₀.under (𝓞 K)) w₀ (x (w₀.under (𝓞 K))) := by
  haveI : (g • w₀).asIdeal.LiesOver v.asIdeal := ⟨(smul_mem_placesOver hw₀ g).symm⟩
  haveI : w₀.asIdeal.LiesOver v.asIdeal := ⟨hw₀.symm⟩
  rw [toIndLocal_coe, toIndLocalFun_apply, semilocalFiniteEquiv_baseChange,
    adicCompletionComap_index_congr K L (HeightOneSpectrum.ext hw₀ : w₀.under (𝓞 K) = v) w₀
      (fun t ↦ x t)]
  exact IsDedekindDomain.FiniteAdeleRing.adicCompletionCongr_adicCompletionComap K L
    (((g⁻¹ : L ≃ₐ[K] L) : L ≃+* L)) (fun k ↦ (g⁻¹ : L ≃ₐ[K] L).commutes k) v (g • w₀) w₀
    (valuation_smul_place g w₀) (x v)

end NumberField
