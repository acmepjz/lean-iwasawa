/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.RestrictedProductSplit
public import Iwasawalib.NumberTheory.CFT.FiniteAdeleSemilocal
public import Iwasawalib.NumberTheory.CFT.SIdeles
public import Iwasawalib.GroupCohomology.FiniteIdeleVanishing

@[expose] public section

/-!
# The `S`-ideles are a product of semilocal factors

Let `L / K` be an extension of number fields and `S` a set of finite places of `K`.  The group
of `S`-ideles of `L` inside the finite ideles is `𝕀_{L,S}^f = {u ∈ (𝔸_L^f)^× | v_w(u_w) = 1 for
every finite place w of L not above S}`.  This file proves that, when `S` is **finite**, that
group is an honest product of semilocal factors:

`𝕀_{L,S}^f ≃ ∏_{v ∈ S} (∏_{w ∣ v} L_w)^× × ∏_{v ∉ S} (∏_{w ∣ v} O_w)^×`

(`NumberField.finiteSIdeleSemilocalEquiv`), `Gal(L/K)`-equivariantly
(`NumberField.finiteSIdeleSemilocalEquiv_smul`).

The grouping is by places **of `K`**, which is what makes the statement equivariant: `Gal(L/K)`
permutes the places of `L`, but it fixes every place of `K`, so it acts on each semilocal factor
separately.  Grouping by places of `L` instead would not give a `Gal(L/K)`-stable
decomposition.

## Proof

Two steps, neither of them arithmetic:

* `NumberField.semilocalFiniteEquiv` (in
  `Iwasawalib/NumberTheory/CFT/FiniteAdeleSemilocal.lean`) writes `𝔸_L^f` as the restricted
  product over the finite places `v` of `K` of the semilocal factors `∏_{w ∣ v} L_w`, and
  Mathlib's `RestrictedProduct.unitsEquiv` passes to units.  This is
  `NumberField.finiteIdeleEquivSemilocal`, already available in
  `Iwasawalib/GroupCohomology/FiniteIdeleVanishing.lean`.
* `RestrictedProduct.outsideSubgroupEquiv` (in
  `Iwasawalib/NumberTheory/CFT/RestrictedProductSplit.lean`) says that a restricted product,
  constrained at *every* index outside a finite set `S`, is a plain product.  The restricted
  product condition — membership in the subgroup for cofinitely many indices — is implied by
  the constraint, so nothing is left of it.

## Main definitions

* `NumberField.SIdeleSemilocal` : the semilocal model of the `S`-ideles.
* `NumberField.outsideOfSIdele`, `NumberField.sIdeleOfOutside`,
  `NumberField.finiteSIdeleEquivOutside` : the `S`-ideles inside the semilocal restricted
  product.
* `NumberField.finiteSIdeleSemilocalEquiv` : the splitting.

## Main statements

* `NumberField.finiteIdeleEquivSemilocal_mem_outsideSubgroup` : an idele is an `S`-idele exactly when
  its semilocal components are integral outside `S`.
* `NumberField.smul_mem_localProductIntegers`, `NumberField.smul_mem_localProductIntegerUnits`
  : the Galois action preserves `∏_{w ∣ v} O_w` and its units.
* `NumberField.finiteIdeleEquivSemilocal_smul`, `NumberField.finiteSIdeleSemilocalEquiv_smul` :
  equivariance.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.semilocalIdeleMulDistribMulAction

namespace NumberField

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L]
  [Algebra K L]

variable {K L}

@[simp]
theorem coe_finiteIdeleEquivSemilocal (u : (FiniteAdeleRing (𝓞 L) L)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : placesOver K L v) :
    ((finiteIdeleEquivSemilocal K L u v : (LocalProduct K L v)ˣ) : LocalProduct K L v) w
      = (u : FiniteAdeleRing (𝓞 L) L) (w : HeightOneSpectrum (𝓞 L)) := rfl

@[simp]
theorem coe_inv_finiteIdeleEquivSemilocal (u : (FiniteAdeleRing (𝓞 L) L)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : placesOver K L v) :
    (((finiteIdeleEquivSemilocal K L u v)⁻¹ : (LocalProduct K L v)ˣ) : LocalProduct K L v) w
      = ((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L)
          (w : HeightOneSpectrum (𝓞 L)) := rfl

theorem mem_localProductIntegerUnits {v : HeightOneSpectrum (𝓞 K)}
    {x : (LocalProduct K L v)ˣ} :
    x ∈ localProductIntegerUnits K L v ↔
      ((x : LocalProduct K L v) ∈ localProductIntegers K L v ∧
        ((x⁻¹ : (LocalProduct K L v)ˣ) : LocalProduct K L v) ∈ localProductIntegers K L v) :=
  Iff.rfl

/-- **The `S`-ideles are the elements of the semilocal restricted product that are integral
outside `S`.** -/
theorem finiteIdeleEquivSemilocal_mem_outsideSubgroup
    (S : Set (HeightOneSpectrum (𝓞 K))) (u : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    finiteIdeleEquivSemilocal K L u ∈
        RestrictedProduct.outsideSubgroup (localProductIntegerUnits K L) S ↔
      u ∈ FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S) := by
  rw [RestrictedProduct.mem_outsideSubgroup, FiniteAdeleRing.mem_sIdeleSubgroup]
  constructor
  · intro h w hw
    have hv : w.under (𝓞 K) ∉ S := fun hc ↦ hw hc
    have hmem := (mem_localProductIntegerUnits).1 (h (w.under (𝓞 K)) hv)
    refine FiniteAdeleRing.valued_eq_one_of_mem_integers ?_ ?_
    · exact hmem.1 ⟨w, rfl⟩
    · exact hmem.2 ⟨w, rfl⟩
  · intro h v hv
    refine (mem_localProductIntegerUnits).2 ⟨fun w ↦ ?_, fun w ↦ ?_⟩
    · have hw : (w : HeightOneSpectrum (𝓞 L)).under (𝓞 K) = v := under_coe_placesOver K L w
      have h1 : Valued.v ((u : FiniteAdeleRing (𝓞 L) L) (w : HeightOneSpectrum (𝓞 L))) = 1 :=
        h _ (by rw [NumberField.mem_placesOverSet, hw]; exact hv)
      show ((u : FiniteAdeleRing (𝓞 L) L) (w : HeightOneSpectrum (𝓞 L)))
          ∈ (w : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L
      rw [mem_adicCompletionIntegers]
      exact h1.le
    · have hw : (w : HeightOneSpectrum (𝓞 L)).under (𝓞 K) = v := under_coe_placesOver K L w
      have h1 : Valued.v ((u : FiniteAdeleRing (𝓞 L) L) (w : HeightOneSpectrum (𝓞 L))) = 1 :=
        h _ (by rw [NumberField.mem_placesOverSet, hw]; exact hv)
      have hmul : (u : FiniteAdeleRing (𝓞 L) L) *
          ((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) = 1 := u.mul_inv
      have h2 := congrArg (fun x : FiniteAdeleRing (𝓞 L) L ↦
        Valued.v (x (w : HeightOneSpectrum (𝓞 L)))) hmul
      simp only [FiniteAdeleRing.mul_apply', map_mul, FiniteAdeleRing.one_apply', map_one,
        h1, one_mul] at h2
      show (((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L)
            (w : HeightOneSpectrum (𝓞 L)))
          ∈ (w : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L
      rw [mem_adicCompletionIntegers]
      exact h2.le

/-! ## The Galois action on the semilocal pieces -/

section Galois

variable {v : HeightOneSpectrum (𝓞 K)}

/-- The semilocal decomposition of the finite ideles, componentwise, is
`Gal(L/K)`-equivariant. -/
theorem finiteIdeleEquivSemilocal_smul_apply (σ : L ≃ₐ[K] L)
    (u : (FiniteAdeleRing (𝓞 L) L)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finiteIdeleEquivSemilocal K L (σ • u) v = σ • finiteIdeleEquivSemilocal K L u v :=
  congrFun (congrArg
    (fun y : SemilocalIdeleGroup K L ↦ (y : ∀ v, (LocalProduct K L v)ˣ))
    (finiteIdeleEquivSemilocal_smul K L σ u)) v

variable (K L)

/-- The Galois action on `∏_{w ∣ v} O_w^×`. -/
instance localProductIntegerUnitsMulDistribMulAction (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction (L ≃ₐ[K] L) (localProductIntegerUnits K L v) where
  smul σ x := ⟨σ • (x : (LocalProduct K L v)ˣ), smul_mem_localProductIntegerUnits σ x.2⟩
  one_smul x := Subtype.ext (one_smul _ (x : (LocalProduct K L v)ˣ))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : (LocalProduct K L v)ˣ))
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ x y := Subtype.ext (smul_mul' σ (x : (LocalProduct K L v)ˣ) _)

variable {K L}

omit [NumberField K] in
@[simp]
theorem coe_smul_localProductIntegerUnits (σ : L ≃ₐ[K] L)
    (x : localProductIntegerUnits K L v) :
    ((σ • x : localProductIntegerUnits K L v) : (LocalProduct K L v)ˣ)
      = σ • (x : (LocalProduct K L v)ˣ) := rfl

variable (K L)

/-- The Galois action on the group of `S`-ideles inside the finite ideles. -/
instance finiteSIdeleMulDistribMulAction (S : Set (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S)) where
  smul σ u := ⟨σ • (u : (FiniteAdeleRing (𝓞 L) L)ˣ),
    FiniteAdeleRing.smul_mem_sIdeleSubgroup S σ u.2⟩
  one_smul u := Subtype.ext (one_smul _ (u : (FiniteAdeleRing (𝓞 L) L)ˣ))
  mul_smul σ τ u := Subtype.ext (mul_smul σ τ (u : (FiniteAdeleRing (𝓞 L) L)ˣ))
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ u w := Subtype.ext (smul_mul' σ (u : (FiniteAdeleRing (𝓞 L) L)ˣ) _)

variable {K L}

omit [NumberField K] in
@[simp]
theorem coe_smul_finiteSIdele {S : Set (HeightOneSpectrum (𝓞 K))} (σ : L ≃ₐ[K] L)
    (u : FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S)) :
    ((σ • u : FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S))
      : (FiniteAdeleRing (𝓞 L) L)ˣ) = σ • (u : (FiniteAdeleRing (𝓞 L) L)ˣ) := rfl

end Galois

/-! ## The splitting of the `S`-ideles -/

section Split

variable (K L) (S : Set (HeightOneSpectrum (𝓞 K)))

/-- **The semilocal model of the `S`-ideles of `L`:**
`∏_{v ∈ S} (∏_{w ∣ v} L_w)^× × ∏_{v ∉ S} (∏_{w ∣ v} O_w)^×`. -/
abbrev SIdeleSemilocal : Type _ :=
  (∀ v : S, (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) ×
    (∀ v : ↥(Sᶜ), localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))

/-- The `S`-ideles, seen inside the semilocal restricted product. -/
def outsideOfSIdele (u : FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S)) :
    RestrictedProduct.outsideSubgroup (localProductIntegerUnits K L) S :=
  ⟨finiteIdeleEquivSemilocal K L (u : (FiniteAdeleRing (𝓞 L) L)ˣ),
    (finiteIdeleEquivSemilocal_mem_outsideSubgroup S _).2 u.2⟩

/-- The inverse of `NumberField.outsideOfSIdele`. -/
def sIdeleOfOutside (y : RestrictedProduct.outsideSubgroup (localProductIntegerUnits K L) S) :
    FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S) := by
  refine ⟨(finiteIdeleEquivSemilocal K L).symm
      (y : SemilocalIdeleGroup K L),
    (finiteIdeleEquivSemilocal_mem_outsideSubgroup S _).1 ?_⟩
  rw [MulEquiv.apply_symm_apply]
  exact y.2

/-- The `S`-ideles inside the finite ideles are exactly the elements of the semilocal
restricted product that are integral outside `S`. -/
def finiteSIdeleEquivOutside :
    FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S) ≃*
      RestrictedProduct.outsideSubgroup (localProductIntegerUnits K L) S where
  toFun := outsideOfSIdele K L S
  invFun := sIdeleOfOutside K L S
  left_inv u := by
    refine Subtype.ext ?_
    show (finiteIdeleEquivSemilocal K L).symm
      (finiteIdeleEquivSemilocal K L (u : (FiniteAdeleRing (𝓞 L) L)ˣ))
        = (u : (FiniteAdeleRing (𝓞 L) L)ˣ)
    rw [MulEquiv.symm_apply_apply]
  right_inv y := by
    refine Subtype.ext ?_
    show finiteIdeleEquivSemilocal K L ((finiteIdeleEquivSemilocal K L).symm
      (y : SemilocalIdeleGroup K L)) = _
    rw [MulEquiv.apply_symm_apply]
  map_mul' u w := Subtype.ext (map_mul (finiteIdeleEquivSemilocal K L) _ _)

variable {K L S}

/-- **The `S`-ideles of `L` are a plain product of semilocal factors.**  Inside the finite
ideles, `𝕀_{L,S}^f = ∏_{v ∈ S} (∏_{w ∣ v} L_w)^× × ∏_{v ∉ S} (∏_{w ∣ v} O_w)^×`.  The
restricted product becomes an honest product because the constraint is imposed at **every**
place outside the finite set `S`. -/
def finiteSIdeleSemilocalEquiv (hS : S.Finite) :
    FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S) ≃* SIdeleSemilocal K L S :=
  (finiteSIdeleEquivOutside K L S).trans (RestrictedProduct.outsideSubgroupEquiv hS)

theorem finiteSIdeleSemilocalEquiv_fst (hS : S.Finite)
    (u : FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S)) (v : S) :
    (finiteSIdeleSemilocalEquiv hS u).1 v
      = finiteIdeleEquivSemilocal K L (u : (FiniteAdeleRing (𝓞 L) L)ˣ)
          (v : HeightOneSpectrum (𝓞 K)) := by
  rw [finiteSIdeleSemilocalEquiv, MulEquiv.trans_apply,
    RestrictedProduct.outsideSubgroupEquiv_apply_fst]
  rfl

theorem finiteSIdeleSemilocalEquiv_snd (hS : S.Finite)
    (u : FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S)) (v : ↥(Sᶜ)) :
    ((finiteSIdeleSemilocalEquiv hS u).2 v
        : (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ)
      = finiteIdeleEquivSemilocal K L (u : (FiniteAdeleRing (𝓞 L) L)ˣ)
          (v : HeightOneSpectrum (𝓞 K)) := by
  rw [finiteSIdeleSemilocalEquiv, MulEquiv.trans_apply,
    RestrictedProduct.outsideSubgroupEquiv_apply_snd]
  rfl

/-- **The splitting of the `S`-ideles is `Gal(L/K)`-equivariant.**  The Galois group permutes
the places of `L` but fixes each place of `K`, so it acts on each semilocal factor
separately. -/
theorem finiteSIdeleSemilocalEquiv_smul (hS : S.Finite) (σ : L ≃ₐ[K] L)
    (u : FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S)) :
    finiteSIdeleSemilocalEquiv hS (σ • u) = σ • finiteSIdeleSemilocalEquiv hS u := by
  refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ Subtype.ext ?_)
  · rw [finiteSIdeleSemilocalEquiv_fst, coe_smul_finiteSIdele, finiteIdeleEquivSemilocal_smul_apply,
      show (σ • finiteSIdeleSemilocalEquiv hS u).1 v
        = σ • (finiteSIdeleSemilocalEquiv hS u).1 v from rfl,
      finiteSIdeleSemilocalEquiv_fst]
  · have h1 : (σ • finiteSIdeleSemilocalEquiv hS u).2 v
        = σ • (finiteSIdeleSemilocalEquiv hS u).2 v := rfl
    rw [h1, coe_smul_localProductIntegerUnits, finiteSIdeleSemilocalEquiv_snd,
      finiteSIdeleSemilocalEquiv_snd, coe_smul_finiteSIdele, finiteIdeleEquivSemilocal_smul_apply]

end Split

end NumberField
