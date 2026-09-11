/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.SUnitHerbrand
public import Iwasawalib.NumberTheory.CFT.SIdeleClass

@[expose] public section

/-!
# The Herbrand quotient of the idele class group

Let `L / K` be a cyclic extension of number fields with group `G = ⟨σ⟩` of order `n`, and let
`S` be a finite set of finite places of `K` large enough that `𝕀_L = L^× · 𝕀_{L,S}` — such an
`S` exists by `NumberField.exists_galois_stable_sIdeleSubgroup_sup`.  This file builds the
short exact sequence of `Gal(L/K)`-modules

`1 → O_{L,S}^× → 𝕀_{L,S} → C_L → 1`   (`NumberField.isShortExact_sUnit_sIdele`),

deduces the multiplicativity

`h(𝕀_{L,S}) = h(O_{L,S}^×) · h(C_L)`   (`NumberField.herbrand_sIdele_eq_mul`),

and combines it with `NumberField.herbrand_sUnitGroup` to get

`h(C_L) = [L : K]`   (`NumberField.herbrand_ideleClassGroup_of_herbrand_sIdele`)

**conditionally on the value `h(𝕀_{L,S}) = ∏_{v ∈ S ∪ S_∞} n_v`.**

## What the conditional depends on, and what it does not

The hypothesis `hidele` of `NumberField.herbrand_ideleClassGroup_of_herbrand_sIdele` is the
*local* half of the computation.  It is the composite of two facts that are not proved in this
repository:

* the semilocal decomposition `𝕀_{L,S} ≅ ∏_{v ∈ S} (∏_{w | v} L_wˣ) × ∏_{v ∉ S} (units)`
  together with Shapiro's lemma `CyclicTate.herbrand_piUnits`, which reduces `h(𝕀_{L,S})` to a
  product of local Herbrand quotients;
* local class field theory, `h(L_wˣ) = e(w | v)`, and the vanishing of the Herbrand quotient of
  the unramified local units.

Everything else in the chain **is** proved here and in the two files it rests on:

* `NumberField.sUnitBasis` (in `Iwasawalib/NumberTheory/CFT/SUnitLattice.lean`) — Dirichlet's
  `S`-unit theorem in *full lattice* form, the step that was previously missing;
* `NumberField.herbrand_sUnitGroup` (in `Iwasawalib/NumberTheory/CFT/SUnitHerbrand.lean`) —
  `h(O_{L,S}^×) = (∏_{v ∈ S ∪ S_∞} n_v) / n`, via Noether-Deuring;
* the short exact sequence and multiplicativity in this file.

So the arithmetic bookkeeping cancels here exactly as it should: `h(C_L) = (∏_v n_v) /
((∏_v n_v) / n) = n`.  The Tate cohomology of `C_L` is not assumed finite; it is deduced from
the finiteness for `O_{L,S}^×` (which follows from `NumberField.module_finite_sUnit`) and the
assumed finiteness for `𝕀_{L,S}`.

## Main definitions

* `NumberField.sUnitToSIdele` : `O_{L,S}^× → 𝕀_{L,S}`, equivariantly.
* `NumberField.sIdeleToIdeleClass` : `𝕀_{L,S} → C_L`, equivariantly.

## Main statements

* `NumberField.galIdeleAut_principalEmbedding` : the principal embedding is equivariant.
* `NumberField.isShortExact_sUnit_sIdele` : the sequence is short exact.
* `NumberField.herbrand_sIdele_eq_mul` : multiplicativity.
* `NumberField.herbrand_ideleClassGroup_of_herbrand_sIdele` : `h(C_L) = [L : K]`, conditional
  on the local input.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MulAction
open NumberField.InfiniteAdeleRing

attribute [local instance] NumberField.galIdeleClassMulDistribMulAction

namespace NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype (placesOverSet K L S)]

/-! ## The short exact sequence `1 → O_{L,S}^× → 𝕀_{L,S} → C_L → 1` -/

section ShortExact

variable {S}

omit [NumberField K] in
/-- **The principal embedding is `Gal(L/K)`-equivariant.** -/
theorem galIdeleAut_principalEmbedding (σ : L ≃ₐ[K] L) (x : Lˣ) :
    galIdeleAut K L σ (IdeleGroup.principalEmbedding (𝓞 L) L x)
      = IdeleGroup.principalEmbedding (𝓞 L) L (σ • x) := by
  rw [galIdeleAut_apply, ideleAut_principalEmbedding]
  exact congrArg _ (Units.ext rfl)

variable (S)

/-- The inclusion of the `S`-units into the `S`-ideles, as an equivariant map. -/
def sUnitToSIdele :
    Additive (SUnitGroup K L S) →+[L ≃ₐ[K] L]
      Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S)) where
  toFun x := Additive.ofMul ⟨IdeleGroup.principalEmbedding (𝓞 L) L
      ((Additive.toMul x : SUnitGroup K L S) : Lˣ),
    (IdeleGroup.principalEmbedding_mem_sIdeleSubgroup_iff _).2 (Additive.toMul x).2⟩
  map_smul' σ x := congrArg Additive.ofMul (Subtype.ext
    (galIdeleAut_principalEmbedding σ _).symm)
  map_zero' := congrArg Additive.ofMul (Subtype.ext (map_one _))
  map_add' x y := congrArg Additive.ofMul (Subtype.ext (map_mul _ _ _))

omit [NumberField K] [Fintype (placesOverSet K L S)] in
@[simp]
theorem coe_sUnitToSIdele (x : Additive (SUnitGroup K L S)) :
    ((Additive.toMul (sUnitToSIdele S x) :
        IdeleGroup.sIdeleSubgroup L (placesOverSet K L S)) : IdeleGroup (𝓞 L) L)
      = IdeleGroup.principalEmbedding (𝓞 L) L ((Additive.toMul x : SUnitGroup K L S) : Lˣ) :=
  rfl

/-- The projection of the `S`-ideles onto the idele class group, as an equivariant map. -/
def sIdeleToIdeleClass :
    Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S)) →+[L ≃ₐ[K] L]
      Additive (IdeleClassGroup (𝓞 L) L) where
  toFun u := Additive.ofMul (IdeleClassGroup.mk (𝓞 L) L
    ((Additive.toMul u : IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))
      : IdeleGroup (𝓞 L) L))
  map_smul' σ u := congrArg Additive.ofMul (galIdeleClassAut_mk σ _).symm
  map_zero' := congrArg Additive.ofMul (map_one _)
  map_add' u v := congrArg Additive.ofMul (map_mul _ _ _)

omit [NumberField K] [Fintype (placesOverSet K L S)] in
@[simp]
theorem toMul_sIdeleToIdeleClass
    (u : Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) :
    Additive.toMul (sIdeleToIdeleClass S u)
      = IdeleClassGroup.mk (𝓞 L) L
        ((Additive.toMul u : IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))
          : IdeleGroup (𝓞 L) L) := rfl

omit [NumberField K] [Fintype (placesOverSet K L S)] in
/-- **`1 → O_{L,S}^× → 𝕀_{L,S} → C_L → 1` is exact**, for any `Gal(L/K)`-stable finite set `S`
of places large enough that `𝕀_L = L^× · 𝕀_{L,S}`.  Such an `S` exists by
`NumberField.exists_galois_stable_sIdeleSubgroup_sup`. -/
theorem isShortExact_sUnit_sIdele
    (hsup : IdeleGroup.principalSubgroup (𝓞 L) L
      ⊔ IdeleGroup.sIdeleSubgroup L (placesOverSet K L S) = ⊤) :
    CyclicTate.IsShortExact (G := L ≃ₐ[K] L) (sUnitToSIdele S) (sIdeleToIdeleClass S) where
  inj := by
    intro x y h
    have h' : IdeleGroup.principalEmbedding (𝓞 L) L
          ((Additive.toMul x : SUnitGroup K L S) : Lˣ)
        = IdeleGroup.principalEmbedding (𝓞 L) L
          ((Additive.toMul y : SUnitGroup K L S) : Lˣ) := by
      rw [← coe_sUnitToSIdele, ← coe_sUnitToSIdele, h]
    exact Additive.toMul.injective (Subtype.ext
      (IdeleGroup.principalEmbedding_injective (𝓞 L) L h'))
  surj := by
    intro c
    obtain ⟨u, hu⟩ := IdeleClassGroup.mk_surjective (𝓞 L) L (Additive.toMul c)
    have hmem : u ∈ IdeleGroup.principalSubgroup (𝓞 L) L
        ⊔ IdeleGroup.sIdeleSubgroup L (placesOverSet K L S) := hsup ▸ Subgroup.mem_top u
    rw [Subgroup.mem_sup] at hmem
    obtain ⟨y, ⟨x, rfl⟩, z, hz, rfl⟩ := hmem
    refine ⟨Additive.ofMul ⟨z, hz⟩, ?_⟩
    refine Additive.toMul.injective ?_
    rw [toMul_sIdeleToIdeleClass]
    rw [← hu, map_mul, IdeleClassGroup.mk_principalEmbedding, one_mul]
    rfl
  exact := by
    intro b
    constructor
    · intro hb
      have hb1 : IdeleClassGroup.mk (𝓞 L) L
          ((Additive.toMul b : IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))
            : IdeleGroup (𝓞 L) L) = 1 := congrArg Additive.toMul hb
      have hmem : ((Additive.toMul b : IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))
          : IdeleGroup (𝓞 L) L)
          ∈ IdeleGroup.principalSubgroup (𝓞 L) L
            ⊓ IdeleGroup.sIdeleSubgroup L (placesOverSet K L S) :=
        ⟨(IdeleClassGroup.mk_eq_one_iff (𝓞 L) L).1 hb1, (Additive.toMul b).2⟩
      rw [IdeleGroup.principalSubgroup_inf_sIdeleSubgroup] at hmem
      obtain ⟨x, hx, hxb⟩ := hmem
      exact ⟨Additive.ofMul ⟨x, hx⟩, Additive.toMul.injective (Subtype.ext hxb)⟩
    · rintro ⟨a, rfl⟩
      refine Additive.toMul.injective ?_
      rw [toMul_sIdeleToIdeleClass, coe_sUnitToSIdele]
      exact IdeleClassGroup.mk_principalEmbedding (𝓞 L) L _

end ShortExact

/-! ## Multiplicativity of the Herbrand quotient along that sequence -/

section Herbrand

variable [IsGalois K L] {σ : L ≃ₐ[K] L}

omit [IsGalois K L] in
/-- **`h(𝕀_{L,S}) = h(O_{L,S}^×) · h(C_L)`.**  The Tate cohomology of the `S`-units is finite
because `O_{L,S}^×` is a finitely generated `ℤ`-module (`NumberField.module_finite_sUnit`);
the finiteness for `C_L` is then *deduced* from the hypothesis for `𝕀_{L,S}`. -/
theorem herbrand_sIdele_eq_mul
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (hsup : IdeleGroup.principalSubgroup (𝓞 L) L
      ⊔ IdeleGroup.sIdeleSubgroup L (placesOverSet K L S) = ⊤)
    [Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ)]
    [Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ)] :
    CyclicTate.herbrand (L ≃ₐ[K] L)
        (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ
      = CyclicTate.herbrand (L ≃ₐ[K] L) (Additive (SUnitGroup K L S)) σ
        * CyclicTate.herbrand (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ := by
  haveI : Finite (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (SUnitGroup K L S)) σ) :=
    CyclicTate.finite_tateH0_of_moduleFinite hgen
  haveI : Finite (CyclicTate.TateH1 (L ≃ₐ[K] L) (Additive (SUnitGroup K L S)) σ) :=
    CyclicTate.finite_tateH1_of_moduleFinite hgen
  have hse := isShortExact_sUnit_sIdele S hsup
  haveI := hse.finite_tateH0_right σ
  haveI := hse.finite_tateH1_right σ
  exact hse.herbrand_eq_mul σ

variable [Fintype S]

/-- **`h(C_L) = [L : K]` for a cyclic extension**, conditional on the value
`h(𝕀_{L,S}) = ∏_{v ∈ S ∪ S_∞} n_v` of the Herbrand quotient of the `S`-ideles.

That hypothesis, `hidele`, is the **only** thing missing: it is the local half of the
computation, obtained from `CyclicTate.herbrand_piUnits` (Shapiro) together with the local
class field theory input `h(L_wˣ) = e(w | v)`.  It is not proved in this repository, and
`hidele` is stated here exactly so that it can be discharged separately.  Everything else —
Dirichlet's `S`-unit theorem in full-lattice form, the Noether-Deuring comparison, the value
`h(O_{L,S}^×) = (∏_v n_v) / n`, and the short exact sequence
`1 → O_{L,S}^× → 𝕀_{L,S} → C_L → 1` — is proved. -/
theorem herbrand_ideleClassGroup_of_herbrand_sIdele
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (hsup : IdeleGroup.principalSubgroup (𝓞 L) L
      ⊔ IdeleGroup.sIdeleSubgroup L (placesOverSet K L S) = ⊤)
    (w₁ : ∀ v : InfinitePlace K, Fibre L v)
    (w₂ : ∀ v : S, FinitePlaceFibre L (v : HeightOneSpectrum (𝓞 K)))
    [Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ)]
    [Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ)]
    (hidele : CyclicTate.herbrand (L ≃ₐ[K] L)
        (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ
      = (∏ v : InfinitePlace K, (Nat.card (stabilizer (L ≃ₐ[K] L) (w₁ v)) : ℚ))
        * ∏ v : S, (Nat.card (stabilizer (L ≃ₐ[K] L) (w₂ v)) : ℚ)) :
    CyclicTate.herbrand (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ
      = (Nat.card (L ≃ₐ[K] L) : ℚ) := by
  have hmul := herbrand_sIdele_eq_mul S hgen hsup
  rw [hidele, herbrand_sUnitGroup S hgen w₁ w₂] at hmul
  have hP : ((∏ v : InfinitePlace K, (Nat.card (stabilizer (L ≃ₐ[K] L) (w₁ v)) : ℚ))
      * ∏ v : S, (Nat.card (stabilizer (L ≃ₐ[K] L) (w₂ v)) : ℚ)) ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ ↦ ?_)
      (Finset.prod_ne_zero_iff.2 fun v _ ↦ ?_)
    · exact_mod_cast (Nat.card_pos (α := stabilizer (L ≃ₐ[K] L) (w₁ v))).ne'
    · exact_mod_cast (Nat.card_pos (α := stabilizer (L ≃ₐ[K] L) (w₂ v))).ne'
  have hn : (Nat.card (L ≃ₐ[K] L) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := L ≃ₐ[K] L)).ne'
  rw [div_mul_eq_mul_div, eq_div_iff hn] at hmul
  exact (mul_left_cancel₀ hP (by linarith [hmul])).symm

end Herbrand

end NumberField