/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.SIdeleSemilocal
public import Iwasawalib.NumberTheory.CFT.HerbrandProduct
public import Iwasawalib.NumberTheory.CFT.HerbrandShapiro
public import Iwasawalib.GroupCohomology.IdeleVanishing
public import Iwasawalib.GroupCohomology.LocalShapiro
public import Iwasawalib.NumberTheory.CFT.SecondInequality

@[expose] public section

/-!
# The Herbrand quotient of the `S`-ideles

Let `L / K` be a cyclic extension of number fields with group `G = ⟨σ⟩`, and let `S` be a
finite set of finite places of `K`.  This file computes the Herbrand quotient of the group
`𝕀_{L,S}` of `S`-ideles in terms of **local** Herbrand quotients:

`h(𝕀_{L,S}) = (∏_{v ∣ ∞} h(D_{w_v}, L_{w_v}^×)) · (∏_{v ∈ S} h(D_{w_v}, L_{w_v}^×))`

(`NumberField.herbrand_sIdele_eq_prod_local`), where `w_v` is a place of `L` above `v` and
`D_{w_v}` its decomposition group.  This is the input `hidele` of
`NumberField.herbrand_ideleClassGroup_of_herbrand_sIdele`, reduced to statements about single
local fields: supplying local class field theory in the form `h(D_w, L_w^×) = #D_w` turns the
right-hand side into `∏_{v ∈ S ∪ S_∞} n_v`, and `h(C_L) = [L : K]` follows.

## The three steps

* **Splitting.**  `𝕀_{L,S} ≃ (𝔸_L^∞)^× × 𝕀_{L,S}^f` (`NumberField.sIdeleProdEquiv`); the
  archimedean factor is a product of semilocal groups
  (`NumberField.infiniteIdeleEquivPi`), and the finite factor is one too
  (`NumberField.finiteSIdeleSemilocalEquiv`, proved in
  `Iwasawalib/NumberTheory/CFT/SIdeleSemilocal.lean`).  Everything here is equivariant.
* **Multiplicativity.**  The Herbrand quotient of a product is the product of the Herbrand
  quotients (`CyclicTate.herbrand_mulProd`, `CyclicTate.herbrand_mulPi`).  The factor over the
  places `v ∉ S` is an **infinite** product, so `CyclicTate.herbrand_pi` does not apply to it;
  what is used instead is that `Ĥ⁰` and `Ĥ¹` commute with arbitrary products
  (`CyclicTate.subsingleton_tateH0_mulPi`, `CyclicTate.subsingleton_tateH1_mulPi`), so that the
  factor is `1` as soon as each of its terms has vanishing Tate cohomology.  That vanishing is
  the unramifiedness hypothesis, and it is an explicit instance hypothesis here; it is *not*
  proved in this repository.
* **Shapiro.**  Each semilocal factor is the corresponding local one:
  `h(Gal(L/K), (∏_{w ∣ v} L_w)^×) = h(D_{w₀}, L_{w₀}^×)`
  (`NumberField.herbrand_localProductUnits` at the finite places, from
  `NumberField.localProductUnitsShapiro`;
  `NumberField.herbrand_infiniteLocalProductUnits` at the archimedean ones, from
  `CyclicTate.herbrand_piUnits`).

## What is assumed and what is proved

Nothing about local fields is proved here.  The local values `h(D_w, L_w^×)` and the vanishing
of the Tate cohomology of `∏_{w ∣ v} O_w^×` at the places outside `S` appear as hypotheses,
and every other step is proved.  In particular the reduction itself — the part that is global,
adelic and equivariant — is complete.

## Main definitions

* `CyclicTate.additiveProdEquiv`, `CyclicTate.additivePiEquiv` : `Additive` commutes with
  products.
* `NumberField.sIdeleProdEquiv` : `𝕀_{L,S} ≃ (𝔸_L^∞)^× × 𝕀_{L,S}^f`.

## Main statements

* `CyclicTate.herbrand_eq_of_mulEquiv`, `CyclicTate.herbrand_mulProd`,
  `CyclicTate.herbrand_mulPi` : multiplicative wrappers for the Herbrand quotient.
* `CyclicTate.subsingleton_tateH0_mulPi`, `CyclicTate.subsingleton_tateH1_mulPi` : vanishing
  passes to arbitrary products.
* `NumberField.herbrand_finiteSIdele`, `NumberField.herbrand_finiteSIdele_of_subsingleton`,
  `NumberField.herbrand_infiniteIdele`, `NumberField.herbrand_sIdele` : the decomposition.
* `NumberField.herbrand_localProductUnits`,
  `NumberField.herbrand_infiniteLocalProductUnits` : Shapiro.
* `NumberField.herbrand_sIdele_eq_prod_local` : **the main result**.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.InfiniteAdeleRing

attribute [local instance] Units.mulDistribMulActionRight

/-! ## Multiplicative wrappers for the Herbrand quotient -/

namespace CyclicTate

section Mul

variable {G : Type*} [Group G] [Fintype G] (σ : G)

/-- `Additive (A × B)` and `Additive A × Additive B` are the same `G`-module. -/
def additiveProdEquiv (A B : Type*) [CommGroup A] [CommGroup B] :
    Additive (A × B) ≃+ Additive A × Additive B where
  toFun x := (Additive.ofMul (Additive.toMul x).1, Additive.ofMul (Additive.toMul x).2)
  invFun z := Additive.ofMul (Additive.toMul z.1, Additive.toMul z.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- `Additive (∀ i, M i)` and `∀ i, Additive (M i)` are the same `G`-module. -/
def additivePiEquiv {ι : Type*} (M : ι → Type*) [∀ i, CommGroup (M i)] :
    Additive (∀ i, M i) ≃+ ∀ i, Additive (M i) where
  toFun x i := Additive.ofMul (Additive.toMul x i)
  invFun z := Additive.ofMul fun i ↦ Additive.toMul (z i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable {A B : Type*} [CommGroup A] [CommGroup B] [MulDistribMulAction G A]
  [MulDistribMulAction G B]

/-- **The Herbrand quotient is invariant under an equivariant multiplicative isomorphism.** -/
theorem herbrand_eq_of_mulEquiv (e : A ≃* B) (he : ∀ (g : G) (a : A), e (g • a) = g • e a) :
    herbrand G (Additive A) σ = herbrand G (Additive B) σ :=
  herbrand_eq_of_addEquiv (MulEquiv.toAdditive e) (fun g a ↦ he g (Additive.toMul a)) σ

theorem finite_tateH0_of_mulEquiv (e : A ≃* B)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a) [Finite (TateH0 G (Additive A) σ)] :
    Finite (TateH0 G (Additive B) σ) :=
  finite_tateH0_of_addEquiv (MulEquiv.toAdditive e) (fun g a ↦ he g (Additive.toMul a)) σ

theorem finite_tateH1_of_mulEquiv (e : A ≃* B)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a) [Finite (TateH1 G (Additive A) σ)] :
    Finite (TateH1 G (Additive B) σ) :=
  finite_tateH1_of_addEquiv (MulEquiv.toAdditive e) (fun g a ↦ he g (Additive.toMul a)) σ

/-- **The Herbrand quotient of a product of two groups.** -/
theorem herbrand_mulProd [Finite (TateH0 G (Additive A) σ)] [Finite (TateH1 G (Additive A) σ)]
    [Finite (TateH0 G (Additive B) σ)] [Finite (TateH1 G (Additive B) σ)] :
    herbrand G (Additive (A × B)) σ
      = herbrand G (Additive A) σ * herbrand G (Additive B) σ := by
  rw [herbrand_eq_of_addEquiv (additiveProdEquiv A B) (fun _ _ ↦ rfl) σ]
  exact herbrand_prod σ

theorem finite_tateH0_mulProd [Finite (TateH0 G (Additive A) σ)]
    [Finite (TateH0 G (Additive B) σ)] : Finite (TateH0 G (Additive (A × B)) σ) :=
  haveI := finite_tateH0_prod (A := Additive A) (B := Additive B) σ
  finite_tateH0_of_addEquiv (additiveProdEquiv A B).symm (fun _ _ ↦ rfl) σ

theorem finite_tateH1_mulProd [Finite (TateH1 G (Additive A) σ)]
    [Finite (TateH1 G (Additive B) σ)] : Finite (TateH1 G (Additive (A × B)) σ) :=
  haveI := finite_tateH1_prod (A := Additive A) (B := Additive B) σ
  finite_tateH1_of_addEquiv (additiveProdEquiv A B).symm (fun _ _ ↦ rfl) σ

/-- **The Herbrand quotient of a finite product of groups.** -/
theorem herbrand_mulPi {ι : Type*} [Fintype ι] (M : ι → Type*) [∀ i, CommGroup (M i)]
    [∀ i, MulDistribMulAction G (M i)] [∀ i, Finite (TateH0 G (Additive (M i)) σ)]
    [∀ i, Finite (TateH1 G (Additive (M i)) σ)] :
    herbrand G (Additive (∀ i, M i)) σ = ∏ i, herbrand G (Additive (M i)) σ := by
  rw [herbrand_eq_of_addEquiv (additivePiEquiv M) (fun _ _ ↦ rfl) σ]
  exact herbrand_pi σ

theorem finite_tateH0_mulPi {ι : Type*} [Fintype ι] (M : ι → Type*) [∀ i, CommGroup (M i)]
    [∀ i, MulDistribMulAction G (M i)] [∀ i, Finite (TateH0 G (Additive (M i)) σ)] :
    Finite (TateH0 G (Additive (∀ i, M i)) σ) :=
  finite_tateH0_of_addEquiv (additivePiEquiv M).symm (fun _ _ ↦ rfl) σ

theorem finite_tateH1_mulPi {ι : Type*} [Fintype ι] (M : ι → Type*) [∀ i, CommGroup (M i)]
    [∀ i, MulDistribMulAction G (M i)] [∀ i, Finite (TateH1 G (Additive (M i)) σ)] :
    Finite (TateH1 G (Additive (∀ i, M i)) σ) :=
  finite_tateH1_of_addEquiv (additivePiEquiv M).symm (fun _ _ ↦ rfl) σ

/-- **A product of groups with vanishing Tate cohomology has trivial `Ĥ⁰`**, for an index type
of any size. -/
theorem subsingleton_tateH0_mulPi {ι : Type*} (M : ι → Type*) [∀ i, CommGroup (M i)]
    [∀ i, MulDistribMulAction G (M i)] [∀ i, Subsingleton (TateH0 G (Additive (M i)) σ)] :
    Subsingleton (TateH0 G (Additive (∀ i, M i)) σ) := by
  haveI : Subsingleton (TateH0 G (∀ i, Additive (M i)) σ) :=
    (tateH0PiEquiv (M := fun i ↦ Additive (M i)) σ).injective.subsingleton
  exact (tateH0Equiv (additivePiEquiv M) (fun _ _ ↦ rfl) σ).injective.subsingleton

/-- **A product of groups with vanishing Tate cohomology has trivial `Ĥ¹`.** -/
theorem subsingleton_tateH1_mulPi {ι : Type*} (M : ι → Type*) [∀ i, CommGroup (M i)]
    [∀ i, MulDistribMulAction G (M i)] [∀ i, Subsingleton (TateH1 G (Additive (M i)) σ)] :
    Subsingleton (TateH1 G (Additive (∀ i, M i)) σ) := by
  haveI : Subsingleton (TateH1 G (∀ i, Additive (M i)) σ) :=
    (tateH1PiEquiv (M := fun i ↦ Additive (M i)) σ).injective.subsingleton
  exact (tateH1Equiv (additivePiEquiv M) (fun _ _ ↦ rfl) σ).injective.subsingleton

end Mul

end CyclicTate

/-! ## The Herbrand quotient of the `S`-ideles -/

namespace NumberField

attribute [local instance] NumberField.galInfiniteAdeleMulSemiringAction
  NumberField.galIdeleMulDistribMulAction

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {S : Set (HeightOneSpectrum (𝓞 K))} {σ : L ≃ₐ[K] L}

/-- **The Herbrand quotient of the finite `S`-ideles is the product of the semilocal Herbrand
quotients.**

`h((𝕀_{L,S})^f) = (∏_{v ∈ S} h((∏_{w ∣ v} L_w)^×)) · h(∏_{v ∉ S} (∏_{w ∣ v} O_w)^×)`.

Each factor with `v ∈ S` is a *semilocal* Herbrand quotient, reduced to the local one
`h(D_w, L_w^×)` by `NumberField.localProductUnitsShapiro`; the remaining factor is `1` as soon
as the Tate cohomology of `∏_{w ∣ v} O_w^×` vanishes for every `v ∉ S`, which is the
unramifiedness input (`NumberField.herbrand_finiteSIdele_of_subsingleton`). -/
theorem herbrand_finiteSIdele [IsGalois K L] [Fintype S]
    [∀ v : S, Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)]
    [∀ v : S, Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)]
    [Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (∀ v : ↥(Sᶜ), localProductIntegerUnits K L
        (v : HeightOneSpectrum (𝓞 K)))) σ)]
    [Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (∀ v : ↥(Sᶜ), localProductIntegerUnits K L
        (v : HeightOneSpectrum (𝓞 K)))) σ)] :
    CyclicTate.herbrand (L ≃ₐ[K] L)
        (Additive (FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S))) σ
      = (∏ v : S, CyclicTate.herbrand (L ≃ₐ[K] L)
            (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)
        * CyclicTate.herbrand (L ≃ₐ[K] L)
            (Additive (∀ v : ↥(Sᶜ), localProductIntegerUnits K L
              (v : HeightOneSpectrum (𝓞 K)))) σ := by
  haveI := CyclicTate.finite_tateH0_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : S ↦ (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ)
  haveI := CyclicTate.finite_tateH1_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : S ↦ (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ)
  rw [CyclicTate.herbrand_eq_of_mulEquiv σ (finiteSIdeleSemilocalEquiv (Set.toFinite S))
      (fun g u ↦ finiteSIdeleSemilocalEquiv_smul (Set.toFinite S) g u),
    CyclicTate.herbrand_mulProd σ, CyclicTate.herbrand_mulPi σ]

/-- **The unramified form of the computation.**  If the Tate cohomology of `∏_{w ∣ v} O_w^×`
vanishes for every finite place `v ∉ S` of `K` — which is the case when `v` is unramified in
`L` — then the finite `S`-ideles have

`h((𝕀_{L,S})^f) = ∏_{v ∈ S} h((∏_{w ∣ v} L_w)^×)`. -/
theorem herbrand_finiteSIdele_of_subsingleton [IsGalois K L] [Fintype S]
    [∀ v : S, Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)]
    [∀ v : S, Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)]
    [∀ v : ↥(Sᶜ), Subsingleton (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ)]
    [∀ v : ↥(Sᶜ), Subsingleton (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ)] :
    CyclicTate.herbrand (L ≃ₐ[K] L)
        (Additive (FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S))) σ
      = ∏ v : S, CyclicTate.herbrand (L ≃ₐ[K] L)
          (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ := by
  haveI := CyclicTate.subsingleton_tateH0_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : ↥(Sᶜ) ↦ localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))
  haveI := CyclicTate.subsingleton_tateH1_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : ↥(Sᶜ) ↦ localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))
  haveI : Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (∀ v : ↥(Sᶜ), localProductIntegerUnits K L
        (v : HeightOneSpectrum (𝓞 K)))) σ) := Finite.of_subsingleton
  haveI : Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (∀ v : ↥(Sᶜ), localProductIntegerUnits K L
        (v : HeightOneSpectrum (𝓞 K)))) σ) := Finite.of_subsingleton
  rw [herbrand_finiteSIdele, CyclicTate.herbrand_eq_one_of_subsingleton, mul_one]

/-! ## Splitting off the archimedean factor -/

variable (K L S)

/-- **The `S`-ideles split into their archimedean and finite parts:**
`𝕀_{L,S} ≃ (𝔸_L^∞)^× × (𝕀_{L,S})^f`.  The archimedean components of an `S`-idele are
unconstrained, so the archimedean factor is the whole group `(𝔸_L^∞)^×`. -/
def sIdeleProdEquiv :
    IdeleGroup.sIdeleSubgroup L (placesOverSet K L S) ≃*
      (InfiniteAdeleRing L)ˣ × FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S) where
  toFun u := ((ideleEquivProd L (u : IdeleGroup (𝓞 L) L)).1,
    ⟨(ideleEquivProd L (u : IdeleGroup (𝓞 L) L)).2, u.2⟩)
  invFun z := ⟨(ideleEquivProd L).symm
      (z.1, (z.2 : (FiniteAdeleRing (𝓞 L) L)ˣ)), z.2.2⟩
  left_inv u := by
    refine Subtype.ext ?_
    show (ideleEquivProd L).symm (ideleEquivProd L (u : IdeleGroup (𝓞 L) L))
      = (u : IdeleGroup (𝓞 L) L)
    rw [MulEquiv.symm_apply_apply]
  right_inv z := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show (ideleEquivProd L ((ideleEquivProd L).symm
        (z.1, (z.2 : (FiniteAdeleRing (𝓞 L) L)ˣ)))).1 = z.1
      rw [MulEquiv.apply_symm_apply]
    · show (ideleEquivProd L ((ideleEquivProd L).symm
        (z.1, (z.2 : (FiniteAdeleRing (𝓞 L) L)ˣ)))).2
        = (z.2 : (FiniteAdeleRing (𝓞 L) L)ˣ)
      rw [MulEquiv.apply_symm_apply]
  map_mul' u w := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show (ideleEquivProd L ((u : IdeleGroup (𝓞 L) L) * (w : IdeleGroup (𝓞 L) L))).1 = _
      rw [map_mul]
      rfl
    · show (ideleEquivProd L ((u : IdeleGroup (𝓞 L) L) * (w : IdeleGroup (𝓞 L) L))).2 = _
      rw [map_mul]
      rfl

variable {K L S}

/-- The splitting of the `S`-ideles into archimedean and finite parts is
`Gal(L/K)`-equivariant. -/
theorem sIdeleProdEquiv_smul (σ : L ≃ₐ[K] L)
    (u : IdeleGroup.sIdeleSubgroup L (placesOverSet K L S)) :
    sIdeleProdEquiv K L S (σ • u) = σ • sIdeleProdEquiv K L S u := by
  have hsmul : ((σ • u : IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))
      : IdeleGroup (𝓞 L) L) = σ • (u : IdeleGroup (𝓞 L) L) := rfl
  refine Prod.ext ?_ (Subtype.ext ?_)
  · show (ideleEquivProd L ((σ • u : IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))
      : IdeleGroup (𝓞 L) L)).1 = _
    rw [hsmul, ideleEquivProd_smul]
    rfl
  · show (ideleEquivProd L ((σ • u : IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))
      : IdeleGroup (𝓞 L) L)).2 = _
    rw [hsmul, ideleEquivProd_smul]
    rfl

/-! ## The Herbrand quotient of the `S`-ideles -/

/-- **The Herbrand quotient of the archimedean ideles is the product of the semilocal
quotients:** `h((𝔸_L^∞)^×) = ∏_{v ∣ ∞} h((∏_{w ∣ v} L_w)^×)`. -/
theorem herbrand_infiniteIdele [IsGalois K L]
    [∀ v : InfinitePlace K, Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ)]
    [∀ v : InfinitePlace K, Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ)] :
    CyclicTate.herbrand (L ≃ₐ[K] L) (Additive (InfiniteAdeleRing L)ˣ) σ
      = ∏ v : InfinitePlace K, CyclicTate.herbrand (L ≃ₐ[K] L)
          (Additive (InfiniteLocalProduct L v)ˣ) σ := by
  rw [CyclicTate.herbrand_eq_of_mulEquiv σ (infiniteIdeleEquivPi K L)
      (fun g u ↦ infiniteIdeleEquivPi_smul g u), CyclicTate.herbrand_mulPi σ]

/-- **The Herbrand quotient of the `S`-ideles of a cyclic extension:**

`h(𝕀_{L,S}) = (∏_{v ∣ ∞} h((∏_{w ∣ v} L_w)^×)) · (∏_{v ∈ S} h((∏_{w ∣ v} L_w)^×))`,

assuming that the Tate cohomology of `∏_{w ∣ v} O_w^×` vanishes at every finite place
`v ∉ S` of `K`.  That assumption is the unramifiedness input: it holds at the places that are
unramified in `L`, and every ramified place may be put into `S`.

This is the reduction of `h(𝕀_{L,S})` to purely **local** Herbrand quotients.  Each factor
`h((∏_{w ∣ v} L_w)^×)` is a semilocal one, identified with the local `h(D_w, L_w^×)` by
Shapiro's lemma (`NumberField.localProductUnitsShapiro` for the finite places,
`NumberField.InfiniteAdeleRing.infiniteLocalUnitsShapiro` for the archimedean ones). -/
theorem herbrand_sIdele [IsGalois K L] [Fintype S]
    [∀ v : InfinitePlace K, Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ)]
    [∀ v : InfinitePlace K, Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ)]
    [∀ v : S, Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)]
    [∀ v : S, Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)]
    [∀ v : ↥(Sᶜ), Subsingleton (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ)]
    [∀ v : ↥(Sᶜ), Subsingleton (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ)] :
    CyclicTate.herbrand (L ≃ₐ[K] L)
        (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ
      = (∏ v : InfinitePlace K, CyclicTate.herbrand (L ≃ₐ[K] L)
            (Additive (InfiniteLocalProduct L v)ˣ) σ)
        * ∏ v : S, CyclicTate.herbrand (L ≃ₐ[K] L)
            (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ := by
  haveI := CyclicTate.finite_tateH0_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : InfinitePlace K ↦ (InfiniteLocalProduct L v)ˣ)
  haveI := CyclicTate.finite_tateH1_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : InfinitePlace K ↦ (InfiniteLocalProduct L v)ˣ)
  haveI : Finite (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (InfiniteAdeleRing L)ˣ) σ) :=
    CyclicTate.finite_tateH0_of_mulEquiv σ (infiniteIdeleEquivPi K L).symm
      (fun g u ↦ ((infiniteIdeleEquivPi K L).eq_symm_apply.2
        (by rw [infiniteIdeleEquivPi_smul, MulEquiv.apply_symm_apply])).symm)
  haveI : Finite (CyclicTate.TateH1 (L ≃ₐ[K] L) (Additive (InfiniteAdeleRing L)ˣ) σ) :=
    CyclicTate.finite_tateH1_of_mulEquiv σ (infiniteIdeleEquivPi K L).symm
      (fun g u ↦ ((infiniteIdeleEquivPi K L).eq_symm_apply.2
        (by rw [infiniteIdeleEquivPi_smul, MulEquiv.apply_symm_apply])).symm)
  haveI := CyclicTate.subsingleton_tateH0_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : ↥(Sᶜ) ↦ localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))
  haveI := CyclicTate.subsingleton_tateH1_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : ↥(Sᶜ) ↦ localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))
  haveI : Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (∀ v : ↥(Sᶜ), localProductIntegerUnits K L
        (v : HeightOneSpectrum (𝓞 K)))) σ) := Finite.of_subsingleton
  haveI : Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (∀ v : ↥(Sᶜ), localProductIntegerUnits K L
        (v : HeightOneSpectrum (𝓞 K)))) σ) := Finite.of_subsingleton
  haveI := CyclicTate.finite_tateH0_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : S ↦ (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ)
  haveI := CyclicTate.finite_tateH1_mulPi (G := L ≃ₐ[K] L) σ
    (fun v : S ↦ (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ)
  haveI := CyclicTate.finite_tateH0_mulProd (G := L ≃ₐ[K] L) (σ := σ)
    (A := ∀ v : S, (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ)
    (B := ∀ v : ↥(Sᶜ), localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))
  haveI := CyclicTate.finite_tateH1_mulProd (G := L ≃ₐ[K] L) (σ := σ)
    (A := ∀ v : S, (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ)
    (B := ∀ v : ↥(Sᶜ), localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))
  haveI : Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S))) σ) :=
    CyclicTate.finite_tateH0_of_mulEquiv σ (finiteSIdeleSemilocalEquiv (Set.toFinite S)).symm
      (fun g u ↦ ((finiteSIdeleSemilocalEquiv (Set.toFinite S)).eq_symm_apply.2
        (by rw [finiteSIdeleSemilocalEquiv_smul, MulEquiv.apply_symm_apply])).symm)
  haveI : Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S))) σ) :=
    CyclicTate.finite_tateH1_of_mulEquiv σ (finiteSIdeleSemilocalEquiv (Set.toFinite S)).symm
      (fun g u ↦ ((finiteSIdeleSemilocalEquiv (Set.toFinite S)).eq_symm_apply.2
        (by rw [finiteSIdeleSemilocalEquiv_smul, MulEquiv.apply_symm_apply])).symm)
  rw [CyclicTate.herbrand_eq_of_mulEquiv σ (sIdeleProdEquiv K L S)
      (fun g u ↦ sIdeleProdEquiv_smul g u), CyclicTate.herbrand_mulProd σ,
    herbrand_infiniteIdele, herbrand_finiteSIdele_of_subsingleton]

/-! ## Shapiro: the semilocal factors are local -/

section Shapiro

open CategoryTheory

/-- **The semilocal Herbrand quotient at a finite place is the local one.**

`h(Gal(L/K), (∏_{w ∣ v} L_w)^×) = h(D_{w₀}, L_{w₀}^×)`.

This is `NumberField.localProductUnitsShapiro`, Shapiro's lemma for the local factors, read
through the identification `CyclicTate.herbrand_eq_card_groupCohomology` of the Herbrand
quotient with `#H² / #H¹`.  The `CommGroup` structures that Mathlib's finite-cyclic machinery
needs on `Gal(L/K)` and on `D_{w₀}` are manufactured from the generation hypotheses by
`CyclicTate.commGroupOfGen`. -/
theorem herbrand_localProductUnits [IsGalois K L] {v : HeightOneSpectrum (𝓞 K)}
    {w₀ : HeightOneSpectrum (𝓞 L)} (hw₀ : w₀ ∈ placesOver K L v)
    [Fintype (decompositionGroup K L w₀)]
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    {τ : decompositionGroup K L w₀} (hτ : ∀ d : decompositionGroup K L w₀, ∃ m : ℕ, τ ^ m = d) :
    CyclicTate.herbrand (L ≃ₐ[K] L) (Additive (LocalProduct K L v)ˣ) σ
      = CyclicTate.herbrand (decompositionGroup K L w₀)
          (Additive (w₀.adicCompletion L)ˣ) τ := by
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  letI : CommGroup (decompositionGroup K L w₀) := CyclicTate.commGroupOfGen hτ
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  have hτz : ∀ d : decompositionGroup K L w₀, d ∈ Subgroup.zpowers τ := fun d ↦ by
    obtain ⟨m, rfl⟩ := hτ d
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers τ) m
  rw [CyclicTate.herbrand_eq_card_groupCohomology
      (M := Additive (LocalProduct K L v)ˣ) σ hσ,
    CyclicTate.herbrand_eq_card_groupCohomology
      (M := Additive (w₀.adicCompletion L)ˣ) τ hτz]
  have h : ∀ n : ℕ,
      Nat.card (groupCohomology
          (CyclicTate.rep (L ≃ₐ[K] L) (Additive (LocalProduct K L v)ˣ)) n : ModuleCat ℤ)
        = Nat.card (groupCohomology
          (CyclicTate.rep (decompositionGroup K L w₀)
            (Additive (w₀.adicCompletion L)ˣ)) n : ModuleCat ℤ) := fun n ↦
    Nat.card_congr (localProductUnitsShapiro hw₀ n).toLinearEquiv.toEquiv
  rw [h 2, h 1]

/-- **The semilocal Herbrand quotient at an archimedean place is the local one.**

`h(Gal(L/K), (∏_{w ∣ v} L_w)^×) = h(D_{w₀}, L_{w₀}^×)` for an infinite place `v` of `K`.

This is `CyclicTate.herbrand_piUnits`, the dependent form of Shapiro's lemma for the Herbrand
quotient, applied to the equivariant family
`NumberField.InfiniteAdeleRing.infiniteFamily`. -/
theorem herbrand_infiniteLocalProductUnits [IsGalois K L] {v : InfinitePlace K}
    {w₀ : Fibre L v} [Fintype (MulAction.stabilizer (L ≃ₐ[K] L) w₀)]
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    {τ : MulAction.stabilizer (L ≃ₐ[K] L) w₀}
    (hτ : ∀ d : MulAction.stabilizer (L ≃ₐ[K] L) w₀, ∃ m : ℕ, τ ^ m = d) :
    CyclicTate.herbrand (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v)ˣ) σ
      = CyclicTate.herbrand (MulAction.stabilizer (L ≃ₐ[K] L) w₀)
          (Additive ((w₀ : InfinitePlace L).Completion)ˣ) τ := by
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  have hτz : ∀ d : MulAction.stabilizer (L ≃ₐ[K] L) w₀, d ∈ Subgroup.zpowers τ := fun d ↦ by
    obtain ⟨m, rfl⟩ := hτ d
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers τ) m
  exact CyclicTate.herbrand_piUnits (infiniteFamily L v)
    (infiniteFamily_isStabilizerAction w₀) infiniteFamily_isPiAction hσ hτz

/-! ## The `S`-ideles in terms of purely local Herbrand quotients -/

/-- **The Herbrand quotient of the `S`-ideles of a cyclic extension, in purely local terms:**

`h(𝕀_{L,S}) = (∏_{v ∣ ∞} h(D_{w_v}, L_{w_v}^×)) · (∏_{v ∈ S} h(D_{w_v}, L_{w_v}^×))`,

where `w_v` is a chosen place of `L` above `v` and `D_{w_v}` its decomposition group.  The
hypotheses are: `L / K` is cyclic with generator `σ`; each decomposition group is cyclic with
the chosen generator `τ₁ v`, `τ₂ v`; and the Tate cohomology of `∏_{w ∣ v} O_w^×` vanishes at
every finite place `v ∉ S`, which holds at the unramified places.

This is the reduction of the global quantity `h(𝕀_{L,S})` to the local ones.  Supplying the
local class field theory input `h(D_w, L_w^×) = #D_w` turns the right-hand side into
`∏_{v ∈ S ∪ S_∞} n_v`, which is exactly the hypothesis `hidele` of
`NumberField.herbrand_ideleClassGroup_of_herbrand_sIdele`. -/
theorem herbrand_sIdele_eq_prod_local [IsGalois K L] [Fintype S]
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (w₁ : ∀ v : InfinitePlace K, Fibre L v)
    [∀ v : InfinitePlace K, Fintype (MulAction.stabilizer (L ≃ₐ[K] L) (w₁ v))]
    (τ₁ : ∀ v : InfinitePlace K, MulAction.stabilizer (L ≃ₐ[K] L) (w₁ v))
    (hτ₁ : ∀ (v : InfinitePlace K) (d : MulAction.stabilizer (L ≃ₐ[K] L) (w₁ v)),
      ∃ m : ℕ, (τ₁ v) ^ m = d)
    (w₂ : ∀ v : S, HeightOneSpectrum (𝓞 L))
    (hw₂ : ∀ v : S, w₂ v ∈ placesOver K L (v : HeightOneSpectrum (𝓞 K)))
    [∀ v : S, Fintype (decompositionGroup K L (w₂ v))]
    (τ₂ : ∀ v : S, decompositionGroup K L (w₂ v))
    (hτ₂ : ∀ (v : S) (d : decompositionGroup K L (w₂ v)), ∃ m : ℕ, (τ₂ v) ^ m = d)
    [∀ v : InfinitePlace K, Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ)]
    [∀ v : InfinitePlace K, Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (InfiniteLocalProduct L v)ˣ) σ)]
    [∀ v : S, Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)]
    [∀ v : S, Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)]
    [∀ v : ↥(Sᶜ), Subsingleton (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ)]
    [∀ v : ↥(Sᶜ), Subsingleton (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ)] :
    CyclicTate.herbrand (L ≃ₐ[K] L)
        (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ
      = (∏ v : InfinitePlace K, CyclicTate.herbrand
            (MulAction.stabilizer (L ≃ₐ[K] L) (w₁ v))
            (Additive ((w₁ v : InfinitePlace L).Completion)ˣ) (τ₁ v))
        * ∏ v : S, CyclicTate.herbrand (decompositionGroup K L (w₂ v))
            (Additive ((w₂ v).adicCompletion L)ˣ) (τ₂ v) := by
  rw [herbrand_sIdele]
  congr 1
  · exact Finset.prod_congr rfl fun v _ ↦
      herbrand_infiniteLocalProductUnits hgen (hτ₁ v)
  · exact Finset.prod_congr rfl fun v _ ↦
      herbrand_localProductUnits (hw₂ v) hgen (hτ₂ v)

end Shapiro

end NumberField
