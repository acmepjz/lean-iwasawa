/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.SemilocalDecomposition
public import Iwasawalib.NumberTheory.CFT.InfiniteSemilocalDecomposition
public import Iwasawalib.NumberTheory.CFT.IdeleClassHerbrandValue

@[expose] public section

/-!
# The semilocal decomposition of the Tate cohomology of the idele group

`Ĥ⁰(Gal(L/K), 𝕀_{L,S}) ≅ (∏_{v ∣ ∞} Ĥ⁰(Gal, (∏_{w ∣ v} L_w)^×))
                          × (∏_{v ∈ S} Ĥ⁰(Gal, (∏_{w ∣ v} L_w)^×))
                          × Ĥ⁰(Gal, ∏_{v ∉ S} (∏_{w ∣ v} O_w)^×)`

and, composing with `Iwasawalib/NumberTheory/CFT/SemilocalDecomposition.lean` and
`Iwasawalib/NumberTheory/CFT/InfiniteSemilocalDecomposition.lean`, each semilocal factor is the
Tate cohomology of a **single** local field under its decomposition group.  When `L / K` is
unramified outside `S` the last factor vanishes and one gets the decomposition in the form that
the sum-of-local-invariants map consumes:

`Ĥ⁰(Gal(L/K), 𝕀_{L,S}) ≅ (∏_{v ∣ ∞} Ĥ⁰(D_{w(v)}, L_{w(v)}^×)) × (∏_{v ∈ S} Ĥ⁰(D_{w(v)}, L_{w(v)}^×))`.

Everything here is an assembly of existing equivariant isomorphisms of *modules* —
`NumberField.sIdeleProdEquiv`, `NumberField.infiniteIdeleEquivPi`,
`NumberField.finiteSIdeleSemilocalEquiv` — with the `Ĥ` functoriality of
`Iwasawalib/NumberTheory/CFT/HerbrandProduct.lean`.  The same assembly was already performed in
`Iwasawalib/NumberTheory/CFT/IdeleClassHerbrandValue.lean`, but only in the `Finite` and
`Subsingleton` registers, which lose the map.

## Main definitions

* `CyclicTate.tateH0ProdEquiv`, `CyclicTate.tateH1ProdEquiv` : `Ĥ` of a binary product.
* `CyclicTate.tateH0MulProdEquiv`, `CyclicTate.tateH0MulPiEquiv` : the multiplicative forms.
* `NumberField.tateH0SIdeleEquiv` : the decomposition of `Ĥ⁰(Gal(L/K), 𝕀_{L,S})`.
* `NumberField.tateH0SIdeleEquivOfUnramified` : the same with the outside-`S` factor removed.
-/

noncomputable section


open MulAction CyclicTate

namespace CyclicTate

/-! ## The Tate cohomology of a binary product -/

section Prod

variable {G : Type*} [Group G] [Fintype G] {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  [DistribMulAction G A] [DistribMulAction G B]

theorem normHom_prod_fst (x : A × B) : (normHom G (A × B) x).1 = normHom G A x.1 := by
  simp only [normHom_apply]
  exact Prod.fst_sum

theorem normHom_prod_snd (x : A × B) : (normHom G (A × B) x).2 = normHom G B x.2 := by
  simp only [normHom_apply]
  exact Prod.snd_sum

variable (σ : G)

/-- The componentwise class map `(A × B)^σ → Ĥ⁰(A) × Ĥ⁰(B)`. -/
def prodTateH0Hom : kerSub G (A × B) σ →+ TateH0 G A σ × TateH0 G B σ where
  toFun x := (TateH0.mk σ (x := (x : A × B).1) (congrArg Prod.fst (mem_kerSub.1 x.2)),
    TateH0.mk σ (x := (x : A × B).2) (congrArg Prod.snd (mem_kerSub.1 x.2)))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem prodTateH0Hom_surjective : Function.Surjective (prodTateH0Hom (A := A) (B := B) σ) := by
  rintro ⟨s, t⟩
  obtain ⟨a, ha, rfl⟩ := TateH0.mk_surjective s
  obtain ⟨b, hb, rfl⟩ := TateH0.mk_surjective t
  exact ⟨⟨(a, b), mem_kerSub.2 (Prod.ext ha hb)⟩, rfl⟩

theorem ker_prodTateH0Hom :
    (prodTateH0Hom (A := A) (B := B) σ).ker
      = (rangeNorm G (A × B)).addSubgroupOf (kerSub G (A × B) σ) := by
  ext x
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (TateH0.mk_eq_zero_iff (σ := σ)
      (congrArg Prod.fst (mem_kerSub.1 x.2))).1 (congrArg Prod.fst h)
    obtain ⟨b, hb⟩ := (TateH0.mk_eq_zero_iff (σ := σ)
      (congrArg Prod.snd (mem_kerSub.1 x.2))).1 (congrArg Prod.snd h)
    exact mem_rangeNorm.2 ⟨(a, b), Prod.ext ((normHom_prod_fst (a, b)).trans ha)
      ((normHom_prod_snd (a, b)).trans hb)⟩
  · intro h
    obtain ⟨y, hy⟩ := mem_rangeNorm.1 h
    exact Prod.ext
      ((TateH0.mk_eq_zero_iff (σ := σ) (congrArg Prod.fst (mem_kerSub.1 x.2))).2
        ⟨y.1, (normHom_prod_fst y).symm.trans (congrArg Prod.fst hy)⟩)
      ((TateH0.mk_eq_zero_iff (σ := σ) (congrArg Prod.snd (mem_kerSub.1 x.2))).2
        ⟨y.2, (normHom_prod_snd y).symm.trans (congrArg Prod.snd hy)⟩)

/-- **`Ĥ⁰` commutes with binary products.** -/
def tateH0ProdEquiv : TateH0 G (A × B) σ ≃+ TateH0 G A σ × TateH0 G B σ :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_prodTateH0Hom (A := A) (B := B) σ).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (prodTateH0Hom_surjective (A := A) (B := B) σ))

/-- The componentwise class map `ker N → Ĥ¹(A) × Ĥ¹(B)`. -/
def prodTateH1Hom : kerNorm G (A × B) →+ TateH1 G A σ × TateH1 G B σ where
  toFun x := (TateH1.mk σ (x := (x : A × B).1)
      ((normHom_prod_fst _).symm.trans (congrArg Prod.fst (mem_kerNorm.1 x.2))),
    TateH1.mk σ (x := (x : A × B).2)
      ((normHom_prod_snd _).symm.trans (congrArg Prod.snd (mem_kerNorm.1 x.2))))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem prodTateH1Hom_surjective : Function.Surjective (prodTateH1Hom (A := A) (B := B) σ) := by
  rintro ⟨s, t⟩
  obtain ⟨a, ha, rfl⟩ := TateH1.mk_surjective s
  obtain ⟨b, hb, rfl⟩ := TateH1.mk_surjective t
  refine ⟨⟨(a, b), mem_kerNorm.2 (Prod.ext ((normHom_prod_fst (a, b)).trans ha)
    ((normHom_prod_snd (a, b)).trans hb))⟩, rfl⟩

theorem ker_prodTateH1Hom :
    (prodTateH1Hom (A := A) (B := B) σ).ker
      = (rangeSub G (A × B) σ).addSubgroupOf (kerNorm G (A × B)) := by
  ext x
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (TateH1.mk_eq_zero_iff (σ := σ)
      ((normHom_prod_fst _).symm.trans (congrArg Prod.fst (mem_kerNorm.1 x.2)))).1
      (congrArg Prod.fst h)
    obtain ⟨b, hb⟩ := (TateH1.mk_eq_zero_iff (σ := σ)
      ((normHom_prod_snd _).symm.trans (congrArg Prod.snd (mem_kerNorm.1 x.2)))).1
      (congrArg Prod.snd h)
    exact mem_rangeSub.2 ⟨(a, b), Prod.ext ha hb⟩
  · intro h
    obtain ⟨y, hy⟩ := mem_rangeSub.1 h
    exact Prod.ext
      ((TateH1.mk_eq_zero_iff (σ := σ)
        ((normHom_prod_fst _).symm.trans (congrArg Prod.fst (mem_kerNorm.1 x.2)))).2
        ⟨y.1, congrArg Prod.fst hy⟩)
      ((TateH1.mk_eq_zero_iff (σ := σ)
        ((normHom_prod_snd _).symm.trans (congrArg Prod.snd (mem_kerNorm.1 x.2)))).2
        ⟨y.2, congrArg Prod.snd hy⟩)

/-- **`Ĥ¹` commutes with binary products.** -/
def tateH1ProdEquiv : TateH1 G (A × B) σ ≃+ TateH1 G A σ × TateH1 G B σ :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_prodTateH1Hom (A := A) (B := B) σ).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (prodTateH1Hom_surjective (A := A) (B := B) σ))

end Prod

/-! ## The multiplicative forms -/

section Mul

variable {G : Type*} [Group G] [Fintype G] (σ : G)

attribute [local instance] Additive.distribMulActionOfMulDistrib

variable {A B : Type*} [CommGroup A] [CommGroup B] [MulDistribMulAction G A]
  [MulDistribMulAction G B]

/-- **`Ĥ⁰` commutes with binary products**, multiplicatively. -/
def tateH0MulProdEquiv :
    TateH0 G (Additive (A × B)) σ ≃+ TateH0 G (Additive A) σ × TateH0 G (Additive B) σ :=
  (tateH0Equiv (additiveProdEquiv A B) (fun _ _ ↦ rfl) σ).trans
    (tateH0ProdEquiv (A := Additive A) (B := Additive B) σ)

/-- **`Ĥ¹` commutes with binary products**, multiplicatively. -/
def tateH1MulProdEquiv :
    TateH1 G (Additive (A × B)) σ ≃+ TateH1 G (Additive A) σ × TateH1 G (Additive B) σ :=
  (tateH1Equiv (additiveProdEquiv A B) (fun _ _ ↦ rfl) σ).trans
    (tateH1ProdEquiv (A := Additive A) (B := Additive B) σ)

variable {ι : Type*} (M : ι → Type*) [∀ i, CommGroup (M i)] [∀ i, MulDistribMulAction G (M i)]

/-- **`Ĥ⁰` commutes with products**, multiplicatively.  The index type is arbitrary. -/
def tateH0MulPiEquiv :
    TateH0 G (Additive (∀ i, M i)) σ ≃+ ∀ i, TateH0 G (Additive (M i)) σ :=
  (tateH0Equiv (additivePiEquiv M) (fun _ _ ↦ rfl) σ).trans
    (tateH0PiEquiv (M := fun i ↦ Additive (M i)) σ)

/-- **`Ĥ¹` commutes with products**, multiplicatively. -/
def tateH1MulPiEquiv :
    TateH1 G (Additive (∀ i, M i)) σ ≃+ ∀ i, TateH1 G (Additive (M i)) σ :=
  (tateH1Equiv (additivePiEquiv M) (fun _ _ ↦ rfl) σ).trans
    (tateH1PiEquiv (M := fun i ↦ Additive (M i)) σ)

end Mul

end CyclicTate

/-! ## Dropping a trivial factor -/

namespace AddEquiv

/-- A product with a trivial group is the other factor. -/
def prodSubsingletonRight (X T : Type*) [AddGroup X] [AddGroup T] [Subsingleton T] :
    X × T ≃+ X where
  toFun := Prod.fst
  invFun x := (x, 0)
  left_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_add' _ _ := rfl

end AddEquiv

/-! ## The decomposition of the Tate cohomology of the ideles -/

namespace NumberField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.InfiniteAdeleRing

attribute [local instance] NumberField.galInfiniteAdeleMulSemiringAction
  NumberField.galIdeleMulDistribMulAction Units.mulDistribMulActionRight

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {S : Set (HeightOneSpectrum (𝓞 K))} {σ : L ≃ₐ[K] L} [Fintype (L ≃ₐ[K] L)]

/-- **The semilocal decomposition of `Ĥ⁰` of the finite `S`-ideles**:

`Ĥ⁰(Gal(L/K), 𝕀^f_{L,S}) ≅ (∏_{v ∈ S} Ĥ⁰(Gal(L/K), (∏_{w ∣ v} L_w)^×))
                            × Ĥ⁰(Gal(L/K), ∏_{v ∉ S} (∏_{w ∣ v} O_w)^×)`.

The module isomorphism is `NumberField.finiteSIdeleSemilocalEquiv`; the cohomological content
is that `Ĥ⁰` commutes with products. -/
def tateH0FiniteSIdeleEquiv (hS : S.Finite) :
    TateH0 (L ≃ₐ[K] L)
        (Additive (FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S))) σ
      ≃+ (∀ v : S, TateH0 (L ≃ₐ[K] L)
            (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)
        × TateH0 (L ≃ₐ[K] L) (Additive (∀ v : ↥(Sᶜ),
            localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ :=
  (CyclicTate.tateH0EquivOfMulEquiv (finiteSIdeleSemilocalEquiv hS)
      (fun g u ↦ finiteSIdeleSemilocalEquiv_smul hS g u) σ).trans
    ((CyclicTate.tateH0MulProdEquiv σ).trans
      ((CyclicTate.tateH0MulPiEquiv σ
        (fun v : S ↦ (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ)).prodCongr
          (AddEquiv.refl _)))

/-- **The semilocal decomposition of `Ĥ¹` of the finite `S`-ideles.** -/
def tateH1FiniteSIdeleEquiv (hS : S.Finite) :
    TateH1 (L ≃ₐ[K] L)
        (Additive (FiniteAdeleRing.sIdeleSubgroup L (placesOverSet K L S))) σ
      ≃+ (∀ v : S, TateH1 (L ≃ₐ[K] L)
            (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)
        × TateH1 (L ≃ₐ[K] L) (Additive (∀ v : ↥(Sᶜ),
            localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ :=
  (CyclicTate.tateH1EquivOfMulEquiv (finiteSIdeleSemilocalEquiv hS)
      (fun g u ↦ finiteSIdeleSemilocalEquiv_smul hS g u) σ).trans
    ((CyclicTate.tateH1MulProdEquiv σ).trans
      ((CyclicTate.tateH1MulPiEquiv σ
        (fun v : S ↦ (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ)).prodCongr
          (AddEquiv.refl _)))

/-- **The semilocal decomposition of `Ĥ⁰` of the infinite ideles**:
`Ĥ⁰(Gal(L/K), (𝔸_L^∞)^×) ≅ ∏_{v ∣ ∞} Ĥ⁰(Gal(L/K), (∏_{w ∣ v} L_w)^×)`. -/
def tateH0InfiniteIdeleEquivPi :
    TateH0 (L ≃ₐ[K] L) (Additive (InfiniteAdeleRing L)ˣ) σ
      ≃+ ∀ v : InfinitePlace K,
          TateH0 (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v)ˣ) σ :=
  (CyclicTate.tateH0EquivOfMulEquiv (infiniteIdeleEquivPi K L)
      (fun g u ↦ infiniteIdeleEquivPi_smul g u) σ).trans
    (CyclicTate.tateH0MulPiEquiv σ (fun v : InfinitePlace K ↦ (InfiniteLocalProduct L v)ˣ))

/-- **The semilocal decomposition of `Ĥ¹` of the infinite ideles.** -/
def tateH1InfiniteIdeleEquivPi :
    TateH1 (L ≃ₐ[K] L) (Additive (InfiniteAdeleRing L)ˣ) σ
      ≃+ ∀ v : InfinitePlace K,
          TateH1 (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v)ˣ) σ :=
  (CyclicTate.tateH1EquivOfMulEquiv (infiniteIdeleEquivPi K L)
      (fun g u ↦ infiniteIdeleEquivPi_smul g u) σ).trans
    (CyclicTate.tateH1MulPiEquiv σ (fun v : InfinitePlace K ↦ (InfiniteLocalProduct L v)ˣ))

/-- **The semilocal decomposition of `Ĥ⁰` of the `S`-ideles**:

`Ĥ⁰(Gal(L/K), 𝕀_{L,S}) ≅ (∏_{v ∣ ∞} Ĥ⁰(Gal, (∏_{w ∣ v} L_w)^×))
                          × ((∏_{v ∈ S} Ĥ⁰(Gal, (∏_{w ∣ v} L_w)^×))
                             × Ĥ⁰(Gal, ∏_{v ∉ S} (∏_{w ∣ v} O_w)^×))`.

Composing each factor with `NumberField.tateH0LocalProductUnitsEquiv` (finite places) and
`NumberField.InfiniteAdeleRing.tateH0InfiniteLocalProductUnitsEquiv` (infinite places) expresses
the whole of `Ĥ⁰(Gal(L/K), 𝕀_{L,S})` in terms of the local groups `Ĥ⁰(D_w, L_w^×)`, which is the
domain of the sum-of-local-invariants map. -/
def tateH0SIdeleEquiv (hS : S.Finite) :
    TateH0 (L ≃ₐ[K] L) (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ
      ≃+ (∀ v : InfinitePlace K,
            TateH0 (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v)ˣ) σ)
        × ((∀ v : S, TateH0 (L ≃ₐ[K] L)
              (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)
          × TateH0 (L ≃ₐ[K] L) (Additive (∀ v : ↥(Sᶜ),
              localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ) :=
  (CyclicTate.tateH0EquivOfMulEquiv (sIdeleProdEquiv K L S)
      (fun g u ↦ sIdeleProdEquiv_smul g u) σ).trans
    ((CyclicTate.tateH0MulProdEquiv σ).trans
      ((tateH0InfiniteIdeleEquivPi (K := K) (L := L) (σ := σ)).prodCongr
          (tateH0FiniteSIdeleEquiv hS)))

/-- **The semilocal decomposition of `Ĥ¹` of the `S`-ideles.** -/
def tateH1SIdeleEquiv (hS : S.Finite) :
    TateH1 (L ≃ₐ[K] L) (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ
      ≃+ (∀ v : InfinitePlace K,
            TateH1 (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v)ˣ) σ)
        × ((∀ v : S, TateH1 (L ≃ₐ[K] L)
              (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ)
          × TateH1 (L ≃ₐ[K] L) (Additive (∀ v : ↥(Sᶜ),
              localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ) :=
  (CyclicTate.tateH1EquivOfMulEquiv (sIdeleProdEquiv K L S)
      (fun g u ↦ sIdeleProdEquiv_smul g u) σ).trans
    ((CyclicTate.tateH1MulProdEquiv σ).trans
      ((tateH1InfiniteIdeleEquivPi (K := K) (L := L) (σ := σ)).prodCongr
          (tateH1FiniteSIdeleEquiv hS)))

set_option synthInstance.maxHeartbeats 80000 in
/-- **The semilocal decomposition of `Ĥ⁰(Gal(L/K), 𝕀_{L,S})` when `L / K` is unramified outside
`S`.**  The hypothesis is the vanishing of the Tate cohomology of the semilocal integral units
at each place outside `S`, which
`NumberField.subsingleton_tateH0_localProductIntegerUnits` supplies at an unramified place; the
outside factor then disappears and

`Ĥ⁰(Gal(L/K), 𝕀_{L,S}) ≅ (∏_{v ∣ ∞} Ĥ⁰(Gal, (∏_{w ∣ v} L_w)^×))
                          × (∏_{v ∈ S} Ĥ⁰(Gal, (∏_{w ∣ v} L_w)^×))`,

a product over the places of `K` of purely local groups. -/
def tateH0SIdeleEquivOfUnramified (hS : S.Finite)
    [∀ v : ↥(Sᶜ), Subsingleton (TateH0 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ)] :
    TateH0 (L ≃ₐ[K] L) (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ
      ≃+ (∀ v : InfinitePlace K,
            TateH0 (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v)ˣ) σ)
        × (∀ v : S, TateH0 (L ≃ₐ[K] L)
              (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ) :=
  haveI := CyclicTate.subsingleton_tateH0_mulPi (G := L ≃ₐ[K] L) (σ := σ)
    (fun v : ↥(Sᶜ) ↦ localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))
  (tateH0SIdeleEquiv hS).trans
    ((AddEquiv.refl _).prodCongr (AddEquiv.prodSubsingletonRight _ _))

set_option synthInstance.maxHeartbeats 80000 in
/-- **The semilocal decomposition of `Ĥ¹(Gal(L/K), 𝕀_{L,S})` when `L / K` is unramified outside
`S`.** -/
def tateH1SIdeleEquivOfUnramified (hS : S.Finite)
    [∀ v : ↥(Sᶜ), Subsingleton (TateH1 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))) σ)] :
    TateH1 (L ≃ₐ[K] L) (Additive (IdeleGroup.sIdeleSubgroup L (placesOverSet K L S))) σ
      ≃+ (∀ v : InfinitePlace K,
            TateH1 (L ≃ₐ[K] L) (Additive (InfiniteLocalProduct L v)ˣ) σ)
        × (∀ v : S, TateH1 (L ≃ₐ[K] L)
              (Additive (LocalProduct K L (v : HeightOneSpectrum (𝓞 K)))ˣ) σ) :=
  haveI := CyclicTate.subsingleton_tateH1_mulPi (G := L ≃ₐ[K] L) (σ := σ)
    (fun v : ↥(Sᶜ) ↦ localProductIntegerUnits K L (v : HeightOneSpectrum (𝓞 K)))
  (tateH1SIdeleEquiv hS).trans
    ((AddEquiv.refl _).prodCongr (AddEquiv.prodSubsingletonRight _ _))

end NumberField
