/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.PermutationLattice
public import Iwasawalib.NumberTheory.CFT.FinitePlaceFibre
public import Iwasawalib.NumberTheory.CFT.InfiniteAdeleBaseChange
public import Iwasawalib.NumberTheory.CFT.SUnitLog
public import Iwasawalib.NumberTheory.CFT.LocalGalois

@[expose] public section

/-!
# The permutation lattice of the places of a number field

The set of places of `L` above a fixed set of places of `K` is a `Gal(L/K)`-set which
decomposes into the fibres over the places of `K`, each of which is transitive.  Feeding this
into `Iwasawalib/NumberTheory/CFT/PermutationLattice.lean` computes the Herbrand quotient of
the corresponding permutation lattice `∏_{w ∈ S_L} ℤ` for a cyclic extension `L / K`:

`h(ℤ[S_L]) = ∏_{v ∈ S} #D_w(v)`,

where `D_w = Stab_{Gal(L/K)}(w)` is the decomposition group of a place `w` above `v`, whose
order is the local degree `n_v = [L_w : K_v]`.

## Main results

* `NumberField.herbrand_infinitePlace`: the archimedean factor.
* `NumberField.herbrand_placesOverSet`: the factor from a set `S` of finite places.
* `NumberField.herbrand_sPlace`: the two combined, for the `S`-places `SPlace L S_L`.
* `NumberField.card_stabilizer_finitePlaceFibre`: the stabiliser of a finite place is the
  decomposition group, of order the local degree `[L_w : K_v]`, so that
  `NumberField.herbrand_placesOverSet_eq_prod_finrank` reads `h(ℤ[S_L]) = ∏_{v ∈ S} n_v`.
* `NumberField.herbrand_kerTotal_sPlace`: the Herbrand quotient of the trace-zero sublattice
  `ℤ[S_L]⁰`, which is `(∏_v n_v) / n` — the value predicted for `h(O_{L,S}^×)`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MulAction
open NumberField.InfiniteAdeleRing

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]

/-! ## The infinite places -/

variable (K L)

/-- The infinite places of `L` are the disjoint union of the fibres over the infinite places
of `K`. -/
def infinitePlaceSigmaEquiv :
    InfinitePlace L ≃ Σ v : InfinitePlace K, Fibre L v :=
  (Equiv.sigmaFiberEquiv fun w : InfinitePlace L ↦ w.comap (algebraMap K L)).symm

variable {K L}

omit [NumberField K] [NumberField L] in
theorem infinitePlaceSigmaEquiv_equivariant (σ : L ≃ₐ[K] L) (w : InfinitePlace L) :
    infinitePlaceSigmaEquiv K L (σ • w) = σ • infinitePlaceSigmaEquiv K L w := by
  refine Sigma.subtype_ext ?_ rfl
  show (σ • w).comap (algebraMap K L) = w.comap (algebraMap K L)
  rw [InfinitePlace.smul_eq_comap]
  exact comap_comap_algEquiv' σ.symm w

/-- **The Herbrand quotient of the archimedean permutation lattice** of a cyclic extension:
`h(ℤ[Σ_∞(L)]) = ∏_{v | ∞} #D_w(v)`. -/
theorem herbrand_infinitePlace [IsGalois K L] {σ : L ≃ₐ[K] L}
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ k : ℕ, σ ^ k = g)
    (w : ∀ v : InfinitePlace K, Fibre L v) :
    CyclicTate.herbrand (L ≃ₐ[K] L) (PermLattice (L ≃ₐ[K] L) (InfinitePlace L)) σ
      = ∏ v : InfinitePlace K, (Nat.card (stabilizer (L ≃ₐ[K] L) (w v)) : ℚ) := by
  classical
  haveI : ∀ v : InfinitePlace K, Fintype (Fibre L v) := fun _ ↦ Fintype.ofFinite _
  rw [PermLattice.herbrand_congr σ (infinitePlaceSigmaEquiv_equivariant (K := K) (L := L))]
  exact PermLattice.herbrand_sigma_eq_prod hgen w

/-! ## The finite places above a set of finite places -/

variable (K L)

/-- The finite places of `L` above a set `S` of finite places of `K` are the disjoint union of
the fibres `FinitePlaceFibre L v` for `v ∈ S`. -/
def placesOverSetSigmaEquiv (S : Set (HeightOneSpectrum (𝓞 K))) :
    placesOverSet K L S ≃ Σ v : S, FinitePlaceFibre L (v : HeightOneSpectrum (𝓞 K)) where
  toFun w := ⟨⟨(w : HeightOneSpectrum (𝓞 L)).under (𝓞 K), w.2⟩,
    ⟨(w : HeightOneSpectrum (𝓞 L)), rfl⟩⟩
  invFun p := ⟨((p.2 : HeightOneSpectrum (𝓞 L))), by
    show ((p.2 : HeightOneSpectrum (𝓞 L))).under (𝓞 K) ∈ S
    rw [p.2.2]
    exact p.1.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv p := Sigma.subtype_ext (Subtype.ext p.2.2) rfl

variable {K L}

omit [NumberField K] [NumberField L] in
theorem placesOverSetSigmaEquiv_equivariant (S : Set (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L) (w : placesOverSet K L S) :
    placesOverSetSigmaEquiv K L S (σ • w) = σ • placesOverSetSigmaEquiv K L S w := by
  refine Sigma.subtype_ext (Subtype.ext ?_) ?_
  · show ((σ • w : placesOverSet K L S) : HeightOneSpectrum (𝓞 L)).under (𝓞 K)
      = ((w : HeightOneSpectrum (𝓞 L))).under (𝓞 K)
    rw [coe_smul_placesOverSet, under_smul_eq]
  · show ((σ • w : placesOverSet K L S) : HeightOneSpectrum (𝓞 L))
      = ((σ • (⟨(w : HeightOneSpectrum (𝓞 L)), rfl⟩ :
        FinitePlaceFibre L ((w : HeightOneSpectrum (𝓞 L)).under (𝓞 K)))) :
          HeightOneSpectrum (𝓞 L))
    rfl

theorem finite_finitePlaceFibre (v : HeightOneSpectrum (𝓞 K)) :
    Finite (FinitePlaceFibre L v) :=
  Set.Finite.to_subtype (s := {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v})
    (placesOver_eq_setOf_under_eq (K := K) (L := L) v ▸ finite_placesOver K L v)

/-- **The Herbrand quotient of the permutation lattice on the finite places above `S`** in a
cyclic extension: `h(ℤ[S_L]) = ∏_{v ∈ S} #D_w(v)`. -/
theorem herbrand_placesOverSet [IsGalois K L] (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    {σ : L ≃ₐ[K] L} (hgen : ∀ g : L ≃ₐ[K] L, ∃ k : ℕ, σ ^ k = g)
    (w : ∀ v : S, FinitePlaceFibre L (v : HeightOneSpectrum (𝓞 K))) :
    CyclicTate.herbrand (L ≃ₐ[K] L) (PermLattice (L ≃ₐ[K] L) (placesOverSet K L S)) σ
      = ∏ v : S, (Nat.card (stabilizer (L ≃ₐ[K] L) (w v)) : ℚ) := by
  classical
  haveI : ∀ v : S, Finite (FinitePlaceFibre L (v : HeightOneSpectrum (𝓞 K))) :=
    fun v ↦ finite_finitePlaceFibre _
  haveI : ∀ v : S, Fintype (FinitePlaceFibre L (v : HeightOneSpectrum (𝓞 K))) :=
    fun _ ↦ Fintype.ofFinite _
  rw [PermLattice.herbrand_congr σ (placesOverSetSigmaEquiv_equivariant S)]
  exact PermLattice.herbrand_sigma_eq_prod hgen w

/-! ## The stabiliser is the decomposition group, of order the local degree -/

section LocalDegree

attribute [local instance] adicCompletionComapAlgebra isScalarTower_adicCompletion

instance liesOver_finitePlaceFibre {v : HeightOneSpectrum (𝓞 K)} (w : FinitePlaceFibre L v) :
    ((w : HeightOneSpectrum (𝓞 L)).asIdeal).LiesOver v.asIdeal :=
  liesOver_of_under_eq w.2

/-- **The order of the stabiliser of a finite place is the local degree** `[L_w : K_v]`. -/
theorem card_stabilizer_finitePlaceFibre [IsGalois K L] {v : HeightOneSpectrum (𝓞 K)}
    (w : FinitePlaceFibre L v) :
    Nat.card (stabilizer (L ≃ₐ[K] L) w)
      = Module.finrank (v.adicCompletion K) ((w : HeightOneSpectrum (𝓞 L)).adicCompletion L) := by
  have hst : stabilizer (L ≃ₐ[K] L) w
      = decompositionGroup K L (w : HeightOneSpectrum (𝓞 L)) := by
    ext σ
    rw [MulAction.mem_stabilizer_iff, mem_decompositionGroup]
    exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩
  rw [hst, finrank_adicCompletion v (w : HeightOneSpectrum (𝓞 L))]

/-- **The Herbrand quotient of the permutation lattice on the finite places above `S`, in
terms of the local degrees**: `h(ℤ[S_L]) = ∏_{v ∈ S} n_v` with `n_v = [L_w : K_v]`. -/
theorem herbrand_placesOverSet_eq_prod_finrank [IsGalois K L]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    {σ : L ≃ₐ[K] L} (hgen : ∀ g : L ≃ₐ[K] L, ∃ k : ℕ, σ ^ k = g)
    (w : ∀ v : S, FinitePlaceFibre L (v : HeightOneSpectrum (𝓞 K))) :
    CyclicTate.herbrand (L ≃ₐ[K] L) (PermLattice (L ≃ₐ[K] L) (placesOverSet K L S)) σ
      = ∏ v : S, (Module.finrank ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)
          ((w v : HeightOneSpectrum (𝓞 L)).adicCompletion L) : ℚ) := by
  rw [herbrand_placesOverSet S hgen w]
  exact Finset.prod_congr rfl fun v _ ↦ by
    rw [card_stabilizer_finitePlaceFibre (w v)]

/-- **`∑_{w | v} n_w = n`, in the Galois case**: the number of places above `v` times the
local degree is the degree of `L / K`. -/
theorem card_finitePlaceFibre_mul_finrank [IsGalois K L] {v : HeightOneSpectrum (𝓞 K)}
    (w : FinitePlaceFibre L v) :
    Nat.card (FinitePlaceFibre L v)
        * Module.finrank (v.adicCompletion K) ((w : HeightOneSpectrum (𝓞 L)).adicCompletion L)
      = Module.finrank K L := by
  rw [← card_stabilizer_finitePlaceFibre w,
    PermLattice.card_mul_card_stabilizer (G := L ≃ₐ[K] L) w]
  exact IsGalois.card_aut_eq_finrank K L

end LocalDegree

/-! ## The `S`-places -/

variable (K L)

/-- The permutation lattice on the `S`-places of `L` is the product of the archimedean one and
the one on the finite places above `S`. -/
def sPlaceProdAddEquiv (S : Set (HeightOneSpectrum (𝓞 K))) :
    PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S)) ≃+
      PermLattice (L ≃ₐ[K] L) (InfinitePlace L)
        × PermLattice (L ≃ₐ[K] L) (placesOverSet K L S) where
  toFun f := (PermLattice.ofFun fun w ↦ PermLattice.eval f (Sum.inl w),
    PermLattice.ofFun fun w ↦ PermLattice.eval f (Sum.inr w))
  invFun p := PermLattice.ofFun
    (Sum.elim (fun w ↦ PermLattice.eval p.1 w) fun w ↦ PermLattice.eval p.2 w)
  left_inv _ := PermLattice.ext fun x ↦ by cases x <;> rfl
  right_inv _ := Prod.ext (PermLattice.ext fun _ ↦ rfl) (PermLattice.ext fun _ ↦ rfl)
  map_add' _ _ := Prod.ext (PermLattice.ext fun _ ↦ rfl) (PermLattice.ext fun _ ↦ rfl)

variable {K L}

omit [NumberField K] [NumberField L] in
theorem sPlaceProdAddEquiv_equivariant (S : Set (HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L)
    (f : PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S))) :
    sPlaceProdAddEquiv K L S (σ • f) = σ • sPlaceProdAddEquiv K L S f :=
  Prod.ext (PermLattice.ext fun _ ↦ rfl) (PermLattice.ext fun _ ↦ rfl)

/-- **The Herbrand quotient of the permutation lattice on the `S`-places of `L`** for a cyclic
extension `L / K`: it is the product over the places of `K` in `S ∪ {∞}` of the orders of the
decomposition groups. -/
theorem herbrand_sPlace [IsGalois K L] (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    [Fintype (placesOverSet K L S)]
    {σ : L ≃ₐ[K] L} (hgen : ∀ g : L ≃ₐ[K] L, ∃ k : ℕ, σ ^ k = g)
    (w₁ : ∀ v : InfinitePlace K, Fibre L v)
    (w₂ : ∀ v : S, FinitePlaceFibre L (v : HeightOneSpectrum (𝓞 K))) :
    CyclicTate.herbrand (L ≃ₐ[K] L)
        (PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S))) σ
      = (∏ v : InfinitePlace K, (Nat.card (stabilizer (L ≃ₐ[K] L) (w₁ v)) : ℚ))
        * ∏ v : S, (Nat.card (stabilizer (L ≃ₐ[K] L) (w₂ v)) : ℚ) := by
  classical
  haveI : ∀ v : InfinitePlace K, Fintype (Fibre L v) := fun _ ↦ Fintype.ofFinite _
  haveI : ∀ v : S, Finite (FinitePlaceFibre L (v : HeightOneSpectrum (𝓞 K))) :=
    fun v ↦ finite_finitePlaceFibre _
  haveI : ∀ v : S, Fintype (FinitePlaceFibre L (v : HeightOneSpectrum (𝓞 K))) :=
    fun _ ↦ Fintype.ofFinite _
  haveI h01 : Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (PermLattice (L ≃ₐ[K] L) (Σ v : InfinitePlace K, Fibre L v)) σ) :=
    PermLattice.finite_tateH0_sigma hgen w₁
  haveI h11 : Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (PermLattice (L ≃ₐ[K] L) (Σ v : InfinitePlace K, Fibre L v)) σ) :=
    PermLattice.finite_tateH1_sigma hgen w₁
  haveI h02 : Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (PermLattice (L ≃ₐ[K] L)
        (Σ v : S, FinitePlaceFibre L (v : HeightOneSpectrum (𝓞 K)))) σ) :=
    PermLattice.finite_tateH0_sigma hgen w₂
  haveI h12 : Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (PermLattice (L ≃ₐ[K] L)
        (Σ v : S, FinitePlaceFibre L (v : HeightOneSpectrum (𝓞 K)))) σ) :=
    PermLattice.finite_tateH1_sigma hgen w₂
  haveI : Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (PermLattice (L ≃ₐ[K] L) (InfinitePlace L)) σ) :=
    PermLattice.finite_tateH0_congr σ
      (PermLattice.equiv_symm_equivariant (infinitePlaceSigmaEquiv_equivariant (K := K) (L := L)))
  haveI : Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (PermLattice (L ≃ₐ[K] L) (InfinitePlace L)) σ) :=
    PermLattice.finite_tateH1_congr σ
      (PermLattice.equiv_symm_equivariant (infinitePlaceSigmaEquiv_equivariant (K := K) (L := L)))
  haveI : Finite (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (PermLattice (L ≃ₐ[K] L) (placesOverSet K L S)) σ) :=
    PermLattice.finite_tateH0_congr σ
      (PermLattice.equiv_symm_equivariant (placesOverSetSigmaEquiv_equivariant S))
  haveI : Finite (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (PermLattice (L ≃ₐ[K] L) (placesOverSet K L S)) σ) :=
    PermLattice.finite_tateH1_congr σ
      (PermLattice.equiv_symm_equivariant (placesOverSetSigmaEquiv_equivariant S))
  rw [CyclicTate.herbrand_eq_of_addEquiv (sPlaceProdAddEquiv K L S)
    (sPlaceProdAddEquiv_equivariant S) σ, CyclicTate.herbrand_prod σ,
    herbrand_infinitePlace hgen w₁, herbrand_placesOverSet S hgen w₂]

/-- **The Herbrand quotient of the trace-zero sublattice of `ℤ[S_L]`**, that is, of the
augmentation ideal `ℤ[S_L]⁰`:

`h(ℤ[S_L]⁰) = (∏_{v ∈ S ∪ S_∞} n_v) / n`.

This is the value predicted for `h(O_{L,S}^×)`: the `S`-unit lattice becomes isomorphic to
`ℤ[S_L]⁰` after `⊗ ℚ` (`NumberField.sUnitSpan_eq_sHyperplane` is the corresponding statement
over `ℝ`), and by `CyclicTate.herbrand_eq_of_span_eq_top` the Herbrand quotient only depends
on the rational representation.  Transporting the real isomorphism of
`sUnitSpan_eq_sHyperplane` to a rational one is the step that is *not* proved here. -/
theorem herbrand_kerTotal_sPlace [IsGalois K L] (S : Set (HeightOneSpectrum (𝓞 K)))
    [Fintype S] [Fintype (placesOverSet K L S)]
    {σ : L ≃ₐ[K] L} (hgen : ∀ g : L ≃ₐ[K] L, ∃ k : ℕ, σ ^ k = g)
    (w₁ : ∀ v : InfinitePlace K, Fibre L v)
    (w₂ : ∀ v : S, FinitePlaceFibre L (v : HeightOneSpectrum (𝓞 K))) :
    CyclicTate.herbrand (L ≃ₐ[K] L)
        (PermLattice.kerTotal (G := L ≃ₐ[K] L) (Ω := SPlace L (placesOverSet K L S))) σ
      = ((∏ v : InfinitePlace K, (Nat.card (stabilizer (L ≃ₐ[K] L) (w₁ v)) : ℚ))
          * ∏ v : S, (Nat.card (stabilizer (L ≃ₐ[K] L) (w₂ v)) : ℚ))
        / (Nat.card (L ≃ₐ[K] L) : ℚ) := by
  classical
  rw [PermLattice.herbrand_kerTotal hgen, herbrand_sPlace S hgen w₁ w₂]

end NumberField
