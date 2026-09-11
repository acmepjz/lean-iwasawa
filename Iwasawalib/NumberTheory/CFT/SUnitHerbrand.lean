/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.SUnitLattice
public import Iwasawalib.NumberTheory.CFT.HerbrandForm
public import Iwasawalib.NumberTheory.CFT.PlaceLattice
public import Iwasawalib.NumberTheory.CFT.HerbrandShapiro

@[expose] public section

/-!
# The Herbrand quotient of the `S`-unit group

Let `L / K` be a cyclic extension of number fields with group `G = ⟨σ⟩` of order `n`, and let
`S` be a finite set of finite places of `K`.  This file proves

`h(O_{L,S}^×) = (∏_{v ∈ S ∪ S_∞} n_v) / n`   (`NumberField.herbrand_sUnitGroup`),

where `n_v = #D_w` is the order of the decomposition group at a place `w` of `L` above `v`.

This is the value that `NumberField.herbrand_kerTotal_sPlace` computes for the augmentation
ideal `ℤ[S_L]⁰`, and whose transport to the `S`-units its docstring described as "the step that
is *not* proved here".  The missing input was the **full-lattice** half of Dirichlet's `S`-unit
theorem, now available as `NumberField.sUnitBasis` in
`Iwasawalib/NumberTheory/CFT/SUnitLattice.lean`.

## Proof

Work inside `V = (∏_{p ∈ S} ℝ)⁰`, the trace-zero hyperplane, with its permutation action of
`Gal(L/K)` (`NumberField.sHyperplaneDistribMulAction`).  There are two `Gal(L/K)`-stable
lattices in `V`, each spanned by an `ℝ`-basis of `V`:

* the `S`-unit lattice, with basis `NumberField.sUnitBasis` — this is Dirichlet;
* the integral lattice `ℤ[S_L]⁰`, with the standard basis `NumberField.intBasis` of vectors
  `e_p - e_{p₀}`.

They are **not** commensurable — the `S`-unit lattice is transcendental — so
`CyclicTate.herbrand_eq_of_commensurable` does not apply.  What does apply is the
Noether-Deuring comparison `CyclicTate.herbrand_intLattice_eq_of_stable`, which needs exactly
the two bases above.  That gives the middle equality of

`h(O_{L,S}^×) = h(Λ_S) = h(ℤ[S_L]⁰) = (∏_v n_v) / n`,

the first equality because the logarithmic embedding is surjective onto `Λ_S` with finite
kernel (`NumberField.finite_ker_sLogHyp`, the roots of unity) so
`CyclicTate.herbrand_eq_of_finite_ker_coker` applies, and the last being
`NumberField.herbrand_kerTotal_sPlace`.

## Main definitions

* `NumberField.intBasisVec`, `NumberField.intBasis` : the standard `ℝ`-basis `e_p - e_{p₀}` of
  the trace-zero hyperplane.
* `NumberField.intHyper` : the integral vectors of the trace-zero hyperplane, i.e. `ℤ[S_L]⁰`
  inside `(∏_{p ∈ S} ℝ)⁰`.
* `NumberField.sHyperplaneDistribMulAction` : the `Gal(L/K)`-action on the hyperplane.
* `NumberField.sLogEquivariant` : the logarithmic embedding as an equivariant map onto the
  `S`-unit lattice.
* `NumberField.kerTotalAddEquiv` : the equivariant identification of `ℤ[S_L]⁰` with
  `NumberField.intHyper`.

## Main statements

* `NumberField.intLattice_intBasis_eq_intHyper` : the standard basis spans exactly the integral
  vectors.
* `NumberField.herbrand_sUnitLattice_eq_intHyper` : the Noether-Deuring comparison of the two
  lattices.
* `NumberField.herbrand_sUnitGroup_eq_lattice` : `h(O_{L,S}^×) = h(Λ_S)`.
* `NumberField.herbrand_kerTotal_eq_intLattice` : `h(ℤ[S_L]⁰) = h(ℤ[S_L]⁰ ⊆ V)`.
* `NumberField.herbrand_sUnitGroup` : **the main result**.
* `NumberField.herbrand_sUnitGroup_mul_card` : the same, without division.

## What is not here

The other factor of the computation of `h(C_L)`, namely `h(𝕀_{L,S}) = ∏_{v ∈ S} h(L_wˣ)` and
the local value `h(L_wˣ) = e(w|v)`, is not proved here; it needs the semilocal decomposition of
the `S`-ideles and local class field theory, and `CyclicTate.herbrand_piUnits` is the Shapiro
step that will consume it.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField.InfinitePlace
open Module MulAction
open NumberField.InfiniteAdeleRing

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]
variable {T : Set (HeightOneSpectrum (𝓞 L))}

/-- Equality of `S`-places is decidable, classically. -/
local instance decEqSPlace : DecidableEq (SPlace L T) := Classical.decEq _

/-! ## The standard integral basis of the trace-zero hyperplane -/

section IntBasis

variable (L T) [Fintype T]

/-- A distinguished `S`-place, used as the origin for the standard basis of `ℤ[S]⁰`. -/
def sBase : SPlace L T := Sum.inl (Classical.arbitrary (InfinitePlace L))

/-- The vector `e_p - e_{p₀}` of the trace-zero hyperplane, for `p ≠ p₀`. -/
def intBasisVec (i : {p : SPlace L T // p ≠ sBase L T}) : sHyperplane L T :=
  ⟨Pi.single (i : SPlace L T) 1 - Pi.single (sBase L T) 1, by
    rw [mem_sHyperplane]
    simp [Finset.sum_pi_single']⟩

@[simp]
theorem coe_intBasisVec (i : {p : SPlace L T // p ≠ sBase L T}) :
    ((intBasisVec L T i : sHyperplane L T) : SPlace L T → ℝ)
      = Pi.single (i : SPlace L T) 1 - Pi.single (sBase L T) 1 := rfl

variable {L T}

/-- **Every element of the trace-zero hyperplane is the combination `∑_{p ≠ p₀} y_p (e_p -
e_{p₀})`.** -/
theorem eq_sum_smul_intBasisVec (y : sHyperplane L T) :
    y = ∑ i : {p : SPlace L T // p ≠ sBase L T},
      ((y : SPlace L T → ℝ) (i : SPlace L T)) • intBasisVec L T i := by
  classical
  refine Subtype.ext (funext fun q ↦ ?_)
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply, coe_intBasisVec,
    Pi.sub_apply, smul_eq_mul]
  have hsub : ∑ x : {p : SPlace L T // p ≠ sBase L T}, (y : SPlace L T → ℝ) (x : SPlace L T)
        * ((Pi.single (x : SPlace L T) (1 : ℝ) : SPlace L T → ℝ) q
          - (Pi.single (sBase L T) (1 : ℝ) : SPlace L T → ℝ) q)
      = ∑ p ∈ Finset.univ.erase (sBase L T), (y : SPlace L T → ℝ) p
        * ((Pi.single p (1 : ℝ) : SPlace L T → ℝ) q
          - (Pi.single (sBase L T) (1 : ℝ) : SPlace L T → ℝ) q) :=
    (Finset.sum_subtype (p := fun p : SPlace L T ↦ p ≠ sBase L T)
      (Finset.univ.erase (sBase L T)) (fun p ↦ by simp)
      (fun p ↦ (y : SPlace L T → ℝ) p
        * ((Pi.single p (1 : ℝ) : SPlace L T → ℝ) q
          - (Pi.single (sBase L T) (1 : ℝ) : SPlace L T → ℝ) q))).symm
  rw [hsub]
  by_cases hq : q = sBase L T
  · rw [hq]
    have h1 : ∀ p ∈ Finset.univ.erase (sBase L T), (y : SPlace L T → ℝ) p
        * ((Pi.single p (1 : ℝ) : SPlace L T → ℝ) (sBase L T)
          - (Pi.single (sBase L T) (1 : ℝ) : SPlace L T → ℝ) (sBase L T))
        = - (y : SPlace L T → ℝ) p := by
      intro p hp
      rw [Pi.single_eq_of_ne (Ne.symm (Finset.ne_of_mem_erase hp)), Pi.single_eq_same]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_neg_distrib]
    have h2 : ∑ p ∈ Finset.univ.erase (sBase L T), (y : SPlace L T → ℝ) p
        = (∑ p : SPlace L T, (y : SPlace L T → ℝ) p) - (y : SPlace L T → ℝ) (sBase L T) := by
      rw [eq_sub_iff_add_eq]
      exact Finset.sum_erase_add _ _ (Finset.mem_univ (sBase L T))
    rw [h2, (mem_sHyperplane L T).1 y.2]
    ring
  · have h0 : ∀ p ∈ Finset.univ.erase (sBase L T), p ≠ q → (y : SPlace L T → ℝ) p
        * ((Pi.single p (1 : ℝ) : SPlace L T → ℝ) q
          - (Pi.single (sBase L T) (1 : ℝ) : SPlace L T → ℝ) q) = 0 := by
      intro p _ hpq
      rw [Pi.single_eq_of_ne (Ne.symm hpq), Pi.single_eq_of_ne hq]
      ring
    rw [Finset.sum_eq_single_of_mem q (Finset.mem_erase.2 ⟨hq, Finset.mem_univ q⟩) h0,
      Pi.single_eq_same, Pi.single_eq_of_ne hq]
    ring

variable (L T)

theorem card_ne_sBase : Fintype.card {p : SPlace L T // p ≠ sBase L T} = sRank L T := by
  classical
  have h1 : Fintype.card {p : SPlace L T // p ≠ sBase L T}
      = Fintype.card (SPlace L T) - 1 := by
    simp [ne_eq, Fintype.card_subtype_compl]
  rw [h1, sRank, Fintype.card_sum]

/-- The standard basis vectors span the hyperplane over `ℝ`. -/
theorem span_intBasisVec_real :
    (⊤ : Submodule ℝ (sHyperplane L T)) ≤ Submodule.span ℝ (Set.range (intBasisVec L T)) := by
  intro y _
  have hmem : (∑ i : {p : SPlace L T // p ≠ sBase L T},
        ((y : SPlace L T → ℝ) (i : SPlace L T)) • intBasisVec L T i)
      ∈ Submodule.span ℝ (Set.range (intBasisVec L T)) :=
    Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rwa [← eq_sum_smul_intBasisVec y] at hmem

/-- The standard basis `{e_p - e_{p₀}}` of the trace-zero hyperplane, indexed by the
`S`-places other than `p₀`. -/
def intBasisSub : Basis {p : SPlace L T // p ≠ sBase L T} ℝ (sHyperplane L T) :=
  basisOfTopLeSpanOfCardEqFinrank _ (span_intBasisVec_real L T)
    (by rw [card_ne_sBase, finrank_sHyperplane_eq_sRank])

@[simp]
theorem coe_intBasisSub : ⇑(intBasisSub L T) = intBasisVec L T :=
  coe_basisOfTopLeSpanOfCardEqFinrank _ _ _

/-- The `S`-places other than `p₀`, reindexed by `Fin (#S - 1)`. -/
def sBaseEquivFin : {p : SPlace L T // p ≠ sBase L T} ≃ Fin (sRank L T) :=
  Fintype.equivFinOfCardEq (card_ne_sBase L T)

/-- The standard basis of the trace-zero hyperplane, indexed by `Fin (#S - 1)` so as to match
the index type of `NumberField.sUnitBasis`. -/
def intBasis : Basis (Fin (sRank L T)) ℝ (sHyperplane L T) :=
  (intBasisSub L T).reindex (sBaseEquivFin L T)

theorem coe_intBasis :
    ⇑(intBasis L T) = fun i ↦ intBasisVec L T ((sBaseEquivFin L T).symm i) := by
  funext i
  rw [intBasis, Basis.reindex_apply, coe_intBasisSub]

theorem range_intBasis :
    Set.range ⇑(intBasis L T) = Set.range (intBasisVec L T) := by
  rw [coe_intBasis]
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨sBaseEquivFin L T j, by simp⟩

end IntBasis

/-! ## The integral points of the trace-zero hyperplane -/

section IntHyper

variable (L T) [Fintype T]

/-- **`ℤ[S]⁰` inside `(∏_{p ∈ S} ℝ)⁰`**: the vectors of the trace-zero hyperplane all of whose
coordinates are integers. -/
def intHyper : AddSubgroup (sHyperplane L T) where
  carrier := {y | ∃ n : SPlace L T → ℤ, ∀ p, (y : SPlace L T → ℝ) p = (n p : ℝ)}
  zero_mem' := ⟨0, fun p ↦ by simp⟩
  add_mem' := by
    rintro a b ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨m + n, fun p ↦ by
      show (a : SPlace L T → ℝ) p + (b : SPlace L T → ℝ) p = _
      rw [hm p, hn p]; simp⟩
  neg_mem' := by
    rintro a ⟨n, hn⟩
    exact ⟨-n, fun p ↦ by
      show - (a : SPlace L T → ℝ) p = _
      rw [hn p]; simp⟩

variable {L T}

theorem mem_intHyper {y : sHyperplane L T} :
    y ∈ intHyper L T ↔ ∃ n : SPlace L T → ℤ, ∀ p, (y : SPlace L T → ℝ) p = (n p : ℝ) := Iff.rfl

variable (L T)

theorem intBasisVec_mem_intHyper (i : {p : SPlace L T // p ≠ sBase L T}) :
    intBasisVec L T i ∈ intHyper L T := by
  refine ⟨fun p ↦ (Pi.single (i : SPlace L T) (1 : ℤ) : SPlace L T → ℤ) p
      - (Pi.single (sBase L T) (1 : ℤ) : SPlace L T → ℤ) p, fun p ↦ ?_⟩
  rw [coe_intBasisVec]
  simp only [Pi.sub_apply, Int.cast_sub, Pi.single_apply]
  split_ifs <;> norm_num

/-- **The lattice spanned by the standard basis is exactly the set of integral vectors of the
trace-zero hyperplane.** -/
theorem intLattice_intBasis_eq_intHyper :
    NoetherDeuring.intLattice ⇑(intBasis L T) = intHyper L T := by
  refine le_antisymm ?_ ?_
  · refine NoetherDeuring.intLattice_le (H := intHyper L T) fun i ↦ ?_
    rw [coe_intBasis]
    exact intBasisVec_mem_intHyper L T _
  · rintro y ⟨n, hn⟩
    have hcoef : ∀ i : {p : SPlace L T // p ≠ sBase L T},
        ((y : SPlace L T → ℝ) (i : SPlace L T)) • intBasisVec L T i
          = (n (i : SPlace L T)) • intBasisVec L T i := by
      intro i
      rw [hn (i : SPlace L T)]
      exact Int.cast_smul_eq_zsmul ℝ (n (i : SPlace L T)) (intBasisVec L T i)
    have hy : y = ∑ i : {p : SPlace L T // p ≠ sBase L T},
        (n (i : SPlace L T)) • intBasisVec L T i := by
      rw [eq_sum_smul_intBasisVec y]
      exact Finset.sum_congr rfl fun i _ ↦ hcoef i
    rw [NoetherDeuring.mem_intLattice, range_intBasis, hy]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end IntHyper

/-! ## The two lattices, as lattices of bases -/

section Lattices

variable (L T) [Fintype T]

/-- The lattice spanned by `NumberField.sUnitBasis` is the `S`-unit lattice. -/
theorem intLattice_sUnitBasis :
    NoetherDeuring.intLattice ⇑(sUnitBasis L T) = (sUnitLattice L T).toAddSubgroup := by
  rw [NoetherDeuring.intLattice, coe_sUnitBasis, span_sUnitBasisVec_int]

end Lattices

/-! ## The Galois action on the trace-zero hyperplane -/

section Galois

variable {K : Type*} [Field K] [NumberField K] [Algebra K L]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype (placesOverSet K L S)]

/-- **The permutation action of `Gal(L/K)` on the trace-zero hyperplane `(∏_{p ∈ S} ℝ)⁰`**,
coming from its action on the `S`-places of `L`. -/
instance sHyperplaneDistribMulAction :
    DistribMulAction (L ≃ₐ[K] L) (sHyperplane L (placesOverSet K L S)) where
  smul σ y := ⟨fun p ↦ (y : SPlace L (placesOverSet K L S) → ℝ) (σ⁻¹ • p), by
    rw [mem_sHyperplane]
    refine (Fintype.sum_equiv (MulAction.toPerm σ⁻¹) _ _ fun p ↦ rfl).trans ?_
    exact (mem_sHyperplane L (placesOverSet K L S)).1 y.2⟩
  one_smul y := Subtype.ext (funext fun p ↦ by
    show (y : SPlace L (placesOverSet K L S) → ℝ) ((1 : L ≃ₐ[K] L)⁻¹ • p) = _
    rw [inv_one, one_smul])
  mul_smul σ τ y := Subtype.ext (funext fun p ↦ by
    show (y : SPlace L (placesOverSet K L S) → ℝ) ((σ * τ)⁻¹ • p)
      = (y : SPlace L (placesOverSet K L S) → ℝ) (τ⁻¹ • σ⁻¹ • p)
    rw [mul_inv_rev, mul_smul])
  smul_zero σ := Subtype.ext (funext fun p ↦ rfl)
  smul_add σ y z := Subtype.ext (funext fun p ↦ rfl)

omit [NumberField K] in
@[simp]
theorem coe_smul_sHyperplane (σ : L ≃ₐ[K] L)
    (y : sHyperplane L (placesOverSet K L S)) (p : SPlace L (placesOverSet K L S)) :
    ((σ • y : sHyperplane L (placesOverSet K L S)) : SPlace L (placesOverSet K L S) → ℝ) p
      = (y : SPlace L (placesOverSet K L S) → ℝ) (σ⁻¹ • p) := rfl

instance sHyperplaneSMulCommClass :
    SMulCommClass (L ≃ₐ[K] L) ℝ (sHyperplane L (placesOverSet K L S)) where
  smul_comm _ _ _ := Subtype.ext (funext fun _ ↦ rfl)

/-- **The logarithmic embedding is `Gal(L/K)`-equivariant**, as a map into the hyperplane. -/
theorem smul_sLogHyp (σ : L ≃ₐ[K] L) (x : Additive (SUnitGroup K L S)) :
    σ • sLogHyp L (placesOverSet K L S) x
      = sLogHyp L (placesOverSet K L S) (σ • x) := by
  refine Subtype.ext (funext fun p ↦ ?_)
  rw [coe_smul_sHyperplane]
  show sLog (σ⁻¹ • p) ((Additive.toMul x : SUnitGroup K L S) : Lˣ)
    = sLog p ((Additive.toMul (σ • x) : SUnitGroup K L S) : Lˣ)
  rw [show ((Additive.toMul (σ • x) : SUnitGroup K L S) : Lˣ)
      = σ • ((Additive.toMul x : SUnitGroup K L S) : Lˣ) from rfl]
  conv_rhs => rw [← smul_inv_smul σ p]
  exact (sLog_smul σ (σ⁻¹ • p) _).symm

/-- **The `S`-unit lattice is a `Gal(L/K)`-stable subgroup of the hyperplane.** -/
instance isStableSubgroup_sUnitLattice :
    CyclicTate.IsStableSubgroup (L ≃ₐ[K] L)
      (NoetherDeuring.intLattice ⇑(sUnitBasis L (placesOverSet K L S))) where
  smul_mem σ {y} hy := by
    rw [intLattice_sUnitBasis] at hy ⊢
    obtain ⟨x, hx⟩ := (mem_sUnitLattice L (placesOverSet K L S)).1 hy
    exact (mem_sUnitLattice L (placesOverSet K L S)).2
      ⟨σ • x, by rw [show Additive.ofMul (σ • x) = σ • Additive.ofMul x from rfl,
        ← smul_sLogHyp, hx]⟩

/-- **The integral lattice `ℤ[S_L]⁰` is a `Gal(L/K)`-stable subgroup of the hyperplane.** -/
instance isStableSubgroup_intHyper :
    CyclicTate.IsStableSubgroup (L ≃ₐ[K] L)
      (NoetherDeuring.intLattice ⇑(intBasis L (placesOverSet K L S))) where
  smul_mem σ {y} hy := by
    rw [intLattice_intBasis_eq_intHyper] at hy ⊢
    obtain ⟨n, hn⟩ := hy
    exact ⟨fun p ↦ n (σ⁻¹ • p), fun p ↦ by rw [coe_smul_sHyperplane, hn]⟩

/-- **Noether-Deuring comparison.**  The `S`-unit lattice and the integral lattice `ℤ[S_L]⁰`
are two `Gal(L/K)`-stable lattices in the trace-zero hyperplane, each spanned by an `ℝ`-basis
of it, so `CyclicTate.herbrand_intLattice_eq_of_stable` gives them the same Herbrand
quotient. -/
theorem herbrand_sUnitLattice_eq_intHyper [Fintype (L ≃ₐ[K] L)] {σ : L ≃ₐ[K] L}
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g) :
    CyclicTate.herbrand (L ≃ₐ[K] L)
        (NoetherDeuring.intLattice ⇑(sUnitBasis L (placesOverSet K L S))) σ
      = CyclicTate.herbrand (L ≃ₐ[K] L)
        (NoetherDeuring.intLattice ⇑(intBasis L (placesOverSet K L S))) σ :=
  CyclicTate.herbrand_intLattice_eq_of_stable hgen
    (sUnitBasis L (placesOverSet K L S)) (intBasis L (placesOverSet K L S))

/-! ## From the `S`-unit group to its lattice -/

variable (L)

/-- The logarithmic embedding, as an equivariant map from the `S`-unit group onto the
`S`-unit lattice. -/
def sLogEquivariant :
    Additive (SUnitGroup K L S) →+[L ≃ₐ[K] L]
      (NoetherDeuring.intLattice ⇑(sUnitBasis L (placesOverSet K L S))) where
  toFun x := ⟨sLogHyp L (placesOverSet K L S) x, by
    rw [intLattice_sUnitBasis]
    exact ⟨x, rfl⟩⟩
  map_smul' σ x := Subtype.ext (smul_sLogHyp S σ x).symm
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

theorem coe_sLogEquivariant (x : Additive (SUnitGroup K L S)) :
    ((sLogEquivariant L S x : NoetherDeuring.intLattice ⇑(sUnitBasis L (placesOverSet K L S)))
      : sHyperplane L (placesOverSet K L S)) = sLogHyp L (placesOverSet K L S) x := rfl

theorem finite_ker_sLogEquivariant [Fintype (L ≃ₐ[K] L)] :
    Finite (sLogEquivariant L S).toAddMonoidHom.ker := by
  haveI := finite_ker_sLogHyp L (placesOverSet K L S)
  refine Finite.of_injective
    (fun x : (sLogEquivariant L S).toAddMonoidHom.ker ↦
      (⟨(x : Additive (SUnitGroup K L S)), ?_⟩ :
        LinearMap.ker (sLogHyp L (placesOverSet K L S)).toIntLinearMap)) ?_
  · show sLogHyp L (placesOverSet K L S) (x : Additive (SUnitGroup K L S)) = 0
    have hx : sLogEquivariant L S (x : Additive (SUnitGroup K L S)) = 0 := x.2
    exact congrArg
      (fun z : NoetherDeuring.intLattice ⇑(sUnitBasis L (placesOverSet K L S)) ↦
        (z : sHyperplane L (placesOverSet K L S))) hx
  · intro a b h
    exact Subtype.ext (congrArg
      (fun z : LinearMap.ker (sLogHyp L (placesOverSet K L S)).toIntLinearMap ↦
        (z : Additive (SUnitGroup K L S))) h)

theorem range_sLogEquivariant : (sLogEquivariant L S).toAddMonoidHom.range = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨y, hy⟩ -
  rw [intLattice_sUnitBasis] at hy
  obtain ⟨x, hx⟩ := (mem_sUnitLattice L (placesOverSet K L S)).1 hy
  exact ⟨Additive.ofMul x, Subtype.ext hx⟩

/-- **The Herbrand quotient of the `S`-unit group equals that of the `S`-unit lattice**: the
logarithmic embedding is surjective onto the lattice with finite (torsion) kernel. -/
theorem herbrand_sUnitGroup_eq_lattice [Fintype (L ≃ₐ[K] L)] {σ : L ≃ₐ[K] L}
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g) :
    CyclicTate.herbrand (L ≃ₐ[K] L) (Additive (SUnitGroup K L S)) σ
      = CyclicTate.herbrand (L ≃ₐ[K] L)
        (NoetherDeuring.intLattice ⇑(sUnitBasis L (placesOverSet K L S))) σ := by
  haveI := finite_ker_sLogEquivariant L S
  haveI : Finite ((NoetherDeuring.intLattice ⇑(sUnitBasis L (placesOverSet K L S)))
      ⧸ (sLogEquivariant L S).toAddMonoidHom.range) := by
    rw [range_sLogEquivariant]
    haveI := QuotientAddGroup.subsingleton_quotient_top
      (G := NoetherDeuring.intLattice ⇑(sUnitBasis L (placesOverSet K L S)))
    exact Finite.of_subsingleton
  haveI : Finite (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (SUnitGroup K L S)) σ) :=
    CyclicTate.finite_tateH0_of_moduleFinite hgen
  haveI : Finite (CyclicTate.TateH1 (L ≃ₐ[K] L) (Additive (SUnitGroup K L S)) σ) :=
    CyclicTate.finite_tateH1_of_moduleFinite hgen
  exact CyclicTate.herbrand_eq_of_finite_ker_coker (sLogEquivariant L S) σ

/-! ## From `ℤ[S_L]⁰` to the integral lattice in the hyperplane -/

/-- The inclusion of `ℤ[S_L]⁰` into the trace-zero hyperplane, landing in the lattice spanned
by the standard basis `NumberField.intBasis`. -/
def kerTotalToIntLattice :
    PermLattice.kerTotal (G := L ≃ₐ[K] L) (Ω := SPlace L (placesOverSet K L S)) →+
      (NoetherDeuring.intLattice ⇑(intBasis L (placesOverSet K L S))) where
  toFun f :=
    ⟨⟨fun p ↦ ((PermLattice.eval
        (f : PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S))) p : ℤ) : ℝ), by
      rw [mem_sHyperplane, ← Int.cast_sum,
        show (∑ p : SPlace L (placesOverSet K L S), PermLattice.eval
            (f : PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S))) p)
          = PermLattice.total
            (f : PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S))) from rfl,
        PermLattice.mem_kerTotal.1 f.2, Int.cast_zero]⟩, by
      rw [intLattice_intBasis_eq_intHyper]
      exact ⟨fun p ↦ PermLattice.eval
        (f : PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S))) p, fun p ↦ rfl⟩⟩
  map_zero' := Subtype.ext (Subtype.ext (funext fun p ↦ by
    show ((PermLattice.eval ((0 : PermLattice.kerTotal (G := L ≃ₐ[K] L)
        (Ω := SPlace L (placesOverSet K L S)))
      : PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S))) p : ℤ) : ℝ) = 0
    rw [show ((0 : PermLattice.kerTotal (G := L ≃ₐ[K] L)
        (Ω := SPlace L (placesOverSet K L S)))
        : PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S))) = 0 from rfl,
      PermLattice.eval_zero, Int.cast_zero]))
  map_add' f g := Subtype.ext (Subtype.ext (funext fun p ↦ by
    show ((PermLattice.eval ((f + g : PermLattice.kerTotal (G := L ≃ₐ[K] L)
          (Ω := SPlace L (placesOverSet K L S)))
        : PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S))) p : ℤ) : ℝ)
      = ((PermLattice.eval
          (f : PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S))) p : ℤ) : ℝ)
        + ((PermLattice.eval
          (g : PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S))) p : ℤ) : ℝ)
    rw [show ((f + g : PermLattice.kerTotal (G := L ≃ₐ[K] L)
          (Ω := SPlace L (placesOverSet K L S)))
        : PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S)))
      = (f : PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S)))
        + (g : PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S))) from rfl,
      PermLattice.eval_add, Int.cast_add]))

omit [NumberField K] in
theorem coe_kerTotalToIntLattice
    (f : PermLattice.kerTotal (G := L ≃ₐ[K] L) (Ω := SPlace L (placesOverSet K L S)))
    (p : SPlace L (placesOverSet K L S)) :
    ((kerTotalToIntLattice L S f
        : NoetherDeuring.intLattice ⇑(intBasis L (placesOverSet K L S)))
      : SPlace L (placesOverSet K L S) → ℝ) p
      = ((PermLattice.eval
          (f : PermLattice (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S))) p : ℤ) : ℝ) := rfl

omit [NumberField K] in
theorem kerTotalToIntLattice_bijective :
    Function.Bijective (kerTotalToIntLattice L S) := by
  constructor
  · intro f g h
    refine Subtype.ext (PermLattice.ext fun p ↦ ?_)
    have h' := congrArg
      (fun z : NoetherDeuring.intLattice ⇑(intBasis L (placesOverSet K L S)) ↦
        ((z : sHyperplane L (placesOverSet K L S))
          : SPlace L (placesOverSet K L S) → ℝ) p) h
    rw [coe_kerTotalToIntLattice, coe_kerTotalToIntLattice] at h'
    exact_mod_cast h'
  · rintro ⟨⟨y, hy⟩, hy'⟩
    rw [intLattice_intBasis_eq_intHyper] at hy'
    obtain ⟨n, hn⟩ := hy'
    have hsum : PermLattice.total (PermLattice.ofFun (G := L ≃ₐ[K] L) n) = 0 := by
      have h0 : ∑ p : SPlace L (placesOverSet K L S), y p = 0 :=
        (mem_sHyperplane L (placesOverSet K L S)).1 hy
      have h1 : ((∑ p : SPlace L (placesOverSet K L S), n p : ℤ) : ℝ) = 0 := by
        rw [Int.cast_sum, ← h0]
        exact Finset.sum_congr rfl fun p _ ↦ (hn p).symm
      exact_mod_cast h1
    refine ⟨⟨PermLattice.ofFun n, PermLattice.mem_kerTotal.2 hsum⟩, ?_⟩
    exact Subtype.ext (Subtype.ext (funext fun p ↦ (hn p).symm))

/-- **`ℤ[S_L]⁰` is the integral lattice of the trace-zero hyperplane**, equivariantly. -/
def kerTotalAddEquiv :
    PermLattice.kerTotal (G := L ≃ₐ[K] L) (Ω := SPlace L (placesOverSet K L S)) ≃+
      (NoetherDeuring.intLattice ⇑(intBasis L (placesOverSet K L S))) :=
  AddEquiv.ofBijective (kerTotalToIntLattice L S) (kerTotalToIntLattice_bijective L S)

omit [NumberField K] in
theorem kerTotalAddEquiv_equivariant (σ : L ≃ₐ[K] L)
    (f : PermLattice.kerTotal (G := L ≃ₐ[K] L) (Ω := SPlace L (placesOverSet K L S))) :
    kerTotalAddEquiv L S (σ • f) = σ • kerTotalAddEquiv L S f :=
  Subtype.ext (Subtype.ext (funext fun _ ↦ rfl))

omit [NumberField K] in
/-- **The Herbrand quotient of `ℤ[S_L]⁰` equals that of the integral lattice in the trace-zero
hyperplane.** -/
theorem herbrand_kerTotal_eq_intLattice [Fintype (L ≃ₐ[K] L)] (σ : L ≃ₐ[K] L) :
    CyclicTate.herbrand (L ≃ₐ[K] L)
        (PermLattice.kerTotal (G := L ≃ₐ[K] L) (Ω := SPlace L (placesOverSet K L S))) σ
      = CyclicTate.herbrand (L ≃ₐ[K] L)
        (NoetherDeuring.intLattice ⇑(intBasis L (placesOverSet K L S))) σ :=
  CyclicTate.herbrand_eq_of_addEquiv (kerTotalAddEquiv L S)
    (kerTotalAddEquiv_equivariant L S) σ

/-! ## The Herbrand quotient of the `S`-unit group -/

variable {L}

/-- **The Herbrand quotient of the group of `S`-units of a cyclic extension `L / K`:**

`h(O_{L,S}^×) = (∏_{v ∈ S ∪ S_∞} n_v) / n`,

where `n = [L : K]` and `n_v` is the order of the decomposition group at a place of `L` above
`v`.  This is Dirichlet's `S`-unit theorem (`NumberField.sUnitBasis`) combined with the
Noether-Deuring comparison `CyclicTate.herbrand_intLattice_eq_of_stable` and the Herbrand
quotient of the augmentation ideal `NumberField.herbrand_kerTotal_sPlace`. -/
theorem herbrand_sUnitGroup [IsGalois K L] [Fintype S] {σ : L ≃ₐ[K] L}
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (w₁ : ∀ v : InfinitePlace K, Fibre L v)
    (w₂ : ∀ v : S, FinitePlaceFibre L (v : HeightOneSpectrum (𝓞 K))) :
    CyclicTate.herbrand (L ≃ₐ[K] L) (Additive (SUnitGroup K L S)) σ
      = ((∏ v : InfinitePlace K, (Nat.card (stabilizer (L ≃ₐ[K] L) (w₁ v)) : ℚ))
          * ∏ v : S, (Nat.card (stabilizer (L ≃ₐ[K] L) (w₂ v)) : ℚ))
        / (Nat.card (L ≃ₐ[K] L) : ℚ) := by
  rw [herbrand_sUnitGroup_eq_lattice L S hgen, herbrand_sUnitLattice_eq_intHyper S hgen,
    ← herbrand_kerTotal_eq_intLattice L S σ, herbrand_kerTotal_sPlace S hgen w₁ w₂]

/-- **The Herbrand quotient of the `S`-units, in division-free form:**
`h(O_{L,S}^×) · [L : K] = ∏_{v ∈ S ∪ S_∞} n_v`. -/
theorem herbrand_sUnitGroup_mul_card [IsGalois K L] [Fintype S] {σ : L ≃ₐ[K] L}
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (w₁ : ∀ v : InfinitePlace K, Fibre L v)
    (w₂ : ∀ v : S, FinitePlaceFibre L (v : HeightOneSpectrum (𝓞 K))) :
    CyclicTate.herbrand (L ≃ₐ[K] L) (Additive (SUnitGroup K L S)) σ
        * (Nat.card (L ≃ₐ[K] L) : ℚ)
      = (∏ v : InfinitePlace K, (Nat.card (stabilizer (L ≃ₐ[K] L) (w₁ v)) : ℚ))
        * ∏ v : S, (Nat.card (stabilizer (L ≃ₐ[K] L) (w₂ v)) : ℚ) := by
  rw [herbrand_sUnitGroup S hgen w₁ w₂, div_mul_cancel₀]
  exact_mod_cast (Nat.card_pos (α := L ≃ₐ[K] L)).ne'

end Galois

end NumberField
