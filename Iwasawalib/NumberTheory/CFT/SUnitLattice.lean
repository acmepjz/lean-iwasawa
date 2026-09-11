/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.SUnitSpan

@[expose] public section

/-!
# Dirichlet's `S`-unit theorem: the `S`-unit log image is a full lattice

Let `L` be a number field and `T` a finite set of finite places of `L`, and let
`S = SPlace L T` be the corresponding set of `S`-places.  `Iwasawalib/NumberTheory/CFT/
SUnitSpan.lean` proves that the image of `O_{L,S}^×` under the logarithmic embedding **spans**
the trace-zero hyperplane `(∏_{p ∈ S} ℝ)⁰` over `ℝ`.  This file supplies the other half of
Dirichlet's `S`-unit theorem: that image is a **full lattice**, i.e. it is a free `ℤ`-module of
rank exactly `#S - 1`, so that any of its `ℤ`-bases is simultaneously an `ℝ`-basis of the
hyperplane (`NumberField.sUnitBasis`).

This is the hypothesis needed by `CyclicTate.herbrand_intLattice_eq_of_stable`, and it is what
turns the real isomorphism `O_{L,S}^× ⊗ ℝ ≅ (∏_{w ∈ S} ℝ)⁰` into a statement about lattices.

## Proof

Mathlib has no `S`-unit lattice: `Mathlib/RingTheory/DedekindDomain/SInteger.lean` defines
`Set.integer` and `Set.unit` and nothing else, and
`Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.lean` covers only the case `T = ∅`.

No Northcott-type finiteness argument is needed here, because the finite generation of
`O_{L,S}^×` is already available as `NumberField.module_finite_sUnit`, proved in
`Iwasawalib/NumberTheory/CFT/SUnitDivisor.lean` from the exact sequence
`1 → (𝓞 L)ˣ → O_{L,S}^× → ℤ^T`, and its rank is `NumberField.finrank_sUnit`.  So write
`Λ` for the log image (`NumberField.sUnitLattice`) and argue purely with ranks:

* `Λ` is a quotient of `O_{L,S}^×`, hence finitely generated, and it is torsion free because it
  sits inside a real vector space; so it is free, of some rank `r`;
* `r ≤ #S - 1`, because `Λ` is the range of a linear map out of a module of rank `#S - 1`
  (`NumberField.finrank_sUnit`);
* `r ≥ #S - 1`, because a `ℤ`-basis of `Λ` is an `ℝ`-spanning family of the hyperplane
  (`NumberField.sUnitSpan_eq_sHyperplane`), whose dimension is `#S - 1`.

Hence `r = #S - 1`, and a spanning family of `#S - 1` vectors in a space of dimension
`#S - 1` is a basis.

Note that the danger this rules out is real: a finitely generated subgroup of `ℝ^d` spanning
`ℝ^d` need *not* be a lattice — `ℤ + √2 ℤ ⊆ ℝ` is free of rank `2` and spans a line.  It is
the rank equality, i.e. Dirichlet's theorem, that excludes it.

## Main definitions

* `NumberField.sLogHyp` : the logarithmic embedding of `O_{L,S}^×` into `(∏_{p ∈ S} ℝ)⁰`.
* `NumberField.sUnitLattice` : its image, the `S`-unit lattice.
* `NumberField.sRank` : the common rank `#S - 1`.
* `NumberField.sUnitLatticeBasis` : a `ℤ`-basis of the `S`-unit lattice.
* `NumberField.sUnitBasis` : the same vectors, as an `ℝ`-basis of the hyperplane.

## Main statements

* `NumberField.span_sUnitLattice_eq_top` : the lattice spans the hyperplane over `ℝ`.
* `NumberField.finrank_sUnitLattice` : `rank_ℤ Λ = #S - 1`.
* `NumberField.span_sUnitBasisVec_int` : the `ℤ`-span of the basis vectors is exactly `Λ`.
* `NumberField.finite_ker_sLogHyp` : the kernel of the logarithmic embedding on `O_{L,S}^×` is
  finite, so `Λ` is `O_{L,S}^×` modulo torsion.
* `NumberField.sUnitQuotEquivLattice`, `NumberField.moduleFinite_sUnitQuot`,
  `NumberField.moduleFree_sUnitQuot`, `NumberField.finrank_sUnitQuot` : `O_{L,S}^×` modulo
  torsion is free of rank `#S - 1`.
* `NumberField.discreteTopology_sUnitLattice`, `NumberField.isZLattice_sUnitLattice` : the
  lattice is discrete, and is a full `ℤ`-lattice in the hyperplane.  Discreteness is a
  *consequence* here, not an input.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField.InfinitePlace
open Module

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]
variable {T : Set (HeightOneSpectrum (𝓞 L))}

section Defs

variable (L T) [Fintype T]

/-- The logarithmic embedding of the `S`-unit group, viewed as landing in the trace-zero
hyperplane `(∏_{p ∈ S} ℝ)⁰`. -/
def sLogHyp : Additive (T.unit L) →+ (sHyperplane L T) where
  toFun x := ⟨fun p ↦ sLog p ((Additive.toMul x : T.unit L) : Lˣ),
    (mem_sHyperplane L T).2 (sum_sLog_eq_zero (Additive.toMul x).2)⟩
  map_zero' := Subtype.ext (funext fun p ↦ sLog_one p)
  map_add' _ _ := Subtype.ext (funext fun p ↦ sLog_mul p _ _)

@[simp]
theorem coe_sLogHyp (x : Additive (T.unit L)) :
    ((sLogHyp L T x : sHyperplane L T) : SPlace L T → ℝ)
      = sLogVec L T ((Additive.toMul x : T.unit L) : Lˣ) := rfl

/-- **The `S`-unit lattice**: the image of the `S`-unit group under the logarithmic embedding,
as a `ℤ`-submodule of the trace-zero hyperplane. -/
def sUnitLattice : Submodule ℤ (sHyperplane L T) :=
  LinearMap.range (sLogHyp L T).toIntLinearMap

theorem mem_sUnitLattice {y : sHyperplane L T} :
    y ∈ sUnitLattice L T ↔ ∃ x : T.unit L, sLogHyp L T (Additive.ofMul x) = y :=
  ⟨fun ⟨x, hx⟩ ↦ ⟨Additive.toMul x, hx⟩, fun ⟨x, hx⟩ ↦ ⟨Additive.ofMul x, hx⟩⟩

end Defs

/-! ## The `S`-unit lattice is finitely generated, free, and spans -/

section Finite

variable (L T) [Fintype T]

instance moduleFinite_sUnitGroup : Module.Finite ℤ (Additive (T.unit L)) :=
  module_finite_sUnit (Set.toFinite T)

instance moduleFinite_sUnitLattice : Module.Finite ℤ (sUnitLattice L T) := by
  rw [sUnitLattice, ← Submodule.map_top]
  exact Module.Finite.map _ _

omit [Fintype T] in
/-- A real vector space has no `ℤ`-torsion. -/
theorem noZeroSMulDivisors_int_of_module_real {V : Type*} [AddCommGroup V] [Module ℝ V] :
    NoZeroSMulDivisors ℤ V := by
  refine ⟨fun {m x} h ↦ ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · exact Or.inl rfl
  · refine Or.inr ?_
    have hk : (m : ℝ) ≠ 0 := Int.cast_ne_zero.2 hm
    have h' : (m : ℝ) • x = 0 := by rwa [Int.cast_smul_eq_zsmul]
    exact (smul_eq_zero.1 h').resolve_left hk

instance isTorsionFree_sHyperplane : IsTorsionFree ℤ (sHyperplane L T) :=
  have : NoZeroSMulDivisors ℤ (sHyperplane L T) := noZeroSMulDivisors_int_of_module_real
  inferInstance

instance moduleFree_sUnitLattice : Module.Free ℤ (sUnitLattice L T) :=
  inferInstance

/-- The image of the `S`-unit lattice in `∏_{p ∈ S} ℝ` is exactly the set of logarithmic
embedding vectors of the `S`-units. -/
theorem image_coe_sUnitLattice :
    (sHyperplane L T).subtype '' (sUnitLattice L T : Set (sHyperplane L T))
      = Set.range (fun x : T.unit L ↦ (fun p ↦ sLog p ((x : Lˣ)))) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx⟩ := (mem_sUnitLattice L T).1 hz
    exact ⟨x, by rw [← hx]; rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨sLogHyp L T (Additive.ofMul x), ⟨Additive.ofMul x, rfl⟩, rfl⟩

/-- **The `S`-unit lattice spans the trace-zero hyperplane over `ℝ`.**  This is
`NumberField.sUnitSpan_eq_sHyperplane` transported into the hyperplane itself. -/
theorem span_sUnitLattice_eq_top :
    Submodule.span ℝ (sUnitLattice L T : Set (sHyperplane L T)) = ⊤ := by
  refine Submodule.map_injective_of_injective (sHyperplane L T).injective_subtype ?_
  rw [Submodule.map_span, Submodule.map_subtype_top, image_coe_sUnitLattice,
    ← sUnitSpan, sUnitSpan_eq_sHyperplane]

end Finite

/-! ## The rank of the `S`-unit lattice, and the basis -/

section Rank

variable (L T) [Fintype T]

/-- The common value of the `ℤ`-rank of the `S`-unit lattice and the `ℝ`-dimension of the
trace-zero hyperplane: `#S - 1 = r₁ + r₂ - 1 + #T`. -/
def sRank : ℕ := Fintype.card (InfinitePlace L) + Fintype.card T - 1

theorem finrank_sHyperplane_eq_sRank : finrank ℝ (sHyperplane L T) = sRank L T :=
  finrank_sHyperplane L T

/-- The `S`-unit lattice has rank at most `#S - 1`, because it is a quotient of the `S`-unit
group, whose rank is `#S - 1` by `NumberField.finrank_sUnit`. -/
theorem finrank_sUnitLattice_le : finrank ℤ (sUnitLattice L T) ≤ sRank L T := by
  have h : finrank ℤ (sUnitLattice L T)
      ≤ finrank ℤ (Additive (T.unit L)) :=
    LinearMap.finrank_range_le (sLogHyp L T).toIntLinearMap
  refine h.trans ?_
  rw [finrank_sUnit (Set.toFinite T), NumberField.Units.rank, Nat.card_eq_fintype_card, sRank]
  have h1 : 1 ≤ Fintype.card (InfinitePlace L) := Fintype.card_pos
  omega

/-- The `S`-unit lattice has rank at least `#S - 1`, because it spans the hyperplane over `ℝ`
(`NumberField.span_sUnitLattice_eq_top`). -/
theorem sRank_le_finrank_sUnitLattice : sRank L T ≤ finrank ℤ (sUnitLattice L T) := by
  set r := finrank ℤ (sUnitLattice L T) with hr
  set b := Module.finBasis ℤ (sUnitLattice L T) with hb
  set c : Fin r → sHyperplane L T := fun i ↦ ((b i : sUnitLattice L T) : sHyperplane L T) with hc
  have hrange : Set.range c = (sUnitLattice L T).subtype '' (Set.range b) := by
    rw [← Set.range_comp]; rfl
  have hspanZ : Submodule.span ℤ (Set.range c) = sUnitLattice L T := by
    rw [hrange, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  have htop : Submodule.span ℝ (Set.range c) = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← span_sUnitLattice_eq_top L T]
    refine Submodule.span_le.2 ?_
    rw [← hspanZ]
    exact Submodule.span_subset_span ℤ ℝ (Set.range c)
  have hle : finrank ℝ (Submodule.span ℝ (Set.range c)) ≤ Fintype.card (Fin r) :=
    finrank_range_le_card (R := ℝ) c
  rw [htop, finrank_top, finrank_sHyperplane_eq_sRank, Fintype.card_fin] at hle
  exact hle

/-- **Dirichlet's `S`-unit theorem, lattice form.**  The `S`-unit lattice is a free `ℤ`-module
of rank exactly `#S - 1`, the dimension of the trace-zero hyperplane it spans. -/
theorem finrank_sUnitLattice : finrank ℤ (sUnitLattice L T) = sRank L T :=
  le_antisymm (finrank_sUnitLattice_le L T) (sRank_le_finrank_sUnitLattice L T)

/-- A `ℤ`-basis of the `S`-unit lattice, indexed by `Fin (#S - 1)`. -/
def sUnitLatticeBasis : Basis (Fin (sRank L T)) ℤ (sUnitLattice L T) :=
  Module.finBasisOfFinrankEq ℤ _ (finrank_sUnitLattice L T)

/-- The vectors of `NumberField.sUnitLatticeBasis`, viewed inside the hyperplane. -/
def sUnitBasisVec (i : Fin (sRank L T)) : sHyperplane L T :=
  ((sUnitLatticeBasis L T i : sUnitLattice L T) : sHyperplane L T)

theorem range_sUnitBasisVec :
    Set.range (sUnitBasisVec L T)
      = (sUnitLattice L T).subtype '' (Set.range (sUnitLatticeBasis L T)) := by
  rw [← Set.range_comp]; rfl

/-- The basis vectors generate the `S`-unit lattice over `ℤ`. -/
theorem span_sUnitBasisVec_int :
    Submodule.span ℤ (Set.range (sUnitBasisVec L T)) = sUnitLattice L T := by
  rw [range_sUnitBasisVec, ← Submodule.map_span, (sUnitLatticeBasis L T).span_eq,
    Submodule.map_subtype_top]

/-- The basis vectors span the hyperplane over `ℝ`. -/
theorem span_sUnitBasisVec_real :
    (⊤ : Submodule ℝ (sHyperplane L T)) ≤ Submodule.span ℝ (Set.range (sUnitBasisVec L T)) := by
  rw [← span_sUnitLattice_eq_top L T]
  refine Submodule.span_le.2 ?_
  rw [← span_sUnitBasisVec_int]
  exact Submodule.span_subset_span ℤ ℝ _

/-- **The full-lattice half of Dirichlet's `S`-unit theorem.**  A `ℤ`-basis of the `S`-unit
lattice is simultaneously an `ℝ`-basis of the trace-zero hyperplane `(∏_{p ∈ S} ℝ)⁰`.  Together
with `NumberField.span_sUnitBasisVec_int`, which says that the `ℤ`-span of these vectors is
exactly the `S`-unit lattice, this says that the logarithmic image of `O_{L,S}^×` is a *full*
lattice in the hyperplane. -/
def sUnitBasis : Basis (Fin (sRank L T)) ℝ (sHyperplane L T) :=
  basisOfTopLeSpanOfCardEqFinrank _ (span_sUnitBasisVec_real L T)
    (by rw [Fintype.card_fin, finrank_sHyperplane_eq_sRank])

@[simp]
theorem coe_sUnitBasis : ⇑(sUnitBasis L T) = sUnitBasisVec L T :=
  coe_basisOfTopLeSpanOfCardEqFinrank _ _ _

end Rank

/-! ## The kernel: the roots of unity -/

section Kernel

/-- An `S`-unit whose logarithmic embedding vanishes comes from a root of unity of `𝓞 L`. -/
theorem exists_torsion_of_sLog_eq_zero {x : Lˣ} (hx : x ∈ T.unit L)
    (h : ∀ p : SPlace L T, sLog p x = 0) :
    ∃ u : (𝓞 L)ˣ, u ∈ NumberField.Units.torsion L ∧
      Units.map (algebraMap (𝓞 L) L : (𝓞 L) →* L) u = x := by
  obtain ⟨u, hu⟩ := exists_unit_ringOfIntegers_of_valuation_eq_one
    (valuation_eq_one_of_sLog_eq_zero hx h)
  refine ⟨u, ?_, Units.ext hu⟩
  rw [NumberField.Units.mem_torsion]
  intro w
  rw [hu]
  exact infinitePlace_eq_one_of_sLog_eq_zero h w

variable (L T) [Fintype T]

theorem mem_ker_sLogHyp_iff {x : Additive (T.unit L)} :
    x ∈ LinearMap.ker (sLogHyp L T).toIntLinearMap
      ↔ ∀ p : SPlace L T, sLog p ((Additive.toMul x : T.unit L) : Lˣ) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h p
    exact congrFun (congrArg Subtype.val h) p
  · intro h
    exact Subtype.ext (funext h)

/-- **The kernel of the logarithmic embedding on the `S`-units is finite**: it is the group of
roots of unity of `L`.  This is the statement that the `S`-unit lattice is the `S`-unit group
modulo torsion. -/
instance finite_ker_sLogHyp :
    Finite (LinearMap.ker (sLogHyp L T).toIntLinearMap) := by
  classical
  set ι : LinearMap.ker (sLogHyp L T).toIntLinearMap → Lˣ :=
    fun x ↦ ((Additive.toMul (x : Additive (T.unit L)) : T.unit L) : Lˣ) with hι
  have hinj : Function.Injective ι := by
    intro x y hxy
    exact Subtype.ext (Additive.toMul.injective (Subtype.ext hxy))
  haveI : Finite ((NumberField.Units.torsion L : Set (𝓞 L)ˣ)) :=
    inferInstanceAs (Finite (NumberField.Units.torsion L))
  have hfin : (Set.range ι).Finite := by
    refine Set.Finite.subset
      (Set.Finite.image (Units.map (algebraMap (𝓞 L) L : (𝓞 L) →* L))
        (Set.toFinite (NumberField.Units.torsion L : Set (𝓞 L)ˣ))) ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨u, hu, hux⟩ := exists_torsion_of_sLog_eq_zero
      (Additive.toMul (x : Additive (T.unit L)) : T.unit L).2
      ((mem_ker_sLogHyp_iff L T).1 x.2)
    exact ⟨u, hu, hux⟩
  haveI := hfin.to_subtype
  refine Finite.of_injective (fun x ↦ (⟨ι x, Set.mem_range_self x⟩ : Set.range ι)) ?_
  intro x y h
  have h' : ι x = ι y := congrArg (fun z : Set.range ι ↦ (z : Lˣ)) h
  exact hinj h'

end Kernel

/-! ## The `S`-unit group modulo torsion, and discreteness -/

section Quotient

variable (L T) [Fintype T]

/-- **The `S`-unit group modulo the roots of unity is the `S`-unit lattice.**  Combined with
`NumberField.finite_ker_sLogHyp`, which identifies the kernel with the roots of unity of `L`,
this is the structure theorem `O_{L,S}^× ≅ μ(L) × ℤ^{#S - 1}` in the form needed here. -/
def sUnitQuotEquivLattice :
    (Additive (T.unit L) ⧸ LinearMap.ker (sLogHyp L T).toIntLinearMap) ≃ₗ[ℤ] sUnitLattice L T :=
  LinearMap.quotKerEquivRange (sLogHyp L T).toIntLinearMap

/-- **`O_{L,S}^×` modulo torsion is a finitely generated `ℤ`-module.** -/
instance moduleFinite_sUnitQuot :
    Module.Finite ℤ (Additive (T.unit L) ⧸ LinearMap.ker (sLogHyp L T).toIntLinearMap) :=
  Module.Finite.equiv (sUnitQuotEquivLattice L T).symm

/-- **`O_{L,S}^×` modulo torsion is free.** -/
instance moduleFree_sUnitQuot :
    Module.Free ℤ (Additive (T.unit L) ⧸ LinearMap.ker (sLogHyp L T).toIntLinearMap) :=
  Module.Free.of_equiv (sUnitQuotEquivLattice L T).symm

/-- **Dirichlet's `S`-unit theorem, structural form.**  `O_{L,S}^×` modulo torsion is free of
rank `#S - 1`. -/
theorem finrank_sUnitQuot :
    finrank ℤ (Additive (T.unit L) ⧸ LinearMap.ker (sLogHyp L T).toIntLinearMap)
      = sRank L T := by
  rw [(sUnitQuotEquivLattice L T).finrank_eq, finrank_sUnitLattice]

theorem span_coe_sUnitBasis_eq_sUnitLattice :
    Submodule.span ℤ (Set.range ⇑(sUnitBasis L T)) = sUnitLattice L T := by
  rw [coe_sUnitBasis, span_sUnitBasisVec_int]

/-- **The `S`-unit lattice is discrete.**  This is the Northcott half of Dirichlet's `S`-unit
theorem, in topological form; here it is a *consequence* of the rank computation rather than an
input to it, because `NumberField.sUnitBasis` exhibits the lattice as the `ℤ`-span of an
`ℝ`-basis. -/
instance discreteTopology_sUnitLattice : DiscreteTopology (sUnitLattice L T) := by
  rw [← span_coe_sUnitBasis_eq_sUnitLattice]
  infer_instance

/-- **The `S`-unit lattice is a full `ℤ`-lattice in the trace-zero hyperplane.** -/
instance isZLattice_sUnitLattice : IsZLattice ℝ (sUnitLattice L T) where
  span_top := span_sUnitLattice_eq_top L T

end Quotient

end NumberField