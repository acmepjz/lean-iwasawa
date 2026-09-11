/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.AdicCompletionDecomposition
public import Iwasawalib.NumberTheory.CFT.FiniteAdeleSemilocal
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

@[expose] public section

/-!
# `S`-integers and `S`-units of a number field as a Galois module

Let `L / K` be an extension of number fields and let `S` be a set of finite places of `K`.
Write `S_L` for the set of finite places of `L` lying above a place in `S`.  The ring of
`S`-integers `O_{L,S}` and the group of `S`-units `O_{L,S}^×` are `Set.integer` and
`Set.unit` of Mathlib, applied to `S_L`.  Because `S_L` is by construction stable under
`Gal(L/K)`, both carry an action of `Gal(L/K)`, and this file builds it.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace NumberField

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ## The places above a set of places of the base field -/

/-- The set of finite places of `L` lying above a set `S` of finite places of `K`. -/
def placesOverSet (S : Set (HeightOneSpectrum (𝓞 K))) : Set (HeightOneSpectrum (𝓞 L)) :=
  {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ S}

variable {K L}

omit [NumberField K] [NumberField L] in
@[simp]
theorem mem_placesOverSet {S : Set (HeightOneSpectrum (𝓞 K))} {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ placesOverSet K L S ↔ w.under (𝓞 K) ∈ S := Iff.rfl

omit [NumberField K] [NumberField L] in
/-- The Galois action preserves the place of `K` lying under a place of `L`. -/
@[simp]
theorem under_smul_eq (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    (σ • w).under (𝓞 K) = w.under (𝓞 K) :=
  HeightOneSpectrum.ext (under_smul_heightOneSpectrum σ w)

omit [NumberField K] [NumberField L] in
theorem placesOverSet_eq_iUnion (S : Set (HeightOneSpectrum (𝓞 K))) :
    placesOverSet K L S = ⋃ v ∈ S, placesOver K L v := by
  ext w
  rw [mem_placesOverSet, Set.mem_iUnion₂]
  constructor
  · exact fun h ↦ ⟨_, h, (placesOver_eq_setOf_under_eq K L _ ▸ rfl : w ∈ placesOver K L _)⟩
  · rintro ⟨v, hv, hw⟩
    rw [placesOver_eq_setOf_under_eq] at hw
    exact hw ▸ hv
    
omit [NumberField K] [NumberField L] in
theorem placesOverSet_mono {S S' : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S') :
    placesOverSet K L S ⊆ placesOverSet K L S' := fun _ hw ↦ h hw

omit [NumberField K] [NumberField L] in
@[simp]
theorem placesOverSet_empty : placesOverSet K L (∅ : Set (HeightOneSpectrum (𝓞 K))) = ∅ := rfl

omit [NumberField K] [NumberField L] in
@[simp]
theorem placesOverSet_univ :
    placesOverSet K L (Set.univ : Set (HeightOneSpectrum (𝓞 K))) = Set.univ := rfl

omit [NumberField K] [NumberField L] in
theorem placesOverSet_union (S S' : Set (HeightOneSpectrum (𝓞 K))) :
    placesOverSet K L (S ∪ S') = placesOverSet K L S ∪ placesOverSet K L S' := rfl

/-- A finite set of finite places of `K` has only finitely many places of `L` above it. -/
theorem finite_placesOverSet {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    (placesOverSet K L S).Finite := by
  rw [placesOverSet_eq_iUnion]
  exact hS.biUnion fun v _ ↦ finite_placesOver K L v

omit [NumberField K] [NumberField L] in
/-- `S_L` is stable under the action of `Gal(L/K)` on the finite places of `L`. -/
@[simp]
theorem smul_mem_placesOverSet {S : Set (HeightOneSpectrum (𝓞 K))} (σ : L ≃ₐ[K] L)
    {w : HeightOneSpectrum (𝓞 L)} : σ • w ∈ placesOverSet K L S ↔ w ∈ placesOverSet K L S := by
  rw [mem_placesOverSet, mem_placesOverSet, under_smul_eq]

omit [NumberField K] [NumberField L] in
theorem placesOverSet_smul_eq (S : Set (HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L) :
    (fun w ↦ σ • w) ⁻¹' placesOverSet K L S = placesOverSet K L S := by
  ext w
  exact smul_mem_placesOverSet σ

/-! ## `S`-integers and `S`-units -/

variable (K L)

/-- The ring `O_{L,S}` of `S`-integers of `L`, for `S` a set of finite places of the base
field `K`: the elements of `L` that are integral at every finite place of `L` not above `S`.
(The archimedean places of `L` are implicitly always in `S`.) -/
abbrev SIntegers (S : Set (HeightOneSpectrum (𝓞 K))) : Subalgebra (𝓞 L) L :=
  (placesOverSet K L S).integer L

/-- The group `O_{L,S}^×` of `S`-units of `L`: the elements of `Lˣ` whose valuation is `1` at
every finite place of `L` not above `S`. -/
abbrev SUnitGroup (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup Lˣ :=
  (placesOverSet K L S).unit L

variable {K L}

omit [NumberField K] in
theorem mem_SIntegers {S : Set (HeightOneSpectrum (𝓞 K))} {x : L} :
    x ∈ SIntegers K L S ↔
      ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S → w.valuation L x ≤ 1 :=
  Iff.rfl

omit [NumberField K] in
theorem mem_SUnitGroup {S : Set (HeightOneSpectrum (𝓞 K))} {x : Lˣ} :
    x ∈ SUnitGroup K L S ↔
      ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S → w.valuation L (x : L) = 1 :=
  Iff.rfl

omit [NumberField K] [NumberField L] in
@[simp]
theorem coe_smul_units (σ : L ≃ₐ[K] L) (x : Lˣ) : ((σ • x : Lˣ) : L) = σ (x : L) := rfl

/-! ## The Galois action on `S`-integers and `S`-units -/

omit [NumberField K] in
/-- The ring of `S`-integers is stable under `Gal(L/K)`. -/
theorem smul_mem_SIntegers {S : Set (HeightOneSpectrum (𝓞 K))} (σ : L ≃ₐ[K] L) {x : L}
    (hx : x ∈ SIntegers K L S) : σ x ∈ SIntegers K L S := by
  rw [mem_SIntegers] at hx ⊢
  intro w hw
  rw [valuation_inv_smul]
  exact hx _ (by rwa [under_smul_eq])

omit [NumberField K] in
/-- The group of `S`-units is stable under `Gal(L/K)`. -/
theorem smul_mem_SUnitGroup {S : Set (HeightOneSpectrum (𝓞 K))} (σ : L ≃ₐ[K] L) {x : Lˣ}
    (hx : x ∈ SUnitGroup K L S) : σ • x ∈ SUnitGroup K L S := by
  rw [mem_SUnitGroup] at hx ⊢
  intro w hw
  rw [coe_smul_units, valuation_inv_smul]
  exact hx _ (by rwa [under_smul_eq])

omit [NumberField K] in
@[simp]
theorem smul_mem_SUnitGroup_iff {S : Set (HeightOneSpectrum (𝓞 K))} (σ : L ≃ₐ[K] L) {x : Lˣ} :
    σ • x ∈ SUnitGroup K L S ↔ x ∈ SUnitGroup K L S := by
  refine ⟨fun h ↦ ?_, smul_mem_SUnitGroup σ⟩
  have := smul_mem_SUnitGroup σ⁻¹ h
  rwa [inv_smul_smul] at this

variable (K L)

/-- The `S`-units form a `Gal(L/K)`-module: `Gal(L/K)` acts on `O_{L,S}^×` by multiplicative
automorphisms. -/
instance sUnitGroupMulDistribMulAction (S : Set (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L) (SUnitGroup K L S) where
  smul σ x := ⟨σ • (x : Lˣ), smul_mem_SUnitGroup σ x.2⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_mul _ _ _ := Subtype.ext (smul_mul' _ _ _)
  smul_one _ := Subtype.ext (smul_one _)

variable {K L}

omit [NumberField K] in
@[simp]
theorem coe_smul_SUnitGroup {S : Set (HeightOneSpectrum (𝓞 K))} (σ : L ≃ₐ[K] L)
    (x : SUnitGroup K L S) : ((σ • x : SUnitGroup K L S) : Lˣ) = σ • (x : Lˣ) := rfl

/-! ## Comparison with the base field -/

/-- Being a unit at `w` can be tested downstairs: for `x` in the base field, the `w`-adic
valuation of `x` is `1` if and only if its valuation at the place below `w` is `1`.  The point
is that the base change map on valuations raises to the (nonzero) ramification index. -/
theorem valuation_algebraMap_eq_one_iff (w : HeightOneSpectrum (𝓞 L)) (x : K) :
    w.valuation L (algebraMap K L x) = 1 ↔ (w.under (𝓞 K)).valuation K x = 1 := by
  rw [← valuation_liesOver L (w.under (𝓞 K)) w x,
    pow_eq_one_iff_left (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal
      (w.under (𝓞 K)).ne_bot)]

/-- An `S`-unit of `K` becomes an `S`-unit of `L`, and conversely. -/
theorem map_mem_SUnitGroup_iff {S : Set (HeightOneSpectrum (𝓞 K))} (x : Kˣ) :
    Units.map (algebraMap K L : K →* L) x ∈ SUnitGroup K L S ↔ x ∈ S.unit K := by
  constructor
  · intro hx v hv
    obtain ⟨w, hw⟩ := exists_under_eq (B := 𝓞 L) v
    have := hx w (by rw [mem_placesOverSet] at *; rw [hw]; exact hv)
    rwa [show ((Units.map (algebraMap K L : K →* L) x : Lˣ) : L) = algebraMap K L (x : K) from rfl,
      valuation_algebraMap_eq_one_iff, hw] at this
  · intro hx w hw
    rw [show ((Units.map (algebraMap K L : K →* L) x : Lˣ) : L) = algebraMap K L (x : K) from rfl,
      valuation_algebraMap_eq_one_iff]
    exact hx _ hw

/-- **The `Gal(L/K)`-invariant `S`-units of `L` are the `S`-units of `K`.** -/
theorem SUnitGroup_fixed [IsGalois K L] (S : Set (HeightOneSpectrum (𝓞 K))) :
    {x : Lˣ | x ∈ SUnitGroup K L S ∧ ∀ σ : L ≃ₐ[K] L, σ • x = x}
      = Units.map (algebraMap K L : K →* L) '' (S.unit K) := by
  ext x
  constructor
  · rintro ⟨hx, hfix⟩
    have hmem : (x : L) ∈ (⊥ : IntermediateField K L) := by
      refine (IsGalois.mem_bot_iff_fixed (F := K) (E := L) (x : L)).2 fun σ ↦ ?_
      exact congrArg (fun u : Lˣ ↦ (u : L)) (hfix σ)
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 hmem
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact x.ne_zero (by simpa using hy.symm)
    refine ⟨Units.mk0 y hy0, ?_, ?_⟩
    · rw [SetLike.mem_coe, ← map_mem_SUnitGroup_iff (L := L)]
      convert hx using 1
      exact Units.ext hy
    · exact Units.ext hy
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(map_mem_SUnitGroup_iff (L := L) y).2 hy, fun σ ↦ ?_⟩
    refine Units.ext ?_
    rw [coe_smul_units]
    exact σ.commutes (y : K)

end NumberField
