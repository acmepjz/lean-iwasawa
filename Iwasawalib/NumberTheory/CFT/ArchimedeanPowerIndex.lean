/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.UnitPowerIndex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

@[expose] public section

/-!
# The archimedean local power indices

`Iwasawalib/NumberTheory/CFT/LocalPowerIndexProduct.lean` computes
`PowerIndex.powIndex n (Additive (v.adicCompletion K)ˣ)` at the *finite* places of a number
field.  This file supplies the two archimedean values, which are small and explicit because
the completions are `ℝ` and `ℂ`:

* `ℂˣ` is divisible, so `[ℂˣ : (ℂˣ)ⁿ] = 1` for every `n ≠ 0`;
* `(ℝˣ)ⁿ = ℝˣ` for `n` odd and `(ℝˣ)ⁿ = ℝ_{>0}` for `n` even and nonzero, so
  `[ℝˣ : (ℝˣ)ⁿ]` is `1` or `2` according to the parity of `n`.

Transport to `v.Completion` is along Mathlib's
`NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal` and
`NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex`, using `PowerIndex.powIndex_congr_mulEquiv`, which is proved
here because `PowerIndex` had no transport lemma along an isomorphism.

## Main definitions

* `Real.posUnits` : the subgroup of positive units of `ℝ`, which is the subgroup of `n`-th
  powers for every even `n ≠ 0`.

## Main statements

* `PowerIndex.powIndex_congr`, `PowerIndex.powIndex_congr_mulEquiv` : `[A : nA]` is an
  isomorphism invariant.
* `Real.exists_pow_eq_of_odd` : every real number is an `n`-th power for `n` odd.
* `Real.powIndex_units_of_odd`, `Real.powIndex_units_of_even`, `Complex.powIndex_units` : the
  two local indices.
* `NumberField.InfinitePlace.powIndex_completion_units_of_isComplex`,
  `NumberField.InfinitePlace.powIndex_completion_units_of_isReal_of_odd`,
  `NumberField.InfinitePlace.powIndex_completion_units_of_isReal_of_even`,
  `NumberField.InfinitePlace.powIndex_completion_units_eq_one_or_two` : the same at an infinite place of a number
  field.
-/

noncomputable section

open PowerIndex

namespace PowerIndex

/-! ## Transport along an isomorphism -/

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] (n : ℕ)

/-- `[A : nA]` only depends on the isomorphism class of `A`. -/
theorem powIndex_congr (e : A ≃+ B) : powIndex n A = powIndex n B := by
  rw [powIndex, powIndex, ← AddSubgroup.index_comap_of_surjective
    (H := (nsmulAddMonoidHom (α := B) n).range) (f := (e : A →+ B)) e.surjective]
  congr 1
  ext x
  simp only [AddSubgroup.mem_comap, AddMonoidHom.coe_coe, mem_nsmul_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨e y, by rw [← map_nsmul, hy]⟩
  · rintro ⟨y, hy⟩
    exact ⟨e.symm y, e.injective (by rw [map_nsmul, e.apply_symm_apply, hy])⟩

/-- `[G : Gⁿ]` only depends on the isomorphism class of `G`. -/
theorem powIndex_congr_mulEquiv {G H : Type*} [CommGroup G] [CommGroup H] (e : G ≃* H) :
    powIndex n (Additive G) = powIndex n (Additive H) :=
  powIndex_congr n (AddEquiv.mk e.toEquiv e.map_mul')

end PowerIndex

/-! ## The two archimedean local fields -/

namespace Real

/-- The subgroup of positive units of `ℝ`, i.e. the `n`-th powers for `n` even. -/
def posUnits : Subgroup ℝˣ where
  carrier := {u : ℝˣ | 0 < (u : ℝ)}
  mul_mem' hu hv := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    exact mul_pos hu hv
  one_mem' := by simp
  inv_mem' hu := by
    simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val] at *
    exact inv_pos.2 hu

@[simp] theorem mem_posUnits {u : ℝˣ} : u ∈ posUnits ↔ 0 < (u : ℝ) := Iff.rfl

/-- Every real number is an `n`-th power for `n` odd. -/
theorem exists_pow_eq_of_odd {n : ℕ} (hn : Odd n) (x : ℝ) : ∃ y : ℝ, y ^ n = x := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  rcases le_or_gt 0 x with hx | hx
  · exact ⟨x ^ ((n : ℝ)⁻¹), Real.rpow_inv_natCast_pow hx hn0⟩
  · refine ⟨-((-x) ^ ((n : ℝ)⁻¹)), ?_⟩
    rw [hn.neg_pow, Real.rpow_inv_natCast_pow (le_of_lt (neg_pos.2 hx)) hn0, neg_neg]

/-- **The index `[ℝˣ : (ℝˣ)ⁿ]` for `n` odd is `1`.** -/
theorem powIndex_units_of_odd {n : ℕ} (hn : Odd n) : powIndex n (Additive ℝˣ) = 1 := by
  rw [powIndex_additive_eq_index n (⊤ : Subgroup ℝˣ) ?_, Subgroup.index_top]
  intro x
  refine ⟨fun _ ↦ Subgroup.mem_top _, fun _ ↦ ?_⟩
  obtain ⟨y, hy⟩ := exists_pow_eq_of_odd hn (x : ℝ)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow (show n ≠ 0 by rintro rfl; simp at hn)] at hy
    exact x.ne_zero hy.symm
  exact ⟨Units.mk0 y hy0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hy])⟩

/-- **The index `[ℝˣ : (ℝˣ)ⁿ]` for `n` even and nonzero is `2`.** -/
theorem powIndex_units_of_even {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) :
    powIndex n (Additive ℝˣ) = 2 := by
  have hpow : ∀ x : ℝˣ, (∃ y : ℝˣ, y ^ n = x) ↔ x ∈ posUnits := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      rw [mem_posUnits, Units.val_pow_eq_pow_val]
      exact hn.pow_pos y.ne_zero
    · intro hx
      rw [mem_posUnits] at hx
      refine ⟨Units.mk0 ((x : ℝ) ^ ((n : ℝ)⁻¹)) ?_, Units.ext ?_⟩
      · exact ne_of_gt (Real.rpow_pos_of_pos hx _)
      · rw [Units.val_pow_eq_pow_val, Units.val_mk0,
          Real.rpow_inv_natCast_pow hx.le hn0]
  rw [powIndex_additive_eq_index n posUnits hpow]
  refine Subgroup.index_eq_two_iff.2 ⟨-1, fun b ↦ ?_⟩
  rcases lt_or_gt_of_ne b.ne_zero with hb | hb
  · refine Or.inl ⟨?_, ?_⟩
    · rw [mem_posUnits, Units.val_mul, Units.val_neg, Units.val_one, mul_neg_one]
      exact neg_pos.2 hb
    · rw [mem_posUnits]; exact not_lt.2 hb.le
  · refine Or.inr ⟨by rwa [mem_posUnits], ?_⟩
    rw [mem_posUnits, Units.val_mul, Units.val_neg, Units.val_one, mul_neg_one]
    exact not_lt.2 (neg_nonpos.2 hb.le)

end Real

namespace Complex

/-- **The index `[ℂˣ : (ℂˣ)ⁿ]` is `1`: `ℂˣ` is divisible.** -/
theorem powIndex_units {n : ℕ} (hn : n ≠ 0) : powIndex n (Additive ℂˣ) = 1 := by
  rw [powIndex_additive_eq_index n (⊤ : Subgroup ℂˣ) ?_, Subgroup.index_top]
  intro x
  refine ⟨fun _ ↦ Subgroup.mem_top _, fun _ ↦ ?_⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hz
    exact x.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩

end Complex

/-! ## The local power index at an infinite place of a number field -/

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] {v : InfinitePlace K} {n : ℕ}

/-- **At a complex place the local power index is `1`.**  `L_v = ℂ` is divisible. -/
theorem powIndex_completion_units_of_isComplex (hv : v.IsComplex) (hn : n ≠ 0) :
    powIndex n (Additive v.Completionˣ) = 1 := by
  rw [powIndex_congr_mulEquiv n
    (Units.mapEquiv (Completion.ringEquivComplexOfIsComplex hv).toMulEquiv)]
  exact Complex.powIndex_units hn

/-- **At a real place the local power index is `1` for odd exponents.** -/
theorem powIndex_completion_units_of_isReal_of_odd (hv : v.IsReal) (hn : Odd n) :
    powIndex n (Additive v.Completionˣ) = 1 := by
  rw [powIndex_congr_mulEquiv n
    (Units.mapEquiv (Completion.ringEquivRealOfIsReal hv).toMulEquiv)]
  exact Real.powIndex_units_of_odd hn

/-- **At a real place the local power index is `2` for even exponents.** -/
theorem powIndex_completion_units_of_isReal_of_even (hv : v.IsReal) (hn : Even n) (hn0 : n ≠ 0) :
    powIndex n (Additive v.Completionˣ) = 2 := by
  rw [powIndex_congr_mulEquiv n
    (Units.mapEquiv (Completion.ringEquivRealOfIsReal hv).toMulEquiv)]
  exact Real.powIndex_units_of_even hn hn0

/-- **The archimedean local power index, in one statement.**  It is `2` exactly at the real
places with `n` even, and `1` everywhere else. -/
theorem powIndex_completion_units_eq_one_or_two (hn : n ≠ 0) :
    powIndex n (Additive v.Completionˣ) = 1 ∨
      (v.IsReal ∧ Even n ∧ powIndex n (Additive v.Completionˣ) = 2) := by
  rcases v.isReal_or_isComplex with hv | hv
  · rcases Nat.even_or_odd n with he | ho
    · exact Or.inr ⟨hv, he, powIndex_completion_units_of_isReal_of_even hv he hn⟩
    · exact Or.inl (powIndex_completion_units_of_isReal_of_odd hv ho)
  · exact Or.inl (powIndex_completion_units_of_isComplex hv hn)

end NumberField.InfinitePlace
