/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.PowerIndex
public import Iwasawalib.NumberTheory.LocalCFT.LocalHerbrand
public import Iwasawalib.NumberTheory.CFT.AdicCompletionCongr
public import Mathlib.RingTheory.RootsOfUnity.Basic

@[expose] public section

/-!
# The index of `n`-th powers in a discretely valued field: `[F^× : (F^×)^n] = n · [𝒪^× : (𝒪^×)^n]`

Chevalley's proof of the first fundamental inequality needs the **absolute** local index
`[K_v^× : (K_v^×)^n]`.  The valuation short exact sequence

`1 → 𝒪^× → F^× → ℤ → 0`

reduces it to the index of `n`-th powers in the units of the valuation ring, and that reduction
is proved here, unconditionally, from the six-term counting identity of
`Iwasawalib/NumberTheory/CFT/PowerIndex.lean`.

## Main statements

* `PowerIndex.powKer_additive_units_eq_card_rootsOfUnity` : `#(F^×)[n] = #μ_n(F)`, and
  `PowerIndex.powKer_additive_units_pos`, `PowerIndex.powKer_additive_units_le` : it is a
  positive number, at most `n`.
* `LocalCFT.unitsInclAdd_injective`, `LocalCFT.valAdd_surjective` and `LocalCFT.valAdd_eq_zero_iff` : the valuation sequence `0 → 𝒪^× → F^× → ℤ → 0` of abelian
  groups, for a valued field admitting a uniformiser.
* `LocalCFT.powIndex_units_eq_mul` : **`[F^× : (F^×)^n] = n · [𝒪^× : (𝒪^×)^n]`.**

## The remaining factor

The remaining factor `[𝒪^× : (𝒪^×)^n]` is `#μ_n(F) / |n|_F` for a local field, and it is proved
in `Iwasawalib/NumberTheory/LocalCFT/UnitPowerIndex.lean`
(`LocalCFT.powIndex_integers_units`, `NumberField.powIndex_adicCompletionIntegers_units`)
without the `p`-adic logarithm isomorphism `1 + 𝔪^m ≅ 𝔪^m` that Mathlib does not have: instead
the `p`-th power map `U^{(m)} → U^{(m+e)}` is shown to be bijective for `m (p-1) > e` directly
(`LocalCFT.isPowData_prime`, `LocalCFT.IsPowData.powEquiv`), with no `p`-adic logarithm and no
series.  Everything in the present file is independent of that argument.
-/

noncomputable section

open WithZero PowerIndex

namespace PowerIndex

/-! ## The `n`-torsion of the unit group of a domain -/

section Monoid

variable (R : Type*) [CommMonoid R] (n : ℕ)

/-- The `n`-torsion of `Additive Rˣ` is the group of `n`-th roots of unity of `R`. -/
def kerEquivRootsOfUnity :
    (nsmulAddMonoidHom (α := Additive Rˣ) n).ker ≃ rootsOfUnity n R where
  toFun x := ⟨Additive.toMul (x : Additive Rˣ), by
    rw [mem_rootsOfUnity, ← toMul_nsmul]
    exact congrArg Additive.toMul (mem_nsmul_ker.1 x.2)⟩
  invFun ζ := ⟨Additive.ofMul (ζ : Rˣ), mem_nsmul_ker.2 <| by
    refine Additive.toMul.injective ?_
    rw [toMul_nsmul, toMul_ofMul]
    exact (mem_rootsOfUnity n _).1 ζ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`#(R^×)[n] = #μ_n(R)`.** -/
theorem powKer_additive_units_eq_card_rootsOfUnity :
    powKer n (Additive Rˣ) = Nat.card (rootsOfUnity n R) :=
  Nat.card_congr (kerEquivRootsOfUnity R n)

end Monoid

section Domain

variable (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) [NeZero n]

instance finite_ker_nsmul_additive_units :
    Finite (nsmulAddMonoidHom (α := Additive Rˣ) n).ker :=
  Finite.of_equiv _ (kerEquivRootsOfUnity R n).symm

theorem powKer_additive_units_pos : 0 < powKer n (Additive Rˣ) :=
  Nat.card_pos_iff.2 ⟨⟨0⟩, inferInstance⟩

/-- `#(R^×)[n] ≤ n`: a domain has at most `n` `n`-th roots of unity. -/
theorem powKer_additive_units_le : powKer n (Additive Rˣ) ≤ n := by
  rw [powKer_additive_units_eq_card_rootsOfUnity]
  exact card_rootsOfUnity R n

end Domain

end PowerIndex

namespace LocalCFT

variable {F : Type*} [Field F] [Valued F ℤᵐ⁰]

/-! ## The valuation sequence, as a sequence of abelian groups -/

/-- The inclusion `𝒪^× → F^×`, additively. -/
def unitsInclAdd : Additive (integers (F := F))ˣ →+ Additive Fˣ where
  toFun u := Additive.ofMul (Units.map (integers (F := F)).subtype.toMonoidHom u.toMul)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem coe_unitsInclAdd (u : Additive (integers (F := F))ˣ) :
    ((Additive.toMul (unitsInclAdd u) : Fˣ) : F)
      = ((Additive.toMul u : (integers (F := F))ˣ) : integers (F := F)) := rfl

/-- The valuation `F^× → ℤ`, additively. -/
def valAdd : Additive Fˣ →+ ℤ where
  toFun u := Multiplicative.toAdd (valZ u.toMul)
  map_zero' := congrArg Multiplicative.toAdd (map_one valZ)
  map_add' u u' := congrArg Multiplicative.toAdd (map_mul valZ u.toMul u'.toMul)

@[simp] theorem valAdd_apply (u : Additive Fˣ) :
    valAdd u = Multiplicative.toAdd (valZ (Additive.toMul u)) := rfl

theorem unitsInclAdd_injective : Function.Injective (unitsInclAdd (F := F)) := by
  intro u u' h
  have h' : (Units.map (integers (F := F)).subtype.toMonoidHom u.toMul : Fˣ)
      = Units.map (integers (F := F)).subtype.toMonoidHom u'.toMul := h
  exact Units.ext (Subtype.ext (congrArg Units.val h'))

theorem valAdd_surjective (hπ : ∃ π : F, (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) :
    Function.Surjective (valAdd (F := F)) := by
  intro m
  obtain ⟨π, hπv⟩ := hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπv
    exact exp_ne_zero hπv.symm
  have hval : valZ (Units.mk0 π hπ0) = Multiplicative.ofAdd (-1 : ℤ) :=
    WithZero.coe_injective (by rw [coe_valZ]; exact hπv)
  refine ⟨Additive.ofMul ((Units.mk0 π hπ0) ^ (-m)), ?_⟩
  show Multiplicative.toAdd (valZ ((Units.mk0 π hπ0) ^ (-m))) = m
  rw [map_zpow, hval]
  simp

theorem valAdd_eq_zero_iff (u : Additive Fˣ) :
    valAdd u = 0 ↔ ∃ a : Additive (integers (F := F))ˣ, unitsInclAdd a = u := by
  constructor
  · intro hu
    have h1 : (Valued.v ((Additive.toMul u : Fˣ) : F) : ℤᵐ⁰) = 1 :=
      (valZ_eq_one_iff _).1 (Multiplicative.toAdd.injective hu)
    exact ⟨Additive.ofMul (unitOfValuedEqOne h1), congrArg Additive.ofMul (Units.ext rfl)⟩
  · rintro ⟨a, rfl⟩
    have hv : (Valued.v ((Additive.toMul (unitsInclAdd a) : Fˣ) : F) : ℤᵐ⁰) = 1 :=
      valued_coe_units (Additive.toMul a)
    show Multiplicative.toAdd (valZ (Additive.toMul (unitsInclAdd a))) = 0
    rw [show valZ (Additive.toMul (unitsInclAdd (F := F) a)) = 1 from (valZ_eq_one_iff _).2 hv]
    rfl

/-! ## The index of `n`-th powers -/

variable (F) in
/-- **Every `n`-th root of unity of `F` lies in `𝒪^×`**, so `F^×` and `𝒪^×` have the same
`n`-torsion. -/
theorem powKer_units_eq (n : ℕ) (hn : n ≠ 0) :
    powKer n (Additive (integers (F := F))ˣ) = powKer n (Additive Fˣ) := by
  refine powKer_eq_of_injective_of_torsion_le unitsInclAdd unitsInclAdd_injective ?_
  intro u hu
  refine (valAdd_eq_zero_iff u).1 ?_
  have h : n • valAdd u = 0 := by rw [← map_nsmul, hu, map_zero]
  exact by simpa [hn] using h

variable (F) in
/-- **`[F^× : (F^×)^n] = n · [𝒪^× : (𝒪^×)^n]`** for a valued field with a uniformiser.

The valuation sequence `1 → 𝒪^× → F^× → ℤ → 0` and the six-term counting identity
`PowerIndex.powIndex_mul_powIndex_mul_powKer`; the `n`-torsion cancels because `F^×` and `𝒪^×`
have the same roots of unity. -/
theorem powIndex_units_eq_mul (n : ℕ) (hn : n ≠ 0)
    (hπ : ∃ π : F, (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) :
    powIndex n (Additive Fˣ) = n * powIndex n (Additive (integers (F := F))ˣ) := by
  haveI : NeZero n := ⟨hn⟩
  have h := powIndex_mul_powIndex_mul_powKer (A := Additive (integers (F := F))ˣ)
    (B := Additive Fˣ) (C := ℤ) hn unitsInclAdd valAdd unitsInclAdd_injective
    (valAdd_surjective hπ) (fun u ↦ valAdd_eq_zero_iff u)
  rw [powIndex_int, powKer_int hn, mul_one, powKer_units_eq F n hn] at h
  have hμ : 0 < powKer n (Additive Fˣ) := powKer_additive_units_pos F n
  refine (Nat.eq_of_mul_eq_mul_right hμ ?_).symm
  rw [← h]
  ring

end LocalCFT

/-! ## The completion of a number field at a finite place -/

namespace NumberField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-- **`[K_v^× : (K_v^×)^n] = n · [O_v^× : (O_v^×)^n]`** at a finite place of a number field.

This is the whole of the valuation half of the local index `[K_v^× : (K_v^×)^n]`.  The
remaining factor `[O_v^× : (O_v^×)^n]` equals `#μ_n(K_v) / |n|_v`, and is
`NumberField.powIndex_adicCompletionIntegers_units`; the two are combined in
`NumberField.powIndex_adicCompletion_units`. -/
theorem powIndex_adicCompletion_units_eq_mul (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : n ≠ 0) :
    PowerIndex.powIndex n (Additive (v.adicCompletion K)ˣ)
      = n * PowerIndex.powIndex n
          (Additive (LocalCFT.integers (F := v.adicCompletion K))ˣ) :=
  LocalCFT.powIndex_units_eq_mul (v.adicCompletion K) n hn
    (valuedAdicCompletion_surjective (K := K) v (exp (-1 : ℤ)))

end NumberField
