/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.AbsoluteValue.RamificationIndex
public import Iwasawalib.NumberTheory.CFT.FiniteAdeleCongr
public import Iwasawalib.NumberTheory.CFT.FinitePlaceFibre
public import Iwasawalib.NumberTheory.CFT.SUnitLog
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.Basic

@[expose] public section

/-!
# The place formalism and the Dedekind formalism agree at a finite place

Ramification of a finite place of a number field is expressed in two different ways in this
repository.

* In `Iwasawalib/NumberTheory/AbsoluteValue/RamificationIndex.lean` a place is an
  `AbsoluteValue K ℝ` and its ramification index `AbsoluteValue.ramificationIdx` is the index of
  the inertia subgroups of a Galois group of absolute values; `AbsoluteValue.IsUnramified` and
  hence `NumberField.IsUnramifiedEverywhere` are phrased with it.
* In `Iwasawalib/NumberTheory/LocalCFT/` a finite place is an
  `IsDedekindDomain.HeightOneSpectrum (𝓞 L)` and ramification is
  `v.asIdeal.ramificationIdx' w.asIdeal = 1`.

This file connects the two at a finite place.  Mathlib already provides the underlying
*bijection* of places, `NumberField.FinitePlace.equivHeightOneSpectrum`, but nothing about
ramification: the comparison of the two ramification indices is proved here.

The bridge is `NumberField.inertiaSubgroup_eq_inertia`: for `w` a prime of `𝓞 L`, the inertia
subgroup of the absolute value `NumberField.HeightOneSpectrum.adicAbv L w` in the sense of
`AbsoluteValue.inertiaSubgroup` is Mathlib's `Ideal.inertia` of `w.asIdeal`.  Since Mathlib
computes the order of the latter (`Ideal.card_inertia_eq_ramificationIdxIn`), the two
ramification indices agree.

## Main statements

* `NumberField.mem_decompositionSubgroup_iff_smul_eq`: `D_w` is the stabiliser of `w`.
* `NumberField.inertiaSubgroup_eq_inertia`: the two inertia subgroups agree.
* `NumberField.ramificationIdx_eq_card_inertiaSubgroup`: for a Galois extension,
  `AbsoluteValue.ramificationIdx` is the order of the inertia subgroup.
* `NumberField.adicAbv_ramificationIdx_eq`: `e` computed in the place formalism is `e` computed
  in the Dedekind formalism.
* `NumberField.adicAbv_isUnramified_iff`: hence `AbsoluteValue.IsUnramified` is
  `v.asIdeal.ramificationIdx' w.asIdeal = 1`.
* `NumberField.ramificationIdx'_eq_one_of_isUnramifiedEverywhere` and
  `NumberField.ramificationIdx'_under_eq_one_of_isUnramifiedEverywhere`: an extension which is
  `NumberField.IsUnramifiedEverywhere` is unramified at every prime in the Dedekind sense.

## Scope

The last three statements assume `IsGalois K L`.  The Galois hypothesis is used exactly once,
in `NumberField.ramificationIdx_eq_card_inertiaSubgroup`, to take the normal extension in
`AbsoluteValue.ramificationIdx_spec` to be `L` itself; a non-Galois statement would have to
pass through a normal closure.  Archimedean places are not treated here: the converse of
`NumberField.ramificationIdx'_eq_one_of_isUnramifiedEverywhere` is false without a condition at
the infinite places.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped Pointwise

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
variable (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))

/-- The `w`-adic absolute value is `≤ 1` exactly where the `w`-adic valuation is. -/
theorem adicAbv_le_one_iff (x : L) :
    NumberField.HeightOneSpectrum.adicAbv L w x ≤ 1 ↔ w.valuation L x ≤ 1 := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, ← NNReal.coe_one, NNReal.coe_le_coe]
  exact WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w)

/-- The `w`-adic absolute value is `< 1` exactly where the `w`-adic valuation is. -/
theorem adicAbv_lt_one_iff (x : L) :
    NumberField.HeightOneSpectrum.adicAbv L w x < 1 ↔ w.valuation L x < 1 := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, ← NNReal.coe_one, NNReal.coe_lt_coe]
  exact WithZeroMulInt.toNNReal_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w)


omit [NumberField K] in
/-- The decomposition subgroup of the `w`-adic absolute value is the stabiliser of `w`. -/
theorem mem_decompositionSubgroup_iff_smul_eq (σ : L ≃ₐ[K] L) :
    σ ∈ (NumberField.HeightOneSpectrum.adicAbv L w).decompositionSubgroup K ↔ σ • w = w := by
  rw [AbsoluteValue.mem_decompositionSubgroup_iff_forall_apply_eq]
  constructor
  · intro h
    refine IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun y ↦ ?_)
    have hy : ∀ u : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
        y ∈ u.asIdeal ↔ u.valuation L (algebraMap (𝓞 L) L y) < 1 := fun u ↦
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) u y).symm
    rw [hy, hy, ← adicAbv_lt_one_iff, ← adicAbv_lt_one_iff]
    set z : L := algebraMap (𝓞 L) L y with hz
    have h2 : NumberField.HeightOneSpectrum.adicAbv L (σ • w) z
        = NumberField.HeightOneSpectrum.adicAbv L w (σ.symm z) := by
      conv_lhs => rw [← σ.apply_symm_apply z]
      exact adicAbv_smul σ w _
    rw [h2, ← h (σ.symm z), σ.apply_symm_apply]
  · intro h x
    conv_lhs => rw [← h]
    exact adicAbv_smul σ w x

omit [NumberField K] in
/-- **The place formalism and the Dedekind formalism agree**: the inertia subgroup of the
`w`-adic absolute value, in the sense of `AbsoluteValue.inertiaSubgroup`, is the inertia
subgroup of the prime `w.asIdeal`, in the sense of `Ideal.inertia`. -/
theorem inertiaSubgroup_eq_inertia :
    (NumberField.HeightOneSpectrum.adicAbv L w).inertiaSubgroup K
      = w.asIdeal.inertia (L ≃ₐ[K] L) := by
  ext σ
  rw [AbsoluteValue.mem_inertiaSubgroup_iff_of_isNonarchimedean _
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv L w),
    mem_decompositionSubgroup_iff_smul_eq, AddSubgroup.mem_inertia]
  constructor
  · rintro ⟨-, hI⟩ y
    have h1 : NumberField.HeightOneSpectrum.adicAbv L w (algebraMap (𝓞 L) L y) ≤ 1 :=
      (adicAbv_le_one_iff w _).2 (IsDedekindDomain.HeightOneSpectrum.valuation_le_one w y)
    have h2 := hI _ h1
    rw [adicAbv_lt_one_iff] at h2
    rw [Submodule.mem_toAddSubgroup,
      ← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]
    refine lt_of_le_of_lt (le_of_eq ?_) h2
    congr 1
  · intro hi
    have hstab : σ • w = w := by
      refine IsDedekindDomain.HeightOneSpectrum.ext ?_
      rw [IsDedekindDomain.HeightOneSpectrum.smul_asIdeal]
      exact Ideal.inertia_le_stabilizer w.asIdeal hi
    refine ⟨hstab, fun x hx ↦ ?_⟩
    rw [adicAbv_le_one_iff] at hx
    rw [adicAbv_lt_one_iff]
    obtain ⟨n, d, hnd⟩ :=
      IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer w x hx
    -- notation
    obtain ⟨dd, hdd⟩ := d
    simp only at hnd
    set a : L := algebraMap (𝓞 L) L dd with ha
    set b : L := algebraMap (𝓞 L) L n with hb
    have hσ : σ x * σ a = σ b := by rw [← map_mul, hnd]
    have hst : σ • w.asIdeal = w.asIdeal := Ideal.inertia_le_stabilizer w.asIdeal hi
    have hva : w.valuation L a = 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) w).2 hdd
    have hd' : (σ • dd) ∉ w.asIdeal := by
      intro hmem
      exact hdd ((Ideal.smul_mem_pointwise_smul_iff (a := σ)).1 (by rw [hst]; exact hmem))
    have hvσa : w.valuation L (σ a) = 1 := by
      have he : σ a = algebraMap (𝓞 L) L (σ • dd) := rfl
      rw [he]
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) w).2 hd'
    set N : 𝓞 L := (σ • n) * dd - n * (σ • dd) with hN
    have hNmem : N ∈ w.asIdeal := by
      have e1 : (σ • n) * dd - n * (σ • dd)
          = (σ • n - n) * dd - n * (σ • dd - dd) := by ring
      rw [hN, e1]
      exact sub_mem (Ideal.mul_mem_right _ _ (hi n)) (Ideal.mul_mem_left _ _ (hi _))
    have hNval : w.valuation L (algebraMap (𝓞 L) L N) < 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) w N).2 hNmem
    have key : (σ x - x) * (a * σ a) = algebraMap (𝓞 L) L N := by
      have hcast : algebraMap (𝓞 L) L N = σ b * a - b * σ a := by
        rw [hN]
        push_cast
        rfl
      rw [hcast]
      linear_combination a * hσ - σ a * hnd
    have hkey := congrArg (w.valuation L) key
    rw [map_mul, map_mul, hva, hvσa] at hkey
    simp only [mul_one] at hkey
    rw [hkey]
    exact hNval

omit [NumberField K] [NumberField L] in
/-- For a Galois extension of number fields, the ramification index of a place in the sense of
`AbsoluteValue.ramificationIdx` is the order of its inertia subgroup. -/
theorem ramificationIdx_eq_card_inertiaSubgroup [IsGalois K L] (u : AbsoluteValue L ℝ) :
    u.ramificationIdx K = Nat.card (u.inertiaSubgroup K) := by
  haveI : u.LiesOver u := ⟨by ext x; rfl⟩
  rw [AbsoluteValue.ramificationIdx_spec K u u, AbsoluteValue.ramificationIdxOfIsScalarTower,
    Subgroup.eq_bot_of_subsingleton (u.inertiaSubgroup L), Subgroup.map_bot,
    Subgroup.relIndex_bot_left]

/-- **The place formalism and the Dedekind formalism agree**: for a Galois extension of number
fields, the ramification index of the `w`-adic absolute value, in the sense of
`AbsoluteValue.ramificationIdx`, is the ramification index of `w` over `v`, in the sense of
`Ideal.ramificationIdx'`. -/
theorem adicAbv_ramificationIdx_eq [IsGalois K L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal] :
    (NumberField.HeightOneSpectrum.adicAbv L w).ramificationIdx K
      = v.asIdeal.ramificationIdx' w.asIdeal := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  rw [ramificationIdx_eq_card_inertiaSubgroup, inertiaSubgroup_eq_inertia,
    Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (L ≃ₐ[K] L),
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]

/-- **Unramifiedness in the place formalism and in the Dedekind formalism agree.** -/
theorem adicAbv_isUnramified_iff [IsGalois K L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal] :
    (NumberField.HeightOneSpectrum.adicAbv L w).IsUnramified K
      ↔ v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
  rw [AbsoluteValue.isUnramified_iff_ramificationIdx_eq_one, adicAbv_ramificationIdx_eq w v]

/-- The `w`-adic absolute value is a nontrivial absolute value. -/
theorem isNontrivial_adicAbv : (NumberField.HeightOneSpectrum.adicAbv L w).IsNontrivial := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  refine ⟨algebraMap (𝓞 L) L a, by simpa using ha0, ne_of_lt ?_⟩
  rw [adicAbv_lt_one_iff]
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) w a).2 ha

/-- **An extension unramified everywhere in the place formalism is unramified at every prime
in the Dedekind formalism.** -/
theorem ramificationIdx'_eq_one_of_isUnramifiedEverywhere [IsGalois K L]
    [NumberField.IsUnramifiedEverywhere K L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal] :
    v.asIdeal.ramificationIdx' w.asIdeal = 1 :=
  (adicAbv_isUnramified_iff w v).1 <|
    (NumberField.isUnramifiedEverywhere_iff K L).1 ‹_› _ (isNontrivial_adicAbv w)

/-- **An extension unramified everywhere is unramified at every prime**, stated for the prime
below `w` rather than for a given `v`. -/
theorem ramificationIdx'_under_eq_one_of_isUnramifiedEverywhere [IsGalois K L]
    [NumberField.IsUnramifiedEverywhere K L] :
    (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal = 1 :=
  ramificationIdx'_eq_one_of_isUnramifiedEverywhere w _

end NumberField
