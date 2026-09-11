/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.TameInjective
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-!
# A worked instance of `e ∣ q - 1`, with `e = 2 > 1`

`LocalCFT.orderOf_dvd_sub_one` says that in an abelian, tamely ramified situation the order of
an inertia element divides `q - 1`.  A divisibility bound is worth nothing if the hypotheses are
never satisfiable with `e > 1`, so this file exhibits an instance in which they are, and in
which the bound is *sharp enough to be falsified by the obvious mutations*.

Take `B = 𝔽₅⟦X⟧`, a discrete valuation ring with uniformizer `X` and residue field `𝔽₅`, and
`σ : X ↦ -X` (`LocalCFT.TameExample.negX`, the rescaling by `-1`).  Then

* `σ` acts trivially on the residue field, so it lies in the inertia group;
* `σ² = 1` and `σ ≠ 1`, so `orderOf σ = e = 2`, and `2` is invertible in `B`: tame;
* `θ(σ) = -1`, which is `≠ 1`: the tame character is faithful here, as the theory says;
* `q = 5` works as the Frobenius exponent with `τ = 1`, because `x ↦ x⁵` is the identity on
  `𝔽₅`; `τ` commutes with `σ` trivially, which is the abelianness hypothesis.

The theorem then gives `2 ∣ 5 - 1 = 4`, which is true, and this instance **refutes** the two
natural mutations of the statement: `2 ∤ 5` and `2 ∤ 5 - 2 = 3`.  So the exponent `q - 1` in
`LocalCFT.orderOf_dvd_sub_one` is not an artefact of a vacuous hypothesis set, and cannot be
weakened to `q` or strengthened to `q - 2`.

This is the equal-characteristic shadow of the arithmetic example in
`Iwasawalib/NumberTheory/ZpExtension/RamifiedFamily.lean`'s module docstring: `ℚ(√5)/ℚ` is
tamely ramified at `5` with `e = 2` and `N(5) - 1 = 4`.

## Main statements

* `LocalCFT.TameExample.control_dvd`: `orderOf negX ∣ 5 - 1`, by
  `LocalCFT.orderOf_dvd_sub_one`.
* `LocalCFT.TameExample.orderOf_negX`: `orderOf negX = 2`, so the instance is non-degenerate.
* `LocalCFT.TameExample.control_nontrivial`: `1 < orderOf negX`.
* `LocalCFT.TameExample.control_mutation_q` and
  `LocalCFT.TameExample.control_mutation_q_sub_two`: the mutations `q` and `q - 2` are refuted.
* `LocalCFT.TameExample.tameChar_negX`: `θ(σ) = -1`.
-/

noncomputable section

open IsLocalRing LocalCFT PowerSeries

namespace LocalCFT.TameExample

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The discrete valuation ring `𝔽₅⟦X⟧`. -/
abbrev BB := PowerSeries (ZMod 5)


example : IsDiscreteValuationRing BB := by infer_instance

theorem irr_X : Irreducible (X : BB) := PowerSeries.X_irreducible

def negX : RingAut BB :=
  RingEquiv.ofRingHom (PowerSeries.rescale (-1 : ZMod 5)) (PowerSeries.rescale (-1 : ZMod 5))
    (by rw [← PowerSeries.rescale_mul]; norm_num [PowerSeries.rescale_one])
    (by rw [← PowerSeries.rescale_mul]; norm_num [PowerSeries.rescale_one])

@[simp] theorem negX_apply (f : BB) : negX f = PowerSeries.rescale (-1 : ZMod 5) f := rfl

theorem negX_X : negX (X : BB) = -X := by
  rw [negX_apply]; exact PowerSeries.rescale_neg_one_X

theorem negX_sq : negX * negX = 1 := by
  refine RingEquiv.ext fun f => ?_
  show negX (negX f) = f
  simp only [negX_apply, PowerSeries.rescale_rescale]
  norm_num [PowerSeries.rescale_one]

theorem maximalIdeal_BB : maximalIdeal BB = Ideal.span {(X : BB)} := irr_X.maximalIdeal_eq

theorem mem_maximalIdeal_iff (f : BB) :
    f ∈ maximalIdeal BB ↔ PowerSeries.constantCoeff f = 0 := by
  rw [maximalIdeal_BB, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

theorem residue_eq_of_sub_mem {f g : BB} (h : f - g ∈ maximalIdeal BB) :
    residue BB f = residue BB g := by
  rw [← sub_eq_zero, ← map_sub]
  exact (Ideal.Quotient.eq_zero_iff_mem).2 h

theorem negX_mem_inertia : negX ∈ inertiaAut BB := by
  intro f
  refine residue_eq_of_sub_mem ?_
  rw [mem_maximalIdeal_iff, map_sub, sub_eq_zero, negX_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_rescale, pow_zero, one_mul]

theorem tameUnit_negX : tameUnit irr_X negX = -1 :=
  (tameUnit_unique irr_X negX (by rw [negX_X]; simp)).symm

theorem tameChar_negX : tameChar irr_X negX = -1 := by
  rw [show tameChar irr_X negX = residue BB ((tameUnit irr_X negX : BBˣ) : BB) from rfl,
    tameUnit_negX]
  simp

theorem negX_ne_one : negX ≠ 1 := by
  intro h
  have hX : negX (X : BB) = X := by rw [h]; rfl
  rw [negX_X] at hX
  have h2 := congrArg (PowerSeries.coeff (R := ZMod 5) 1) hX
  simp only [map_neg, PowerSeries.coeff_one_X] at h2
  exact absurd h2 (by decide)

theorem orderOf_negX : orderOf negX = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact negX_sq) negX_ne_one

theorem residue_pow_five (f : BB) : residue BB f ^ 5 = residue BB f := by
  have hC : residue BB f = residue BB (PowerSeries.C (PowerSeries.constantCoeff f)) := by
    refine residue_eq_of_sub_mem ?_
    rw [mem_maximalIdeal_iff, map_sub, PowerSeries.constantCoeff_C, sub_self]
  rw [hC, ← map_pow, ← map_pow, ZMod.pow_card]

theorem two_isUnit : IsUnit ((2 : ℕ) : BB) := by
  refine isUnit_iff_exists_inv.2 ⟨((3 : ℕ) : BB), ?_⟩
  rw [← Nat.cast_mul]
  have : ((6 : ℕ) : BB) = PowerSeries.C ((6 : ℕ) : ZMod 5) := (map_natCast _ 6).symm
  rw [show (2 * 3 : ℕ) = 6 from rfl, this, show ((6 : ℕ) : ZMod 5) = 1 from by decide, map_one]

/-- **The anti-vacuity control.** -/
theorem control_dvd : orderOf negX ∣ 5 - 1 :=
  orderOf_dvd_sub_one irr_X negX_mem_inertia (n := 2) (by rw [pow_two]; exact negX_sq)
    two_isUnit (τ := 1) (by norm_num) (fun b => (residue_pow_five b).symm) (by rw [one_mul, mul_one])

theorem control_nontrivial : 1 < orderOf negX := by rw [orderOf_negX]; norm_num

theorem control_mutation_q : ¬ (orderOf negX ∣ 5) := by rw [orderOf_negX]; decide

theorem control_mutation_q_sub_two : ¬ (orderOf negX ∣ 5 - 2) := by rw [orderOf_negX]; decide

end LocalCFT.TameExample
