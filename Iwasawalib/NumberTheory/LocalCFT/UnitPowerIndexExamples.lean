/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.UnitPowerIndex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# `ℚ_3` and `ℚ_2`: the power isomorphism at a concrete field

`Iwasawalib/NumberTheory/LocalCFT/UnitFiltrationPow.lean` proves an isomorphism
`U^(k) ≃ U^(k+e)` under hypotheses packaged as `LocalCFT.IsPowData`.  A package of hypotheses
that nothing satisfies would prove nothing, and an isomorphism `U^(k) ≃ U^(k)` — no shift —
would be the trivial identity.  This file rules both out at an honest example, the completion
of `ℚ` at the `3`-adic valuation, where `p = 3`, `e = 1` and the classical answer is known.

* `LocalCFT.Example3.valued_three`: `v 3 = exp (-1)`, so `e = 1`.
* `LocalCFT.Example3.cubeEquiv`: **`1 + 3ℤ_3 ≅ 1 + 9ℤ_3` by cubing**, an instance of
  `LocalCFT.unitFiltrationPowEquiv` at a genuine field.  The classical statement is that
  `x ↦ x^3` is a bijection `U^{(1)} → U^{(2)}` of `ℚ_3`.
* `LocalCFT.Example3.four_mem_one`, `LocalCFT.Example3.four_notMem_two`: `4 ∈ U^(1)` and
  `4 ∉ U^(2)`, so `U^(2)` is a *proper* subgroup of `U^(1)` and the shift by `e = 1` in
  `cubeEquiv` is real: cubing is **not** onto `U^(1)`.

At `p = 2` the side condition `e < m (p-1)` reads `1 < m`, so the isomorphism starts at level
`2` (`LocalCFT.Example2.squareEquiv`: `1 + 4ℤ_2 ≅ 1 + 8ℤ_2`) and is *not* claimed at level `1`.
That is correct and not an artefact: squaring is not onto `1 + 4ℤ_2`, since the square of
`1 + 2t` is `1 + 4t(1+t) ∈ 1 + 8ℤ_2`.
-/

noncomputable section

open WithZero Valuation

namespace LocalCFT

/-! ## `p = 3` -/

namespace Example3

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The completion of `ℚ` at the `3`-adic valuation. -/
abbrev Q3 : Type := (Rat.padicValuation 3).Completion

/-- **`v 3 = exp (-1)`**: the absolute ramification index of `ℚ_3` is `e = 1`. -/
theorem valued_three : (Valued.v (((3 : ℕ) : Q3)) : ℤᵐ⁰) = exp (-((1 : ℕ) : ℤ)) := by
  have h : (((3 : ℕ) : Q3))
      = ((UniformSpace.Completion.coeRingHom (α := WithVal (Rat.padicValuation 3)))
          (((3 : ℕ) : WithVal (Rat.padicValuation 3)))) := (map_natCast _ 3).symm
  rw [h]
  show (Valued.v ((((3 : ℕ) : WithVal (Rat.padicValuation 3)) : Q3)) : ℤᵐ⁰)
    = exp (-((1 : ℕ) : ℤ))
  rw [Valued.valuedCompletion_apply]
  show Rat.padicValuation 3 ((3 : ℕ) : ℚ) = exp (-((1 : ℕ) : ℤ))
  rw [show (-((1 : ℕ) : ℤ)) = (-1 : ℤ) by norm_num]
  exact_mod_cast Rat.padicValuation_self 3

/-- **`1 + 3ℤ_3 ≅ 1 + 9ℤ_3`, by cubing.**  This is `LocalCFT.unitFiltrationPowEquiv` at a
concrete complete discretely valued field of mixed characteristic `(0, 3)`. -/
def cubeEquiv : unitFiltration (F := Q3) 1 ≃* unitFiltration (F := Q3) 2 :=
  unitFiltrationPowEquiv (F := Q3) (p := 3) (m := 1) (e := 1)
    (by norm_num) le_rfl valued_three (by norm_num) le_rfl

@[simp] theorem coe_cubeEquiv (u : unitFiltration (F := Q3) 1) :
    ((cubeEquiv u : unitFiltration (F := Q3) 2) : (integers (F := Q3))ˣ)
      = (u : (integers (F := Q3))ˣ) ^ 3 := rfl

/-! ### The shift is real: `U^(2) ⊊ U^(1)` -/

theorem valued_three_lt_one : (Valued.v (((3 : ℕ) : Q3)) : ℤᵐ⁰) < 1 := by
  rw [valued_three, show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm, exp_lt_exp]
  norm_num

/-- `4 = 1 + 3`, as a unit of `ℤ_3`. -/
def four : (integers (F := Q3))ˣ := oneAddUnit valued_three_lt_one

@[simp] theorem coe_four : ((four : integers (F := Q3)) : Q3) = 1 + ((3 : ℕ) : Q3) := rfl

/-- `4 ∈ U^(1)`. -/
theorem four_mem_one : four ∈ unitFiltration (F := Q3) 1 :=
  oneAddUnit_mem valued_three_lt_one (le_of_eq valued_three)

/-- **`4 ∉ U^(2)`.**  So `U^(2) ⊊ U^(1)` and `LocalCFT.Example3.cubeEquiv` is *not* an
isomorphism onto `U^(1)`: `4` is not a cube in `1 + 3ℤ_3`. -/
theorem four_notMem_two : four ∉ unitFiltration (F := Q3) 2 := by
  rw [mem_unitFiltration, coe_four, add_sub_cancel_left, valued_three]
  rw [exp_le_exp]
  norm_num

/-- **Cubing is not onto `U^(1)`.**  The anti-vacuity statement in its sharpest form. -/
theorem not_surjective_cube :
    ¬ (∀ x ∈ unitFiltration (F := Q3) 1,
        ∃ u ∈ unitFiltration (F := Q3) 1, u ^ 3 = x) := by
  intro h
  obtain ⟨u, hu, hux⟩ := h four four_mem_one
  refine four_notMem_two ?_
  rw [← hux]
  exact (isPowData_prime (F := Q3) (p := 3) (m := 1) (e := 1)
    (by norm_num) le_rfl valued_three (by norm_num)).pow_mem le_rfl hu

end Example3

/-! ## `p = 2`: the isomorphism starts one level higher -/

namespace Example2

instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-- The completion of `ℚ` at the `2`-adic valuation. -/
abbrev Q2 : Type := (Rat.padicValuation 2).Completion

/-- `v 2 = exp (-1)`: the absolute ramification index of `ℚ_2` is `e = 1`. -/
theorem valued_two : (Valued.v (((2 : ℕ) : Q2)) : ℤᵐ⁰) = exp (-((1 : ℕ) : ℤ)) := by
  have h : (((2 : ℕ) : Q2))
      = ((UniformSpace.Completion.coeRingHom (α := WithVal (Rat.padicValuation 2)))
          (((2 : ℕ) : WithVal (Rat.padicValuation 2)))) := (map_natCast _ 2).symm
  rw [h]
  show (Valued.v ((((2 : ℕ) : WithVal (Rat.padicValuation 2)) : Q2)) : ℤᵐ⁰)
    = exp (-((1 : ℕ) : ℤ))
  rw [Valued.valuedCompletion_apply]
  show Rat.padicValuation 2 ((2 : ℕ) : ℚ) = exp (-((1 : ℕ) : ℤ))
  rw [show (-((1 : ℕ) : ℤ)) = (-1 : ℤ) by norm_num]
  exact_mod_cast Rat.padicValuation_self 2

/-- **`1 + 4ℤ_2 ≅ 1 + 8ℤ_2`, by squaring.**  The side condition `e < m (p-1)` reads `1 < m` at
`p = 2`, so the isomorphism is available from level `m = 2` upwards — and *not* at level `1`,
where squaring is genuinely not onto `1 + 4ℤ_2`. -/
def squareEquiv : unitFiltration (F := Q2) 2 ≃* unitFiltration (F := Q2) 3 :=
  unitFiltrationPowEquiv (F := Q2) (p := 2) (m := 2) (e := 1)
    (by norm_num) (by norm_num) valued_two (by norm_num) le_rfl

/-- The side condition of `LocalCFT.unitFiltrationPowEquiv` **fails** at `p = 2`, `m = 1`,
`e = 1`.  It has to: squaring is not onto `1 + 4ℤ_2`. -/
theorem side_condition_fails_at_level_one : ¬ ((1 : ℕ) < 1 * (2 - 1)) := by norm_num

end Example2

end LocalCFT
