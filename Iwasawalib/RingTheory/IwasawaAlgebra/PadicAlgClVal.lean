/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.DistinguishedRoots
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The additive valuation of `ℚ̄_p`

`PadicAlgCl p` carries the unique absolute value extending the `p`-adic one on `ℚ_p`. This
file records the associated *additive* valuation `v(x) = -log_p ‖x‖`, normalized so that
`v(p) = 1`, which is the normalization used throughout Washington's Chapter 13 and in the
blueprint (nodes `omega-val-growth`, `quotient-by-distinguished` (iii), `growth-general`).

By convention `v(0) = 0`; all statements below therefore carry a nonvanishing hypothesis.

## Main results

* `PadicAlgCl.val`: the valuation `v`.
* `PadicAlgCl.norm_eq_rpow_neg_val`: `‖x‖ = p ^ (-v(x))` for `x ≠ 0`.
* `PadicAlgCl.val_mul`, `PadicAlgCl.val_multiset_prod`: additivity.
* `PadicAlgCl.val_toPadicAlgCl`: `v` restricts to `PadicInt.valuation` on `ℤ_p`.
-/

namespace PadicAlgCl

variable (p : ℕ) [hp : Fact p.Prime]

/-- The additive valuation `v(x) = -log_p ‖x‖` of `ℚ̄_p`, normalized by `v(p) = 1`.
By convention `v(0) = 0`. -/
noncomputable def val (x : PadicAlgCl p) : ℝ := -Real.logb p ‖x‖

variable {p}

theorem one_lt_cast_p : (1 : ℝ) < (p : ℝ) := by
  exact_mod_cast hp.out.one_lt

theorem val_eq_neg_logb (x : PadicAlgCl p) : val p x = -Real.logb p ‖x‖ := rfl

@[simp]
theorem val_zero : val p 0 = 0 := by simp [val]

@[simp]
theorem val_one : val p (1 : PadicAlgCl p) = 0 := by simp [val]

theorem norm_eq_rpow_neg_val {x : PadicAlgCl p} (hx : x ≠ 0) :
    ‖x‖ = (p : ℝ) ^ (-(val p x)) := by
  rw [val, neg_neg]
  exact (Real.rpow_logb (by linarith [one_lt_cast_p (p := p)]) (one_lt_cast_p (p := p)).ne'
    (norm_pos_iff.2 hx)).symm

theorem val_mul {x y : PadicAlgCl p} (hx : x ≠ 0) (hy : y ≠ 0) :
    val p (x * y) = val p x + val p y := by
  rw [val, val, val, norm_mul, Real.logb_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy)]
  ring

theorem val_multiset_prod (s : Multiset (PadicAlgCl p)) (hs : ∀ x ∈ s, x ≠ 0) :
    val p s.prod = (s.map (val p)).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ x ∈ s, x ≠ 0 := fun x hx ↦ hs x (Multiset.mem_cons_of_mem hx)
    have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h ↦ (hs' 0 h) rfl)
    rw [Multiset.prod_cons, val_mul ha hprod, ih hs', Multiset.map_cons, Multiset.sum_cons]

/-- On `ℤ_p` the valuation `v` is the usual `p`-adic valuation. -/
theorem val_toPadicAlgCl {a : ℤ_[p]} (ha : a ≠ 0) :
    val p (PadicInt.toPadicAlgCl p a) = a.valuation := by
  have h1 : (1 : ℝ) < (p : ℝ) := one_lt_cast_p (p := p)
  rw [val, PadicInt.norm_toPadicAlgCl, PadicInt.norm_eq_zpow_neg_valuation ha,
    ← Real.rpow_intCast, Real.logb_rpow (by linarith) h1.ne']
  push_cast
  ring

end PadicAlgCl
