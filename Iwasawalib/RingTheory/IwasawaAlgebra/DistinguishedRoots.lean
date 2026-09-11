/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished

@[expose] public section

/-!
# Roots of distinguished polynomials

This file proves blueprint node `omega-val-growth` (i): if `F ∈ ℤ_p[X]` is a distinguished
polynomial of degree at least one and `α` is a root of `F` in a fixed algebraic closure
`ℚ̄_p = PadicAlgCl p` of `ℚ_p`, then `v(α) > 0`, i.e. `‖α‖ < 1`.

## Main results

* `PadicInt.toPadicAlgCl`: the ring homomorphism `ℤ_p → ℚ̄_p`.
* `Polynomial.IsDistinguishedAt.norm_lt_one_of_isRoot`: the roots of a distinguished polynomial
  of positive degree have absolute value `< 1`.
* `Polynomial.IsDistinguishedAt.exists_isRoot`: such a polynomial does have a root.
-/

open Polynomial

variable (p : ℕ) [Fact p.Prime]

namespace PadicInt

/-- The ring homomorphism from `ℤ_p` into a fixed algebraic closure of `ℚ_p`. -/
noncomputable def toPadicAlgCl : ℤ_[p] →+* PadicAlgCl p :=
  (algebraMap ℚ_[p] (PadicAlgCl p)).comp PadicInt.Coe.ringHom

@[simp]
theorem norm_toPadicAlgCl (a : ℤ_[p]) : ‖toPadicAlgCl p a‖ = ‖a‖ := by
  rw [toPadicAlgCl, RingHom.comp_apply,
    show (algebraMap ℚ_[p] (PadicAlgCl p)) (PadicInt.Coe.ringHom a) =
      ((PadicInt.Coe.ringHom a : ℚ_[p]) : PadicAlgCl p) from rfl,
    PadicAlgCl.norm_extends]
  rfl

end PadicInt

namespace Polynomial.IsDistinguishedAt

variable {p}
variable {F : Polynomial ℤ_[p]} (hF : F.IsDistinguishedAt (Ideal.span {(p : ℤ_[p])}))

include hF

/-- The non-leading coefficients of a distinguished polynomial have norm at most `1 / p`. -/
theorem norm_coeff_le {i : ℕ} (hi : i < F.natDegree) : ‖F.coeff i‖ ≤ (p : ℝ)⁻¹ := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hF.mem hi)
  rw [← hb, norm_mul, PadicInt.norm_p]
  calc ‖b‖ * (p : ℝ)⁻¹ ≤ 1 * (p : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right b.norm_le_one (by positivity)
    _ = (p : ℝ)⁻¹ := one_mul _

/-- **Blueprint node `omega-val-growth` (i)**: every root of a distinguished polynomial of
positive degree, in a fixed algebraic closure of `ℚ_p`, has absolute value `< 1`, i.e. has
positive valuation. -/
theorem norm_lt_one_of_isRoot {α : PadicAlgCl p}
    (hα : (F.map (PadicInt.toPadicAlgCl p)).IsRoot α) : ‖α‖ < 1 := by
  by_contra hcon
  rw [not_lt] at hcon
  set d := F.natDegree with hddef
  set φ := PadicInt.toPadicAlgCl p with hφ
  have hdegmap : (F.map φ).natDegree = d := hF.monic.natDegree_map _
  have heval : ∑ i ∈ Finset.range (d + 1), (F.map φ).coeff i * α ^ i = 0 := by
    rw [← Polynomial.eval_eq_sum_range' (by omega) α]
    exact hα
  rw [Finset.sum_range_succ, Polynomial.coeff_map, hF.monic.coeff_natDegree, map_one,
    one_mul] at heval
  have hkey : α ^ d = -∑ i ∈ Finset.range d, (F.map φ).coeff i * α ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact heval
  have hα0 : (0 : ℝ) < ‖α‖ := zero_lt_one.trans_le hcon
  have hpow : (1 : ℝ) ≤ ‖α‖ ^ d := one_le_pow₀ hcon
  have hbound : ‖α ^ d‖ ≤ (p : ℝ)⁻¹ * ‖α‖ ^ d := by
    rw [hkey, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow, Polynomial.coeff_map, PadicInt.norm_toPadicAlgCl]
    exact mul_le_mul (hF.norm_coeff_le hi) (pow_le_pow_right₀ hcon (by omega))
      (by positivity) (by positivity)
  rw [norm_pow] at hbound
  have hple : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
    rw [inv_le_inv₀ hppos (by norm_num)]
    exact hple
  have hmul := mul_le_mul_of_nonneg_right hinv (by linarith : (0 : ℝ) ≤ ‖α‖ ^ d)
  linarith

/-- A distinguished polynomial of positive degree has a root in `ℚ̄_p`. -/
theorem exists_isRoot (hd : 0 < F.natDegree) :
    ∃ α : PadicAlgCl p, (F.map (PadicInt.toPadicAlgCl p)).IsRoot α := by
  refine IsAlgClosed.exists_root _ ?_
  rw [Polynomial.degree_eq_natDegree (hF.monic.map (PadicInt.toPadicAlgCl p)).ne_zero,
    hF.monic.natDegree_map]
  exact_mod_cast hd.ne'

end Polynomial.IsDistinguishedAt
