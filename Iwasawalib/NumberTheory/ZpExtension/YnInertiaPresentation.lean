/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.InertiaExponent
public import Iwasawalib.NumberTheory.ZpExtension.XinfYeGenerators

@[expose] public section

/-!
# The power calculation in the inertia-generator presentation

This file isolates the group-theoretic calculation in Step 2 of Washington's Lemma 13.15.
If two inertia lifts satisfy `sigma_i = a_i * sigma_1`, then

`sigma_i ^ k = (prod l < k, sigma_1 ^ l * a_i * sigma_1 ^ (-l)) * sigma_1 ^ k`.

The second theorem rewrites the conjugates as the quotient action of `G / X` on an abelian
normal subgroup `X`.  These statements contain no ramification or class-field-theory input;
they are the reusable algebraic core of the eventual `Y_n` presentation.
-/

open scoped Pointwise

/-- The noncommutative power identity used for the inertia lifts in Washington 13.15. -/
theorem mul_pow_eq_prod_conj_mul_pow {G : Type*} [Group G] (a sigma : G) (k : ℕ) :
    (a * sigma) ^ k =
      ((List.range k).map (fun l ↦ sigma ^ l * a * (sigma ^ l)⁻¹)).prod * sigma ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, List.range_succ, List.map_append, List.prod_append]
      simp only [List.map_singleton, List.prod_singleton]
      group

namespace Subgroup

variable {G : Type*} [Group G] (X : Subgroup G) [X.Normal]
  (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)

/-- The inertia-lift power identity, expressed using the canonical action of `G / X` on `X`.
This is the multiplicative form of the source's formula
`a_i^(n) = sum_(l < p^n) gamma^l . a_i`. -/
theorem mul_pow_eq_prod_conjAct_mul_pow (a : X) (sigma : G) (k : ℕ) :
    ((a : G) * sigma) ^ k =
      ((↑((List.range k).map (fun l ↦
          conjAct X hX ((QuotientGroup.mk sigma) ^ l) a)).prod : X) : G) * sigma ^ k := by
  rw [mul_pow_eq_prod_conj_mul_pow]
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_append, List.prod_append,
        List.prod_append]
      simp only [List.map_singleton, List.prod_singleton, Subgroup.coe_mul, ih]
      rw [show (QuotientGroup.mk sigma) ^ k = QuotientGroup.mk (sigma ^ k) by
        exact ((QuotientGroup.mk' X).map_pow sigma k).symm, coe_conjAct_mk]

/-- If `sigma_i = a_i * sigma_1`, its powers have the source-prescribed presentation. -/
theorem pow_eq_prod_conjAct_mul_pow_of_eq_mul (a : X) (sigma sigma_i : G)
    (hsigma : sigma_i = (a : G) * sigma) (k : ℕ) :
    sigma_i ^ k =
      ((↑((List.range k).map (fun l ↦
          conjAct X hX ((QuotientGroup.mk sigma) ^ l) a)).prod : X) : G) * sigma ^ k := by
  rw [hsigma]
  exact Subgroup.mul_pow_eq_prod_conjAct_mul_pow X hX a sigma k

end Subgroup
