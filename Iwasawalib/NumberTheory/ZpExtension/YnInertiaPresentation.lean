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

open PowerSeries

namespace MvZpExtension

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]
variable (H : MvZpExtension p ι K Kinf)

/-- In the Iwasawa action, `1 + X` acts on `X∞` by conjugation by `γ`. -/
theorem oneAddX_smul_ofMul (γ : H.GG ⧸ H.Xinf) (a : H.Xinf) :
    letI := H.XinfLambdaModule γ
    ((1 + X : ℤ_[p]⟦X⟧) • Additive.ofMul a) =
      Additive.ofMul (Subgroup.conjAct H.Xinf H.mul_comm_Xinf' γ a) := by
  letI := H.XinfLambdaModule γ
  rw [add_smul, one_smul, H.XinfLambdaModule_X_smul]
  change Additive.ofMul (a * (Subgroup.conjAct H.Xinf H.mul_comm_Xinf' γ a / a)) = _
  congr 1
  apply Subtype.ext
  change (a : H.GG) *
    ((Subgroup.conjAct H.Xinf H.mul_comm_Xinf' γ a : H.Xinf) : H.GG) /
      (a : H.GG) = _
  rw [H.mul_comm_Xinf _ a.property _
    (Subgroup.conjAct H.Xinf H.mul_comm_Xinf' γ a).property]
  simp

/-- The `l`-th power of `1 + X` acts by conjugation by `γ ^ l`. -/
theorem oneAddX_pow_smul_ofMul (γ : H.GG ⧸ H.Xinf) (a : H.Xinf) (l : ℕ) :
    letI := H.XinfLambdaModule γ
    ((1 + X : ℤ_[p]⟦X⟧) ^ l • Additive.ofMul a) =
      Additive.ofMul (Subgroup.conjAct H.Xinf H.mul_comm_Xinf' (γ ^ l) a) := by
  letI := H.XinfLambdaModule γ
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pow_succ', mul_smul, ih]
    rw [add_smul, one_smul, H.XinfLambdaModule_X_smul]
    rw [show γ ^ (l + 1) = γ * γ ^ l by rw [pow_succ']]
    rw [Subgroup.conjAct_mul]
    change Additive.ofMul
      (Subgroup.conjAct H.Xinf H.mul_comm_Xinf' (γ ^ l) a *
      (Subgroup.conjAct H.Xinf H.mul_comm_Xinf' γ
        (Subgroup.conjAct H.Xinf H.mul_comm_Xinf' (γ ^ l) a) : H.Xinf) /
          Subgroup.conjAct H.Xinf H.mul_comm_Xinf' (γ ^ l) a) = _
    congr 1
    apply Subtype.ext
    change ((Subgroup.conjAct H.Xinf H.mul_comm_Xinf' (γ ^ l) a : H.Xinf) : H.GG) *
      ((Subgroup.conjAct H.Xinf H.mul_comm_Xinf' γ
        (Subgroup.conjAct H.Xinf H.mul_comm_Xinf' (γ ^ l) a) : H.Xinf) : H.GG) /
      ((Subgroup.conjAct H.Xinf H.mul_comm_Xinf' (γ ^ l) a : H.Xinf) : H.GG) = _
    rw [H.mul_comm_Xinf _
      (Subgroup.conjAct H.Xinf H.mul_comm_Xinf' (γ ^ l) a).property _
      (Subgroup.conjAct H.Xinf H.mul_comm_Xinf' γ
        (Subgroup.conjAct H.Xinf H.mul_comm_Xinf' (γ ^ l) a)).property]
    simp

/-- **The source's `a_i^(n) = ν_(n,e) a_i` calculation.**  The acting generator after
shifting the base to `K_e` is `γ ^ (p ^ e)`, and the product has `p ^ (n - e)` factors. -/
theorem nu_smul_ofMul_eq_prod_conjAct (γ : H.GG ⧸ H.Xinf) (a : H.Xinf) (n e : ℕ) :
    letI := H.XinfLambdaModule γ
    ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Additive.ofMul a =
      Additive.ofMul (((List.range (p ^ (n - e))).map (fun i ↦
        Subgroup.conjAct H.Xinf H.mul_comm_Xinf' ((γ ^ (p ^ e)) ^ i) a)).prod) := by
  letI := H.XinfLambdaModule γ
  rw [Polynomial.nu]
  have hcoe :
      (↑((∑ i ∈ Finset.range (p ^ (n - e)),
          (1 + Polynomial.X) ^ (p ^ e * i)) : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) =
        ∑ i ∈ Finset.range (p ^ (n - e)),
          (↑((1 + Polynomial.X) ^ (p ^ e * i) : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) := by
    generalize Finset.range (p ^ (n - e)) = s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, ih]
  rw [hcoe, Finset.sum_smul]
  induction p ^ (n - e) with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_singleton, List.prod_singleton]
    rw [ih]
    rw [show (((1 + Polynomial.X) ^ (p ^ e * k) : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧)
      = (1 + X) ^ (p ^ e * k) by simp]
    rw [H.oneAddX_pow_smul_ofMul γ, pow_mul]
    change Additive.ofMul (_ * _) = _
    rfl

/-- The inertia-lift power formula with its conjugate product replaced by the exact
`ν_(n,e)` scalar.  This is the algebraic calculation used after shifting the base to `K_e`. -/
theorem pow_eq_nu_smul_mul_pow_of_eq_mul (γ : H.GG ⧸ H.Xinf) (a : H.Xinf)
    (sigma sigma_i : H.GG) (n e : ℕ)
    (hgamma : QuotientGroup.mk sigma = γ ^ (p ^ e))
    (hsigma : sigma_i = (a : H.GG) * sigma) :
    letI := H.XinfLambdaModule γ
    sigma_i ^ (p ^ (n - e)) =
      ((Additive.toMul
        (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) •
          Additive.ofMul a) : H.Xinf) : H.GG) * sigma ^ (p ^ (n - e)) := by
  letI := H.XinfLambdaModule γ
  rw [Subgroup.pow_eq_prod_conjAct_mul_pow_of_eq_mul H.Xinf H.mul_comm_Xinf' a sigma
    sigma_i hsigma]
  congr 1
  apply congrArg Subtype.val
  apply Additive.ofMul.injective
  rw [H.nu_smul_ofMul_eq_prod_conjAct γ a n e]
  simp only [hgamma]
  rfl

end MvZpExtension
