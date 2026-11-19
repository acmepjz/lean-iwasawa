/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.GrowthGeneral
public import Iwasawalib.RingTheory.IwasawaAlgebra.OmegaValGrowth
public import Iwasawalib.RingTheory.IwasawaAlgebra.RankBounded

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# Blueprint nodes `coinvariant-growth` and `coinvariant-growth-2`
-/

open Function Module PowerSeries

namespace IwasawaAlgebra

variable {p : ℕ} [hp : Fact p.Prime]

theorem logb_inv_pow (k : ℕ) : Real.logb p (((p : ℝ)⁻¹) ^ k) = -(k : ℝ) := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hlog : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos h1)
  simp only [Real.logb, Real.log_pow, Real.log_inv]
  field_simp

/-- `v(p ^ k) = k` in `ℚ̄_p`. -/
theorem val_natCast_p_pow (k : ℕ) :
    PadicAlgCl.val p (((p ^ k : ℕ) : PadicAlgCl p)) = (k : ℝ) := by
  have hnorm : ‖((p ^ k : ℕ) : PadicAlgCl p)‖ = ((p : ℝ)⁻¹) ^ k := by
    push_cast
    rw [norm_pow, PadicAlgCl.norm_p_eq]
  rw [PadicAlgCl.val, hnorm, logb_inv_pow, neg_neg]

/-- The value of `ω_k` at `α`, after base change to `ℚ̄_p`. -/
theorem eval_map_omega (α : PadicAlgCl p) (k : ℕ) :
    Polynomial.eval α ((Polynomial.oneAddXPowSubOne ℤ_[p] k).map (PadicInt.toPadicAlgCl p))
      = (1 + α) ^ k - 1 := by
  rw [Polynomial.oneAddXPowSubOne_def]
  simp

/-- **Hypothesis (c) of `growth-general` for the sequence `ω_n`**: this is blueprint node
`omega-val-growth` (ii), translated from norms to the valuation `v`. -/
theorem exists_val_omega_eq {α : PadicAlgCl p} (hα : ‖α‖ < 1) (n₀ : ℕ)
    (hne : ∀ n, n₀ ≤ n → Polynomial.eval α
      ((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n)).map (PadicInt.toPadicAlgCl p)) ≠ 0) :
    ∃ (c : ℝ) (N : ℕ), ∀ n, N ≤ n →
      PadicAlgCl.val p (Polynomial.eval α
        ((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n)).map (PadicInt.toPadicAlgCl p))) = n + c := by
  have hne' : ∀ n : ℕ, (1 + α) ^ (p ^ n) ≠ 1 := by
    intro n h
    refine hne (max n₀ n) (le_max_left _ _) ?_
    rw [eval_map_omega, show p ^ (max n₀ n) = p ^ n * p ^ (max n₀ n - n) by
      rw [← pow_add]; congr 1; omega, pow_mul, h, one_pow, sub_self]
  obtain ⟨N, c, hc, hN⟩ := PadicAlgCl.exists_norm_delta_eq hα hne'
  refine ⟨-Real.logb p c, N, fun n hn ↦ ?_⟩
  rw [eval_map_omega, PadicAlgCl.val, hN n hn,
    Real.logb_mul (ne_of_gt hc)
      (pow_ne_zero n (inv_ne_zero (Nat.cast_ne_zero.2 hp.out.pos.ne'))), logb_inv_pow]
  ring

/-- `coinvariant-growth` for a module already known to be `Λ`-torsion. Unlike
`IwasawaAlgebra.exists_factorization_card_quotSMulTop_omega` this needs no `ℤ_p`-module
structure on `M`. -/
theorem exists_factorization_card_quotSMulTop_omega_of_isTorsion
    {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]
    (hM : Module.IsTorsion ℤ_[p]⟦X⟧ M) (n₀ : ℕ)
    (hfin : ∀ n, n₀ ≤ n → Finite (QuotSMulTop
      ((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) M)) :
    ∃ (ν : ℤ) (N : ℕ), ∀ n, N ≤ n →
      ((Nat.card (QuotSMulTop
        ((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) :
          ℤ_[p]⟦X⟧) M)).factorization p : ℤ) =
        (muMod p M : ℤ) * (p : ℤ) ^ n + (lambdaMod p M : ℤ) * n + ν :=
  exists_factorization_card_quotSMulTop_eq hM
    (fun n ↦ Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n)) n₀ 0
    (fun n _ ↦ isDistinguishedAt_omega n)
    (fun n _ ↦ Polynomial.oneAddXPowSubOne_dvd_of_dvd ℤ_[p] (p ^ n) (p ^ (n + 1))
      (pow_dvd_pow p (Nat.le_succ n)))
    (fun n _ ↦ by rw [Polynomial.natDegree_oneAddXPowSubOne]; push_cast; ring)
    (fun α hα hne ↦ exists_val_omega_eq hα n₀ hne) hfin

/-- **Blueprint node `coinvariant-growth`**: if `X ⧸ ω_n X` is finite for all sufficiently
large `n`, then `X` is a torsion `Λ`-module and
`ord_p #(X ⧸ ω_n X) = μ(X) p ^ n + λ(X) n + ν` for all sufficiently large `n`. -/
theorem exists_factorization_card_quotSMulTop_omega
    {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module ℤ_[p]⟦X⟧ M]
    [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M] (n₀ : ℕ)
    (hfin : ∀ n, n₀ ≤ n → Finite (QuotSMulTop
      ((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) M)) :
    Module.IsTorsion ℤ_[p]⟦X⟧ M ∧
      ∃ (ν : ℤ) (N : ℕ), ∀ n, N ≤ n →
        ((Nat.card (QuotSMulTop
          ((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) :
            ℤ_[p]⟦X⟧) M)).factorization p : ℤ) =
          (muMod p M : ℤ) * (p : ℤ) ^ n + (lambdaMod p M : ℤ) * n + ν := by
  have htor := isTorsion_of_finite_quotSMulTop_omega M n₀ hfin
  exact ⟨htor, exists_factorization_card_quotSMulTop_omega_of_isTorsion htor n₀ hfin⟩


section Nu

/-- The value of `ν_{n,e}` at `α`, after base change to `ℚ̄_p`. -/
theorem eval_map_nu (α : PadicAlgCl p) (n e : ℕ) :
    Polynomial.eval α ((Polynomial.nu ℤ_[p] p n e).map (PadicInt.toPadicAlgCl p))
      = ∑ i ∈ Finset.range (p ^ (n - e)), ((1 + α) ^ (p ^ e)) ^ i := by
  rw [Polynomial.nu, Polynomial.map_sum, Polynomial.eval_finsetSum]
  simp [pow_mul]

theorem omega_eq_omega_mul_nu (α : PadicAlgCl p) {n e : ℕ} (h : e ≤ n) :
    (1 + α) ^ (p ^ n) - 1 = ((1 + α) ^ (p ^ e) - 1) *
      Polynomial.eval α ((Polynomial.nu ℤ_[p] p n e).map (PadicInt.toPadicAlgCl p)) := by
  have hq := congrArg
    (fun q : Polynomial ℤ_[p] ↦ Polynomial.eval α (q.map (PadicInt.toPadicAlgCl p)))
    (Polynomial.nu_mul_oneAddXPowSubOne ℤ_[p] p h)
  simp only [Polynomial.map_mul, Polynomial.eval_mul] at hq
  rw [eval_map_omega, eval_map_omega] at hq
  rw [← hq]

theorem isDistinguishedAt_nu' {n e : ℕ} (h : e ≤ n) :
    (Polynomial.nu ℤ_[p] p n e).IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p]) := by
  haveI : (Ideal.span {(p : ℤ_[p])}).IsPrime := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact Polynomial.isDistinguishedAt_nu ℤ_[p] p h

/-- **Hypothesis (c) of `growth-general` for the sequence `ν_{n,e}`**: the two-case analysis of
`v(ν_{n,e}(α))` of blueprint node `coinvariant-growth-2`. -/
theorem exists_val_nu_eq (e : ℕ) {α : PadicAlgCl p} (hα : ‖α‖ < 1) (n₀ : ℕ) (he : e ≤ n₀)
    (hne : ∀ n, n₀ ≤ n → Polynomial.eval α
      ((Polynomial.nu ℤ_[p] p n e).map (PadicInt.toPadicAlgCl p)) ≠ 0) :
    ∃ (c : ℝ) (N : ℕ), ∀ n, N ≤ n →
      PadicAlgCl.val p (Polynomial.eval α
        ((Polynomial.nu ℤ_[p] p n e).map (PadicInt.toPadicAlgCl p))) = n + c := by
  by_cases hω : (1 + α) ^ (p ^ e) = 1
  · refine ⟨-(e : ℝ), n₀, fun n hn ↦ ?_⟩
    have hev : Polynomial.eval α ((Polynomial.nu ℤ_[p] p n e).map (PadicInt.toPadicAlgCl p))
        = ((p ^ (n - e) : ℕ) : PadicAlgCl p) := by
      rw [eval_map_nu, hω]
      simp
    rw [hev, val_natCast_p_pow, Nat.cast_sub (he.trans hn)]
    ring
  · have hωe : (1 + α) ^ (p ^ e) - 1 ≠ 0 := sub_ne_zero.2 hω
    have hne2 : ∀ n : ℕ, (1 + α) ^ (p ^ n) ≠ 1 := by
      intro n h
      have hm : (1 + α) ^ (p ^ (max n₀ n)) = 1 := by
        rw [show p ^ (max n₀ n) = p ^ n * p ^ (max n₀ n - n) by
          rw [← pow_add]; congr 1; omega, pow_mul, h, one_pow]
      have hkey := omega_eq_omega_mul_nu α (n := max n₀ n) (e := e) (he.trans (le_max_left _ _))
      rw [hm, sub_self] at hkey
      exact mul_ne_zero hωe (hne (max n₀ n) (le_max_left _ _)) hkey.symm
    obtain ⟨N, c, hc, hN⟩ := PadicAlgCl.exists_norm_delta_eq hα hne2
    refine ⟨-Real.logb p c - PadicAlgCl.val p ((1 + α) ^ (p ^ e) - 1), max n₀ N, fun n hn ↦ ?_⟩
    have hn0 : n₀ ≤ n := le_of_max_le_left hn
    have hvω : PadicAlgCl.val p ((1 + α) ^ (p ^ n) - 1) = n + -Real.logb p c := by
      rw [PadicAlgCl.val, hN n (le_of_max_le_right hn), Real.logb_mul (ne_of_gt hc)
        (pow_ne_zero n (inv_ne_zero (Nat.cast_ne_zero.2 hp.out.pos.ne'))), logb_inv_pow]
      ring
    rw [omega_eq_omega_mul_nu α (he.trans hn0), PadicAlgCl.val_mul hωe (hne n hn0)] at hvω
    linarith

/-- `coinvariant-growth-2` for a module already known to be `Λ`-torsion. Unlike
`IwasawaAlgebra.exists_factorization_card_quotSMulTop_nu` this needs no `ℤ_p`-module
structure on `M`. -/
theorem exists_factorization_card_quotSMulTop_nu_of_isTorsion
    {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]
    (hM : Module.IsTorsion ℤ_[p]⟦X⟧ M) (e n₀ : ℕ) (he : e ≤ n₀)
    (hfin : ∀ n, n₀ ≤ n → Finite (QuotSMulTop
      ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) M)) :
    ∃ (ν : ℤ) (N : ℕ), ∀ n, N ≤ n →
      ((Nat.card (QuotSMulTop
        ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) :
          ℤ_[p]⟦X⟧) M)).factorization p : ℤ) =
        (muMod p M : ℤ) * (p : ℤ) ^ n + (lambdaMod p M : ℤ) * n + ν := by
  have hple : ∀ n, e ≤ n → p ^ e ≤ p ^ n := fun n hn ↦ Nat.pow_le_pow_right hp.out.pos hn
  refine exists_factorization_card_quotSMulTop_eq hM
    (fun n ↦ Polynomial.nu ℤ_[p] p n e) n₀ (-(p : ℤ) ^ e)
    (fun n hn ↦ isDistinguishedAt_nu' (he.trans hn))
    (fun n hn ↦ Polynomial.nu_dvd_nu ℤ_[p] p (he.trans hn) (Nat.le_succ n))
    (fun n hn ↦ ?_) (fun α hα hne ↦ exists_val_nu_eq e hα n₀ he hne) hfin
  rw [Polynomial.natDegree_nu ℤ_[p] p (he.trans hn), Nat.cast_sub (hple n (he.trans hn))]
  push_cast
  ring

/-- **Blueprint node `coinvariant-growth-2`** (Washington, Proposition 13.19): if
`X ⧸ ν_{n,e} X` is finite for all sufficiently large `n`, then `X` is a torsion `Λ`-module and
`ord_p #(X ⧸ ν_{n,e} X) = μ(X) p ^ n + λ(X) n + ν` for all sufficiently large `n`. -/
theorem exists_factorization_card_quotSMulTop_nu
    {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module ℤ_[p]⟦X⟧ M]
    [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M] (e n₀ : ℕ) (he : e ≤ n₀)
    (hfin : ∀ n, n₀ ≤ n → Finite (QuotSMulTop
      ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) M)) :
    Module.IsTorsion ℤ_[p]⟦X⟧ M ∧
      ∃ (ν : ℤ) (N : ℕ), ∀ n, N ≤ n →
        ((Nat.card (QuotSMulTop
          ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) :
            ℤ_[p]⟦X⟧) M)).factorization p : ℤ) =
          (muMod p M : ℤ) * (p : ℤ) ^ n + (lambdaMod p M : ℤ) * n + ν := by
  have hp1 : 1 < p := hp.out.one_lt
  have hple : ∀ n, e ≤ n → p ^ e ≤ p ^ n := fun n hn ↦ Nat.pow_le_pow_right hp.out.pos hn
  have htor : Module.IsTorsion ℤ_[p]⟦X⟧ M := by
    refine isTorsion_of_finite_quotSMulTop M (ι := {n : ℕ // n₀ ≤ n})
      (fun i ↦ Polynomial.nu ℤ_[p] p (i : ℕ) e)
      (fun i ↦ isDistinguishedAt_nu' (he.trans i.2)) (fun c ↦ ?_) (fun i ↦ hfin i i.2)
    refine ⟨⟨max n₀ (c + p ^ e), le_max_left _ _⟩, ?_⟩
    rw [Polynomial.natDegree_nu ℤ_[p] p (he.trans (le_max_left _ _))]
    have h1 : max n₀ (c + p ^ e) < p ^ (max n₀ (c + p ^ e)) := Nat.lt_pow_self hp1
    have h2 : c + p ^ e ≤ max n₀ (c + p ^ e) := le_max_right _ _
    omega
  exact ⟨htor, exists_factorization_card_quotSMulTop_nu_of_isTorsion htor e n₀ he hfin⟩

end Nu


section Multiplicity

/-- `coinvariant-growth` in the `multiplicity` form used downstream. -/
theorem exists_multiplicity_card_quotSMulTop_omega
    {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module ℤ_[p]⟦X⟧ M]
    [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M] (n₀ : ℕ)
    (hfin : ∀ n, n₀ ≤ n → Finite (QuotSMulTop
      ((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) M)) :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n, N < n →
      (multiplicity p (Nat.card (QuotSMulTop
        ((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) M)) : ℤ)
        = (mu : ℤ) * (p : ℤ) ^ n + (lambda : ℤ) * n + nu := by
  obtain ⟨-, ν, N, hN⟩ := exists_factorization_card_quotSMulTop_omega n₀ hfin
  refine ⟨muMod p M, lambdaMod p M, ν, max n₀ N, fun n hn ↦ ?_⟩
  haveI := hfin n (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn))
  rw [Nat.multiplicity_eq_factorization hp.out]
  exact hN n (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn))

/-- `coinvariant-growth-2` in the `multiplicity` form used downstream. -/
theorem exists_multiplicity_card_quotSMulTop_nu
    {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module ℤ_[p]⟦X⟧ M]
    [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M] (e n₀ : ℕ) (he : e ≤ n₀)
    (hfin : ∀ n, n₀ ≤ n → Finite (QuotSMulTop
      ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) M)) :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n, N < n →
      (multiplicity p (Nat.card (QuotSMulTop
        ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) M)) : ℤ)
        = (mu : ℤ) * (p : ℤ) ^ n + (lambda : ℤ) * n + nu := by
  obtain ⟨-, ν, N, hN⟩ := exists_factorization_card_quotSMulTop_nu e n₀ he hfin
  refine ⟨muMod p M, lambdaMod p M, ν, max n₀ N, fun n hn ↦ ?_⟩
  haveI := hfin n (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn))
  rw [Nat.multiplicity_eq_factorization hp.out]
  exact hN n (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn))

end Multiplicity

end IwasawaAlgebra
