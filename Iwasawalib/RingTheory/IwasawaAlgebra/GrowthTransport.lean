/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.FiniteIndexGrowth

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# Transporting the growth formula along abstract isomorphisms

`IwasawaAlgebra.exists_multiplicity_card_quotient_smul_submodule_of_isTorsion` computes the
growth of `ord_p #(M / ν_{n,e} Y)`.  In the arithmetic application the groups one actually
cares about (`X_n = Gal(L_n/K_n)`) are only *isomorphic* to these quotients, so this file
records the transport of the conclusion along a family of additive isomorphisms.

This is the final step of the proof of Iwasawa's class number formula: blueprint node
`Xn-isom-qout` supplies the family of isomorphisms, and `clgp-growth` is the conclusion.
-/

open Module PowerSeries
open scoped Pointwise

namespace IwasawaAlgebra

variable {p : ℕ} [hp : Fact p.Prime]

/-- Transport of `exists_multiplicity_card_quotient_smul_submodule_of_isTorsion` along a family
of additive isomorphisms `A n ≃+ M / ν_{n,e} Y`.  This is the shape in which Iwasawa's theorem
on growth of class groups consumes the module-theoretic growth formula. -/
theorem exists_multiplicity_card_of_addEquiv_quotient_nu_smul
    {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]
    (hM : Module.IsTorsion ℤ_[p]⟦X⟧ M)
    (Y : Submodule ℤ_[p]⟦X⟧ M) [Finite (M ⧸ Y)] (e : ℕ)
    {A : ℕ → Type*} [∀ n, AddCommGroup (A n)] [hA : ∀ n, Finite (A n)]
    (iso : ∀ n, e ≤ n → (A n ≃+
      (M ⧸ (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y)))) :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n, N < n →
      (multiplicity p (Nat.card (A n)) : ℤ)
        = (mu : ℤ) * (p : ℤ) ^ n + (lambda : ℤ) * n + nu := by
  have hcard : ∀ n, e ≤ n → Nat.card (A n) = Nat.card (M ⧸
      (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y)) :=
    fun n hn ↦ Nat.card_congr (iso n hn).toEquiv
  have hfin : ∀ n, e ≤ n → Finite (M ⧸
      (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y)) :=
    fun n hn ↦ Finite.of_equiv _ (iso n hn).toEquiv
  obtain ⟨mu, lambda, ν, N, hN⟩ :=
    exists_multiplicity_card_quotient_smul_submodule_of_isTorsion hM Y e e le_rfl hfin
  refine ⟨mu, lambda, ν, max e N, fun n hn ↦ ?_⟩
  rw [hcard n (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn))]
  exact hN n (lt_of_le_of_lt (le_max_right _ _) hn)

/-- Cardinality form of `exists_multiplicity_card_of_addEquiv_quotient_nu_smul`: only the
equality of cardinalities is needed, so the isomorphisms may be of any kind (in the arithmetic
application `X_n = Gal(L_n/K_n)` is a multiplicative group). -/
theorem exists_multiplicity_card_of_card_eq
    {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]
    (hM : Module.IsTorsion ℤ_[p]⟦X⟧ M)
    (Y : Submodule ℤ_[p]⟦X⟧ M) [Finite (M ⧸ Y)] (e : ℕ)
    (hfin : ∀ n, e ≤ n → Finite (M ⧸
      (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y)))
    (c : ℕ → ℕ)
    (hcard : ∀ n, e ≤ n → c n = Nat.card (M ⧸
      (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y))) :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n, N < n →
      (multiplicity p (c n) : ℤ) = (mu : ℤ) * (p : ℤ) ^ n + (lambda : ℤ) * n + nu := by
  obtain ⟨mu, lambda, ν, N, hN⟩ :=
    exists_multiplicity_card_quotient_smul_submodule_of_isTorsion hM Y e e le_rfl hfin
  refine ⟨mu, lambda, ν, max e N, fun n hn ↦ ?_⟩
  rw [hcard n (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn))]
  exact hN n (lt_of_le_of_lt (le_max_right _ _) hn)

end IwasawaAlgebra
