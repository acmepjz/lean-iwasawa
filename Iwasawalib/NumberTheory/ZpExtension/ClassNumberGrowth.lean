/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.Basic
public import Iwasawalib.RingTheory.IwasawaAlgebra.GrowthTransport
public import Mathlib.NumberTheory.NumberField.ClassNumber

@[expose] public section

/-!
# Iwasawa's class number theorem, conditional on `Xn-isom-qout`

The `Λ`-module side of Iwasawa's theorem on growth of class groups is complete: blueprint node
`finite-index-submodule-growth` is
`IwasawaAlgebra.exists_multiplicity_card_quotient_smul_submodule_of_isTorsion`.
What is still missing is the arithmetic input, blueprint nodes
`Xn-isom-qout` (`X_n ≅ X_∞ / ν_{n,e} Y`) and `Xn-isom-An` (`ord_p #Cl(K_n) = ord_p #X_n`).

`MvZpExtension.finrank_Ln` is the Lean form of `Xn-isom-An`, but as of this file it still
depends on `sorryAx` (through `NumberField.bijective_artinMap_of_isSepClosed` in
`Iwasawalib/NumberTheory/NumberField/HilbertClassField/ClassFieldTheory.lean`).  Closing
`MvZpExtension.multiplicity_classNumber_Kn_eq₁` on top of it would produce a theorem that
*looks* proved and is not, so it is deliberately **not** closed here.

Instead this file records the assembly as a standalone, unconditionally proved theorem which
takes the missing arithmetic as an explicit hypothesis: once someone produces, for a
`ℤₚ`-extension `K∞/K`, a finitely generated torsion `Λ`-module `M` (`= X_∞`) with a
finite-index `Λ`-submodule `Y` and the cardinality identity

`#(M / ν_{n,e} Y) = p ^ ord_p(h_{K_n})` for all `n ≥ e`,

Iwasawa's formula follows by `exists_multiplicity_classNumber_of_card_eq` below.  Combining
that hypothesis with blueprint node `Xn-isom-qout` (which supplies `X_n ≅ M / ν_{n,e} Y`) and
`Xn-isom-An` (which supplies `#X_n = p ^ ord_p(h_{K_n})`) gives
`MvZpExtension.multiplicity_classNumber_Kn_eq₁`.
-/

open Module PowerSeries
open scoped Pointwise

universe u v

namespace MvZpExtension

variable {p : ℕ} [hp : Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

variable (H : MvZpExtension p ι K Kinf)

/-- **Iwasawa's class number theorem, conditional on blueprint nodes `Xn-isom-qout` and
`Xn-isom-An`.**  If the `p`-parts of the class numbers of the layers `K_n` are the
cardinalities of the quotients `M / ν_{n,e} Y` of a finitely generated torsion `Λ`-module `M`
by a finite-index `Λ`-submodule `Y`, then `ord_p(h_{K_n}) = μ p^n + λ n + ν` for large `n`.

This is proved unconditionally; the hypothesis `hcard` is exactly the arithmetic input that is
not yet formalized (see the module docstring). -/
theorem exists_multiplicity_classNumber_of_card_eq
    {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]
    (hM : Module.IsTorsion ℤ_[p]⟦X⟧ M)
    (Y : Submodule ℤ_[p]⟦X⟧ M) [Finite (M ⧸ Y)] (e : ℕ)
    (hfin : ∀ n, e ≤ n → Finite (M ⧸
      (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y)))
    (hcard : ∀ n, e ≤ n → Nat.card (M ⧸
      (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y))
        = p ^ multiplicity p (NumberField.classNumber (H.Kn n))) :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n, N < n →
      (multiplicity p (NumberField.classNumber (H.Kn n)) : ℤ)
        = (mu : ℤ) * (p : ℤ) ^ n + (lambda : ℤ) * n + nu := by
  classical
  set c : ℕ → ℕ := fun n ↦ p ^ multiplicity p (NumberField.classNumber (H.Kn n)) with hc
  obtain ⟨mu, lambda, ν, N, hN⟩ :=
    IwasawaAlgebra.exists_multiplicity_card_of_card_eq hM Y e hfin c fun n hn ↦ (hcard n hn).symm
  refine ⟨mu, lambda, ν, max e N, fun n hn ↦ ?_⟩
  have hmul : multiplicity p (c n) = multiplicity p (NumberField.classNumber (H.Kn n)) :=
    multiplicity_pow_self_of_prime hp.out.prime _
  have := hN n (lt_of_le_of_lt (le_max_right _ _) hn)
  rwa [hmul] at this

end MvZpExtension
