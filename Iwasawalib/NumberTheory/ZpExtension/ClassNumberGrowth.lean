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
The arithmetic input, blueprint nodes `Xn-isom-qout` (`X_n ≅ X_∞ / ν_{n,e} Y`) and `Xn-isom-An`
(`ord_p #Cl(K_n) = ord_p #X_n`), is now supplied, conditionally on class field theory: the main theorem
`MvZpExtension.multiplicity_classNumber_Kn_eq₁` is closed through
`MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_cft`
(`Iwasawalib/NumberTheory/ZpExtension/IwasawaTheorem.lean`).

That proof is still **conditional on class field theory**.  For instance
`MvZpExtension.finrank_Ln`, the Lean form of `Xn-isom-An`, depends on `sorryAx` through the
class field theory `sorry`s `NumberField.IsUnramifiedEverywhere.artinMap`,
`NumberField.IsUnramifiedEverywhere.surjective_artinMap` and
`NumberField.IsUnramifiedEverywhere.bijective_artinMap_of_isSepClosed` of
`Iwasawalib/NumberTheory/NumberField/HilbertClassField/ClassFieldTheory.lean`; see the
docstring of `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_cft` for the route.

This file records the last step of the assembly as a standalone, unconditionally proved
theorem which takes the arithmetic as an explicit hypothesis: for a `ℤₚ`-extension `K∞/K`, a
finitely generated torsion `Λ`-module `M` (`= X_∞`) with a finite-index `Λ`-submodule `Y` and
the cardinality identity

`#(M / ν_{n,e} Y) = p ^ ord_p(h_{K_n})` for all `n ≥ e`,

Iwasawa's formula follows by `exists_multiplicity_classNumber_of_card_eq` below.  That
hypothesis is discharged, with `M = X_∞`, in
`MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_eventual_Yn_data`
(`Iwasawalib/NumberTheory/ZpExtension/EventualClassNumberBridge.lean`), which lies on the proof
route of `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_cft`.
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

This is proved unconditionally; the hypothesis `hcard` is the arithmetic input, discharged in
`MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_eventual_Yn_data` (see the module
docstring). -/
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
