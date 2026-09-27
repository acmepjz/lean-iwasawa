/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.FieldTheory.ZpExtension.Cyclotomic

@[expose] public section

/-!
# Iwasawa's theorem for the cyclotomic `ℤₚ`-extension of a number field

Iwasawa's theorem (`MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf`, and its
unconditional form `MvZpExtension.multiplicity_classNumber_Kn_eq₁` in the nested package
`IwasawalibCFT`) is stated for an arbitrary `H : MvZpExtension p ι K K∞` with `ι` a singleton.
This file shows that the hypotheses can be met, for every prime `p` and every number field `K`:
the cyclotomic `ℤₚ`-extension of `K` exists (instance `NumberField.hasCyclotomicZpExtension`), it
is a `ℤₚ`-extension in the sense of `MvZpExtension p (Fin 1)`, and it is not a degenerate
witness: `K∞ / K` is an infinite extension and its `n`-th layer `Kₙ` has degree `p ^ n` over
`K`.  One such `K∞` is
`CyclotomicPinfField.cyclotomicZpSubfield p K`, see
`hasCyclotomicZpExtension_iff_isCyclotomicZpExtension_cyclotomicZpSubfield`.

## Main statements

* `NumberField.exists_isCyclotomicZpExtension`: every number field has a cyclotomic
  `ℤₚ`-extension `K∞`; `K∞ / K` is infinite, and for every `H : MvZpExtension p (Fin 1) K K∞`
  the layer `Kₙ` has degree `p ^ n` over `K`.  Proved without `sorryAx`.

Iwasawa's formula `ord_p #Cl(Kₙ) = μ pⁿ + λ n + ν` (for large `n`) for this cyclotomic
`ℤₚ`-extension, `NumberField.exists_cyclotomic_multiplicity_classNumber_eq`, is proved from this
theorem in the nested package `IwasawalibCFT`.
-/

universe u

namespace NumberField

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]

/-- **Every number field has a cyclotomic `ℤₚ`-extension, and it is a genuine
`ℤₚ`-extension.**  For every prime `p` and every number field `K` there is a Galois extension
`K∞ / K` which is a cyclotomic `ℤₚ`-extension (`IsCyclotomicZpExtension p K K∞`), hence carries
some `H : MvZpExtension p (Fin 1) K K∞`; moreover `K∞ / K` is not finite-dimensional
(`IsCyclotomicZpExtension.infinite_dimensional`) and, for every such `H`, the layer `Kₙ` has
degree `p ^ n` over `K` (`MvZpExtension.finrank_Kn₁`).

In particular the hypotheses of Iwasawa's theorem
(`MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf`) are satisfiable, by a non-trivial tower,
for every number field.

Proved without `sorryAx`, from the instance `NumberField.hasCyclotomicZpExtension`. -/
theorem exists_isCyclotomicZpExtension :
    ∃ (Kinf : Type u) (_ : Field Kinf) (_ : Algebra K Kinf) (_ : IsGalois K Kinf),
      IsCyclotomicZpExtension p K Kinf ∧ Nonempty (MvZpExtension p (Fin 1) K Kinf) ∧
        ¬FiniteDimensional K Kinf ∧
        ∀ (H : MvZpExtension p (Fin 1) K Kinf) (n : ℕ), Module.finrank K (H.Kn n) = p ^ n := by
  obtain ⟨Kinf, _, _, _, hK⟩ :=
    (inferInstance : HasCyclotomicZpExtension p K).exists_isCyclotomicZpExtension
  exact ⟨Kinf, _, _, _, hK, hK.isZpExtension, hK.infinite_dimensional,
    fun H n ↦ H.finrank_Kn₁ n⟩

end NumberField
