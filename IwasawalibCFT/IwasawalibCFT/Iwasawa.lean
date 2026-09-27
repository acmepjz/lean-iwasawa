/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import IwasawalibCFT.HilbertClassField
import Iwasawalib.NumberTheory.ZpExtension.CyclotomicIwasawa
import Iwasawalib.NumberTheory.ZpExtension.IwasawaTheoremOfHCF

/-!
# Iwasawa's theorem, unconditionally

This file is part of the nested Lake package `IwasawalibCFT` (directory `IwasawalibCFT/` of the
repository). It is **not** a Lean module file: through `IwasawalibCFT.HilbertClassField` it
depends on the external `sorry`-free class field theory library `ClassFieldTheory`
(<https://github.com/n-yamaguchi-0729/ClassFieldTheory>, commit
`2e6280f9d2579705a0cc6c76ec68c2b60f9c601a`), which is not module based and therefore cannot be
imported by the module library `Iwasawalib`. The package is kept separate from the root package
`Iwasawalib`, so that the root package, and its CI, do not depend on the external library.

## Architecture

* `Iwasawalib/NumberTheory/NumberField/HilbertClassField/Hypothesis.lean` states the two Hilbert
  class field theorems needed as explicit propositions `NumberField.HilbertClassFieldUpperBound`
  and `NumberField.HilbertClassFieldExistence`, and
  `Iwasawalib/NumberTheory/ZpExtension/IwasawaTheoremOfHCF.lean` proves, without `sorry`,
  Iwasawa's theorem from them: `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf`.
* `IwasawalibCFT/IwasawalibCFT/HilbertClassField.lean` proves the two hypotheses from the
  external library.
* This file combines the two into **Iwasawa's theorem**
  `MvZpExtension.multiplicity_classNumber_Kn_eq₁`, which depends only on the axioms `propext`,
  `Classical.choice` and `Quot.sound`, and applies it to the cyclotomic `ℤₚ`-extension of every
  number field (`NumberField.exists_cyclotomic_multiplicity_classNumber_eq`).

Up to commit `b236c1b` the library `Iwasawalib` contained a theorem
`MvZpExtension.multiplicity_classNumber_Kn_eq₁` with the same statement, proved from class field
theory `sorry`s, and this file proved it without `sorry` under the same name with the suffix
_unconditional, with a build-time check that the two constants
had the same universe parameters and alpha-equivalent types. The `sorry`-based theorem has been
removed, and the `sorry`-free one took over its name.
`NumberField.exists_cyclotomic_multiplicity_classNumber_eq` likewise has the statement it had in
`Iwasawalib/NumberTheory/ZpExtension/CyclotomicIwasawa.lean` at that commit.

The guards at the end of the file (the `#print axioms` outputs, and the fact that the statement
of `MvZpExtension.multiplicity_classNumber_Kn_eq₁` is the conclusion of
`MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf`) are checked whenever the package is built
(`cd IwasawalibCFT && lake build`). The repository's CI builds only `Iwasawalib` and does not
run them.

## Main statements

* `MvZpExtension.multiplicity_classNumber_Kn_eq₁`: **Iwasawa's theorem**, free of `sorry`.
* `NumberField.exists_cyclotomic_multiplicity_classNumber_eq`: Iwasawa's formula for the
  cyclotomic `ℤₚ`-extension of every number field, free of `sorry`.
-/

universe u

section Main

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*}
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- **Iwasawa's theorem** on growth of class groups of `ℤₚ`-extension of number fields
(Washington, *Introduction to cyclotomic fields*, Theorem 13.13): for a `ℤₚ`-extension `K∞ / K`
of a number field with layers `Kₙ` there are natural numbers `μ`, `λ`, an integer `ν` and a bound
`N` such that `ord_p #Cl(Kₙ) = μ pⁿ + λ n + ν` for all `n > N`.

It is `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf` applied to the Hilbert class field
theorems `NumberField.hilbertClassFieldUpperBound` and `NumberField.hilbertClassFieldExistence`
proved from the external class field theory library, and it depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`. -/
theorem multiplicity_classNumber_Kn_eq₁ [Unique ι] :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n > N,
      multiplicity p (NumberField.classNumber (H.Kn n)) = mu * p ^ n + lambda * n + nu :=
  multiplicity_classNumber_Kn_eq₁_of_hcf NumberField.hilbertClassFieldUpperBound
    NumberField.hilbertClassFieldExistence H

end MvZpExtension

end Main

namespace NumberField

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]

/-- **Iwasawa's theorem for the cyclotomic `ℤₚ`-extension of a number field.**  For every prime
`p` and every number field `K` there is a cyclotomic `ℤₚ`-extension `K∞ / K`, with some
`H : MvZpExtension p (Fin 1) K K∞`, and natural numbers `μ`, `λ`, an integer `ν` and a bound
`N` such that `ord_p #Cl(Kₙ) = μ pⁿ + λ n + ν` for all `n > N`.

The extension is the one of `NumberField.exists_isCyclotomicZpExtension` (an infinite extension,
whose `n`-th layer has degree `p ^ n`), and the formula is
`MvZpExtension.multiplicity_classNumber_Kn_eq₁` applied to it. It depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`. -/
theorem exists_cyclotomic_multiplicity_classNumber_eq :
    ∃ (Kinf : Type u) (_ : Field Kinf) (_ : Algebra K Kinf) (_ : IsGalois K Kinf)
      (H : MvZpExtension p (Fin 1) K Kinf), IsCyclotomicZpExtension p K Kinf ∧
      ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n > N,
        (multiplicity p (NumberField.classNumber (H.Kn n)) : ℤ) =
          mu * p ^ n + lambda * n + nu := by
  obtain ⟨Kinf, _, _, _, hK, ⟨H⟩, -⟩ := exists_isCyclotomicZpExtension p K
  exact ⟨Kinf, _, _, _, H, hK, H.multiplicity_classNumber_Kn_eq₁⟩

end NumberField

/-! ### Build-time guards -/

/--
info: 'MvZpExtension.multiplicity_classNumber_Kn_eq₁' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms MvZpExtension.multiplicity_classNumber_Kn_eq₁

/--
info: 'NumberField.exists_cyclotomic_multiplicity_classNumber_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms NumberField.exists_cyclotomic_multiplicity_classNumber_eq

/--
info: 'NumberField.hilbertClassFieldUpperBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms NumberField.hilbertClassFieldUpperBound

/--
info: 'NumberField.hilbertClassFieldExistence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms NumberField.hilbertClassFieldExistence

/--
info: 'NumberField.hilbertClassFieldUpperBound_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms NumberField.hilbertClassFieldUpperBound_zero

/--
info: 'NumberField.hilbertClassFieldExistence_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms NumberField.hilbertClassFieldExistence_zero

/- The statement of `MvZpExtension.multiplicity_classNumber_Kn_eq₁` is, syntactically, the
conclusion of `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf` once its two hypotheses are
instantiated: the type of the latter is `∀ hU hE, T` with `T` not depending on `hU` and `hE`, and
`T`, up to renaming of universe parameters, is alpha-equivalent to the type of the former
(`Lean.Expr.eqv`); moreover the two types have the same binder annotations and the same names
for all binders other than the (anonymous, hygienic) instance binders. -/
open Lean in
run_cmd do
  let env ← getEnv
  let some c₁ := env.find? ``MvZpExtension.multiplicity_classNumber_Kn_eq₁
    | throwError "missing MvZpExtension.multiplicity_classNumber_Kn_eq₁"
  let some c₂ := env.find? ``MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf
    | throwError "missing MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf"
  let .forallE _ _ (.forallE _ _ body _) _ := c₂.type
    | throwError "unexpected shape of the type of multiplicity_classNumber_Kn_eq₁_of_hcf"
  if body.hasLooseBVars then
    throwError "the conclusion of multiplicity_classNumber_Kn_eq₁_of_hcf depends on its hypotheses"
  unless c₁.levelParams.length == c₂.levelParams.length do
    throwError "different numbers of universe parameters"
  let lvls₁ := c₁.levelParams.map Level.param
  unless lvls₁.permutations.any fun lvls ↦
      body.instantiateLevelParams c₂.levelParams lvls == c₁.type do
    throwError "MvZpExtension.multiplicity_classNumber_Kn_eq₁ does not have the statement of the \
      conclusion of MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf"
  let mut e₁ := c₁.type
  let mut e₂ := body
  while e₁.isForall do
    unless e₂.isForall && e₁.bindingInfo! == e₂.bindingInfo! &&
        (e₁.bindingInfo!.isInstImplicit || e₁.bindingName! == e₂.bindingName!) do
      throwError "binder mismatch at {e₁.bindingName!}"
    e₁ := e₁.bindingBody!
    e₂ := e₂.bindingBody!
