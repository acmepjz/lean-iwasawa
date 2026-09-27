/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import IwasawalibCFT.HilbertClassField
import Iwasawalib.NumberTheory.ZpExtension.ClassGroup
import Iwasawalib.NumberTheory.ZpExtension.IwasawaTheoremOfHCF

/-!
# Iwasawa's theorem, unconditionally

This file is part of the leaf library `IwasawalibCFT`. It is **not** a Lean module file: through
`IwasawalibCFT.HilbertClassField` it depends on the external `sorry`-free class field theory
library `ClassFieldTheory` (<https://github.com/n-yamaguchi-0729/ClassFieldTheory>, commit
`2e6280f9d2579705a0cc6c76ec68c2b60f9c601a`), which is not module based and therefore cannot be
imported by the module library `Iwasawalib`.

## Architecture

* `Iwasawalib` proves Iwasawa's theorem `MvZpExtension.multiplicity_classNumber_Kn_eq₁` using the
  class field theory `sorry`s of
  `Iwasawalib/NumberTheory/NumberField/HilbertClassField/ClassFieldTheory.lean`, so its
  `#print axioms` shows `sorryAx`.
* `Iwasawalib/NumberTheory/NumberField/HilbertClassField/Hypothesis.lean` states the two Hilbert
  class field theorems needed as explicit propositions `NumberField.HilbertClassFieldUpperBound`
  and `NumberField.HilbertClassFieldExistence`, and
  `Iwasawalib/NumberTheory/ZpExtension/IwasawaTheoremOfHCF.lean` proves, without `sorry`,
  Iwasawa's theorem from them: `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf`.
* `IwasawalibCFT/HilbertClassField.lean` proves the two hypotheses from the external library.
* This file combines the two into `MvZpExtension.multiplicity_classNumber_Kn_eq₁_unconditional`,
  which has exactly the statement of `MvZpExtension.multiplicity_classNumber_Kn_eq₁` and depends
  only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

The guards at the end of the file (the `#print axioms` outputs, and the fact that the
unconditional theorem and `MvZpExtension.multiplicity_classNumber_Kn_eq₁` have the same type) are
checked whenever the `IwasawalibCFT` target is built (`lake build IwasawalibCFT`).  It is not a
default target, so a plain `lake build`, and the repository's CI, do not run them.

## Main statements

* `MvZpExtension.multiplicity_classNumber_Kn_eq₁_unconditional`: **Iwasawa's theorem**, free of
  `sorry`.
-/

/- The following instances depend on `sorryAx` (through the class field theory `sorry`s of
`Iwasawalib/NumberTheory/NumberField/HilbertClassField/ClassFieldTheory.lean`); they are removed
from instance search so that nothing in this file can use them. -/
attribute [-instance] NumberField.IsUnramifiedEverywhere.finiteDimensional
  NumberField.finiteDimensional_maximalUnramifiedAbelianExtension
  NumberField.numberField_maximalUnramifiedAbelianExtension
  MvZpExtension.finiteDimensional_Ln MvZpExtension.numberField_Ln
  MvZpExtension.finiteDimensional_Ln'

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*}
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- **Iwasawa's theorem** on growth of class groups of `ℤₚ`-extension of number fields
(Washington, *Introduction to cyclotomic fields*, Theorem 13.13), **unconditionally**: for a
`ℤₚ`-extension `K∞ / K` of a number field with layers `Kₙ` there are natural numbers `μ`, `λ`, an
integer `ν` and a bound `N` such that `ord_p #Cl(Kₙ) = μ pⁿ + λ n + ν` for all `n > N`.

It has exactly the statement of `MvZpExtension.multiplicity_classNumber_Kn_eq₁`. It is
`MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf` applied to the Hilbert class field
theorems `NumberField.hilbertClassFieldUpperBound` and `NumberField.hilbertClassFieldExistence`
proved from the external class field theory library, and it depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`. -/
theorem multiplicity_classNumber_Kn_eq₁_unconditional [Unique ι] :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n > N,
      multiplicity p (NumberField.classNumber (H.Kn n)) = mu * p ^ n + lambda * n + nu :=
  multiplicity_classNumber_Kn_eq₁_of_hcf NumberField.hilbertClassFieldUpperBound
    NumberField.hilbertClassFieldExistence H

end MvZpExtension

/-! ### Build-time guards -/

/--
info: 'MvZpExtension.multiplicity_classNumber_Kn_eq₁_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms MvZpExtension.multiplicity_classNumber_Kn_eq₁_unconditional

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

/- The unconditional theorem and `MvZpExtension.multiplicity_classNumber_Kn_eq₁` have the same
type: the equation below only typechecks if the two types are definitionally equal (and then it
holds by proof irrelevance). -/
example : @MvZpExtension.multiplicity_classNumber_Kn_eq₁_unconditional =
    @MvZpExtension.multiplicity_classNumber_Kn_eq₁ := rfl

/- A stronger, syntactic version of the previous check: both constants have the same universe
parameters and alpha-equivalent types. -/
open Lean in
run_cmd do
  let env ← getEnv
  let some c₁ := env.find? ``MvZpExtension.multiplicity_classNumber_Kn_eq₁_unconditional
    | throwError "missing MvZpExtension.multiplicity_classNumber_Kn_eq₁_unconditional"
  let some c₂ := env.find? ``MvZpExtension.multiplicity_classNumber_Kn_eq₁
    | throwError "missing MvZpExtension.multiplicity_classNumber_Kn_eq₁"
  unless c₁.levelParams == c₂.levelParams && c₁.type == c₂.type do
    throwError "the unconditional theorem does not have the statement of \
      MvZpExtension.multiplicity_classNumber_Kn_eq₁"
