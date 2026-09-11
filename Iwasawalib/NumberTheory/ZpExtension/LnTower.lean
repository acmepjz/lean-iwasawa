/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.Compositum
public import Iwasawalib.NumberTheory.ZpExtension.Ln

@[expose] public section

/-!

# The tower `L₀ ⊆ L₁ ⊆ ⋯` of maximal unramified abelian `p`-extensions

Let `K∞ / K` be a `ℤₚᵈ`-extension of number fields, with layers `Kₙ`, and let `Lₙ` be the
maximal unramified abelian `p`-extension of `Kₙ` inside a fixed separable closure of `K∞`
(`MvZpExtension.Ln`). The main result of this file is `MvZpExtension.Ln_mono`, saying that
the fields `Lₙ` increase, together with its sharper form `MvZpExtension.adjoin_Ln_le`
(`Kₙ Lₘ ⊆ Lₙ` for `m ≤ n`).

-/

open IntermediateField NumberField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- The separable closure of `K∞` is a separable closure of each `Kₙ`. -/
instance isSepClosure_Kn (n : ℕ) : IsSepClosure (H.Kn n) (SeparableClosure Kinf) :=
  IsSepClosure.ofSeparable (H.Kn n) Kinf (SeparableClosure Kinf)

/-- `Lₙ / Kₙ` is a `{p}`-extension, i.e. its degree is a power of `p`. -/
instance isSExtension_Ln (n : ℕ) : IsSExtension (H.Kn n) (H.Ln n) {p} :=
  .of_algEquiv {p} (IntermediateField.liftAlgEquiv _)

/-- Warning: like `MvZpExtension.finrank_Ln`, this depends on the class field theory `sorry`s in
`Iwasawalib.NumberTheory.NumberField.HilbertClassField.ClassFieldTheory`, because the
finiteness of `Lₙ / Kₙ` does. `MvZpExtension.isSExtension_Ln` is the `sorry`-free form that
`MvZpExtension.Ln_mono` actually uses. -/
theorem exists_finrank_Ln_eq_pow (n : ℕ) : ∃ k, Module.finrank (H.Kn n) (H.Ln n) = p ^ k :=
  (isSExtension_singleton_iff_of_finiteDimensional (H.Kn n) (H.Ln n) p).1 inferInstance

/-- The compositum `Kₙ Lₘ` is contained in `Lₙ` for `m ≤ n`: it is an unramified abelian
extension of `Kₙ` of `p`-power degree. This is the blueprint node `Ln-mono`. -/
theorem adjoin_Ln_le {m n : ℕ} (h : m ≤ n) :
    IntermediateField.adjoin (H.Kn n) (H.Ln m : Set (SeparableClosure Kinf)) ≤ H.Ln n :=
  IntermediateField.adjoin_le_lift_maximalGaloisSExtension_of_ringHom
    (IntermediateField.inclusion (H.monotone_Kn h)).toRingHom
    (IntermediateField.algebraMap_inclusion (Ω := SeparableClosure Kinf) (H.monotone_Kn h)
      (fun y ↦ IsScalarTower.algebraMap_apply (H.Kn m) Kinf (SeparableClosure Kinf) y)
      (fun y ↦ IsScalarTower.algebraMap_apply (H.Kn n) Kinf (SeparableClosure Kinf) y))
    (H.Ln m)

/-- `Lₘ ⊆ Lₙ` for `m ≤ n`. This is the blueprint node `Ln-mono`. -/
theorem Ln_mono {m n : ℕ} (h : m ≤ n) :
    (H.Ln m : Set (SeparableClosure Kinf)) ⊆ (H.Ln n : Set (SeparableClosure Kinf)) :=
  fun _ hx ↦ H.adjoin_Ln_le h (IntermediateField.subset_adjoin _ _ hx)

end MvZpExtension
