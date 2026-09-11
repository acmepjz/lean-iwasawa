/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Tactic.Ring
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

/-!
# Counting in an exact sequence of abelian groups

`AddMonoidHom.card_mul_card_ker_eq` records the first isomorphism theorem in the form
`#A = #(range f) * #(ker f)`, and `Nat.card_alternating_of_exact` deduces from it the
identity `#A₁ · #A₃ · #A₅ = #A₂ · #A₄ · #A₆` for a *cyclically* exact hexagon

`A₁ → A₂ → A₃ → A₄ → A₅ → A₆ → A₁ → A₂`.

This is the counting step behind the multiplicativity of the Herbrand quotient.
-/

namespace AddMonoidHom

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- The first isomorphism theorem as a cardinality identity. -/
theorem card_eq_card_range_mul_card_ker (f : A →+ B) :
    Nat.card A = Nat.card f.range * Nat.card f.ker := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker]
  exact congrArg (· * Nat.card f.ker)
    (Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv)

end AddMonoidHom

/-- **Counting in a cyclically exact hexagon.**  If

`A₁ --f₁--> A₂ --f₂--> A₃ --f₃--> A₄ --f₄--> A₅ --f₅--> A₆ --f₆--> A₁ --f₁--> A₂`

is exact at every one of the six spots, then `#A₁ · #A₃ · #A₅ = #A₂ · #A₄ · #A₆`. -/
theorem Nat.card_alternating_of_exact
    {A₁ A₂ A₃ A₄ A₅ A₆ : Type*} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]
    [AddCommGroup A₄] [AddCommGroup A₅] [AddCommGroup A₆]
    (f₁ : A₁ →+ A₂) (f₂ : A₂ →+ A₃) (f₃ : A₃ →+ A₄) (f₄ : A₄ →+ A₅) (f₅ : A₅ →+ A₆)
    (f₆ : A₆ →+ A₁)
    (e₁ : f₁.ker = f₆.range) (e₂ : f₂.ker = f₁.range) (e₃ : f₃.ker = f₂.range)
    (e₄ : f₄.ker = f₃.range) (e₅ : f₅.ker = f₄.range) (e₆ : f₆.ker = f₅.range) :
    Nat.card A₁ * Nat.card A₃ * Nat.card A₅ = Nat.card A₂ * Nat.card A₄ * Nat.card A₆ := by
  rw [f₁.card_eq_card_range_mul_card_ker, f₂.card_eq_card_range_mul_card_ker,
    f₃.card_eq_card_range_mul_card_ker, f₄.card_eq_card_range_mul_card_ker,
    f₅.card_eq_card_range_mul_card_ker, f₆.card_eq_card_range_mul_card_ker,
    e₁, e₂, e₃, e₄, e₅, e₆]
  ring

end
