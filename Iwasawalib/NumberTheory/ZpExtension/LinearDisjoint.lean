module

import Mathlib.FieldTheory.LinearDisjoint

open IntermediateField

universe u v

namespace IntermediateField

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

theorem linearDisjoint_of_inf_eq_bot
    (A B : IntermediateField F E)
    [IsGalois F A] [FiniteDimensional F A] [FiniteDimensional F B]
    (h : A ⊓ B = ⊥) : A.LinearDisjoint B := by
  exact IntermediateField.LinearDisjoint.iff_inf_eq_bot.mpr h

theorem inf_eq_bot_of_linearDisjoint
    (A B : IntermediateField F E) (h : A.LinearDisjoint B) :
    A ⊓ B = ⊥ :=
  h.inf_eq_bot

end IntermediateField
