module

public import Mathlib.FieldTheory.LinearDisjoint

@[expose] public section

variable {F F' E : Type*} [Field F] [Field F'] [Field E]
variable [Algebra F F'] [Algebra F E] [Algebra F' E]
variable [IsScalarTower F F' E]

theorem IntermediateField.finrank_adjoin_eq_finrank_of_linearDisjoint
    (A : IntermediateField F E) [FiniteDimensional F A]
    (h : A.LinearDisjoint F') :
    Module.finrank F' (IntermediateField.adjoin F' (A : Set E)) =
      Module.finrank F A := by
  letI : Algebra.IsAlgebraic F (↥A) := Algebra.IsAlgebraic.of_finite F (↥A)
  have hrank := h.adjoin_rank_eq_rank_left_of_isAlgebraic_left
  simpa only [Module.finrank] using congrArg Cardinal.toNat hrank
