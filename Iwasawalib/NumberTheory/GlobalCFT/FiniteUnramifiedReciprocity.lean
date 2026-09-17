/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.GlobalCFT.IdeleFrobenius

@[expose] public section

/-!
# Conditional finite unramified reciprocity assembly

This module records the canonical data contract for finite unramified reciprocity and the
Lean-side assembly from its two remaining arithmetic inputs.
-/

noncomputable section

namespace NumberField

/-- The finite unramified reciprocity map, with surjectivity and arithmetic-Frobenius
normalization on idele representatives. -/
structure FiniteUnramifiedReciprocityData
    (F L : Type*) [Field F] [NumberField F] [Field L] [Algebra F L]
    [IsAbelianGalois F L] [IsUnramifiedEverywhere F L]
    [FiniteDimensional F L] where
  toMonoidHom : IdeleClassGroup (𝓞 F) F →* Gal(L/F)
  surjective : Function.Surjective toMonoidHom
  mk_apply : ∀ a : IdeleGroup (𝓞 F) F,
    toMonoidHom (IdeleClassGroup.mk (𝓞 F) F a) = frobIdeleHom F L a

/-- All Lean-side assembly after the two arithmetic inputs: Artin reciprocity for principal
ideles and generation of the finite Galois group by Frobenius elements. -/
theorem finiteUnramifiedReciprocity_of_reciprocal_of_surjective_candidate
    (F L : Type*) [Field F] [NumberField F] [Field L] [Algebra F L]
    [IsAbelianGalois F L] [IsUnramifiedEverywhere F L]
    [FiniteDimensional F L]
    (hrec : IsArtinReciprocal F L)
    (hsurj : Function.Surjective (frobIdeleHom F L)) :
    Nonempty (FiniteUnramifiedReciprocityData F L) := by
  refine ⟨{
    toMonoidHom := artinIdeleClassMap F L hrec
    surjective := (surjective_artinIdeleClassMap_iff F L hrec).2 hsurj
    mk_apply := ?_
  }⟩
  intro a
  exact artinIdeleClassMap_mk F L hrec a

end NumberField
