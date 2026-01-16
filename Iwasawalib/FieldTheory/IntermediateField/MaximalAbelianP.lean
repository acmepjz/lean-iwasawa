/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.Galois.Abelian
public import Iwasawalib.GroupTheory.Torsion

@[expose] public section

/-!

# Maximal abelian `p`-subextension

-/

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

namespace IntermediateField

/-- The maximal abelian `p`-subextension of `K / F` is the compositum of all
finite abelian subextension of `K / F` whose degree is a power of `p`. -/
def maximalAbelianPExtension (p : ℕ) : IntermediateField F K :=
  sSup {E | FiniteDimensional F E ∧ IsAbelianGalois F E ∧ ∃ n, Module.finrank F E = p ^ n}

instance isAbelianGalois_maximalAbelianPExtension (p : ℕ) :
    IsAbelianGalois F (maximalAbelianPExtension F K p) := by
  sorry

theorem exists_finrank_maximalAbelianPExtension_eq (p : ℕ) [Fact p.Prime] [FiniteDimensional F K] :
    ∃ n, Module.finrank F (maximalAbelianPExtension F K p) = p ^ n := by
  sorry

theorem not_dvd_finrank_maximalAbelianPExtension (p : ℕ) [Fact p.Prime] [FiniteDimensional F K]
    [IsAbelianGalois F K] :
    ¬p ∣ Module.finrank (maximalAbelianPExtension F K p) K := by
  sorry

theorem fixingSubgroup_maximalAbelianPExtension (p : ℕ) [Fact p.Prime] [FiniteDimensional F K]
    [IsAbelianGalois F K] :
    (maximalAbelianPExtension F K p).fixingSubgroup = CommGroup.primeToComponent Gal(K/F) p := by
  sorry

end IntermediateField
