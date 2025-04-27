/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Exact

/-!

# Some auxiliary results for `Function.Exact`

-/

namespace Function.Exact

variable {R M N P : Type*}

section Set

variable [Zero P] {f : M → N} {g : N → P}

theorem iff_rangeFactorization (hg : 0 ∈ Set.range g) :
    letI : Zero (Set.range g) := ⟨⟨0, hg⟩⟩
    Exact f g ↔ Exact ((↑) : Set.range f → N) (Set.rangeFactorization g) := by
  rw [Exact, Exact, Subtype.range_coe]
  congr! 2
  rw [Set.rangeFactorization]
  exact ⟨fun _ ↦ by rwa [Subtype.ext_iff], fun h ↦ by rwa [Subtype.ext_iff] at h⟩

theorem rangeFactorization (H : Exact f g) (hg : 0 ∈ Set.range g) :
    letI : Zero (Set.range g) := ⟨⟨0, hg⟩⟩
    Exact ((↑) : Set.range f → N) (Set.rangeFactorization g) :=
  (iff_rangeFactorization hg).1 H

end Set

section AddMonoidHom

variable [AddGroup M] [AddGroup N] [AddGroup P] {f : M →+ N} {g : N →+ P}

theorem iff_addMonoidHom_rangeRestrict :
    Exact f g ↔ Exact f.range.subtype g.rangeRestrict :=
  iff_rangeFactorization (zero_mem g.range)

alias ⟨addMonoidHom_rangeRestrict, _⟩ := iff_addMonoidHom_rangeRestrict

end AddMonoidHom

section LinearMap

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem iff_linearMap_rangeRestrict :
    Exact f g ↔ Exact f.range.subtype g.rangeRestrict :=
  iff_rangeFactorization (zero_mem (LinearMap.range g))

alias ⟨linearMap_rangeRestrict, _⟩ := iff_linearMap_rangeRestrict

end LinearMap

end Function.Exact
