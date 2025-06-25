/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!

# Cyclotomic extension of finite field

-/

theorem FiniteField.isCyclotomicExtension_iff_isAlgClosure (K L : Type*) [Field K] [Field L]
    [Algebra K L] [Finite K] : IsCyclotomicExtension {n | (n : K) ≠ 0} K L ↔ IsAlgClosure K L := by
  -- unused so just leave it as sorry
  sorry
