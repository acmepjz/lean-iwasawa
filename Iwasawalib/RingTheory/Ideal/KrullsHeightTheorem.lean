/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.RingTheory.Ideal.UFD

@[expose] public section

/-!

# Consequences of Krull's Height Theorem

The results in this file were already in mathlib (with different names).

-/

@[deprecated (since := "2026-07-25")]
alias UniqueFactorizationMonoid.of_primeHeight_eq_one_imp_isPrincipal :=
  UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one

@[deprecated (since := "2026-07-25")]
alias IsNoetherianRing.uniqueFactorizationMonoid_iff :=
  UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one
