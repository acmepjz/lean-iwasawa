/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.Algebra.Module.RankEulerChar
public import Mathlib.RingTheory.Finiteness.Prod

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# Additivity of `finrank` over finite products, without freeness

Over a commutative domain `A` with infinitely many elements, rank-nullity holds for finitely
generated modules, so `finrank` is additive along short exact sequences. In particular it is
additive over finite products, even for modules which are not free. Mathlib's
`Module.finrank_pi_fintype` requires freeness, which fails for the summands `Λ ⧸ (p ^ n)` of
the structure theorem.

## Main results

* `Module.finrank_le_of_surjective`, `Module.finrank_le_of_injective`.
* `Module.finrank_prod'`, `Module.finrank_pi_of_fintype`.
-/

open Function

namespace Module

variable {A : Type*} [CommRing A] [IsDomain A] [Infinite A]

section

variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

theorem finrank_le_of_surjective {f : M →ₗ[A] N} (hf : Surjective f) [Module.Finite A M] :
    Module.finrank A N ≤ Module.finrank A M := by
  have h := finrank_range_add_finrank_ker f
  rw [finrank_range_of_surjective hf] at h
  omega

theorem finrank_le_of_injective {f : M →ₗ[A] N} (hf : Injective f) [Module.Finite A N] :
    Module.finrank A M ≤ Module.finrank A N := by
  have h := (LinearMap.range f).finrank_quotient_add_finrank
  rw [finrank_range_of_injective hf] at h
  omega

variable (A M N)

/-- `finrank` is additive over binary products; unlike `Module.finrank_prod` this does not
require the factors to be free. -/
theorem finrank_prod' [Module.Finite A M] [Module.Finite A N] :
    Module.finrank A (M × N) = Module.finrank A M + Module.finrank A N := by
  have h := finrank_range_add_finrank_ker (LinearMap.snd A M N)
  rw [finrank_range_of_surjective LinearMap.snd_surjective] at h
  have hker : Module.finrank A (LinearMap.ker (LinearMap.snd A M N)) = Module.finrank A M := by
    rw [LinearMap.ker_snd, finrank_range_of_injective LinearMap.inl_injective]
  omega

end

variable (A) in
/-- `finrank` is additive over finite products; unlike `Module.finrank_pi_fintype` this does
not require the factors to be free. -/
theorem finrank_pi_of_fintype : ∀ {ι : Type*} [Fintype ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module.Finite A (M i)],
    Module.finrank A (∀ i, M i) = ∑ i, Module.finrank A (M i) := by
  apply Fintype.induction_empty_option
  · intro α β _ e IH M _ _ _
    let _ : Fintype α := .ofEquiv β e.symm
    rw [← (LinearEquiv.piCongrLeft A M e).finrank_eq, IH, e.sum_comp (finrank A <| M ·)]
  · intro M _ _ _
    have : Subsingleton ((i : PEmpty) → M i) := ⟨fun _ _ ↦ funext fun i ↦ i.elim⟩
    simp [Module.finrank_zero_of_subsingleton]
  · intro ι _ IH M _ _ _
    haveI : Module.Finite A (∀ i : ι, M (some i)) := by
      infer_instance
    rw [(LinearEquiv.piOptionEquivProd A).finrank_eq, finrank_prod', IH, add_comm,
      Fintype.sum_option, add_comm]

end Module
