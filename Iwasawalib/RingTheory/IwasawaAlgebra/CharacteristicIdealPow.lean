/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.CharacteristicIdeal.Basic
public import Iwasawalib.RingTheory.IwasawaAlgebra.LambdaStructure
public import Iwasawalib.RingTheory.PseudoNull.CharacteristicIdeal
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

@[expose] public section

/-!
# The characteristic ideal of `A ⧸ (q ^ c)`

For a prime element `q` of a Noetherian domain `A` whose associated prime ideal has height one,
the characteristic ideal of `A ⧸ (q ^ c)` is `(q) ^ c`. This is the computational half of
blueprint node `Lambda-module-structure` needed to identify the `μ`- and `λ`-invariants of a
finitely generated torsion `Λ`-module with those of a generator of its characteristic ideal.

The proof is an induction on `c` along the exact sequences
`0 → A ⧸ (q ^ c) --·q--> A ⧸ (q ^ (c + 1)) → A ⧸ (q) → 0`,
using additivity of the characteristic ideal.

## Main results

* `Module.charIdeal_quotient_span_singleton_pow`.
* `IwasawaAlgebra.charIdeal_quotient_span_pow`: the case `A = Λ`.
-/

open Function

set_option linter.unusedSectionVars false

namespace Module

section

variable {A : Type*} [CommRing A] [IsDomain A] (q : A) (c : ℕ)

/-- Multiplication by `q`, from `A ⧸ (q ^ c)` to `A ⧸ (q ^ (c + 1))`. -/
noncomputable def mulQMap :
    (A ⧸ (Ideal.span {q ^ c} : Ideal A)) →ₗ[A] (A ⧸ (Ideal.span {q ^ (c + 1)} : Ideal A)) :=
  Submodule.mapQ _ _ (LinearMap.lsmul A A q) (by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine Ideal.mem_span_singleton'.2 ⟨y, ?_⟩
    simp only [LinearMap.lsmul_apply, smul_eq_mul]
    ring)

@[simp]
theorem mulQMap_mk (y : A) :
    mulQMap q c (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (p := (Ideal.span {q ^ (c + 1)} : Ideal A)) (q * y) := rfl

/-- The natural surjection `A ⧸ (q ^ (c + 1)) → A ⧸ (q)`. -/
noncomputable def projQMap :
    (A ⧸ (Ideal.span {q ^ (c + 1)} : Ideal A)) →ₗ[A] (A ⧸ (Ideal.span {q} : Ideal A)) :=
  Submodule.mapQ _ _ LinearMap.id (by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine Ideal.mem_span_singleton'.2 ⟨y * q ^ c, ?_⟩
    ring)

@[simp]
theorem projQMap_mk (y : A) :
    projQMap q c (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (p := (Ideal.span {q} : Ideal A)) y := rfl

theorem projQMap_surjective : Surjective (projQMap q c) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H y => exact ⟨Submodule.Quotient.mk y, rfl⟩

variable {q}

theorem mulQMap_injective (hq : q ≠ 0) : Injective (mulQMap q c) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    rw [mulQMap_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hx
    rw [Submodule.Quotient.mk_eq_zero]
    refine Ideal.mem_span_singleton'.2 ⟨z, mul_left_cancel₀ hq ?_⟩
    rw [← hz]
    ring

theorem exact_mulQMap_projQMap : Exact (mulQMap q c) (projQMap q c) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    constructor
    · intro hy
      rw [projQMap_mk, Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      refine ⟨Submodule.Quotient.mk z, ?_⟩
      rw [mulQMap_mk]
      ring_nf
    · rintro ⟨x, hx⟩
      rw [← hx]
      induction x using Submodule.Quotient.induction_on with
      | H z =>
        rw [mulQMap_mk, projQMap_mk, Submodule.Quotient.mk_eq_zero]
        exact Ideal.mem_span_singleton'.2 ⟨z, mul_comm z q⟩

variable [IsNoetherianRing A]

theorem isTorsion_quotient_span_pow (hq : q ≠ 0) (c : ℕ) :
    Module.IsTorsion A (A ⧸ (Ideal.span {q ^ c} : Ideal A)) := by
  intro x
  refine ⟨⟨q ^ c, pow_mem (mem_nonZeroDivisors_of_ne_zero hq) c⟩, ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine Ideal.mem_span_singleton'.2 ⟨y, ?_⟩
    show y * q ^ c = q ^ c * y
    ring

/-- The characteristic ideal of `A ⧸ (q ^ c)` is `(q) ^ c`, for `q` a prime element of a
Noetherian domain generating a height one prime ideal. -/
theorem charIdeal_quotient_span_singleton_pow (hq : Prime q)
    (hqh : (Ideal.span {q} : Ideal A).height = 1) (c : ℕ) :
    Module.charIdeal A (A ⧸ (Ideal.span {q ^ c} : Ideal A)) = Ideal.span {q} ^ c := by
  induction c with
  | zero =>
    haveI : Subsingleton (A ⧸ (Ideal.span {q ^ 0} : Ideal A)) := by
      rw [pow_zero, Ideal.span_singleton_one]
      exact Ideal.Quotient.subsingleton_iff.2 rfl
    rw [Module.charIdeal_eq_one_of_subsingleton, pow_zero]
  | succ c ih =>
    haveI : (Ideal.span {q} : Ideal A).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).2 hq
    have hbase : Module.charIdeal A (A ⧸ (Ideal.span {q} : Ideal A)) = Ideal.span {q} := by
      have := Module.charIdeal_quotient_prime_eq_of_one_le_height
        (⟨Ideal.span {q}, inferInstance⟩ : PrimeSpectrum A) (le_of_eq hqh.symm)
      rwa [if_pos hqh] at this
    rw [(isTorsion_quotient_span_pow hq.ne_zero (c + 1)).charIdeal_eq_mul_of_exact
      (mulQMap q c) (projQMap q c) (mulQMap_injective c hq.ne_zero) (projQMap_surjective q c)
      (exact_mulQMap_projQMap c), ih, hbase, pow_succ]

/-- For a prime element `q` of a Noetherian domain, `char(A ⧸ (q ^ c)) = (q ^ c)`. -/
theorem charIdeal_quotient_span_pow_of_prime (hq : Prime q) (c : ℕ) :
    Module.charIdeal A (A ⧸ (Ideal.span {q ^ c} : Ideal A)) = Ideal.span {q ^ c} := by
  rw [charIdeal_quotient_span_singleton_pow hq
    (Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hq.ne_zero) hq.not_unit) c,
    Ideal.span_singleton_pow]

end

variable (A : Type*) [CommRing A] [IsNoetherianRing A]

/-- A finite product of torsion modules is torsion. -/
theorem IsTorsion.pi {ι : Type*} [Fintype ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] (hM : ∀ i, Module.IsTorsion A (M i)) :
    Module.IsTorsion A (∀ i, M i) := by
  classical
  intro x
  choose a ha using fun i ↦ hM i (x := x i)
  refine ⟨∏ i, a i, funext fun i ↦ ?_⟩
  have h : ((∏ j, a j : nonZeroDivisors A) : A) =
      (∏ j ∈ Finset.univ.erase i, (a j : A)) * (a i : A) := by
    rw [Submonoid.coe_finsetProd, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  show ((∏ j, a j : nonZeroDivisors A) : A) • x i = 0
  rw [h, mul_smul]
  have := ha i
  simp only [Submonoid.smul_def] at this
  rw [this, smul_zero]

/-- The characteristic ideal of a finite product of finitely generated torsion modules is the
product of the characteristic ideals. -/
theorem IsTorsion.charIdeal_pi : ∀ {ι : Type*} [Fintype ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module.Finite A (M i)], (∀ i, Module.IsTorsion A (M i)) →
    Module.charIdeal A (∀ i, M i) = ∏ i, Module.charIdeal A (M i) := by
  apply Fintype.induction_empty_option
  · intro α β _ e IH M _ _ _ hM
    let _ : Fintype α := .ofEquiv β e.symm
    rw [← (LinearEquiv.piCongrLeft A M e).charIdeal_eq, IH _ (fun i ↦ hM (e i)),
      e.prod_comp (Module.charIdeal A <| M ·)]
  · intro M _ _ _ _
    have : Subsingleton ((i : PEmpty) → M i) := ⟨fun _ _ ↦ funext fun i ↦ i.elim⟩
    rw [Module.charIdeal_eq_one_of_subsingleton]
    simp
  · intro ι _ IH M _ _ _ hM
    rw [(LinearEquiv.piOptionEquivProd A).charIdeal_eq,
      Module.IsTorsion.charIdeal_prod (hM none) (Module.IsTorsion.pi A _ fun i ↦ hM (some i)),
      IH _ (fun i ↦ hM (some i)), Fintype.prod_option]

end Module

namespace IwasawaAlgebra

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- **Blueprint node `Lambda-module-structure`**, characteristic ideal half: the characteristic
ideal of a finitely generated torsion `Λ`-module is generated by a nonzero element of `Λ`,
namely by `∏ g_i ^ e_i` for any decomposition provided by the structure theorem. -/
theorem exists_charIdeal_eq_span {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M]
    [Module.Finite ℤ_[p]⟦X⟧ M] (hM : Module.IsTorsion ℤ_[p]⟦X⟧ M) :
    ∃ a : ℤ_[p]⟦X⟧, a ≠ 0 ∧ Module.charIdeal ℤ_[p]⟦X⟧ M = Ideal.span {a} := by
  classical
  obtain ⟨ι, hι, g, e, hgprime, -, -, hpis⟩ := exists_isPseudoIsomorphic_pi hM
  refine ⟨∏ i, g i ^ e i, Finset.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ (hgprime i).ne_zero,
    ?_⟩
  rw [hpis.charIdeal_eq, Module.IsTorsion.charIdeal_pi ℤ_[p]⟦X⟧ _
      (fun i ↦ Module.isTorsion_quotient_span_pow (hgprime i).ne_zero (e i)),
    Finset.prod_congr rfl (fun i _ ↦ Module.charIdeal_quotient_span_pow_of_prime
      (hgprime i) (e i)),
    Ideal.prod_span_singleton]

end IwasawaAlgebra
