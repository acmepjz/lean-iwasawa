/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# The `g`-Euler characteristic of a module

For a commutative ring `R`, an element `g : R` and an `R`-module `M`, write
`M[g] = Submodule.torsionBy R M g` and `M/gM = QuotSMulTop g M`. When both are finite we set
`χ_g(M) := ord_p #(M/gM) - ord_p #(M[g])`.

This file proves blueprint node `euler-char-lemma`:

* `Module.chi_eq_zero_of_finite`: `χ_g(M) = 0` for finite `M`;
* `Module.chi_eq_add_of_exact`: `χ_g(B) = χ_g(A) + χ_g(C)` for a short exact sequence
  `0 → A → B → C → 0`, together with the three "two out of three" finiteness statements
  `Module.finite_*_of_exact_*`;
* `Module.chi_eq_of_finite_ker_of_finite_coker`: `χ_g(M) = χ_g(N)` for a map `M → N` with
  finite kernel and cokernel.

The main ingredient is the snake lemma for modules
(`Mathlib/Algebra/Module/SnakeLemma.lean`), which yields the six term exact sequence
`0 → A[g] → B[g] → C[g] → A/gA → B/gB → C/gC → 0`.
-/

open Function

namespace Module

section CardLemmas

variable {R : Type*} [Ring R]

theorem card_eq_card_quotient_mul_card {M : Type*} [AddCommGroup M] [Module R M]
    (S : Submodule R M) : Nat.card M = Nat.card (M ⧸ S) * Nat.card S :=
  AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup S.toAddSubgroup

theorem card_eq_card_ker_mul_card_range {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) :
    Nat.card M = Nat.card (LinearMap.ker φ) * Nat.card (LinearMap.range φ) := by
  rw [card_eq_card_quotient_mul_card (LinearMap.ker φ),
    Nat.card_congr φ.quotKerEquivRange.toEquiv, mul_comm]

instance finite_quotient {M : Type*} [AddCommGroup M] [Module R M] [Finite M]
    (S : Submodule R M) : Finite (M ⧸ S) := Quotient.finite _

instance finite_range {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) [Finite M] :
    Finite (LinearMap.range φ) :=
  _root_.Finite.of_surjective (fun m ↦ (⟨φ m, ⟨m, rfl⟩⟩ : LinearMap.range φ))
    (by rintro ⟨_, m, rfl⟩; exact ⟨m, rfl⟩)

/-- The middle term of an exact sequence of modules with finite outer terms is finite. -/
theorem finite_of_exact {W X Y : Type*} [AddCommGroup W] [Module R W]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (u : W →ₗ[R] X) (v : X →ₗ[R] Y) (huv : Exact u v) [Finite W] [Finite Y] : Finite X := by
  have h := card_eq_card_ker_mul_card_range v
  rw [huv.linearMap_ker_eq] at h
  have h1 : Nat.card (LinearMap.range u) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  have h2 : Nat.card (LinearMap.range v) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  have : Nat.card X ≠ 0 := by rw [h]; exact mul_ne_zero h1 h2
  exact (Nat.card_ne_zero.1 this).2

/-- The cardinality identity coming from a six term exact sequence. -/
theorem card_six_exact {M₁ M₂ M₃ M₄ M₅ M₆ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup M₄] [Module R M₄] [AddCommGroup M₅] [Module R M₅] [AddCommGroup M₆] [Module R M₆]
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {f₃ : M₃ →ₗ[R] M₄} {f₄ : M₄ →ₗ[R] M₅}
    {f₅ : M₅ →ₗ[R] M₆}
    (h₁ : Injective f₁) (e₁ : Exact f₁ f₂) (e₂ : Exact f₂ f₃) (e₃ : Exact f₃ f₄)
    (e₄ : Exact f₄ f₅) (h₅ : Surjective f₅) :
    Nat.card M₁ * Nat.card M₃ * Nat.card M₅ = Nat.card M₂ * Nat.card M₄ * Nat.card M₆ := by
  have hr1 : Nat.card (LinearMap.range f₁) = Nat.card M₁ :=
    (Nat.card_congr (LinearEquiv.ofInjective f₁ h₁).toEquiv).symm
  have hr5 : Nat.card (LinearMap.range f₅) = Nat.card M₆ := by
    rw [LinearMap.range_eq_top.2 h₅]
    exact Nat.card_congr (Submodule.topEquiv).toEquiv
  have c2 := card_eq_card_ker_mul_card_range f₂
  have c3 := card_eq_card_ker_mul_card_range f₃
  have c4 := card_eq_card_ker_mul_card_range f₄
  have c5 := card_eq_card_ker_mul_card_range f₅
  rw [e₁.linearMap_ker_eq, hr1] at c2
  rw [e₂.linearMap_ker_eq] at c3
  rw [e₃.linearMap_ker_eq] at c4
  rw [e₄.linearMap_ker_eq, hr5] at c5
  rw [c2, c3, c4, c5]
  ring

end CardLemmas

section Snake

variable {R : Type*} [CommRing R] (g : R)

section
variable (M : Type*) [AddCommGroup M] [Module R M]

open Pointwise in
theorem range_distribSMul_toLinearMap :
    LinearMap.range (DistribSMul.toLinearMap R M g) = g • (⊤ : Submodule R M) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact Submodule.smul_mem_pointwise_smul x g ⊤ trivial
  · intro x hx
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x g ⊤).1 hx
    exact ⟨y, rfl⟩

open Pointwise in
theorem exact_distribSMul_mkQ :
    Exact (DistribSMul.toLinearMap R M g) (Submodule.mkQ (g • (⊤ : Submodule R M))) := by
  rw [LinearMap.exact_iff, Submodule.ker_mkQ, range_distribSMul_toLinearMap]

theorem exact_subtype_distribSMul :
    Exact (Submodule.torsionBy R M g).subtype (DistribSMul.toLinearMap R M g) := by
  rw [LinearMap.exact_iff, Submodule.range_subtype]
  rfl

end

variable {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- The restriction of `f : M →ₗ[R] N` to the `g`-torsion submodules. -/
def torsionByMap (f : M →ₗ[R] N) :
    Submodule.torsionBy R M g →ₗ[R] Submodule.torsionBy R N g :=
  f.restrict (fun x hx ↦ by
    rw [Submodule.mem_torsionBy_iff] at hx ⊢
    rw [← map_smul, hx, map_zero])

@[simp]
theorem torsionByMap_apply (f : M →ₗ[R] N) (x : Submodule.torsionBy R M g) :
    (torsionByMap g f x : N) = f x := rfl

theorem torsionByMap_injective {f : M →ₗ[R] N} (hf : Injective f) :
    Injective (torsionByMap g f) := fun x y h ↦ by
  apply Subtype.ext
  exact hf (by simpa using congr(($h : N)))

theorem torsionByMap_exact {f : M →ₗ[R] N} {h : N →ₗ[R] P} (hfh : Exact f h)
    (hf : Injective f) : Exact (torsionByMap g f) (torsionByMap g h) := by
  intro x
  constructor
  · intro hx
    have hx' : h (x : N) = 0 := by simpa using congr(($hx : P))
    obtain ⟨a, ha⟩ := hfh _ |>.1 hx'
    have hga : g • a = 0 := hf (by
      rw [map_smul, ha, map_zero, ← Submodule.mem_torsionBy_iff]
      exact x.2)
    exact ⟨⟨a, Submodule.mem_torsionBy_iff .. |>.2 hga⟩, Subtype.ext ha⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    show h (f (y : M)) = 0
    exact hfh.apply_apply_eq_zero _

theorem comm_square (f : M →ₗ[R] N) :
    f.comp (DistribSMul.toLinearMap R M g) = (DistribSMul.toLinearMap R N g).comp f :=
  LinearMap.ext fun x ↦ by simp

/-- The connecting map `C[g] → A/gA` of the snake lemma applied to multiplication by `g` on a
short exact sequence `0 → A → B → C → 0`. -/
noncomputable def delta (f : M →ₗ[R] N) (h : N →ₗ[R] P) (hfh : Exact f h)
    (hf : Injective f) (hh : Surjective h) :
    Submodule.torsionBy R P g →ₗ[R] QuotSMulTop g M :=
  SnakeLemma.δ' (DistribSMul.toLinearMap R M g) (DistribSMul.toLinearMap R N g)
    (DistribSMul.toLinearMap R P g) f h hfh f h hfh (comm_square g f) (comm_square g h)
    (Submodule.torsionBy R P g).subtype (exact_subtype_distribSMul g P)
    (Submodule.mkQ _) (exact_distribSMul_mkQ g M) hh hf

theorem exact_torsionByMap_delta (f : M →ₗ[R] N) (h : N →ₗ[R] P) (hfh : Exact f h)
    (hf : Injective f) (hh : Surjective h) :
    Exact (torsionByMap g h) (delta g f h hfh hf hh) :=
  SnakeLemma.exact_δ'_right (DistribSMul.toLinearMap R M g) (DistribSMul.toLinearMap R N g)
    (DistribSMul.toLinearMap R P g) f h hfh f h hfh (comm_square g f) (comm_square g h)
    (Submodule.torsionBy R N g).subtype (exact_subtype_distribSMul g N)
    (Submodule.torsionBy R P g).subtype (exact_subtype_distribSMul g P)
    (Submodule.mkQ _) (exact_distribSMul_mkQ g M) hh hf
    (torsionByMap g h) rfl Subtype.val_injective

theorem exact_delta_quotSMulTopMap (f : M →ₗ[R] N) (h : N →ₗ[R] P) (hfh : Exact f h)
    (hf : Injective f) (hh : Surjective h) :
    Exact (delta g f h hfh hf hh) (QuotSMulTop.map g f) :=
  SnakeLemma.exact_δ'_left (DistribSMul.toLinearMap R M g) (DistribSMul.toLinearMap R N g)
    (DistribSMul.toLinearMap R P g) f h hfh f h hfh (comm_square g f) (comm_square g h)
    (Submodule.torsionBy R P g).subtype (exact_subtype_distribSMul g P)
    (Submodule.mkQ _) (exact_distribSMul_mkQ g M)
    (Submodule.mkQ _) (exact_distribSMul_mkQ g N) hh hf
    (QuotSMulTop.map g f) (QuotSMulTop.map_comp_mkQ g f) (Submodule.mkQ_surjective _)

/-- **The six term exact sequence** of blueprint node `euler-char-lemma` (ii), in cardinality
form: `#A[g] * #C[g] * #(B/gB) = #B[g] * #(A/gA) * #(C/gC)`. -/
theorem card_torsionBy_mul_card_quotSMulTop (f : M →ₗ[R] N) (h : N →ₗ[R] P) (hfh : Exact f h)
    (hf : Injective f) (hh : Surjective h) :
    Nat.card (Submodule.torsionBy R M g) * Nat.card (Submodule.torsionBy R P g) *
        Nat.card (QuotSMulTop g N) =
      Nat.card (Submodule.torsionBy R N g) * Nat.card (QuotSMulTop g M) *
        Nat.card (QuotSMulTop g P) :=
  card_six_exact (torsionByMap_injective g hf) (torsionByMap_exact g hfh hf)
    (exact_torsionByMap_delta g f h hfh hf hh) (exact_delta_quotSMulTopMap g f h hfh hf hh)
    (QuotSMulTop.map_exact g hfh hh) (QuotSMulTop.map_surjective g hh)

end Snake

section Chi

variable {R : Type*} [CommRing R] (p : ℕ) (g : R)

/-- The `g`-Euler characteristic `χ_g(M) = ord_p #(M/gM) - ord_p #(M[g])` of an `R`-module `M`
(blueprint node `euler-char-lemma`). It is only meaningful when `M[g]` and `M/gM` are
finite. -/
noncomputable def chi (M : Type*) [AddCommGroup M] [Module R M] : ℤ :=
  ((Nat.card (QuotSMulTop g M)).factorization p : ℤ) -
    ((Nat.card (Submodule.torsionBy R M g)).factorization p : ℤ)

theorem factorization_mul_three {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (a * b * c).factorization p = a.factorization p + b.factorization p + c.factorization p := by
  rw [Nat.factorization_mul (mul_ne_zero ha hb) hc, Nat.factorization_mul ha hb]
  simp

open Pointwise in
/-- **Blueprint node `euler-char-lemma` (i)**: the `g`-Euler characteristic of a finite module
vanishes. -/
theorem chi_eq_zero_of_finite (M : Type*) [AddCommGroup M] [Module R M] [Finite M] :
    chi p g M = 0 := by
  have h1 : Nat.card M =
      Nat.card (Submodule.torsionBy R M g) * Nat.card ↥(g • (⊤ : Submodule R M)) := by
    rw [← range_distribSMul_toLinearMap]
    exact card_eq_card_ker_mul_card_range _
  have h2 : Nat.card M = Nat.card (QuotSMulTop g M) * Nat.card ↥(g • (⊤ : Submodule R M)) :=
    card_eq_card_quotient_mul_card _
  have hne : Nat.card ↥(g • (⊤ : Submodule R M)) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  have : Nat.card (Submodule.torsionBy R M g) = Nat.card (QuotSMulTop g M) :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (h1.symm.trans h2)
  rw [chi, this, sub_self]

variable {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

section Exact

variable (f : M →ₗ[R] N) (h : N →ₗ[R] P) (hfh : Exact f h) (hf : Injective f)
  (hh : Surjective h)

include hfh hf hh

/-- Two out of three, first case: if the data of the two outer terms is finite, so is the
`g`-torsion of the middle term. -/
theorem finite_torsionBy_middle [Finite (Submodule.torsionBy R M g)]
    [Finite (Submodule.torsionBy R P g)] : Finite (Submodule.torsionBy R N g) :=
  finite_of_exact _ _ (torsionByMap_exact g hfh hf)

/-- Two out of three, first case: if the data of the two outer terms is finite, so is
`N/gN`. -/
theorem finite_quotSMulTop_middle [Finite (QuotSMulTop g M)] [Finite (QuotSMulTop g P)] :
    Finite (QuotSMulTop g N) :=
  finite_of_exact _ _ (QuotSMulTop.map_exact g hfh hh)

/-- Two out of three, second case: the `g`-torsion of the left term is finite as soon as that
of the middle term is. -/
theorem finite_torsionBy_left [Finite (Submodule.torsionBy R N g)] :
    Finite (Submodule.torsionBy R M g) :=
  _root_.Finite.of_injective _ (torsionByMap_injective g hf)

/-- Two out of three, second case: if the data of `B` and `C` is finite, so is `A/gA`. -/
theorem finite_quotSMulTop_left [Finite (Submodule.torsionBy R P g)] [Finite (QuotSMulTop g N)] :
    Finite (QuotSMulTop g M) :=
  finite_of_exact _ _ (exact_delta_quotSMulTopMap g f h hfh hf hh)

/-- Two out of three, third case: if the data of `A` and `B` is finite, so is `C[g]`. -/
theorem finite_torsionBy_right [Finite (Submodule.torsionBy R N g)] [Finite (QuotSMulTop g M)] :
    Finite (Submodule.torsionBy R P g) :=
  finite_of_exact _ _ (exact_torsionByMap_delta g f h hfh hf hh)

/-- Two out of three, third case: `C/gC` is finite as soon as `B/gB` is. -/
theorem finite_quotSMulTop_right [Finite (QuotSMulTop g N)] : Finite (QuotSMulTop g P) :=
  _root_.Finite.of_surjective _ (QuotSMulTop.map_surjective g hh)

/-- **Blueprint node `euler-char-lemma` (ii)**: the `g`-Euler characteristic is additive in
short exact sequences. -/
theorem chi_eq_add_of_exact [Finite (Submodule.torsionBy R M g)] [Finite (QuotSMulTop g M)]
    [Finite (Submodule.torsionBy R N g)] [Finite (QuotSMulTop g N)]
    [Finite (Submodule.torsionBy R P g)] [Finite (QuotSMulTop g P)] :
    chi p g N = chi p g M + chi p g P := by
  have key := card_torsionBy_mul_card_quotSMulTop g f h hfh hf hh
  have n1 : Nat.card (Submodule.torsionBy R M g) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  have n2 : Nat.card (Submodule.torsionBy R N g) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  have n3 : Nat.card (Submodule.torsionBy R P g) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  have m1 : Nat.card (QuotSMulTop g M) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  have m2 : Nat.card (QuotSMulTop g N) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  have m3 : Nat.card (QuotSMulTop g P) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  have hfac := congrArg (fun n : ℕ ↦ n.factorization p) key
  simp only [factorization_mul_three p n1 n3 m2, factorization_mul_three p n2 m1 m3] at hfac
  simp only [chi]
  omega

end Exact

section KerCoker

variable (φ : M →ₗ[R] N)

theorem exact_subtype_rangeRestrict :
    Exact (LinearMap.ker φ).subtype φ.rangeRestrict := by
  rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]

variable [Finite (LinearMap.ker φ)] [Finite (N ⧸ LinearMap.range φ)]
  [Finite (Submodule.torsionBy R N g)] [Finite (QuotSMulTop g N)]

include φ

theorem finite_torsionBy_range : Finite (Submodule.torsionBy R (LinearMap.range φ) g) :=
  finite_torsionBy_left g (LinearMap.range φ).subtype (LinearMap.range φ).mkQ
    (LinearMap.exact_subtype_mkQ _) (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)

theorem finite_quotSMulTop_range : Finite (QuotSMulTop g (LinearMap.range φ)) :=
  finite_quotSMulTop_left g (LinearMap.range φ).subtype (LinearMap.range φ).mkQ
    (LinearMap.exact_subtype_mkQ _) (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)

theorem chi_range_eq : chi p g (LinearMap.range φ) = chi p g N := by
  haveI := finite_torsionBy_range g φ
  haveI := finite_quotSMulTop_range g φ
  have := chi_eq_add_of_exact p g (LinearMap.range φ).subtype (LinearMap.range φ).mkQ
    (LinearMap.exact_subtype_mkQ _) (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
  rw [chi_eq_zero_of_finite p g (N ⧸ LinearMap.range φ), add_zero] at this
  exact this.symm

/-- **Blueprint node `euler-char-lemma` (iii)**: if `φ : M → N` has finite kernel and finite
cokernel and `N[g]`, `N/gN` are finite, then `M[g]` is finite. -/
theorem finite_torsionBy_of_finite_ker_of_finite_coker :
    Finite (Submodule.torsionBy R M g) := by
  haveI := finite_torsionBy_range g φ
  exact finite_torsionBy_middle g (LinearMap.ker φ).subtype φ.rangeRestrict
    (exact_subtype_rangeRestrict φ) (Submodule.subtype_injective _)
    φ.surjective_rangeRestrict

/-- **Blueprint node `euler-char-lemma` (iii)**: if `φ : M → N` has finite kernel and finite
cokernel and `N[g]`, `N/gN` are finite, then `M/gM` is finite. -/
theorem finite_quotSMulTop_of_finite_ker_of_finite_coker : Finite (QuotSMulTop g M) := by
  haveI := finite_quotSMulTop_range g φ
  exact finite_quotSMulTop_middle g (LinearMap.ker φ).subtype φ.rangeRestrict
    (exact_subtype_rangeRestrict φ) (Submodule.subtype_injective _)
    φ.surjective_rangeRestrict

/-- **Blueprint node `euler-char-lemma` (iii)**: a map with finite kernel and cokernel
preserves the `g`-Euler characteristic. -/
theorem chi_eq_of_finite_ker_of_finite_coker : chi p g M = chi p g N := by
  haveI := finite_torsionBy_range g φ
  haveI := finite_quotSMulTop_range g φ
  haveI := finite_torsionBy_of_finite_ker_of_finite_coker g φ
  haveI := finite_quotSMulTop_of_finite_ker_of_finite_coker g φ
  have := chi_eq_add_of_exact p g (LinearMap.ker φ).subtype φ.rangeRestrict
    (exact_subtype_rangeRestrict φ) (Submodule.subtype_injective _)
    φ.surjective_rangeRestrict
  rw [chi_eq_zero_of_finite p g (LinearMap.ker φ), zero_add, chi_range_eq] at this
  exact this

end KerCoker

end Chi

end Module
