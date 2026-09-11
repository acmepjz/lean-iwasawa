/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.Algebra.Module.EulerChar
public import Iwasawalib.RingTheory.IwasawaAlgebra.FreeQuotientCard
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# The rank-Euler characteristic of a module

Let `A ⊆ R` be commutative rings, `g : R` and `M` an `R`-module. Writing
`M[g] = Submodule.torsionBy R M g` and `M/gM = QuotSMulTop g M` we set
`ρ_g(M) := rank_A (M/gM) - rank_A (M[g])`.

This file proves blueprint node `rank-euler-char` in this generality; the case of interest is
`A = ℤ_p`, `R = Λ = ℤ_p⟦X⟧` and `g` a distinguished polynomial.

## Main results

* `Module.Finite.quotSMulTop`, `Module.Finite.of_isTorsionBy`: `M/gM` and `M[g]` are finite
  `A`-modules as soon as `M` is a finite `R`-module and `R ⧸ (g)` is a finite `A`-module.
  This is blueprint node `rank-euler-char` (i).
* `Module.rho_eq_zero_of_finite`: **`rank-euler-char` (ii)**, `ρ_g` vanishes on finite modules.
* `Module.rho_eq_add_of_exact`: **`rank-euler-char` (iii)**, `ρ_g` is additive.
* `Module.rho_eq_of_finite_ker_of_finite_coker`: **`rank-euler-char` (iv)**, a map with finite
  kernel and cokernel preserves `rank_A (M/gM)`, `rank_A (M[g])` and hence `ρ_g`.

The six term exact sequence is the one produced in
`Iwasawalib/Algebra/Module/EulerChar.lean` by the snake lemma; here we take the alternating
sum of `A`-ranks along it instead of the alternating sum of `ord_p` of cardinalities.
-/

open Function Module
open scoped Pointwise

namespace Module

section Finiteness

variable (A R : Type*) [CommRing A] [CommRing R] [Algebra A R] (g : R)
  [Module.Finite A (R ⧸ Ideal.span {g})]

/-- **Blueprint node `rank-euler-char` (i)**, first half: if `M` is a finite `R`-module and
`R ⧸ (g)` is a finite `A`-module, then `M / gM` is a finite `A`-module. -/
theorem Finite.quotSMulTop (M : Type*) [AddCommGroup M] [Module A M] [Module R M]
    [IsScalarTower A R M] [Module.Finite R M] : Module.Finite A (QuotSMulTop g M) := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have hpi : Module.Finite A (QuotSMulTop g (Fin n → R)) := by
    have e : QuotSMulTop g (Fin n → R) ≃ₗ[R] (Fin n → R ⧸ Ideal.span {g}) :=
      (Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul g
        (⊤ : Submodule R (Fin n → R))).symm).trans
        ((Pi.basisFun R (Fin n)).quotientSmulTopEquivPi (Ideal.span {g}))
    exact Module.Finite.equiv (e.restrictScalars A).symm
  exact Module.Finite.of_surjective ((QuotSMulTop.map g f).restrictScalars A)
    (QuotSMulTop.map_surjective g hf)

/-- A finite `R`-module killed by `g` is a finite `A`-module. -/
theorem Finite.of_isTorsionBy (M : Type*) [AddCommGroup M] [Module A M] [Module R M]
    [IsScalarTower A R M] [Module.Finite R M] (hM : ∀ x : M, g • x = 0) :
    Module.Finite A M := by
  haveI := Finite.quotSMulTop A R g M
  have hbot : (g • (⊤ : Submodule R M)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x g ⊤).1 hx
    simp [hM y]
  exact Module.Finite.equiv
    (((Submodule.quotEquivOfEq _ _ hbot).trans (Submodule.quotEquivOfEqBot _
      rfl)).restrictScalars A)

/-- **Blueprint node `rank-euler-char` (i)**, second half: if `R` is Noetherian, `M` is a finite
`R`-module and `R ⧸ (g)` is a finite `A`-module, then `M[g]` is a finite `A`-module. -/
theorem Finite.torsionBy [IsNoetherianRing R] (M : Type*) [AddCommGroup M] [Module A M]
    [Module R M] [IsScalarTower A R M] [Module.Finite R M] :
    Module.Finite A (Submodule.torsionBy R M g) :=
  Finite.of_isTorsionBy A R g _ fun x ↦ Subtype.ext (by simp)

end Finiteness

section RankNullity

variable (A : Type*) [CommRing A] [IsDomain A] [Infinite A]

/-- A finite module over an infinite domain is a torsion module. -/
theorem isTorsion_of_finite (M : Type*) [AddCommGroup M] [Module A M] [Finite M] :
    Module.IsTorsion A M := by
  intro x
  have h : ¬ Injective (fun a : A ↦ a • x) := fun h ↦
    @not_finite A _ (_root_.Finite.of_injective _ h)
  simp only [Injective, not_forall] at h
  obtain ⟨a, b, hab, hne⟩ := h
  refine ⟨⟨a - b, mem_nonZeroDivisors_of_ne_zero (sub_ne_zero.2 hne)⟩, ?_⟩
  simpa [sub_smul, sub_eq_zero] using hab

/-- A finite module over an infinite domain has rank zero. -/
theorem finrank_eq_zero_of_finite (M : Type*) [AddCommGroup M] [Module A M]
    [Finite M] : Module.finrank A M = 0 :=
  (isTorsion_of_finite A M).finrank_eq_zero

variable {A}
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- The rank-nullity theorem in the form used below. -/
theorem finrank_range_add_finrank_ker (f : M →ₗ[A] N) [Module.Finite A M] :
    Module.finrank A (LinearMap.range f) + Module.finrank A (LinearMap.ker f) =
      Module.finrank A M := by
  rw [← (f.quotKerEquivRange).finrank_eq]
  exact (LinearMap.ker f).finrank_quotient_add_finrank

theorem finrank_range_of_injective {f : M →ₗ[A] N} (hf : Injective f) :
    Module.finrank A (LinearMap.range f) = Module.finrank A M :=
  ((LinearEquiv.ofInjective f hf).finrank_eq).symm

theorem finrank_range_of_surjective {f : M →ₗ[A] N} (hf : Surjective f) :
    Module.finrank A (LinearMap.range f) = Module.finrank A N := by
  rw [LinearMap.range_eq_top.2 hf]
  exact (Submodule.topEquiv).finrank_eq

/-- The ranks along a six term exact sequence, expressed through the ranks of the images. -/
theorem finrank_six_exact' {M₁ M₂ M₃ M₄ M₅ M₆ : Type*}
    [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₃] [Module A M₃]
    [AddCommGroup M₄] [Module A M₄] [AddCommGroup M₅] [Module A M₅] [AddCommGroup M₆] [Module A M₆]
    [Module.Finite A M₂] [Module.Finite A M₃] [Module.Finite A M₄] [Module.Finite A M₅]
    {f₁ : M₁ →ₗ[A] M₂} {f₂ : M₂ →ₗ[A] M₃} {f₃ : M₃ →ₗ[A] M₄} {f₄ : M₄ →ₗ[A] M₅}
    {f₅ : M₅ →ₗ[A] M₆}
    (h₁ : Injective f₁) (e₁ : Exact f₁ f₂) (e₂ : Exact f₂ f₃) (e₃ : Exact f₃ f₄)
    (e₄ : Exact f₄ f₅) (h₅ : Surjective f₅) :
    ∃ r₂ r₃ r₄ : ℕ,
      Module.finrank A M₂ = Module.finrank A M₁ + r₂ ∧
      Module.finrank A M₃ = r₂ + r₃ ∧
      Module.finrank A M₄ = r₃ + r₄ ∧
      Module.finrank A M₅ = r₄ + Module.finrank A M₆ := by
  refine ⟨Module.finrank A (LinearMap.range f₂), Module.finrank A (LinearMap.range f₃),
    Module.finrank A (LinearMap.range f₄), ?_, ?_, ?_, ?_⟩
  · have c2 := finrank_range_add_finrank_ker f₂
    rw [e₁.linearMap_ker_eq, finrank_range_of_injective h₁] at c2
    omega
  · have c3 := finrank_range_add_finrank_ker f₃
    rw [e₂.linearMap_ker_eq] at c3
    omega
  · have c4 := finrank_range_add_finrank_ker f₄
    rw [e₃.linearMap_ker_eq] at c4
    omega
  · have c5 := finrank_range_add_finrank_ker f₅
    rw [e₄.linearMap_ker_eq, finrank_range_of_surjective h₅] at c5
    omega

/-- The alternating sum of the ranks along a six term exact sequence vanishes. -/
theorem finrank_six_exact {M₁ M₂ M₃ M₄ M₅ M₆ : Type*}
    [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₃] [Module A M₃]
    [AddCommGroup M₄] [Module A M₄] [AddCommGroup M₅] [Module A M₅] [AddCommGroup M₆] [Module A M₆]
    [Module.Finite A M₂] [Module.Finite A M₃] [Module.Finite A M₄] [Module.Finite A M₅]
    {f₁ : M₁ →ₗ[A] M₂} {f₂ : M₂ →ₗ[A] M₃} {f₃ : M₃ →ₗ[A] M₄} {f₄ : M₄ →ₗ[A] M₅}
    {f₅ : M₅ →ₗ[A] M₆}
    (h₁ : Injective f₁) (e₁ : Exact f₁ f₂) (e₂ : Exact f₂ f₃) (e₃ : Exact f₃ f₄)
    (e₄ : Exact f₄ f₅) (h₅ : Surjective f₅) :
    Module.finrank A M₁ + Module.finrank A M₃ + Module.finrank A M₅ =
      Module.finrank A M₂ + Module.finrank A M₄ + Module.finrank A M₆ := by
  obtain ⟨r₂, r₃, r₄, h2, h3, h4, h5⟩ := finrank_six_exact' h₁ e₁ e₂ e₃ e₄ h₅
  omega

end RankNullity

section Rho

variable (A : Type*) [CommRing A] [IsDomain A] [Infinite A]
variable {R : Type*} [CommRing R] [Algebra A R] (g : R)

/-- **Blueprint node `rank-euler-char` (i)**: the `g`-rank-Euler characteristic
`ρ_g(M) = rank_A (M/gM) - rank_A (M[g])` of an `R`-module `M`, where `A` is a base ring
of `R`. -/
noncomputable def rho (M : Type*) [AddCommGroup M] [Module A M] [Module R M]
    [IsScalarTower A R M] : ℤ :=
  (Module.finrank A (QuotSMulTop g M) : ℤ) -
    (Module.finrank A (Submodule.torsionBy R M g) : ℤ)

variable {A g}
variable {M N P : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M]
  [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower A R N]
  [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower A R P]

/-- **Blueprint node `rank-euler-char` (ii)**: the rank-Euler characteristic of a finite module
vanishes; so do both of its terms. -/
theorem rho_eq_zero_of_finite [Finite M] : rho A g M = 0 := by
  have h1 : Module.finrank A (QuotSMulTop g M) = 0 := finrank_eq_zero_of_finite A _
  have h2 : Module.finrank A (Submodule.torsionBy R M g) = 0 := finrank_eq_zero_of_finite A _
  rw [rho, h1, h2, sub_self]

/-- **Blueprint node `rank-euler-char` (iii)**: `ρ_g` is additive in short exact sequences. -/
theorem rho_eq_add_of_exact (f : M →ₗ[R] N) (h : N →ₗ[R] P) (hfh : Exact f h)
    (hf : Injective f) (hh : Surjective h)
    [Module.Finite A (Submodule.torsionBy R N g)] [Module.Finite A (QuotSMulTop g M)]
    [Module.Finite A (Submodule.torsionBy R P g)] [Module.Finite A (QuotSMulTop g N)] :
    rho A g N = rho A g M + rho A g P := by
  have key := finrank_six_exact (A := A)
    (f₁ := (torsionByMap g f).restrictScalars A)
    (f₂ := (torsionByMap g h).restrictScalars A)
    (f₃ := (delta g f h hfh hf hh).restrictScalars A)
    (f₄ := (QuotSMulTop.map g f).restrictScalars A)
    (f₅ := (QuotSMulTop.map g h).restrictScalars A)
    (torsionByMap_injective g hf) (torsionByMap_exact g hfh hf)
    (exact_torsionByMap_delta g f h hfh hf hh) (exact_delta_quotSMulTopMap g f h hfh hf hh)
    (QuotSMulTop.map_exact g hfh hh) (QuotSMulTop.map_surjective g hh)
  simp only [rho]
  omega

section SixTerm

variable (f : M →ₗ[R] N) (h : N →ₗ[R] P) (hfh : Exact f h) (hf : Injective f) (hh : Surjective h)
variable [Module.Finite A (Submodule.torsionBy R N g)] [Module.Finite A (QuotSMulTop g M)]
  [Module.Finite A (Submodule.torsionBy R P g)] [Module.Finite A (QuotSMulTop g N)]

include hfh hf hh

/-- The six ranks along the snake sequence of `0 → M → N → P → 0`. -/
theorem finrank_snake :
    ∃ r₂ r₃ r₄ : ℕ,
      Module.finrank A (Submodule.torsionBy R N g) =
          Module.finrank A (Submodule.torsionBy R M g) + r₂ ∧
      Module.finrank A (Submodule.torsionBy R P g) = r₂ + r₃ ∧
      Module.finrank A (QuotSMulTop g M) = r₃ + r₄ ∧
      Module.finrank A (QuotSMulTop g N) = r₄ + Module.finrank A (QuotSMulTop g P) :=
  finrank_six_exact' (A := A)
    (f₁ := (torsionByMap g f).restrictScalars A)
    (f₂ := (torsionByMap g h).restrictScalars A)
    (f₃ := (delta g f h hfh hf hh).restrictScalars A)
    (f₄ := (QuotSMulTop.map g f).restrictScalars A)
    (f₅ := (QuotSMulTop.map g h).restrictScalars A)
    (torsionByMap_injective g hf) (torsionByMap_exact g hfh hf)
    (exact_torsionByMap_delta g f h hfh hf hh) (exact_delta_quotSMulTopMap g f h hfh hf hh)
    (QuotSMulTop.map_exact g hfh hh) (QuotSMulTop.map_surjective g hh)

variable [Module.Finite A (Submodule.torsionBy R M g)] [Module.Finite A (QuotSMulTop g P)]

/-- If the left term of a short exact sequence is finite, the two others have the same
`g`-torsion rank. -/
theorem finrank_torsionBy_eq_of_finite_left [Finite M] :
    Module.finrank A (Submodule.torsionBy R N g) =
      Module.finrank A (Submodule.torsionBy R P g) := by
  obtain ⟨r₂, r₃, r₄, h2, h3, h4, h5⟩ := finrank_snake (A := A) (g := g) f h hfh hf hh
  rw [finrank_eq_zero_of_finite A (Submodule.torsionBy R M g)] at h2
  rw [finrank_eq_zero_of_finite A (QuotSMulTop g M)] at h4
  omega

/-- If the left term of a short exact sequence is finite, the two others have the same
rank modulo `g`. -/
theorem finrank_quotSMulTop_eq_of_finite_left [Finite M] :
    Module.finrank A (QuotSMulTop g N) = Module.finrank A (QuotSMulTop g P) := by
  obtain ⟨r₂, r₃, r₄, h2, h3, h4, h5⟩ := finrank_snake (A := A) (g := g) f h hfh hf hh
  rw [finrank_eq_zero_of_finite A (QuotSMulTop g M)] at h4
  omega

/-- If the right term of a short exact sequence is finite, the two others have the same
`g`-torsion rank. -/
theorem finrank_torsionBy_eq_of_finite_right [Finite P] :
    Module.finrank A (Submodule.torsionBy R M g) =
      Module.finrank A (Submodule.torsionBy R N g) := by
  obtain ⟨r₂, r₃, r₄, h2, h3, h4, h5⟩ := finrank_snake (A := A) (g := g) f h hfh hf hh
  rw [finrank_eq_zero_of_finite A (Submodule.torsionBy R P g)] at h3
  omega

/-- If the right term of a short exact sequence is finite, the two others have the same
rank modulo `g`. -/
theorem finrank_quotSMulTop_eq_of_finite_right [Finite P] :
    Module.finrank A (QuotSMulTop g M) = Module.finrank A (QuotSMulTop g N) := by
  obtain ⟨r₂, r₃, r₄, h2, h3, h4, h5⟩ := finrank_snake (A := A) (g := g) f h hfh hf hh
  rw [finrank_eq_zero_of_finite A (Submodule.torsionBy R P g)] at h3
  rw [finrank_eq_zero_of_finite A (QuotSMulTop g P)] at h5
  omega

end SixTerm

end Rho

section KerCoker

variable (A : Type*) [CommRing A] [IsDomain A] [Infinite A]
variable {R : Type*} [CommRing R] [Algebra A R] [IsNoetherianRing R] (g : R)
  [Module.Finite A (R ⧸ Ideal.span {g})]
variable {M N : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M]
  [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower A R N]

theorem rho_range_eq (φ : M →ₗ[R] N) [Module.Finite R N] [Finite (N ⧸ LinearMap.range φ)] :
    rho A g (LinearMap.range φ) = rho A g N := by
  haveI := Finite.torsionBy A R g N
  haveI := Finite.quotSMulTop A R g N
  haveI := Finite.torsionBy A R g (N ⧸ LinearMap.range φ)
  haveI := Finite.quotSMulTop A R g (N ⧸ LinearMap.range φ)
  haveI := Finite.quotSMulTop A R g (LinearMap.range φ)
  have h := rho_eq_add_of_exact (A := A) (g := g) (LinearMap.range φ).subtype
    (LinearMap.range φ).mkQ (LinearMap.exact_subtype_mkQ _) (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _)
  rw [rho_eq_zero_of_finite (A := A) (g := g) (M := N ⧸ LinearMap.range φ), add_zero] at h
  exact h.symm

/-- **Blueprint node `rank-euler-char` (iv)**: a homomorphism of finite `R`-modules with finite
kernel and finite cokernel preserves the rank-Euler characteristic. -/
theorem rho_eq_of_finite_ker_of_finite_coker (φ : M →ₗ[R] N) [Module.Finite R M]
    [Module.Finite R N] [Finite (LinearMap.ker φ)] [Finite (N ⧸ LinearMap.range φ)] :
    rho A g M = rho A g N := by
  haveI := Finite.torsionBy A R g M
  haveI := Finite.quotSMulTop A R g M
  haveI := Finite.torsionBy A R g (LinearMap.range φ)
  haveI := Finite.quotSMulTop A R g (LinearMap.range φ)
  haveI := Finite.torsionBy A R g (LinearMap.ker φ)
  haveI := Finite.quotSMulTop A R g (LinearMap.ker φ)
  have h := rho_eq_add_of_exact (A := A) (g := g) (LinearMap.ker φ).subtype φ.rangeRestrict
    (exact_subtype_rangeRestrict φ) (Submodule.subtype_injective _) φ.surjective_rangeRestrict
  rw [rho_eq_zero_of_finite (A := A) (g := g) (M := LinearMap.ker φ), zero_add,
    rho_range_eq A g φ] at h
  exact h

/-- **Blueprint node `rank-euler-char` (iv)**, first half: a homomorphism of finite
`R`-modules with finite kernel and cokernel preserves `rank_A (M[g])`. -/
theorem finrank_torsionBy_eq_of_finite_ker_of_finite_coker (φ : M →ₗ[R] N) [Module.Finite R M]
    [Module.Finite R N] [Finite (LinearMap.ker φ)] [Finite (N ⧸ LinearMap.range φ)] :
    Module.finrank A (Submodule.torsionBy R M g) =
      Module.finrank A (Submodule.torsionBy R N g) := by
  haveI := Finite.torsionBy A R g M
  haveI := Finite.quotSMulTop A R g M
  haveI := Finite.torsionBy A R g N
  haveI := Finite.quotSMulTop A R g N
  haveI := Finite.torsionBy A R g (LinearMap.range φ)
  haveI := Finite.quotSMulTop A R g (LinearMap.range φ)
  haveI := Finite.torsionBy A R g (LinearMap.ker φ)
  haveI := Finite.quotSMulTop A R g (LinearMap.ker φ)
  haveI := Finite.torsionBy A R g (N ⧸ LinearMap.range φ)
  haveI := Finite.quotSMulTop A R g (N ⧸ LinearMap.range φ)
  rw [finrank_torsionBy_eq_of_finite_left (A := A) (g := g) (LinearMap.ker φ).subtype
      φ.rangeRestrict (exact_subtype_rangeRestrict φ) (Submodule.subtype_injective _)
      φ.surjective_rangeRestrict,
    finrank_torsionBy_eq_of_finite_right (A := A) (g := g) (LinearMap.range φ).subtype
      (LinearMap.range φ).mkQ (LinearMap.exact_subtype_mkQ _) (Submodule.subtype_injective _)
      (Submodule.mkQ_surjective _)]

/-- **Blueprint node `rank-euler-char` (iv)**, second half: a homomorphism of finite
`R`-modules with finite kernel and cokernel preserves `rank_A (M/gM)`. -/
theorem finrank_quotSMulTop_eq_of_finite_ker_of_finite_coker (φ : M →ₗ[R] N) [Module.Finite R M]
    [Module.Finite R N] [Finite (LinearMap.ker φ)] [Finite (N ⧸ LinearMap.range φ)] :
    Module.finrank A (QuotSMulTop g M) = Module.finrank A (QuotSMulTop g N) := by
  haveI := Finite.torsionBy A R g M
  haveI := Finite.quotSMulTop A R g M
  haveI := Finite.torsionBy A R g N
  haveI := Finite.quotSMulTop A R g N
  haveI := Finite.torsionBy A R g (LinearMap.range φ)
  haveI := Finite.quotSMulTop A R g (LinearMap.range φ)
  haveI := Finite.torsionBy A R g (LinearMap.ker φ)
  haveI := Finite.quotSMulTop A R g (LinearMap.ker φ)
  haveI := Finite.torsionBy A R g (N ⧸ LinearMap.range φ)
  haveI := Finite.quotSMulTop A R g (N ⧸ LinearMap.range φ)
  rw [finrank_quotSMulTop_eq_of_finite_left (A := A) (g := g) (LinearMap.ker φ).subtype
      φ.rangeRestrict (exact_subtype_rangeRestrict φ) (Submodule.subtype_injective _)
      φ.surjective_rangeRestrict,
    finrank_quotSMulTop_eq_of_finite_right (A := A) (g := g) (LinearMap.range φ).subtype
      (LinearMap.range φ).mkQ (LinearMap.exact_subtype_mkQ _) (Submodule.subtype_injective _)
      (Submodule.mkQ_surjective _)]

end KerCoker


section Pi

variable {R : Type*} [CommRing R] (g : R) {ι : Type*} [Fintype ι] [DecidableEq ι]
  (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The `g`-torsion of a finite product is the product of the `g`-torsions. -/
def torsionByPiEquiv :
    Submodule.torsionBy R (∀ i, M i) g ≃ₗ[R] ∀ i, Submodule.torsionBy R (M i) g where
  toFun x i := ⟨x.1 i, by
    have := (Submodule.mem_torsionBy_iff g x.1).1 x.2
    rw [Submodule.mem_torsionBy_iff]
    exact congrFun this i⟩
  invFun y := ⟨fun i ↦ (y i).1, by
    rw [Submodule.mem_torsionBy_iff]
    funext i
    exact (Submodule.mem_torsionBy_iff g (y i).1).1 (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem smul_top_pi :
    (g • (⊤ : Submodule R (∀ i, M i))) =
      Submodule.pi Set.univ fun i ↦ (g • (⊤ : Submodule R (M i))) := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x g ⊤).1 hx
    exact Submodule.mem_pi.2 fun i _ ↦
      Submodule.smul_mem_pointwise_smul (y i) g ⊤ trivial
  · rw [Submodule.mem_pi] at hx
    have h : ∀ i, ∃ z, g • z = x i := fun i ↦ by
      obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists (x i) g ⊤).1
        (hx i (Set.mem_univ i))
      exact ⟨y, hy⟩
    choose z hz using h
    refine (Submodule.mem_smul_pointwise_iff_exists x g ⊤).2 ⟨z, trivial, ?_⟩
    funext i
    exact hz i

/-- Reduction mod `g` of a finite product is the product of the reductions. -/
noncomputable def quotSMulTopPiEquiv :
    QuotSMulTop g (∀ i, M i) ≃ₗ[R] ∀ i, QuotSMulTop g (M i) :=
  (Submodule.quotEquivOfEq _ _ (smul_top_pi g M)).trans (Submodule.quotientPi _)

end Pi

section FreeSubmodule

/-- **Blueprint node `free-submodule-full-rank`**: a finitely generated module `X` over a
commutative domain `A` contains a free submodule `L` of the same rank, with torsion quotient. -/
theorem exists_free_submodule_isTorsion_quotient (A X : Type*) [CommRing A] [IsDomain A]
    [AddCommGroup X] [Module A X] [Module.Finite A X] :
    ∃ L : Submodule A X, Module.Free A L ∧ Module.Finite A L ∧
      Module.finrank A L = Module.finrank A X ∧ Module.IsTorsion A (X ⧸ L) := by
  classical
  obtain ⟨s, hcard, hli⟩ := exists_set_linearIndependent A X
  have hrange : Set.range ((↑) : s → X) = s := Subtype.range_coe
  have hb : Module.Basis s A (Submodule.span A s) := by
    have := Module.Basis.span (R := A) (v := ((↑) : s → X)) hli
    rwa [hrange] at this
  have hrankX : Module.rank A X = (Module.finrank A X : Cardinal) :=
    (Module.finrank_eq_rank A X).symm
  have hsfin : Cardinal.mk s = (Module.finrank A X : Cardinal) := by rw [hcard, hrankX]
  haveI : Fintype s := by
    have : Cardinal.mk s < Cardinal.aleph0 := by rw [hsfin]; exact Cardinal.natCast_lt_aleph0
    exact (Cardinal.lt_aleph0_iff_fintype.1 this).some
  haveI : Module.Finite A (Submodule.span A s) := Module.Finite.of_basis hb
  refine ⟨Submodule.span A s, Module.Free.of_basis hb, inferInstance, ?_, ?_⟩
  · have h := hb.mk_eq_rank''
    rw [hsfin] at h
    rw [← Module.finrank_eq_rank] at h
    exact_mod_cast h.symm
  · rw [← Module.rank_eq_zero_iff_isTorsion]
    have h := (Submodule.span A s).rank_quotient_add_rank
    have hL : Module.rank A (Submodule.span A s) = (Module.finrank A X : Cardinal) := by
      rw [← hb.mk_eq_rank'', hsfin]
    rw [hL, hrankX] at h
    exact Cardinal.eq_of_add_eq_add_right (b := (Module.finrank A X : Cardinal))
      (by rw [h, zero_add]) Cardinal.natCast_lt_aleph0

end FreeSubmodule

end Module
