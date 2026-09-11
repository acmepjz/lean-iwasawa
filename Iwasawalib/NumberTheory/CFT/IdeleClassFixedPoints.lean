/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.CyclicTate
public import Iwasawalib.NumberTheory.CFT.HerbrandShapiro
public import Iwasawalib.GroupCohomology.IdeleShortExact
public import Iwasawalib.NumberTheory.CFT.AdeleFixedPoints

@[expose] public section

/-!
# `(C_L)^{Gal(L/K)} = C_K`, and what `Ĥ⁰(Gal(L/K), C_L)` literally is

For a finite Galois extension of number fields `L / K` this file proves that the natural map
`C_K → C_L` of idele class groups is **injective** with image exactly the `Gal(L/K)`-invariants
of `C_L`.

## Why this matters for the first inequality

The first fundamental inequality is classically stated as the norm-index bound

`[C_K : N_{L/K} C_L] ≤ [L : K]`.

What this library actually bounds is `Nat.card (CyclicTate.TateH0 Gal(L/K) (Additive C_L) σ)`,
the Tate group `Ĥ⁰(Gal(L/K), C_L) = ker(σ - 1) / N C_L`.  Those two are the same number only if
`ker(σ - 1) = (C_L)^{Gal(L/K)}` really is `C_K`.  That identification is not formal: the easy
inclusion `C_K ⊆ (C_L)^{Gal(L/K)}` is `NumberField.IdeleClassGroup.galIdeleClassAut_baseChange`,
but the reverse inclusion needs Hilbert 90 and the injectivity needs that `Kˣ = (Lˣ)^{Gal(L/K)}`.
Both are proved here, so `NumberField.IdeleClassGroup.mem_kerSub_iff_mem_range_baseChange`
records that the cohomological statements of `Iwasawalib/NumberTheory/CFT/FirstInequality.lean`
and `Iwasawalib/NumberTheory/CFT/BrauerHassePrinciple.lean` are statements about the honest norm
quotient `C_K / N_{L/K} C_L`.

## The proofs

Injectivity: if `u ∈ 𝕀_K` becomes principal in `𝕀_L`, say `u = (x)` with `x ∈ Lˣ`, then `(x)` is
`Gal(L/K)`-invariant because `u` is, so `σ x = x` for every `σ` by injectivity of the principal
embedding, so `x ∈ Kˣ` by `IsGalois.mem_bot_iff_fixed`, and `u` is principal already.

Surjectivity onto the invariants: if `c ∈ C_L` is invariant, lift it to `u ∈ 𝕀_L`.  Then
`σ ↦ f σ`, where `(f σ) = (σ • u) u⁻¹` in `Lˣ`, is a multiplicative `1`-cocycle, so Hilbert 90
(`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_faithful`) gives `β ∈ Lˣ` with
`f σ = σ • β / β`, and `u (β)⁻¹` is a `Gal(L/K)`-invariant idele representing `c`.  It lies in
`𝕀_K` by `NumberField.IdeleGroup.range_baseChange_eq_setOf_fixed`.

## Main statements

* `NumberField.IdeleClassGroup.baseChange_injective` : `C_K → C_L` is injective.
* `NumberField.IdeleClassGroup.mem_range_baseChange_of_fixed` : every `Gal(L/K)`-invariant idele
  class of `L` comes from `K`.
* `NumberField.IdeleClassGroup.range_baseChange_eq_setOf_fixed` : `(C_L)^{Gal(L/K)} = C_K`.
* `NumberField.IdeleClassGroup.baseChangeEquivRange` : the resulting isomorphism.
* `NumberField.IdeleClassGroup.mem_kerSub_iff_mem_range_baseChange` : for a generator `σ` of a
  cyclic `Gal(L/K)`, the numerator of `Ĥ⁰(Gal(L/K), C_L)` is the image of `C_K`.
-/

noncomputable section

open IsDedekindDomain

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.galIdeleMulDistribMulAction NumberField.galIdeleClassMulDistribMulAction

namespace NumberField.IdeleClassGroup

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **The map `C_K → C_L` is injective.**  An idele of `K` that becomes principal in `L` is
already principal in `K`, because a principal idele of `L` fixed by `Gal(L/K)` comes from an
element of `L` fixed by `Gal(L/K)`, i.e. from `K`. -/
theorem baseChange_injective : Function.Injective (baseChange K L) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨u, rfl⟩ := mk_surjective (𝓞 K) K c
  rw [baseChange_mk, mk_eq_one_iff] at hc
  obtain ⟨x, hx⟩ := hc
  have hfix : ∀ σ : L ≃ₐ[K] L, σ (x : L) = (x : L) := by
    intro σ
    have h1 : σ • IdeleGroup.principalEmbedding (𝓞 L) L x
        = IdeleGroup.principalEmbedding (𝓞 L) L x := by
      rw [hx]
      exact IdeleGroup.galIdeleAut_baseChange σ u
    rw [← principalEmbedding_smul] at h1
    have := IdeleGroup.principalEmbedding_injective (𝓞 L) L h1
    exact congrArg (fun y : Lˣ ↦ (y : L)) this
  obtain ⟨y, hy⟩ : (x : L) ∈ Set.range (algebraMap K L) := by
    rw [← IntermediateField.mem_bot]
    exact (IsGalois.mem_bot_iff_fixed (x : L)).2 hfix
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by simpa using hy.symm)
  set yu : Kˣ := Units.mk0 y hy0 with hyu
  have hmapy : Units.map (algebraMap K L) yu = x := Units.ext hy
  have : IdeleGroup.baseChange K L (IdeleGroup.principalEmbedding (𝓞 K) K yu)
      = IdeleGroup.baseChange K L u := by
    rw [IdeleGroup.baseChange_principalEmbedding, hmapy, hx]
  rw [mk_eq_one_iff]
  exact ⟨yu, IdeleGroup.baseChange_injective this⟩

/-- **Every `Gal(L/K)`-invariant idele class of `L` comes from `K`.**  This is Hilbert 90 applied
to the cocycle `σ ↦ (σ • u) u⁻¹` attached to any lift `u ∈ 𝕀_L` of the invariant class. -/
theorem mem_range_baseChange_of_fixed {c : IdeleClassGroup (𝓞 L) L}
    (hc : ∀ σ : L ≃ₐ[K] L, galIdeleClassAut K L σ c = c) :
    c ∈ Set.range (baseChange K L) := by
  obtain ⟨u, rfl⟩ := mk_surjective (𝓞 L) L c
  have hex : ∀ σ : L ≃ₐ[K] L, ∃ x : Lˣ,
      IdeleGroup.principalEmbedding (𝓞 L) L x = (σ • u) * u⁻¹ := by
    intro σ
    have h1 := hc σ
    rw [galIdeleClassAut_mk] at h1
    refine (mk_eq_one_iff (𝓞 L) L).1 ?_
    rw [map_mul, map_inv, show mk (𝓞 L) L (σ • u) = mk (𝓞 L) L (galIdeleAut K L σ u) from rfl,
      h1, mul_inv_cancel]
  choose f hf using hex
  have hcoc : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    refine IdeleGroup.principalEmbedding_injective (𝓞 L) L ?_
    rw [hf, map_mul, principalEmbedding_smul, hf, hf]
    rw [smul_mul', smul_inv', smul_smul]
    group
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_faithful
    (NumberField.galois_smul_injective K L) f hcoc
  set u' := u * (IdeleGroup.principalEmbedding (𝓞 L) L β)⁻¹ with hu'
  have hfix : ∀ σ : L ≃ₐ[K] L, σ • u' = u' := by
    intro σ
    have h2 : IdeleGroup.principalEmbedding (𝓞 L) L (σ • β / β) = (σ • u) * u⁻¹ := by
      have := congrArg (IdeleGroup.principalEmbedding (𝓞 L) L) (hβ σ)
      rw [hf] at this
      exact this
    rw [hu', smul_mul', smul_inv', ← principalEmbedding_smul]
    have h3 : σ • u = u * IdeleGroup.principalEmbedding (𝓞 L) L (σ • β / β) := by
      rw [h2, mul_comm (σ • u) u⁻¹]
      exact (mul_inv_cancel_left u (σ • u)).symm
    rw [h3, map_div]
    simp only [div_eq_mul_inv, mul_assoc]
    simp
  obtain ⟨v, hv⟩ : u' ∈ Set.range (IdeleGroup.baseChange K L) := by
    rw [IdeleGroup.range_baseChange_eq_setOf_fixed]
    intro σ
    have := hfix σ
    rw [show σ • u' = galIdeleAut K L σ u' from rfl, galIdeleAut_apply] at this
    exact congrArg (fun w : IdeleGroup (𝓞 L) L ↦ (w : AdeleRing (𝓞 L) L)) this
  refine ⟨mk (𝓞 K) K v, ?_⟩
  rw [baseChange_mk, hv, hu', map_mul, map_inv, mk_principalEmbedding, inv_one, mul_one]

/-- **`(C_L)^{Gal(L/K)} = C_K`.**  The `Gal(L/K)`-invariants of the idele class group of `L` are
exactly the image of the idele class group of `K`. -/
theorem range_baseChange_eq_setOf_fixed :
    Set.range (baseChange K L)
      = {c : IdeleClassGroup (𝓞 L) L | ∀ σ : L ≃ₐ[K] L, galIdeleClassAut K L σ c = c} := by
  ext c
  refine ⟨?_, mem_range_baseChange_of_fixed K L⟩
  rintro ⟨d, rfl⟩ σ
  exact galIdeleClassAut_baseChange σ d

/-- **`C_K ≃ (C_L)^{Gal(L/K)}`**, as a group isomorphism onto the range of the base change,
which `NumberField.IdeleClassGroup.range_baseChange_eq_setOf_fixed` identifies with the set of
`Gal(L/K)`-invariants of `C_L`. -/
def baseChangeEquivRange : IdeleClassGroup (𝓞 K) K ≃* (baseChange K L).range :=
  MonoidHom.ofInjective (baseChange_injective K L)

theorem mem_range_baseChange_iff (c : IdeleClassGroup (𝓞 L) L) :
    c ∈ Set.range (baseChange K L) ↔ ∀ σ : L ≃ₐ[K] L, galIdeleClassAut K L σ c = c := by
  rw [range_baseChange_eq_setOf_fixed]
  exact Iff.rfl

/-! ## What `Ĥ⁰(Gal(L/K), C_L)` is -/

section Tate

attribute [local instance] CyclicTate.Additive.distribMulActionOfMulDistrib

variable {K L}

/-- **`ker(σ - 1)` on `C_L` is exactly the image of `C_K`**, for a generator `σ` of a cyclic
`Gal(L/K)`.

Together with `CyclicTate.TateH0` this says that the group whose order the two fundamental
inequalities bound, `Ĥ⁰(Gal(L/K), C_L) = ker(σ - 1) / N C_L`, really is the norm quotient
`C_K / N_{L/K} C_L` of the statement `[C_K : N_{L/K} C_L] ≤ [L : K]`, and not merely an
abstract cohomology group. -/
theorem mem_kerSub_iff_mem_range_baseChange {σ : L ≃ₐ[K] L}
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (c : Additive (IdeleClassGroup (𝓞 L) L)) :
    c ∈ CyclicTate.kerSub (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ ↔
      Additive.toMul c ∈ Set.range (baseChange K L) := by
  rw [CyclicTate.mem_kerSub, range_baseChange_eq_setOf_fixed]
  constructor
  · intro h g
    obtain ⟨m, rfl⟩ := hgen g
    have hpow : ∀ n : ℕ, (σ ^ n) • c = c := by
      intro n
      induction n with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_smul, h, ih]
    exact congrArg Additive.toMul (hpow m)
  · intro h
    exact congrArg Additive.ofMul (h σ)

end Tate

end NumberField.IdeleClassGroup
