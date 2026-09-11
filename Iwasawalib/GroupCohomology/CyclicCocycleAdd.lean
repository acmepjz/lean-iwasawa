/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.FiniteFieldTate
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

@[expose] public section

/-!
# Additive 1-cocycles of a finite cyclic group, and `H¹(G, E⁺) = 0`

This is the additive counterpart of `Iwasawalib/GroupCohomology/CyclicCocycle.lean`.  A
1-cocycle `f : G → M` of a finite cyclic group `G = ⟨σ⟩` with values in a `G`-module `M` is
determined by `f σ`, whose possible values are exactly the elements of norm zero.  Hence the
vanishing of the *Tate* group `Ĥ¹(G, M) = ker N / (σ - 1)M`, which is what
`Iwasawalib/GroupCohomology/TraceOne.lean` proves in the presence of an element of trace one,
implies the vanishing of `H¹(G, M)` in Mathlib's sense.

Applied to a finite cyclic Galois extension of fields this is **additive Hilbert 90**,
`H¹(Gal(E/F), E⁺) = 0`, which is listed as a TODO in Mathlib's
`Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`.

## Main statements

* `CyclicCocycleAdd.isCocycle₁_pow`: `f (σ ^ n) = ∑ i < n, σ ^ i • f σ`.
* `CyclicCocycleAdd.normHom_apply_generator`: `N (f σ) = 0`.
* `CyclicCocycleAdd.isCoboundary₁_of_normHom`: `Ĥ¹ = 0` implies `H¹ = 0`.
* `CyclicCocycleAdd.isZero_H1_of_traceOne`: `H¹(G, R⁺) = 0` for a `G`-ring with an element of
  trace one.
* `CyclicCocycleAdd.isZero_H1_additive_of_isGalois`: **additive Hilbert 90** for a finite cyclic
  Galois extension of fields.
-/

noncomputable section

open Finset CategoryTheory CategoryTheory.Limits CyclicTate

namespace CyclicCocycleAdd

open groupCohomology

section

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- The value of an additive 1-cocycle at a power of `σ`. -/
theorem isCocycle₁_pow {f : G → M} (hf : IsCocycle₁ f) (σ : G) (n : ℕ) :
    f (σ ^ n) = ∑ i ∈ range n, (σ ^ i) • f σ := by
  induction n with
  | zero => simpa using map_one_of_isCocycle₁ hf
  | succ n ih =>
    rw [pow_succ', hf σ (σ ^ n), ih, Finset.sum_range_succ']
    simp only [pow_zero, one_smul, Finset.smul_sum, smul_smul, ← pow_succ']

/-- `x ↦ g • x - x` is an additive 1-cocycle. -/
theorem isCocycle₁_smul_sub (y : M) : IsCocycle₁ fun g : G ↦ g • y - y := by
  intro g h
  show (g * h) • y - y = g • (h • y - y) + (g • y - y)
  rw [smul_sub, mul_smul]
  abel

variable [Fintype G] {σ : G}

/-- The value of an additive 1-cocycle at a generator has norm zero. -/
theorem normHom_apply_generator (hg : ∀ x : G, x ∈ Subgroup.zpowers σ) {f : G → M}
    (hf : IsCocycle₁ f) : normHom G M (f σ) = 0 := by
  rw [normHom_eq_sum_range hg, ← isCocycle₁_pow hf σ (Nat.card G),
    ← orderOf_eq_card_of_forall_mem_zpowers hg, pow_orderOf_eq_one,
    map_one_of_isCocycle₁ hf]

/-- An additive 1-cocycle of a finite cyclic group is determined by its value at a
generator. -/
theorem eq_of_apply_generator_eq (hg : ∀ x : G, x ∈ Subgroup.zpowers σ) {f f' : G → M}
    (hf : IsCocycle₁ f) (hf' : IsCocycle₁ f') (h : f σ = f' σ) : f = f' := by
  funext g
  obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers (x := σ) (y := g)).2 (hg g)
  rw [isCocycle₁_pow hf, isCocycle₁_pow hf', h]

/-- **`Ĥ¹ = 0` implies `H¹ = 0`** for a finite cyclic group: if every element of norm `0` is of
the form `σ • y - y`, then every additive 1-cocycle is a 1-coboundary. -/
theorem isCoboundary₁_of_normHom (hg : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (h : ∀ x : M, normHom G M x = 0 → ∃ y : M, σ • y - y = x)
    {f : G → M} (hf : IsCocycle₁ f) : IsCoboundary₁ f := by
  obtain ⟨y, hy⟩ := h (f σ) (normHom_apply_generator hg hf)
  exact ⟨y, fun g ↦ congrFun (eq_of_apply_generator_eq hg (isCocycle₁_smul_sub y) hf hy) g⟩

end

/-! ## The cohomological statement -/

section Rep

variable {G M : Type} [Group G] [Fintype G] [AddCommGroup M] [DistribMulAction G M] {σ : G}

/-- **`H¹(G, M) = 0`** for a finite cyclic group `G = ⟨σ⟩` whose Tate group `Ĥ¹` vanishes. -/
theorem H1_eq_zero_of_normHom (hg : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (h : ∀ x : M, normHom G M x = 0 → ∃ y : M, σ • y - y = x)
    (x : groupCohomology (Rep.ofDistribMulAction ℤ G M) 1) : x = 0 :=
  H1_induction_on x fun y ↦ (H1π_eq_zero_iff _).2 <|
    (coboundariesOfIsCoboundary₁ (k := ℤ)
      (isCoboundary₁_of_normHom hg h (isCocycle₁_of_mem_cocycles₁ _ y.2))).2

/-- `H¹(G, M) = 0`, as an `IsZero` statement. -/
theorem isZero_H1_of_normHom (hg : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (h : ∀ x : M, normHom G M x = 0 → ∃ y : M, σ • y - y = x) :
    IsZero (groupCohomology (Rep.ofDistribMulAction ℤ G M) 1) := by
  have : Subsingleton (groupCohomology (Rep.ofDistribMulAction ℤ G M) 1) :=
    ⟨fun x y ↦ by rw [H1_eq_zero_of_normHom hg h x, H1_eq_zero_of_normHom hg h y]⟩
  exact ModuleCat.isZero_of_subsingleton _

end Rep

section TraceOne

variable {G R : Type} [Group G] [Fintype G] [CommRing R] [MulSemiringAction G R] {σ : G} {c : R}

/-- **`H¹(G, R⁺) = 0`** for a finite cyclic group acting on a commutative ring with an element
of trace one. -/
theorem isZero_H1_of_traceOne (hg : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (hc : ∑ g : G, g • c = 1) :
    IsZero (groupCohomology (Rep.ofDistribMulAction ℤ G R) 1) :=
  isZero_H1_of_normHom hg fun _ hx ↦ exists_smul_sub_eq_of_normHom_eq_zero hg hc hx

end TraceOne

section Galois

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

/-- **Additive Hilbert 90.**  For a finite Galois extension of fields with cyclic Galois group,
`H¹(Gal(E/F), E⁺) = 0`. -/
theorem isZero_H1_additive_of_isGalois {σ : E ≃ₐ[F] E}
    (hg : ∀ g : E ≃ₐ[F] E, g ∈ Subgroup.zpowers σ) :
    IsZero (groupCohomology (Rep.ofDistribMulAction ℤ (E ≃ₐ[F] E) E) 1) := by
  obtain ⟨c, hc⟩ := exists_sum_smul_eq_one_of_isGalois F E
  exact isZero_H1_of_traceOne hg hc

end Galois

end CyclicCocycleAdd
