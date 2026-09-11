/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.Herbrand
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section

/-!
# Additive Hilbert 90: a `G`-ring with an element of trace one is cohomologically trivial

Let `G = ⟨σ⟩` be a finite cyclic group acting by ring automorphisms on a commutative ring `R`,
and suppose there is `c : R` with `∑ g : G, g • c = 1` ("an element of trace one").  Then both
Tate cohomology groups of the *additive* group of `R` vanish:

* `Ĥ⁰(G, R⁺) = R^G / N R = 0`, because `x = N (x · c)` for `G`-invariant `x`;
* `Ĥ¹(G, R⁺) = ker N / (σ - 1) R = 0`, by the classical telescoping witness
  `y = ∑_{i < n} (∑_{j < i} σ^j x) · σ^i c`, which satisfies `σ • y - y = -x`.

For a finite Galois extension of fields `E / F` the trace is surjective, so `c` exists and this
is **additive Hilbert 90**, listed as a TODO in Mathlib's
`Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`.  In particular the
additive group of a finite field is cohomologically trivial for its Galois group — the input
needed for the quotients `1 + 𝔪^n / 1 + 𝔪^{n+1} ≅ k⁺` of the unit filtration of a local field.

## Main statements

* `CyclicTate.exists_normHom_eq_of_smul_eq`, `CyclicTate.tateH0_subsingleton_of_traceOne`.
* `CyclicTate.exists_smul_sub_eq_of_normHom_eq_zero`,
  `CyclicTate.tateH1_subsingleton_of_traceOne`.
* `CyclicTate.herbrand_eq_one_of_traceOne`: the Herbrand quotient of `R⁺` is `1`.
* `CyclicTate.exists_sum_smul_eq_one_of_isGalois`: a finite Galois extension has an element of
  trace one, so the above applies to `E⁺`.
-/

noncomputable section

open Finset

namespace CyclicTate

/-! ## Powers of the generator -/

section Cyclic

variable {G : Type*} [Group G] [Finite G] {σ : G}

/-- In a cyclic group `G = ⟨σ⟩`, a point fixed by `σ` is fixed by everything. -/
theorem smul_eq_self_of_forall_mem_zpowers (hg : ∀ x : G, x ∈ Subgroup.zpowers σ)
    {M : Type*} [MulAction G M] {x : M} (hx : σ • x = x) (g : G) :
    g • x = x := by
  have key : ∀ n : ℕ, (σ ^ n) • x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_smul, ih, hx]
  obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers (x := σ) (y := g)).2 (hg g)
  exact key n

variable [Fintype G]

omit [Finite G] in
/-- For a finite cyclic group `G = ⟨σ⟩` the norm is the sum over the first `Nat.card G` powers
of `σ`. -/
theorem normHom_eq_sum_range (hg : ∀ x : G, x ∈ Subgroup.zpowers σ)
    {M : Type*} [AddCommGroup M] [DistribMulAction G M] (x : M) :
    normHom G M x = ∑ i ∈ range (Nat.card G), (σ ^ i) • x := by
  classical
  have himg : Finset.image (fun i ↦ σ ^ i) (range (Nat.card G)) = univ :=
    IsCyclic.image_range_card hg
  have hinj : ∀ i ∈ range (Nat.card G), ∀ j ∈ range (Nat.card G), σ ^ i = σ ^ j → i = j := by
    intro i hi j hj hij
    rw [mem_range, ← orderOf_eq_card_of_forall_mem_zpowers hg] at hi hj
    exact pow_injOn_Iio_orderOf hi hj hij
  rw [normHom_apply, ← himg, Finset.sum_image hinj]

omit [Finite G] [Fintype G] in
theorem pow_card_eq_one_of_forall_mem_zpowers (hg : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    σ ^ Nat.card G = 1 := by
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact pow_orderOf_eq_one σ

end Cyclic

/-! ## Vanishing in the presence of an element of trace one -/

section TraceOne

variable {G R : Type*} [Group G] [Fintype G] [CommRing R] [MulSemiringAction G R] {σ : G}
  {c : R}

/-- **`Ĥ⁰(G, R⁺) = 0`**: if some `c : R` has `∑ g, g • c = 1`, every invariant element is a
norm, with witness `x · c`. -/
theorem exists_normHom_eq_of_smul_eq (hg : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (hc : ∑ g : G, g • c = 1) {x : R} (hx : σ • x = x) :
    ∃ y : R, normHom G R y = x := by
  refine ⟨x * c, ?_⟩
  rw [normHom_apply]
  have : ∀ g : G, g • (x * c) = x * (g • c) := fun g ↦ by
    rw [smul_mul', smul_eq_self_of_forall_mem_zpowers hg hx g]
  rw [Finset.sum_congr rfl fun g _ ↦ this g, ← Finset.mul_sum, hc, mul_one]

/-- **`Ĥ¹(G, R⁺) = 0`**: if some `c : R` has `∑ g, g • c = 1`, every element of norm zero is of
the form `σ • y - y`. -/
theorem exists_smul_sub_eq_of_normHom_eq_zero (hg : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (hc : ∑ g : G, g • c = 1) {x : R} (hx : normHom G R x = 0) :
    ∃ y : R, σ • y - y = x := by
  classical
  set n := Nat.card G with hn
  have hσn : σ ^ n = 1 := pow_card_eq_one_of_forall_mem_zpowers hg
  set S : ℕ → R := fun i ↦ ∑ j ∈ range i, (σ ^ j) • x with hSdef
  have hS0 : S 0 = 0 := by simp [hSdef]
  have hSn : S n = 0 := by
    rw [normHom_eq_sum_range hg] at hx
    simpa [hSdef, hn] using hx
  have hSsucc : ∀ i : ℕ, S (i + 1) = (∑ j ∈ range i, (σ ^ (j + 1)) • x) + x := by
    intro i
    rw [hSdef]
    simp only
    rw [Finset.sum_range_succ']
    simp
  have hsmulS : ∀ i : ℕ, σ • S i = S (i + 1) - x := by
    intro i
    rw [hSsucc i, hSdef]
    simp only [Finset.smul_sum, smul_smul, ← pow_succ']
    abel
  set e : ℕ → R := fun k ↦ (σ ^ k) • c with hedef
  set f : ℕ → R := fun k ↦ S k * e k with hfdef
  set y : R := ∑ i ∈ range n, f i with hydef
  -- the two telescoping identities
  have hf0 : f 0 = 0 := by simp [hfdef, hS0]
  have hfn : f n = 0 := by simp [hfdef, hSn]
  have hshiftf : ∑ i ∈ range n, f (i + 1) = y := by
    have h₁ : ∑ i ∈ range (n + 1), f i = (∑ i ∈ range n, f (i + 1)) + f 0 :=
      Finset.sum_range_succ' f n
    have h₂ : ∑ i ∈ range (n + 1), f i = (∑ i ∈ range n, f i) + f n :=
      Finset.sum_range_succ f n
    rw [hf0, add_zero] at h₁
    rw [hfn, add_zero] at h₂
    rw [← h₁, h₂, hydef]
  have hen : e n = e 0 := by simp [hedef, hσn]
  have hesum : ∑ i ∈ range n, e i = 1 := by
    rw [← normHom_eq_sum_range hg, normHom_apply, hc]
  have hshifte : ∑ i ∈ range n, e (i + 1) = 1 := by
    have h₁ : ∑ i ∈ range (n + 1), e i = (∑ i ∈ range n, e (i + 1)) + e 0 :=
      Finset.sum_range_succ' e n
    have h₂ : ∑ i ∈ range (n + 1), e i = (∑ i ∈ range n, e i) + e n :=
      Finset.sum_range_succ e n
    rw [hen] at h₂
    have := h₁.symm.trans h₂
    rw [hesum] at this
    exact add_right_cancel this
  -- the key computation `σ • y = y - x`
  have key : σ • y = y - x := by
    have h₁ : σ • y = ∑ i ∈ range n, (S (i + 1) - x) * e (i + 1) := by
      rw [hydef, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hfdef]
      simp only
      rw [smul_mul', hsmulS i, hedef]
      simp only [smul_smul, ← pow_succ']
    have h₂ : ∑ i ∈ range n, (S (i + 1) - x) * e (i + 1) =
        (∑ i ∈ range n, f (i + 1)) - x * ∑ i ∈ range n, e (i + 1) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hfdef]
      ring
    rw [h₁, h₂, hshiftf, hshifte, mul_one]
  exact ⟨-y, by rw [smul_neg, key]; abel⟩

variable (G R)

/-- `Ĥ⁰(G, R⁺) = 0` for a `G`-ring with an element of trace one. -/
theorem tateH0_subsingleton_of_traceOne (hg : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (hc : ∑ g : G, g • c = 1) : Subsingleton (TateH0 G R σ) :=
  (tateH0_subsingleton_iff σ).2 fun _ hx ↦ exists_normHom_eq_of_smul_eq hg hc hx

/-- `Ĥ¹(G, R⁺) = 0` for a `G`-ring with an element of trace one. -/
theorem tateH1_subsingleton_of_traceOne (hg : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (hc : ∑ g : G, g • c = 1) : Subsingleton (TateH1 G R σ) :=
  (tateH1_subsingleton_iff σ).2 fun _ hx ↦ exists_smul_sub_eq_of_normHom_eq_zero hg hc hx

/-- The Herbrand quotient of a `G`-ring with an element of trace one is `1`. -/
theorem herbrand_eq_one_of_traceOne (hg : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (hc : ∑ g : G, g • c = 1) : herbrand G R σ = 1 :=
  haveI := tateH0_subsingleton_of_traceOne G R hg hc
  haveI := tateH1_subsingleton_of_traceOne G R hg hc
  herbrand_eq_one_of_subsingleton σ

end TraceOne

/-! ## Galois extensions have an element of trace one -/

section Galois

variable (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

/-- **A finite Galois extension has an element of trace one**: the trace form is surjective, so
some `c : E` has `∑ g : Gal(E/F), g • c = 1`. -/
theorem exists_sum_smul_eq_one_of_isGalois :
    ∃ c : E, ∑ g : E ≃ₐ[F] E, g • c = 1 := by
  obtain ⟨c, hc⟩ := Algebra.trace_surjective F E 1
  refine ⟨c, ?_⟩
  have h := _root_.trace_eq_sum_automorphisms (K := F) (L := E) c
  simp only [AlgEquiv.smul_def]
  rw [← h, hc, map_one]

variable {F E}

/-- **Additive Hilbert 90 for a finite cyclic Galois extension**: `Ĥ¹(Gal(E/F), E⁺) = 0`. -/
theorem tateH1_subsingleton_of_isGalois {σ : E ≃ₐ[F] E}
    (hg : ∀ x : E ≃ₐ[F] E, x ∈ Subgroup.zpowers σ) :
    Subsingleton (TateH1 (E ≃ₐ[F] E) E σ) := by
  obtain ⟨c, hc⟩ := exists_sum_smul_eq_one_of_isGalois F E
  exact tateH1_subsingleton_of_traceOne _ _ hg hc

/-- `Ĥ⁰(Gal(E/F), E⁺) = 0` for a finite cyclic Galois extension: every element of `F` is a
trace. -/
theorem tateH0_subsingleton_of_isGalois {σ : E ≃ₐ[F] E}
    (hg : ∀ x : E ≃ₐ[F] E, x ∈ Subgroup.zpowers σ) :
    Subsingleton (TateH0 (E ≃ₐ[F] E) E σ) := by
  obtain ⟨c, hc⟩ := exists_sum_smul_eq_one_of_isGalois F E
  exact tateH0_subsingleton_of_traceOne _ _ hg hc

/-- The additive group of a finite cyclic Galois extension has Herbrand quotient `1`; indeed
both its Tate groups vanish. -/
theorem herbrand_eq_one_of_isGalois {σ : E ≃ₐ[F] E}
    (hg : ∀ x : E ≃ₐ[F] E, x ∈ Subgroup.zpowers σ) :
    herbrand (E ≃ₐ[F] E) E σ = 1 := by
  obtain ⟨c, hc⟩ := exists_sum_smul_eq_one_of_isGalois F E
  exact herbrand_eq_one_of_traceOne _ _ hg hc

end Galois

end CyclicTate
