/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.TameCharacter
public import Mathlib.RingTheory.Filtration

@[expose] public section

/-!
# Tameness makes the tame character injective, and `e ∣ q - 1` unconditionally

`Iwasawalib/NumberTheory/LocalCFT/TameCharacter.lean` builds the tame character
`θ(σ) = σ(π)/π mod 𝔪` of a discrete valuation ring `B` and proves `θ(σ)^{q-1} = 1` whenever
`σ` lies in the inertia group and commutes with an automorphism inducing `x ↦ x^q` on the
residue field.  What was left there as a hypothesis is the **injectivity of `θ`**, i.e.
tameness.  This file proves it, with no completion, no monogenicity and no class field theory.

## The argument

Let `σ` be an automorphism of `B` acting trivially on the residue field `k`, with `σ^n = 1` and
`n` invertible in `B` — the tameness hypothesis, since `n` is invertible exactly when it is
prime to `char k`.  Suppose `θ(σ) = 1`.

* *A `σ`-fixed uniformizer exists.*  Put `ϖ = ∑_{i<n} σ^i(π)`.  Then `σ ϖ = ϖ` because the sum
  is over a full orbit (`LocalCFT.sum_orbit_fixed`), and `ϖ = π · c` with
  `c = ∑_{i<n} u_{σ^i}` of residue `∑_{i<n} θ(σ)^i = n ≠ 0`, so `c` is a unit and `ϖ` is again
  a uniformizer (`LocalCFT.exists_irreducible_fixed`).
* *`B` is approximated by the fixed ring.*  Averaging, `a = n⁻¹ ∑_{i<n} σ^i(b)` is `σ`-fixed and
  congruent to `b` mod `𝔪` (`LocalCFT.exists_fixed_sub_mem_maximalIdeal`); iterating along the
  `σ`-fixed uniformizer gives, for every `k`, a `σ`-fixed `a` with `b - a ∈ (ϖ^k)`
  (`LocalCFT.exists_fixed_sub_eq_pow_mul`).
* *Conclusion.*  Then `σ b - b = σ(b-a) - (b-a) ∈ 𝔪^k` for every `k`, and `⋂ₖ 𝔪^k = 0` by
  Krull's intersection theorem, so `σ = 1` (`LocalCFT.eq_one_of_tameChar_eq_one`).

Note that the usual proof — `ker θ = G₁` is a pro-`ℓ` group, by embedding `Gᵢ/Gᵢ₊₁` into the
additive group of `k` — needs `B` monogenic over the base, hence a completeness or perfectness
hypothesis.  The argument above needs neither: it replaces the whole higher filtration by one
averaging step plus Krull separatedness.

## Main statements

* `LocalCFT.exists_irreducible_fixed`: a `σ`-fixed uniformizer, when `θ(σ) = 1`.
* `LocalCFT.eq_one_of_tameChar_eq_one`: **`θ` is injective on tame inertia.**
* `LocalCFT.orderOf_dvd_sub_one`: **`e ∣ q - 1`**, with no hypothesis beyond tameness, the
  inertia condition, and the existence of a commuting `q`-Frobenius.  Unconditional: this file
  has no `sorry` and no axiom beyond the Lean standard three.
-/

noncomputable section

open IsLocalRing

namespace LocalCFT

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]


omit [IsDomain B] [IsDiscreteValuationRing B] in
theorem sum_orbit_fixed {σ : RingAut B} {n : ℕ} (hn : σ ^ n = 1) (x : B) :
    σ (∑ i ∈ Finset.range n, (σ ^ i) x) = ∑ i ∈ Finset.range n, (σ ^ i) x := by
  rw [map_sum]
  have hstep : ∀ i : ℕ, σ ((σ ^ i) x) = (σ ^ (i + 1)) x := fun i => by rw [pow_succ']; rfl
  simp only [hstep]
  have h1 := Finset.sum_range_succ' (fun i => (σ ^ i) x) n
  have h2 := Finset.sum_range_succ (fun i => (σ ^ i) x) n
  have h3 : (σ ^ n) x = x := by rw [hn]; rfl
  simp only [pow_zero] at h1
  rw [h3] at h2
  rw [h2, show (1 : RingAut B) x = x from rfl] at h1
  exact (add_right_cancel h1).symm

theorem map_natCast_inv {σ : RingAut B} {n : ℕ} (hu : IsUnit ((n : ℕ) : B)) :
    σ ((hu.unit⁻¹ : Bˣ) : B) = ((hu.unit⁻¹ : Bˣ) : B) := by
  have h : ((hu.unit⁻¹ : Bˣ) : B) * (n : B) = 1 := by
    simp
  have h2 : σ ((hu.unit⁻¹ : Bˣ) : B) * (n : B) = 1 := by
    have := congrArg σ h
    rwa [map_mul, map_natCast, map_one] at this
  have hn0 : (n : B) ≠ 0 := hu.ne_zero
  exact mul_right_cancel₀ hn0 (h2.trans h.symm)

theorem exists_fixed_sub_mem_maximalIdeal {σ : RingAut B} (hσ : σ ∈ inertiaAut B) {n : ℕ}
    (hn : σ ^ n = 1) (hu : IsUnit ((n : ℕ) : B)) (b : B) :
    ∃ a : B, σ a = a ∧ b - a ∈ maximalIdeal B := by
  set c : B := ((hu.unit⁻¹ : Bˣ) : B) with hc
  refine ⟨c * ∑ i ∈ Finset.range n, (σ ^ i) b, ?_, ?_⟩
  · rw [map_mul, map_natCast_inv hu, sum_orbit_fixed hn]
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    show residue B (b - c * _) = 0
    rw [map_sub, sub_eq_zero, map_mul, map_sum]
    have hres : ∀ i ∈ Finset.range n, residue B ((σ ^ i) b) = residue B b := fun i _ =>
      (Subgroup.pow_mem _ hσ i) b
    rw [Finset.sum_congr rfl hres, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcn : residue B c * (n : ResidueField B) = 1 := by
      have h : c * (n : B) = 1 := by simp [hc]
      have := congrArg (residue B) h
      rwa [map_mul, map_natCast, map_one] at this
    rw [← mul_assoc, hcn, one_mul]

theorem exists_irreducible_fixed {π : B} (hπ : Irreducible π) {σ : RingAut B}
    (hσ : σ ∈ inertiaAut B) {n : ℕ} (hn : σ ^ n = 1) (hu : IsUnit ((n : ℕ) : B))
    (hθ : tameChar hπ σ = 1) :
    ∃ ϖ : B, Irreducible ϖ ∧ σ ϖ = ϖ := by
  set c : B := ∑ i ∈ Finset.range n, ((tameUnit hπ (σ ^ i) : Bˣ) : B) with hcdef
  have hsum : ∑ i ∈ Finset.range n, (σ ^ i) π = π * c := by
    rw [hcdef, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (mul_tameUnit hπ (σ ^ i)).symm
  have hresc : residue B c = (n : ResidueField B) := by
    rw [hcdef, map_sum]
    have : ∀ i ∈ Finset.range n, residue B ((tameUnit hπ (σ ^ i) : Bˣ) : B) = 1 := by
      intro i _
      rw [show residue B ((tameUnit hπ (σ ^ i) : Bˣ) : B) = tameChar hπ (σ ^ i) from rfl,
        tameChar_pow hπ hσ, hθ, one_pow]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hcunit : IsUnit c := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hmem
    have h0 : (n : ResidueField B) = 0 := by
      rw [← hresc]; exact hmem
    refine (hu.map (residue B)).ne_zero ?_
    rw [map_natCast]
    exact h0
  refine ⟨π * c, ?_, ?_⟩
  · exact (associated_mul_unit_right π c hcunit).irreducible hπ
  · rw [← hsum, sum_orbit_fixed hn]

theorem exists_fixed_sub_eq_pow_mul {ϖ : B} (hϖ : Irreducible ϖ) {σ : RingAut B}
    (hσ : σ ∈ inertiaAut B) {n : ℕ} (hn : σ ^ n = 1) (hu : IsUnit ((n : ℕ) : B))
    (hfix : σ ϖ = ϖ) : ∀ (k : ℕ) (b : B), ∃ a : B, σ a = a ∧ ∃ y : B, b - a = ϖ ^ k * y := by
  intro k
  induction k with
  | zero => exact fun b => ⟨0, map_zero σ, b, by simp⟩
  | succ k ih =>
    intro b
    obtain ⟨a₀, ha₀, hb₀⟩ := exists_fixed_sub_mem_maximalIdeal hσ hn hu b
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hb₀
    obtain ⟨d, hd⟩ := hb₀
    obtain ⟨a₁, ha₁, y, hy⟩ := ih d
    refine ⟨a₀ + ϖ * a₁, by rw [map_add, map_mul, ha₀, ha₁, hfix], y, ?_⟩
    have : b - (a₀ + ϖ * a₁) = ϖ * (d - a₁) := by linear_combination -hd
    rw [this, hy, pow_succ']
    ring

/-- **Tame injectivity.**  An automorphism of a discrete valuation ring which acts trivially on
the residue field, has finite order invertible in the ring, and has trivial tame character, is
the identity. -/
theorem eq_one_of_tameChar_eq_one {π : B} (hπ : Irreducible π) {σ : RingAut B}
    (hσ : σ ∈ inertiaAut B) {n : ℕ} (hn : σ ^ n = 1) (hu : IsUnit ((n : ℕ) : B))
    (hθ : tameChar hπ σ = 1) : σ = 1 := by
  obtain ⟨ϖ, hϖ, hfix⟩ := exists_irreducible_fixed hπ hσ hn hu hθ
  have hbot : (⨅ k : ℕ, (maximalIdeal B) ^ k) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  refine RingEquiv.ext fun b => ?_
  have hmem : ∀ k : ℕ, σ b - b ∈ (maximalIdeal B) ^ k := by
    intro k
    obtain ⟨a, ha, y, hy⟩ := exists_fixed_sub_eq_pow_mul hϖ hσ hn hu hfix k b
    have hkey : σ b - b = ϖ ^ k * (σ y - y) := by
      have h1 : σ (b - a) = σ b - a := by rw [map_sub, ha]
      have h2 : σ (b - a) = ϖ ^ k * σ y := by rw [hy, map_mul, map_pow, hfix]
      have h3 : σ b - a = ϖ ^ k * σ y := h1.symm.trans h2
      linear_combination h3 - hy
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨σ y - y, by rw [hkey]; ring⟩
  have hin : σ b - b ∈ (⨅ k : ℕ, (maximalIdeal B) ^ k) := Ideal.mem_iInf.2 hmem
  rw [hbot] at hin
  have h0 : σ b - b = 0 := by simpa using hin
  rw [show (1 : RingAut B) b = b from rfl, ← sub_eq_zero]
  exact h0

/-- **`e ∣ q - 1` for an abelian, tamely ramified situation.** -/
theorem orderOf_dvd_sub_one {π : B} (hπ : Irreducible π) {σ τ : RingAut B}
    (hσ : σ ∈ inertiaAut B) {n : ℕ} (hn : σ ^ n = 1) (hu : IsUnit ((n : ℕ) : B))
    {q : ℕ} (hq : 1 ≤ q) (hτ : ∀ b : B, residue B (τ b) = residue B b ^ q)
    (hcomm : τ * σ = σ * τ) : orderOf σ ∣ q - 1 := by
  refine orderOf_dvd_of_pow_eq_one ?_
  refine eq_one_of_tameChar_eq_one hπ (Subgroup.pow_mem _ hσ _) (n := n) ?_ hu ?_
  · rw [← pow_mul, mul_comm, pow_mul, hn, one_pow]
  · rw [tameChar_pow hπ hσ]
    exact tameChar_pow_sub_one_eq_one hπ hq hσ hτ hcomm

end LocalCFT
