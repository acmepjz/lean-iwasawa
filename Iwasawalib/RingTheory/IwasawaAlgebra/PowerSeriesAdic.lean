/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

/-!
# The ideal `(a, X)` of a power series ring

Let `A` be a commutative ring and `a : A`. We describe the powers of the ideal `(a, X)` of
`A⟦X⟧` in terms of coefficients: a power series `g` lies in `(a, X) ^ K` if and only if
`coeff i g ∈ (a ^ (K - i))` for all `i < K`.

This is the technical input for the separatedness and completeness of `A⟦X⟧` with respect to
the `(a, X)`-adic topology, used in the construction of the isomorphism between the Iwasawa
algebra and `A⟦X⟧` (blueprint node `Iwasawa-alg-isom`).
-/

namespace PowerSeries

variable {A : Type*} [CommRing A] (a : A)

/-- The ideal `(a, X)` of `A⟦X⟧`. -/
noncomputable def idealAX : Ideal A⟦X⟧ := Ideal.span {C a, X}

theorem C_mem_idealAX : C a ∈ idealAX a := Ideal.subset_span (by simp)

theorem X_mem_idealAX : (X : A⟦X⟧) ∈ idealAX a := Ideal.subset_span (by simp)

variable {a}

/-- Easy direction: an element of `(a, X) ^ K` has `i`-th coefficient divisible by
`a ^ (K - i)`. -/
theorem coeff_mem_of_mem_idealAX_pow {K : ℕ} {g : A⟦X⟧} (hg : g ∈ idealAX a ^ K) (i : ℕ) :
    coeff i g ∈ Ideal.span {a ^ (K - i)} := by
  induction K generalizing g i with
  | zero => simp
  | succ K ih =>
    rw [pow_succ] at hg
    revert i
    refine Submodule.mul_induction_on hg ?_ (fun x y hx hy i ↦ by
      rw [map_add]; exact Ideal.add_mem _ (hx i) (hy i))
    intro m hm n hn i
    · obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.1 hn
      have h1 : m * u ∈ idealAX a ^ K := Ideal.mul_mem_right _ _ hm
      have h2 : m * v ∈ idealAX a ^ K := Ideal.mul_mem_right _ _ hm
      have : m * (u * C a + v * X) = (m * u) * C a + (m * v) * X := by ring
      rw [this, map_add]
      refine Ideal.add_mem _ ?_ ?_
      · rw [coeff_mul_C, Ideal.mem_span_singleton]
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (ih h1 i)
        refine dvd_trans (pow_dvd_pow a (show K + 1 - i ≤ (K - i) + 1 by omega)) ?_
        rw [hc, pow_succ]
        exact ⟨c, by ring⟩
      · cases i with
        | zero => simp
        | succ j =>
          rw [coeff_succ_mul_X, show K + 1 - (j + 1) = K - j by omega]
          exact ih h2 j


/-- Hard direction: if the `i`-th coefficient of `g` is divisible by `a ^ (K - i)` for all
`i < K`, then `g ∈ (a, X) ^ K`. -/
theorem mem_idealAX_pow_of_coeff_mem {K : ℕ} {g : A⟦X⟧}
    (h : ∀ i < K, coeff i g ∈ Ideal.span {a ^ (K - i)}) : g ∈ idealAX a ^ K := by
  induction K generalizing g with
  | zero => simp
  | succ K ih =>
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (h 0 (Nat.succ_pos K))
    have hc : constantCoeff (g - C (coeff 0 g)) = 0 := by simp
    obtain ⟨t, ht⟩ := X_dvd_iff.2 hc
    have hgt : g = C (coeff 0 g) + X * t := by rw [← ht]; ring
    have htmem : t ∈ idealAX a ^ K := by
      refine ih fun i hi ↦ ?_
      have : coeff i t = coeff (i + 1) g := by
        have := congr(coeff (i + 1) $ht)
        rwa [map_sub, coeff_succ_X_mul, coeff_C, if_neg (Nat.succ_ne_zero i), sub_zero,
          eq_comm] at this
      rw [this]
      have := h (i + 1) (by omega)
      rwa [show K + 1 - (i + 1) = K - i by omega] at this
    rw [hgt]
    refine Ideal.add_mem _ ?_ ?_
    · rw [← hb, map_mul, map_pow]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (C_mem_idealAX a) _)
    · rw [show (X : A⟦X⟧) * t = t * X by ring, pow_succ]
      exact Ideal.mul_mem_mul htmem (X_mem_idealAX a)

end PowerSeries
