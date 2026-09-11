/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.Polynomial.OneAddXPowSubOne

@[expose] public section

/-!
# The polynomials `ν_{n,e} = ω_n / ω_e`

For `n ≥ e ≥ 0` we set, following Washington's *Introduction to cyclotomic fields*,
`ω_n := (1 + X) ^ (p ^ n) - 1` and
`ν_{n,e} := ∑_{k < p ^ (n - e)} (1 + X) ^ (k * p ^ e)`.

This file proves blueprint node `nu-distinguished`:

* `Polynomial.nu_mul_omega`: `ν_{n,e} * ω_e = ω_n`;
* `Polynomial.isDistinguishedAt_nu`: `ν_{n,e}` is distinguished at `(p)`;
* `Polynomial.natDegree_nu`: `deg ν_{n,e} = p ^ n - p ^ e`;
* `Polynomial.nu_dvd_nu`: `ν_{n,e} ∣ ν_{n',e}` for `e ≤ n ≤ n'`.

The key general tool is `Polynomial.IsDistinguishedAt.of_mul_right`: if `f * g` and `g` are
distinguished at a prime ideal `I`, then so is `f`.
-/

open Finset

namespace Polynomial

section Cancel

variable {A : Type*} [CommRing A] {I : Ideal A}

/-- If `f * g` and `g` are distinguished at a prime ideal `I`, then so is `f`. -/
theorem IsDistinguishedAt.of_mul_right [I.IsPrime] {f g : A[X]}
    (hfg : (f * g).IsDistinguishedAt I) (hg : g.IsDistinguishedAt I) :
    f.IsDistinguishedAt I := by
  have hmono : f.Monic := hg.monic.of_mul_monic_right hfg.monic
  have hdeg : (f * g).natDegree = f.natDegree + g.natDegree := hmono.natDegree_mul hg.monic
  have hnt : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr ‹I.IsPrime›.ne_top
  have hdom : IsDomain (A ⧸ I) := Ideal.Quotient.isDomain I
  have hmapf : f.map (Ideal.Quotient.mk I) = (X : (A ⧸ I)[X]) ^ f.natDegree := by
    have h1 : f.map (Ideal.Quotient.mk I) * (X : (A ⧸ I)[X]) ^ g.natDegree =
        (X : (A ⧸ I)[X]) ^ f.natDegree * (X : (A ⧸ I)[X]) ^ g.natDegree :=
      calc f.map (Ideal.Quotient.mk I) * (X : (A ⧸ I)[X]) ^ g.natDegree
          = f.map (Ideal.Quotient.mk I) * g.map (Ideal.Quotient.mk I) := by
            rw [hg.map_eq_X_pow]
        _ = (f * g).map (Ideal.Quotient.mk I) := (Polynomial.map_mul _).symm
        _ = (X : (A ⧸ I)[X]) ^ (f.natDegree + g.natDegree) := by rw [hfg.map_eq_X_pow, hdeg]
        _ = (X : (A ⧸ I)[X]) ^ f.natDegree * (X : (A ⧸ I)[X]) ^ g.natDegree := pow_add _ _ _
    exact mul_right_cancel₀ (pow_ne_zero _ X_ne_zero) h1
  refine ⟨⟨fun {i} hi ↦ ?_⟩, hmono⟩
  have := congr(Polynomial.coeff $hmapf i)
  rw [coeff_map, coeff_X_pow, if_neg hi.ne] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 this

end Cancel

variable (R : Type*) (p : ℕ) [Fact p.Prime]

section Semiring

variable [Semiring R]

/-- `ν_{n,e} := ∑_{k < p ^ (n - e)} (1 + X) ^ (k * p ^ e)`, the quotient `ω_n / ω_e`. -/
noncomputable def nu (n e : ℕ) : R[X] := ∑ i ∈ Finset.range (p ^ (n - e)), (1 + X) ^ (p ^ e * i)

omit [Fact p.Prime] in
/-- **Blueprint node `nu-distinguished` (ii)**, first half: `ν_{n,e} * ω_e = ω_n`. -/
theorem nu_mul_oneAddXPowSubOne {n e : ℕ} (h : e ≤ n) :
    oneAddXPowSubOne R (p ^ e) * nu R p n e = oneAddXPowSubOne R (p ^ n) := by
  rw [nu, oneAddXPowSubOne_mul_geom_sum, ← pow_add, Nat.add_sub_cancel' h]

end Semiring

section CommRing

variable [CommRing R]

/-- `ν_{n,e}` is monic of degree `p ^ n - p ^ e` and distinguished at `(p)`, provided that
`(p)` is a prime ideal of `R` (e.g. `R = ℤ_p`). -/
theorem isDistinguishedAt_nu [h : (Ideal.span {(p : R)}).IsPrime] {n e : ℕ} (h : e ≤ n) :
    (nu R p n e).IsDistinguishedAt (Ideal.span {(p : R)}) := by
  refine IsDistinguishedAt.of_mul_right (g := oneAddXPowSubOne R (p ^ e)) ?_
    (isDistinguishedAt_oneAddXPowSubOne R p e)
  rw [mul_comm, nu_mul_oneAddXPowSubOne R p h]
  exact isDistinguishedAt_oneAddXPowSubOne R p n

/-- **Blueprint node `nu-distinguished` (ii)**, second half: `deg ν_{n,e} = p ^ n - p ^ e`. -/
theorem natDegree_nu [Nontrivial R] {n e : ℕ} (h : e ≤ n) :
    (nu R p n e).natDegree = p ^ n - p ^ e := by
  have hmul := nu_mul_oneAddXPowSubOne R p h
  have hmonic : (nu R p n e).Monic := by
    refine ((monic_oneAddXPowSubOne_of_ne_zero R (p ^ e)
      (by simp [(Fact.out : p.Prime).ne_zero])).of_mul_monic_left ?_)
    rw [hmul]
    exact monic_oneAddXPowSubOne_of_ne_zero R _ (by simp [(Fact.out : p.Prime).ne_zero])
  have hd := congr(Polynomial.natDegree $hmul)
  rw [(monic_oneAddXPowSubOne_of_ne_zero R (p ^ e)
      (by simp [(Fact.out : p.Prime).ne_zero])).natDegree_mul hmonic,
    natDegree_oneAddXPowSubOne, natDegree_oneAddXPowSubOne] at hd
  have : p ^ e ≤ p ^ n := Nat.pow_le_pow_right (Fact.out : p.Prime).pos h
  omega

end CommRing

section Domain

variable [CommRing R] [IsDomain R]

/-- **Blueprint node `nu-distinguished` (iii)**: `ν_{n,e} ∣ ν_{n',e}` for `e ≤ n ≤ n'`. -/
theorem nu_dvd_nu {n n' e : ℕ} (he : e ≤ n) (h : n ≤ n') : nu R p n e ∣ nu R p n' e := by
  have hω : oneAddXPowSubOne R (p ^ e) ≠ 0 :=
    (monic_oneAddXPowSubOne_of_ne_zero R (p ^ e)
      (by simp [(Fact.out : p.Prime).ne_zero])).ne_zero
  obtain ⟨c, hc⟩ := oneAddXPowSubOne_dvd_of_dvd R (p ^ n) (p ^ n')
    (pow_dvd_pow p h)
  refine ⟨c, mul_left_cancel₀ hω ?_⟩
  rw [nu_mul_oneAddXPowSubOne R p (he.trans h), ← mul_assoc,
    nu_mul_oneAddXPowSubOne R p he, hc]

end Domain

end Polynomial
