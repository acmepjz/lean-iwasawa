/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.GlobalPowerIndex

@[expose] public section

/-!
# `∏_{v ∈ S} [K_v^× : (K_v^×)^n] = n ^ #S · (∏_{v ∈ S} #μ_n(K_v)) · n ^ [K : ℚ]`

`Iwasawalib/NumberTheory/LocalCFT/UnitPowerIndex.lean` computes the local power index at one
finite place in the form

`[K_v^× : (K_v^×)^n] = n · #μ_n(K_v) · q_v ^ (v_p(n) · e_v)`,

which mentions a choice of residue characteristic `p` and the absolute ramification index
`e_v`.  `Iwasawalib/NumberTheory/CFT/GlobalPowerIndex.lean` supplies the two dictionary lemmas
`NumberField.ord_natCast_eq` (`ord_v(n) = v_p(n) · e_v`) and
`NumberField.card_residueField_adicCompletionIntegers` (`q_v = N(v)`), together with the product
formula `NumberField.prod_absNorm_pow_ord_natCast` (`∏_{v ∈ S} N(v) ^ ord_v(n) = n ^ [K : ℚ]`),
but it stops short of assembling them.  This file does the assembly; the two statements below
are the ones the module docstring of `GlobalPowerIndex.lean` advertises under these names but
does not contain.

## Main statements

* `NumberField.ord_eq_of_valued_adicCompletion_natCast` : `v p = exp (-e)` in the completion is
  `ord_v(p) = e` globally.
* `NumberField.powIndex_adicCompletion_units_eq_absNorm_pow_ord` :
  `[K_v^× : (K_v^×)^n] = n · #μ_n(K_v) · N(v) ^ ord_v(n)`.  The right-hand side no longer
  mentions a choice of residue characteristic or a ramification index.
* `NumberField.prod_powIndex_adicCompletion_units` :
  `∏_{v ∈ S} [K_v^× : (K_v^×)^n] = n ^ #S · (∏_{v ∈ S} #μ_n(K_v)) · n ^ [K : ℚ]`, for every
  finite `S` containing every place at which `n` has nonzero order.

* `NumberField.card_rootsOfUnity_integers_of_isPrimitiveRoot` : `#μ_n(K_v) = n` when `K`
  contains a primitive `n`-th root of unity.
* `NumberField.prod_powIndex_adicCompletion_units_of_isPrimitiveRoot` : in that case the
  product is `n ^ (2 · #S) · n ^ [K : ℚ]`.

Everything here is unconditional.  Note that `#μ_n(K_v)` is the number of `n`-th roots of unity
of the *valuation ring* `O_v`, which is how `UnitPowerIndex` states it; every root of unity is a
unit, so this is `#μ_n(K_v)`, but that identification is not proved here.

**The products are over finite places only.**  In Chevalley's count `S` also contains the
archimedean places, whose local indices `[K_v^× : (K_v^×)^n]` are not computed in this
repository; the remaining factor `n ^ [K : ℚ]` here is what they have to cancel against (by the
product formula `∏_{v ∣ ∞} ‖n‖_v = n ^ [K : ℚ]`).
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero LocalCFT

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem ord_eq_of_valued_adicCompletion_natCast {p e : ℕ}
    (hpv : (Valued.v ((p : v.adicCompletion K)) : ℤᵐ⁰) = exp (-(e : ℤ))) :
    v.ord K ((p : K)) = e := by
  have hcast : ((p : v.adicCompletion K)) = algebraMap K (v.adicCompletion K) ((p : K)) :=
    (map_natCast (algebraMap K (v.adicCompletion K)) p).symm
  have hval : (Valued.v ((p : v.adicCompletion K)) : ℤᵐ⁰) = v.valuation K ((p : K)) := by
    rw [hcast]
    exact valuedAdicCompletion_eq_valuation' (v := v) ((p : K))
  rw [ord, ← hval, hpv, WithZero.log_exp, neg_neg]

/-- The local power index at `v`, with the residue cardinality replaced by the absolute norm
`N(v)` and the exponent by `ord_v(n)`. -/
theorem powIndex_adicCompletion_units_eq_absNorm_pow_ord {n : ℕ} (hn : n ≠ 0) :
    PowerIndex.powIndex n (Additive (v.adicCompletion K)ˣ)
      = n * (Nat.card (rootsOfUnity n (LocalCFT.integers (F := v.adicCompletion K)))
        * Ideal.absNorm v.asIdeal ^ (v.ord K ((n : K))).toNat) := by
  obtain ⟨p, hp, hpv⟩ := HeightOneSpectrum.exists_prime_natCast_mem v
  obtain ⟨e, he1, hpe⟩ := exists_valued_natCast_eq_exp v hpv hp.pos.ne'
  have hord : v.ord K ((n : K)) = (n.factorization p : ℤ) * e :=
    ord_natCast_eq v hp hpv (ord_eq_of_valued_adicCompletion_natCast v hpe) hn
  have hexp : (v.ord K ((n : K))).toNat = n.factorization p * e := by
    rw [hord]; omega
  have hcard : Nat.card (IsLocalRing.ResidueField (LocalCFT.integers (F := v.adicCompletion K)))
      = Ideal.absNorm v.asIdeal := card_residueField_adicCompletionIntegers v
  rw [powIndex_adicCompletion_units_of_ne_zero v hp he1 hpe hn, hcard, hexp]

/-- **`#μ_n(K_v) = n` when `K` contains a primitive `n`-th root of unity.**

A root of unity has valuation `1`, so it lies in the valuation ring of the completion, and it
stays primitive there because `K → K_v` and `O_v → K_v` are injective. -/
theorem card_rootsOfUnity_integers_of_isPrimitiveRoot {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) :
    Nat.card (rootsOfUnity n (LocalCFT.integers (F := v.adicCompletion K))) = n := by
  have hζ' : IsPrimitiveRoot (algebraMap K (v.adicCompletion K) ζ) n :=
    hζ.map_of_injective (algebraMap K (v.adicCompletion K)).injective
  have hval : (Valued.v (algebraMap K (v.adicCompletion K) ζ) : ℤᵐ⁰) ≤ 1 := by
    have hpow : (algebraMap K (v.adicCompletion K) ζ) ^ n = 1 := hζ'.pow_eq_one
    have h1 : (Valued.v (algebraMap K (v.adicCompletion K) ζ) : ℤᵐ⁰) ^ n = 1 := by
      rw [← map_pow, hpow, map_one]
    by_contra hcon
    rw [not_le] at hcon
    have : (1 : ℤᵐ⁰) < (Valued.v (algebraMap K (v.adicCompletion K) ζ) : ℤᵐ⁰) ^ n :=
      one_lt_pow₀ hcon (NeZero.ne n)
    rw [h1] at this
    exact lt_irrefl _ this
  set z : LocalCFT.integers (F := v.adicCompletion K) :=
    ⟨algebraMap K (v.adicCompletion K) ζ, hval⟩ with hz
  have hzp : IsPrimitiveRoot z n :=
    hζ'.of_map_of_injective (f := (LocalCFT.integers (F := v.adicCompletion K)).subtype)
      Subtype.val_injective
  exact hzp.card_rootsOfUnity

/-- **The product over `S` of the local power indices.** -/
theorem prod_powIndex_adicCompletion_units {n : ℕ} (hn : n ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : ∀ w : HeightOneSpectrum (𝓞 K), w.ord K ((n : K)) ≠ 0 → w ∈ S) :
    ∏ w ∈ S, PowerIndex.powIndex n (Additive (w.adicCompletion K)ˣ)
      = n ^ S.card
        * (∏ w ∈ S, Nat.card (rootsOfUnity n (LocalCFT.integers (F := w.adicCompletion K))))
        * n ^ (Module.finrank ℚ K) := by
  rw [Finset.prod_congr rfl fun w _ ↦ powIndex_adicCompletion_units_eq_absNorm_pow_ord w hn,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    prod_absNorm_pow_ord_natCast hn hS]
  ring

/-- **`∏_{v ∈ S} [K_v^× : (K_v^×)^n] = n ^ (2 · #S) · n ^ [K : ℚ]`** when `K` contains a
primitive `n`-th root of unity.

This is the local factor of Chevalley's count, for `n = ℓ` and `μ_ℓ ⊆ K`; the `S`-unit factor
that it is compared with is `NumberField.powIndex_sUnit_of_isPrimitiveRoot`. -/
theorem prod_powIndex_adicCompletion_units_of_isPrimitiveRoot {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : ∀ w : HeightOneSpectrum (𝓞 K), w.ord K ((n : K)) ≠ 0 → w ∈ S) :
    ∏ w ∈ S, PowerIndex.powIndex n (Additive (w.adicCompletion K)ˣ)
      = n ^ (2 * S.card) * n ^ (Module.finrank ℚ K) := by
  rw [prod_powIndex_adicCompletion_units (NeZero.ne n) hS,
    Finset.prod_congr rfl fun w _ ↦ card_rootsOfUnity_integers_of_isPrimitiveRoot w hζ,
    Finset.prod_const, two_mul, pow_add]

end NumberField
