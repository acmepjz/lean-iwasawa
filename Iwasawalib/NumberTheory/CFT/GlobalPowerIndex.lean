/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.UnitPowerIndex
public import Iwasawalib.NumberTheory.CFT.SUnitSpan
public import Mathlib.NumberTheory.NumberField.ProductFormula

@[expose] public section

/-!
# The product over `S` of the local power indices

`Iwasawalib/NumberTheory/LocalCFT/UnitPowerIndex.lean` computes, at one finite place `v` of a
number field `K`,

`[K_v^× : (K_v^×)^n] = n · #μ_n(K_v) · q_v ^ (v_p(n) · e_v)`,

where `p` is the residue characteristic at `v`, `e_v = ord_v(p)` and `q_v` is the residue field
cardinality.  The last factor is `|n|_v⁻¹`.  Chevalley's count needs the **product** of these
over a finite set `S` of places containing every place above `n`, and the point of the exercise
is that the third factors multiply to a single power of `n`:

`∏_{v ∈ S} q_v ^ ord_v(n) = n ^ [K : ℚ]`,

by the product formula, because `|n|_v = 1` off `S` and the archimedean absolute values of `n`
multiply to `n ^ [K : ℚ]`.  So the whole local contribution is

`∏_{v ∈ S} [K_v^× : (K_v^×)^n] = n ^ #S · (∏_{v ∈ S} #μ_n(K_v)) · n ^ [K : ℚ]`,

which is `NumberField.prod_powIndex_adicCompletion_units`.  This is the factor that Chevalley's
argument compares with the `S`-unit index `[E_S : E_S^n] = n ^ #S` of
`Iwasawalib/NumberTheory/CFT/SUnitPowerIndex.lean`.

## Main statements

* `IsDedekindDomain.HeightOneSpectrum.exists_prime_natCast_mem` : the residue characteristic.
* `NumberField.ord_natCast_eq` : `ord_v(n) = v_p(n) · e_v`, the bridge between the exponent that
  `UnitPowerIndex` produces and the exponent that the product formula consumes.
* `NumberField.card_residueField_adicCompletionIntegers` :
  `#(𝒪_v/𝔪_v) = N(v)`, the bridge between the local residue field and the ideal norm.
* `NumberField.prod_absNorm_pow_ord_natCast` : **`∏_{v ∈ S} N(v) ^ ord_v(n) = n ^ [K : ℚ]`** for
  every finite `S` containing the places above `n`.

Everything here is unconditional.

This list previously also advertised `NumberField.powIndex_adicCompletion_units_eq_absNorm_pow_ord`
and `NumberField.prod_powIndex_adicCompletion_units` as main statements of this file, when
neither declaration existed anywhere in the repository.  They are now proved, in
`Iwasawalib/NumberTheory/CFT/LocalPowerIndexProduct.lean`, which is where they belong: they
consume both this file's `ord`/`absNorm` bridges and `LocalCFT/UnitPowerIndex.lean`
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- `ord_v (x ^ a) = a · ord_v x`. -/
theorem ord_pow {v : HeightOneSpectrum R} {x : K} (hx : x ≠ 0) (a : ℕ) :
    v.ord K (x ^ a) = a * v.ord K x := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ, ord_mul (pow_ne_zero a hx) hx, ih]; push_cast; ring

variable (K) in
/-- **The residue characteristic.**  Every finite place of a number field lies above a rational
prime.  Stated for an arbitrary Dedekind domain with finite residue fields. -/
theorem exists_prime_natCast_mem (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    ∃ p : ℕ, p.Prime ∧ (p : R) ∈ v.asIdeal := by
  haveI : Fact (v.asIdeal.IsMaximal) := ⟨v.isMaximal⟩
  haveI : Field (R ⧸ v.asIdeal) := Ideal.Quotient.field _
  obtain ⟨p, hp⟩ := CharP.exists (R ⧸ v.asIdeal)
  haveI := hp
  have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite (R ⧸ v.asIdeal) p
  haveI : NeZero p := ⟨hp0⟩
  refine ⟨p, (CharP.char_is_prime_of_pos (R ⧸ v.asIdeal) p).out, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact (CharP.cast_eq_zero_iff (R ⧸ v.asIdeal) p p).2 dvd_rfl

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-! ## `ord_v` of a natural number -/

/-- A natural number prime to the residue characteristic has `ord_v = 0`. -/
theorem ord_natCast_eq_zero_of_coprime {p s : ℕ} (hpv : (p : 𝓞 K) ∈ v.asIdeal)
    (hs : Nat.Coprime s p) (hs0 : s ≠ 0) : v.ord K (s : K) = 0 := by
  have hcoe : (((s : 𝓞 K) : K)) = ((s : K)) := by push_cast; ring
  have hcop : IsCoprime ((s : 𝓞 K)) ((p : 𝓞 K)) := by
    have h : IsCoprime ((s : ℤ)) ((p : ℤ)) := Int.isCoprime_iff_gcd_eq_one.2 (by
      simpa [Int.gcd_natCast_natCast] using hs)
    simpa using h.map (algebraMap ℤ (𝓞 K))
  have hsmem : (s : 𝓞 K) ∉ v.asIdeal := by
    intro h
    obtain ⟨a, b, hab⟩ := hcop
    have hone : (1 : 𝓞 K) ∈ v.asIdeal := by
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hpv)
    exact (v.isMaximal.ne_top) (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)
  have h1 : v.valuation K (((s : 𝓞 K) : K)) = 1 := by
    refine le_antisymm (v.valuation_le_one (K := K) _) ?_
    by_contra hcon
    rw [not_le] at hcon
    exact hsmem ((v.valuation_lt_one_iff_mem (K := K) _).1 hcon)
  rw [ord_eq_zero_iff (Nat.cast_ne_zero.2 hs0 : ((s : K)) ≠ 0), ← hcoe, h1]

/-- **`ord_v(n) = v_p(n) · e_v`.**  The exponent produced by the local power-index computation
is the `ℤ`-valued adic valuation of `n`. -/
theorem ord_natCast_eq {p e n : ℕ} (hp : p.Prime) (hpv : (p : 𝓞 K) ∈ v.asIdeal)
    (he : v.ord K ((p : K)) = e) (hn : n ≠ 0) :
    v.ord K ((n : K)) = (n.factorization p : ℤ) * e := by
  set a := n.factorization p with ha
  set s := n / p ^ a with hs
  have hsplit : p ^ a * s = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsplit
    exact hn hsplit.symm
  have hcop : Nat.Coprime s p := (Nat.coprime_ordCompl hp hn).symm
  have hpK : ((p : K)) ≠ 0 := Nat.cast_ne_zero.2 hp.pos.ne'
  have hsK : ((s : K)) ≠ 0 := Nat.cast_ne_zero.2 hs0
  have hcast : ((n : K)) = ((p : K)) ^ a * ((s : K)) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, hsplit]
  rw [hcast, ord_mul (pow_ne_zero a hpK) hsK, ord_pow hpK,
    ord_natCast_eq_zero_of_coprime v hpv hcop hs0, he, add_zero]

/-- `ord_v(n) ≥ 0` for a natural number `n`. -/
theorem ord_natCast_nonneg (n : ℕ) : 0 ≤ v.ord K ((n : K)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hcoe : (((n : 𝓞 K) : K)) = ((n : K)) := by push_cast; ring
  have hle : v.valuation K ((n : K)) ≤ 1 := by rw [← hcoe]; exact v.valuation_le_one (K := K) _
  have h0 : v.valuation K ((n : K)) ≠ 0 :=
    valuation_ne_zero (Nat.cast_ne_zero.2 hn)
  rw [ord, neg_nonneg, ← WithZero.exp_zero (M := ℤ)] at *
  rw [← WithZero.exp_log h0] at hle
  exact_mod_cast (WithZero.exp_le_exp).1 hle

/-! ## The residue field of the completion -/

/-- **`#(𝒪_v / 𝔪_v) = N(v)`.**  The residue field of the completion at `v` has the same
cardinality as the residue field `𝓞_K / v` of the global ring, which is the absolute norm of
`v`. -/
theorem card_residueField_adicCompletionIntegers :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
      = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (quotientEquivResidueField K v).toEquiv).symm

/-! ## The product over the finite places -/

variable (K) in
/-- The local factor `N(v) ^ ord_v(x)`, as a real number; `|x|_v⁻¹`. -/
def absNormPowOrd (x : K) (v : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (Ideal.absNorm v.asIdeal : ℝ) ^ (v.ord K x)

theorem absNormPowOrd_eq_inv_adicAbv {x : K} (hx : x ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    absNormPowOrd K x v = (NumberField.HeightOneSpectrum.adicAbv K v x)⁻¹ := by
  rw [absNormPowOrd, adicAbv_eq_zpow v hx, ← zpow_neg, neg_neg]

theorem absNormPowOrd_ne_one_iff {x : K} (v : HeightOneSpectrum (𝓞 K)) :
    absNormPowOrd K x v ≠ 1 ↔ v.ord K x ≠ 0 := by
  have h1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  rw [absNormPowOrd, ne_eq, ne_eq, zpow_eq_one_iff_right₀ (le_of_lt (by positivity)) h1.ne']

variable (K) in
/-- **The product formula, in the form `∏_v N(v) ^ ord_v(x) = |N_{K/ℚ}(x)|`.**  The product is
over *all* finite places; all but finitely many factors are `1`. -/
theorem finprod_absNormPowOrd {x : K} (hx : x ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), absNormPowOrd K x v = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have hprod : ∏ᶠ v : HeightOneSpectrum (𝓞 K), NumberField.HeightOneSpectrum.adicAbv K v x
      = ((|Algebra.norm ℚ x|⁻¹ : ℚ) : ℝ) := by
    rw [← NumberField.FinitePlace.prod_eq_inv_abs_norm hx,
      ← finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm]
    refine finprod_congr fun v ↦ ?_
    rw [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply v x,
      NumberField.FinitePlace.norm_embedding]
  have h : ∏ᶠ v : HeightOneSpectrum (𝓞 K), absNormPowOrd K x v
      = (∏ᶠ v : HeightOneSpectrum (𝓞 K), NumberField.HeightOneSpectrum.adicAbv K v x)⁻¹ := by
    rw [← finprod_inv_distrib]
    exact finprod_congr fun v ↦ absNormPowOrd_eq_inv_adicAbv hx v
  rw [h, hprod]
  push_cast
  rw [inv_inv]

/-- **`∏_{v ∈ S} N(v) ^ ord_v(n) = n ^ [K : ℚ]`.**

For a nonzero natural number `n` and any finite set `S` of finite places containing every place
at which `n` has positive order — in particular any `S` containing the places above `n` — the
local factors `|n|_v⁻¹` multiply to `n ^ [K : ℚ]`.  This is the cancellation that makes
Chevalley's count come out. -/
theorem prod_absNorm_pow_ord_natCast {n : ℕ} (hn : n ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.ord K ((n : K)) ≠ 0 → v ∈ S) :
    ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ (v.ord K ((n : K))).toNat
      = n ^ (Module.finrank ℚ K) := by
  have hx : ((n : K)) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hsupp : (Function.mulSupport (absNormPowOrd K ((n : K)))) ⊆ (S : Set _) := by
    intro v hv
    exact hS v ((absNormPowOrd_ne_one_iff v).1 hv)
  have hfin : ∏ v ∈ S, absNormPowOrd K ((n : K)) v = ((|Algebra.norm ℚ ((n : K))| : ℚ) : ℝ) := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ hsupp]
    exact finprod_absNormPowOrd K hx
  have hnorm : Algebra.norm ℚ ((n : K)) = (n : ℚ) ^ (Module.finrank ℚ K) := by
    rw [show ((n : K)) = algebraMap ℚ K ((n : ℚ)) by push_cast; ring, Algebra.norm_algebraMap]
  have h2 : ∏ v ∈ S, absNormPowOrd K ((n : K)) v
      = ∏ v ∈ S, ((Ideal.absNorm v.asIdeal : ℝ) ^ (v.ord K ((n : K))).toNat) :=
    Finset.prod_congr rfl fun v _ ↦ by
      rw [absNormPowOrd, ← zpow_natCast]
      congr 1
      exact (Int.toNat_of_nonneg (ord_natCast_nonneg v n)).symm
  rw [h2, hnorm] at hfin
  have hcast : ((∏ v ∈ S, Ideal.absNorm v.asIdeal ^ (v.ord K ((n : K))).toNat : ℕ) : ℝ)
      = ((n ^ (Module.finrank ℚ K) : ℕ) : ℝ) := by
    push_cast
    push_cast at hfin
    rw [hfin, abs_of_nonneg (by positivity)]
  exact_mod_cast hcast

end NumberField
