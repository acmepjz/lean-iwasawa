/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.EventualClassNumberBridge
public import Iwasawalib.NumberTheory.ZpExtension.SelectedInertiaCover
public import Iwasawalib.NumberTheory.AbsoluteValue.Normalization
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

@[expose] public section

open NumberField IsDedekindDomain

namespace AbsoluteValue

variable {F L E : Type*} [Field F] [Field L] [Algebra F L]

/-- Equivalent absolute values define the same inertia subgroup. -/
theorem inertiaSubgroup_eq_of_equiv
    {v w : AbsoluteValue L ℝ} (h : v.IsEquiv w) :
    v.inertiaSubgroup F = w.inertiaSubgroup F := by
  ext σ
  simp only [mem_inertiaSubgroup_iff]
  rw [decompositionSubgroup_eq_of_equiv (F := F) h]
  constructor <;> rintro ⟨hd, hrest⟩ <;> refine ⟨hd, ?_⟩
  · simpa only [isNonarchimedean_iff_of_equiv h, h.le_one_iff, h.lt_one_iff] using hrest
  · simpa only [← isNonarchimedean_iff_of_equiv h, ← h.le_one_iff,
      ← h.lt_one_iff] using hrest

/-- Normalizing an absolute value does not change its inertia subgroup. -/
theorem inertiaSubgroup_normalization [CharZero L] (v : AbsoluteValue L ℝ) :
    v.normalization.inertiaSubgroup F = v.inertiaSubgroup F := by
  exact inertiaSubgroup_eq_of_equiv v.isEquiv_normalization.symm

/-- Equivalence remains sufficient after restriction along an injective field homomorphism. -/
theorem inertiaSubgroup_comp_eq_of_equiv
    [Field E] [Algebra F E] {f : E →+* L} (hf : Function.Injective f)
    {v w : AbsoluteValue L ℝ} (h : v.IsEquiv w) :
    (v.comp (f := f) hf).inertiaSubgroup F =
      (w.comp (f := f) hf).inertiaSubgroup F := by
  exact inertiaSubgroup_eq_of_equiv (h.comp hf)

end AbsoluteValue

namespace NumberField

/-- A normalized nonarchimedean absolute value determines a unique finite-place class. -/
theorem existsUnique_heightOneSpectrum_adicAbv_isEquiv
    {F : Type*} [Field F] [NumberField F]
    (v : AbsoluteValue F ℝ) [v.IsNormalized]
    (hna : IsNonarchimedean v) :
    ∃! q : HeightOneSpectrum (𝓞 F),
      v.IsEquiv (HeightOneSpectrum.adicAbv F q) := by
  let V := (v.toValuation hna).valuationSubring
  have hle (x : 𝓞 F) : v (x : F) ≤ 1 := by
    have hxZ : IsIntegral ℤ (x : F) := x.isIntegral_coe
    have hx : IsIntegral V (x : F) := hxZ.tower_top
    rw [IsIntegrallyClosedIn.isIntegral_iff] at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    change v (y : F) ≤ 1
    exact_mod_cast y.2
  let i : 𝓞 F →+* V := (algebraMap (𝓞 F) F).codRestrict V fun x => by
    change (v.toValuation hna) (x : F) ≤ 1
    exact_mod_cast hle x
  let Q : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal V).comap i
  have hQmem (x : 𝓞 F) : x ∈ Q ↔ v (x : F) < 1 := by
    rw [Ideal.mem_comap, Valuation.mem_maximalIdeal_iff]
    rfl
  have hQprime : Q.IsPrime := Ideal.comap_isPrime i _
  have hQne : Q ≠ ⊥ := by
    have hp : v.adic.Prime :=
      v.prime_adic_of_isAlgebraic v.isNontrivial_of_isNormalized hna
    have hvp : v (v.adic : F) < 1 := by
      rw [v.apply_adic_eq_inv_of_isNormalized]
      rw [inv_lt_one₀ (by exact_mod_cast hp.pos)]
      exact_mod_cast hp.one_lt
    have hmem : (v.adic : 𝓞 F) ∈ Q := (hQmem _).2 (by exact_mod_cast hvp)
    intro hbot
    rw [hbot, Ideal.mem_bot] at hmem
    exact hp.ne_zero (by exact_mod_cast hmem)
  let q : HeightOneSpectrum (𝓞 F) := ⟨Q, hQprime, hQne⟩
  have hq : v.IsEquiv (HeightOneSpectrum.adicAbv F q) := by
    have hsub : HeightOneSpectrum.valuationSubringAtPrime F q ≤ V := by
      rintro x ⟨a, s, hs, rfl⟩
      have hsle : v (s : F) ≤ 1 := hle s
      have hsnotlt : ¬v (s : F) < 1 := by
        intro hslt
        exact hs (show s ∈ Q from (hQmem s).2 hslt)
      have hseq : v (s : F) = 1 := le_antisymm hsle (not_lt.mp hsnotlt)
      rw [Valuation.mem_valuationSubring_iff]
      change v ((a : F) * (s : F)⁻¹) ≤ 1
      rw [map_mul, map_inv₀, hseq, inv_one, mul_one]
      exact hle a
    have hVne : V ≠ ⊤ := by
      rw [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
      rw [Valuation.isNontrivial_iff_exists_lt_one]
      have hp : v.adic.Prime :=
        v.prime_adic_of_isAlgebraic v.isNontrivial_of_isNormalized hna
      refine ⟨v.adic, by exact_mod_cast hp.ne_zero, ?_⟩
      have hvp : v (v.adic : F) < 1 := by
        rw [v.apply_adic_eq_inv_of_isNormalized]
        exact (inv_lt_one₀ (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_lt)
      exact_mod_cast hvp
    have hVeq : HeightOneSpectrum.valuationSubringAtPrime F q = V :=
      ValuationSubring.eq_of_le_of_ne_top _ hsub hVne
    have hval : (v.toValuation hna).IsEquiv (q.valuation F) := by
      rw [Valuation.isEquiv_iff_valuationSubring,
        ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (K := F) q, hVeq]
    rw [AbsoluteValue.isEquiv_iff_lt_one_iff]
    intro x
    have hx := hval.lt_one_iff_lt_one (x := x)
    rw [HeightOneSpectrum.adicAbv_def]
    have hto :
        (↑(WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero q)
          ((q.valuation F) x)) : ℝ) < 1 ↔ (q.valuation F) x < 1 := by
      exact_mod_cast WithZeroMulInt.toNNReal_lt_one_iff
        (HeightOneSpectrum.one_lt_absNorm_nnreal q) (m := (q.valuation F) x)
    rw [hto]
    constructor
    · intro hvx
      exact hx.mp (by exact_mod_cast hvx)
    · intro hqx
      exact_mod_cast hx.mpr hqx
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply HeightOneSpectrum.ext
  ext x
  rw [show x ∈ q.asIdeal ↔ v (x : F) < 1 from hQmem x]
  rw [hq'.lt_one_iff]
  rw [← FinitePlace.norm_embedding]
  exact (FinitePlace.norm_lt_one_iff_mem F q' x).symm

end NumberField
