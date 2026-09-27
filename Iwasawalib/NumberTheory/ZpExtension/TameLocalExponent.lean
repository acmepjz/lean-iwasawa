/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.BasePrimeRamification
public import Iwasawalib.NumberTheory.LocalCFT.PlaceDedekind
public import Iwasawalib.NumberTheory.LocalCFT.TameInertiaOrder

@[expose] public section

/-!
# A `ℤₚ`-extension is unramified outside `p`: the local exponent input

`MvZpExtension.exists_ramifiedBasePlaceData`
(`Iwasawalib/NumberTheory/ZpExtension/BasePrimeRamification.lean`) packages the ramified base
primes of a `ℤₚ`-extension `K∞ / K` under one hypothesis `hlocal`: at every prime `q` of `𝓞 K`
with `p ∉ q` and every place `v` of `K∞` over the `q`-adic place, some `M ≠ 0` kills the image
of the inertia subgroup `I_v(K∞/K)` in every layer `Gal(Kₙ/K)`.  This file proves `hlocal`
unconditionally (`MvZpExtension.exists_restrictNormalHom_pow_eq_one_of_liesOver_adicAbv`), so
the base-prime package exists with no hypothesis
(`MvZpExtension.exists_ramifiedBasePlaceData_unconditional`).

This is the finite-place half of the blueprint's Proposition `p:unr-outside-p`
(Washington, Proposition 13.2; Iwasawa, Lemma 7.1): a prime not above `p` is unramified in
`K∞ / K`.  The blueprint proves it by local class field theory
(`Gal(K_ℓ^ab / K_ℓ^unr) ≅ 𝓞_ℓ^×` has no `ℤₚ`-quotient for `ℓ ≠ p`).  The formal proof is the
**tame** one instead: the restriction of `σ ∈ I_v(K∞/K)` to the abelian `p`-power layer `Kₙ` is
an inertia element of `p`-power order at a prime `w | q` with `p ∉ w`, so it is tame, and
`NumberField.pow_card_quotient_sub_one_eq_one_of_mem_inertia`
(`Iwasawalib/NumberTheory/LocalCFT/TameInertiaOrder.lean`) kills it by `M = N(q) - 1`, a
number independent of `n` and `σ`.  The archimedean half of the proposition is
`MvZpExtension.inertiaSubgroup_eq_bot_of_archimedean`.

## Main statements

* `NumberField.exists_heightOneSpectrum_isEquiv_of_liesOver_adicAbv`: a place of `E` over the
  `q`-adic place of `K` restricts, on an intermediate number field `L`, to an equivalent of the
  `w`-adic place of a prime `w` of `𝓞 L` lying over `q`.
* `NumberField.natCast_pow_notMem_of_liesOver`: `N ∉ q` implies `N ^ k ∉ w` for `w | q`.
* `MvZpExtension.restrictNormalHom_mem_inertia_of_mem_inertiaSubgroup`: the restriction of an
  element of `I_v(K∞/K)` to `Kₙ` lies in Mathlib's inertia group of the corresponding prime `w`.
* `MvZpExtension.restrictNormalHom_pow_finrank_eq_one`: `Gal(Kₙ/K)` has exponent dividing
  `p ^ (n · #ι)`.
* `MvZpExtension.exists_restrictNormalHom_pow_eq_one_of_liesOver_adicAbv`: **`hlocal`**, the
  local exponent input at primes `q ∤ p`.
* `MvZpExtension.exists_ramifiedBasePlaceData_unconditional`: the base-prime package
  `MvZpExtension.RamifiedBasePlaceData` exists unconditionally.
-/

open NumberField IsDedekindDomain

namespace NumberField

/-- A place `v` of `E` lying over the `q`-adic place of `K` restricts, on an intermediate number
field `L`, to (an equivalent of) the `w`-adic place for some prime `w` of `𝓞 L` lying over
`q`. -/
theorem exists_heightOneSpectrum_isEquiv_of_liesOver_adicAbv
    {K L E : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    (q : HeightOneSpectrum (𝓞 K)) (v : AbsoluteValue E ℝ)
    [v.LiesOver (NumberField.HeightOneSpectrum.adicAbv K q)] :
    ∃ w : HeightOneSpectrum (𝓞 L),
      (v.comp (algebraMap L E).injective).IsEquiv (NumberField.HeightOneSpectrum.adicAbv L w) ∧
      w.asIdeal.LiesOver q.asIdeal := by
  set vL : AbsoluteValue L ℝ := v.comp (algebraMap L E).injective with hvL
  -- (i) the restriction of `vL` to `K` is the `q`-adic absolute value
  have hcomp : vL.comp (algebraMap K L).injective =
      NumberField.HeightOneSpectrum.adicAbv K q := by
    rw [← AbsoluteValue.LiesOver.comp_eq v (NumberField.HeightOneSpectrum.adicAbv K q)]
    ext x
    change v (algebraMap L E (algebraMap K L x)) = v (algebraMap K E x)
    rw [← IsScalarTower.algebraMap_apply K L E]
  -- (ii) `vL` is nontrivial and nonarchimedean
  have hnt : vL.IsNontrivial := by
    apply vL.isNontrivial_of_isNontrivial_comp (f := algebraMap K L)
    rw [hcomp]
    exact NumberField.isNontrivial_adicAbv q
  have hna : IsNonarchimedean vL := by
    rw [← vL.isNonarchimedean_comp_iff (algebraMap K L), hcomp]
    exact NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K q
  -- (iii) normalise and pick the prime
  have hvn_norm : vL.normalization.IsNormalized :=
    vL.isNormalized_normalization_of_isNontrivial_of_isAlgebraic hnt
  have hvn_na : IsNonarchimedean vL.normalization :=
    (AbsoluteValue.isNonarchimedean_iff_of_equiv vL.isEquiv_normalization).1 hna
  letI : vL.normalization.IsNormalized := hvn_norm
  obtain ⟨w, hw, _⟩ :=
    NumberField.existsUnique_heightOneSpectrum_adicAbv_isEquiv vL.normalization hvn_na
  have hvw : vL.IsEquiv (NumberField.HeightOneSpectrum.adicAbv L w) :=
    vL.isEquiv_normalization.trans hw
  refine ⟨w, hvw, ⟨?_⟩⟩
  -- (iv) `w` lies over `q`
  ext x
  rw [Ideal.mem_under,
    ← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) q x,
    ← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) w
      (algebraMap (𝓞 K) (𝓞 L) x),
    ← NumberField.adicAbv_lt_one_iff, ← NumberField.adicAbv_lt_one_iff, ← hvw.lt_one_iff,
    ← hcomp]
  have hx : algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) x) =
      algebraMap K L (algebraMap (𝓞 K) K x) := by
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      ← IsScalarTower.algebraMap_apply (𝓞 K) K L]
  change vL (algebraMap K L (algebraMap (𝓞 K) K x)) < 1 ↔
    vL (algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) x)) < 1
  rw [hx]

/-- A natural number outside a prime `q` of `𝓞 K` stays outside every prime `w` of `𝓞 L` lying
over `q`, and so do all its powers. -/
theorem natCast_pow_notMem_of_liesOver
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (q : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver q.asIdeal]
    {N : ℕ} (hN : (N : 𝓞 K) ∉ q.asIdeal) (k : ℕ) :
    ((N ^ k : ℕ) : 𝓞 L) ∉ w.asIdeal := by
  intro h
  rw [Nat.cast_pow] at h
  have h1 : (N : 𝓞 L) ∈ w.asIdeal := w.isPrime.mem_of_pow_mem k h
  apply hN
  rw [Ideal.over_def w.asIdeal q.asIdeal, Ideal.mem_under, map_natCast]
  exact h1

end NumberField

namespace MvZpExtension

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]
variable (H : MvZpExtension p ι K Kinf)

/-- Restricting an element of the inertia subgroup `I_v(K∞/K)` to the layer `Kₙ` lands in
Mathlib's inertia group `w.asIdeal.inertia Gal(Kₙ/K)` of any prime `w` of `𝓞 Kₙ` whose adic
absolute value is equivalent to the restriction `v|Kₙ`. -/
theorem restrictNormalHom_mem_inertia_of_mem_inertiaSubgroup
    (v : AbsoluteValue Kinf ℝ) (n : ℕ) (w : HeightOneSpectrum (𝓞 (H.Kn n)))
    (hw : (v.comp (algebraMap (H.Kn n) Kinf).injective).IsEquiv
      (NumberField.HeightOneSpectrum.adicAbv (H.Kn n) w))
    {σ : H.Γ} (hσ : σ ∈ v.inertiaSubgroup K) :
    AlgEquiv.restrictNormalHom (H.Kn n) σ ∈ w.asIdeal.inertia ((H.Kn n) ≃ₐ[K] (H.Kn n)) := by
  haveI : v.LiesOver (v.comp (algebraMap (H.Kn n) Kinf).injective) := ⟨rfl⟩
  have hmem : AlgEquiv.restrictNormalHom (H.Kn n) σ ∈
      (v.inertiaSubgroup K).map (AlgEquiv.restrictNormalHom (H.Kn n)) :=
    Subgroup.mem_map_of_mem _ hσ
  rw [AbsoluteValue.map_inertiaSubgroup_eq_of_liesOver K
    (v.comp (algebraMap (H.Kn n) Kinf).injective) v,
    AbsoluteValue.inertiaSubgroup_eq_of_equiv hw,
    NumberField.inertiaSubgroup_eq_inertia] at hmem
  exact hmem

omit [NumberField K] in
/-- `Gal(Kₙ/K)` has order `p ^ (n · #ι)` (`MvZpExtension.finrank_Kn`), so the restriction of
any `σ ∈ Γ` to `Kₙ` is killed by that power of `p`. -/
theorem restrictNormalHom_pow_finrank_eq_one (n : ℕ) (σ : H.Γ) :
    AlgEquiv.restrictNormalHom (H.Kn n) σ ^ (p ^ (n * Nat.card ι)) = 1 := by
  rw [← H.finrank_Kn n, ← IsGalois.card_aut_eq_finrank K (H.Kn n)]
  exact pow_card_eq_one'

/-- **Prop. p:unr-outside-p, local form.** At a prime `q ∤ p`, `N(q) - 1` kills the image of the
inertia subgroup `I_v(K∞/K)` in every layer `Kₙ`, uniformly in `n`: inertia at `q` in the abelian
`p`-power layer `Kₙ/K` is tame, and `LocalCFT.orderOf_dvd_sub_one` gives `e ∣ N(q) - 1`.

Equivalently, `I_v(K∞/K) = ⊥` for every prime `q ∤ p` and every place `v` of `K∞` lying over
the `q`-adic place: for a given `v` the conclusion forces `I_v(K∞/K) = ⊥` by
`MvZpExtension.inertiaSubgroup_eq_bot_of_fixes_Kn` (this is how
`MvZpExtension.ramified_place_liesOver_basePrimeAbove_p` uses it), and conversely it holds
trivially, with `M = 1`, when `I_v(K∞/K) = ⊥`. -/
theorem exists_restrictNormalHom_pow_eq_one_of_liesOver_adicAbv :
    ∀ (q : HeightOneSpectrum (𝓞 K)),
      (p : 𝓞 K) ∉ q.asIdeal →
      ∀ (v : AbsoluteValue Kinf ℝ),
        [v.LiesOver (HeightOneSpectrum.adicAbv K q)] →
        ∃ M : ℕ, M ≠ 0 ∧
          ∀ n σ, σ ∈ v.inertiaSubgroup K →
            AlgEquiv.restrictNormalHom (H.Kn n) (σ ^ M) = 1 := by
  intro q hq v _
  refine ⟨Nat.card (𝓞 K ⧸ q.asIdeal) - 1,
    Nat.sub_ne_zero_of_lt (NumberField.one_lt_card_quotient q), ?_⟩
  intro n σ hσ
  obtain ⟨w, hw, hwq⟩ := NumberField.exists_heightOneSpectrum_isEquiv_of_liesOver_adicAbv
    (L := H.Kn n) q v
  haveI := hwq
  have hmem := H.restrictNormalHom_mem_inertia_of_mem_inertiaSubgroup v n w hw hσ
  have hpow := H.restrictNormalHom_pow_finrank_eq_one n σ
  have hp := NumberField.natCast_pow_notMem_of_liesOver q w hq (n * Nat.card ι)
  rw [map_pow]
  exact NumberField.pow_card_quotient_sub_one_eq_one_of_mem_inertia q w hmem hpow hp

/-- **The finite base-prime package exists unconditionally.**  This is
`MvZpExtension.exists_ramifiedBasePlaceData` with its hypothesis `hlocal` discharged by
`MvZpExtension.exists_restrictNormalHom_pow_eq_one_of_liesOver_adicAbv`.

The index `base` of the package produced here may be empty, as the docstring of
`MvZpExtension.RamifiedBasePlaceData` allows: this theorem does not say that any prime ramifies.
Nonemptiness is `MvZpExtension.RamifiedBasePlaceData.nonempty_orbitIndex`, which is
`sorry`-tainted through `MvZpExtension.exists_inertiaSubgroup_ne_bot`. -/
theorem exists_ramifiedBasePlaceData_unconditional [Unique ι] :
    Nonempty (RamifiedBasePlaceData H) :=
  H.exists_ramifiedBasePlaceData H.exists_restrictNormalHom_pow_eq_one_of_liesOver_adicAbv

end MvZpExtension
