/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.Algebra.Module.ElementaryDivisors
public import Iwasawalib.RingTheory.IwasawaAlgebra.QuotientDistinguished
public import Iwasawalib.RingTheory.PseudoNull.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished

@[expose] public section

/-!
# The Iwasawa algebra is a two dimensional regular local ring

This file proves blueprint node `Lambda-is-reg-of-dim-2` in the form needed later: the Iwasawa
algebra `Λ = ℤ_p⟦X⟧` is a Noetherian local ring of Krull dimension `2` whose maximal ideal is
`(p, X)` and whose residue field is `𝔽_p`, in particular finite.

Together with `Module.isPseudoNull_iff_finite_of_ringKrullDim_eq_two` this yields blueprint
node `pseudo-null-criterion` (ii): a finitely generated `Λ`-module is pseudo-null if and only if
it is finite.

## Main results

* `IwasawaAlgebra.maximalIdeal_eq_span_pair`: `𝔪 = (p, X)`.
* `IwasawaAlgebra.card_quotient_maximalIdeal`: `#(Λ ⧸ 𝔪) = p`.
* `IwasawaAlgebra.ringKrullDim_eq_two`: `dim Λ = 2`.
* `IwasawaAlgebra.isPseudoNull_iff_finite`: **blueprint node `pseudo-null-criterion` (ii)**.
-/

open PowerSeries Polynomial

namespace IwasawaAlgebra

variable (p : ℕ) [Fact p.Prime]

/-- The maximal ideal of `Λ = ℤ_p⟦X⟧` is `(p, X)`. -/
theorem maximalIdeal_eq_span_pair :
    IsLocalRing.maximalIdeal ℤ_[p]⟦X⟧ =
      Ideal.span {(algebraMap ℤ_[p] ℤ_[p]⟦X⟧ (p : ℤ_[p])), (PowerSeries.X : ℤ_[p]⟦X⟧)} := by
  have hp : (algebraMap ℤ_[p] ℤ_[p]⟦X⟧ (p : ℤ_[p])) = PowerSeries.C (p : ℤ_[p]) := rfl
  refine le_antisymm (fun f hf ↦ ?_) ?_
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff] at hf
    have hc : PowerSeries.constantCoeff f ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
      IsLocalRing.mem_maximalIdeal _ |>.2 hf
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hc
    obtain ⟨a, ha⟩ := hc
    have hdvd : (PowerSeries.X : ℤ_[p]⟦X⟧) ∣ f - PowerSeries.C (a * (p : ℤ_[p])) := by
      rw [PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, ha, sub_self]
    obtain ⟨g, hg⟩ := hdvd
    have : f = PowerSeries.C a * PowerSeries.C (p : ℤ_[p]) + PowerSeries.X * g := by
      rw [← map_mul]
      linear_combination hg
    rw [this, hp]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        PowerSeries.isUnit_iff_constantCoeff, hp, PowerSeries.constantCoeff_C]
      exact fun h ↦ (PadicInt.prime_p (p := p)).not_unit h
    · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
      simp

/-- `X` is a distinguished polynomial of degree one at `(p)`. -/
theorem isDistinguishedAt_X :
    (Polynomial.X : Polynomial ℤ_[p]).IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p]) :=
  ⟨⟨fun {i} hi ↦ by
    rw [Polynomial.natDegree_X] at hi
    interval_cases i
    simp⟩, Polynomial.monic_X⟩

/-- The residue field of `Λ = ℤ_p⟦X⟧` has `p` elements. -/
theorem card_quotient_maximalIdeal :
    Nat.card (ℤ_[p]⟦X⟧ ⧸ IsLocalRing.maximalIdeal ℤ_[p]⟦X⟧) = p := by
  have h := (isDistinguishedAt_X p).card_quotient_span_pair (p : ℤ_[p])
  rw [Polynomial.natDegree_X, pow_one] at h
  have hX : ((Polynomial.X : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) = (PowerSeries.X : ℤ_[p]⟦X⟧) := by
    simp
  rw [hX] at h
  rw [maximalIdeal_eq_span_pair, h,
    show ((p : ℤ_[p])) = (p : ℤ_[p]) ^ 1 from (pow_one _).symm,
    PadicInt.card_quotient_span_pow 1, pow_one]

instance finite_residueField : Finite (IsLocalRing.ResidueField ℤ_[p]⟦X⟧) := by
  have h := card_quotient_maximalIdeal p
  have : Nat.card (IsLocalRing.ResidueField ℤ_[p]⟦X⟧) ≠ 0 := by
    rw [show Nat.card (IsLocalRing.ResidueField ℤ_[p]⟦X⟧) = p from h]
    exact (Fact.out : p.Prime).ne_zero
  exact (Nat.card_ne_zero.1 this).2

/-- **Blueprint node `Lambda-is-reg-of-dim-2`**: the Iwasawa algebra `Λ = ℤ_p⟦X⟧` has Krull
dimension `2`. -/
theorem ringKrullDim_eq_two : ringKrullDim ℤ_[p]⟦X⟧ = 2 := by
  refine le_antisymm ?_ ?_
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    have h1 := Ideal.height_le_spanRank_toENat (IsLocalRing.maximalIdeal ℤ_[p]⟦X⟧)
      (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]⟦X⟧).ne_top
    have h2 : (IsLocalRing.maximalIdeal ℤ_[p]⟦X⟧).spanRank ≤ 2 := by
      rw [maximalIdeal_eq_span_pair]
      refine (Submodule.spanRank_span_le_card _).trans ?_
      calc Cardinal.mk ({(algebraMap ℤ_[p] ℤ_[p]⟦X⟧ (p : ℤ_[p])),
            (PowerSeries.X : ℤ_[p]⟦X⟧)} : Set ℤ_[p]⟦X⟧)
          ≤ Cardinal.mk ({(PowerSeries.X : ℤ_[p]⟦X⟧)} : Set ℤ_[p]⟦X⟧) + 1 :=
            Cardinal.mk_insert_le
        _ ≤ 2 := by simp; norm_num
    have h3 : (IsLocalRing.maximalIdeal ℤ_[p]⟦X⟧).spanRank.toENat ≤ 2 := by
      simpa using OrderHom.monotone (Cardinal.toENat : Cardinal →o ℕ∞) h2
    have h4 : (IsLocalRing.maximalIdeal ℤ_[p]⟦X⟧).height ≤ 2 := h1.trans h3
    exact le_trans (WithBot.coe_le_coe.mpr h4) (by norm_num)
  · have := ringKrullDim_succ_le_ringKrullDim_powerseries (R := ℤ_[p])
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one ℤ_[p]] at this
    refine le_trans ?_ this
    norm_num

/-- **Blueprint node `pseudo-null-criterion` (ii)** for `Λ = ℤ_p⟦X⟧`: a finitely generated
`Λ`-module is pseudo-null if and only if it is finite. -/
theorem isPseudoNull_iff_finite (M : Type*) [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M]
    [Module.Finite ℤ_[p]⟦X⟧ M] : Module.IsPseudoNull ℤ_[p]⟦X⟧ M ↔ Finite M :=
  Module.isPseudoNull_iff_finite_of_ringKrullDim_eq_two _ _ (ringKrullDim_eq_two p)

variable {p}

/-- A pseudo-null finitely generated `Λ`-module is finite. -/
theorem finite_of_isPseudoNull (M : Type*) [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M]
    [Module.Finite ℤ_[p]⟦X⟧ M] [Module.IsPseudoNull ℤ_[p]⟦X⟧ M] : Finite M :=
  (isPseudoNull_iff_finite p M).1 inferInstance

end IwasawaAlgebra
