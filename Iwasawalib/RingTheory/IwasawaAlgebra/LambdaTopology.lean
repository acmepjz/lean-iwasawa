/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

public import Iwasawalib.RingTheory.IwasawaAlgebra.PowerSeriesAdic
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

@[expose] public section

/-!
# The topology on the Iwasawa algebra `Λ = ℤ_p⟦X⟧`

This file puts a topology on `Λ = ℤ_p⟦X⟧` and proves that it makes `Λ` a **profinite**
(compact, Hausdorff, totally disconnected) topological ring which is local, and that the
topology is the `(p, X)`-adic one.

The topology used is mathlib's coefficientwise (product) topology,
`PowerSeries.WithPiTopology`, for which compactness, Hausdorffness and total disconnectedness
are inherited from `ℤ_[p]` by Tychonoff and the corresponding `Pi` instances, and for which the
ring operations are already known to be continuous. The main content of the file is therefore
the identification of this topology with the `(p, X)`-adic topology
(`IwasawaAlgebra.isAdic_idealAX`), which is what makes the topology usable in the Iwasawa
theory: the neighbourhood basis of `0` is given by the ideals `(p, X) ^ K`.

## Main results

* `IwasawaAlgebra.instCompactSpacePowerSeriesPadicInt`,
  `IwasawaAlgebra.instTotallyDisconnectedSpacePowerSeriesPadicInt`: `Λ` is profinite.
* `IwasawaAlgebra.isOpen_idealAX_pow`, `IwasawaAlgebra.isClosed_idealAX_pow`: the ideals
  `(p, X) ^ K` are clopen.
* `IwasawaAlgebra.hasBasis_nhds_zero_idealAX`: they are a neighbourhood basis of `0`.
* `IwasawaAlgebra.isAdic_idealAX`: the topology is the `(p, X)`-adic topology.
* `IwasawaAlgebra.maximalIdeal_powerSeries_eq_idealAX`: `(p, X)` is *the* maximal ideal, so in
  particular `X = T = γ - 1` lies in it (`IwasawaAlgebra.X_mem_maximalIdeal`).

These are the hypotheses of the compact Nakayama lemma
`IwasawaAlgebra.eq_top_span_of_sup_smul_top_le` proved in
`Iwasawalib.RingTheory.IwasawaAlgebra.ProfiniteNakayama`; see
`Iwasawalib.RingTheory.IwasawaAlgebra.LambdaNakayama` for the instantiation.
-/

open Topology Set Filter PowerSeries
open scoped PowerSeries.WithPiTopology

namespace IwasawaAlgebra

section PadicIntAux

variable {p : ℕ} [Fact p.Prime]

theorem one_lt_cast_prime : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

/-- The ideal `(p ^ m)` of `ℤ_[p]` is open. -/
theorem isOpen_span_p_pow (m : ℕ) :
    IsOpen ((Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
  have h : ((Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p]) : Set ℤ_[p])
      = Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-m : ℤ)) := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, SetLike.mem_coe]
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [h]
  exact IsUltrametricDist.isOpen_closedBall _
    (ne_of_gt (zpow_pos (by linarith [one_lt_cast_prime (p := p)]) _))

/-- The ideal `(p ^ m)` of `ℤ_[p]` is closed. -/
theorem isClosed_span_p_pow (m : ℕ) :
    IsClosed ((Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
  have h : ((Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p]) : Set ℤ_[p])
      = Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-m : ℤ)) := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, SetLike.mem_coe]
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [h]
  exact Metric.isClosed_closedBall

/-- The ideals `(p ^ m)` are a neighbourhood basis of `0` in `ℤ_[p]`. -/
theorem exists_span_p_pow_subset {u : Set ℤ_[p]} (hu : u ∈ 𝓝 (0 : ℤ_[p])) :
    ∃ M : ℕ, ((Ideal.span {(p : ℤ_[p]) ^ M} : Ideal ℤ_[p]) : Set ℤ_[p]) ⊆ u := by
  have hp : (1 : ℝ) < p := one_lt_cast_prime
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.1 hu
  have htend : Tendsto (fun m : ℕ ↦ ((p : ℝ)⁻¹) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (by rw [inv_lt_one_iff₀]; right; exact hp)
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 htend ε hε).imp
    (fun M h ↦ h M le_rfl)
  refine ⟨M, fun x hx ↦ hεu ?_⟩
  have hnorm : ‖x‖ ≤ ((p : ℝ)⁻¹) ^ M := by
    have := (PadicInt.norm_le_pow_iff_mem_span_pow x M).2 hx
    rwa [zpow_neg, zpow_natCast, ← inv_pow] at this
  have : ((p : ℝ)⁻¹) ^ M < ε := by
    have := hM
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    exact this
  simpa [Metric.mem_ball, dist_zero_right] using lt_of_le_of_lt hnorm this

/-- `⋂_m (p ^ m) = 0` in `ℤ_[p]`. -/
theorem eq_zero_of_mem_span_p_pow_forall {x : ℤ_[p]}
    (h : ∀ m : ℕ, x ∈ (Ideal.span {(p : ℤ_[p]) ^ m} : Ideal ℤ_[p])) : x = 0 := by
  have hp : (1 : ℝ) < p := one_lt_cast_prime
  have key : ∀ m : ℕ, ‖x‖ ≤ ((p : ℝ)⁻¹) ^ m := fun m ↦ by
    have := (PadicInt.norm_le_pow_iff_mem_span_pow x m).2 (h m)
    rwa [zpow_neg, zpow_natCast, ← inv_pow] at this
  have htend : Tendsto (fun m : ℕ ↦ ((p : ℝ)⁻¹) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (by rw [inv_lt_one_iff₀]; right; exact hp)
  exact norm_eq_zero.1 (le_antisymm (ge_of_tendsto' htend key) (norm_nonneg _))

end PadicIntAux

section Profinite

variable (p : ℕ) [Fact p.Prime]

instance instCompactSpacePowerSeriesPadicInt : CompactSpace ℤ_[p]⟦X⟧ :=
  inferInstanceAs (CompactSpace ((Unit →₀ ℕ) → ℤ_[p]))

instance instTotallyDisconnectedSpacePowerSeriesPadicInt :
    TotallyDisconnectedSpace ℤ_[p]⟦X⟧ :=
  inferInstanceAs (TotallyDisconnectedSpace ((Unit →₀ ℕ) → ℤ_[p]))

example : T2Space ℤ_[p]⟦X⟧ := inferInstance
example : IsTopologicalRing ℤ_[p]⟦X⟧ := inferInstance
example : IsLocalRing ℤ_[p]⟦X⟧ := inferInstance

end Profinite

section Adic

variable {p : ℕ} [Fact p.Prime]

/-- Coefficientwise description of the set underlying `(p, X) ^ K`, from
`PowerSeries.coeff_mem_of_mem_idealAX_pow` and `PowerSeries.mem_idealAX_pow_of_coeff_mem`. -/
theorem coe_idealAX_pow (K : ℕ) :
    ((PowerSeries.idealAX (p : ℤ_[p]) ^ K : Ideal ℤ_[p]⟦X⟧) : Set ℤ_[p]⟦X⟧)
      = {g | ∀ i < K, coeff i g ∈ Ideal.span {(p : ℤ_[p]) ^ (K - i)}} := by
  ext g
  exact ⟨fun hg i _ ↦ PowerSeries.coeff_mem_of_mem_idealAX_pow hg i,
    fun hg ↦ PowerSeries.mem_idealAX_pow_of_coeff_mem hg⟩

theorem coe_idealAX_pow_eq_iInter (K : ℕ) :
    ((PowerSeries.idealAX (p : ℤ_[p]) ^ K : Ideal ℤ_[p]⟦X⟧) : Set ℤ_[p]⟦X⟧)
      = ⋂ i ∈ Finset.range K,
          (coeff i) ⁻¹' ((Ideal.span {(p : ℤ_[p]) ^ (K - i)} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
  rw [coe_idealAX_pow]
  ext g
  simp [Finset.mem_range]

/-- **The ideals `(p, X) ^ K` of `Λ` are open.** -/
theorem isOpen_idealAX_pow (K : ℕ) :
    IsOpen ((PowerSeries.idealAX (p : ℤ_[p]) ^ K : Ideal ℤ_[p]⟦X⟧) : Set ℤ_[p]⟦X⟧) := by
  rw [coe_idealAX_pow_eq_iInter]
  exact (Finset.range K).finite_toSet.isOpen_biInter fun i _ ↦
    (isOpen_span_p_pow _).preimage (WithPiTopology.continuous_coeff ℤ_[p] i)

/-- **The ideals `(p, X) ^ K` of `Λ` are closed.** -/
theorem isClosed_idealAX_pow (K : ℕ) :
    IsClosed ((PowerSeries.idealAX (p : ℤ_[p]) ^ K : Ideal ℤ_[p]⟦X⟧) : Set ℤ_[p]⟦X⟧) := by
  rw [coe_idealAX_pow_eq_iInter]
  exact isClosed_biInter fun i _ ↦
    (isClosed_span_p_pow _).preimage (WithPiTopology.continuous_coeff ℤ_[p] i)

/-- `⋂_K (p, X) ^ K = 0` in `Λ`. -/
theorem eq_zero_of_mem_idealAX_pow_forall {g : ℤ_[p]⟦X⟧}
    (h : ∀ K : ℕ, g ∈ (PowerSeries.idealAX (p : ℤ_[p]) ^ K : Ideal ℤ_[p]⟦X⟧)) : g = 0 := by
  ext i
  have h0 : coeff i g = 0 := eq_zero_of_mem_span_p_pow_forall (p := p) fun m ↦ by
    have := PowerSeries.coeff_mem_of_mem_idealAX_pow (h (i + m)) i
    rwa [show i + m - i = m by omega] at this
  simpa using h0

/-- **The ideals `(p, X) ^ K` form a neighbourhood basis of `0` in `Λ`.** -/
theorem hasBasis_nhds_zero_idealAX :
    (𝓝 (0 : ℤ_[p]⟦X⟧)).HasBasis (fun _ : ℕ ↦ True)
      fun K ↦ ((PowerSeries.idealAX (p : ℤ_[p]) ^ K : Ideal ℤ_[p]⟦X⟧) : Set ℤ_[p]⟦X⟧) := by
  refine ⟨fun s ↦ ⟨fun hs ↦ ?_, ?_⟩⟩
  swap
  · rintro ⟨K, -, hK⟩
    exact Filter.mem_of_superset ((isOpen_idealAX_pow K).mem_nhds (Submodule.zero_mem _)) hK
  obtain ⟨U, hUs, hUopen, hU0⟩ := mem_nhds_iff.1 hs
  -- the closed sets `(p,X)^K ∩ Uᶜ` have empty intersection
  set C : ℕ → Set ℤ_[p]⟦X⟧ := fun K ↦
    ((PowerSeries.idealAX (p : ℤ_[p]) ^ K : Ideal ℤ_[p]⟦X⟧) : Set ℤ_[p]⟦X⟧) ∩ Uᶜ with hC
  have hCclosed : ∀ K, IsClosed (C K) := fun K ↦
    (isClosed_idealAX_pow K).inter hUopen.isClosed_compl
  have hCempty : ((univ : Set ℤ_[p]⟦X⟧) ∩ ⋂ K, C K) = ∅ := by
    rw [univ_inter, eq_empty_iff_forall_notMem]
    intro g hg
    simp only [hC, mem_iInter, mem_inter_iff, SetLike.mem_coe, mem_compl_iff] at hg
    exact (hg 0).2 (eq_zero_of_mem_idealAX_pow_forall (fun K ↦ (hg K).1) ▸ hU0)
  obtain ⟨u, hu⟩ := isCompact_univ.elim_finite_subfamily_closed C hCclosed (Set.disjoint_iff_inter_eq_empty.mpr hCempty)
  refine ⟨u.sup id, trivial, fun g hg ↦ hUs ?_⟩
  by_contra hgU
  have : g ∈ (univ : Set ℤ_[p]⟦X⟧) ∩ ⋂ K ∈ u, C K := by
    refine ⟨mem_univ g, mem_biInter fun K hK ↦ ⟨?_, hgU⟩⟩
    exact Ideal.pow_le_pow_right (Finset.le_sup (f := id) hK) hg
  exact Set.disjoint_left.mp hu this.1 this.2

/-- **The topology on `Λ = ℤ_p⟦X⟧` is the `(p, X)`-adic topology.** -/
theorem isAdic_idealAX : IsAdic (PowerSeries.idealAX (p : ℤ_[p])) := by
  rw [isAdic_iff]
  exact ⟨isOpen_idealAX_pow, fun s hs ↦ by
    obtain ⟨K, -, hK⟩ := hasBasis_nhds_zero_idealAX.mem_iff.1 hs
    exact ⟨K, hK⟩⟩

end Adic

section MaximalIdeal

variable (p : ℕ) [Fact p.Prime]

/-- The maximal ideal of `Λ = ℤ_p⟦X⟧` is `(p, X)`. -/
theorem maximalIdeal_powerSeries_eq_idealAX :
    IsLocalRing.maximalIdeal ℤ_[p]⟦X⟧ = PowerSeries.idealAX (p : ℤ_[p]) := by
  apply le_antisymm
  · intro g hg
    have hgc : ¬ IsUnit (constantCoeff g) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        PowerSeries.isUnit_iff_constantCoeff] at hg
      exact hg
    have hmem : constantCoeff g ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
      (IsLocalRing.mem_maximalIdeal _).2 hgc
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hmem
    obtain ⟨a, ha⟩ := hmem
    obtain ⟨t, ht⟩ := PowerSeries.X_dvd_iff.2
      (show constantCoeff (g - C (constantCoeff g)) = 0 by simp)
    have hgt : g = C (constantCoeff g) + X * t := by rw [← ht]; ring
    rw [hgt, ← ha, map_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (PowerSeries.C_mem_idealAX _))
      (Ideal.mul_mem_right _ _ (PowerSeries.X_mem_idealAX _))
  · rw [PowerSeries.idealAX, Ideal.span_le]
    rintro g (rfl | rfl)
    · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        PowerSeries.isUnit_iff_constantCoeff]
      simpa using fun h ↦ ((IsLocalRing.mem_maximalIdeal _).1
        (PadicInt.maximalIdeal_eq_span_p (p := p) ▸
          Ideal.mem_span_singleton_self (p : ℤ_[p]))) h
    · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        PowerSeries.isUnit_iff_constantCoeff]
      simp

/-- `X = T = γ - 1` lies in the maximal ideal of `Λ`. -/
theorem X_mem_maximalIdeal : (X : ℤ_[p]⟦X⟧) ∈ IsLocalRing.maximalIdeal ℤ_[p]⟦X⟧ := by
  rw [maximalIdeal_powerSeries_eq_idealAX]
  exact PowerSeries.X_mem_idealAX _

/-- `p` lies in the maximal ideal of `Λ`. -/
theorem p_mem_maximalIdeal :
    (algebraMap ℤ_[p] ℤ_[p]⟦X⟧ (p : ℤ_[p])) ∈ IsLocalRing.maximalIdeal ℤ_[p]⟦X⟧ := by
  rw [maximalIdeal_powerSeries_eq_idealAX]
  exact PowerSeries.C_mem_idealAX _

end MaximalIdeal

end IwasawaAlgebra
