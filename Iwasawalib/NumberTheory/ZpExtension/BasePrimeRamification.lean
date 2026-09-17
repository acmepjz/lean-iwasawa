/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.AbsoluteValue.FinitePlace
public import Iwasawalib.NumberTheory.ZpExtension.EventualClassNumberBridge
public import Iwasawalib.NumberTheory.ZpExtension.SelectedInertiaCover
public import Iwasawalib.NumberTheory.ZpExtension.RamifiedFamily
public import Iwasawalib.NumberTheory.ZpExtension.TotallyRamifiedLayer
public import Iwasawalib.NumberTheory.ZpExtension.InertiaExponent

@[expose] public section

open Module PowerSeries NumberField IsDedekindDomain
open scoped Pointwise commutatorElement

namespace MvZpExtension

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]
variable (H : MvZpExtension p ι K Kinf)

/-- The height-one primes of `O_K` lying above `p` form a finite set. -/
theorem finite_basePrimesAbove_p :
    {q : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ q.asIdeal}.Finite := by
  apply Set.Finite.subset (Ideal.finite_factors
    (I := Ideal.span {(p : 𝓞 K)}) (by
      simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
        using (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : 𝓞 K) ≠ 0)))
  intro q hq
  rw [Set.mem_setOf_eq, Ideal.dvd_iff_le]
  exact (Ideal.span_singleton_le_iff_mem q.asIdeal).2 hq

include H in
private theorem inertiaSubgroup_eq_bot_of_archimedean_aux [Unique ι]
    (w : AbsoluteValue Kinf ℝ) (hw : ¬IsNonarchimedean w) :
    w.inertiaSubgroup K = ⊥ := by
  have hcard := AbsoluteValue.card_decompositionSubgroup_dvd_two_of_not_isNonarchimedean K w hw
  letI : Finite (w.decompositionSubgroup K) :=
    Nat.finite_of_card_ne_zero (by
      intro hc
      rw [hc] at hcard
      norm_num at hcard)
  letI : Finite (w.inertiaSubgroup K) :=
    Finite.of_injective (fun σ : w.inertiaSubgroup K ↦
      (⟨σ, w.inertiaSubgroup_le_decompositionSubgroup K σ.2⟩ : w.decompositionSubgroup K))
      (fun _ _ h ↦ Subtype.ext (congrArg
        (fun z : w.decompositionSubgroup K ↦ (z : Gal(Kinf / K))) h))
  exact MvZpExtension.inertiaSubgroup_eq_bot_of_finite H w

/-- An archimedean place has trivial inertia in a `Z_p`-extension. -/
theorem inertiaSubgroup_eq_bot_of_archimedean [Unique ι]
    (w : AbsoluteValue Kinf ℝ) (hw : ¬IsNonarchimedean w) :
    w.inertiaSubgroup K = (⊥ : Subgroup H.Γ) := by
  exact inertiaSubgroup_eq_bot_of_archimedean_aux H w hw

/-- Replace an equivalent lift by one lying literally over the canonical finite place. -/
private theorem exists_equiv_lift_comp_eq
    (w : AbsoluteValue Kinf ℝ) (q : HeightOneSpectrum (𝓞 K))
    (h : (w.comp (algebraMap K Kinf).injective).IsEquiv
      (HeightOneSpectrum.adicAbv K q)) :
    ∃ w' : AbsoluteValue Kinf ℝ, w'.IsEquiv w ∧
      w'.comp (algebraMap K Kinf).injective = HeightOneSpectrum.adicAbv K q := by
  obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 h
  have hna_comp : IsNonarchimedean (w.comp (algebraMap K Kinf).injective) :=
    (AbsoluteValue.isNonarchimedean_iff_of_equiv h).2
      (HeightOneSpectrum.isNonarchimedean_adicAbv K q)
  have hna : IsNonarchimedean w :=
    (w.isNonarchimedean_comp_iff (algebraMap K Kinf)).1 hna_comp
  let w' := AbsoluteValue.rpowOfLeOneOrIsNonarchimedean w c hc (Or.inr hna)
  refine ⟨w', ?_, ?_⟩
  · exact (AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨c, hc, rfl⟩).symm
  · ext x
    exact congrFun hpow x

include H in
private theorem ramified_place_liesOver_basePrimeAbove_p_aux [Unique ι]
    (hlocal : ∀ (q : HeightOneSpectrum (𝓞 K)),
      (p : 𝓞 K) ∉ q.asIdeal →
      ∀ (v : AbsoluteValue Kinf ℝ),
        [v.LiesOver (HeightOneSpectrum.adicAbv K q)] →
        ∃ M : ℕ, M ≠ 0 ∧
          ∀ n σ, σ ∈ v.inertiaSubgroup K →
            AlgEquiv.restrictNormalHom (H.Kn n) (σ ^ M) = 1)
    (w : AbsoluteValue Kinf ℝ)
    (hw : w.inertiaSubgroup K ≠ ⊥) :
    ∃ q : HeightOneSpectrum (𝓞 K),
      (p : 𝓞 K) ∈ q.asIdeal ∧
      (w.comp (algebraMap K Kinf).injective).IsEquiv
        (HeightOneSpectrum.adicAbv K q) := by
  have hna : IsNonarchimedean w := by
    by_contra h
    exact hw (inertiaSubgroup_eq_bot_of_archimedean_aux H w h)
  let v := w.comp (algebraMap K Kinf).injective
  have hna_v : IsNonarchimedean v :=
    (w.isNonarchimedean_comp_iff (algebraMap K Kinf)).2 hna
  have hnt_w : w.IsNontrivial := by
    by_contra hnt
    exact hw (AbsoluteValue.inertiaSubgroup_eq_bot_of_not_isNontrivial K w hnt)
  have hnt_v : v.IsNontrivial := by
    rw [AbsoluteValue.isNontrivial_iff_of_liesOver v w]
    exact hnt_w
  let vn := v.normalization
  have hvn_norm : vn.IsNormalized :=
    v.isNormalized_normalization_of_isNontrivial_of_isAlgebraic hnt_v
  have hvn_na : IsNonarchimedean vn :=
    (AbsoluteValue.isNonarchimedean_iff_of_equiv v.isEquiv_normalization).1 hna_v
  letI : vn.IsNormalized := hvn_norm
  obtain ⟨q, hq, _⟩ := NumberField.existsUnique_heightOneSpectrum_adicAbv_isEquiv vn hvn_na
  have hvq : v.IsEquiv (HeightOneSpectrum.adicAbv K q) :=
    v.isEquiv_normalization.trans hq
  refine ⟨q, ?_, hvq⟩
  by_contra hpq
  obtain ⟨w', hw'eq, hw'comp⟩ := exists_equiv_lift_comp_eq w q hvq
  letI : w'.LiesOver (HeightOneSpectrum.adicAbv K q) := ⟨hw'comp⟩
  obtain ⟨M, hM, hfix⟩ := hlocal q hpq w'
  have hw'bot : w'.inertiaSubgroup K = ⊥ := by
    apply H.inertiaSubgroup_eq_bot_of_fixes_Kn w' hM
    intro n σ hσ
    rw [← (H.Kn n).restrictNormalHom_ker]
    exact hfix n σ hσ
  apply hw
  rw [← AbsoluteValue.inertiaSubgroup_eq_of_equiv hw'eq, hw'bot]

/-- Every ramified place lies above a height-one prime containing `p`, conditional on the
full local exponent input away from `p`. -/
theorem ramified_place_liesOver_basePrimeAbove_p
    [Unique ι]
    (hlocal : ∀ (q : HeightOneSpectrum (𝓞 K)),
      (p : 𝓞 K) ∉ q.asIdeal →
      ∀ (v : AbsoluteValue Kinf ℝ),
        [v.LiesOver (HeightOneSpectrum.adicAbv K q)] →
        ∃ M : ℕ, M ≠ 0 ∧
          ∀ n σ, σ ∈ v.inertiaSubgroup K →
            AlgEquiv.restrictNormalHom (H.Kn n) (σ ^ M) = 1)
    (w : AbsoluteValue Kinf ℝ)
    (hw : w.inertiaSubgroup K ≠ ⊥) :
    ∃ q : HeightOneSpectrum (𝓞 K),
      (p : 𝓞 K) ∈ q.asIdeal ∧
      (w.comp (algebraMap K Kinf).injective).IsEquiv
        (HeightOneSpectrum.adicAbv K q) := by
  exact ramified_place_liesOver_basePrimeAbove_p_aux H hlocal w hw

/-- One ramified lift for each ramified base prime, with all raw representatives covered up
to equivalence of their restrictions. The finite index is allowed to be empty. -/
structure RamifiedBasePlaceData (H : MvZpExtension p ι K Kinf) where
  base : Finset (HeightOneSpectrum (𝓞 K))
  above_p : ∀ q : base, (p : 𝓞 K) ∈ q.1.asIdeal
  place : (q : base) → AbsoluteValue Kinf ℝ
  comp_eq_adicAbv : ∀ q,
    (place q).comp (algebraMap K Kinf).injective =
      HeightOneSpectrum.adicAbv K q.1
  ramified : ∀ q, (place q).inertiaSubgroup K ≠ ⊥
  covers : ∀ w : AbsoluteValue Kinf ℝ,
    w.inertiaSubgroup K ≠ ⊥ → ∃ q : base,
      (w.comp (algebraMap K Kinf).injective).IsEquiv
        (HeightOneSpectrum.adicAbv K q.1)

include H in
private theorem exists_ramifiedBasePlaceData_aux [Unique ι]
    (hS1 : ∀ w : AbsoluteValue Kinf ℝ,
      w.inertiaSubgroup K ≠ ⊥ →
      ∃ q : HeightOneSpectrum (𝓞 K),
        (p : 𝓞 K) ∈ q.asIdeal ∧
        (w.comp (algebraMap K Kinf).injective).IsEquiv
          (HeightOneSpectrum.adicAbv K q)) :
    Nonempty (RamifiedBasePlaceData H) := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 K)) :=
    {q | (p : 𝓞 K) ∈ q.asIdeal ∧
      ∃ w : AbsoluteValue Kinf ℝ,
        w.comp (algebraMap K Kinf).injective = HeightOneSpectrum.adicAbv K q ∧
        w.inertiaSubgroup K ≠ ⊥}
  have hSfin : S.Finite := finite_basePrimesAbove_p (p := p) (K := K) |>.subset
    (fun _ hq ↦ hq.1)
  let base := hSfin.toFinset
  have hbase (q : base) : q.1 ∈ S := hSfin.mem_toFinset.mp q.2
  let place (q : base) : AbsoluteValue Kinf ℝ := (hbase q).2.choose
  have hplace_comp (q : base) :
      (place q).comp (algebraMap K Kinf).injective = HeightOneSpectrum.adicAbv K q.1 :=
    (hbase q).2.choose_spec.1
  have hplace_ramified (q : base) : (place q).inertiaSubgroup K ≠ ⊥ :=
    (hbase q).2.choose_spec.2
  refine ⟨{
    base := base
    above_p := fun q ↦ (hbase q).1
    place := place
    comp_eq_adicAbv := hplace_comp
    ramified := hplace_ramified
    covers := ?_ }⟩
  intro w hw
  obtain ⟨q, hpq, hwq⟩ := hS1 w hw
  obtain ⟨w', hw'eq, hw'comp⟩ := exists_equiv_lift_comp_eq w q hwq
  have hw'ram : w'.inertiaSubgroup K ≠ ⊥ := by
    rw [AbsoluteValue.inertiaSubgroup_eq_of_equiv hw'eq]
    exact hw
  have hqS : q ∈ S := ⟨hpq, w', hw'comp, hw'ram⟩
  have hqbase : q ∈ base := hSfin.mem_toFinset.mpr hqS
  exact ⟨⟨q, hqbase⟩, hwq⟩

/-- The finite base-prime package exists from the full local support input. -/
theorem exists_ramifiedBasePlaceData [Unique ι]
    (hlocal : ∀ (q : HeightOneSpectrum (𝓞 K)),
      (p : 𝓞 K) ∉ q.asIdeal →
      ∀ (v : AbsoluteValue Kinf ℝ),
        [v.LiesOver (HeightOneSpectrum.adicAbv K q)] →
        ∃ M : ℕ, M ≠ 0 ∧
          ∀ n σ, σ ∈ v.inertiaSubgroup K →
            AlgEquiv.restrictNormalHom (H.Kn n) (σ ^ M) = 1) :
    Nonempty (RamifiedBasePlaceData H) := by
  apply exists_ramifiedBasePlaceData_aux H
  intro w hw
  exact H.ramified_place_liesOver_basePrimeAbove_p hlocal w hw

namespace RamifiedBasePlaceData

/-- A single power subgroup lies in every selected inertia subgroup. -/
theorem exists_common_shift [Unique ι]
    (D : RamifiedBasePlaceData H) :
    ∃ e : ℕ, ∀ q : D.base,
      (H.Γpow e : Subgroup H.Γ) ≤ (D.place q).inertiaSubgroup K := by
  exact H.exists_Γpow_le_of_isClosed (fun q : D.base ↦ (D.place q).inertiaSubgroup K)
    (fun q ↦ AbsoluteValue.isClosed_inertiaSubgroup K (D.place q)) D.ramified

/-- After a common shift, each selected representative is totally ramified at later layers. -/
theorem inertia_Kn_eq_top [Unique ι]
    (D : RamifiedBasePlaceData H) {e n : ℕ}
    (he : ∀ q : D.base,
      (H.Γpow e : Subgroup H.Γ) ≤ (D.place q).inertiaSubgroup K)
    (hen : e ≤ n) (q : D.base) :
    (D.place q).inertiaSubgroup (H.Kn n) = ⊤ := by
  exact (H.inertiaSubgroup_Kn_eq_top_iff n (D.place q)).2
    (H.Γpow_le_of_le hen (he q))

end RamifiedBasePlaceData

private theorem exists_algEquiv_comp_isEquiv_of_comp_isEquiv
    {F L : Type*} [Field F] [Field L] [Algebra F L] [Normal F L]
    {v w : AbsoluteValue L ℝ}
    (h : (v.comp (algebraMap F L).injective).IsEquiv
      (w.comp (algebraMap F L).injective)) :
    ∃ σ : Gal(L / F), (v.comp (f := σ) σ.injective).IsEquiv w := by
  obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 h
  by_cases hc_one : c ≤ 1
  · let vc := AbsoluteValue.rpowOfLeOneOrIsNonarchimedean v c hc (Or.inl hc_one)
    have hbase : vc.comp (algebraMap F L).injective =
        w.comp (algebraMap F L).injective := by
      ext x
      exact congrFun hpow x
    obtain ⟨σ, hσ⟩ := AbsoluteValue.exists_algEquiv_comp_eq_of_comp_eq hbase
    refine ⟨σ, ?_⟩
    rw [← hσ, AbsoluteValue.isEquiv_iff_exists_rpow_eq]
    exact ⟨c, hc, rfl⟩
  · have hc_one' : c⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hc]
      exact le_of_not_ge hc_one
    let wc := AbsoluteValue.rpowOfLeOneOrIsNonarchimedean w c⁻¹ (inv_pos.mpr hc)
      (Or.inl hc_one')
    have hbase : v.comp (algebraMap F L).injective =
        wc.comp (algebraMap F L).injective := by
      ext x
      change v (algebraMap F L x) = w (algebraMap F L x) ^ c⁻¹
      have hp := congrFun hpow x
      change v (algebraMap F L x) ^ c = w (algebraMap F L x) at hp
      rw [← hp, Real.rpow_rpow_inv (v.nonneg _) hc.ne']
    obtain ⟨σ, hσ⟩ := AbsoluteValue.exists_algEquiv_comp_eq_of_comp_eq hbase
    refine ⟨σ, ?_⟩
    rw [hσ, AbsoluteValue.isEquiv_iff_exists_rpow_eq]
    refine ⟨c, hc, ?_⟩
    funext x
    exact Real.rpow_inv_rpow (w.nonneg x) hc.ne'

/-- Equivalent restrictions to `K` are conjugate-equivalent over `K∞`. -/
theorem exists_Γ_conjugating_of_comp_equiv
    {v w : AbsoluteValue Kinf ℝ}
    (h : (v.comp (algebraMap K Kinf).injective).IsEquiv
      (w.comp (algebraMap K Kinf).injective)) :
    ∃ τ : H.Γ, (v.comp (f := τ) τ.injective).IsEquiv w := by
  exact exists_algEquiv_comp_isEquiv_of_comp_isEquiv h

/-- Total inertia gives uniqueness of a lift as a place class. -/
theorem isEquiv_of_inertia_eq_top_of_comp_isEquiv
    {n : ℕ} {v w : AbsoluteValue Kinf ℝ}
    (hv : v.inertiaSubgroup (H.Kn n) = ⊤)
    (hcomp :
      (v.comp (algebraMap (H.Kn n) Kinf).injective).IsEquiv
      (w.comp (algebraMap (H.Kn n) Kinf).injective)) :
    v.IsEquiv w := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comp_isEquiv_of_comp_isEquiv hcomp
  have hσmem : σ ∈ v.inertiaSubgroup (H.Kn n) := by
    rw [hv]
    exact Subgroup.mem_top σ
  have heq : v.comp (f := σ) σ.injective = v := by
    ext x
    exact v.apply_eq_of_mem_decompositionSubgroup
      (v.inertiaSubgroup_le_decompositionSubgroup (H.Kn n) hσmem) x
  rwa [heq] at hσ

/-- Equivalent restrictions of places on `L∞` are conjugate-equivalent over `K`. -/
theorem exists_GG_conjugating_places_of_comp_equiv
    (v w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ)
    (h : ((H.placeBelow v).comp (algebraMap K Kinf).injective).IsEquiv
      ((H.placeBelow w).comp (algebraMap K Kinf).injective)) :
    ∃ τ : H.GG, (v.comp (f := τ) τ.injective).IsEquiv w := by
  have hdirect :
      (v.comp (algebraMap K ↥(H.Linf.restrictScalars K)).injective).IsEquiv
        (w.comp (algebraMap K ↥(H.Linf.restrictScalars K)).injective) := by
    intro x y
    have hv (z : K) :
        v (algebraMap K ↥(H.Linf.restrictScalars K) z) =
          H.placeBelow v (algebraMap K Kinf z) := by
      have hz := congrArg
        (fun u : AbsoluteValue ↥H.KinfIn ℝ ↦ u (algebraMap K ↥H.KinfIn z))
        (H.comp_placeBelow v)
      change
        v (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K) (algebraMap K ↥H.KinfIn z)) =
          H.placeBelow v (H.kinfInEquiv (algebraMap K ↥H.KinfIn z)) at hz
      rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply K ↥H.KinfIn
        ↥(H.Linf.restrictScalars K)] at hz
      exact hz
    have hw (z : K) :
        w (algebraMap K ↥(H.Linf.restrictScalars K) z) =
          H.placeBelow w (algebraMap K Kinf z) := by
      have hz := congrArg
        (fun u : AbsoluteValue ↥H.KinfIn ℝ ↦ u (algebraMap K ↥H.KinfIn z))
        (H.comp_placeBelow w)
      change
        w (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K) (algebraMap K ↥H.KinfIn z)) =
          H.placeBelow w (H.kinfInEquiv (algebraMap K ↥H.KinfIn z)) at hz
      rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply K ↥H.KinfIn
        ↥(H.Linf.restrictScalars K)] at hz
      exact hz
    simpa [AbsoluteValue.comp_apply, hv, hw] using h x y
  obtain ⟨v', hv'v, hv'K⟩ :=
    AbsoluteValue.exists_equiv_and_liesOver_of_comp_equiv v
      (w.comp (algebraMap K ↥(H.Linf.restrictScalars K)).injective) hdirect
  obtain ⟨τ, hτ⟩ := AbsoluteValue.exists_algEquiv_comp_eq_of_comp_eq hv'K.comp_eq
  exact ⟨τ, (hv'v.comp τ.injective).symm.trans (hτ ▸ AbsoluteValue.IsEquiv.rfl)⟩

/-- Inertia at conjugate-equivalent places is controlled modulo the commutator. -/
theorem inertiaSubgroup_le_commutator_sup_of_conjugate_equiv
    {v w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ}
    (τ : H.GG) (hvw : (v.comp (f := τ) τ.injective).IsEquiv w) :
    w.inertiaSubgroup K ≤ commutator H.GG ⊔ v.inertiaSubgroup K := by
  rw [← AbsoluteValue.inertiaSubgroup_eq_of_equiv hvw]
  exact H.inertiaSubgroup_le_commutator_sup_of_conjugate τ rfl

namespace RamifiedBasePlaceData

/-- The selected inertia groups cover every inertia group modulo the commutator. -/
theorem selectedInertia_cover
    (D : RamifiedBasePlaceData H)
    (selected : (q : D.base) → AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ)
    (hselected : ∀ q, H.placeBelow (selected q) = D.place q) :
    ∀ w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ,
      w.inertiaSubgroup K ≤ commutator H.GG ⊔
        ⨆ q : D.base, (selected q).inertiaSubgroup K := by
  intro w
  by_cases hw : (H.placeBelow w).inertiaSubgroup K = ⊥
  · rw [H.inertiaSubgroup_eq_bot_of_placeBelow_inertiaSubgroup_eq_bot w hw]
    exact bot_le
  · obtain ⟨q, hq⟩ := D.covers (H.placeBelow w) hw
    have hcomp :
        ((H.placeBelow (selected q)).comp (algebraMap K Kinf).injective).IsEquiv
          ((H.placeBelow w).comp (algebraMap K Kinf).injective) := by
      rw [hselected q, D.comp_eq_adicAbv q]
      exact hq.symm
    obtain ⟨τ, hτ⟩ := H.exists_GG_conjugating_places_of_comp_equiv (selected q) w hcomp
    exact le_trans (H.inertiaSubgroup_le_commutator_sup_of_conjugate_equiv τ hτ)
      (sup_le_sup_left (le_iSup (fun u : D.base ↦ (selected u).inertiaSubgroup K) q) _)

/-- `HH` is generated by the commutator and the selected finite inertia family. -/
theorem HH_eq_commutator_sup_iSup
    (D : RamifiedBasePlaceData H)
    (selected : (q : D.base) → AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ)
    (hselected : ∀ q, H.placeBelow (selected q) = D.place q) :
    H.HH = commutator H.GG ⊔
      ⨆ q : D.base, (selected q).inertiaSubgroup K := by
  apply le_antisymm
  · rw [MvZpExtension.HH]
    exact sup_le le_sup_left (iSup_le <| selectedInertia_cover H D selected hselected)
  · exact sup_le H.commutator_le_HH
      (iSup_le fun q ↦ H.inertiaSubgroup_le_HH (selected q))

end RamifiedBasePlaceData

end MvZpExtension
