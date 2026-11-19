/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.YnFiniteInertiaFamily

@[expose] public section

open scoped commutatorElement Pointwise

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- Every place of `K∞` has a place of `L∞` above it. -/
theorem exists_Linf_place_placeBelow_eq (v : AbsoluteValue Kinf ℝ) :
    ∃ w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ, H.placeBelow w = v := by
  let v' : AbsoluteValue ↥H.KinfIn ℝ :=
    v.comp (f := (H.kinfInEquiv : ↥H.KinfIn →+* Kinf)) H.kinfInEquiv.injective
  obtain ⟨w, hw⟩ := v'.exists_liesOver ↥(H.Linf.restrictScalars K)
  refine ⟨w, ?_⟩
  ext x
  have h := congrArg
    (fun u : AbsoluteValue ↥H.KinfIn ℝ ↦ u (H.kinfInEquiv.symm x))
    (H.comp_placeBelow w)
  rw [show w.comp (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)).injective = v'
    from hw.under_eq] at h
  change v (H.kinfInEquiv (H.kinfInEquiv.symm x)) =
    H.placeBelow w (H.kinfInEquiv (H.kinfInEquiv.symm x)) at h
  simpa only [H.kinfInEquiv.apply_symm_apply] using h.symm

/-- Simultaneously choose one place of `L∞` above every member of a finite family. -/
theorem exists_selected_Linf_places (S : Finset (AbsoluteValue Kinf ℝ)) :
    ∃ w : (v : ↥S) → AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ,
      ∀ v, H.placeBelow (w v) = v := by
  choose w hw using fun v : ↥S ↦ H.exists_Linf_place_placeBelow_eq (v : AbsoluteValue Kinf ℝ)
  exact ⟨w, hw⟩

/-- Two places of `L∞` above the same place of `K∞` are conjugate by `Gal(L∞/K)`. -/
theorem exists_GG_conjugating_places
    (v w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ)
    (hbelow : H.placeBelow v = H.placeBelow w) :
    ∃ τ : H.GG, v.comp (f := τ) τ.injective = w := by
  apply AbsoluteValue.exists_algEquiv_comp_eq_of_comp_eq
  have hkinf :
      v.comp (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)).injective =
        w.comp (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)).injective := by
    rw [H.comp_placeBelow v, H.comp_placeBelow w, hbelow]
  ext x
  have h := congrArg (fun u : AbsoluteValue ↥H.KinfIn ℝ ↦ u (algebraMap K ↥H.KinfIn x)) hkinf
  change v (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)
    (algebraMap K ↥H.KinfIn x)) =
      w (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)
        (algebraMap K ↥H.KinfIn x)) at h
  change v (algebraMap K ↥(H.Linf.restrictScalars K) x) =
    w (algebraMap K ↥(H.Linf.restrictScalars K) x)
  rw [IsScalarTower.algebraMap_apply K ↥H.KinfIn ↥(H.Linf.restrictScalars K)]
  exact h

/-- Conjugate inertia subgroups have the same image modulo the commutator subgroup. -/
theorem inertiaSubgroup_le_commutator_sup_of_conjugate
    {v w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ}
    (τ : H.GG) (hvw : v.comp (f := τ) τ.injective = w) :
    w.inertiaSubgroup K ≤ commutator H.GG ⊔ v.inertiaSubgroup K := by
  let Q : Subgroup H.GG := commutator H.GG ⊔ v.inertiaSubgroup K
  letI : Q.Normal := Subgroup.normal_of_commutator_le le_sup_left
  intro σ hσ
  have hsub : w.inertiaSubgroup K = (MulAut.conj τ)⁻¹ • v.inertiaSubgroup K := by
    rw [← hvw, AbsoluteValue.inertiaSubgroup_comp_algEquiv_eq_smul]
  rw [hsub] at hσ
  obtain ⟨ρ, hρ, rfl⟩ := hσ
  exact Subgroup.Normal.conj_mem inferInstance _
    ((show v.inertiaSubgroup K ≤ Q from le_sup_right) hρ) _

/-- If the place below `w` is unramified in `K∞ / K`, then `w` has trivial inertia in
`L∞ / K`. -/
theorem inertiaSubgroup_eq_bot_of_placeBelow_inertiaSubgroup_eq_bot
    (w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ)
    (hbelow : (H.placeBelow w).inertiaSubgroup K = ⊥) :
    w.inertiaSubgroup K = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  let r := AlgEquiv.restrictNormalHom (F := K)
    (K₁ := ↥(H.Linf.restrictScalars K)) ↥H.KinfIn
  have hmap : (w.inertiaSubgroup K).map r =
      (w.comp (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)).injective).inertiaSubgroup K := by
    exact AbsoluteValue.map_inertiaSubgroup_eq_of_liesOver K
      (w.comp (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)).injective) w
  have hres : r σ ∈ (w.inertiaSubgroup K).map r := Subgroup.mem_map_of_mem r hσ
  have htransport :
      (w.comp (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)).injective).inertiaSubgroup K = ⊥ := by
    rw [H.comp_placeBelow w, AbsoluteValue.inertiaSubgroup_comp_algEquiv_eq_comap, hbelow]
    exact MonoidHom.ker_eq_bot _ (AlgEquiv.autCongr H.kinfInEquiv).injective
  rw [hmap, htransport, Subgroup.mem_bot] at hres
  have hX : σ ∈ H.Xinf := by
    rw [H.Xinf_eq_ker, MonoidHom.mem_ker]
    exact hres
  rw [Subgroup.mem_bot]
  exact H.inertiaSubgroup_inf_Xinf w σ hσ hX

/-- Selected lifts of a finite support cover every inertia subgroup modulo the commutator. -/
theorem selectedInertia_cover
    (S : Finset (AbsoluteValue Kinf ℝ))
    (selected : (v : ↥S) → AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ)
    (hselected : ∀ v, H.placeBelow (selected v) = v)
    (hsupport : ∀ v : AbsoluteValue Kinf ℝ, v ∉ S → v.inertiaSubgroup K = ⊥)
    (w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ) :
    w.inertiaSubgroup K ≤ commutator H.GG ⊔
      ⨆ v : ↥S, (selected v).inertiaSubgroup K := by
  by_cases hw : H.placeBelow w ∈ S
  · let v : ↥S := ⟨H.placeBelow w, hw⟩
    obtain ⟨τ, hτ⟩ := H.exists_GG_conjugating_places (selected v) w (hselected v)
    exact le_trans (H.inertiaSubgroup_le_commutator_sup_of_conjugate τ hτ)
      (sup_le_sup_left (le_iSup (fun u : ↥S ↦ (selected u).inertiaSubgroup K) v) _)
  · rw [H.inertiaSubgroup_eq_bot_of_placeBelow_inertiaSubgroup_eq_bot w
      (hsupport (H.placeBelow w) hw)]
    exact bot_le

end MvZpExtension
