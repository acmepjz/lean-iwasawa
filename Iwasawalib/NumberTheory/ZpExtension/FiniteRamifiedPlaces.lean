/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.InertiaExponent

@[expose] public section

open IntermediateField

namespace MvZpExtension

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]
variable (H : MvZpExtension p ι K Kinf)

/-- Restricting an element of infinite inertia to `Kₙ` lands in the inertia subgroup of
the restricted place. -/
theorem mem_inertiaSubgroup_Kn_of_mem_inertiaSubgroup
    (w : AbsoluteValue Kinf ℝ) (n : ℕ) (σ : H.Γ)
    (hσ : σ ∈ w.inertiaSubgroup K) :
    AlgEquiv.restrictNormalHom (H.Kn n) σ ∈
      (w.comp (algebraMap (H.Kn n) Kinf).injective).inertiaSubgroup K := by
  have hmem : AlgEquiv.restrictNormalHom (H.Kn n) σ ∈
      (w.inertiaSubgroup K).map (AlgEquiv.restrictNormalHom (H.Kn n)) :=
    Subgroup.mem_map_of_mem _ hσ
  rwa [AbsoluteValue.map_inertiaSubgroup_eq_of_liesOver K
    (w.comp (algebraMap (H.Kn n) Kinf).injective) w] at hmem

/-- A layerwise exponent bound outside a finite exceptional family makes the full ramified
family finite. -/
@[deprecated "conditional raw-place API; do not use for the source-facing finite base-prime route"
  (since := "2026-09-17")]
theorem finite_ramified_of_layer_exponent_outside
    {S : Set (AbsoluteValue Kinf ℝ)} (hS : S.Finite)
    (hexp : ∀ w ∉ S, ∃ M : ℕ, M ≠ 0 ∧
      ∀ n : ℕ, ∀ σ ∈ w.inertiaSubgroup K,
        AlgEquiv.restrictNormalHom (H.Kn n) (σ ^ M) = 1) :
    {w : AbsoluteValue Kinf ℝ | w.inertiaSubgroup K ≠ ⊥}.Finite := by
  refine hS.subset fun w hw ↦ ?_
  by_contra hwS
  obtain ⟨M, hM, hfix⟩ := hexp w hwS
  apply hw
  apply H.inertiaSubgroup_eq_bot_of_fixes_Kn w hM
  intro n σ hσ
  rw [← (H.Kn n).restrictNormalHom_ker]
  exact hfix n σ hσ

set_option linter.unusedSectionVars false in
/-- A concrete finite index set containing precisely all ramified places. -/
@[deprecated "conditional raw-place API; do not use for the source-facing finite base-prime route"
  (since := "2026-09-17")]
theorem exists_ramifiedPlaces_finset
    (hfin : {w : AbsoluteValue Kinf ℝ | w.inertiaSubgroup K ≠ ⊥}.Finite) :
    ∃ ramified : Finset (AbsoluteValue Kinf ℝ),
      ∀ w, w ∈ ramified ↔ w.inertiaSubgroup K ≠ ⊥ := by
  classical
  refine ⟨hfin.toFinset, ?_⟩
  intro w
  simp

/-- The finite ramified-place index is nonempty once nonemptiness is supplied explicitly. -/
@[deprecated "conditional raw-place API; do not use for the source-facing finite base-prime route"
  (since := "2026-09-17")]
theorem exists_nonempty_ramifiedPlaces_finset
    (hfin : {w : AbsoluteValue Kinf ℝ | w.inertiaSubgroup K ≠ ⊥}.Finite)
    (hne : ∃ w : AbsoluteValue Kinf ℝ, w.inertiaSubgroup K ≠ ⊥) :
    ∃ ramified : Finset (AbsoluteValue Kinf ℝ),
      ramified.Nonempty ∧
      ∀ w, w ∈ ramified ↔ w.inertiaSubgroup K ≠ ⊥ := by
  classical
  obtain ⟨ramified, hramified⟩ :=
    exists_ramifiedPlaces_finset (K := K) (Kinf := Kinf) hfin
  obtain ⟨w, hw⟩ := hne
  exact ⟨ramified, ⟨w, (hramified w).2 hw⟩, hramified⟩

/-- A finite index type for all ramified places, together with a distinguished index. -/
@[deprecated "conditional raw-place API; do not use for the source-facing finite base-prime route"
  (since := "2026-09-17")]
theorem exists_ramifiedPlace_index
    (hfin : {w : AbsoluteValue Kinf ℝ | w.inertiaSubgroup K ≠ ⊥}.Finite)
    (hne : ∃ w : AbsoluteValue Kinf ℝ, w.inertiaSubgroup K ≠ ⊥) :
    ∃ (ramified : Finset (AbsoluteValue Kinf ℝ))
        (i0 : {w // w ∈ ramified}),
      i0.1.inertiaSubgroup K ≠ ⊥ ∧
      (∀ i : {w // w ∈ ramified}, i.1.inertiaSubgroup K ≠ ⊥) ∧
      (∀ w, w.inertiaSubgroup K ≠ ⊥ →
        ∃ i : {w // w ∈ ramified}, i.1 = w) := by
  classical
  obtain ⟨ramified, hramified, hmem⟩ :=
    exists_nonempty_ramifiedPlaces_finset (K := K) (Kinf := Kinf) hfin hne
  obtain ⟨w0, hw0⟩ := hramified
  refine ⟨ramified, ⟨w0, hw0⟩, (hmem w0).1 hw0,
    fun i ↦ (hmem i.1).1 i.2, ?_⟩
  intro w hw
  exact ⟨⟨w, (hmem w).2 hw⟩, rfl⟩

/-- Local layer exponents give an exact nonempty finite ramified family when nonemptiness is
also supplied. -/
@[deprecated "conditional raw-place API; do not use for the source-facing finite base-prime route"
  (since := "2026-09-17")]
theorem exists_nonempty_ramifiedPlaces_finset_of_layer_exponent_outside
    {S : Set (AbsoluteValue Kinf ℝ)} (hS : S.Finite)
    (hexp : ∀ w ∉ S, ∃ M : ℕ, M ≠ 0 ∧
      ∀ n : ℕ, ∀ σ ∈ w.inertiaSubgroup K,
        AlgEquiv.restrictNormalHom (H.Kn n) (σ ^ M) = 1)
    (hne : ∃ w : AbsoluteValue Kinf ℝ, w.inertiaSubgroup K ≠ ⊥) :
    ∃ ramified : Finset (AbsoluteValue Kinf ℝ),
      ramified.Nonempty ∧
      ∀ w, w ∈ ramified ↔ w.inertiaSubgroup K ≠ ⊥ :=
  exists_nonempty_ramifiedPlaces_finset (K := K) (Kinf := Kinf)
    (H.finite_ramified_of_layer_exponent_outside hS hexp) hne

/-- The final finite-index output from local layer exponent data and explicit nonemptiness. -/
@[deprecated "conditional raw-place API; do not use for the source-facing finite base-prime route"
  (since := "2026-09-17")]
theorem exists_ramifiedPlace_index_of_layer_exponent_outside
    {S : Set (AbsoluteValue Kinf ℝ)} (hS : S.Finite)
    (hexp : ∀ w ∉ S, ∃ M : ℕ, M ≠ 0 ∧
      ∀ n : ℕ, ∀ σ ∈ w.inertiaSubgroup K,
        AlgEquiv.restrictNormalHom (H.Kn n) (σ ^ M) = 1)
    (hne : ∃ w : AbsoluteValue Kinf ℝ, w.inertiaSubgroup K ≠ ⊥) :
    ∃ (ramified : Finset (AbsoluteValue Kinf ℝ))
        (i0 : {w // w ∈ ramified}),
      i0.1.inertiaSubgroup K ≠ ⊥ ∧
      (∀ i : {w // w ∈ ramified}, i.1.inertiaSubgroup K ≠ ⊥) ∧
      (∀ w, w.inertiaSubgroup K ≠ ⊥ →
        ∃ i : {w // w ∈ ramified}, i.1 = w) :=
  exists_ramifiedPlace_index (K := K) (Kinf := Kinf)
    (H.finite_ramified_of_layer_exponent_outside hS hexp) hne

end MvZpExtension
