/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.AbsoluteValue.RamificationIndex
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.Basic

@[expose] public section

/-!
# Inertia subgroups of an infinite Galois extension

`AbsoluteValue.inertiaSubgroup` is defined in
`Iwasawalib.NumberTheory.AbsoluteValue.InertiaSubgroup` for an arbitrary algebra `K / F` and an
arbitrary absolute value on `K`; nothing there assumes `K / F` finite.  What was missing, and
is supplied here, is the API that makes it usable for an *infinite* Galois extension:

* the translation between `AbsoluteValue.IsUnramified` and triviality of the inertia subgroup
  (`AbsoluteValue.isUnramified_iff_inertiaSubgroup_eq_bot`), which for a normal `M / F` needs
  no finiteness;
* the passage to a limit: `AbsoluteValue.inertiaSubgroup_eq_iInf` expresses `I_v(L/F)` as the
  inverse limit of the `I_{v|E}(E/F)` over a directed family of normal intermediate fields
  exhausting `L`, and `AbsoluteValue.inertiaSubgroup_eq_bot_of_iSup_eq_top` is the special case
  which says that an increasing union of unramified extensions is unramified;
* the criterion for total ramification, `AbsoluteValue.inertiaSubgroup_eq_top_iff`;
* the characterisation of "unramified everywhere" by inertia subgroups,
  `AbsoluteValue.isUnramifiedEverywhere_iff_forall_inertiaSubgroup_le`;
* topology: `AbsoluteValue.isClosed_decompositionSubgroup` and
  `AbsoluteValue.isClosed_inertiaSubgroup` say that decomposition and inertia subgroups are
  closed for the Krull topology.  This is the input that
  `EquivMvZp.exists_Γpow_le_of_isClosed` (blueprint node `exists-totally-ramified`) was
  waiting for.

Compare `AbsoluteValue.isUnramified_iSup` in
`Iwasawalib.NumberTheory.NumberField.HilbertClassField.Basic`, which proves a related limit
statement about `AbsoluteValue.IsUnramified` for a family of intermediate fields that need not
be normal; the results here are stated directly in terms of inertia subgroups and are what the
group theory of Washington's Lemma 13.15 consumes.
-/

namespace AbsoluteValue

section Bot

variable (F : Type*) {M : Type*} [Field F] [Field M] [Algebra F M] [Normal F M]
  (v : AbsoluteValue M ℝ)

theorem range_restrictRestrictAlgEquivMapHom_self :
    (IntermediateField.restrictRestrictAlgEquivMapHom F M M M).range = ⊥ := by
  refine le_bot_iff.1 ?_
  rintro _ ⟨τ, rfl⟩
  rw [Subgroup.mem_bot, show τ = 1 from Subsingleton.elim _ _, map_one]

/-- **A place of a normal extension is unramified exactly when its inertia subgroup is
trivial.**  No finiteness is assumed: `M / F` may be an infinite Galois extension. -/
theorem isUnramified_iff_inertiaSubgroup_eq_bot :
    v.IsUnramified F ↔ v.inertiaSubgroup F = ⊥ := by
  rw [v.isUnramified_spec F (L := M) v, IsUnramifiedOfIsScalarTower,
    range_restrictRestrictAlgEquivMapHom_self, le_bot_iff]

/-- Every place of an everywhere-unramified normal extension has trivial inertia. -/
theorem inertiaSubgroup_eq_bot_of_isUnramifiedEverywhere
    [NumberField.IsUnramifiedEverywhere F M] : v.inertiaSubgroup F = ⊥ := by
  by_cases hv : v.IsNontrivial
  · exact (v.isUnramified_iff_inertiaSubgroup_eq_bot F).1
      ((NumberField.isUnramifiedEverywhere_iff F M).1 ‹_› v hv)
  · exact inertiaSubgroup_eq_bot_of_not_isNontrivial F v hv

end Bot

section Limit

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [Normal F L]

/-- **Inertia in an infinite Galois extension is detected at finite levels.**  If `L / F` is
normal and is the union of a family of normal intermediate fields `E i` at each of which the
place `v` has trivial inertia, then `v` has trivial inertia in `L / F` itself. -/
theorem inertiaSubgroup_eq_bot_of_iSup_eq_top {ι : Type*} (E : ι → IntermediateField F L)
    [∀ i, Normal F ↥(E i)] (hE : ⨆ i, E i = ⊤) (v : AbsoluteValue L ℝ)
    (h : ∀ i, (v.comp (algebraMap ↥(E i) L).injective).inertiaSubgroup F = ⊥) :
    v.inertiaSubgroup F = ⊥ := by
  refine le_bot_iff.1 fun σ hσ ↦ ?_
  rw [Subgroup.mem_bot]
  have hfix : ∀ i, ∀ x : ↥(E i), σ (algebraMap ↥(E i) L x) = algebraMap ↥(E i) L x := by
    intro i x
    have himg : AlgEquiv.restrictNormalHom ↥(E i) σ ∈
        (v.inertiaSubgroup F).map (AlgEquiv.restrictNormalHom ↥(E i)) :=
      Subgroup.mem_map_of_mem _ hσ
    rw [map_inertiaSubgroup_eq_of_liesOver F (v.comp (algebraMap ↥(E i) L).injective) v,
      h i, Subgroup.mem_bot] at himg
    have := AlgEquiv.algebraMap_restrictNormalHom_apply (F := F) (K₁ := L) ↥(E i) σ x
    rw [himg] at this
    simpa using this.symm
  have hle : (⊤ : IntermediateField F L) ≤
      IntermediateField.fixedField (Subgroup.closure {σ}) := by
    rw [← hE]
    refine iSup_le fun i x hx ↦ ?_
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy => rw [Set.mem_singleton_iff] at hy; subst hy; exact hfix i ⟨x, hx⟩
    | one => rfl
    | mul a b _ _ ha hb => rw [AlgEquiv.mul_apply, hb, ha]
    | inv a _ ha => exact (AlgEquiv.symm_apply_eq _).2 ha.symm
  ext x
  have := hle (show x ∈ (⊤ : IntermediateField F L) from trivial)
  rw [IntermediateField.mem_fixedField_iff] at this
  exact this σ (Subgroup.subset_closure rfl)

/-- **Inertia in an infinite Galois extension is the inverse limit of the inertia subgroups at
the finite levels.**  If `L / F` is normal and is the *directed* union of normal intermediate
fields `E i`, then `σ` lies in `I_v(L/F)` exactly when each restriction `σ|_{E i}` lies in
`I_{v|E i}(E i / F)`. -/
theorem inertiaSubgroup_eq_iInf {ι : Type*} [Nonempty ι] (E : ι → IntermediateField F L)
    [∀ i, Normal F ↥(E i)] (hdir : Directed (· ≤ ·) E) (hE : ⨆ i, E i = ⊤)
    (v : AbsoluteValue L ℝ) :
    v.inertiaSubgroup F = ⨅ i, ((v.comp (algebraMap ↥(E i) L).injective).inertiaSubgroup F).comap
      (AlgEquiv.restrictNormalHom ↥(E i)) := by
  have hex : ∀ x : L, ∃ i, x ∈ E i := by
    intro x
    have hx : x ∈ (⊤ : IntermediateField F L) := trivial
    rw [← hE, ← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed hdir,
      Set.mem_iUnion] at hx
    exact hx
  refine le_antisymm (le_iInf fun i ↦ ?_) fun σ hσ ↦ ?_
  · rw [← Subgroup.map_le_iff_le_comap,
      map_inertiaSubgroup_eq_of_liesOver F (v.comp (algebraMap ↥(E i) L).injective) v]
  · simp only [Subgroup.mem_iInf, Subgroup.mem_comap] at hσ
    have key : ∀ i, ∀ y : ↥(E i),
        (v.comp (algebraMap ↥(E i) L).injective) (AlgEquiv.restrictNormalHom ↥(E i) σ y) =
          v (σ (y : L)) := by
      intro i y
      rw [comp_apply, AlgEquiv.algebraMap_restrictNormalHom_apply]
      rfl
    have hD : σ ∈ v.decompositionSubgroup F := by
      rw [mem_decompositionSubgroup_iff_forall_apply_eq]
      intro x
      obtain ⟨i, hi⟩ := hex x
      have h1 := inertiaSubgroup_le_decompositionSubgroup F _ (hσ i)
      rw [mem_decompositionSubgroup_iff_forall_apply_eq] at h1
      have h2 := h1 ⟨x, hi⟩
      rw [key i ⟨x, hi⟩] at h2
      exact h2
    rw [mem_inertiaSubgroup_iff]
    refine ⟨hD, ?_⟩
    by_cases hna : IsNonarchimedean v
    · refine Or.inr fun x hx ↦ ?_
      obtain ⟨i, hi⟩ := hex x
      have hna' : IsNonarchimedean (v.comp (algebraMap ↥(E i) L).injective) :=
        (v.isNonarchimedean_comp_iff (algebraMap ↥(E i) L)).2 hna
      have h3 := (v.comp (algebraMap ↥(E i) L).injective
        ).apply_sub_lt_one_of_mem_inertiaSubgroup_of_isNonarchimedean (hσ i) hna'
        (x := (⟨x, hi⟩ : ↥(E i))) (by simpa [comp_apply] using hx)
      rw [comp_apply, map_sub, AlgEquiv.algebraMap_restrictNormalHom_apply] at h3
      exact h3
    · exact Or.inl hna

end Limit

section Top

variable (F : Type*) {L : Type*} [Field F] [Field L] [Algebra F L] [Normal F L]
  (E : IntermediateField F L) [Normal F ↥E]

/-- `Gal(L/E) ⊆ Gal(L/F)`, as the image of `restrictRestrictAlgEquivMapHom`, is the fixing
subgroup of `E`. -/
theorem _root_.IntermediateField.range_restrictRestrictAlgEquivMapHom_eq_fixingSubgroup' :
    (IntermediateField.restrictRestrictAlgEquivMapHom F L ↥E L).range = E.fixingSubgroup :=
  (AlgEquiv.restrictNormalHom_ker_eq_range (F := F) (K₁ := L) ↥E).symm.trans
    E.restrictNormalHom_ker

/-- **`L / E` is totally ramified at `v` exactly when `Gal(L/E)` lies inside the inertia
subgroup of `v` in `Gal(L/F)`.**  No finiteness is assumed. -/
theorem inertiaSubgroup_eq_top_iff (v : AbsoluteValue L ℝ) :
    v.inertiaSubgroup ↥E = ⊤ ↔ E.fixingSubgroup ≤ v.inertiaSubgroup F := by
  rw [v.inertiaSubgroup_eq_comap F ↥E, eq_top_iff,
    ← IntermediateField.range_restrictRestrictAlgEquivMapHom_eq_fixingSubgroup' F E]
  constructor
  · rintro h _ ⟨τ, rfl⟩
    exact h (Subgroup.mem_top τ)
  · exact fun h τ _ ↦ h ⟨τ, rfl⟩

/-- If `E / F` is unramified everywhere then every inertia subgroup of `L / F` lies in
`Gal(L/E)`.  This is the direction `L₀ ⊆ L∞^H` of the claim `L₀ = L∞^H` in Step 1 of
Washington's Lemma 13.15. -/
theorem inertiaSubgroup_le_fixingSubgroup [NumberField.IsUnramifiedEverywhere F ↥E]
    (w : AbsoluteValue L ℝ) : w.inertiaSubgroup F ≤ E.fixingSubgroup := by
  intro σ hσ
  rw [← E.restrictNormalHom_ker, MonoidHom.mem_ker]
  have h : AlgEquiv.restrictNormalHom ↥E σ ∈
      (w.inertiaSubgroup F).map (AlgEquiv.restrictNormalHom ↥E) := Subgroup.mem_map_of_mem _ hσ
  rw [map_inertiaSubgroup_eq_of_liesOver F (w.comp (algebraMap ↥E L).injective) w,
    inertiaSubgroup_eq_bot_of_isUnramifiedEverywhere F _, Subgroup.mem_bot] at h
  exact h

/-- Conversely, if every inertia subgroup of `L / F` lies in `Gal(L/E)` then `E / F` is
unramified everywhere.  This is the direction `L∞^H ⊆ L₀` (the unramifiedness half of it) of the
claim `L₀ = L∞^H` in Step 1 of Washington's Lemma 13.15. -/
theorem isUnramifiedEverywhere_of_inertiaSubgroup_le_fixingSubgroup
    (h : ∀ w : AbsoluteValue L ℝ, w.inertiaSubgroup F ≤ E.fixingSubgroup) :
    NumberField.IsUnramifiedEverywhere F ↥E := by
  haveI : Algebra.IsAlgebraic ↥E L :=
    Algebra.IsAlgebraic.tower_top (K := F) (L := ↥E) (A := L)
  rw [NumberField.isUnramifiedEverywhere_iff]
  intro u _
  obtain ⟨w, hw⟩ := u.exists_liesOver L
  rw [u.isUnramified_spec F w, IsUnramifiedOfIsScalarTower,
    IntermediateField.range_restrictRestrictAlgEquivMapHom_eq_fixingSubgroup' F E]
  exact h w

/-- **`E / F` is unramified everywhere exactly when every inertia subgroup of `L / F` lies in
`Gal(L/E)`.**  No finiteness is assumed anywhere: this is the infinite-extension form of the
claim `L₀ = L∞^H` in Step 1 of Washington's Lemma 13.15. -/
theorem isUnramifiedEverywhere_iff_forall_inertiaSubgroup_le :
    NumberField.IsUnramifiedEverywhere F ↥E ↔
      ∀ w : AbsoluteValue L ℝ, w.inertiaSubgroup F ≤ E.fixingSubgroup :=
  ⟨fun _ ↦ inertiaSubgroup_le_fixingSubgroup F E,
    isUnramifiedEverywhere_of_inertiaSubgroup_le_fixingSubgroup F E⟩

end Top

section Closed

open Topology

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [Algebra.IsIntegral F L]

/-- For the Krull topology, `{σ | σ x ∈ S}` is open: it is a union of left cosets of the open
stabilizer of `x`. -/
theorem isOpen_setOf_apply_mem (x : L) (S : Set L) : IsOpen {σ : Gal(L/F) | σ x ∈ S} := by
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ ↦ σ * τ) '' (MulAction.stabilizer Gal(L/F) x : Set Gal(L/F)), ?_,
    (Homeomorph.mulLeft σ).isOpen_image.2 (stabilizer_isOpen_of_isIntegral x),
    ⟨1, one_mem _, mul_one σ⟩⟩
  rintro _ ⟨g, hg, rfl⟩
  have hgx : g x = x := hg
  simpa [AlgEquiv.mul_apply, hgx] using hσ

/-- The same set is closed, its complement being of the same form. -/
theorem isClosed_setOf_apply_mem (x : L) (S : Set L) : IsClosed {σ : Gal(L/F) | σ x ∈ S} := by
  rw [← isOpen_compl_iff]
  exact isOpen_setOf_apply_mem x Sᶜ

/-- **The decomposition subgroup of a place is closed** in the Krull topology, with no
finiteness assumption on `L / F`. -/
theorem isClosed_decompositionSubgroup (F : Type*) [Field F] [Algebra F L]
    [Algebra.IsIntegral F L] (v : AbsoluteValue L ℝ) :
    IsClosed (v.decompositionSubgroup F : Set Gal(L/F)) := by
  have : (v.decompositionSubgroup F : Set Gal(L/F)) =
      ⋂ x : L, {σ : Gal(L/F) | σ x ∈ {y | v y = v x}} := by
    ext σ
    simp [mem_decompositionSubgroup_iff_forall_apply_eq]
  rw [this]
  exact isClosed_iInter fun x ↦ isClosed_setOf_apply_mem x _

/-- **The inertia subgroup of a place is closed** in the Krull topology, with no finiteness
assumption on `L / F`.  This is what feeds `EquivMvZp.exists_Γpow_le_of_isClosed`. -/
theorem isClosed_inertiaSubgroup (F : Type*) [Field F] [Algebra F L]
    [Algebra.IsIntegral F L] (v : AbsoluteValue L ℝ) :
    IsClosed (v.inertiaSubgroup F : Set Gal(L/F)) := by
  by_cases hv : IsNonarchimedean v
  · have : (v.inertiaSubgroup F : Set Gal(L/F)) =
        (v.decompositionSubgroup F : Set Gal(L/F)) ∩
          ⋂ x ∈ {x : L | v x ≤ 1}, {σ : Gal(L/F) | σ x ∈ {y | v (y - x) < 1}} := by
      ext σ
      simp [mem_inertiaSubgroup_iff_of_isNonarchimedean _ hv]
    rw [this]
    exact (isClosed_decompositionSubgroup F v).inter
      (isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦ isClosed_setOf_apply_mem x _)
  · rw [inertiaSubgroup_eq_decompositionSubgroup_of_not_isNonarchimedean _ _ hv]
    exact isClosed_decompositionSubgroup F v

end Closed

end AbsoluteValue
