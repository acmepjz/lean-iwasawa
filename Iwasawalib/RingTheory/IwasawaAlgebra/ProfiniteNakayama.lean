/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.ProfiniteModule
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Topology.Algebra.ClopenNhdofOne

@[expose] public section

/-!
# Nakayama's lemma for compact modules

Blueprint node `p:nak` (Nakayama's lemma, pro-`p` version).

Let `R` be a compact topological *local* ring, `t` an element of its maximal ideal, and `Z` a
profinite topological `R`-module (compact, Hausdorff, totally disconnected, with continuous
action).  If `x₁, …, x_n ∈ Z` have images generating `Z / t Z`, then they generate `Z` as an
`R`-module: `Submodule.eq_top_span_of_sup_smul_top_le`.

The blueprint runs the argument through `Z = lim_V Z/V` and the nilpotency of the maximal ideal
of a finite local ring.  The proof below is the same in substance but shorter, because mathlib's
ordinary Nakayama lemma (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`) already applies to the
*finite* — hence finitely generated — modules `Z / (N ⊔ V)`:

* for every open `R`-submodule `V` the quotient `Z ⧸ (N ⊔ V)` is finite (compactness), and `t`
  lies in the Jacobson radical of the local ring `R`, so Nakayama gives `N ⊔ V = ⊤`;
* the open `R`-submodules are a neighbourhood basis of `0`
  (`AddSubgroup.isOpen_moduleCore` of `ProfiniteModule.lean`, plus the fact that a clopen
  neighbourhood of `0` in a compact group contains an open subgroup), so `N` closed and
  `N ⊔ V = ⊤` for all such `V` forces `N = ⊤`.
-/

open Topology Set

namespace IwasawaAlgebra

section Basis

variable {R Z : Type*} [Ring R] [TopologicalSpace R] [CompactSpace R]
  [AddCommGroup Z] [Module R Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z]
  [CompactSpace Z] [T2Space Z] [TotallyDisconnectedSpace Z] [ContinuousSMul R Z]

/-- In a profinite module over a compact ring, the open submodules form a neighbourhood basis
of `0`. -/
theorem exists_isOpen_submodule_subset_of_mem_nhds {U : Set Z} (hU : U ∈ 𝓝 (0 : Z)) :
    ∃ V : Submodule R Z, IsOpen (V : Set Z) ∧ (V : Set Z) ⊆ U := by
  obtain ⟨O, hOU, hOopen, hO0⟩ := mem_nhds_iff.1 hU
  obtain ⟨W, hWclopen, hW0, hWO⟩ := compact_exists_isClopen_in_isOpen hOopen hO0
  obtain ⟨H, hH⟩ :=
    IsTopologicalAddGroup.exist_openAddSubgroup_sub_clopen_nhds_of_zero hWclopen hW0
  exact ⟨H.toAddSubgroup.moduleCore R, H.toAddSubgroup.isOpen_moduleCore H.isOpen,
    (H.toAddSubgroup.moduleCore_le).trans (hH.trans (hWO.trans hOU))⟩

end Basis

section Nakayama

variable {R Z : Type*} [CommRing R] [IsLocalRing R] [TopologicalSpace R] [CompactSpace R]
  [AddCommGroup Z] [Module R Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z]
  [CompactSpace Z] [T2Space Z] [TotallyDisconnectedSpace Z] [ContinuousSMul R Z]

omit [IsLocalRing R] [TopologicalSpace R] [CompactSpace R] [T2Space Z]
  [TotallyDisconnectedSpace Z] [ContinuousSMul R Z] in
/-- If `V` is an open `R`-submodule then `Z ⧸ V` is finite. -/
theorem finite_quotient_of_isOpen (V : Submodule R Z) (hV : IsOpen (V : Set Z)) :
    Finite (Z ⧸ V) := by
  haveI : Finite (Z ⧸ V.toAddSubgroup) :=
    AddSubgroup.quotient_finite_of_isOpen V.toAddSubgroup hV
  refine Finite.of_surjective
    (QuotientAddGroup.lift V.toAddSubgroup (V.mkQ.toAddMonoidHom) fun x hx ↦ ?_) ?_
  · simpa using (Submodule.Quotient.mk_eq_zero V).2 hx
  · intro z
    obtain ⟨w, rfl⟩ := V.mkQ_surjective z
    exact ⟨QuotientAddGroup.mk w, rfl⟩

/-- **Blueprint node `p:nak`** (Nakayama's lemma, compact version), submodule form:
a *closed* submodule `N` of a profinite module `Z` over a compact local ring `R` with
`Z = N + t Z` for some `t` in the maximal ideal is all of `Z`. -/
theorem eq_top_of_isClosed_of_sup_smul_top_le {t : R} (ht : t ∈ IsLocalRing.maximalIdeal R)
    (N : Submodule R Z) (hNclosed : IsClosed (N : Set Z))
    (h : (⊤ : Submodule R Z) ≤ N ⊔ (Ideal.span {t}) • (⊤ : Submodule R Z)) :
    N = ⊤ := by
  have hjac : Ideal.span {t} ≤ Ideal.jacobson (⊥ : Ideal R) :=
    (Ideal.span_le.2 (by simpa using ht)).trans (IsLocalRing.maximalIdeal_le_jacobson _)
  -- every open submodule `V` satisfies `N ⊔ V = ⊤`
  have key : ∀ V : Submodule R Z, IsOpen (V : Set Z) → N ⊔ V = ⊤ := by
    intro V hV
    set W : Submodule R Z := N ⊔ V with hW
    have hWopen : IsOpen (W : Set Z) :=
      AddSubgroup.isOpen_mono (H₁ := V.toAddSubgroup) (H₂ := W.toAddSubgroup)
        (fun x hx ↦ (le_sup_right : V ≤ W) hx) hV
    haveI : Finite (Z ⧸ W) := finite_quotient_of_isOpen W hWopen
    have htop : (⊤ : Submodule R (Z ⧸ W)) ≤ (Ideal.span {t}) • (⊤ : Submodule R (Z ⧸ W)) := by
      intro z _
      obtain ⟨y, rfl⟩ := W.mkQ_surjective z
      have hy : y ∈ N ⊔ (Ideal.span {t}) • (⊤ : Submodule R Z) := h Submodule.mem_top
      rw [Submodule.mem_sup] at hy
      obtain ⟨n, hn, u, hu, rfl⟩ := hy
      have hn0 : W.mkQ n = 0 := (Submodule.Quotient.mk_eq_zero W).2 ((le_sup_left : N ≤ W) hn)
      have : W.mkQ (n + u) = W.mkQ u := by rw [map_add, hn0, zero_add]
      rw [this]
      have := Submodule.mem_map_of_mem (f := W.mkQ) hu
      rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
    have hbot : (⊤ : Submodule R (Z ⧸ W)) = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ ⊤ (Module.Finite.fg_top) htop hjac
    have hzero : ∀ y : Z ⧸ W, y = 0 := fun y ↦ by
      have : y ∈ (⊥ : Submodule R (Z ⧸ W)) := hbot ▸ Submodule.mem_top
      simpa using this
    rw [eq_top_iff]
    intro z _
    have : W.mkQ z = 0 := hzero _
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  -- hence `N` is dense, and it is closed
  refine eq_top_iff.2 fun z _ ↦ ?_
  show z ∈ (N : Set Z)
  rw [← hNclosed.closure_eq, mem_closure_iff_nhds]
  intro U hU
  obtain ⟨V, hVopen, hVU⟩ :=
    exists_isOpen_submodule_subset_of_mem_nhds (R := R) (U := (fun w ↦ z + w) ⁻¹' U) (by
      have : Continuous fun w : Z ↦ z + w := continuous_const.add continuous_id
      simpa using this.continuousAt.preimage_mem_nhds (by simpa using hU))
  have hz : z ∈ N ⊔ V := by rw [key V hVopen]; trivial
  rw [Submodule.mem_sup] at hz
  obtain ⟨n, hn, v, hv, hnv⟩ := hz
  refine ⟨n, ?_, hn⟩
  have : n = z + (-v) := by rw [← hnv]; abel
  rw [this]
  exact hVU (V.neg_mem hv)

end Nakayama

section Span

variable {R Z : Type*} [CommRing R] [IsLocalRing R] [TopologicalSpace R] [CompactSpace R]
  [AddCommGroup Z] [Module R Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z]
  [CompactSpace Z] [T2Space Z] [TotallyDisconnectedSpace Z] [ContinuousSMul R Z]

omit [IsLocalRing R] [CompactSpace Z] [TotallyDisconnectedSpace Z] in
/-- The `R`-span of a finite set in a module over a compact ring is compact, hence closed. -/
theorem isClosed_span_finset (s : Finset Z) :
    IsClosed ((Submodule.span R (s : Set Z) : Submodule R Z) : Set Z) := by
  have hcont : Continuous fun c : (↥s) → R ↦ ∑ a : ↥s, c a • (a : Z) :=
    continuous_finsetSum _ fun a _ ↦ (continuous_apply a).smul continuous_const
  have hrange : Set.range (fun c : (↥s) → R ↦ ∑ a : ↥s, c a • (a : Z))
      = (Submodule.span R (s : Set Z) : Set Z) := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem _ fun a _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span a.2)
    · intro hx
      obtain ⟨f, hf⟩ := Submodule.mem_span_finset' (s := s).1 hx
      exact ⟨f, hf⟩
  rw [← hrange]
  exact (isCompact_range hcont).isClosed

/-- **Blueprint node `p:nak`** (Nakayama's lemma, pro-`p` version).  Let `R` be a compact local
topological ring, `t` an element of its maximal ideal, and `Z` a profinite `R`-module.  If the
images of `x ∈ s` generate `Z / t Z`, then `s` generates `Z` as an `R`-module. -/
theorem eq_top_span_of_sup_smul_top_le {t : R} (ht : t ∈ IsLocalRing.maximalIdeal R)
    (s : Finset Z)
    (h : (⊤ : Submodule R Z) ≤
      Submodule.span R (s : Set Z) ⊔ (Ideal.span {t}) • (⊤ : Submodule R Z)) :
    Submodule.span R (s : Set Z) = ⊤ :=
  eq_top_of_isClosed_of_sup_smul_top_le ht _ (isClosed_span_finset s) h

end Span

end IwasawaAlgebra
