/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.LambdaTopology
public import Iwasawalib.RingTheory.IwasawaAlgebra.ProfiniteNakayama

@[expose] public section

/-!
# Nakayama's lemma for compact `Λ`-modules

`Iwasawalib.RingTheory.IwasawaAlgebra.ProfiniteNakayama` proves blueprint node `p:nak` for an
abstract compact local topological ring `R`.  Now that `Λ = ℤ_p⟦X⟧` carries a topology making
it such a ring (`Iwasawalib.RingTheory.IwasawaAlgebra.LambdaTopology`), this file instantiates
it at `R = Λ` and `t = X = T = γ - 1`, and derives the form that is actually used in Iwasawa
theory: *a profinite `Λ`-module `Z` with `Z / T Z` finite is a finitely generated
`Λ`-module.*

## Main results

* `IwasawaAlgebra.eq_top_of_isClosed_of_sup_ideal_smul_top_le`: the ideal-valued version of
  `IwasawaAlgebra.eq_top_of_isClosed_of_sup_smul_top_le`.
* `IwasawaAlgebra.moduleFinite_of_finite_quotient_smul`: a profinite module over a compact
  local ring with finite `Z / t Z` is finitely generated.
* `IwasawaAlgebra.span_eq_top_of_sup_X_smul_top_le`, `IwasawaAlgebra.lambdaModuleFinite`:
  the `Λ`-instances.
-/

open Topology Set PowerSeries
open scoped PowerSeries.WithPiTopology

namespace IwasawaAlgebra

section GeneralIdeal

variable {R Z : Type*} [CommRing R] [IsLocalRing R] [TopologicalSpace R] [CompactSpace R]
  [AddCommGroup Z] [Module R Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z]
  [CompactSpace Z] [T2Space Z] [TotallyDisconnectedSpace Z] [ContinuousSMul R Z]

/-- **Blueprint node `p:nak`, ideal form.**  A closed submodule `N` of a profinite module `Z`
over a compact local ring `R` with `Z = N + I Z` for an ideal `I` inside the maximal ideal is
all of `Z`.  Same proof as `IwasawaAlgebra.eq_top_of_isClosed_of_sup_smul_top_le`, with
`Ideal.span {t}` replaced by `I`. -/
theorem eq_top_of_isClosed_of_sup_ideal_smul_top_le {I : Ideal R}
    (hI : I ≤ IsLocalRing.maximalIdeal R)
    (N : Submodule R Z) (hNclosed : IsClosed (N : Set Z))
    (h : (⊤ : Submodule R Z) ≤ N ⊔ I • (⊤ : Submodule R Z)) :
    N = ⊤ := by
  have hjac : I ≤ Ideal.jacobson (⊥ : Ideal R) :=
    hI.trans (IsLocalRing.maximalIdeal_le_jacobson _)
  have key : ∀ V : Submodule R Z, IsOpen (V : Set Z) → N ⊔ V = ⊤ := by
    intro V hV
    set W : Submodule R Z := N ⊔ V with hW
    have hWopen : IsOpen (W : Set Z) :=
      AddSubgroup.isOpen_mono (H₁ := V.toAddSubgroup) (H₂ := W.toAddSubgroup)
        (fun x hx ↦ (le_sup_right : V ≤ W) hx) hV
    haveI : Finite (Z ⧸ W) := finite_quotient_of_isOpen W hWopen
    have htop : (⊤ : Submodule R (Z ⧸ W)) ≤ I • (⊤ : Submodule R (Z ⧸ W)) := by
      intro z _
      obtain ⟨y, rfl⟩ := W.mkQ_surjective z
      have hy : y ∈ N ⊔ I • (⊤ : Submodule R Z) := h Submodule.mem_top
      rw [Submodule.mem_sup] at hy
      obtain ⟨n, hn, u, hu, rfl⟩ := hy
      have hn0 : W.mkQ n = 0 := (Submodule.Quotient.mk_eq_zero W).2 ((le_sup_left : N ≤ W) hn)
      have hrw : W.mkQ (n + u) = W.mkQ u := by rw [map_add, hn0, zero_add]
      rw [hrw]
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
  have hn' : n = z + (-v) := by rw [← hnv]; abel
  rw [hn']
  exact hVU (V.neg_mem hv)

/-- **Blueprint node `p:nak`, ideal-and-span form.** -/
theorem eq_top_span_of_sup_ideal_smul_top_le {I : Ideal R}
    (hI : I ≤ IsLocalRing.maximalIdeal R) (s : Finset Z)
    (h : (⊤ : Submodule R Z) ≤ Submodule.span R (s : Set Z) ⊔ I • (⊤ : Submodule R Z)) :
    Submodule.span R (s : Set Z) = ⊤ :=
  eq_top_of_isClosed_of_sup_ideal_smul_top_le hI _ (isClosed_span_finset s) h

/-- **Finite generation from a finite quotient.**  If `Z` is a profinite module over a compact
local ring `R` and `Z / I Z` is finite for some ideal `I` inside the maximal ideal, then `Z`
is a finitely generated `R`-module. -/
theorem moduleFinite_of_finite_quotient_ideal_smul {I : Ideal R}
    (hI : I ≤ IsLocalRing.maximalIdeal R)
    (hfin : Finite (Z ⧸ (I • (⊤ : Submodule R Z)))) :
    Module.Finite R Z := by
  classical
  set N : Submodule R Z := I • (⊤ : Submodule R Z) with hN
  haveI := hfin
  haveI : Fintype (Z ⧸ N) := Fintype.ofFinite _
  -- pick a set-theoretic section of `Z → Z ⧸ N`
  choose sec hsec using N.mkQ_surjective
  set s : Finset Z := Finset.image sec (Finset.univ : Finset (Z ⧸ N)) with hs
  have hspan : Submodule.span R (s : Set Z) = ⊤ := by
    refine eq_top_span_of_sup_ideal_smul_top_le hI s (fun z _ ↦ ?_)
    have hmem : sec (N.mkQ z) ∈ s := Finset.mem_image_of_mem sec (Finset.mem_univ _)
    have hdiff : z - sec (N.mkQ z) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero N, ← Submodule.mkQ_apply, map_sub, hsec, sub_self]
    have : z = sec (N.mkQ z) + (z - sec (N.mkQ z)) := by abel
    rw [this]
    exact Submodule.add_mem_sup (Submodule.subset_span hmem) hdiff
  exact ⟨⟨s, by rw [hspan]⟩⟩

/-- The single-element version of `moduleFinite_of_finite_quotient_ideal_smul`. -/
theorem moduleFinite_of_finite_quotient_smul {t : R} (ht : t ∈ IsLocalRing.maximalIdeal R)
    (hfin : Finite (Z ⧸ ((Ideal.span {t}) • (⊤ : Submodule R Z)))) :
    Module.Finite R Z :=
  moduleFinite_of_finite_quotient_ideal_smul (Ideal.span_le.2 (by simpa using ht)) hfin

end GeneralIdeal

section Lambda

variable {p : ℕ} [Fact p.Prime] {Z : Type*} [AddCommGroup Z] [Module ℤ_[p]⟦X⟧ Z]
  [TopologicalSpace Z] [IsTopologicalAddGroup Z] [CompactSpace Z] [T2Space Z]
  [TotallyDisconnectedSpace Z] [ContinuousSMul ℤ_[p]⟦X⟧ Z]

/-- **Blueprint node `p:nak` for `Λ = ℤ_p⟦X⟧`, literally.**  Let `Z` be a profinite
`Λ`-module.  If the images of a finite set `s ⊆ Z` generate `Z / T Z` (`T = X = γ - 1`), then
`s` generates `Z` as a `Λ`-module. -/
theorem span_eq_top_of_sup_X_smul_top_le (s : Finset Z)
    (h : (⊤ : Submodule ℤ_[p]⟦X⟧ Z) ≤ Submodule.span ℤ_[p]⟦X⟧ (s : Set Z) ⊔
      (Ideal.span {(X : ℤ_[p]⟦X⟧)}) • (⊤ : Submodule ℤ_[p]⟦X⟧ Z)) :
    Submodule.span ℤ_[p]⟦X⟧ (s : Set Z) = ⊤ :=
  eq_top_span_of_sup_smul_top_le (X_mem_maximalIdeal p) s h

/-- **Blueprint node `p:nak` for `Λ`, maximal-ideal form**: `s` generates `Z` as soon as it
generates `Z / (p, T) Z`. -/
theorem span_eq_top_of_sup_maximalIdeal_smul_top_le (s : Finset Z)
    (h : (⊤ : Submodule ℤ_[p]⟦X⟧ Z) ≤ Submodule.span ℤ_[p]⟦X⟧ (s : Set Z) ⊔
      (PowerSeries.idealAX (p : ℤ_[p])) • (⊤ : Submodule ℤ_[p]⟦X⟧ Z)) :
    Submodule.span ℤ_[p]⟦X⟧ (s : Set Z) = ⊤ :=
  eq_top_span_of_sup_ideal_smul_top_le
    (le_of_eq (maximalIdeal_powerSeries_eq_idealAX p).symm) s h

/-- **A profinite `Λ`-module with finite `Z / T Z` is a finitely generated `Λ`-module.**
This is the form of `p:nak` used to prove that `X_n` is a finitely generated `Λ`-module
(blueprint node `Xn-isom-qout-of-totally-ramified`, Step 3). -/
theorem lambdaModuleFinite_of_finite_quotient_X_smul
    (hfin : Finite (Z ⧸ ((Ideal.span {(X : ℤ_[p]⟦X⟧)}) • (⊤ : Submodule ℤ_[p]⟦X⟧ Z)))) :
    Module.Finite ℤ_[p]⟦X⟧ Z :=
  moduleFinite_of_finite_quotient_smul (X_mem_maximalIdeal p) hfin

/-- Maximal-ideal version of `lambdaModuleFinite_of_finite_quotient_X_smul`. -/
theorem lambdaModuleFinite_of_finite_quotient_maximalIdeal_smul
    (hfin : Finite (Z ⧸ ((PowerSeries.idealAX (p : ℤ_[p])) • (⊤ : Submodule ℤ_[p]⟦X⟧ Z)))) :
    Module.Finite ℤ_[p]⟦X⟧ Z :=
  moduleFinite_of_finite_quotient_ideal_smul
    (le_of_eq (maximalIdeal_powerSeries_eq_idealAX p).symm) hfin

end Lambda

end IwasawaAlgebra
