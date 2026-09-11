/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.FgTorsion
public import Iwasawalib.RingTheory.IwasawaAlgebra.NuSubmodule

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# Step 3 of `Xn-isom-qout-of-totally-ramified` from a finite-index submodule and finitely
many extra generators

`Iwasawalib.RingTheory.IwasawaAlgebra.FgTorsion` proves Step 3 of blueprint node
`Xn-isom-qout-of-totally-ramified` from two hypotheses phrased directly in terms of `ℤ_p`-module
data (`IwasawaAlgebra.moduleFinite_and_isTorsion_of_finite_index`): a finitely generated
`Y / TM`, and, for each `n`, a finite-index submodule covered modulo `ω_n M` by boundedly many
elements.  This file removes the second hypothesis's covering data, deriving it from the first,
so that what is left is exactly the geometric input of the blueprint:

* a `Λ`-submodule `Y` of finite index, with `ω_e M ⊆ Y` (in the application
  `Y = Gal(L∞/L_e K∞)` and `ω_e M = (γ^{p^e} - 1) X∞`);
* a finite set `a` (in the application `a₂, …, a_s`, one element per ramified prime beyond the
  first) with `Y ⊆ ℤ_p·a + ω_e M`;
* finiteness of `M / ν_{n,e} Y` for `n ≥ e` (in the application `M / ν_{n,e} Y ≅ X_n`, which is
  class field theory).

The bridge is `IwasawaAlgebra.exists_mem_span_nu_smul`: applying `ν_{n,e}` to
`Y ⊆ ℤ_p·a + ω_e M` gives `ν_{n,e} Y ⊆ ℤ_p·(ν_{n,e} a) + ω_n M`, because
`ν_{n,e} ω_e = ω_n` (`IwasawaAlgebra.coe_oneAddXPowSubOne_mul_coe_nu`).  The `ℤ_p`-rank of
`M / ω_n M` is therefore at most `#a` for every `n ≥ e`, uniformly, and blueprint node
`p:rank-growth` forces the `Λ`-rank to vanish.

## Main results

* `IwasawaAlgebra.moduleFinite_quotient_X_smul_of_le_span`: `M / TM` is a finitely generated
  `ℤ_p`-module.
* `IwasawaAlgebra.isTorsion_of_forall_ge_finrank_quotSMulTop_omega_le`: the `n ≥ n₀` form of
  `IwasawaAlgebra.isTorsion_of_forall_finrank_quotSMulTop_omega_le`.
* `IwasawaAlgebra.exists_mem_span_nu_smul`: `ν_{n,e} Y ⊆ ℤ_p·(ν_{n,e} a) + ω_n M`.
* `IwasawaAlgebra.moduleFinite_and_isTorsion_of_le_span`: **Step 3**, from the geometric data.
-/

open Module PowerSeries
open scoped Pointwise
open scoped PowerSeries.WithPiTopology

namespace IwasawaAlgebra

variable {p : ℕ} [Fact p.Prime]

/-! ### Quotients by a submodule and by its underlying subgroup -/

/-- A submodule and an additive subgroup with the same carrier have the same quotient set.
This is `IwasawaAlgebra.quotientEquivQuotientAddSubgroup` with the `Λ`-module structure and the
closedness dropped: only the carriers matter. -/
def quotientEquivQuotientAddSubgroupOfCoe {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (S : AddSubgroup M) (h : (N : Set M) = (S : Set M)) :
    (M ⧸ N) ≃ (M ⧸ S) :=
  Quotient.congr (Equiv.refl M) fun a b ↦ by
    have hmem : ∀ z : M, z ∈ N ↔ z ∈ S := fun z ↦ Set.ext_iff.1 h z
    rw [Submodule.quotientRel_def, QuotientAddGroup.leftRel_apply, hmem]
    simp only [Equiv.refl_apply]
    constructor
    · intro hab
      have hn := S.neg_mem hab
      rwa [show -(a - b) = -a + b by abel] at hn
    · intro hab
      have hn := S.neg_mem hab
      rwa [show -(-a + b) = a - b by abel] at hn

/-! ### `ω_e` is divisible by `T` -/

/-- `T = X` divides `ω_k = (1 + X) ^ k - 1` in `Λ`. -/
theorem X_dvd_coe_oneAddXPowSubOne (k : ℕ) :
    (X : ℤ_[p]⟦X⟧) ∣ ((Polynomial.oneAddXPowSubOne ℤ_[p] k : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) := by
  obtain ⟨c, hc⟩ := Polynomial.X_dvd_oneAddXPowSubOne ℤ_[p] k
  refine ⟨(c : ℤ_[p]⟦X⟧), ?_⟩
  rw [← Polynomial.coe_X (R := ℤ_[p]), ← Polynomial.coe_mul, ← hc]

section Module

variable {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module ℤ_[p]⟦X⟧ M]

/-- `ω_e M ⊆ T M`. -/
theorem omega_smul_top_le_X_smul_top (e : ℕ) :
    Ideal.span {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ e) : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧)} •
        (⊤ : Submodule ℤ_[p]⟦X⟧ M)
      ≤ Ideal.span {(X : ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ M) := by
  refine Submodule.smul_mono ?_ le_rfl
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
  exact X_dvd_coe_oneAddXPowSubOne _

end Module

/-! ### Finitely generated coinvariants -/

section Coinvariants

variable {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module ℤ_[p]⟦X⟧ M]
  [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M]

/-- **Step 3, first half, in the form the geometry supplies it.**  If `Y` is a `ℤ_p`-submodule
of finite index in `M` contained in `ℤ_p·a + TM` for a finite set `a`, then the coinvariants
`M / TM` are a finitely generated `ℤ_p`-module. -/
theorem moduleFinite_quotient_X_smul_of_le_span (Y : Submodule ℤ_[p] M) (a : Finset M)
    (hMY : Finite (M ⧸ Y))
    (hY : Y ≤ Submodule.span ℤ_[p] (a : Set M) ⊔
      ((Ideal.span {(X : ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ M)).restrictScalars ℤ_[p])) :
    Module.Finite ℤ_[p]
      (M ⧸ ((Ideal.span {(X : ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ M)).restrictScalars
        ℤ_[p])) := by
  classical
  haveI := hMY
  set N : Submodule ℤ_[p] M :=
    (Ideal.span {(X : ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ M)).restrictScalars ℤ_[p] with hN
  set s : Finset (M ⧸ N) := a.image N.mkQ with hs
  set S : Submodule ℤ_[p] (M ⧸ N) := Submodule.span ℤ_[p] (s : Set (M ⧸ N)) with hS
  haveI : Module.Finite ℤ_[p] ↥S := Module.Finite.iff_fg.2 ⟨s, rfl⟩
  have hker : Y ≤ LinearMap.ker (S.mkQ.comp N.mkQ) := by
    intro y hy
    obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.1 (hY hy)
    have hw0 : N.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero N).2 hw
    have hvS : N.mkQ v ∈ S := by
      have h := Submodule.apply_mem_span_image_of_mem_span (f := N.mkQ) hv
      rwa [hS, hs, Finset.coe_image]
    have hvw : N.mkQ (v + w) = N.mkQ v := by rw [map_add, hw0, add_zero]
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, hvw,
      Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero S).2 hvS
  haveI : Finite ((M ⧸ N) ⧸ S) := by
    refine Finite.of_surjective (Submodule.liftQ Y _ hker) ?_
    refine Function.Surjective.of_comp (g := Y.mkQ) ?_
    have h : (Submodule.liftQ Y (S.mkQ.comp N.mkQ) hker) ∘ Y.mkQ = S.mkQ ∘ N.mkQ := rfl
    rw [h]
    exact (Submodule.mkQ_surjective S).comp (Submodule.mkQ_surjective N)
  haveI : Module.Finite ℤ_[p] ((M ⧸ N) ⧸ S) := Module.Finite.of_finite
  exact Module.Finite.of_submodule_quotient S

end Coinvariants

/-! ### The covering of `ν_{n,e} Y` modulo `ω_n M` -/

section Covering

variable {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module ℤ_[p]⟦X⟧ M]
  [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M]

variable (M) in
/-- Multiplication by `r : Λ`, as a `ℤ_p`-linear endomorphism of `M`.  It is how `ν_{n,e} Y`
is formed for a submodule `Y` which is only assumed `ℤ_p`-stable: in the application `Y` is an
arbitrary closed subgroup of `X∞`, and closed subgroups of `X∞` are automatically
`ℤ_p`-submodules but not `Λ`-submodules. -/
noncomputable def lsmulZp (r : ℤ_[p]⟦X⟧) : M →ₗ[ℤ_[p]] M :=
  (LinearMap.lsmul ℤ_[p]⟦X⟧ M r).restrictScalars ℤ_[p]

@[simp]
theorem lsmulZp_apply (r : ℤ_[p]⟦X⟧) (z : M) : lsmulZp M r z = r • z := rfl

/-- `ν_{n,e} · (ω_e M) = ω_n M`, the submodule half of
`IwasawaAlgebra.coe_oneAddXPowSubOne_mul_coe_nu`.  It is the computation `h1` inside
`IwasawaAlgebra.nu_smul_sup_span`, isolated. -/
theorem nu_smul_omega_smul_top {n e : ℕ} (h : e ≤ n) :
    ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) •
        (Ideal.span {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ e) : Polynomial ℤ_[p]) :
          ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ M))
      = Ideal.span {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) :
          ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ M) := by
  rw [← Submodule.ideal_span_singleton_smul, ← Submodule.mul_smul,
    Ideal.span_singleton_mul_span_singleton, mul_comm, coe_oneAddXPowSubOne_mul_coe_nu h]

/-- **`ν_{n,e} Y ⊆ ℤ_p·(ν_{n,e} a) + ω_n M`.**  Apply `ν_{n,e}` to `Y ⊆ ℤ_p·a + ω_e M`: the
`ℤ_p`-coefficients pass through because `ν_{n,e} · (-)` is `ℤ_p`-linear, and
`ν_{n,e} ω_e = ω_n`.  This is the hypothesis `hcov` of
`IwasawaAlgebra.finrank_quotSMulTop_le_card`, with a spanning set of `#a` elements independent
of `n`. -/
theorem exists_mem_span_nu_smul [DecidableEq M] (Y : Submodule ℤ_[p] M) (a : Finset M)
    {n e : ℕ} (he : e ≤ n)
    (hY : Y ≤ Submodule.span ℤ_[p] (a : Set M) ⊔
      ((Ideal.span {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ e) : Polynomial ℤ_[p]) :
        ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ M)).restrictScalars ℤ_[p]))
    (y : M)
    (hy : y ∈ Submodule.map
      (lsmulZp M ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧)) Y) :
    ∃ v ∈ Submodule.span ℤ_[p]
        ((a.image fun z ↦ ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • z :
          Finset M) : Set M),
      y - v ∈ Ideal.span {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) :
        ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ M) := by
  classical
  set nu : ℤ_[p]⟦X⟧ := ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) with hnu
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.1 (hY hz)
  refine ⟨lsmulZp M nu v, ?_, ?_⟩
  · have h := Submodule.apply_mem_span_image_of_mem_span (f := lsmulZp M nu) hv
    rw [Finset.coe_image]
    exact h
  · have hsub : lsmulZp M nu (v + w) - lsmulZp M nu v = nu • w := by
      rw [map_add, add_sub_cancel_left, lsmulZp_apply]
    rw [hsub, ← nu_smul_omega_smul_top (M := M) he]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hw

end Covering

/-! ### Torsion from the `ω_n`-coinvariants, above a threshold -/

section Threshold

variable {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module ℤ_[p]⟦X⟧ M]
  [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]

/-- **Blueprint node `Xn-isom-qout-of-totally-ramified`, Step 3, second half, above a
threshold.**  `IwasawaAlgebra.isTorsion_of_forall_finrank_quotSMulTop_omega_le` asks for the
rank bound at *every* `n`; the geometry only supplies it for `n ≥ e`, where `e` is the layer
above which `K∞` is totally ramified.  That is enough, because the contradiction is drawn at
one large `n`. -/
theorem isTorsion_of_forall_ge_finrank_quotSMulTop_omega_le (n₀ c : ℕ)
    (hle : ∀ n : ℕ, n₀ ≤ n → Module.finrank ℤ_[p] (QuotSMulTop
      ((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) M) ≤ c) :
    Module.IsTorsion ℤ_[p]⟦X⟧ M := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨c', hc'⟩ := exists_bound_finrank_quotSMulTop_omega (p := p) M
  refine isTorsion_of_finrank_eq_zero ?_
  by_contra hne
  set r := Module.finrank ℤ_[p]⟦X⟧ M with hr
  set n := max n₀ (c + c' + 1) with hn
  have hn₀ : n₀ ≤ n := le_max_left _ _
  have hnlt : c + c' < n := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have hpow : c + c' < p ^ n := lt_of_lt_of_le hnlt (Nat.lt_pow_self hp1).le
  have h1 := hc' n
  have h2 := hle n hn₀
  have h3 : p ^ n ≤ r * p ^ n := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
  have h4 : (r : ℤ) * (p : ℤ) ^ n = ((r * p ^ n : ℕ) : ℤ) := by push_cast; ring
  rw [h4] at h1
  omega

end Threshold

/-! ### `ℤ_p·a + r·M` is closed -/

section Closed

variable {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module ℤ_[p]⟦X⟧ M]
  [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M]
  [ContinuousSMul ℤ_[p] M] [ContinuousSMul ℤ_[p]⟦X⟧ M]

/-- The `ℤ_p`-span of a finite subset of a compact `ℤ_p`-module is compact: it is the image of
the compact space `ℤ_p ^ #a` under a continuous map.  This is why a *topological* generation
hypothesis over `ℤ_p` — which is what the blueprint supplies, `Y` being defined as a closure —
gives the *algebraic* containment that Step 3 uses. -/
theorem isCompact_coe_span_finset (a : Finset M) :
    IsCompact ((Submodule.span ℤ_[p] (a : Set M) : Submodule ℤ_[p] M) : Set M) := by
  classical
  have hcont : Continuous fun c : (↥(a : Set M) → ℤ_[p]) ↦ ∑ i : ↥(a : Set M), c i • (i : M) :=
    continuous_finset_sum _ fun i _ ↦ (continuous_apply i).smul continuous_const
  have hrange : Set.range (fun i : ↥(a : Set M) ↦ (i : M)) = (a : Set M) := Subtype.range_coe
  have himg : ((Submodule.span ℤ_[p] (a : Set M) : Submodule ℤ_[p] M) : Set M)
      = Set.range fun c : (↥(a : Set M) → ℤ_[p]) ↦ ∑ i : ↥(a : Set M), c i • (i : M) := by
    ext x
    rw [SetLike.mem_coe]
    constructor
    · intro hx
      have hx' : x ∈ Submodule.span ℤ_[p] (Set.range fun i : ↥(a : Set M) ↦ (i : M)) := by
        rwa [hrange]
      exact (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hx'
    · rintro ⟨c, rfl⟩
      have hmem : (∑ i : ↥(a : Set M), c i • (i : M)) ∈
          Submodule.span ℤ_[p] (Set.range fun i : ↥(a : Set M) ↦ (i : M)) :=
        (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).2 ⟨c, rfl⟩
      rwa [hrange] at hmem
  rw [himg, ← Set.image_univ]
  exact isCompact_univ.image hcont

/-- `r · M` is the continuous image of the compact space `M`, hence compact. -/
theorem isCompact_coe_ideal_span_singleton_smul_top (r : ℤ_[p]⟦X⟧) :
    IsCompact (((Ideal.span {r} • (⊤ : Submodule ℤ_[p]⟦X⟧ M)) : Submodule ℤ_[p]⟦X⟧ M) :
      Set M) := by
  have hcoe : (((Ideal.span {r} • (⊤ : Submodule ℤ_[p]⟦X⟧ M)) : Submodule ℤ_[p]⟦X⟧ M) : Set M)
      = Set.range fun z : M ↦ r • z := by
    refine Set.Subset.antisymm (fun w hw ↦ ?_) ?_
    · refine Submodule.smul_induction_on hw ?_ ?_
      · rintro c hc z -
        obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hc
        exact ⟨g • z, by show r • (g • z) = (g * r) • z; rw [← mul_smul, mul_comm r g]⟩
      · rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u + v, by show r • (u + v) = r • u + r • v; rw [smul_add]⟩
    · rintro _ ⟨z, rfl⟩
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) Submodule.mem_top
  rw [hcoe, ← Set.image_univ]
  exact isCompact_univ.image (continuous_const.smul continuous_id)

/-- **`ℤ_p·a + r·M` is closed.**  Both summands are compact subgroups. -/
theorem isClosed_coe_span_sup (a : Finset M) (r : ℤ_[p]⟦X⟧) :
    IsClosed ((Submodule.span ℤ_[p] (a : Set M) ⊔
        ((Ideal.span {r} • (⊤ : Submodule ℤ_[p]⟦X⟧ M)).restrictScalars ℤ_[p]) :
          Submodule ℤ_[p] M) : Set M) := by
  have hsup : ((Submodule.span ℤ_[p] (a : Set M) ⊔
        ((Ideal.span {r} • (⊤ : Submodule ℤ_[p]⟦X⟧ M)).restrictScalars ℤ_[p]) :
          Submodule ℤ_[p] M) : Set M)
      = ((Submodule.span ℤ_[p] (a : Set M) : Submodule ℤ_[p] M) : Set M) +
        (((Ideal.span {r} • (⊤ : Submodule ℤ_[p]⟦X⟧ M)) : Submodule ℤ_[p]⟦X⟧ M) : Set M) :=
    Submodule.coe_sup _ _
  rw [hsup]
  exact ((isCompact_coe_span_finset a).add
    (isCompact_coe_ideal_span_singleton_smul_top (M := M) r)).isClosed

/-- **The topological generation hypothesis implies the algebraic one.**  If `Y` is contained in
the closure of `ℤ_p·a + r·M` then it is contained in `ℤ_p·a + r·M`. -/
theorem le_span_sup_of_le_topologicalClosure (Y : Submodule ℤ_[p] M) (a : Finset M)
    (r : ℤ_[p]⟦X⟧)
    (h : Y ≤ (Submodule.span ℤ_[p] (a : Set M) ⊔
      ((Ideal.span {r} • (⊤ : Submodule ℤ_[p]⟦X⟧ M)).restrictScalars ℤ_[p])).topologicalClosure) :
    Y ≤ Submodule.span ℤ_[p] (a : Set M) ⊔
      ((Ideal.span {r} • (⊤ : Submodule ℤ_[p]⟦X⟧ M)).restrictScalars ℤ_[p]) :=
  h.trans (Submodule.topologicalClosure_minimal _ le_rfl (isClosed_coe_span_sup a r))

end Closed

/-! ### Step 3, assembled from the geometric data -/

section Assembled

variable {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module ℤ_[p]⟦X⟧ M]
  [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M]

variable [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M]
  [TotallyDisconnectedSpace M] [ContinuousSMul ℤ_[p]⟦X⟧ M]

/-- **Blueprint node `Xn-isom-qout-of-totally-ramified`, Step 3, from the geometric data.**
Let `M` be a profinite `Λ`-module, `e : ℕ`, `Y` a `ℤ_p`-submodule of finite index with
`Y ⊆ ℤ_p·a + ω_e M` for a finite set `a`, and suppose `M / ν_{n,e} Y` is finite for every
`n ≥ e`.  Then `M` is a finitely generated torsion `Λ`-module.

`Y` is **not** assumed `Λ`-stable: only its `ℤ_p`-structure is used, which matters because on
`X∞` the submodule `Y = Gal(L∞/L_e K∞)` is a `Λ`-submodule only by an extra argument
(`L_e / K` is Galois), while *every* closed subgroup of `X∞` is a `ℤ_p`-submodule. -/
theorem moduleFinite_and_isTorsion_of_le_span (Y : Submodule ℤ_[p] M) (a : Finset M) (e : ℕ)
    (hMY : Finite (M ⧸ Y))
    (hY : Y ≤ Submodule.span ℤ_[p] (a : Set M) ⊔
      ((Ideal.span {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ e) : Polynomial ℤ_[p]) :
        ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ M)).restrictScalars ℤ_[p]))
    (hfin : ∀ n : ℕ, e ≤ n → Finite (M ⧸ Submodule.map
      (lsmulZp M ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧)) Y)) :
    Module.Finite ℤ_[p]⟦X⟧ M ∧ Module.IsTorsion ℤ_[p]⟦X⟧ M := by
  classical
  haveI := hMY
  have hYX : Y ≤ Submodule.span ℤ_[p] (a : Set M) ⊔
      ((Ideal.span {(X : ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ M)).restrictScalars ℤ_[p]) :=
    hY.trans (sup_le_sup_left
      (fun x hx ↦ omega_smul_top_le_X_smul_top (M := M) e hx) _)
  haveI : Module.Finite ℤ_[p]
      (M ⧸ ((Ideal.span {(X : ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ M)).restrictScalars ℤ_[p])) :=
    moduleFinite_quotient_X_smul_of_le_span Y a hMY hYX
  haveI hfgL : Module.Finite ℤ_[p]⟦X⟧ M :=
    lambdaModuleFinite_of_moduleFinite_quotient_X_smul this
  refine ⟨hfgL, ?_⟩
  refine isTorsion_of_forall_ge_finrank_quotSMulTop_omega_le e a.card fun n hn ↦ ?_
  haveI := hfin n hn
  refine le_trans (finrank_quotSMulTop_le_card _
    (Submodule.map (lsmulZp M ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧)) Y)
    inferInstance
    (a.image fun z ↦ ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • z)
    fun y hy ↦ exists_mem_span_nu_smul Y a hn hY y hy) Finset.card_image_le

/-- **Firing control for `IwasawaAlgebra.moduleFinite_and_isTorsion_of_le_span`**, and a
degenerate case of it.  Its hypotheses are jointly satisfiable: take `Y = ⊥`, `a = ∅`, `e = 0`
on a *finite* profinite `Λ`-module.  The conclusion is then that a finite `Λ`-module is finitely
generated and torsion — true, and here obtained by actually running Nakayama
(`IwasawaAlgebra.lambdaModuleFinite_of_moduleFinite_quotient_X_smul`) and the rank growth
bound (`IwasawaAlgebra.exists_bound_finrank_quotSMulTop_omega`). -/
theorem moduleFinite_and_isTorsion_of_finite (h : Finite M) :
    Module.Finite ℤ_[p]⟦X⟧ M ∧ Module.IsTorsion ℤ_[p]⟦X⟧ M := by
  haveI := h
  refine moduleFinite_and_isTorsion_of_le_span (⊥ : Submodule ℤ_[p] M) ∅ 0
    (Finite.of_surjective _ (Submodule.mkQ_surjective (⊥ : Submodule ℤ_[p] M))) bot_le
    fun n _ ↦ Finite.of_surjective _ (Submodule.mkQ_surjective _)

end Assembled

end IwasawaAlgebra
