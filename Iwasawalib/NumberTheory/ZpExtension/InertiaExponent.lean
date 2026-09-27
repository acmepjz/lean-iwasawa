/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.RamifiedFamily

@[expose] public section

/-!
# An exponent bound on inertia kills it: the `ℤₚ`-side of "unramified outside `p`"

`MvZpExtension.exists_shift_totally_ramified_of_bddAbove_outside`
(`Iwasawalib/NumberTheory/ZpExtension/RamifiedFamily.lean`) reduces the ramified family to the
hypothesis

`hbound : ∀ w ∉ S, ∃ N : ℕ, ∀ n : ℕ, e(w | Kₙ/K) ≤ N`,

a bound on the *ramification indices* of the layers, uniform in `n`.  The local input that is
supposed to discharge it — `LocalCFT.orderOf_dvd_sub_one`, i.e. `e ∣ N(v) - 1` — does not
produce a bound on an index: it produces a bound on the *order of an individual automorphism*.
This file shows that the second is enough, and that the usual intermediate step is not needed.

## The observation

Classically one passes from "every element of the tame inertia group is killed by `q - 1`" to
"the tame inertia group has order at most `q - 1`" by proving the group **cyclic** — which is
how `LocalCFT.TameInjective` was scoped, the tame character being injective into `kˣ` and a
finite subgroup of the units of a field being cyclic.  *For a `ℤₚ`-extension that step is
unnecessary.*  The inertia subgroup `I_w(K∞/K)` sits inside `Γ ≅ ℤₚᵈ`, which is **torsion-free**
(`EquivMvZp.eq_one_of_pow_eq_one`), so an exponent bound does not merely bound the order of
`I_w(K∞/K)` — it makes it trivial outright
(`MvZpExtension.inertiaSubgroup_eq_bot_of_exponent`), and then every layer has ramification
index `1`, not `≤ q - 1`.

Neither cyclicity nor any counting argument appears below.  What replaces them is that `ℤₚ` has
no torsion, which is `PadicInt.norm_le_pow_iff_mem_span_pow` plus `p⁻ⁿ → 0`.

## The layer form

The local statement is naturally proved one layer at a time: at each `n` it says that the image
of `σ` in `Gal(Kₙ/K)` is killed by `M`, i.e. that `σ ^ M` fixes `Kₙ` pointwise, i.e. that
`σ ^ M ∈ Γ^{pⁿ}`.  Since `⋂ₙ Γ^{pⁿ} = ⊥` (`EquivMvZp.eq_one_of_forall_mem_Γpow`), the layerwise
form implies the global one; `MvZpExtension.inertiaSubgroup_eq_bot_of_layer_exponent` and
`MvZpExtension.inertiaSubgroup_eq_bot_of_fixes_Kn` are the two shapes of that.

Everything here is unconditional: no class field theory is used.  Note in
particular that `[Unique ι]` is *not* needed — the argument works for `ℤₚᵈ`, unlike the
bounded-ramification criterion it replaces.

## Main statements

* `EquivMvZp.eq_one_of_pow_eq_one`: `Γ ≅ ℤₚᵈ` is torsion-free.
* `EquivMvZp.eq_one_of_forall_mem_Γpow`, `EquivMvZp.iInf_Γpow_eq_bot`: `⋂ₙ Γ^{pⁿ} = ⊥`.
* `MvZpExtension.inertiaSubgroup_eq_bot_of_exponent`: **an exponent bound on `I_w(K∞/K)` makes
  it trivial.**
* `MvZpExtension.inertiaSubgroup_eq_bot_of_layer_exponent`,
  `MvZpExtension.inertiaSubgroup_eq_bot_of_fixes_Kn`: the layerwise forms of the same.
* `MvZpExtension.ramificationIdx_Kn_eq_one_of_exponent`,
  `MvZpExtension.bddAbove_ramificationIdx_of_exponent`: hence `hbound`, with `N = 1`.
* `MvZpExtension.finite_ramified_of_exponent_outside`,
  `MvZpExtension.exists_shift_totally_ramified_of_exponent_outside`: the ramified family from an
  exponent bound outside a finite set of places.  **Warning**: their hypotheses can hold only
  when no place of `K∞` ramifies, so they are vacuous for a `ℤₚ`-extension of a number field;
  see their docstrings.

The layerwise local statement at the primes not above `p` is proved in
`Iwasawalib/NumberTheory/ZpExtension/TameLocalExponent.lean`
(`MvZpExtension.exists_restrictNormalHom_pow_eq_one_of_liesOver_adicAbv`), and turned into
`I_w(K∞/K) = ⊥` by `MvZpExtension.inertiaSubgroup_eq_bot_of_fixes_Kn` in the proof of
`MvZpExtension.ramified_place_liesOver_basePrimeAbove_p`.
-/

namespace EquivMvZp

variable {G : Type*} [Group G] [TopologicalSpace G] {p : ℕ} [Fact p.Prime] {ι : Type*}

/-- An element of `ℤₚ` lying in `(pⁿ)` for every `n` is `0`. -/
theorem eq_zero_of_forall_mem_span_pow (x : ℤ_[p])
    (h : ∀ n : ℕ, x ∈ Ideal.span {(p : ℤ_[p]) ^ n}) : x = 0 := by
  have hnorm : ∀ n : ℕ, ‖x‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := fun n ↦
    (PadicInt.norm_le_pow_iff_mem_span_pow x n).2 (h n)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out (p := p.Prime)).one_lt
  have hlim : Filter.Tendsto (fun n : ℕ ↦ ((p : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      ((inv_lt_one₀ (by linarith)).2 hp1)
  have hle : ‖x‖ ≤ 0 := ge_of_tendsto hlim (Filter.Eventually.of_forall fun n ↦ by
    have := hnorm n
    rwa [zpow_neg, zpow_natCast, ← inv_pow] at this)
  exact norm_eq_zero.1 (le_antisymm hle (norm_nonneg x))

/-- **`Γ ≅ ℤₚᵈ` is torsion-free.**  This is what replaces the cyclicity step: an exponent bound
on a subgroup of `Γ` is not a bound on its order, it is triviality. -/
theorem eq_one_of_pow_eq_one (H : EquivMvZp G p ι) {M : ℕ} (hM : M ≠ 0) {σ : H.Γ}
    (h : σ ^ M = 1) : σ = 1 := by
  apply H.continuousMulEquiv.injective
  rw [map_one]
  have h1 : H.continuousMulEquiv σ ^ M = 1 := by rw [← map_pow, h, map_one]
  have h2 : M • (Multiplicative.toAdd (H.continuousMulEquiv σ)) = 0 := h1
  apply Multiplicative.toAdd.injective
  show Multiplicative.toAdd (H.continuousMulEquiv σ) = 0
  funext i
  have h3 : M • (Multiplicative.toAdd (H.continuousMulEquiv σ) i) = 0 := congrFun h2 i
  rw [nsmul_eq_mul] at h3
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd (Nat.cast_eq_zero.1 h4) hM
  · exact h4

/-- **`⋂ₙ Γ^{pⁿ} = ⊥`**, in element form: an element which is a `pⁿ`-th power for every `n` is
trivial. -/
theorem eq_one_of_forall_mem_Γpow (H : EquivMvZp G p ι) {σ : H.Γ}
    (h : ∀ n : ℕ, σ ∈ H.Γpow' n) : σ = 1 := by
  apply H.continuousMulEquiv.injective
  rw [map_one]
  apply Multiplicative.toAdd.injective
  show Multiplicative.toAdd (H.continuousMulEquiv σ) = 0
  funext i
  refine eq_zero_of_forall_mem_span_pow _ fun n ↦ ?_
  obtain ⟨τ, hτ⟩ := (H.mem_Γpow'_iff n σ).1 (h n)
  rw [hτ, map_pow]
  refine Ideal.mem_span_singleton'.2 ⟨Multiplicative.toAdd (H.continuousMulEquiv τ) i, ?_⟩
  show _ = Multiplicative.toAdd (H.continuousMulEquiv τ ^ p ^ n) i
  have hpow : Multiplicative.toAdd (H.continuousMulEquiv τ ^ p ^ n)
      = (p ^ n) • Multiplicative.toAdd (H.continuousMulEquiv τ) := rfl
  rw [hpow]
  simp [mul_comm]

/-- **`⋂ₙ Γ^{pⁿ} = ⊥`.** -/
theorem iInf_Γpow_eq_bot (H : EquivMvZp G p ι) [Finite ι] :
    (⨅ n : ℕ, (H.Γpow n : Subgroup H.Γ)) = ⊥ := by
  refine eq_bot_iff.2 fun σ hσ ↦ ?_
  rw [Subgroup.mem_bot]
  exact H.eq_one_of_forall_mem_Γpow fun n ↦ Subgroup.mem_iInf.1 hσ n

end EquivMvZp

open IntermediateField

namespace MvZpExtension

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]
variable (H : MvZpExtension p ι K Kinf)

include H in
set_option linter.unusedSectionVars false in
/-- **An exponent bound on the inertia subgroup of `K∞ / K` makes it trivial.**  If some `M ≠ 0`
kills every element of `I_w(K∞/K)`, then `I_w(K∞/K) = ⊥`: there is nothing to count, because
`Γ ≅ ℤₚᵈ` is torsion-free (`EquivMvZp.eq_one_of_pow_eq_one`).

This is the exact interface for `LocalCFT.orderOf_dvd_sub_one`, which produces `σ ^ (q - 1) = 1`
for `σ` in tame inertia of an abelian extension: take `M = q - 1 = N(v) - 1`, which is nonzero
because `N(v) ≥ 2`. -/
theorem inertiaSubgroup_eq_bot_of_exponent (w : AbsoluteValue Kinf ℝ) {M : ℕ} (hM : M ≠ 0)
    (h : ∀ σ ∈ w.inertiaSubgroup K, σ ^ M = 1) : w.inertiaSubgroup K = ⊥ := by
  refine eq_bot_iff.2 fun σ hσ ↦ ?_
  rw [Subgroup.mem_bot]
  exact H.eq_one_of_pow_eq_one hM (h σ hσ)

include H in
/-- **The layerwise form.**  The local input is proved one layer at a time: it says that the
image of `σ ∈ I_w(K∞/K)` in `Gal(Kₙ/K)` is killed by `M`, i.e. that `σ ^ M ∈ Γ^{pⁿ}`.  Since
`⋂ₙ Γ^{pⁿ} = ⊥`, that already forces `I_w(K∞/K) = ⊥`; no bound on `M` is needed here at all,
not even `M ≠ 0`. -/
theorem inertiaSubgroup_eq_bot_of_layer_exponent (w : AbsoluteValue Kinf ℝ) {M : ℕ}
    (h : ∀ n : ℕ, ∀ σ ∈ w.inertiaSubgroup K, σ ^ M ∈ (H.Γpow n : Subgroup H.Γ)) (hM : M ≠ 0) :
    w.inertiaSubgroup K = ⊥ :=
  H.inertiaSubgroup_eq_bot_of_exponent w hM fun σ hσ ↦
    H.eq_one_of_forall_mem_Γpow fun n ↦ h n σ hσ

include H in
/-- The layerwise form again, stated as "`σ ^ M` fixes every layer pointwise" rather than as
membership in `Γ^{pⁿ}`. -/
theorem inertiaSubgroup_eq_bot_of_fixes_Kn (w : AbsoluteValue Kinf ℝ) {M : ℕ} (hM : M ≠ 0)
    (h : ∀ n : ℕ, ∀ σ ∈ w.inertiaSubgroup K, σ ^ M ∈ (H.Kn n).fixingSubgroup) :
    w.inertiaSubgroup K = ⊥ :=
  H.inertiaSubgroup_eq_bot_of_layer_exponent w
    (fun n σ hσ ↦ by rw [← H.fixingSubgroup_Kn n]; exact h n σ hσ) hM

/-- Under an exponent bound on `I_w(K∞/K)`, every layer is unramified at `w`. -/
theorem ramificationIdx_Kn_eq_one_of_exponent (w : AbsoluteValue Kinf ℝ) {M : ℕ} (hM : M ≠ 0)
    (h : ∀ σ ∈ w.inertiaSubgroup K, σ ^ M = 1) (n : ℕ) :
    w.ramificationIdxOfIsScalarTower K ↥(H.Kn n) = 1 :=
  H.ramificationIdx_Kn_eq_one w (H.inertiaSubgroup_eq_bot_of_exponent w hM h) n

/-- **`hbound` from an exponent bound**, with `N = 1`: the hypothesis of
`MvZpExtension.finite_ramified_of_bddAbove_outside` and
`MvZpExtension.exists_shift_totally_ramified_of_bddAbove_outside`, at a single place.  Note that
the resulting bound is `1`, not `M`: the layers are *unramified* at `w`, not merely boundedly
ramified. -/
theorem bddAbove_ramificationIdx_of_exponent (w : AbsoluteValue Kinf ℝ) {M : ℕ} (hM : M ≠ 0)
    (h : ∀ σ ∈ w.inertiaSubgroup K, σ ^ M = 1) :
    ∃ N : ℕ, ∀ n : ℕ, w.ramificationIdxOfIsScalarTower K ↥(H.Kn n) ≤ N :=
  ⟨1, fun n ↦ (H.ramificationIdx_Kn_eq_one_of_exponent w hM h n).le⟩

include H in
/-- **Only finitely many places ramify, from an exponent bound outside a finite set.**  The
form of `MvZpExtension.finite_ramified_of_bddAbove_outside` that the tame character can feed:
outside `S` — in practice the places above `p` — it suffices that some nonzero `M` (depending on
the place: `M = N(v) - 1`) kills the inertia subgroup.

**Warning**: `hexp` makes every absolute value outside `S` unramified
(`MvZpExtension.inertiaSubgroup_eq_bot_of_exponent`), so it puts every ramified absolute value of
`K∞` into the finite set `S`.  But the set of ramified absolute values is infinite as soon as it
is nonempty: a ramified `w` gives the ramified absolute values `w ^ c`, `0 < c ≤ 1`, pairwise
distinct and all equivalent to `w` (`AbsoluteValue.rpowOfLeOneOrIsNonarchimedean`,
`AbsoluteValue.inertiaSubgroup_eq_of_equiv`).  So `hS` and `hexp` can hold together only when no
place of `K∞` ramifies in `K∞ / K`, which never happens for a `ℤₚ`-extension of a number field
(`MvZpExtension.exists_inertiaSubgroup_ne_bot_of_hcf`, from the upper-bound half of the Hilbert
class field theorem); the lemma is vacuous there. -/
theorem finite_ramified_of_exponent_outside {S : Set (AbsoluteValue Kinf ℝ)} (hS : S.Finite)
    (hexp : ∀ w ∉ S, ∃ M : ℕ, M ≠ 0 ∧ ∀ σ ∈ w.inertiaSubgroup K, σ ^ M = 1) :
    {w : AbsoluteValue Kinf ℝ | w.inertiaSubgroup K ≠ ⊥}.Finite := by
  refine hS.subset fun w hw ↦ ?_
  by_contra hwS
  obtain ⟨M, hM, h⟩ := hexp w hwS
  exact hw (H.inertiaSubgroup_eq_bot_of_exponent w hM h)

variable [NumberField K]

/-- **The ramified family from an exponent bound on inertia outside a finite set of places**, in
the form `MvZpExtension.exists_shift_totally_ramified` — and hence Step 1 of Washington's
Lemma 13.15 — consumes.

This is `MvZpExtension.exists_shift_totally_ramified_of_bddAbove_outside` with its hypothesis
replaced by the one the tame character actually produces.  Unconditional.
The local statement, in its layerwise form (`σ ^ (N(v) - 1)` restricts to the identity on every
layer `Kₙ`, for `σ ∈ I_w(K∞/K)` and `w` over a prime `v ∤ p`), is
`MvZpExtension.exists_restrictNormalHom_pow_eq_one_of_liesOver_adicAbv`.

**Warning**: as for `MvZpExtension.finite_ramified_of_exponent_outside`, the hypotheses `hS` and
`hexp` can hold together only when no place of `K∞` ramifies in `K∞ / K`, so this lemma is
vacuous for a `ℤₚ`-extension of a number field.  The local statement is used instead through
`MvZpExtension.exists_ramifiedBasePlaceData_unconditional`, and the family actually used
downstream is `MvZpExtension.RamifiedBasePlaceData.orbitPlace`. -/
theorem exists_shift_totally_ramified_of_exponent_outside [Unique ι]
    {S : Set (AbsoluteValue Kinf ℝ)} (hS : S.Finite)
    (hexp : ∀ w ∉ S, ∃ M : ℕ, M ≠ 0 ∧ ∀ σ ∈ w.inertiaSubgroup K, σ ^ M = 1) :
    ∃ e : ℕ, ∀ n, e ≤ n →
      ∀ w : AbsoluteValue ↥((H.shift n).Linf.restrictScalars ↥(H.Kn n)) ℝ,
        ((H.shift n).placeBelow w).inertiaSubgroup K ≠ ⊥ →
          ((H.shift n).placeBelow w).inertiaSubgroup ↥(H.Kn n) = ⊤ :=
  H.exists_shift_totally_ramified_of_finite_ramified
    (H.finite_ramified_of_exponent_outside hS hexp)

end MvZpExtension
