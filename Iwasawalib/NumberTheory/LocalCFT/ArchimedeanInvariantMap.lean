/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.ArchimedeanLocalNormIndex
public import Iwasawalib.NumberTheory.LocalCFT.LocalInvariantMap
public import Iwasawalib.GroupCohomology.CyclicOrderIso

@[expose] public section

/-!
# The local invariant map at an archimedean place

`Iwasawalib/NumberTheory/LocalCFT/LocalInvariantMap.lean` builds the invariant map
`inv_w : Ĥ⁰(D_w, L_w^×) ≃ ℤ/n_w` only at **finite unramified** places, where it comes from the
valuation sequence `0 → 𝒪^× → F^× → ℤ → 0` and the cohomological triviality of `𝒪^×`.  At an
archimedean place there is no valuation sequence and no `𝒪^×`, and
`Iwasawalib/NumberTheory/LocalCFT/ArchimedeanLocalNormIndex.lean` stops at the two **orders**
`#Ĥ⁰ = 2` (real `v`, complex `w`) and `#Ĥ⁰ = 1` (unramified).

This file supplies the map itself, at **every** infinite place and with no ramification
hypothesis.  The archimedean case is small enough that the orders determine the map: `Ĥ⁰` has
order `1` or `2`, a group of order `1` or of prime order is cyclic, and a cyclic group of order
`n` is `ℤ/n` — uniquely so when `n ≤ 2`, so no normalisation choice is being smuggled in.  In
Brauer-group language the invariant of a real place is `1/2 ∈ ℚ/ℤ` and that of a complex place
is `0`, which is exactly what `ZMod #D_w` records here.

## Main statements

* `NumberField.InfinitePlace.card_tateH0_completion_units` : **`#Ĥ⁰(D_w, L_w^×) = #D_w` at every
  infinite place**, with no ramification hypothesis.  This is the archimedean local norm index;
  previously only the two separate ramified/unramified computations existed.
* `NumberField.InfinitePlace.isAddCyclic_tateH0_completion_units` : `Ĥ⁰(D_w, L_w^×)` is cyclic.

## Main definitions

* `NumberField.InfinitePlace.invCompletionUnits` : the invariant map
  `Ĥ⁰(D_w, L_w^×) ≃+ ZMod #D_w`.
* `NumberField.InfinitePlace.archLocalReciprocityEquiv` : local reciprocity at an infinite
  place, `Ĥ⁰(D_w, L_w^×) ≃+ Additive D_w`.
-/

noncomputable section

open CyclicTate MulAction

/-! ## Small groups are cyclic -/

namespace LocalCFT

/-- A group with one element is cyclic. -/
theorem isAddCyclic_of_card_eq_one {A : Type*} [AddGroup A] (h : Nat.card A = 1) :
    IsAddCyclic A := by
  haveI : Subsingleton A := (Nat.card_eq_one_iff_unique.1 h).1
  refine ⟨⟨0, fun x ↦ ?_⟩⟩
  rw [Subsingleton.elim x (0 : A)]
  exact AddSubgroup.zero_mem (AddSubgroup.zmultiples (0 : A))

/-- A group of order `2` is cyclic. -/
theorem isAddCyclic_of_card_eq_two {A : Type*} [AddGroup A] (h : Nat.card A = 2) :
    IsAddCyclic A := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [h]; exact two_ne_zero)
  obtain ⟨a, -, ha⟩ := (Nat.card_eq_two_iff' (0 : A)).1 h
  refine ⟨⟨a, fun x ↦ ?_⟩⟩
  by_cases hx : x = 0
  · rw [hx]
    exact AddSubgroup.zero_mem (AddSubgroup.zmultiples a)
  · rw [ha x hx]
    exact AddSubgroup.mem_zmultiples a

/-- **A cyclic group is `ZMod` of its order**, transported along a known value of that order. -/
def addEquivZModOfCard {A : Type*} [AddGroup A] (hcyc : IsAddCyclic A) {n : ℕ}
    (hn : Nat.card A = n) : A ≃+ ZMod n :=
  (zmodAddCyclicAddEquiv hcyc).symm.trans (zmodCongr hn)

end LocalCFT

namespace NumberField.InfinitePlace

-- The `Herbrand` section of `Iwasawalib/NumberTheory/LocalCFT/ArchimedeanLocalNormIndex.lean`,
-- which supplies the two order computations used below, is stated for `K L : Type`, so this
-- file inherits that restriction.  Nothing in the argument needs it.
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]

attribute [local instance] stabilizerCompletionMulSemiringAction Units.mulDistribMulActionRight

variable [Fintype (stabilizer (L ≃ₐ[K] L) w)] {σ : stabilizer (L ≃ₐ[K] L) w}
  (hσ : ∀ g : stabilizer (L ≃ₐ[K] L) w, g ∈ Subgroup.zpowers σ)

include hσ

omit [NumberField K] [NumberField L] [IsGalois K L] [w.LiesOver v]
  [Fintype (stabilizer (L ≃ₐ[K] L) w)] in
/-- A generator of a group of order `2` is not the identity. -/
theorem ne_one_of_card_eq_two (h : Nat.card (stabilizer (L ≃ₐ[K] L) w) = 2) : σ ≠ 1 := by
  intro h1
  haveI : Subsingleton (stabilizer (L ≃ₐ[K] L) w) := by
    refine ⟨fun a b ↦ ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hσ a)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hσ b)
    rw [← hm, ← hn, h1, one_zpow, one_zpow]
  rw [Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩] at h
  exact absurd h (by norm_num)

include v in
/-- **The archimedean local norm index, at every infinite place**:
`#Ĥ⁰(D_w, L_w^×) = #D_w`.

Equivalently `#(K_v^× / N L_w^×) = [L_w : K_v]`.  There is no ramification hypothesis: the two
cases `#D_w = 2` (a real place of `K` that becomes complex) and `#D_w = 1` (unramified) are
`NumberField.InfinitePlace.card_tateH0_completion_units_eq_two_of_isReal_of_isComplex` and
`NumberField.InfinitePlace.card_tateH0_completion_units_eq_one_of_isUnramified`, and
`NumberField.InfinitePlace.isUnramified_or_isRamified` says there is no third case. -/
theorem card_tateH0_completion_units :
    Nat.card (TateH0 (stabilizer (L ≃ₐ[K] L) w) (Additive (w.Completion)ˣ) σ)
      = Nat.card (stabilizer (L ≃ₐ[K] L) w) := by
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [card_tateH0_completion_units_eq_one_of_isUnramified (v := v) h hσ,
      card_stabilizer_eq_one_of_isUnramified v w h]
  · have hcard : Nat.card (stabilizer (L ≃ₐ[K] L) w) = 2 :=
      card_stabilizer_eq_two_of_isRamified v w h
    rw [card_tateH0_completion_units_eq_two_of_isReal_of_isComplex (v := v)
      (h.liesOver_isReal_under (v := v)) h.isComplex (ne_one_of_card_eq_two w hσ hcard) hσ,
      hcard]

include v in
/-- **`Ĥ⁰(D_w, L_w^×)` is cyclic at every infinite place.**  Its order is `1` or `2`. -/
theorem isAddCyclic_tateH0_completion_units :
    IsAddCyclic (TateH0 (stabilizer (L ≃ₐ[K] L) w) (Additive (w.Completion)ˣ) σ) := by
  rcases w.isUnramified_or_isRamified K with h | h
  · exact LocalCFT.isAddCyclic_of_card_eq_one
      (card_tateH0_completion_units_eq_one_of_isUnramified (v := v) h hσ)
  · have hcard : Nat.card (stabilizer (L ≃ₐ[K] L) w) = 2 :=
      card_stabilizer_eq_two_of_isRamified v w h
    exact LocalCFT.isAddCyclic_of_card_eq_two
      (card_tateH0_completion_units_eq_two_of_isReal_of_isComplex (v := v)
        (h.liesOver_isReal_under (v := v)) h.isComplex
        (ne_one_of_card_eq_two w hσ hcard) hσ)

include v in
/-- **The local invariant map at an infinite place**: `inv_w : Ĥ⁰(D_w, L_w^×) ≃ ℤ/#D_w`.

At a complex place, and at a real place of `K` staying real in `L`, both sides are trivial.  At
a real place of `K` becoming complex in `L`, both sides have order `2` and this is the unique
isomorphism between them: the invariant of the nontrivial class — the class of `-1 ∈ ℝ^×`, which
is not a norm from `ℂ^×` — is `1/2 ∈ ℚ/ℤ`.

Together with `NumberField.invAdicCompletionUnits` at the unramified finite places this covers
every place of `K` except the ramified finite ones. -/
def invCompletionUnits :
    TateH0 (stabilizer (L ≃ₐ[K] L) w) (Additive (w.Completion)ˣ) σ
      ≃+ ZMod (Nat.card (stabilizer (L ≃ₐ[K] L) w)) :=
  LocalCFT.addEquivZModOfCard (isAddCyclic_tateH0_completion_units v w hσ)
    (card_tateH0_completion_units v w hσ)

include v in
/-- **Local reciprocity at an infinite place**: `K_v^× / N L_w^× ≅ D_w`.  The composite of the
invariant map with the normalisation `ℤ/n ≅ D_w` sending `1` to the generator `σ`. -/
def archLocalReciprocityEquiv :
    TateH0 (stabilizer (L ≃ₐ[K] L) w) (Additive (w.Completion)ˣ) σ
      ≃+ Additive (stabilizer (L ≃ₐ[K] L) w) :=
  (invCompletionUnits v w hσ).trans
    (zmodAddEquivOfGeneratorMul (G := stabilizer (L ≃ₐ[K] L) w) (σ := σ)
      (fun g ↦ by
        obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff g σ).1 (mem_powers_iff_mem_zpowers.2 (hσ g))
        exact ⟨k, hk⟩))

end NumberField.InfinitePlace
