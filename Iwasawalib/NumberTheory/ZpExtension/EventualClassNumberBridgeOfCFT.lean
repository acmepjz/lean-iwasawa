/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.EventualClassNumberBridge
public import Iwasawalib.NumberTheory.ZpExtension.FiniteSubalgebraLinearDisjoint
public import Iwasawalib.NumberTheory.ZpExtension.BaseChangeLinearDisjoint
public import Iwasawalib.NumberTheory.ZpExtension.Linf

@[expose] public section

/-!
# The eventual class-number cardinality bridge, conditional on class field theory

Let `K∞ / K` be a `ℤₚ`-extension of number fields with layers `Kₙ`, let `Lₙ` be the maximal
unramified abelian `p`-extension of `Kₙ` and `K∞ Lₙ` (`MvZpExtension.Ln'`) its compositum with
`K∞`.  This file constructs the structure
`MvZpExtension.EventualClassNumberCardinalityBridge H e` for some threshold `e`: for `n ≥ e`,

`#Gal(K∞ Lₙ / K∞) = p ^ ord_p(h_{Kₙ})`.

The argument is the classical one (blueprint nodes `isom-of-totally-ramified` and
`Xn-isom-An`): some place of `K∞` ramifies in `K∞ / K`, hence is totally ramified in `K∞ / Kₙ`
for `n ≥ e`, so that `Lₙ` and `K∞` are linearly disjoint over `Kₙ` and
`[K∞ Lₙ : K∞] = [Lₙ : Kₙ] = p ^ ord_p(h_{Kₙ})`.

## Main statements

* `MvZpExtension.card_gal_Ln'_eq_classNumber_pow_of_linearDisjoint`: the cardinality identity at
  one layer `n`, given that `Lₙ` and `K∞` are linearly disjoint over `Kₙ`.
* `MvZpExtension.exists_eventualClassNumberCardinalityBridge`: there is `e` with
  `EventualClassNumberCardinalityBridge H e`.

The hypothesis `[Unique ι]` (the `ℤₚ` case, as opposed to a general `ℤₚᵈ`-extension) is required
for the main statement `MvZpExtension.exists_eventualClassNumberCardinalityBridge` only; the
single-layer statement holds for any finite `ι`.

**Warning**: neither statement is unconditional.  Both depend on `sorryAx` through the class
field theory `sorry`s in
`Iwasawalib.NumberTheory.NumberField.HilbertClassField.ClassFieldTheory`; see the docstrings.
-/

open IntermediateField

namespace MvZpExtension

variable {p : ℕ} [hp : Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf]
  [IsGalois K Kinf]
variable (H : MvZpExtension p ι K Kinf)

/-- If `Lₙ` and `K∞` are linearly disjoint over `Kₙ`, then
`#Gal(K∞ Lₙ / K∞) = p ^ ord_p(h_{Kₙ})`.

**Warning**: this declaration is *not* unconditional.  It uses `MvZpExtension.finrank_Ln`,
which is derived from
`NumberField.IsUnramifiedEverywhere.bijective_artinMap_of_isSepClosed` and
`NumberField.IsUnramifiedEverywhere.surjective_artinMap`, which are `sorry` (and
`NumberField.IsUnramifiedEverywhere.artinMap` is itself defined by `sorry`).
`NumberField.IsUnramifiedEverywhere.surjective_artinMap` is also reached through the
finite-dimensionality instances `MvZpExtension.finiteDimensional_Ln` and
`MvZpExtension.finiteDimensional_Ln'`, which supply the `FiniteDimensional` arguments required
by `IntermediateField.finrank_adjoin_eq_finrank_of_linearDisjoint` and
`IsGalois.card_aut_eq_finrank` respectively.  So this theorem depends on `sorryAx`. -/
theorem card_gal_Ln'_eq_classNumber_pow_of_linearDisjoint (n : ℕ)
    (hld : (H.Ln n).LinearDisjoint Kinf) :
    Nat.card Gal(↥(H.Ln' n) / Kinf) =
      p ^ multiplicity p (NumberField.classNumber (H.Kn n)) := by
  rw [IsGalois.card_aut_eq_finrank, ← H.finrank_Ln n]
  exact IntermediateField.finrank_adjoin_eq_finrank_of_linearDisjoint (H.Ln n) hld

/-- **The eventual class-number cardinality bridge.**  For a `ℤₚ`-extension `K∞ / K` there is a
layer `e` such that `#Gal(K∞ Lₙ / K∞) = p ^ ord_p(h_{Kₙ})` for all `n ≥ e`.

**Warning**: this declaration is *not* unconditional.  Its proof is the classical one, and in
this repository that route is `MvZpExtension.finrank_Ln`, which is derived from
`NumberField.IsUnramifiedEverywhere.bijective_artinMap_of_isSepClosed` and
`NumberField.IsUnramifiedEverywhere.surjective_artinMap`, which are `sorry`.  The same
`surjective_artinMap` is reached a second and third time, through the instance
`MvZpExtension.finiteDimensional_Ln` and through
`MvZpExtension.exists_inertiaSubgroup_ne_bot` (existence of a ramified place).  So this theorem
depends on `sorryAx`. -/
theorem exists_eventualClassNumberCardinalityBridge [Unique ι] :
    ∃ e : ℕ, EventualClassNumberCardinalityBridge H e := by
  obtain ⟨w, hw⟩ := H.exists_inertiaSubgroup_ne_bot
  obtain ⟨e, he⟩ := H.exists_eventually_linearDisjoint_Ln_Kinf_of_ramified_of_finite
    (fun n ↦ H.finiteDimensional_Ln n) w hw
  exact ⟨e, ⟨fun n hn ↦ H.card_gal_Ln'_eq_classNumber_pow_of_linearDisjoint n (he n hn)⟩⟩

end MvZpExtension
