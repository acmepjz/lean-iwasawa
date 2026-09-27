/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.ShiftLinf
public import Iwasawalib.NumberTheory.ZpExtension.TotallyRamifiedLayer
public import Iwasawalib.NumberTheory.ZpExtension.XinfStepOne

@[expose] public section

/-!
# Step 1 of Washington's Lemma 13.15 after moving the base up the tower

`MvZpExtension.exists_totally_ramified` (Washington, Lemma 13.3) produces a layer `Kₑ` such
that `K∞ / Kₑ` is totally ramified at each of a given finite family of ramified places, in the
form `(v j).inertiaSubgroup ↥(H.Kn e) = ⊤`.  `MvZpExtension.xinfQuotientMulEquivOfPlace'`
(Step 1) wants total ramification over the *base* field of the `ℤₚ`-extension it is applied to.
The two are composed here by applying Step 1 not to `H` but to `H.shift e`
(`MvZpExtension.shift`), the same extension read as a `ℤₚ`-extension of `Kₑ`.  This is legitimate
for the blueprint because `H.shift e` has the *same* `L∞` and the *same* `X∞`
(`MvZpExtension.Linf_shift`, `MvZpExtension.xinfShiftContinuousMulEquiv`).

This file supplies the two hypotheses of `MvZpExtension.xinfQuotientMulEquivOfPlace'` for
`H.shift e`:

* `hγ` is `MvZpExtension.exists_dense_zpowers` applied to `H.shift e`, recorded here as
  `MvZpExtension.exists_dense_zpowers_shift`;
* `hram` is `MvZpExtension.exists_shift_totally_ramified`.

What is *not* supplied here is the family `v` itself: in this file the ramified family stays a
parameter, exactly as in `MvZpExtension.exists_totally_ramified`.  It is supplied elsewhere.
That only the primes above `p` ramify is proved unconditionally
(`MvZpExtension.exists_ramifiedBasePlaceData_unconditional`, in
`Iwasawalib/NumberTheory/ZpExtension/TameLocalExponent.lean`), and the resulting finite family
of places of `K∞`, which at a suitable level `e` contains every ramified place up to
equivalence (`MvZpExtension.RamifiedBasePlaceData.exists_isEquiv_orbitPlace`), is
`MvZpExtension.RamifiedBasePlaceData.orbitPlace`
(`Iwasawalib/NumberTheory/ZpExtension/RamifiedPlaceFamily.lean`).  That at least one prime of
`K` ramifies in `K∞` is only available conditionally on class field theory:
`MvZpExtension.exists_inertiaSubgroup_ne_bot` depends on the `sorry`
`NumberField.IsUnramifiedEverywhere.surjective_artinMap`, and it is what makes the family
nonempty (`MvZpExtension.RamifiedBasePlaceData.nonempty_orbitIndex`).

## Main results

* `MvZpExtension.exists_shift_totally_ramified`.
* `MvZpExtension.exists_dense_zpowers_shift`.
-/

open IntermediateField NumberField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

set_option linter.unusedSectionVars false in
/-- **Washington, Lemma 13.3, in the form Step 1 consumes.**  Given finitely many places of
`K∞` ramified in `K∞ / K`, there is a layer `Kₑ` such that, for every `n ≥ e`, the
`ℤₚ`-extension `K∞ / Kₙ` given by `MvZpExtension.shift` is totally ramified at all of them:
this is the hypothesis `hram` of `MvZpExtension.xinfQuotientMulEquivOfPlace'` applied to
`H.shift n`. -/
theorem exists_shift_totally_ramified [Unique ι] {s : Type*} [Finite s]
    (v : s → AbsoluteValue Kinf ℝ) (hne : ∀ j, (v j).inertiaSubgroup K ≠ ⊥) :
    ∃ e : ℕ, ∀ n, e ≤ n → ∀ j
      (w : AbsoluteValue ↥((H.shift n).Linf.restrictScalars ↥(H.Kn n)) ℝ),
      (H.shift n).placeBelow w = v j →
        ((H.shift n).placeBelow w).inertiaSubgroup ↥(H.Kn n) = ⊤ := by
  obtain ⟨e, he⟩ := H.exists_totally_ramified v hne
  exact ⟨e, fun n hn j w hw ↦ hw ▸ he n hn j⟩

/-- `Γ_e = Gal(K∞/Kₑ)` has a topological generator: the hypothesis `hγ` of
`MvZpExtension.xinfQuotientMulEquivOfPlace'` applied to `H.shift e`. -/
theorem exists_dense_zpowers_shift [Unique ι] (e : ℕ) :
    ∃ γ : (H.shift e).GG ⧸ (H.shift e).Xinf,
      Dense (Subgroup.zpowers γ : Set ((H.shift e).GG ⧸ (H.shift e).Xinf)) :=
  (H.shift e).exists_dense_zpowers

end MvZpExtension
