/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.RamifiedFamily
public import Iwasawalib.NumberTheory.ZpExtension.Ln
public import Mathlib.FieldTheory.LinearDisjoint

@[expose] public section

/-!
# Total ramification and linear disjointness at a common layer

Two thin wrappers that combine the ramified-family lemmas with a linear-disjointness statement
`(H.Ln n).LinearDisjoint Kinf` for all large `n`, at a common threshold.  Neither proves any
linear disjointness: both take it as the hypothesis `hld` and return it in the conclusion.

## Main statements

* `MvZpExtension.exists_eventually_totallyRamified_and_linearDisjoint`: from a finite family of
  ramified places, via `MvZpExtension.exists_shift_totally_ramified`.
* `MvZpExtension.exists_eventually_totallyRamified_of_finiteRamified_and_linearDisjoint`: from
  the raw-place finiteness hypothesis `hfin`, via
  `MvZpExtension.exists_totally_ramified_of_finite_ramified`.  **Warning**: vacuous for a
  `ℤₚ`-extension of a number field; see its docstring.
-/

open IntermediateField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- The ramified-family API supplies the total-ramification half.  The linear-disjointness half
remains an explicit arithmetic input.

**Warning**: the linear-disjointness part of the conclusion is not proved here: it is the
hypothesis `hld`, returned unchanged.  Only the total-ramification part, from
`MvZpExtension.exists_shift_totally_ramified`, has content. -/
theorem exists_eventually_totallyRamified_and_linearDisjoint
    [Unique ι] {s : Type*} [Finite s]
    (v : s → AbsoluteValue Kinf ℝ)
    (hne : ∀ j, (v j).inertiaSubgroup K ≠ ⊥)
    (e₀ : ℕ)
    (hld : ∀ n, e₀ ≤ n → (H.Ln n).LinearDisjoint Kinf) :
    ∃ e : ℕ, ∀ n, e ≤ n →
      (∀ j (w : AbsoluteValue ↥((H.shift n).Linf.restrictScalars ↥(H.Kn n)) ℝ),
        (H.shift n).placeBelow w = v j →
          ((H.shift n).placeBelow w).inertiaSubgroup ↥(H.Kn n) = ⊤) ∧
      (H.Ln n).LinearDisjoint Kinf := by
  obtain ⟨e₁, he₁⟩ := H.exists_shift_totally_ramified v hne
  refine ⟨max e₀ e₁, fun n hn ↦ ?_⟩
  have hn₀ : e₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn₁ : e₁ ≤ n := le_trans (le_max_right _ _) hn
  exact ⟨he₁ n hn₁, hld n hn₀⟩

/-- The same composition using the finiteness-of-the-ramified-set interface.

**Warning**: `hfin` ranges over raw absolute values of `K∞`, and holds only when no place of
`K∞` ramifies in `K∞ / K`: a ramified `w` gives infinitely many ramified absolute values
`w ^ c`, `0 < c ≤ 1`, all equivalent to `w` (see the module docstring of
`Iwasawalib/NumberTheory/ZpExtension/RamifiedFamily.lean`).  For a `ℤₚ`-extension of a number
field some place ramifies (`MvZpExtension.exists_inertiaSubgroup_ne_bot_of_hcf`, from the
upper-bound half of the Hilbert class field theorem), so this lemma is vacuous there.  As in
`MvZpExtension.exists_eventually_totallyRamified_and_linearDisjoint`, the linear-disjointness
part of the conclusion is the hypothesis `hld`, returned unchanged. -/
theorem exists_eventually_totallyRamified_of_finiteRamified_and_linearDisjoint
    [Unique ι]
    (hfin : {w : AbsoluteValue Kinf ℝ | w.inertiaSubgroup K ≠ ⊥}.Finite)
    (e₀ : ℕ)
    (hld : ∀ n, e₀ ≤ n → (H.Ln n).LinearDisjoint Kinf) :
    ∃ e : ℕ, ∀ n, e ≤ n →
      (∀ w : AbsoluteValue Kinf ℝ, w.inertiaSubgroup K ≠ ⊥ →
        w.inertiaSubgroup ↥(H.Kn n) = ⊤) ∧
      (H.Ln n).LinearDisjoint Kinf := by
  obtain ⟨e₁, he₁⟩ := H.exists_totally_ramified_of_finite_ramified hfin
  refine ⟨max e₀ e₁, fun n hn ↦ ?_⟩
  have hn₀ : e₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn₁ : e₁ ≤ n := le_trans (le_max_right _ _) hn
  exact ⟨he₁ n hn₁, hld n hn₀⟩

end MvZpExtension
