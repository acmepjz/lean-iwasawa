/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.FieldTheory.ZpExtension.Basic

@[expose] public section

/-!
# The group-theoretic core of Washington's Lemma 13.3

Blueprint node `exists-totally-ramified` reads: if `K∞ / K` is a `ℤₚ`-extension, then there is
`e ≥ 0` such that `K∞ / K_e` is totally ramified at every ramified prime.  After the
ramification-theoretic reductions the statement is the following purely group-theoretic fact
about `Γ ≅ ℤₚ`:

*finitely many nonzero closed subgroups `I₁, …, I_s` of `Γ` all contain `Γ^{p^e}` for a common
`e`* — namely `e = max mᵢ` where `Iᵢ = Γ^{p^{mᵢ}}`, using that the nonzero closed subgroups of
`ℤₚ` are exactly the `p^m ℤₚ`.

That last fact is `EquivMvZp.eq_bot_or_Γpow_of_isClosed`.  The arithmetic input needed for the
full blueprint node is:

* at least one prime ramifies (needs finiteness of the Hilbert class field);
* only primes above `p` ramify (blueprint node `p:unr-outside-p`);
* the inertia subgroup of a place of `K∞` is a closed subgroup of `Γ`, nonzero exactly when
  the prime ramifies.

None of these is in mathlib, and only the group-theoretic core is formalized in this file.  All
three are now in the repository, elsewhere:

* the first is `MvZpExtension.exists_inertiaSubgroup_ne_bot_of_hcf`
  (`Iwasawalib/NumberTheory/ZpExtension/IwasawaTheoremOfHCF.lean`), which is **class field
  theory**: it assumes the upper-bound half `NumberField.HilbertClassFieldUpperBound` of the
  Hilbert class field theorem;
* the second is proved unconditionally, by the tame route rather than by local class field
  theory, in `Iwasawalib/NumberTheory/ZpExtension/TameLocalExponent.lean`:
  `MvZpExtension.exists_restrictNormalHom_pow_eq_one_of_liesOver_adicAbv` discharges the
  hypothesis of `MvZpExtension.ramified_place_liesOver_basePrimeAbove_p`, and the result is
  packaged as `MvZpExtension.exists_ramifiedBasePlaceData_unconditional`;
* the third is `AbsoluteValue.isClosed_inertiaSubgroup` (closedness) together with
  `MvZpExtension.inertiaSubgroup_eq_bot_iff_bddAbove_ramificationIdx` (the inertia subgroup is
  trivial exactly when the ramification indices in the layers are bounded).
-/

namespace EquivMvZp

variable {G : Type*} [Group G] [TopologicalSpace G] {p : ℕ} [Fact p.Prime] {ι : Type*}
  [Finite ι] [Unique ι] (H : EquivMvZp G p ι)

/-- **Group-theoretic core of blueprint node `exists-totally-ramified`** (Washington, Lemma
13.3).  Given finitely many nontrivial closed subgroups of `Γ ≅ ℤₚ` there is an `e` with
`Γ^{p^e}` contained in all of them. -/
theorem exists_Γpow_le_of_isClosed {s : Type*} [Finite s] (I : s → Subgroup H.Γ)
    (hclosed : ∀ i, IsClosed (I i : Set H.Γ)) (hne : ∀ i, I i ≠ ⊥) :
    ∃ e : ℕ, ∀ i, (H.Γpow e : Subgroup H.Γ) ≤ I i := by
  have hm : ∀ i, ∃ m : ℕ, I i = H.Γpow m := by
    intro i
    rcases H.eq_bot_or_Γpow_of_isClosed (I i) (hclosed i) with h | h
    · exact absurd h (hne i)
    · exact h
  choose m hmspec using hm
  obtain ⟨e, he⟩ : ∃ e : ℕ, ∀ i, m i ≤ e := by
    rcases isEmpty_or_nonempty s with _ | _
    · exact ⟨0, fun i ↦ isEmptyElim i⟩
    obtain ⟨e, he⟩ := (Set.finite_range m).bddAbove
    exact ⟨e, fun i ↦ he (Set.mem_range_self i)⟩
  refine ⟨e, fun i ↦ ?_⟩
  rw [hmspec i]
  exact H.antitone_Γpow (he i)

omit [Unique ι] in
/-- The `e` produced by `exists_Γpow_le_of_isClosed` also works for every larger index. -/
theorem Γpow_le_of_le {e n : ℕ} (h : e ≤ n) {O : Subgroup H.Γ}
    (hO : (H.Γpow e : Subgroup H.Γ) ≤ O) : (H.Γpow n : Subgroup H.Γ) ≤ O :=
  le_trans (H.antitone_Γpow h) hO

end EquivMvZp
