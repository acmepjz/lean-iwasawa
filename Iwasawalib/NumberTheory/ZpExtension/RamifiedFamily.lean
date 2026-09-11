/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.ShiftStepOne

@[expose] public section

/-!
# Which places ramify in a `ℤₚ`-extension, and the ramified family

`MvZpExtension.exists_totally_ramified` (Washington, Lemma 13.3) and its shifted form
`MvZpExtension.exists_shift_totally_ramified` take the ramified places of `K∞ / K` as a
*parameter*: a finite family `v : s → AbsoluteValue K∞ ℝ` with `I_{v j}(K∞/K) ≠ ⊥`.  This file
supplies what is needed to produce that family, and separates sharply what is unconditional
from what is not.

## The unconditional part: ramification in a `ℤₚ`-extension is all-or-unbounded

The inertia subgroup `I_w(K∞/K)` of a place `w` of `K∞` is a *closed* subgroup of
`Γ = Gal(K∞/K) ≅ ℤₚ` (`AbsoluteValue.isClosed_inertiaSubgroup`), hence is either trivial or
`Γ^{p^m}` for a unique `m` (`EquivMvZp.eq_bot_or_Γpow_of_isClosed`).  In the second case the
ramification index of `w` in the layer `Kₙ / K` is computed exactly:

`e(w | Kₙ/K) = [I_w(K∞/K) : I_w(K∞/Kₙ)] = [Γ^{p^m} : Γ^{p^n}] = p^{n-m}`   (`n ≥ m`),

which is unbounded in `n`.  Hence the criterion

`I_w(K∞/K) = ⊥  ↔  the ramification indices e(w | Kₙ/K) are bounded`

(`MvZpExtension.inertiaSubgroup_eq_bot_iff_bddAbove_ramificationIdx`).  Nothing in this part
uses class field theory, and none of it is `sorry`-tainted.

## What this does *not* prove: "only the primes above `p` ramify"

It is tempting to argue that at a place `w` of residue characteristic `ℓ ≠ p` the extension is
*tamely* ramified, that tame inertia is finite cyclic, and that a finite subgroup of the
torsion-free pro-`p` group `Γ ≅ ℤₚ` is trivial.  The last step is correct and is recorded here
as `MvZpExtension.inertiaSubgroup_eq_bot_of_finite`.  The middle step is not: tame inertia is
cyclic of order prime to the **residue** characteristic `ℓ`, not prime to `p`.  For `ℓ ≠ p`
those are different conditions, and tame inertia of order divisible by `p` is common —
`ℚ(√5) / ℚ` is tamely ramified at `5` with inertia of order `2 = p` for `p = 2`.  What has to
be ruled out is an infinite tame inertia group, i.e. a tamely and totally ramified
`ℤₚ`-extension of the local field `K_v`, and that is *not* ruled out by tameness: the tame
quotient of the absolute inertia group of `K_v` is `∏_{q ≠ ℓ} ℤ_q`, which does have `ℤₚ` as a
quotient.  It is ruled out by *abelianness*: Frobenius acts on the tame quotient by `x ↦ x^q`,
so in an abelian extension inertia is killed by `q - 1` and `e(w | v) ∣ N(v) - 1`, a bound
uniform in the layer.  That bound is the local reciprocity input — classically local class
field theory, `I_v ≅ 𝒪_v^×` whose pro-`p` part is finite — and neither it nor the tame
character is available in this repository or in mathlib.

So the criterion above is the exact interface: *supply a bound on the tame ramification indices
that is uniform in `n`, and "unramified outside `p`" follows with no further `ℤₚ`-theory.*

## The two arithmetic inputs, and their status

* *at least one place ramifies*: `MvZpExtension.exists_inertiaSubgroup_ne_bot` is proved here,
  but is **`sorry`-tainted**: the only route in the repository is
  `NumberField.IsUnramifiedEverywhere.finiteDimensional`, which rests on
  `NumberField.IsUnramifiedEverywhere.surjective_artinMap`, which is `sorry`.  There is no
  `sorry`-free route: "unramified everywhere ⇒ finite" *is* the reciprocity statement.
* *only finitely many places ramify* (classically: only those above `p`, of which there are
  finitely many): this stays a **hypothesis**, `hfin` below.  It is exactly the missing local
  input described above.

## Main results

* `MvZpExtension.ramificationIdx_Kn_eq_relIndex`, `MvZpExtension.ramificationIdx_Kn_eq_pow`:
  the ramification index in the layers, computed.
* `MvZpExtension.inertiaSubgroup_eq_bot_iff_bddAbove_ramificationIdx`: **the bounded-ramification
  criterion**, and `MvZpExtension.not_bddAbove_ramificationIdx_of_ne_bot`,
  `MvZpExtension.inertiaSubgroup_eq_bot_of_finite`.
* `MvZpExtension.finite_ramified_of_bddAbove_outside`: the finiteness of the ramified set,
  reduced to a uniform bound on the tame ramification indices outside a finite set of places.
* `MvZpExtension.exists_totally_ramified_of_finite_ramified`,
  `MvZpExtension.exists_shift_totally_ramified_of_bddAbove_outside` and
  `MvZpExtension.exists_shift_totally_ramified_of_finite_ramified`: the ramified family, in the
  two forms `MvZpExtension.exists_totally_ramified` and
  `MvZpExtension.exists_shift_totally_ramified` consume; both take only `hfin`, and neither is
  `sorry`-tainted.
* `MvZpExtension.exists_inertiaSubgroup_ne_bot`: at least one place ramifies — **tainted**, see
  its own warning.
-/
open IntermediateField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- `Gal(K∞/Kₙ)`, as the range of the transport map, is `Γ^{pⁿ}`. -/
theorem range_restrictRestrict_Kn (n : ℕ) :
    (IntermediateField.restrictRestrictAlgEquivMapHom K Kinf ↥(H.Kn n) Kinf).range
      = (H.Γpow n : Subgroup H.Γ) := by
  haveI := H.isGalois (H.Kn n)
  rw [IntermediateField.range_restrictRestrictAlgEquivMapHom_eq_fixingSubgroup' K (H.Kn n),
    H.fixingSubgroup_Kn]

/-- The ramification index of a place `w` of `K∞` in the layer `Kₙ / K` is the relative index
of `Γ^{pⁿ}` in the inertia subgroup `I_w(K∞/K)`. -/
theorem ramificationIdx_Kn_eq_relIndex (w : AbsoluteValue Kinf ℝ) (n : ℕ) :
    w.ramificationIdxOfIsScalarTower K ↥(H.Kn n)
      = (H.Γpow n : Subgroup H.Γ).relIndex (w.inertiaSubgroup K) := by
  rw [AbsoluteValue.ramificationIdxOfIsScalarTower_eq_range_relIndex K ↥(H.Kn n) w,
    H.range_restrictRestrict_Kn n]

/-! ### The relative index of the layers -/

set_option linter.unusedSectionVars false in
/-- `[Γ^{p^m} : Γ^{p^n}] = p^{n-m}` for `m ≤ n`. -/
theorem relIndex_Γpow [Unique ι] {m n : ℕ} (h : m ≤ n) :
    (H.Γpow n : Subgroup H.Γ).relIndex (H.Γpow m) = p ^ (n - m) := by
  have hle : (H.Γpow n : Subgroup H.Γ) ≤ (H.Γpow m : Subgroup H.Γ) := H.antitone_Γpow h
  have key := Subgroup.relIndex_mul_index hle
  rw [H.index_Γpow₁ n, H.index_Γpow₁ m] at key
  have hpm : 0 < p ^ m := pow_pos (Nat.pos_of_ne_zero (Fact.out (p := p.Prime)).ne_zero) m
  refine Nat.eq_of_mul_eq_mul_right hpm ?_
  rw [key, ← pow_add, Nat.sub_add_cancel h]

/-! ### Ramification indices in the layers, computed -/

/-- **The ramification index in the layers, computed.**  If the inertia subgroup of a place `w`
of `K∞` in `Γ = Gal(K∞/K)` is `Γ^{p^m}` — which by `EquivMvZp.eq_bot_or_Γpow_of_isClosed` is
the only alternative to being trivial — then the ramification index of `w` in `Kₙ / K` is
exactly `p^{n-m}` for `n ≥ m`. -/
theorem ramificationIdx_Kn_eq_pow [Unique ι] (w : AbsoluteValue Kinf ℝ) {m : ℕ}
    (hm : w.inertiaSubgroup K = (H.Γpow m : Subgroup H.Γ)) {n : ℕ} (h : m ≤ n) :
    w.ramificationIdxOfIsScalarTower K ↥(H.Kn n) = p ^ (n - m) := by
  rw [H.ramificationIdx_Kn_eq_relIndex w n, hm, H.relIndex_Γpow h]

/-- An unramified place of `K∞ / K` is unramified in every layer. -/
theorem ramificationIdx_Kn_eq_one (w : AbsoluteValue Kinf ℝ)
    (hw : w.inertiaSubgroup K = ⊥) (n : ℕ) :
    w.ramificationIdxOfIsScalarTower K ↥(H.Kn n) = 1 := by
  rw [H.ramificationIdx_Kn_eq_relIndex w n, hw, Subgroup.relIndex_bot_right]

/-- Either the inertia subgroup of `w` in `Γ` is trivial, or it is `Γ^{p^m}` for some `m`. -/
theorem inertiaSubgroup_eq_bot_or_eq_Γpow [Unique ι] (w : AbsoluteValue Kinf ℝ) :
    w.inertiaSubgroup K = ⊥ ∨ ∃ m : ℕ, w.inertiaSubgroup K = (H.Γpow m : Subgroup H.Γ) :=
  H.eq_bot_or_Γpow_of_isClosed _ (AbsoluteValue.isClosed_inertiaSubgroup K w)

/-! ### The bounded-ramification criterion -/

/-- **A place of a `ℤₚ`-extension is unramified exactly when its ramification indices in the
layers are bounded.**  In one direction an unramified place has all ramification indices `1`;
in the other, a ramified place has inertia subgroup `Γ^{p^m}` and hence ramification index
`p^{n-m}` in `Kₙ / K`, which is unbounded.

This is the unconditional `ℤₚ`-side of "only the primes above `p` ramify": at a place `w` of
`K∞` whose residue characteristic is different from `p`, every layer `Kₙ / K` is *tamely*
ramified at `w`, and what has to be supplied is a bound on the tame ramification indices
`e(w | v)` that is uniform in `n` (classically `e(w | v) ∣ N(v) - 1`, which comes from local
class field theory or, equivalently, from the tame character of an abelian extension).  No
such bound is available in this repository; see the module docstring. -/
theorem inertiaSubgroup_eq_bot_iff_bddAbove_ramificationIdx [Unique ι]
    (w : AbsoluteValue Kinf ℝ) :
    w.inertiaSubgroup K = ⊥ ↔
      ∃ N : ℕ, ∀ n : ℕ, w.ramificationIdxOfIsScalarTower K ↥(H.Kn n) ≤ N := by
  refine ⟨fun hw ↦ ⟨1, fun n ↦ (H.ramificationIdx_Kn_eq_one w hw n).le⟩, fun ⟨N, hN⟩ ↦ ?_⟩
  rcases H.inertiaSubgroup_eq_bot_or_eq_Γpow w with hw | ⟨m, hm⟩
  · exact hw
  · exfalso
    have hle := hN (m + N + 1)
    rw [H.ramificationIdx_Kn_eq_pow w hm (by omega)] at hle
    have h2 : (2 : ℕ) ^ (N + 1) ≤ p ^ (m + N + 1 - m) := by
      have : m + N + 1 - m = N + 1 := by omega
      rw [this]
      exact Nat.pow_le_pow_left (Fact.out (p := p.Prime)).two_le _
    have h3 : N < 2 ^ (N + 1) := lt_of_lt_of_le (Nat.lt_two_pow_self)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega


/-- **A ramified place of a `ℤₚ`-extension has unbounded ramification indices in the layers.**
The contrapositive half of `MvZpExtension.inertiaSubgroup_eq_bot_iff_bddAbove_ramificationIdx`,
in the form that is usually applied. -/
theorem not_bddAbove_ramificationIdx_of_ne_bot [Unique ι] (w : AbsoluteValue Kinf ℝ)
    (hw : w.inertiaSubgroup K ≠ ⊥) (N : ℕ) :
    ∃ n : ℕ, N < w.ramificationIdxOfIsScalarTower K ↥(H.Kn n) := by
  by_contra hc
  refine hw ((H.inertiaSubgroup_eq_bot_iff_bddAbove_ramificationIdx w).2 ⟨N, fun n ↦ ?_⟩)
  by_contra hn
  exact hc ⟨n, by omega⟩

include H in
/-- **A finite inertia subgroup in a `ℤₚ`-extension is trivial.**  This is the correct form of
the "torsion-free pro-`p`" argument: `Γ ≅ ℤₚ` has no nontrivial finite subgroup.  Note what it
does *not* say: at a place of residue characteristic `≠ p` the inertia subgroup of a single
layer `Kₙ / K` is tame, but tameness bounds its order away from the *residue* characteristic,
not from `p`, so tameness alone does not make `I_w(K∞/K)` finite. -/
theorem inertiaSubgroup_eq_bot_of_finite [Unique ι] (w : AbsoluteValue Kinf ℝ)
    [hfin : Finite (w.inertiaSubgroup K)] : w.inertiaSubgroup K = ⊥ := by
  rw [H.inertiaSubgroup_eq_bot_iff_bddAbove_ramificationIdx w]
  refine ⟨Nat.card (w.inertiaSubgroup K), fun n ↦ ?_⟩
  rw [H.ramificationIdx_Kn_eq_relIndex w n]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)

/-! ### The ramified family -/

section Family

variable [NumberField K]

include H in
/-- **At least one place of `K` ramifies in `K∞`.**

**Warning**: this declaration is *not* unconditional.  Its proof is the classical one — an
everywhere unramified abelian extension of a number field is finite, because the Artin map
`Cl(K) → Gal(K∞/K)` is surjective — and in this repository that route is
`NumberField.IsUnramifiedEverywhere.finiteDimensional`, which is derived from
`NumberField.IsUnramifiedEverywhere.surjective_artinMap`, which is `sorry`.  So this theorem
depends on `sorryAx`, and so does everything below it that does not take the conclusion as a
hypothesis.  No `sorry`-free route to this statement exists in the repository: the implication
"unramified everywhere ⇒ finite" *is* the reciprocity input. -/
theorem exists_inertiaSubgroup_ne_bot [Unique ι] :
    ∃ w : AbsoluteValue Kinf ℝ, w.inertiaSubgroup K ≠ ⊥ := by
  by_contra hcon
  have hc : ∀ w : AbsoluteValue Kinf ℝ, w.inertiaSubgroup K = ⊥ := fun w ↦ by
    by_contra h
    exact hcon ⟨w, h⟩
  haveI := H.isGalois (⊤ : IntermediateField K Kinf)
  haveI := H.isAbelianGalois (⊤ : IntermediateField K Kinf)
  haveI : NumberField.IsUnramifiedEverywhere K ↥(⊤ : IntermediateField K Kinf) :=
    AbsoluteValue.isUnramifiedEverywhere_of_inertiaSubgroup_le_fixingSubgroup K ⊤
      fun w ↦ by rw [hc w]; exact bot_le
  haveI : FiniteDimensional K ↥(⊤ : IntermediateField K Kinf) :=
    NumberField.IsUnramifiedEverywhere.finiteDimensional K _
  exact H.infinite_dimensional
    ((IntermediateField.topEquiv (F := K) (E := Kinf)).toLinearEquiv.finiteDimensional)

omit [NumberField K] in
/-- **The ramified family, as `MvZpExtension.exists_totally_ramified` consumes it.**  If only
finitely many places of `K∞` ramify in `K∞ / K`, then there is a single layer `Kₑ` beyond which
`K∞ / Kₙ` is totally ramified at *every* ramified place simultaneously.

The hypothesis `hfin` is the only input: it is the statement that the ramified set is finite,
which classically follows from "only the primes above `p` ramify" (local class field theory)
together with the finiteness of the set of places above `p`.  Nothing here is `sorry`-tainted:
the taint enters only through `MvZpExtension.exists_inertiaSubgroup_ne_bot`, which is what
makes the family *nonempty*, and which is not used here. -/
theorem exists_totally_ramified_of_finite_ramified [Unique ι]
    (hfin : {w : AbsoluteValue Kinf ℝ | w.inertiaSubgroup K ≠ ⊥}.Finite) :
    ∃ e : ℕ, ∀ n, e ≤ n → ∀ w : AbsoluteValue Kinf ℝ, w.inertiaSubgroup K ≠ ⊥ →
      w.inertiaSubgroup ↥(H.Kn n) = ⊤ := by
  haveI := hfin.to_subtype
  obtain ⟨e, he⟩ := H.exists_totally_ramified
    (s := ↥{w : AbsoluteValue Kinf ℝ | w.inertiaSubgroup K ≠ ⊥}) (fun j ↦ (j : _)) fun j ↦ j.2
  exact ⟨e, fun n hn w hw ↦ he n hn ⟨w, hw⟩⟩

/-- **The ramified family in the form `MvZpExtension.exists_shift_totally_ramified` consumes**,
i.e. total ramification of `K∞ / Kₙ` read as a `ℤₚ`-extension of `Kₙ` (`MvZpExtension.shift`),
which is what `MvZpExtension.xinfQuotientMulEquivOfPlace'` — Step 1 of Washington's Lemma
13.15 — is applied to.  As in
`MvZpExtension.exists_totally_ramified_of_finite_ramified`, the only input is finiteness of
the ramified set, and nothing here is `sorry`-tainted. -/
theorem exists_shift_totally_ramified_of_finite_ramified [Unique ι]
    (hfin : {w : AbsoluteValue Kinf ℝ | w.inertiaSubgroup K ≠ ⊥}.Finite) :
    ∃ e : ℕ, ∀ n, e ≤ n →
      ∀ w : AbsoluteValue ↥((H.shift n).Linf.restrictScalars ↥(H.Kn n)) ℝ,
        ((H.shift n).placeBelow w).inertiaSubgroup K ≠ ⊥ →
          ((H.shift n).placeBelow w).inertiaSubgroup ↥(H.Kn n) = ⊤ := by
  haveI := hfin.to_subtype
  obtain ⟨e, he⟩ := H.exists_shift_totally_ramified
    (s := ↥{w : AbsoluteValue Kinf ℝ | w.inertiaSubgroup K ≠ ⊥}) (fun j ↦ (j : _)) fun j ↦ j.2
  exact ⟨e, fun n hn w hw ↦ he n hn ⟨_, hw⟩ w rfl⟩

omit [NumberField K] in
/-- **The finiteness hypothesis `hfin`, reduced to the local input.**  If outside a finite set
`S` of places of `K∞` — in practice the places above `p`, of which there are finitely many —
every place has ramification indices in the layers `Kₙ / K` bounded uniformly in `n`, then only
finitely many places ramify in `K∞ / K`.

This is the whole of the `ℤₚ`-side of "only the primes above `p` ramify": the user of this
lemma has to supply exactly the classical local statement `e(w | v) ∣ N(v) - 1` for `v ∤ p`,
uniformly in the layer, and nothing else.  Unconditional. -/
theorem finite_ramified_of_bddAbove_outside [Unique ι] {S : Set (AbsoluteValue Kinf ℝ)}
    (hS : S.Finite)
    (hbound : ∀ w ∉ S, ∃ N : ℕ, ∀ n : ℕ, w.ramificationIdxOfIsScalarTower K ↥(H.Kn n) ≤ N) :
    {w : AbsoluteValue Kinf ℝ | w.inertiaSubgroup K ≠ ⊥}.Finite := by
  refine hS.subset fun w hw ↦ ?_
  by_contra hwS
  exact hw ((H.inertiaSubgroup_eq_bot_iff_bddAbove_ramificationIdx w).2 (hbound w hwS))

/-- **The ramified family from the local input alone**, in the form
`MvZpExtension.exists_shift_totally_ramified` consumes: combine
`MvZpExtension.finite_ramified_of_bddAbove_outside` with
`MvZpExtension.exists_shift_totally_ramified_of_finite_ramified`.  Unconditional: not
`sorry`-tainted. -/
theorem exists_shift_totally_ramified_of_bddAbove_outside [Unique ι]
    {S : Set (AbsoluteValue Kinf ℝ)} (hS : S.Finite)
    (hbound : ∀ w ∉ S, ∃ N : ℕ, ∀ n : ℕ, w.ramificationIdxOfIsScalarTower K ↥(H.Kn n) ≤ N) :
    ∃ e : ℕ, ∀ n, e ≤ n →
      ∀ w : AbsoluteValue ↥((H.shift n).Linf.restrictScalars ↥(H.Kn n)) ℝ,
        ((H.shift n).placeBelow w).inertiaSubgroup K ≠ ⊥ →
          ((H.shift n).placeBelow w).inertiaSubgroup ↥(H.Kn n) = ⊤ :=
  H.exists_shift_totally_ramified_of_finite_ramified
    (H.finite_ramified_of_bddAbove_outside hS hbound)


end Family

end MvZpExtension
