/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.NormIndexIdele
public import Iwasawalib.NumberTheory.CFT.LocalPowerIndexProduct

@[expose] public section

/-!
# Anti-vacuity controls for the index reduction and for the local power index

A reduction lemma that is true for a trivial reason proves nothing, so both halves of the
reduction are exercised here on data where the answer is known independently.

## The index lemma

`Subgroup.index_sup_eq_relIndex_of_sup_eq_top` rewrites `[G : P · D]` as a *relative* index
inside `A`.  Taking `G = ℤ/2 × ℤ/3`, `P = ℤ/2 × 1`, `A = 1 × ℤ/3` and `D = 1`, the two sides are
`[G : P] = 3` and `[A : 1] = 3`, while the plain index `[G : A] = 2`.  So the control
distinguishes the relative index from the absolute one: `Subgroup.Control.index_eq_three` and
`Subgroup.Control.relIndex_eq_three` agree at `3`, and `Subgroup.Control.index_A_eq_two` shows
that the value is *not* the index of `A` in `G`.

## The local power index

`NumberField.powIndex_adicCompletion_units_eq_absNorm_pow_ord` writes the local index as
`n · #μ_n(K_v) · N(v) ^ ord_v(n)`.  The last factor is the one that the residue-characteristic
bookkeeping produces, and it is *not* always `1` and *not* always `≠ 1`:

* `NumberField.Control.powIndex_adicCompletion_units_of_coprime` : at a place not above `n` the
  factor is `1` and the index is exactly `n · #μ_n(K_v)`;
* `NumberField.Control.one_lt_absNorm_pow_ord_natCast` : at a place above the prime `p`, the
  factor for `n = p` is `> 1`, so the index is strictly larger than `p · #μ_p(K_v)`.

A bookkeeping error that made the exponent identically zero would refute the second, and one
that made it always positive would refute the first.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace Subgroup.Control

/-- `G = ℤ/2 × ℤ/3`, written multiplicatively. -/
abbrev G : Type := Multiplicative (ZMod 2) × Multiplicative (ZMod 3)

/-- `P = ℤ/2 × 1`. -/
abbrev P : Subgroup G := (⊤ : Subgroup (Multiplicative (ZMod 2))).prod ⊥

/-- `A = 1 × ℤ/3`. -/
abbrev A : Subgroup G := (⊥ : Subgroup (Multiplicative (ZMod 2))).prod ⊤

theorem sup_eq_top : P ⊔ A = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  have hx : x = ((x.1, 1) : G) * ((1, x.2) : G) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [hx]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨trivial, rfl⟩)
    (Subgroup.mem_sup_right ⟨rfl, trivial⟩)

theorem inf_eq_bot : P ⊓ A = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  exact Prod.ext hx.2.1 hx.1.2

/-- `[G : P] = 3`. -/
theorem index_eq_three : (P ⊔ (⊥ : Subgroup G)).index = 3 := by
  rw [sup_bot_eq, Subgroup.index_prod, Subgroup.index_top, Subgroup.index_bot, one_mul,
    Nat.card_eq_fintype_card]
  rfl

/-- The relative index produced by `Subgroup.index_sup_eq_relIndex_of_sup_eq_top` is also `3`. -/
theorem relIndex_eq_three : ((P ⊓ A) ⊔ (⊥ : Subgroup G)).relIndex A = 3 := by
  rw [← Subgroup.index_sup_eq_relIndex_of_sup_eq_top sup_eq_top (bot_le (a := A))]
  exact index_eq_three

/-- **The discriminating half**: the absolute index of `A` is `2`, not `3`, so the relative
index of the lemma is genuinely relative. -/
theorem index_A_eq_two : (A : Subgroup G).index = 2 := by
  rw [Subgroup.index_prod, Subgroup.index_top, Subgroup.index_bot, mul_one,
    Nat.card_eq_fintype_card]
  rfl

end Subgroup.Control

namespace NumberField.Control

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- **At a place prime to `n` the local index is exactly `n · #μ_n(K_v)`.** -/
theorem powIndex_adicCompletion_units_of_coprime {p n : ℕ} (hpv : (p : 𝓞 K) ∈ v.asIdeal)
    (hn : Nat.Coprime n p) (hn0 : n ≠ 0) :
    PowerIndex.powIndex n (Additive (v.adicCompletion K)ˣ)
      = n * Nat.card (rootsOfUnity n (LocalCFT.integers (F := v.adicCompletion K))) := by
  rw [powIndex_adicCompletion_units_eq_absNorm_pow_ord v hn0,
    ord_natCast_eq_zero_of_coprime v hpv hn hn0]
  simp

/-- **At a place above `p` the factor `N(v) ^ ord_v(p)` is `> 1`.**  So the local index at
`n = p` is strictly larger than `p · #μ_p(K_v)`: the exponent produced by the residue
characteristic is not identically zero. -/
theorem one_lt_absNorm_pow_ord_natCast {p : ℕ} (hp : p.Prime) (hpv : (p : 𝓞 K) ∈ v.asIdeal) :
    1 < Ideal.absNorm v.asIdeal ^ (v.ord K ((p : K))).toNat := by
  obtain ⟨e, he1, hpe⟩ := exists_valued_natCast_eq_exp v hpv hp.pos.ne'
  have hord : v.ord K ((p : K)) = e := ord_eq_of_valued_adicCompletion_natCast v hpe
  have hN : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine one_lt_pow₀ hN ?_
  rw [hord]
  omega

/-- The strict inequality, spelled out on the index itself. -/
theorem lt_powIndex_adicCompletion_units {p : ℕ} (hp : p.Prime)
    (hpv : (p : 𝓞 K) ∈ v.asIdeal) :
    p * Nat.card (rootsOfUnity p (LocalCFT.integers (F := v.adicCompletion K)))
      < PowerIndex.powIndex p (Additive (v.adicCompletion K)ˣ) := by
  rw [powIndex_adicCompletion_units_eq_absNorm_pow_ord v hp.pos.ne']
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hpos : 0 < Nat.card (rootsOfUnity p (LocalCFT.integers (F := v.adicCompletion K))) := by
    rw [← PowerIndex.powKer_additive_units_eq_card_rootsOfUnity]
    exact PowerIndex.powKer_additive_units_pos _ p
  have h := one_lt_absNorm_pow_ord_natCast v hp hpv
  calc p * Nat.card (rootsOfUnity p (LocalCFT.integers (F := v.adicCompletion K)))
      = p * (Nat.card (rootsOfUnity p (LocalCFT.integers (F := v.adicCompletion K))) * 1) := by
        rw [mul_one]
    _ < p * (Nat.card (rootsOfUnity p (LocalCFT.integers (F := v.adicCompletion K)))
        * Ideal.absNorm v.asIdeal ^ (v.ord K ((p : K))).toNat) := by
        exact (Nat.mul_lt_mul_left hp.pos).2 ((Nat.mul_lt_mul_left hpos).2 h)

end NumberField.Control

end
