/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.UnitFiltrationGraded

@[expose] public section

/-!
# The additive filtration of the valuation ring, and its finite quotients

`Iwasawalib/NumberTheory/LocalCFT/UnitFiltrationGraded.lean` computes the graded pieces of the
*multiplicative* filtration `U^(k) = 1 + 𝔪^k`.  This file does the same for the *additive*
filtration by the powers of the maximal ideal,

`valBall F k = 𝔪^k = {x ∈ 𝒪 : v x ≤ exp (-k)}`,

whose graded pieces are again the residue field, via `x ↦ x / π^k mod 𝔪`.  The consequence
used downstream is that every `𝔪^k` — and hence every additive subgroup of `𝒪` containing one
of them — has **finite index** in `𝒪` when the residue field is finite
(`LocalCFT.finite_quotient_of_valBall_le`).

That is the finiteness half of the commensurability argument for
`h(D_w, O_w⁺) = 1`: an `O_v`-lattice spanned by a normal basis of `L_w / K_v` contains a ball
`𝔪^k`, so it has finite index in `O_w`, so the two have the same Herbrand quotient.

## Main definitions

* `LocalCFT.valBall`: the additive subgroup `𝔪^k` of `𝒪`.
* `LocalCFT.ballGradedHom`: the homomorphism `𝔪^k → 𝒪/𝔪`, `x ↦ x / π^k mod 𝔪`.

## Main statements

* `LocalCFT.ker_ballGradedHom`: its kernel is `𝔪^(k+1)`.
* `LocalCFT.index_valBall_ne_zero`: `[𝒪 : 𝔪^k] < ∞` when the residue field is finite.
* `LocalCFT.finite_quotient_of_valBall_le`: any additive subgroup of `𝒪` containing some `𝔪^k`
  has finite index.
-/

noncomputable section

open WithZero IsLocalRing

namespace LocalCFT

variable {F : Type*} [Field F] [Valued F ℤᵐ⁰]

/-! ## Discreteness of the value group -/

/-- In `ℤᵐ⁰` an element strictly below `exp m` is at most `exp (m - 1)`. -/
theorem le_exp_sub_one_of_lt_exp {a : ℤᵐ⁰} {m : ℤ} (h : a < exp m) : a ≤ exp (m - 1) := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact zero_le
  · rw [← exp_log ha] at h ⊢
    rw [exp_le_exp]
    have := (exp_lt_exp).1 h
    omega

/-! ## The additive filtration -/

variable (F) in
/-- The additive subgroup `𝔪^k = {x ∈ 𝒪 : v x ≤ exp (-k)}` of the valuation ring. -/
def valBall (k : ℕ) : AddSubgroup (integers (F := F)) where
  carrier := {x : integers (F := F) | (Valued.v (x : F) : ℤᵐ⁰) ≤ exp (-(k : ℤ))}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    calc (Valued.v ((a + b : integers (F := F)) : F) : ℤᵐ⁰)
        ≤ max (Valued.v ((a : integers (F := F)) : F)) (Valued.v ((b : integers (F := F)) : F)) :=
          Valuation.map_add _ _ _
      _ ≤ exp (-(k : ℤ)) := max_le ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [show ((0 : integers (F := F)) : F) = 0 from rfl, map_zero]
    exact zero_le
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rwa [show ((-a : integers (F := F)) : F) = -((a : integers (F := F)) : F) from rfl,
      Valuation.map_neg]

theorem mem_valBall {k : ℕ} {x : integers (F := F)} :
    x ∈ valBall F k ↔ (Valued.v ((x : integers (F := F)) : F) : ℤᵐ⁰) ≤ exp (-(k : ℤ)) :=
  Set.mem_ofPred_eq ▸ Iff.rfl

theorem valBall_zero : valBall F 0 = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  rw [mem_valBall, Nat.cast_zero, neg_zero, exp_zero]
  exact x.2

theorem valBall_succ_le (k : ℕ) : valBall F (k + 1) ≤ valBall F k := by
  intro x hx
  rw [mem_valBall] at hx ⊢
  refine le_trans hx ?_
  rw [exp_le_exp]
  omega

/-! ## The graded map -/

variable {π : F}

/-- The element `x / π^k` of the valuation ring, for `x ∈ 𝔪^k`. -/
def ballGradedFun (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (k : ℕ) (x : valBall F k) :
    integers (F := F) :=
  ⟨((x : integers (F := F)) : F) / π ^ k, by
    rw [mem_integer, map_div₀, valued_uniformizer_pow hπ, div_le_iff₀ exp_pos, one_mul]
    exact x.2⟩

@[simp] theorem coe_ballGradedFun (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (k : ℕ)
    (x : valBall F k) :
    ((ballGradedFun hπ k x : integers (F := F)) : F)
      = ((x : integers (F := F)) : F) / π ^ k := rfl

/-- **The graded map `𝔪^k → 𝒪/𝔪`**, `x ↦ x / π^k mod 𝔪`. -/
def ballGradedHom (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (k : ℕ) :
    valBall F k →+ ResidueField (integers (F := F)) where
  toFun x := residue (integers (F := F)) (ballGradedFun hπ k x)
  map_zero' := by
    have h : ballGradedFun hπ k (0 : valBall F k) = 0 := by
      refine Subtype.ext ?_
      rw [coe_ballGradedFun]
      show ((0 : F)) / π ^ k = 0
      simp
    rw [h, map_zero]
  map_add' x y := by
    have h : ballGradedFun hπ k (x + y)
        = ballGradedFun hπ k x + ballGradedFun hπ k y := by
      refine Subtype.ext ?_
      rw [coe_ballGradedFun]
      push_cast
      rw [coe_ballGradedFun, coe_ballGradedFun]
      show (((x : integers (F := F)) : F) + ((y : integers (F := F)) : F)) / π ^ k = _
      ring
    rw [h, map_add]

/-- **The kernel of the graded map is the next step of the filtration.** -/
theorem ker_ballGradedHom (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (k : ℕ) :
    (ballGradedHom hπ k).ker = (valBall F (k + 1)).addSubgroupOf (valBall F k) := by
  ext x
  rw [AddMonoidHom.mem_ker]
  show residue (integers (F := F)) (ballGradedFun hπ k x) = 0 ↔ _
  rw [residue_eq_zero_iff_valued_lt_one]
  show (Valued.v (((x : integers (F := F)) : F) / π ^ k) : ℤᵐ⁰) < 1 ↔ _
  rw [map_div₀, valued_uniformizer_pow hπ, div_lt_iff₀ exp_pos, one_mul]
  constructor
  · intro h
    have := le_exp_sub_one_of_lt_exp h
    rw [AddSubgroup.mem_addSubgroupOf, mem_valBall]
    refine le_trans this ?_
    rw [exp_le_exp]
    omega
  · intro h
    have h' : (Valued.v ((x : integers (F := F)) : F) : ℤᵐ⁰) ≤ exp (-((k : ℤ) + 1)) := by
      have := (AddSubgroup.mem_addSubgroupOf.1 h)
      rw [mem_valBall] at this
      refine le_trans this ?_
      rw [exp_le_exp]
      push_cast
      omega
    refine lt_of_le_of_lt h' ?_
    rw [exp_lt_exp]
    omega

/-! ## Finiteness of the quotients -/

variable [Finite (ResidueField (integers (F := F)))]

/-- The relative index of `𝔪^(k+1)` in `𝔪^k` is finite: the quotient embeds in the residue
field. -/
theorem relIndex_valBall_succ_ne_zero (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (k : ℕ) :
    (valBall F (k + 1)).relIndex (valBall F k) ≠ 0 := by
  have hfin : Finite (valBall F k ⧸ (valBall F (k + 1)).addSubgroupOf (valBall F k)) := by
    rw [← ker_ballGradedHom hπ k]
    exact Finite.of_injective _ (QuotientAddGroup.kerLift_injective (ballGradedHom hπ k))
  rw [AddSubgroup.relIndex]
  exact Nat.card_ne_zero.2 ⟨⟨0⟩, hfin⟩

/-- **`𝔪^k` has finite index in `𝒪`** when the residue field is finite. -/
theorem index_valBall_ne_zero (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (k : ℕ) :
    (valBall F k).index ≠ 0 := by
  induction k with
  | zero => rw [valBall_zero, AddSubgroup.index_top]; exact one_ne_zero
  | succ n ih =>
      rw [← AddSubgroup.relIndex_mul_index (valBall_succ_le (F := F) n)]
      exact mul_ne_zero (relIndex_valBall_succ_ne_zero hπ n) ih

/-- **Any additive subgroup of `𝒪` containing some `𝔪^k` has finite index.** -/
theorem finite_quotient_of_valBall_le (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) {k : ℕ}
    {N : AddSubgroup (integers (F := F))} (hN : valBall F k ≤ N) :
    Finite (integers (F := F) ⧸ N) := by
  have hdvd : N.index ∣ (valBall F k).index := AddSubgroup.index_dvd_of_le hN
  have hne : N.index ≠ 0 := fun h ↦ index_valBall_ne_zero hπ k (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  exact Nat.finite_of_card_ne_zero hne

end LocalCFT
