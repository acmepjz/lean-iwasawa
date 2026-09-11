/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.UnitFiltrationPow
public import Iwasawalib.NumberTheory.LocalCFT.TameUnits
public import Mathlib.GroupTheory.Index

@[expose] public section

/-!
# The graded pieces of the unit filtration

Let `F` be a field with a discrete valuation `v : F → ℤᵐ⁰` admitting a uniformizer `π`
(`v π = exp (-1)`).  For `k ≥ 1` the map

`u ↦ (u - 1) / π^k  mod  𝔪`

is a surjective group homomorphism `U^(k) → (𝒪/𝔪, +)` with kernel `U^(k+1)`.  Hence

`[U^(k) : U^(k+1)] = q`   and   `[U^(k) : U^(k+j)] = q^j`,

where `q = #(𝒪/𝔪)` is the residue cardinality.  Together with
`LocalCFT.finite_quotient_unitFiltration_one` this gives that every `U^(k)` has finite index in
`𝒪^×`, which is the finiteness hypothesis of
`PowerIndex.powIndex_eq_powKer_mul_of_finiteIndex`.

## Main statements

* `LocalCFT.gradedHom`: the homomorphism `U^(k) → (𝒪/𝔪, +)`, with `gradedHom_surjective` and
  `ker_gradedHom`.
* `LocalCFT.relIndex_unitFiltration_succ`: `[U^(k) : U^(k+1)] = q`.
* `LocalCFT.relIndex_unitFiltration`: `[U^(k) : U^(k+j)] = q^j`.
* `LocalCFT.index_unitFiltration_one`: `U^(k)` has finite index in `𝒪^×`.
-/

noncomputable section

open WithZero IsLocalRing

namespace LocalCFT

variable {F : Type*} [Field F] [hv : Valued F ℤᵐ⁰]

/-! ## Powers of a uniformizer -/

variable {π : F}

theorem uniformizer_ne_zero (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) : π ≠ 0 := by
  intro h
  rw [h, map_zero] at hπ
  exact exp_ne_zero hπ.symm

theorem valued_uniformizer_pow (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (k : ℕ) :
    (Valued.v (π ^ k) : ℤᵐ⁰) = exp (-(k : ℤ)) := by
  rw [map_pow, hπ, ← exp_nsmul]
  congr 1
  rw [nsmul_eq_mul]
  ring

theorem uniformizer_pow_ne_zero (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (k : ℕ) :
    π ^ k ≠ 0 := pow_ne_zero k (uniformizer_ne_zero hπ)

/-! ## The graded map -/

/-- The element `(u - 1) / π^k` of the valuation ring, for `u ∈ U^(k)`. -/
def gradedFun (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (k : ℕ)
    (u : unitFiltration (F := F) k) : integers (F := F) :=
  ⟨((((u : (integers (F := F))ˣ) : integers (F := F)) : F) - 1) / π ^ k, by
    rw [mem_integer, map_div₀, valued_uniformizer_pow hπ, div_le_iff₀ exp_pos, one_mul]
    exact u.2⟩

@[simp] theorem coe_gradedFun (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (k : ℕ)
    (u : unitFiltration (F := F) k) :
    ((gradedFun hπ k u : integers (F := F)) : F)
      = ((((u : (integers (F := F))ˣ) : integers (F := F)) : F) - 1) / π ^ k := rfl

/-- **The graded map `U^(k) → (𝒪/𝔪, +)`**, `u ↦ (u-1)/π^k mod 𝔪`.  It is a homomorphism
because `(1+x)(1+y) - 1 = x + y + xy` and the cross term `xy/π^k` has valuation at most
`exp (-k) < 1`. -/
def gradedHom (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) {k : ℕ} (hk : 1 ≤ k) :
    unitFiltration (F := F) k →* Multiplicative (ResidueField (integers (F := F))) where
  toFun u := Multiplicative.ofAdd (residue (integers (F := F)) (gradedFun hπ k u))
  map_one' := by
    refine congrArg Multiplicative.ofAdd ?_
    have h : gradedFun hπ k (1 : unitFiltration (F := F) k) = 0 := by
      refine Subtype.ext ?_
      rw [coe_gradedFun]
      norm_num
    rw [h, map_zero]
  map_mul' u v := by
    refine congrArg Multiplicative.ofAdd ?_
    set a : F := (((u : (integers (F := F))ˣ) : integers (F := F)) : F) - 1 with hadef
    set b : F := (((v : (integers (F := F))ˣ) : integers (F := F)) : F) - 1 with hbdef
    have ha : (Valued.v a : ℤᵐ⁰) ≤ exp (-(k : ℤ)) := u.2
    have hb : (Valued.v b : ℤᵐ⁰) ≤ exp (-(k : ℤ)) := v.2
    have hdiff : gradedFun hπ k (u * v) - gradedFun hπ k u - gradedFun hπ k v
        = ⟨(a * b) / π ^ k, by
            rw [mem_integer, map_div₀, valued_uniformizer_pow hπ, div_le_iff₀ exp_pos, one_mul,
              map_mul]
            refine le_trans (mul_le_mul' ha hb) ?_
            rw [← exp_add, exp_le_exp]
            omega⟩ := by
      refine Subtype.ext ?_
      have hprod : ((((u * v : unitFiltration (F := F) k) : (integers (F := F))ˣ)
          : integers (F := F)) : F) = (1 + a) * (1 + b) := by
        rw [hadef, hbdef]
        push_cast
        ring
      push_cast
      rw [coe_gradedFun, coe_gradedFun, coe_gradedFun, hprod, ← hadef, ← hbdef]
      field_simp
      ring
    have hres : residue (integers (F := F))
        (gradedFun hπ k (u * v) - gradedFun hπ k u - gradedFun hπ k v) = 0 := by
      rw [hdiff, residue_eq_zero_iff_valued_lt_one]
      show (Valued.v ((a * b) / π ^ k) : ℤᵐ⁰) < 1
      rw [map_div₀, valued_uniformizer_pow hπ, div_lt_iff₀ exp_pos, one_mul, map_mul]
      refine lt_of_le_of_lt (mul_le_mul' ha hb) ?_
      rw [← exp_add, exp_lt_exp]
      omega
    rw [map_sub, map_sub, sub_eq_zero] at hres
    simp only [toAdd_ofAdd]
    linear_combination hres

@[simp] theorem gradedHom_apply (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) {k : ℕ} (hk : 1 ≤ k)
    (u : unitFiltration (F := F) k) :
    gradedHom hπ hk u = Multiplicative.ofAdd (residue (integers (F := F)) (gradedFun hπ k u)) :=
  rfl

/-- **The graded map is surjective.** -/
theorem gradedHom_surjective (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) {k : ℕ} (hk : 1 ≤ k) :
    Function.Surjective (gradedHom (F := F) hπ hk) := by
  intro r
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (Multiplicative.toAdd r)
  set x : F := ((a : integers (F := F)) : F) * π ^ k with hxdef
  have hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ)) := by
    rw [hxdef, map_mul, valued_uniformizer_pow hπ]
    exact le_trans (mul_le_mul' a.2 le_rfl) (by rw [one_mul])
  have hx1 : (Valued.v x : ℤᵐ⁰) < 1 := by
    refine lt_of_le_of_lt hx ?_
    rw [show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm, exp_lt_exp]
    omega
  refine ⟨⟨oneAddUnit hx1, oneAddUnit_mem hx1 hx⟩, ?_⟩
  have hval : gradedFun hπ k ⟨oneAddUnit hx1, oneAddUnit_mem hx1 hx⟩ = a := by
    refine Subtype.ext ?_
    rw [coe_gradedFun]
    show ((1 + x) - 1) / π ^ k = ((a : integers (F := F)) : F)
    rw [hxdef, add_sub_cancel_left, mul_div_assoc,
      div_self (uniformizer_pow_ne_zero hπ k), mul_one]
  rw [gradedHom_apply, hval]
  rfl

/-- **The kernel of the graded map is the next step of the filtration.** -/
theorem ker_gradedHom (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) {k : ℕ} (hk : 1 ≤ k) :
    (gradedHom (F := F) hπ hk).ker
      = (unitFiltration (F := F) (k + 1)).subgroupOf (unitFiltration (F := F) k) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    rw [gradedHom_apply, ofAdd_eq_one] at h
    have h0 := h
    rw [residue_eq_zero_iff_valued_lt_one, coe_gradedFun, map_div₀,
      valued_uniformizer_pow hπ, div_lt_iff₀ exp_pos, one_mul, lt_exp_iff_le_exp_sub_one] at h0
    show (Valued.v ((((u : (integers (F := F))ˣ) : integers (F := F)) : F) - 1) : ℤᵐ⁰)
      ≤ exp (-((k + 1 : ℕ) : ℤ))
    refine le_trans h0 ?_
    rw [exp_le_exp]
    push_cast
    omega
  · intro h
    have h0 : (Valued.v ((((u : (integers (F := F))ˣ) : integers (F := F)) : F) - 1) : ℤᵐ⁰)
        ≤ exp (-((k + 1 : ℕ) : ℤ)) := h
    rw [gradedHom_apply, ofAdd_eq_one]
    rw [residue_eq_zero_iff_valued_lt_one, coe_gradedFun, map_div₀,
      valued_uniformizer_pow hπ, div_lt_iff₀ exp_pos, one_mul, lt_exp_iff_le_exp_sub_one]
    refine le_trans h0 ?_
    rw [exp_le_exp]
    push_cast
    omega

/-! ## The indices -/

theorem unitFiltration_le {m n : ℕ} (h : m ≤ n) :
    unitFiltration (F := F) n ≤ unitFiltration (F := F) m :=
  fun _ hu ↦ unitFiltration_mem_of_le h hu


/-- **`[U^(k) : U^(k+1)] = q`**, the residue cardinality. -/
theorem relIndex_unitFiltration_succ (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) {k : ℕ}
    (hk : 1 ≤ k) :
    (unitFiltration (F := F) (k + 1)).relIndex (unitFiltration (F := F) k)
      = Nat.card (ResidueField (integers (F := F))) := by
  rw [Subgroup.relIndex, ← ker_gradedHom hπ hk, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (gradedHom_surjective hπ hk)]
  exact Nat.card_congr (Equiv.Set.univ _)

/-- **`[U^(k) : U^(k+j)] = q^j`.** -/
theorem relIndex_unitFiltration (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) {k : ℕ} (hk : 1 ≤ k)
    (j : ℕ) :
    (unitFiltration (F := F) (k + j)).relIndex (unitFiltration (F := F) k)
      = Nat.card (ResidueField (integers (F := F))) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show k + (j + 1) = (k + j) + 1 by omega,
      ← Subgroup.relIndex_mul_relIndex (unitFiltration (F := F) (k + j + 1))
        (unitFiltration (F := F) (k + j)) (unitFiltration (F := F) k)
        (unitFiltration_antitone _) (unitFiltration_le (by omega)),
      relIndex_unitFiltration_succ hπ (by omega : 1 ≤ k + j), ih, pow_succ]
    ring

/-! ## The bottom of the filtration: `[𝒪^× : U^(1)] = q - 1`

This is the sanity check that pins the indexing of `LocalCFT.unitFiltration` down: the *bottom*
step of the filtration has index `q - 1`, not `q`, while every *higher* step has index `q`.  Any
off-by-one in the definition of `unitFiltration` would give the same answer twice. -/

/-- The reduction map `𝒪^× → k^×`. -/
def residueUnitsHom : (integers (F := F))ˣ →* (ResidueField (integers (F := F)))ˣ :=
  Units.map (residue (integers (F := F))).toMonoidHom

/-- **`𝒪^× → k^×` is surjective**: a lift of a nonzero residue has valuation one, so it is a
unit of `𝒪`. -/
theorem residueUnitsHom_surjective : Function.Surjective (residueUnitsHom (F := F)) := by
  intro r
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((r : ResidueField (integers (F := F))))
  have hne : residue (integers (F := F)) a ≠ 0 := by
    rw [show residue (integers (F := F)) a = (r : ResidueField (integers (F := F))) from ha]
    exact r.ne_zero
  have hv : (Valued.v ((a : integers (F := F)) : F) : ℤᵐ⁰) = 1 := by
    refine le_antisymm a.2 ?_
    by_contra hlt
    exact hne ((residue_eq_zero_iff_valued_lt_one a).2 (lt_of_not_ge hlt))
  have hcoe : (unitOfValuedEqOne hv : integers (F := F)) = a := Subtype.ext rfl
  refine ⟨unitOfValuedEqOne hv, Units.ext ?_⟩
  show residue (integers (F := F)) (unitOfValuedEqOne hv : integers (F := F))
    = (r : ResidueField (integers (F := F)))
  rw [hcoe]
  exact ha

/-- **The kernel of `𝒪^× → k^×` is `U^(1)`.** -/
theorem ker_residueUnitsHom :
    (residueUnitsHom (F := F)).ker = unitFiltration (F := F) 1 := by
  ext u
  rw [MonoidHom.mem_ker, mem_unitFiltration, Nat.cast_one, le_exp_neg_one_iff_lt_one]
  have hcoe : (((u : integers (F := F)) - 1 : integers (F := F)) : F)
      = ((u : integers (F := F)) : F) - 1 := by push_cast; ring
  rw [← hcoe, ← residue_eq_zero_iff_valued_lt_one ((u : integers (F := F)) - 1), map_sub,
    map_one, sub_eq_zero]
  exact ⟨fun h ↦ congrArg Units.val h, fun h ↦ Units.ext h⟩

/-- **`[𝒪^× : U^(1)] = #k^× = q - 1`.**  Contrast `LocalCFT.relIndex_unitFiltration_succ`:
every higher step has index `q`. -/
theorem index_unitFiltration_one :
    (unitFiltration (F := F) 1).index = Nat.card (ResidueField (integers (F := F))) - 1 := by
  rw [← ker_residueUnitsHom, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 residueUnitsHom_surjective,
    Nat.card_congr (Subgroup.topEquiv (G := (ResidueField (integers (F := F)))ˣ)).toEquiv]
  exact Nat.card_units _

/-! ## Finiteness of the index in `𝒪^×` -/

/-- **Every step of the unit filtration has finite index in `𝒪^×`**, provided the residue field
is finite. -/
theorem finite_quotient_unitFiltration (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ))
    [Finite (ResidueField (integers (F := F)))] (k : ℕ) :
    Finite ((integers (F := F))ˣ ⧸ unitFiltration (F := F) k) := by
  haveI := finite_quotient_unitFiltration_one (F := F)
  have h1 : (unitFiltration (F := F) 1).index ≠ 0 := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos.ne'
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [unitFiltration_zero]
    have htop : (⊤ : Subgroup (integers (F := F))ˣ).index = 1 := Subgroup.index_top
    rw [Subgroup.index_eq_card] at htop
    exact Nat.finite_of_card_ne_zero (by omega)
  · have hrel : (unitFiltration (F := F) k).relIndex (unitFiltration (F := F) 1)
        = Nat.card (ResidueField (integers (F := F))) ^ (k - 1) := by
      have := relIndex_unitFiltration hπ (le_refl 1) (k - 1)
      rwa [show 1 + (k - 1) = k by omega] at this
    have hmul := Subgroup.relIndex_mul_index (H := unitFiltration (F := F) k)
      (K := unitFiltration (F := F) 1) (unitFiltration_le hk)
    have hne : (unitFiltration (F := F) k).index ≠ 0 := by
      rw [← hmul, hrel]
      exact Nat.mul_ne_zero (pow_ne_zero _ Nat.card_pos.ne') h1
    rw [Subgroup.index_eq_card] at hne
    exact Nat.finite_of_card_ne_zero hne

end LocalCFT
