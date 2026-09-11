/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.CyclicLimit
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

/-!
# The unit filtration of a complete discretely valued field

Let `F` be a field carrying a valuation `v : F → ℤᵐ⁰` and let `𝒪 = {x | v x ≤ 1}` be its
valuation ring.  This file introduces the filtration

`𝒪ˣ = U 0 ⊇ U 1 ⊇ U 2 ⊇ ⋯`,   `U n = {u : 𝒪ˣ | v (u - 1) ≤ exp (-n)}`,

the *unit filtration*, which for a discretely valued field is the classical
`𝒪ˣ ⊇ 1 + 𝔪 ⊇ 1 + 𝔪² ⊇ ⋯`.

The point of the file is to verify, for a *complete* `F`, the four hypotheses of
`CyclicLimit.IsCompleteFiltration` — the filtration is decreasing, `G`-stable, separated and
complete — so that the successive-approximation theorems
`CyclicLimit.IsCompleteFiltration.exists_smul_div_of_mulNorm_eq_one` and
`CyclicLimit.IsCompleteFiltration.exists_mulNorm_eq_of_smul_eq` can be applied to `𝒪ˣ`.

## Main definitions

* `LocalCFT.unitFiltration n`: the subgroup `U n` of `𝒪ˣ`.
* `LocalCFT.valuationSubringMulSemiringAction`: a valuation-preserving action of `G` on `F`
  restricts to `𝒪`.

## Main statements

* `LocalCFT.unitFiltration_zero`, `LocalCFT.unitFiltration_antitone`,
  `LocalCFT.unitFiltration_separated`, `LocalCFT.unitFiltration_complete`.
* `LocalCFT.isCompleteFiltration_unitFiltration`: the package, as a
  `CyclicLimit.IsCompleteFiltration`.
-/

noncomputable section

open Filter Topology WithZero

namespace LocalCFT

variable {F : Type*} [Field F] [hv : Valued F ℤᵐ⁰]

/-- The valuation ring `{x : F | v x ≤ 1}` of a valued field. -/
abbrev integers : ValuationSubring F := (Valued.v : Valuation F ℤᵐ⁰).valuationSubring

theorem mem_integer {x : F} : x ∈ integers (F := F) ↔ Valued.v x ≤ 1 := Iff.rfl

/-! ## Units of the valuation ring -/

/-- A unit of the valuation ring has valuation one. -/
theorem valued_coe_units (u : (integers (F := F))ˣ) :
    Valued.v ((u : integers (F := F)) : F) = 1 := by
  have h1 : Valued.v ((u : integers (F := F)) : F) ≤ 1 := u.1.2
  have h2 : Valued.v (((u⁻¹ : (integers (F := F))ˣ) : integers (F := F)) : F) ≤ 1 := u⁻¹.1.2
  have h3 : Valued.v ((u : integers (F := F)) : F) *
      Valued.v (((u⁻¹ : (integers (F := F))ˣ) : integers (F := F)) : F) = 1 := by
    rw [← map_mul]
    have : ((u : integers (F := F)) : F) *
        (((u⁻¹ : (integers (F := F))ˣ) : integers (F := F)) : F) = 1 := by
      have := u.mul_inv
      exact_mod_cast congrArg (fun a : integers (F := F) ↦ (a : F)) this
    rw [this, map_one]
  by_contra hne
  have hlt : Valued.v ((u : integers (F := F)) : F) < 1 := lt_of_le_of_ne h1 hne
  have : Valued.v ((u : integers (F := F)) : F) *
      Valued.v (((u⁻¹ : (integers (F := F))ˣ) : integers (F := F)) : F) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' h2) hlt
  exact absurd h3 this.ne

/-- A unit of the valuation ring is nonzero in `F`. -/
theorem coe_units_ne_zero (u : (integers (F := F))ˣ) : ((u : integers (F := F)) : F) ≠ 0 := by
  intro h
  have := valued_coe_units u
  rw [h, map_zero] at this
  exact zero_ne_one this

/-- The inverse of a unit of the valuation ring is its inverse in `F`. -/
theorem coe_units_inv (u : (integers (F := F))ˣ) :
    (((u⁻¹ : (integers (F := F))ˣ) : integers (F := F)) : F)
      = (((u : integers (F := F)) : F))⁻¹ := by
  have h : (((u⁻¹ : (integers (F := F))ˣ) : integers (F := F)) : F)
      * ((u : integers (F := F)) : F) = 1 := by
    have h2 := u.inv_mul
    exact_mod_cast congrArg (fun z : integers (F := F) ↦ (z : F)) h2
  field_simp at h ⊢
  linear_combination h

/-- The quotient of two units of the valuation ring is their quotient in `F`. -/
theorem coe_units_div (x y : (integers (F := F))ˣ) :
    (((x / y : (integers (F := F))ˣ) : integers (F := F)) : F)
      = ((x : integers (F := F)) : F) / ((y : integers (F := F)) : F) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← coe_units_inv y]
  push_cast
  rfl

/-- An element of valuation one is a unit of the valuation ring. -/
def unitOfValuedEqOne {x : F} (hx : Valued.v x = 1) : (integers (F := F))ˣ where
  val := ⟨x, le_of_eq hx⟩
  inv := ⟨x⁻¹, by
    rw [mem_integer, map_inv₀, hx, inv_one]⟩
  val_inv := by
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    exact Subtype.ext (by simpa using mul_inv_cancel₀ hx0)
  inv_val := by
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    exact Subtype.ext (by simpa using inv_mul_cancel₀ hx0)

@[simp] theorem coe_unitOfValuedEqOne {x : F} (hx : Valued.v x = 1) :
    ((unitOfValuedEqOne hx : integers (F := F)) : F) = x := rfl

/-! ## The filtration -/

/-- The `n`-th step `U n = {u : 𝒪ˣ | v (u - 1) ≤ exp (-n)}` of the unit filtration.  For a
discretely valued field this is the group of principal units `1 + 𝔪ⁿ`. -/
def unitFiltration (n : ℕ) : Subgroup (integers (F := F))ˣ where
  carrier := {u | Valued.v (((u : integers (F := F)) : F) - 1) ≤ exp (-(n : ℤ))}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have hkey : (((a * b : (integers (F := F))ˣ) : integers (F := F)) : F) - 1 =
        ((((a : integers (F := F))) : F) - 1) * (((b : integers (F := F))) : F) +
          ((((b : integers (F := F))) : F) - 1) := by
      push_cast
      ring
    rw [hkey]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ hb)
    rw [map_mul, valued_coe_units, mul_one]
    exact ha
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have hv1 : Valued.v ((a : integers (F := F)) : F) = 1 := valued_coe_units a
    have ha0 : (((a : integers (F := F))) : F) ≠ 0 := by
      intro h; rw [h, map_zero] at hv1; exact zero_ne_one hv1
    have hkey : ((((a⁻¹ : (integers (F := F))ˣ)) : integers (F := F)) : F) - 1 =
        -(((((a : integers (F := F))) : F) - 1) * (((a : integers (F := F))) : F)⁻¹) := by
      have : ((((a⁻¹ : (integers (F := F))ˣ)) : integers (F := F)) : F) =
          (((a : integers (F := F))) : F)⁻¹ := by
        have h := a.inv_mul
        have h' : ((((a⁻¹ : (integers (F := F))ˣ)) : integers (F := F)) : F) *
            (((a : integers (F := F))) : F) = 1 := by
          exact_mod_cast congrArg (fun z : integers (F := F) ↦ (z : F)) h
        field_simp at h' ⊢
        linear_combination h'

      rw [this]
      field_simp
      ring
    rw [hkey, Valuation.map_neg, map_mul, map_inv₀, hv1, inv_one, mul_one]
    exact ha

theorem mem_unitFiltration {n : ℕ} {u : (integers (F := F))ˣ} :
    u ∈ unitFiltration n ↔ Valued.v (((u : integers (F := F)) : F) - 1) ≤ exp (-(n : ℤ)) :=
  Iff.rfl

@[simp] theorem unitFiltration_zero : unitFiltration (F := F) 0 = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun u ↦ ?_
  rw [mem_unitFiltration]
  have h : Valued.v (((u : integers (F := F)) : F) - 1) ≤ 1 :=
    le_trans (Valuation.map_sub _ _ _) (max_le u.1.2 (by simp))
  simpa using h

theorem unitFiltration_antitone (n : ℕ) :
    unitFiltration (F := F) (n + 1) ≤ unitFiltration (F := F) n := by
  intro u hu
  rw [mem_unitFiltration] at hu ⊢
  refine le_trans hu ?_
  simp only [exp_le_exp]
  push_cast
  linarith

theorem unitFiltration_mem_of_le {m n : ℕ} (hmn : m ≤ n) {u : (integers (F := F))ˣ}
    (hu : u ∈ unitFiltration n) : u ∈ unitFiltration m := by
  rw [mem_unitFiltration] at hu ⊢
  refine le_trans hu ?_
  simp only [exp_le_exp]
  exact_mod_cast neg_le_neg (by exact_mod_cast hmn)

/-- **The unit filtration is separated.** -/
theorem unitFiltration_separated {u : (integers (F := F))ˣ}
    (hu : ∀ n, u ∈ unitFiltration n) : u = 1 := by
  have hzero : Valued.v (((u : integers (F := F)) : F) - 1) = 0 := by
    by_contra hne
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (((u : integers (F := F)) : F) - 1) = exp m :=
      ⟨log _, (exp_log hne).symm⟩
    have := hu (m.natAbs + 1)
    rw [mem_unitFiltration, hm, exp_le_exp] at this
    push_cast at this
    have hb : -|m| ≤ m := neg_abs_le m
    omega
  have h0 : (((u : integers (F := F)) : F) - 1) = 0 := by
    simpa using hzero
  refine Units.ext (Subtype.ext ?_)
  simpa using sub_eq_zero.1 h0

/-! ## Stability under a valuation-preserving action -/

section Action

variable {G : Type*} [Monoid G]

/-- A valuation-preserving action of `G` on `F` by ring automorphisms restricts to an action
on the valuation ring. -/
@[instance_reducible] def valuationSubringMulSemiringAction [MulSemiringAction G F]
    (hG : ∀ (g : G) (x : F), Valued.v (g • x) = Valued.v x) :
    MulSemiringAction G (integers (F := F)) where
  smul g a := ⟨g • (a : F), by rw [mem_integer, hG]; exact a.2⟩
  one_smul a := Subtype.ext (one_smul G (a : F))
  mul_smul g h a := Subtype.ext (mul_smul g h (a : F))
  smul_zero g := Subtype.ext (show g • (0 : F) = 0 from smul_zero g)
  smul_add g a b := Subtype.ext
    (show g • ((a : F) + (b : F)) = g • (a : F) + g • (b : F) from smul_add g _ _)
  smul_one g := Subtype.ext (show g • (1 : F) = 1 from smul_one g)
  smul_mul g a b := Subtype.ext
    (show g • ((a : F) * (b : F)) = g • (a : F) * g • (b : F) from smul_mul' g _ _)

variable [MulSemiringAction G (integers (F := F))]

attribute [local instance] Units.mulDistribMulActionRight

/-- **The unit filtration is stable under a valuation-preserving action.** -/
theorem unitFiltration_smul_mem
    (hG : ∀ (g : G) (a : integers (F := F)),
      Valued.v ((g • a : integers (F := F)) : F) = Valued.v ((a : integers (F := F)) : F))
    (n : ℕ) (g : G) {u : (integers (F := F))ˣ} (hu : u ∈ unitFiltration n) :
    g • u ∈ unitFiltration n := by
  rw [mem_unitFiltration] at hu ⊢
  have hcoe : (((g • u : (integers (F := F))ˣ) : integers (F := F)) : F)
      = ((g • (u : integers (F := F)) : integers (F := F)) : F) := rfl
  rw [hcoe]
  have hkey : ((g • (u : integers (F := F)) : integers (F := F)) : F) - 1
      = ((g • ((u : integers (F := F)) - 1) : integers (F := F)) : F) := by
    rw [smul_sub, smul_one]
    push_cast
    ring
  rw [hkey, hG]
  simpa using hu

end Action

/-! ## Closed balls -/

/-- A closed ball around the origin of a valued field is closed. -/
theorem isClosed_valued_le (c : ℤᵐ⁰) : IsClosed {x : F | Valued.v x ≤ c} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
  have hx0 : (Valued.v x : ℤᵐ⁰) ≠ 0 := by
    intro h
    rw [h] at hx
    exact absurd hx (not_lt.2 (zero_le : (0 : ℤᵐ⁰) ≤ c))
  refine Filter.mem_of_superset (Valued.locally_const hx0) fun y hy ↦ ?_
  simp only [Set.mem_ofPred_eq] at hy
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, hy]
  exact hx

/-- A closed ball of a valued field is closed. -/
theorem isClosed_valued_sub_le (a : F) (c : ℤᵐ⁰) : IsClosed {x : F | Valued.v (x - a) ≤ c} :=
  (isClosed_valued_le c).preimage (continuous_id.sub continuous_const)

/-! ## Completeness -/

section Complete

variable [CompleteSpace F]

/-- **The unit filtration is complete.**  A sequence of units whose consecutive quotients
converge to one along the filtration has a limit. -/
theorem unitFiltration_complete (f : ℕ → (integers (F := F))ˣ)
    (hf : ∀ n, f n / f (n + 1) ∈ unitFiltration n) :
    ∃ y : (integers (F := F))ˣ, ∀ n, y / f n ∈ unitFiltration n := by
  set a : ℕ → F := fun n ↦ ((f n : integers (F := F)) : F) with ha
  have hone : ∀ n, Valued.v (a n) = 1 := fun n ↦ valued_coe_units (f n)
  have hne : ∀ n, a n ≠ 0 := by
    intro n h
    have := hone n
    rw [h, map_zero] at this
    exact zero_ne_one this
  -- consecutive terms are close
  have hstep : ∀ n, Valued.v (a n - a (n + 1)) ≤ exp (-(n : ℤ)) := by
    intro n
    have h := hf n
    rw [mem_unitFiltration, coe_units_div] at h
    have hexp : a n / a (n + 1) - 1 = (a n - a (n + 1)) / a (n + 1) := by
      rw [sub_div, div_self (hne (n + 1))]
    rw [show ((f n : integers (F := F)) : F) = a n from rfl,
      show ((f (n + 1) : integers (F := F)) : F) = a (n + 1) from rfl, hexp, map_div₀,
      hone (n + 1), div_one] at h
    exact h
  -- all later terms are close
  have hdist : ∀ n m : ℕ, n ≤ m → Valued.v (a n - a m) ≤ exp (-(n : ℤ)) := by
    intro n m hnm
    induction m with
    | zero => simp_all
    | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hnm) with h | h
      · have h1 := ih (Nat.lt_succ_iff.1 h)
        have h2 : Valued.v (a m - a (m + 1)) ≤ exp (-(n : ℤ)) := by
          refine le_trans (hstep m) ?_
          simp only [exp_le_exp]
          exact_mod_cast neg_le_neg (by exact_mod_cast Nat.lt_succ_iff.1 h)
        have : a n - a (m + 1) = (a n - a m) + (a m - a (m + 1)) := by ring
        rw [this]
        exact le_trans (Valuation.map_add _ _ _) (max_le h1 h2)
      · subst h; simp
  -- the sequence is Cauchy
  have hcauchy : Cauchy (Filter.map a Filter.atTop) := by
    rw [Valued.cauchy_iff]
    refine ⟨Filter.map_neBot, fun γ ↦ ?_⟩
    have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
      MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
    obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = exp k :=
      ⟨log _, (exp_log hγ).symm⟩
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (-(N : ℤ)) < k := ⟨(1 - k).toNat, by omega⟩
    refine ⟨a '' (Set.Ici N), Filter.image_mem_map (Filter.Ici_mem_atTop N), ?_⟩
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [Valuation.restrict_lt_iff_lt_embedding, hk]
    have hpq : Valued.v (a q - a p) ≤ exp (-(N : ℤ)) := by
      have : a q - a p = (a N - a p) - (a N - a q) := by ring
      rw [this]
      exact le_trans (Valuation.map_sub _ _ _) (max_le (hdist N p hp) (hdist N q hq))
    exact lt_of_le_of_lt hpq (exp_lt_exp.2 hN)
  obtain ⟨y₀, hy₀⟩ := CompleteSpace.complete hcauchy
  have htendsto : Filter.Tendsto a Filter.atTop (nhds y₀) := hy₀
  -- the limit is within `exp (-n)` of every term
  have hclose : ∀ n, Valued.v (y₀ - a n) ≤ exp (-(n : ℤ)) := by
    intro n
    refine (isClosed_valued_sub_le (a n) (exp (-(n : ℤ)))).mem_of_tendsto htendsto ?_
    filter_upwards [Filter.Ici_mem_atTop n] with m hm
    show Valued.v (a m - a n) ≤ exp (-(n : ℤ))
    rw [Valuation.map_sub_swap]
    exact hdist n m hm
  -- the limit is a unit
  have hy1 : Valued.v y₀ = 1 := by
    have hlt : exp (-((1 : ℕ) : ℤ)) < (1 : ℤᵐ⁰) := by
      rw [show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm, exp_lt_exp]
      norm_num
    have h1 : Valued.v (y₀ - a 1) < Valued.v (a 1) := by
      rw [hone 1]
      exact lt_of_le_of_lt (hclose 1) hlt
    rw [Valuation.map_eq_of_sub_lt _ h1, hone 1]
  refine ⟨unitOfValuedEqOne hy1, fun n ↦ ?_⟩
  rw [mem_unitFiltration, coe_units_div, coe_unitOfValuedEqOne,
    show ((f n : integers (F := F)) : F) = a n from rfl]
  have hexp : y₀ / a n - 1 = (y₀ - a n) / a n := by
    rw [sub_div, div_self (hne n)]
  rw [hexp, map_div₀, hone n, div_one]
  exact hclose n

end Complete

/-! ## The package -/

section Package

variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G (integers (F := F))]
  [CompleteSpace F]

attribute [local instance] Units.mulDistribMulActionRight

omit [Fintype G] in
/-- **The unit filtration of a complete valued field is a complete filtration** in the sense of
`CyclicLimit.IsCompleteFiltration`: it is decreasing, `G`-stable, separated and complete. -/
theorem isCompleteFiltration_unitFiltration
    (hG : ∀ (g : G) (a : integers (F := F)),
      Valued.v ((g • a : integers (F := F)) : F) = Valued.v ((a : integers (F := F)) : F)) :
    CyclicLimit.IsCompleteFiltration (G := G) (unitFiltration (F := F)) where
  top := unitFiltration_zero
  antitone := unitFiltration_antitone
  smul_mem n g _ hx := unitFiltration_smul_mem hG n g hx
  separated _ hx := unitFiltration_separated hx
  complete := unitFiltration_complete

end Package

end LocalCFT
