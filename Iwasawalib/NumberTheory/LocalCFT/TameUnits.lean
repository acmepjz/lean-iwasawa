/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.CyclicCocycleNorm
public import Iwasawalib.NumberTheory.LocalCFT.LocalUnits
public import Iwasawalib.NumberTheory.LocalCFT.UnitCohomology

@[expose] public section

/-!
# The principal units of a complete valued field, in the tame case

Let `F` be a complete field with a valuation `v : F → ℤᵐ⁰`, `𝒪` its valuation ring, and let a
finite cyclic group `G = ⟨σ⟩` act on `𝒪` by valuation-preserving ring automorphisms.  This
file proves that the Tate cohomology of the group `1 + 𝔪 = U 1` of principal units vanishes as
soon as the residue characteristic is prime to `#G`.

Nothing here needs a `G`-fixed uniformizer, so — unlike
`Iwasawalib/NumberTheory/LocalCFT/UnitCohomology.lean` — it applies at *ramified* places.
What it does need is a natural number `p` with `v p < 1` (the residue characteristic) which is
coprime to `#G`.  The two inputs are:

* `LocalCFT.unitFiltration_pow_mem_succ`: `U nᵖ ⊆ U (n+1)` for `n ≥ 1`, i.e. the graded pieces
  of the principal unit filtration are killed by `p`.  This is `(1+x)^p = 1 + p x + O(x²)`.
* the graded pieces are therefore killed by `p`, while Tate cohomology is killed by `#G`; a
  Bézout relation `a·#G + b·p = 1` then trivialises every class *explicitly*, with no appeal
  to a `p`-adic logarithm.

The wild case `p ∣ #G` is **not** covered.  The classical proof that `h(𝒪ˣ) = 1` in general
goes through the `p`-adic logarithm `1 + 𝔪^m ≅ 𝔪^m`, and Mathlib has no nonarchimedean
`exp`/`log` for a complete discretely valued field of mixed characteristic.
`Iwasawalib/NumberTheory/LocalCFT/UnitFiltrationExp.lean` now constructs an exponential,
`LocalCFT.IsExpData.expUnit`, which for `k` beyond the absolute ramification index maps
`{x | v x ≤ exp (-k)}` onto `U k`, turning sums into products and with trivial kernel.  It is
not yet shown to commute with the action of `G`, and no Herbrand quotient computation uses it,
so the wild case remains open.

## Main statements

* `LocalCFT.unitFiltration_pow_mem_succ`: `u ∈ U n`, `n ≥ 1` implies `u ^ p ∈ U (n+1)`.
* `LocalCFT.exists_mulNorm_mem_succ_tame`, `LocalCFT.exists_smul_div_mem_succ_tame`: the two
  graded vanishing statements, in the representative form that
  `Iwasawalib/GroupCohomology/CyclicLimit.lean` consumes.
-/

noncomputable section

open Finset WithZero CyclicCocycle

namespace LocalCFT

variable {F : Type*} [Field F] [hv : Valued F ℤᵐ⁰]

/-! ## The graded pieces are killed by the residue characteristic -/

/-- **`(1 + x)^p ≡ 1 + p x` to second order.**  For `u` in the `n`-th step of the unit
filtration with `n ≥ 1`, and `p` a natural number of valuation `< 1`, the `p`-th power of `u`
lies in the `(n+1)`-st step: the binomial expansion has linear term `p (u - 1)`, of valuation
at most `exp (-1) · exp (-n)`, and all higher terms have valuation at most `exp (-n)²`. -/
theorem unitFiltration_pow_mem_succ {p n : ℕ} (hn : 1 ≤ n)
    (hp : Valued.v ((p : F)) ≤ exp (-1 : ℤ)) {u : (integers (F := F))ˣ}
    (hu : u ∈ unitFiltration n) : u ^ p ∈ unitFiltration (n + 1) := by
  set x : F := ((u : integers (F := F)) : F) - 1 with hxdef
  have hx : Valued.v x ≤ exp (-(n : ℤ)) := hu
  have hone : ((u : integers (F := F)) : F) = 1 + x := by rw [hxdef]; ring
  have hpow : (((u ^ p : (integers (F := F))ˣ) : integers (F := F)) : F) = (1 + x) ^ p := by
    push_cast
    rw [hone]
  have hexp := prod_one_add_sub_le (F := F) (Finset.range p) (fun _ ↦ x)
    (exp_neg_natCast_le_one n) (fun _ _ ↦ hx)
  rw [Finset.prod_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hexp
  rw [mem_unitFiltration, hpow]
  have hsplit : (1 + x) ^ p - 1 = ((1 + x) ^ p - 1 - (p : F) * x) + (p : F) * x := by ring
  rw [hsplit]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
  · exact le_trans hexp (exp_neg_sq_le hn)
  · rw [map_mul]
    refine le_trans (mul_le_mul' hp hx) ?_
    rw [mul_comm, exp_neg_mul_exp_neg_one]

/-! ## The two graded vanishing statements -/

section Tame

variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G (integers (F := F))]

attribute [local instance] Units.mulDistribMulActionRight

variable (hG : ∀ (g : G) (a : integers (F := F)),
    (Valued.v ((g • a : integers (F := F)) : F) : ℤᵐ⁰)
      = Valued.v ((a : integers (F := F)) : F))
  {σ : G} (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)

/-- The norm is a group homomorphism, so it commutes with integer powers. -/
theorem mulNorm_zpow (u : (integers (F := F))ˣ) (a : ℤ) :
    mulNorm (G := G) (u ^ a) = (mulNorm (G := G) u) ^ a :=
  map_zpow (MonoidHom.mk' (mulNorm (G := G)) CyclicLimit.mulNorm_mul) u a

include hgen

/-- The norm of a `σ`-invariant element is its `#G`-th power. -/
theorem mulNorm_eq_pow_card {u : (integers (F := F))ˣ} (hfix : σ • u = u) :
    mulNorm (G := G) u = u ^ (Nat.card G) := by
  have hall : ∀ g : G, g • u = u := by
    have hpow : ∀ k : ℕ, (σ ^ k) • u = u := by
      intro k
      induction k with
      | zero => rw [pow_zero, one_smul]
      | succ k ih => rw [pow_succ, mul_smul, hfix, ih]
    intro g
    obtain ⟨k, rfl⟩ := CyclicCocycle.exists_pow_eq hgen g
    exact hpow k
  rw [mulNorm_def, Finset.prod_congr rfl (fun g _ ↦ hall g), Finset.prod_const,
    Finset.card_univ, Nat.card_eq_fintype_card]

include hG

/-- **`Ĥ⁰` of the graded piece vanishes in the tame case.**  A `σ`-invariant `u ∈ U n` differs
from the norm of `u ^ a` by `u ^ (b p)`, which lies in `U (n+1)`. -/
theorem exists_mulNorm_mem_succ_tame {p n : ℕ} (hn : 1 ≤ n)
    (hp : Valued.v ((p : F)) ≤ exp (-1 : ℤ)) {a b : ℤ} (hab : a * (Nat.card G) + b * p = 1)
    {u : (integers (F := F))ˣ} (hu : u ∈ unitFiltration n) (hfix : σ • u = u) :
    ∃ z ∈ unitFiltration (F := F) n,
      u / mulNorm (G := G) z ∈ unitFiltration (F := F) (n + 1) := by
  refine ⟨u ^ a, Subgroup.zpow_mem _ hu a, ?_⟩
  have key : u / u ^ ((Nat.card G : ℤ) * a) = (u ^ p) ^ b := by
    rw [show u / u ^ ((Nat.card G : ℤ) * a) = u ^ ((1 : ℤ) - (Nat.card G : ℤ) * a) by
      rw [zpow_sub, zpow_one, div_eq_mul_inv],
      show (1 : ℤ) - (Nat.card G : ℤ) * a = (p : ℤ) * b by linarith [hab],
      zpow_mul, zpow_natCast]
  rw [mulNorm_zpow, mulNorm_eq_pow_card hgen hfix, ← zpow_natCast u (Nat.card G), ← zpow_mul,
    key]
  exact Subgroup.zpow_mem _ (unitFiltration_pow_mem_succ hn hp hu) b

/-- **`Ĥ¹` of the graded piece vanishes in the tame case.**  For `u ∈ U n` of norm one the
partial products of the `σ`-orbit of `u` assemble into `W ∈ U n` with `σ • W / W = u ^ #G`; the
Bézout relation then reduces `u` to `u ^ (b p) ∈ U (n+1)`. -/
theorem exists_smul_div_mem_succ_tame {p n : ℕ} (hn : 1 ≤ n)
    (hp : Valued.v ((p : F)) ≤ exp (-1 : ℤ)) {a b : ℤ} (hab : a * (Nat.card G) + b * p = 1)
    {u : (integers (F := F))ˣ} (hu : u ∈ unitFiltration n)
    (hnorm : mulNorm (G := G) u = 1) :
    ∃ z ∈ unitFiltration (F := F) n,
      u * (σ • z / z) ∈ unitFiltration (F := F) (n + 1) := by
  set w : ℕ → (integers (F := F))ˣ := fun i ↦ ∏ j ∈ range i, (σ ^ j) • u with hwdef
  have hsmul_mem : ∀ (g : G) {y : (integers (F := F))ˣ},
      y ∈ unitFiltration (F := F) n → g • y ∈ unitFiltration (F := F) n :=
    fun g _ hy ↦ unitFiltration_smul_mem hG n g hy
  have hwmem : ∀ i, w i ∈ unitFiltration (F := F) n :=
    fun i ↦ Subgroup.prod_mem _ fun j _ ↦ hsmul_mem _ hu
  have hwtel : ∀ i : ℕ, σ • w i / w i = (σ ^ i) • u / u := by
    intro i
    induction i with
    | zero => rw [hwdef]; simp
    | succ i ih =>
      have hstep : w (i + 1) = w i * (σ ^ i) • u := by
        rw [hwdef]; exact Finset.prod_range_succ _ i
      have hs : σ • ((σ ^ i) • u) = (σ ^ (i + 1)) • u := by rw [smul_smul, ← pow_succ']
      rw [hstep, smul_mul', hs,
        show σ • w i * (σ ^ (i + 1)) • u / (w i * (σ ^ i) • u)
            = (σ • w i / w i) * ((σ ^ (i + 1)) • u / (σ ^ i) • u) by
          simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc], ih]
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
  set W : (integers (F := F))ˣ := (∏ i ∈ range (Nat.card G), w i)⁻¹ with hWdef
  have hWmem : W ∈ unitFiltration (F := F) n :=
    Subgroup.inv_mem _ (Subgroup.prod_mem _ fun i _ ↦ hwmem i)
  have hP : σ • (∏ i ∈ range (Nat.card G), w i) / (∏ i ∈ range (Nat.card G), w i)
      = (u ^ (Nat.card G))⁻¹ := by
    rw [smul_prod', ← Finset.prod_div_distrib,
      Finset.prod_congr rfl (fun i _ ↦ hwtel i), Finset.prod_div_distrib,
      ← mulNorm_eq_prod_range hgen u, hnorm, Finset.prod_const, Finset.card_range, one_div]
  have hWtel : σ • W / W = u ^ (Nat.card G) := by
    rw [show σ • W / W
        = (σ • (∏ i ∈ range (Nat.card G), w i) / (∏ i ∈ range (Nat.card G), w i))⁻¹ by
      rw [hWdef, smul_inv']
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm], hP, inv_inv]
  refine ⟨W ^ (-a), Subgroup.zpow_mem _ hWmem _, ?_⟩
  have hsm : σ • (W ^ (-a)) = (σ • W) ^ (-a) :=
    map_zpow (MulDistribMulAction.toMonoidHom (integers (F := F))ˣ σ) W (-a)
  have hz : σ • (W ^ (-a)) / W ^ (-a) = (u ^ (Nat.card G)) ^ (-a) := by
    rw [hsm, ← div_zpow, hWtel]
  have key : u * ((u ^ (Nat.card G)) ^ (-a)) = (u ^ p) ^ b := by
    rw [show (u ^ (Nat.card G)) ^ (-a) = u ^ ((Nat.card G : ℤ) * (-a)) by
      rw [zpow_mul, zpow_natCast],
      show u * u ^ ((Nat.card G : ℤ) * (-a)) = u ^ ((1 : ℤ) + (Nat.card G : ℤ) * (-a)) by
      rw [zpow_add, zpow_one],
      show (1 : ℤ) + (Nat.card G : ℤ) * (-a) = (p : ℤ) * b by linarith [hab],
      zpow_mul, zpow_natCast]
  rw [hz, key]
  exact Subgroup.zpow_mem _ (unitFiltration_pow_mem_succ hn hp hu) b

end Tame

/-! ## The principal units as a `G`-module -/

section Module

variable (G F)

/-- A group acting on the valuation ring of a valued field by valuation-preserving ring
automorphisms.  This is the hypothesis `hG` of
`Iwasawalib/NumberTheory/LocalCFT/UnitFiltration.lean`, packaged as a class so that the steps
of the unit filtration carry a `G`-action as an instance. -/
class IsIsometricSMul (G : Type*) [Group G] [MulSemiringAction G (integers (F := F))] :
    Prop where
  /-- the action preserves the valuation -/
  valued_smul : ∀ (g : G) (a : integers (F := F)),
    (Valued.v ((g • a : integers (F := F)) : F) : ℤᵐ⁰)
      = Valued.v ((a : integers (F := F)) : F)

variable {G F}

variable {G : Type*} [Group G] [MulSemiringAction G (integers (F := F))]

attribute [local instance] Units.mulDistribMulActionRight

/-- The `G`-action on the `n`-th step of the unit filtration. -/
instance unitFiltrationMulDistribMulAction [IsIsometricSMul F G] (n : ℕ) :
    MulDistribMulAction G (unitFiltration (F := F) n) where
  smul g u := ⟨g • (u : (integers (F := F))ˣ),
    unitFiltration_smul_mem IsIsometricSMul.valued_smul n g u.2⟩
  one_smul u := Subtype.ext (one_smul G (u : (integers (F := F))ˣ))
  mul_smul g g' u := Subtype.ext (mul_smul g g' (u : (integers (F := F))ˣ))
  smul_one g := Subtype.ext (smul_one g)
  smul_mul g u u' := Subtype.ext (smul_mul' g (u : (integers (F := F))ˣ) _)

@[simp] theorem coe_smul_unitFiltration [IsIsometricSMul F G] {n : ℕ} (g : G)
    (u : unitFiltration (F := F) n) :
    ((g • u : unitFiltration (F := F) n) : (integers (F := F))ˣ)
      = g • (u : (integers (F := F))ˣ) := rfl

variable [Fintype G] [IsIsometricSMul F G]

/-- The norm of the subgroup agrees with the norm of the ambient group. -/
theorem coe_mulNorm_unitFiltration {n : ℕ} (u : unitFiltration (F := F) n) :
    ((mulNorm (G := G) u : unitFiltration (F := F) n) : (integers (F := F))ˣ)
      = mulNorm (G := G) (u : (integers (F := F))ˣ) := by
  rw [mulNorm_def, mulNorm_def]
  exact map_prod (unitFiltration (F := F) n).subtype _ _

omit [Fintype G] in
/-- **The unit filtration, shifted.**  The steps `U (m + n)` form a complete filtration of the
group `U n`, for every `n`. -/
theorem isCompleteFiltration_shift [CompleteSpace F] (n : ℕ) :
    CyclicLimit.IsCompleteFiltration (G := G)
      (fun m ↦ (unitFiltration (F := F) (m + n)).subgroupOf (unitFiltration (F := F) n)) where
  top := by
    refine (Subgroup.eq_top_iff' _).2 fun u ↦ ?_
    show (u : (integers (F := F))ˣ) ∈ unitFiltration (0 + n)
    rw [Nat.zero_add]
    exact u.2
  antitone m u hu := unitFiltration_mem_of_le (by omega) hu
  smul_mem m g u hu :=
    unitFiltration_smul_mem IsIsometricSMul.valued_smul (m + n) g hu
  separated u hu := by
    refine Subtype.ext (unitFiltration_separated fun m ↦ ?_)
    exact unitFiltration_mem_of_le (Nat.le_add_right m n) (hu m)
  complete := by
    classical
    intro f hf
    set g : ℕ → (integers (F := F))ˣ :=
      fun j ↦ if j < n then (f 0 : (integers (F := F))ˣ) else (f (j - n)) with hgdef
    have hgge : ∀ j, n ≤ j → g j = (f (j - n) : (integers (F := F))ˣ) := by
      intro j hj
      rw [hgdef]
      simp only [if_neg (Nat.not_lt.2 hj)]
    have hcauchy : ∀ j, g j / g (j + 1) ∈ unitFiltration (F := F) j := by
      intro j
      by_cases hj : n ≤ j
      · rw [hgge j hj, hgge (j + 1) (by omega),
          show j + 1 - n = (j - n) + 1 by omega]
        have := hf (j - n)
        have hmem : ((f (j - n) : (integers (F := F))ˣ)) / (f ((j - n) + 1))
            ∈ unitFiltration (F := F) ((j - n) + n) := this
        rwa [show (j - n) + n = j by omega] at hmem
      · push_neg at hj
        by_cases hj1 : n ≤ j + 1
        · rw [hgdef]
          simp only [if_pos hj, if_neg (Nat.not_lt.2 hj1),
            show j + 1 - n = 0 by omega, div_self']
          exact (unitFiltration (F := F) j).one_mem
        · rw [hgdef]
          simp only [if_pos hj, if_pos (by omega : j + 1 < n), div_self']
          exact (unitFiltration (F := F) j).one_mem
    obtain ⟨y, hy⟩ := (isCompleteFiltration_unitFiltration
      (G := G) IsIsometricSMul.valued_smul).complete g hcauchy
    have hyn : y ∈ unitFiltration (F := F) n := by
      have h1 : y / g n ∈ unitFiltration (F := F) n := hy n
      have h2 : g n ∈ unitFiltration (F := F) n := by
        rw [hgge n le_rfl, Nat.sub_self]
        exact (f 0).2
      simpa using (unitFiltration (F := F) n).mul_mem h1 h2
    refine ⟨⟨y, hyn⟩, fun m ↦ ?_⟩
    show y / (f m : (integers (F := F))ˣ) ∈ unitFiltration (m + n)
    have := hy (m + n)
    rwa [hgge (m + n) (Nat.le_add_left n m), show m + n - n = m by omega] at this

/-! ## Finiteness of `𝒪ˣ / (1 + 𝔪)` -/

/-- **`𝒪ˣ / (1 + 𝔪)` embeds in the multiplicative group of the residue field**, so it is finite
whenever the residue field is.  This is the finite-index input to
`LocalCFT.herbrand_units_eq_one_tame`. -/
theorem finite_quotient_unitFiltration_one
    [Finite (IsLocalRing.ResidueField (integers (F := F)))] :
    Finite ((integers (F := F))ˣ ⧸ unitFiltration (F := F) 1) := by
  classical
  set ρ : (integers (F := F))ˣ →* (IsLocalRing.ResidueField (integers (F := F)))ˣ :=
    Units.map (IsLocalRing.residue (integers (F := F))).toMonoidHom with hρ
  have hcoe : ∀ u : (integers (F := F))ˣ,
      (((u : integers (F := F)) - 1 : integers (F := F)) : F)
        = ((u : integers (F := F)) : F) - 1 := by
    intro u; push_cast; ring
  have hker : ∀ u : (integers (F := F))ˣ, ρ u = 1 ↔ u ∈ unitFiltration (F := F) 1 := by
    intro u
    rw [mem_unitFiltration, Nat.cast_one, le_exp_neg_one_iff_lt_one, ← hcoe u,
      ← residue_eq_zero_iff_valued_lt_one ((u : integers (F := F)) - 1), map_sub, map_one,
      sub_eq_zero]
    exact ⟨fun h ↦ congrArg Units.val h, fun h ↦ Units.ext h⟩
  refine Finite.of_injective
    (fun q : (integers (F := F))ˣ ⧸ unitFiltration (F := F) 1 ↦
      Quotient.liftOn' q (fun u ↦ ρ u) (fun u u' h ↦ ?_)) ?_
  · have h1 : u⁻¹ * u' ∈ unitFiltration (F := F) 1 := (QuotientGroup.leftRel_apply).1 h
    have h2 := (hker _).2 h1
    rw [map_mul, map_inv] at h2
    exact inv_mul_eq_one.1 h2
  · intro q q'
    induction q using QuotientGroup.induction_on with | _ u =>
    induction q' using QuotientGroup.induction_on with | _ u' =>
    intro h
    refine QuotientGroup.eq.2 ((hker _).1 ?_)
    have h3 : ρ u = ρ u' := h
    rw [map_mul, map_inv, h3, inv_mul_cancel]

/-! ## `Ĥ⁰` and `Ĥ¹` of the principal units -/

section Vanishing

variable [CompleteSpace F] {σ : G} (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
  {p : ℕ} (hp : Valued.v ((p : F)) ≤ exp (-1 : ℤ))
  {a b : ℤ} (hab : a * (Nat.card G) + b * p = 1)

include hgen hp hab

/-- **`Ĥ⁰(G, 1 + 𝔪) = 0` in the tame case.**  Successive approximation along the filtration of
`1 + 𝔪` by the `1 + 𝔪ⁿ`, whose graded pieces are handled by
`LocalCFT.exists_mulNorm_mem_succ_tame`. -/
theorem exists_mulNorm_eq_of_smul_eq_tame {u : (integers (F := F))ˣ}
    (hu : u ∈ unitFiltration (F := F) 1) (hfix : σ • u = u) :
    ∃ z ∈ unitFiltration (F := F) 1, mulNorm (G := G) z = u := by
  have hvanish : ∀ (m : ℕ), ∀ x ∈ (unitFiltration (F := F) (m + 1)).subgroupOf
      (unitFiltration (F := F) 1), σ • x = x →
      ∃ z ∈ (unitFiltration (F := F) (m + 1)).subgroupOf (unitFiltration (F := F) 1),
        x / mulNorm (G := G) z ∈ (unitFiltration (F := F) (m + 1 + 1)).subgroupOf
          (unitFiltration (F := F) 1) := by
    intro m x hx hfx
    have hx' : (x : (integers (F := F))ˣ) ∈ unitFiltration (F := F) (m + 1) := hx
    have hfx' : σ • (x : (integers (F := F))ˣ) = (x : (integers (F := F))ˣ) :=
      congrArg (fun t : unitFiltration (F := F) 1 ↦ (t : (integers (F := F))ˣ)) hfx
    obtain ⟨z, hz1, hz2⟩ := exists_mulNorm_mem_succ_tame (G := G)
      IsIsometricSMul.valued_smul hgen (Nat.le_add_left 1 m) hp hab hx' hfx'
    refine ⟨⟨z, unitFiltration_mem_of_le (by omega) hz1⟩, hz1, ?_⟩
    show ((x : (integers (F := F))ˣ)) / ((mulNorm (G := G)
      (⟨z, unitFiltration_mem_of_le (by omega) hz1⟩ : unitFiltration (F := F) 1)
        : unitFiltration (F := F) 1) : (integers (F := F))ˣ)
      ∈ unitFiltration (F := F) (m + 1 + 1)
    rw [coe_mulNorm_unitFiltration]
    exact hz2
  obtain ⟨y, hy⟩ := (isCompleteFiltration_shift (G := G) (F := F) 1).exists_mulNorm_eq_of_smul_eq
    (σ := σ) hvanish (x := (⟨u, hu⟩ : unitFiltration (F := F) 1))
    (Subtype.ext hfix)
  refine ⟨(y : (integers (F := F))ˣ), y.2, ?_⟩
  rw [← coe_mulNorm_unitFiltration]
  exact congrArg (fun t : unitFiltration (F := F) 1 ↦ (t : (integers (F := F))ˣ)) hy

/-- **`Ĥ¹(G, 1 + 𝔪) = 0` in the tame case.** -/
theorem exists_smul_div_of_mulNorm_eq_one_tame {u : (integers (F := F))ˣ}
    (hu : u ∈ unitFiltration (F := F) 1) (hnorm : mulNorm (G := G) u = 1) :
    ∃ z ∈ unitFiltration (F := F) 1, σ • z / z = u := by
  have hvanish : ∀ (m : ℕ), ∀ x ∈ (unitFiltration (F := F) (m + 1)).subgroupOf
      (unitFiltration (F := F) 1), mulNorm (G := G) x = 1 →
      ∃ z ∈ (unitFiltration (F := F) (m + 1)).subgroupOf (unitFiltration (F := F) 1),
        x * (σ • z / z) ∈ (unitFiltration (F := F) (m + 1 + 1)).subgroupOf
          (unitFiltration (F := F) 1) := by
    intro m x hx hnx
    have hx' : (x : (integers (F := F))ˣ) ∈ unitFiltration (F := F) (m + 1) := hx
    have hnx' : mulNorm (G := G) (x : (integers (F := F))ˣ) = 1 := by
      rw [← coe_mulNorm_unitFiltration]
      exact congrArg (fun t : unitFiltration (F := F) 1 ↦ (t : (integers (F := F))ˣ)) hnx
    obtain ⟨z, hz1, hz2⟩ := exists_smul_div_mem_succ_tame (G := G)
      IsIsometricSMul.valued_smul hgen (Nat.le_add_left 1 m) hp hab hx' hnx'
    exact ⟨⟨z, unitFiltration_mem_of_le (by omega) hz1⟩, hz1, hz2⟩
  obtain ⟨y, hy⟩ := (isCompleteFiltration_shift (G := G) (F := F)
      1).exists_smul_div_of_mulNorm_eq_one (σ := σ) hvanish
    (x := (⟨u, hu⟩ : unitFiltration (F := F) 1))
    (by
      refine Subtype.ext ?_
      rw [coe_mulNorm_unitFiltration]
      exact hnorm)
  exact ⟨(y : (integers (F := F))ˣ), y.2,
    congrArg (fun t : unitFiltration (F := F) 1 ↦ (t : (integers (F := F))ˣ)) hy⟩

/-- `Ĥ⁰(G, 1 + 𝔪) = 0`, as a `Subsingleton` statement. -/
theorem subsingleton_tateH0_unitFiltration_one :
    Subsingleton (CyclicTate.TateH0 G (Additive (unitFiltration (F := F) 1)) σ) := by
  rw [CyclicTate.tateH0_subsingleton_iff]
  intro x hx
  obtain ⟨z, hz1, hz2⟩ := exists_mulNorm_eq_of_smul_eq_tame hgen hp hab
    (x.toMul : unitFiltration (F := F) 1).2
    (congrArg (fun t : unitFiltration (F := F) 1 ↦ (t : (integers (F := F))ˣ)) hx)
  refine ⟨Additive.ofMul (⟨z, hz1⟩ : unitFiltration (F := F) 1), ?_⟩
  rw [LocalCFT.normHom_additive]
  exact congrArg Additive.ofMul (Subtype.ext ((coe_mulNorm_unitFiltration _).trans hz2))

/-- `Ĥ¹(G, 1 + 𝔪) = 0`, as a `Subsingleton` statement. -/
theorem subsingleton_tateH1_unitFiltration_one :
    Subsingleton (CyclicTate.TateH1 G (Additive (unitFiltration (F := F) 1)) σ) := by
  rw [CyclicTate.tateH1_subsingleton_iff]
  intro x hx
  rw [LocalCFT.normHom_additive] at hx
  obtain ⟨z, hz1, hz2⟩ := exists_smul_div_of_mulNorm_eq_one_tame hgen hp hab
    (x.toMul : unitFiltration (F := F) 1).2
    ((coe_mulNorm_unitFiltration _).symm.trans
      (congrArg (fun t : unitFiltration (F := F) 1 ↦ (t : (integers (F := F))ˣ))
        (Additive.ofMul.injective hx)))
  exact ⟨Additive.ofMul (⟨z, hz1⟩ : unitFiltration (F := F) 1),
    congrArg Additive.ofMul (Subtype.ext hz2)⟩

/-! ## The Herbrand quotient of the units -/

/-- The inclusion `1 + 𝔪 → 𝒪ˣ`, as an equivariant map of additive `G`-modules. -/
def unitFiltrationOneIncl :
    Additive (unitFiltration (F := F) 1) →+[G] Additive (integers (F := F))ˣ where
  toFun x := Additive.ofMul ((x.toMul : unitFiltration (F := F) 1) : (integers (F := F))ˣ)
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **`h(𝒪ˣ) = 1` in the tame case.**  The principal units have vanishing Tate cohomology, and
they have finite index in `𝒪ˣ` — the quotient is the multiplicative group of the residue
field — so the Herbrand quotient of `𝒪ˣ` is that of `1 + 𝔪`, namely `1`.

No `G`-fixed uniformizer is required, so this applies at a **ramified** place; what is required
is a natural number `p` with `v p < 1` and `a · #G + b · p = 1`, i.e. that the residue
characteristic is prime to `#G`. -/
theorem tate_units_tame
    [Finite ((integers (F := F))ˣ ⧸ unitFiltration (F := F) 1)] :
    Finite (CyclicTate.TateH0 G (Additive (integers (F := F))ˣ) σ)
      ∧ Finite (CyclicTate.TateH1 G (Additive (integers (F := F))ˣ) σ)
      ∧ CyclicTate.herbrand G (Additive (integers (F := F))ˣ) σ = 1 := by
  haveI := subsingleton_tateH0_unitFiltration_one (G := G) hgen hp hab
  haveI := subsingleton_tateH1_unitFiltration_one (G := G) hgen hp hab
  haveI : Finite (CyclicTate.TateH0 G (Additive (unitFiltration (F := F) 1)) σ) :=
    Finite.of_subsingleton
  haveI : Finite (CyclicTate.TateH1 G (Additive (unitFiltration (F := F) 1)) σ) :=
    Finite.of_subsingleton
  set f := unitFiltrationOneIncl (G := G) (F := F) with hf
  haveI : Finite (f.toAddMonoidHom.ker) := by
    haveI : Subsingleton (f.toAddMonoidHom.ker) := by
      refine ⟨fun x y ↦ Subtype.ext (Additive.toMul.injective (Subtype.ext ?_))⟩
      have hx' : (((x : Additive (unitFiltration (F := F) 1)).toMul)
          : (integers (F := F))ˣ) = 1 :=
        Additive.ofMul.injective (x.2 : f (x : Additive (unitFiltration (F := F) 1)) = 0)
      have hy' : (((y : Additive (unitFiltration (F := F) 1)).toMul)
          : (integers (F := F))ˣ) = 1 :=
        Additive.ofMul.injective (y.2 : f (y : Additive (unitFiltration (F := F) 1)) = 0)
      exact hx'.trans hy'.symm
    exact Finite.of_subsingleton
  haveI : Finite (Additive (integers (F := F))ˣ ⧸ f.toAddMonoidHom.range) := by
    refine Finite.of_surjective
      (fun q : (integers (F := F))ˣ ⧸ unitFiltration (F := F) 1 ↦
        Quotient.liftOn' q
          (fun x : (integers (F := F))ˣ ↦
            (QuotientAddGroup.mk (Additive.ofMul x) :
              Additive (integers (F := F))ˣ ⧸ f.toAddMonoidHom.range))
          (fun x y hxy ↦ ?_)) ?_
    · exact QuotientAddGroup.eq.2
        ⟨Additive.ofMul (⟨x⁻¹ * y, (QuotientGroup.leftRel_apply).1 hxy⟩ :
          unitFiltration (F := F) 1), rfl⟩
    · intro z
      obtain ⟨A, rfl⟩ := QuotientAddGroup.mk_surjective (s := f.toAddMonoidHom.range) z
      exact ⟨QuotientGroup.mk (A.toMul), rfl⟩
  have h₁ := CyclicTate.isShortExact_ker_range f
  have h₂ := CyclicTate.isShortExact_stableQuotient G f.toAddMonoidHom.range
  haveI : Finite (CyclicTate.TateH0 G f.toAddMonoidHom.range σ) := h₁.finite_tateH0_right σ
  haveI : Finite (CyclicTate.TateH1 G f.toAddMonoidHom.range σ) := h₁.finite_tateH1_right σ
  haveI : Finite (CyclicTate.TateH0 G (Additive (integers (F := F))ˣ) σ) :=
    h₂.finite_tateH0_mid σ
  haveI : Finite (CyclicTate.TateH1 G (Additive (integers (F := F))ˣ) σ) :=
    h₂.finite_tateH1_mid σ
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [← CyclicTate.herbrand_eq_of_finite_ker_coker f σ]
  exact CyclicTate.herbrand_eq_one_of_subsingleton σ

/-- **`h(𝒪ˣ) = 1` in the tame case.** -/
theorem herbrand_units_eq_one_tame
    [Finite ((integers (F := F))ˣ ⧸ unitFiltration (F := F) 1)] :
    CyclicTate.herbrand G (Additive (integers (F := F))ˣ) σ = 1 :=
  (tate_units_tame hgen hp hab).2.2

/-- `Ĥ⁰(G, 𝒪ˣ)` is finite in the tame case. -/
theorem finite_tateH0_units_tame
    [Finite ((integers (F := F))ˣ ⧸ unitFiltration (F := F) 1)] :
    Finite (CyclicTate.TateH0 G (Additive (integers (F := F))ˣ) σ) :=
  (tate_units_tame hgen hp hab).1

/-- `Ĥ¹(G, 𝒪ˣ)` is finite in the tame case. -/
theorem finite_tateH1_units_tame
    [Finite ((integers (F := F))ˣ ⧸ unitFiltration (F := F) 1)] :
    Finite (CyclicTate.TateH1 G (Additive (integers (F := F))ˣ) σ) :=
  (tate_units_tame hgen hp hab).2.1

end Vanishing

end Module

end LocalCFT
