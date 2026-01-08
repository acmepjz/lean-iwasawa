/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.NumberTheory.Basic
public import Iwasawalib.NumberTheory.Padics.ForMathlib
public import Iwasawalib.NumberTheory.Padics.HasBasis
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Iwasawalib.Topology.Algebra.Group.Basic

@[expose] public section

/-!

# Structure of `ℤₚˣ`

- `PadicInt.torsionfreeUnitsExponent`: the smallest integer `n` such that the subgroup `1 + pⁿℤₚ`
  of `ℤₚˣ` is torsion-free. More explicitly, `n = 2` if `p = 2`, and `n = 1` otherwise.
- `PadicInt.teichmuller`: the Teichmüller map `(ℤ/pⁿℤ)ˣ →* ℤₚˣ` where `n = 2` if `p = 2`, and
  `n = 1` otherwise, which maps `a` to the unique `ϕ(pⁿ)`-th roots of unity
  (`PadicInt.torsionUnits_eq_torsion` shows that it is indeed the unique roots of unity)
  in `ℤₚ` such that it is congruent to `a` modulo `pⁿ`.
- `PadicInt.principalUnits p n`: the subgroup `1 + pⁿℤₚ` of `ℤₚˣ`.
- `PadicInt.torsionfreeUnits`: the subgroup `1 + pⁿℤₚ` of `ℤₚˣ` where `n = 2` if `p = 2`,
  and `n = 1` otherwise.
- `PadicInt.torsionUnits`: the subgroup `(ℤₚˣ)ₜₒᵣ` of torsion elements of `ℤₚˣ`. Note that for
  definitionally equal reason, its actual definition is the image of the Teichmüller map
  (`PadicInt.teichmuller`). `PadicInt.torsionUnits_eq_torsion` shows that it is indeed equal to
  the set of torsion elements of `ℤₚˣ`.
- `PadicInt.unitsContinuousEquivTorsionfreeProdTorsion`:
  the natural continuous group isomorphism `ℤₚˣ ≃ (1 + pⁿℤₚ) × (ℤₚˣ)ₜₒᵣ`,
  where `n = 2` if `p = 2`, and `n = 1` otherwise.
- `PadicInt.torsionfreeZModPowUnits p n`: the subgroup `1 + pᵏℤ` of
  `(ℤ/pⁿ⁺ᵏℤ)ˣ` where `k = 2` if `p = 2`, and `k = 1` otherwise.
- `PadicInt.torsionfreeZModPowUnits.generator p n`: the element `1 + pᵏ`
  in the subgroup `1 + pᵏℤ` of `(ℤ/pⁿ⁺ᵏℤ)ˣ` where `k = 2` if `p = 2`, and `k = 1` otherwise.
- `PadicInt.equivTorsionfreeUnits.toFun`: the map `ℤₚ → ℤₚ` by sending `x` to the limit of
  `(1 + pᵏ) ^ (x mod pⁿ)` as `n → ∞`, where `k = 2` if `p = 2`, and `k = 1` otherwise.
- `PadicInt.equivTorsionfreeUnits`: the continuous group isomorphism `(ℤₚ, +) ≃ (1 + pᵏℤₚ, *)` by
  sending `x` to the limit of `(1 + pᵏ) ^ (x mod pⁿ)` as `n → ∞`, where `k = 2` if `p = 2`, and
  `k = 1` otherwise.

-/

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

namespace PadicInt

/-! ### Teichmüller map -/

/-- The smallest integer `n` such that the subgroup `1 + pⁿℤₚ` of `ℤₚˣ` is torsion-free.
More explicitly, `n = 2` if `p = 2`, and `n = 1` otherwise. -/
def torsionfreeUnitsExponent : ℕ := if p = 2 then 2 else 1

omit [Fact p.Prime] in
theorem torsionfreeUnitsExponent_ne_zero : torsionfreeUnitsExponent p ≠ 0 := by
  rw [torsionfreeUnitsExponent]
  split_ifs <;> decide

theorem two_lt_p_pow_torsionfreeUnitsExponent : 2 < p ^ torsionfreeUnitsExponent p := by
  rw [torsionfreeUnitsExponent]
  split_ifs with hp
  · rw [hp]
    decide
  · rw [pow_one]
    exact Ne.lt_of_le (Ne.symm hp) ‹Fact p.Prime›.out.two_le

theorem even_totient_p_pow_torsionfreeUnitsExponent :
    Even (p ^ torsionfreeUnitsExponent p).totient :=
  Nat.totient_even (two_lt_p_pow_torsionfreeUnitsExponent p)

theorem two_le_totient_p_pow_torsionfreeUnitsExponent :
    2 ≤ (p ^ torsionfreeUnitsExponent p).totient := by
  rw [torsionfreeUnitsExponent]
  split_ifs with hp
  · rw [hp]
    decide
  · rw [pow_one, Nat.totient_prime Fact.out]
    apply Nat.le_sub_one_of_lt
    exact Ne.lt_of_le (Ne.symm hp) ‹Fact p.Prime›.out.two_le

open Polynomial in
theorem existsUnique_pow_eq_one_and_unitsMap_toZModPow_one_eq (x : (ZMod (p ^ 1))ˣ) :
    ∃! y : ℤ_[p]ˣ, y ^ (p - 1) = 1 ∧ Units.map (toZModPow 1).toMonoidHom y = x := by
  obtain ⟨a, rfl⟩ := unitsMap_toZModPow_surjective p 1 x
  have hu : IsUnit (↑(p - 1) : ℤ_[p]) := by
    rw [← isUnit_map_iff toZMod, map_natCast, ZMod.isUnit_iff_coprime,
      ← Nat.coprime_self_sub_left (by simp), Nat.sub_sub_self ‹Fact p.Prime›.out.one_le]
    exact Nat.coprime_one_left p
  have h1 (a : ℤ_[p]ˣ) : ‖eval a.1 (X ^ (p - 1) - 1)‖ < 1 := by
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    have : toZMod a.1 ≠ 0 := (a.map (toZMod (p := p)).toMonoidHom).ne_zero
    rw [norm_lt_one_iff_dvd, ← Ideal.mem_span_singleton, ← maximalIdeal_eq_span_p, ← ker_toZMod]
    simp [ZMod.pow_card_sub_one_eq_one this]
  have h2 (a : ℤ_[p]ˣ) : ‖eval a.1 (derivative (X ^ (p - 1) - 1))‖ = 1 := by
    simp [derivative_X_pow, isUnit_iff.1 hu]
  obtain ⟨z, hz1, hz2, -, hz3⟩ := hensels_lemma (R := ℤ_[p]) (F := X ^ (p - 1) - 1) (a := a.1) <| by
    simpa only [coe_aeval_eq_eval, h2, one_pow] using h1 a
  simp only [coe_aeval_eq_eval] at hz1 hz2 hz3
  simp only [eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] at hz1 hz3
  simp only [h2] at hz2 hz3
  have hp1 : p - 1 ≠ 0 := by
    have := ‹Fact p.Prime›.out.two_le
    omega
  rw [ExistsUnique]
  refine ⟨(IsUnit.of_pow_eq_one hz1 hp1).unit, ⟨?_, ?_⟩, fun y ⟨hy1, hy2⟩ ↦ ?_⟩
  · ext1; simpa
  · ext1
    simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe]
    rwa [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ker_toZModPow, pow_one,
      Ideal.mem_span_singleton, ← norm_lt_one_iff_dvd]
  · replace hy2 := congr($(hy2).1)
    simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe] at hy2
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ker_toZModPow, pow_one,
      Ideal.mem_span_singleton, ← norm_lt_one_iff_dvd] at hy2
    ext1
    exact hz3 y.1 congr($(hy1).1) hy2

theorem existsUnique_pow_eq_one_and_unitsMap_toZModPow_torsionfreeUnitsExponent_eq
    (x : (ZMod (p ^ torsionfreeUnitsExponent p))ˣ) :
    ∃! y : ℤ_[p]ˣ, y ^ (p ^ torsionfreeUnitsExponent p).totient = 1 ∧
      Units.map (toZModPow (torsionfreeUnitsExponent p)).toMonoidHom y = x := by
  have hsq (p : ℕ) [Fact p.Prime] (y : ℤ_[p]ˣ) : y ^ 2 = 1 ↔ y = 1 ∨ y = -1 := by
    refine ⟨fun h ↦ ?_, ?_⟩
    · rcases sq_eq_one_iff.1 congr($(h).1) with hy | hy
      · left; ext1; exact hy
      · right; ext1; exact hy
    rintro (rfl | rfl) <;> simp
  by_cases hp : p = 2
  · dsimp [torsionfreeUnitsExponent] at x ⊢
    subst hp
    dsimp at x ⊢
    simp_rw [show Nat.totient 4 = 2 by decide, ExistsUnique, hsq]
    rcases ZMod.units_eq_one_or_neg_one_of_eq_four rfl x with rfl | rfl
    · use 1, by simp
      rintro _ ⟨rfl | rfl, h⟩
      · rfl
      · rw [Units.map_neg, map_one] at h
        contradiction
    · use -1, by simp
      rintro _ ⟨rfl | rfl, h⟩
      · rw [map_one] at h
        contradiction
      · rfl
  revert x
  convert existsUnique_pow_eq_one_and_unitsMap_toZModPow_one_eq p using 0
  rw [show torsionfreeUnitsExponent p = 1 by rw [torsionfreeUnitsExponent, if_neg hp]]
  simp_rw [pow_one, Nat.totient_prime Fact.out]

/-- The Teichmüller map `(ℤ/pⁿℤ)ˣ →* ℤₚˣ` where `n = 2` if `p = 2`, and `n = 1` otherwise, which
maps `a` to the unique `ϕ(pⁿ)`-th roots of unity
(later we will show that in fact it is the unique roots of unity)
in `ℤₚ` such that it is congruent to `a` modulo `pⁿ`. -/
@[no_expose]
noncomputable def teichmuller : (ZMod (p ^ torsionfreeUnitsExponent p))ˣ →* ℤ_[p]ˣ where
  toFun x :=
    (existsUnique_pow_eq_one_and_unitsMap_toZModPow_torsionfreeUnitsExponent_eq p x).exists.choose
  map_one' := by
    have h := existsUnique_pow_eq_one_and_unitsMap_toZModPow_torsionfreeUnitsExponent_eq p 1
    exact h.unique h.exists.choose_spec (by simp)
  map_mul' x y := by
    have hx := existsUnique_pow_eq_one_and_unitsMap_toZModPow_torsionfreeUnitsExponent_eq p x
    have hy := existsUnique_pow_eq_one_and_unitsMap_toZModPow_torsionfreeUnitsExponent_eq p y
    have hxy := existsUnique_pow_eq_one_and_unitsMap_toZModPow_torsionfreeUnitsExponent_eq p (x * y)
    apply hxy.unique hxy.exists.choose_spec
    rw [mul_pow, map_mul, hx.exists.choose_spec.1, hx.exists.choose_spec.2,
      hy.exists.choose_spec.1, hy.exists.choose_spec.2, one_mul]
    tauto

theorem teichmuller_spec (x : (ZMod (p ^ torsionfreeUnitsExponent p))ˣ) :
    teichmuller p x ^ (p ^ torsionfreeUnitsExponent p).totient = 1 ∧
      Units.map (toZModPow (torsionfreeUnitsExponent p)).toMonoidHom (teichmuller p x) = x :=
  existsUnique_pow_eq_one_and_unitsMap_toZModPow_torsionfreeUnitsExponent_eq p x
    |>.exists.choose_spec

theorem teichmuller_unique {x : (ZMod (p ^ torsionfreeUnitsExponent p))ˣ} {y : ℤ_[p]ˣ}
    (hy1 : y ^ (p ^ torsionfreeUnitsExponent p).totient = 1)
    (hy2 : Units.map (toZModPow (torsionfreeUnitsExponent p)).toMonoidHom y = x) :
    teichmuller p x = y := by
  have h := existsUnique_pow_eq_one_and_unitsMap_toZModPow_torsionfreeUnitsExponent_eq p x
  exact h.unique h.exists.choose_spec ⟨hy1, hy2⟩

theorem teichmuller_unitsMap_toZModPow_apply_eq_self_of_pow_eq_one {x : ℤ_[p]ˣ}
    (hx : x ^ (p ^ torsionfreeUnitsExponent p).totient = 1) :
    teichmuller p (Units.map (toZModPow (torsionfreeUnitsExponent p)).toMonoidHom x) = x :=
  teichmuller_unique p hx rfl

@[simp]
theorem teichmuller_neg (x : (ZMod (p ^ torsionfreeUnitsExponent p))ˣ) :
    teichmuller p (-x) = -teichmuller p x := by
  refine teichmuller_unique p ?_ ?_
  · rw [(even_totient_p_pow_torsionfreeUnitsExponent p).neg_pow, (teichmuller_spec p x).1]
  · simpa using (teichmuller_spec p x).2

theorem teichmuller_injective : Function.Injective (teichmuller p) := fun x y hxy ↦ by
  rw [← (teichmuller_spec p x).2, ← (teichmuller_spec p y).2, hxy]

theorem unitsMap_toZModPow_comp_teichmuller :
    (Units.map (toZModPow (torsionfreeUnitsExponent p)).toMonoidHom).comp (teichmuller p) =
      MonoidHom.id _ := by
  ext1 x
  exact (teichmuller_spec p x).2

theorem leftInverse_unitsMap_toZModPow_teichmuller :
    Function.LeftInverse (Units.map (toZModPow (torsionfreeUnitsExponent p)).toMonoidHom)
      (teichmuller p) :=
  fun x ↦ (teichmuller_spec p x).2

theorem isOpen_ker_unitsMap_toZModPow :
    IsOpen ((Units.map (toZModPow (p := p) n).toMonoidHom).ker : Set ℤ_[p]ˣ) := by
  rw [Units.isInducing_embedProduct.isOpen_iff]
  refine ⟨Metric.closedBall 1 ((1 / p) ^ n) ×ˢ Set.univ, ?_, ?_⟩
  · refine IsOpen.prod (IsUltrametricDist.isOpen_closedBall _ ?_) isOpen_univ
    have := ‹Fact p.Prime›.out.ne_zero
    positivity
  · ext x
    simp only [one_div, inv_pow, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
      Metric.mem_closedBall, Set.mem_univ, and_true, RingHom.toMonoidHom_eq_coe, SetLike.mem_coe]
    rw [MonoidHom.mem_ker, dist_eq_norm, ← zpow_natCast, ← zpow_neg, norm_le_pow_iff_mem_span_pow,
      ← ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
    exact ⟨fun h ↦ by ext1; exact h, fun h ↦ congr($(h).1)⟩

theorem continuous_teichmuller_comp_unitsMap_toZModPow :
    Continuous ((teichmuller p).comp
      (Units.map (toZModPow (torsionfreeUnitsExponent p)).toMonoidHom)) := by
  rw [MonoidHom.continuous_iff]
  rintro s hs1 -
  refine ⟨(Units.map (toZModPow (p := p) (torsionfreeUnitsExponent p)).toMonoidHom).ker,
    one_mem _, isOpen_ker_unitsMap_toZModPow p _, fun x hx ↦ ?_⟩
  simp only [RingHom.toMonoidHom_eq_coe, SetLike.mem_coe, MonoidHom.mem_ker] at hx
  simpa [Set.mem_preimage, hx] using hs1

/-! ### Subgroups of `ℤₚˣ` -/

/-- The subgroup `1 + pⁿℤₚ` of `ℤₚˣ`. -/
noncomputable def principalUnits : Subgroup ℤ_[p]ˣ := (Units.map (toZModPow n).toMonoidHom).ker

theorem index_principalUnits : (principalUnits p n).index = (p ^ n).totient := by
  rw [principalUnits, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _
    (unitsMap_toZModPow_surjective p n)]
  simp

instance finiteIndex_principalUnits : (principalUnits p n).FiniteIndex := by
  refine ⟨fun h ↦ ?_⟩
  simp [index_principalUnits, ‹Fact p.Prime›.out.ne_zero] at h

@[simp]
theorem principalUnits_zero : principalUnits p 0 = ⊤ := by
  simp [← Subgroup.index_eq_one, index_principalUnits]

@[simp]
theorem principalUnits_two_one : principalUnits 2 1 = ⊤ := by
  simp [← Subgroup.index_eq_one, index_principalUnits]

theorem mem_principalUnits_iff_coe_sub_one_mem (x) :
    x ∈ principalUnits p n ↔ (x - 1 : ℤ_[p]) ∈ RingHom.ker (toZModPow n) := by
  rw [principalUnits, MonoidHom.mem_ker, RingHom.mem_ker, map_sub, sub_eq_zero, Units.ext_iff]
  simp

theorem isOpen_principalUnits : IsOpen (principalUnits p n : Set ℤ_[p]ˣ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [Units.isOpenEmbedding_val.isOpen_iff_image_isOpen]
  convert (show Continuous fun x : ℤ_[p] ↦ x - 1 by fun_prop).isOpen_preimage _
    (isOpen_span_p_pow p n)
  ext x
  simp only [Set.mem_image, SetLike.mem_coe, mem_principalUnits_iff_coe_sub_one_mem, ker_toZModPow,
    Set.mem_preimage]
  constructor
  · rintro ⟨y, h, rfl⟩; exact h
  · intro h
    have hu : IsUnit x := by
      rw [← ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero, map_one] at h
      have := NeZero.mk hn
      simp [← isUnit_map_iff (toZModPow n), h]
    use hu.unit
    simp [h]

theorem antitone_principalUnits : Antitone (principalUnits p) :=
    antitone_nat_of_succ_le fun n x ↦ by
  simp_rw [mem_principalUnits_iff_coe_sub_one_mem, ker_toZModPow, Ideal.mem_span_singleton']
  rintro ⟨y, hy⟩
  use y * p
  rw [mul_assoc, ← pow_succ', hy]

theorem units_nhds_one_hasAntitoneBasis_principalUnits :
    (nhds (1 : ℤ_[p]ˣ)).HasAntitoneBasis (fun n ↦ principalUnits p n) where
  toHasBasis := by
    refine ⟨fun s ↦ ⟨fun hs ↦ ?_, ?_⟩⟩
    · obtain ⟨t, h1, h2, h3⟩ := mem_nhds_iff.1 hs
      let t' := (· + 1) ⁻¹' (Units.val '' t)
      rw [Units.isOpenEmbedding_val.isOpen_iff_image_isOpen] at h2
      replace h2 : IsOpen t' :=
        (show Continuous fun x : ℤ_[p] ↦ x + 1 by fun_prop).isOpen_preimage _ h2
      replace h3 : 0 ∈ t' := by simp [t', h3]
      have : t' ∈ nhds 0 := mem_nhds_iff.2 ⟨t', by rfl, h2, h3⟩
      obtain ⟨n, hn⟩ := (nhds_zero_hasAntitoneBasis_span_p_pow p).mem_iff.1 this
      refine ⟨n, trivial, fun x hx ↦ ?_⟩
      rw [SetLike.mem_coe, mem_principalUnits_iff_coe_sub_one_mem, ker_toZModPow] at hx
      replace hx := hn hx
      simp only [Set.mem_preimage, sub_add_cancel, Set.mem_image, t'] at hx
      obtain ⟨y, hy, heq⟩ := hx
      simpa only [Units.ext heq] using h1 hy
    · rintro ⟨n, ⟨-, h⟩⟩
      rw [mem_nhds_iff]
      exact ⟨_, h, isOpen_principalUnits p n, one_mem _⟩
  antitone _ _ h := antitone_principalUnits p h

/-- The subgroup `1 + pⁿℤₚ` of `ℤₚˣ` where `n = 2` if `p = 2`, and `n = 1` otherwise. -/
noncomputable def torsionfreeUnits : Subgroup ℤ_[p]ˣ :=
  principalUnits p (torsionfreeUnitsExponent p)

theorem index_torsionfreeUnits :
    (torsionfreeUnits p).index = (p ^ torsionfreeUnitsExponent p).totient :=
  index_principalUnits ..

instance finiteIndex_torsionfreeUnits : (torsionfreeUnits p).FiniteIndex :=
  finiteIndex_principalUnits ..

/-- The subgroup `(ℤₚˣ)ₜₒᵣ` of torsion elements of `ℤₚˣ`. Note that for definitionally equal reason,
its actual definition is the image of the Teichmüller map. Later we will show that it is
indeed equal to the set of torsion elements of `ℤₚˣ`. -/
noncomputable def torsionUnits : Subgroup ℤ_[p]ˣ := (teichmuller p).range

/-- The natural continuous group isomorphism `ℤₚˣ ≃ (1 + pⁿℤₚ) × (ℤₚˣ)ₜₒᵣ`,
where `n = 2` if `p = 2`, and `n = 1` otherwise. -/
noncomputable def unitsContinuousEquivTorsionfreeProdTorsion :
    ℤ_[p]ˣ ≃ₜ* torsionfreeUnits p × torsionUnits p :=
  MonoidHom.continuousEquivKerProdRangeOfLeftInverse
    (Units.map (toZModPow (torsionfreeUnitsExponent p)).toMonoidHom)
    (teichmuller p)
    (leftInverse_unitsMap_toZModPow_teichmuller p)
    (continuous_teichmuller_comp_unitsMap_toZModPow p)

@[simp]
theorem val_fst_unitsContinuousEquivTorsionfreeProdTorsion_apply (x) :
    (unitsContinuousEquivTorsionfreeProdTorsion p x).1.1 = x * (teichmuller p
      (Units.map (toZModPow (torsionfreeUnitsExponent p)).toMonoidHom x))⁻¹ := rfl

@[simp]
theorem val_snd_unitsContinuousEquivTorsionfreeProdTorsion_apply (x) :
    (unitsContinuousEquivTorsionfreeProdTorsion p x).2.1 = teichmuller p
      (Units.map (toZModPow (torsionfreeUnitsExponent p)).toMonoidHom x) := rfl

@[simp]
theorem unitsContinuousEquivTorsionfreeProdTorsion_symm_apply (x) :
    (unitsContinuousEquivTorsionfreeProdTorsion p).symm x = x.1.1 * x.2.1 := rfl

theorem units_eq_unitsContinuousEquivTorsionfreeProdTorsion_mul (x) :
    x = (unitsContinuousEquivTorsionfreeProdTorsion p x).1.1 *
      (unitsContinuousEquivTorsionfreeProdTorsion p x).2.1 := by
  simp

@[simp]
theorem fst_unitsContinuousEquivTorsionfreeProdTorsion_eq_one_iff (x) :
    (unitsContinuousEquivTorsionfreeProdTorsion p x).1 = 1 ↔ x ∈ torsionUnits p := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · convert (unitsContinuousEquivTorsionfreeProdTorsion p x).2.2
    conv_lhs => rw [units_eq_unitsContinuousEquivTorsionfreeProdTorsion_mul p x]
    simp [h]
  · rw [torsionUnits, MonoidHom.mem_range] at h
    obtain ⟨y, rfl⟩ := h
    ext1
    simp only [val_fst_unitsContinuousEquivTorsionfreeProdTorsion_apply,
      RingHom.toMonoidHom_eq_coe, OneMemClass.coe_one]
    suffices (teichmuller p) y * ((teichmuller p) y)⁻¹ = 1 by
      convert this using 4
      exact (teichmuller_spec p y).2
    simp

@[simp]
theorem snd_unitsContinuousEquivTorsionfreeProdTorsion_eq_one_iff (x) :
    (unitsContinuousEquivTorsionfreeProdTorsion p x).2 = 1 ↔ x ∈ torsionfreeUnits p := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · convert (unitsContinuousEquivTorsionfreeProdTorsion p x).1.2
    conv_lhs => rw [units_eq_unitsContinuousEquivTorsionfreeProdTorsion_mul p x]
    simp [h]
  · ext1
    simp only [val_snd_unitsContinuousEquivTorsionfreeProdTorsion_apply,
      RingHom.toMonoidHom_eq_coe, OneMemClass.coe_one, map_eq_one_iff _ (teichmuller_injective p)]
    exact h

theorem torsionUnits_eq_rootsOfUnity :
    torsionUnits p = rootsOfUnity (p ^ torsionfreeUnitsExponent p).totient _ := by
  ext x
  rw [torsionUnits, mem_rootsOfUnity, MonoidHom.mem_range]
  exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ (teichmuller_spec p y).1,
    fun h ↦ ⟨_, teichmuller_unitsMap_toZModPow_apply_eq_self_of_pow_eq_one p h⟩⟩

theorem torsionUnits_le_torsion : torsionUnits p ≤ CommGroup.torsion _ := fun x ↦ by
  rw [torsionUnits_eq_rootsOfUnity, mem_rootsOfUnity, CommGroup.mem_torsion,
    isOfFinOrder_iff_pow_eq_one]
  intro hx
  have := two_le_totient_p_pow_torsionfreeUnitsExponent p
  exact ⟨_, by positivity, hx⟩

theorem card_torsionUnits :
    Nat.card (torsionUnits p) = (p ^ torsionfreeUnitsExponent p).totient := by
  simpa using Nat.card_range_of_injective (teichmuller_injective p)

instance finite_torsionUnits : Finite (torsionUnits p) := by
  apply Nat.finite_of_card_ne_zero
  simp [card_torsionUnits, ‹Fact p.Prime›.out.ne_zero]

@[simp]
theorem torsionfreeUnits_sup_torsionUnits :
    torsionfreeUnits p ⊔ torsionUnits p = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  simpa using Subgroup.mul_mem_sup (unitsContinuousEquivTorsionfreeProdTorsion p x).1.2
    (unitsContinuousEquivTorsionfreeProdTorsion p x).2.2

@[simp]
theorem disjoint_principalUnits_torsionUnits_iff :
    Disjoint (principalUnits p n) (torsionUnits p) ↔ torsionfreeUnitsExponent p ≤ n := by
  refine ⟨fun h ↦ ?_, fun h ↦ disjoint_iff_inf_le.2 fun x h' ↦ ?_⟩
  · by_contra! hn
    rw [torsionfreeUnitsExponent] at hn
    have : principalUnits p n = ⊤ := by
      split_ifs at hn with hp
      · subst hp
        interval_cases n <;> simp
      · interval_cases n; simp
    rw [this, top_disjoint] at h
    simpa [← card_torsionUnits p, h] using even_totient_p_pow_torsionfreeUnitsExponent p
  · obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h'
    replace h1 := antitone_principalUnits p h h1
    rw [principalUnits, MonoidHom.mem_ker] at h1
    rw [torsionUnits_eq_rootsOfUnity, mem_rootsOfUnity] at h2
    rw [Subgroup.mem_bot, ← teichmuller_unitsMap_toZModPow_apply_eq_self_of_pow_eq_one p h2, h1,
      map_one]

theorem disjoint_torsionfreeUnits_torsionUnits : Disjoint (torsionfreeUnits p) (torsionUnits p) :=
  (disjoint_principalUnits_torsionUnits_iff p _).2 le_rfl

@[simp]
theorem cardinalMk_units_eq_continuum : Cardinal.mk ℤ_[p]ˣ = Cardinal.continuum := by
  refine ((Cardinal.mk_le_of_injective Units.val_injective).trans_eq
    (cardinalMk_eq_continuum p)).antisymm ?_
  have hu (x : ℤ_[p]) : IsUnit (1 + p * x) := by
    refine isUnit_of_map_unit toZMod _ ?_
    simp
  let f (x : ℤ_[p]) := (hu x).unit
  have hf : Function.Injective f := fun x y hxy ↦ by
    simpa [f, ‹Fact p.Prime›.out.ne_zero] using congr($(hxy).1)
  simpa using Cardinal.mk_le_of_injective hf

theorem not_isCyclic_units : ¬IsCyclic ℤ_[p]ˣ := fun _ ↦ by
  have := IsCyclic.cardinalMk_le_aleph0 ℤ_[p]ˣ
  rw [cardinalMk_units_eq_continuum] at this
  exact this.not_gt Cardinal.aleph0_lt_continuum

/-! ### The subgroup `1 + pᵏℤ` of `(ℤ/pⁿ⁺ᵏℤ)ˣ` where `k = 2` if `p = 2`, and `k = 1` otherwise -/

/-- The subgroup `1 + pᵏℤ` of `(ℤ/pⁿ⁺ᵏℤ)ˣ` where `k = 2` if `p = 2`, and `k = 1` otherwise. -/
noncomputable def torsionfreeZModPowUnits :
    Subgroup (ZMod (p ^ (n + torsionfreeUnitsExponent p)))ˣ :=
  ZMod.unitsMap (show p ^ torsionfreeUnitsExponent p ∣ p ^ (n + torsionfreeUnitsExponent p) by
    simp [pow_add]) |>.ker

theorem torsionfreeUnits_eq_comap_torsionfreeZModPowUnits : torsionfreeUnits p =
    (torsionfreeZModPowUnits p n).comap (Units.map (toZModPow _).toMonoidHom) := by
  rw [torsionfreeUnits, principalUnits, torsionfreeZModPowUnits, ← MonoidHom.comap_bot,
    ← MonoidHom.comap_bot, Subgroup.comap_comap, ZMod.unitsMap, ← Units.map_comp]
  congr 2
  ext x
  simp

@[simp]
theorem card_torsionfreeZModPowUnits : Nat.card (torsionfreeZModPowUnits p n) = p ^ n := by
  have hdvd : p ^ torsionfreeUnitsExponent p ∣ p ^ (n + torsionfreeUnitsExponent p) := by
    simp [pow_add]
  let f := ZMod.unitsMap hdvd
  change Nat.card f.ker = _
  have hne : (p ^ torsionfreeUnitsExponent p).totient ≠ 0 := by
    have := two_le_totient_p_pow_torsionfreeUnitsExponent p
    positivity
  rw [← Nat.mul_left_inj hne]
  have h1 := Subgroup.index_ker f
  rw [f.range_eq_top_of_surjective (ZMod.unitsMap_surjective hdvd),
    Nat.card_congr Subgroup.topEquiv.toEquiv] at h1
  have h2 := f.ker.card_mul_index
  simp only [h1, Nat.card_eq_fintype_card (α := (ZMod _)ˣ), ZMod.card_units_eq_totient] at h2
  have : p ∣ p ^ torsionfreeUnitsExponent p := by
    rw [torsionfreeUnitsExponent]
    split_ifs with hp <;> simp [hp]
  rw [h2, pow_add, Nat.totient_pow_mul_of_prime_of_dvd Fact.out this]

/-! ### The element `1 + pᵏ` in `(ℤ/pⁿ⁺ᵏℤ)ˣ` where `k = 2` if `p = 2`, and `k = 1` otherwise -/

theorem isUnit_one_add_pow_torsionfreeUnitsExponent_toZModPow :
    IsUnit (1 + p ^ torsionfreeUnitsExponent p : ZMod (p ^ (n + torsionfreeUnitsExponent p))) := by
  norm_cast
  have h1 := torsionfreeUnitsExponent_ne_zero p
  have h2 : 0 < n + torsionfreeUnitsExponent p := by positivity
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff h2, Nat.coprime_comm,
    ‹Fact p.Prime›.out.coprime_iff_not_dvd, ← ZMod.natCast_eq_zero_iff]
  simp [h1]

theorem one_add_pow_torsionfreeUnitsExponent_toZModPow_mem_torsionfreeZModPowUnits :
    (isUnit_one_add_pow_torsionfreeUnitsExponent_toZModPow p n).unit ∈
      torsionfreeZModPowUnits p n := by
  rw [torsionfreeZModPowUnits, MonoidHom.mem_ker]
  ext1
  rw [ZMod.unitsMap, Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe, Units.val_one]
  norm_cast
  rw [map_natCast]
  simp

@[simp]
theorem orderOf_one_add_pow_torsionfreeUnitsExponent_toZModPow :
    orderOf (1 + p ^ torsionfreeUnitsExponent p : ZMod (p ^ (n + torsionfreeUnitsExponent p))) =
      p ^ n := by
  rcases eq_or_ne p 2 with hp | hp
  · subst hp
    dsimp [torsionfreeUnitsExponent, if_pos trivial]
    convert ZMod.orderOf_five n
    norm_num
  have : torsionfreeUnitsExponent p = 1 := by rw [torsionfreeUnitsExponent, if_neg hp]
  simp_rw [this, pow_one]
  convert ZMod.orderOf_one_add_prime Fact.out hp n

theorem isOfFinOrder_one_add_pow_torsionfreeUnitsExponent_toZModPow : IsOfFinOrder
    (1 + p ^ torsionfreeUnitsExponent p : ZMod (p ^ (n + torsionfreeUnitsExponent p))) := by
  rw [← orderOf_pos_iff, orderOf_one_add_pow_torsionfreeUnitsExponent_toZModPow]
  have := ‹Fact p.Prime›.out.ne_zero
  positivity

/-- The element `1 + pᵏ` in the subgroup `1 + pᵏℤ` of `(ℤ/pⁿ⁺ᵏℤ)ˣ`
where `k = 2` if `p = 2`, and `k = 1` otherwise. -/
noncomputable def torsionfreeZModPowUnits.generator : torsionfreeZModPowUnits p n :=
  ⟨_, one_add_pow_torsionfreeUnitsExponent_toZModPow_mem_torsionfreeZModPowUnits p n⟩

@[simp]
theorem torsionfreeZModPowUnits.coe_generator : (generator p n).1 =
    (isUnit_one_add_pow_torsionfreeUnitsExponent_toZModPow p n).unit := rfl

@[simp]
theorem torsionfreeZModPowUnits.orderOf_generator : orderOf (generator p n) = p ^ n := by
  rw [← orderOf_injective _ (torsionfreeZModPowUnits p n).subtype_injective,
    ← orderOf_injective _ Units.coeHom_injective]
  exact orderOf_one_add_pow_torsionfreeUnitsExponent_toZModPow p n

theorem torsionfreeZModPowUnits.isOfFinOrder_generator : IsOfFinOrder (generator p n) := by
  rw [← orderOf_pos_iff, orderOf_generator]
  have := ‹Fact p.Prime›.out.ne_zero
  positivity

theorem torsionfreeZModPowUnits.zpowers_generator : Subgroup.zpowers (generator p n) = ⊤ := by
  apply Subgroup.eq_top_of_le_card
  rw [card_torsionfreeZModPowUnits, Nat.card_zpowers, orderOf_generator]

instance torsionfreeZModPowUnits.isCyclic : IsCyclic (torsionfreeZModPowUnits p n) := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  exact ⟨_, zpowers_generator p n⟩

theorem torsionfreeZModPowUnits.generator_spec (x : torsionfreeZModPowUnits p n) :
    ∃! i < p ^ n, generator p n ^ i = x := by
  have hx : x ∈ Subgroup.zpowers (generator p n) := by simp [zpowers_generator]
  simp_rw [mem_zpowers_iff_mem_range_orderOf, orderOf_generator, Finset.mem_image,
    Finset.mem_range] at hx
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, hi, ?_⟩
  intro j hj
  simpa only [(isOfFinOrder_generator p n).pow_inj_mod, orderOf_generator,
    Nat.mod_eq_of_lt hi.1, Nat.mod_eq_of_lt hj.1] using hj.2.trans hi.2.symm

/-! ### The isomorphism `(1 + pⁿℤₚ, *) ≃ (ℤₚ, +)` -/

theorem val_toZModPow_eq_appr (x : ℤ_[p]) (i : ℕ) : (toZModPow i x).val = x.appr i := by
  change (x.appr i : ZMod (p ^ i)).val = _
  rw [ZMod.val_natCast_of_lt (appr_lt x i)]

theorem pow_succ_dvd_one_add_pow_pow_pow_pow_sub_one (i : ℕ) :
    (p ^ (i + 1) : ℤ) ∣ ((1 + p ^ torsionfreeUnitsExponent p) ^ n) ^ p ^ i - 1 := by
  nth_rw 3 [← one_pow (p ^ i)]
  apply dvd_sub_pow_of_dvd_sub
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
  simp [zero_pow (torsionfreeUnitsExponent_ne_zero p)]

namespace equivTorsionfreeUnits

theorem toFun_aux (x : ℤ_[p]) (i : ℕ) :
    (p ^ i : ℤ) ∣ (1 + p ^ torsionfreeUnitsExponent p) ^ x.appr (i + 1) -
      (1 + p ^ torsionfreeUnitsExponent p) ^ x.appr i := by
  obtain ⟨n, hn⟩ := dvd_appr_sub_appr x i (i + 1) (by simp)
  replace hn := congr($(hn) + x.appr i)
  rw [Nat.sub_add_cancel (appr_mono x (by simp))] at hn
  rw [hn, pow_add, ← sub_one_mul, mul_comm _ n, pow_mul]
  apply dvd_mul_of_dvd_left
  refine (show (p ^ i : ℤ) ∣ p ^ (i + 1) by simp [pow_succ]).trans ?_
  exact pow_succ_dvd_one_add_pow_pow_pow_pow_sub_one p n i

/-- The map `ℤₚ → ℤₚ` by sending `x` to the limit of `(1 + pᵏ) ^ (x mod pⁿ)` as `n → ∞`,
where `k = 2` if `p = 2`, and `k = 1` otherwise. -/
noncomputable def toFun (x : ℤ_[p]) : ℤ_[p] :=
  .ofIntSeq (fun i ↦ (1 + p ^ torsionfreeUnitsExponent p) ^ x.appr i) <|
    isCauSeq_padicNorm_of_pow_dvd_sub _ _ (toFun_aux p x)

@[simp]
theorem toZModPow_toFun (x : ℤ_[p]) (i : ℕ) :
    toZModPow i (toFun p x) = (1 + p ^ torsionfreeUnitsExponent p) ^ x.appr i := by
  simpa using toZModPow_ofIntSeq_of_pow_dvd_sub
    (fun i ↦ (1 + p ^ torsionfreeUnitsExponent p) ^ (x.appr i)) p (toFun_aux p x) i

@[simp]
theorem toFun_natCast (x : ℕ) : toFun p x = (1 + p ^ torsionfreeUnitsExponent p) ^ x := by
  rw [← ext_of_toZModPow]
  intro n
  simp_rw [← zmod_cast_comp_toZModPow _ _ (show n ≤ n + torsionfreeUnitsExponent p by simp),
    RingHom.comp_apply]
  congr 1
  simp only [toZModPow_toFun, ← val_toZModPow_eq_appr, map_natCast, ZMod.val_natCast, map_pow,
    map_add, map_one]
  refine (pow_eq_pow_mod _ ?_).symm
  simp [← orderOf_dvd_iff_pow_eq_one, pow_add]

@[simp]
theorem toFun_zero : toFun p 0 = 1 := by
  simpa using toFun_natCast p 0

@[simp]
theorem toFun_one : toFun p 1 = 1 + p ^ torsionfreeUnitsExponent p := by
  simpa using toFun_natCast p 1

@[simp]
theorem toFun_add (x y : ℤ_[p]) : toFun p (x + y) = toFun p x * toFun p y := by
  rw [← ext_of_toZModPow]
  intro n
  simp_rw [map_mul, toZModPow_toFun, ← pow_add, ← val_toZModPow_eq_appr, map_add]
  rcases lt_or_ge ((toZModPow n x).val + (toZModPow n y).val) (p ^ n) with h | h
  · rw [ZMod.val_add_of_lt h]
  rw [ZMod.val_add_val_of_le h]
  conv_rhs => rw [pow_add]
  suffices (((1 + p ^ torsionfreeUnitsExponent p) ^ p ^ n : ℤ) : ZMod (p ^ n)) = (1 : ℤ) by
    push_cast at this
    simp [this]
  rw [Eq.comm, ZMod.intCast_eq_intCast_iff_dvd_sub]
  push_cast
  refine (show (p ^ n : ℤ) ∣ p ^ (n + 1) by simp [pow_succ]).trans ?_
  simpa using pow_succ_dvd_one_add_pow_pow_pow_pow_sub_one p 1 n

theorem isUnit_toFun (x : ℤ_[p]) : IsUnit (toFun p x) := by
  apply isUnit_of_map_unit (toZModPow 1)
  rw [toZModPow_toFun, pow_one]
  simp [torsionfreeUnitsExponent_ne_zero p]

theorem toFun_mem_principalUnits_iff (x : ℤ_[p]) :
    (isUnit_toFun p x).unit ∈ principalUnits p (n + torsionfreeUnitsExponent p) ↔
      x ∈ Ideal.span {(p ^ n : ℤ_[p])} := by
  have hle : n ≤ n + torsionfreeUnitsExponent p := by simp
  rw [principalUnits, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, IsUnit.unit_spec,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, toZModPow_toFun, Units.val_one, ← ker_toZModPow,
    RingHom.mem_ker, ← orderOf_dvd_iff_pow_eq_one,
    orderOf_one_add_pow_torsionfreeUnitsExponent_toZModPow, ← Nat.sub_add_cancel (appr_mono x hle),
    ← Nat.dvd_add_iff_right (dvd_appr_sub_appr x _ _ hle), ← ZMod.val_eq_zero,
    val_toZModPow_eq_appr]
  exact ⟨fun h ↦ Nat.eq_zero_of_dvd_of_lt h (appr_lt x n), fun h ↦ by simp [h]⟩

theorem toFun_mem_torsionfreeUnits (x : ℤ_[p]) : (isUnit_toFun p x).unit ∈ torsionfreeUnits p := by
  simpa using toFun_mem_principalUnits_iff p 0 x

theorem toFun_injective : Function.Injective (toFun p) := fun x y H ↦ by
  simp only [← ext_of_toZModPow, toZModPow_toFun] at H ⊢
  intro n
  specialize H (n + torsionfreeUnitsExponent p)
  have ho := orderOf_one_add_pow_torsionfreeUnitsExponent_toZModPow p n
  have hfin : 0 < p ^ n := by
    have : p ≠ 0 := NeZero.out
    positivity
  rw [← ho, orderOf_pos_iff] at hfin
  rw [hfin.pow_eq_pow_iff_modEq, ho] at H
  have happr (x : ℤ_[p]) (n m : ℕ) : x.appr n ≡ x.appr (n + m) [MOD p ^ n] := by
    rw [Nat.modEq_iff_dvd, ← Int.ofNat_sub (appr_mono x (by simp))]
    norm_cast
    exact x.dvd_appr_sub_appr _ _ (by simp)
  replace H := (happr x n _).trans H |>.trans (happr y n _).symm
  simp_rw [Nat.modEq_iff_dvd, ← ZMod.intCast_eq_intCast_iff_dvd_sub, Int.cast_natCast] at H
  exact H

theorem toFun_surjective (x : torsionfreeUnits p) : ∃ y, toFun p y = x.1.1 := by
  have h1 (n) : Units.map (toZModPow (n + torsionfreeUnitsExponent p)).toMonoidHom x.1 ∈
      torsionfreeZModPowUnits p n := by
    simpa only [torsionfreeUnits_eq_comap_torsionfreeZModPowUnits p n, Subgroup.mem_comap] using x.2
  let x' (n) : torsionfreeZModPowUnits p n := ⟨_, h1 n⟩
  have h2 (n) := (torsionfreeZModPowUnits.generator_spec p n (x' n)).exists
  choose s hs using h2
  have h4' (n) : (1 + p ^ torsionfreeUnitsExponent p) ^ s n =
      toZModPow (n + torsionfreeUnitsExponent p) x.1.1 := by
    simpa using congr($((hs n).2).1.1)
  have h4 (n) : (1 + p ^ torsionfreeUnitsExponent p) ^ s n = toZModPow n x.1.1 := by
    rw [← zmod_cast_comp_toZModPow _ _ (show n ≤ n + torsionfreeUnitsExponent p by simp),
      RingHom.comp_apply, ← h4', map_pow]
    congr 1
    norm_cast
    rw [map_natCast]
  have hy0 (n) : (p ^ n : ℤ) ∣ s (n + 1) - s n := by
    have := h4' n
    rw [← zmod_cast_comp_toZModPow _ _
      (show n + torsionfreeUnitsExponent p ≤ (n + 1) + torsionfreeUnitsExponent p by simp),
      RingHom.comp_apply, ← h4', map_pow] at this
    norm_cast at this
    rw [map_natCast] at this
    push_cast at this
    rw [(isOfFinOrder_one_add_pow_torsionfreeUnitsExponent_toZModPow p n).pow_eq_pow_iff_modEq,
      orderOf_one_add_pow_torsionfreeUnitsExponent_toZModPow, Nat.modEq_iff_dvd] at this
    exact_mod_cast this
  let y : ℤ_[p] := .ofIntSeq (fun n ↦ s n) (isCauSeq_padicNorm_of_pow_dvd_sub _ _ hy0)
  have h3 (n) : toZModPow n y = _ := toZModPow_ofIntSeq_of_pow_dvd_sub (fun n ↦ s n) p hy0 n
  simp only [Int.cast_natCast] at h3
  use y
  rw [← ext_of_toZModPow]
  intro n
  rw [toZModPow_toFun, ← val_toZModPow_eq_appr, h3, ZMod.val_natCast_of_lt (hs n).1, h4]

end equivTorsionfreeUnits

open equivTorsionfreeUnits in
/-- The continuous group isomorphism `(ℤₚ, +) ≃ (1 + pᵏℤₚ, *)` by sending `x` to the limit of
`(1 + pᵏ) ^ (x mod pⁿ)` as `n → ∞`, where `k = 2` if `p = 2`, and `k = 1` otherwise. -/
noncomputable def equivTorsionfreeUnits : Multiplicative ℤ_[p] ≃ₜ* torsionfreeUnits p :=
  letI f : Multiplicative ℤ_[p] → torsionfreeUnits p :=
    fun x ↦ ⟨_, toFun_mem_torsionfreeUnits p x⟩
  letI f0 : Multiplicative ℤ_[p] →* torsionfreeUnits p := {
    toFun := f
    map_one' := by ext : 2; exact toFun_zero p
    map_mul' x y := by ext : 2; exact toFun_add p x y
  }
  letI f1 := Equiv.ofBijective f <| by
    refine ⟨fun x y h ↦ toFun_injective p congr($(h).1.1), fun x ↦ ?_⟩
    obtain ⟨y, hy⟩ := toFun_surjective p x
    use y
    ext : 2; exact hy
  haveI hc : Continuous f := by
    let f0' : Multiplicative ℤ_[p] →* ℤ_[p]ˣ := {
      toFun x := (isUnit_toFun p x).unit
      map_one' := by ext1; exact toFun_zero p
      map_mul' x y := by ext1; exact toFun_add p x y
    }
    suffices Continuous f0' by
      refine ⟨fun s hs ↦ ?_⟩
      convert this.isOpen_preimage _ (hs.trans (isOpen_principalUnits p _))
      rw [show f0' = Subtype.val ∘ f from rfl, Set.preimage_comp]
      exact congr(f ⁻¹' $((s.preimage_image_eq Subtype.val_injective).symm))
    refine f0'.continuous_iff.2 fun s hs1 ho1 ↦ ?_
    have : s ∈ nhds 1 := mem_nhds_iff.2 ⟨s, by rfl, ho1, hs1⟩
    obtain ⟨n, hn⟩ := (units_nhds_one_hasAntitoneBasis_principalUnits p).mem_iff.1 this
    refine ⟨(Ideal.span {(p ^ n : ℤ_[p])} : Set ℤ_[p]), zero_mem _, isOpen_span_p_pow p n, ?_⟩
    rintro (x : ℤ_[p]) (hx : x ∈ Ideal.span {(p ^ n : ℤ_[p])})
    rw [← toFun_mem_principalUnits_iff] at hx
    rw [Set.mem_preimage]
    exact hn (antitone_principalUnits p (show n ≤ n + torsionfreeUnitsExponent p by simp) hx)
  letI f2 := hc.homeoOfEquivCompactToT2 (f := f1)
  { f1, f0, f2 with }

@[simp]
theorem coe_equivTorsionfreeUnits_apply (x : ℤ_[p]) :
    (equivTorsionfreeUnits p x).1.1 = equivTorsionfreeUnits.toFun p x := rfl

/-! ### Further results of `torsionUnits` -/

theorem torsionUnits_eq_torsion : torsionUnits p = CommGroup.torsion _ := by
  refine (torsionUnits_le_torsion p).antisymm fun x hx ↦ ?_
  suffices ∀ (x : ℤ_[p]ˣ) (hx : x ∈ CommGroup.torsion _) (h : x ∈ torsionfreeUnits p), x = 1 by
    have h1 : (unitsContinuousEquivTorsionfreeProdTorsion p x).1.1 ∈ CommGroup.torsion _ := by
      rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one] at hx ⊢
      obtain ⟨n, h1, h2⟩ := hx
      exact ⟨n, h1, by simp [mul_pow, ← map_pow, h2]⟩
    have := this _ h1 (unitsContinuousEquivTorsionfreeProdTorsion p x).1.2
    simp only [val_fst_unitsContinuousEquivTorsionfreeProdTorsion_apply,
      RingHom.toMonoidHom_eq_coe, mul_eq_one_iff_eq_inv, inv_inv] at this
    rw [torsionUnits, MonoidHom.mem_range]
    exact ⟨_, this.symm⟩
  intro x hx h
  let x' : torsionfreeUnits p := ⟨x, h⟩
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one] at hx
  obtain ⟨n, h1, h2⟩ := hx
  have h2' : x' ^ n = 1 := by ext1; exact h2
  apply_fun (equivTorsionfreeUnits p).symm at h2'
  rw [map_pow, map_one] at h2'
  let y : ℤ_[p] := (equivTorsionfreeUnits p).symm x'
  change n • y = 0 at h2'
  simp only [nsmul_eq_mul, mul_eq_zero, Nat.cast_eq_zero, h1.ne', false_or] at h2'
  change (equivTorsionfreeUnits p).symm x' = 1 at h2'
  apply_fun equivTorsionfreeUnits p at h2'
  simp only [ContinuousMulEquiv.apply_symm_apply, map_one] at h2'
  exact congr($(h2').1)

theorem hasEnoughRootsOfUnity_iff :
    HasEnoughRootsOfUnity ℤ_[p] n ↔ n ∣ (p ^ torsionfreeUnitsExponent p).totient := by
  constructor
  · rintro ⟨⟨r, hr⟩, hcyc⟩
    have : NeZero n := .mk <| by
      rintro rfl
      rw [rootsOfUnity_zero, Subgroup.topEquiv.isCyclic] at hcyc
      exact not_isCyclic_units p hcyc
    have h1 := Fintype.card_eq_nat_card ▸ hr.card_rootsOfUnity
    have h2 : rootsOfUnity n ℤ_[p] ≤ torsionUnits p := by
      rw [torsionUnits_eq_torsion]
      intro x hx
      rw [mem_rootsOfUnity] at hx
      rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨n, Nat.pos_of_ne_zero NeZero.out, hx⟩
    simpa only [h1, card_torsionUnits] using Subgroup.card_dvd_of_le h2
  · intro h
    have : NeZero (p ^ torsionfreeUnitsExponent p).totient := .mk <| by
      have := two_le_totient_p_pow_torsionfreeUnitsExponent p
      positivity
    refine @HasEnoughRootsOfUnity.of_dvd _ _ _ _ _ h ⟨?_, inferInstance⟩
    have hcard := card_torsionUnits p
    rw [torsionUnits_eq_rootsOfUnity] at hcard
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard
      (α := rootsOfUnity (p ^ torsionfreeUnitsExponent p).totient ℤ_[p])
    rw [hcard] at hg
    refine ⟨g.1, congr($(g.2).1), fun d hd ↦ ?_⟩
    rw [← hg, orderOf_dvd_iff_pow_eq_one]
    ext : 2; exact hd

instance hasEnoughRootsOfUnity_sub_one : HasEnoughRootsOfUnity ℤ_[p] (p - 1) := by
  rw [hasEnoughRootsOfUnity_iff, torsionfreeUnitsExponent]
  split_ifs <;> simp only [Nat.totient_prime_pow_succ ‹Fact p.Prime›.out, Nat.dvd_mul_left]

/-! ### Closed subgroups of `ℤₚˣ` -/

/-- A closed subgroup of `ℤₚˣ` is either finite or is of finite index. -/
theorem finite_or_finiteIndex_of_subgroup_units_of_isClosed
    (G : Subgroup ℤ_[p]ˣ) (hG : IsClosed (G : Set ℤ_[p]ˣ)) :
    (G : Set ℤ_[p]ˣ).Finite ∧ G ≤ torsionUnits p ∨ G.FiniteIndex ∧ IsOpen (G : Set ℤ_[p]ˣ) := by
  rcases (G : Set ℤ_[p]ˣ).finite_or_infinite with hf | hf
  · refine .inl ⟨‹_›, fun g hg ↦ ?_⟩
    rw [torsionUnits_eq_torsion, CommGroup.mem_torsion, ← finite_zpowers]
    exact hf.subset (Subgroup.zpowers_le_of_mem hg)
  suffices G.FiniteIndex from .inr ⟨this, G.isOpen_of_isClosed_of_finiteIndex hG⟩
  let G' := G.subgroupOf (torsionfreeUnits p)
  suffices G'.index ≠ 0 by
    simp_rw [G'] at this
    rw [← Subgroup.relIndex] at this
    refine @Subgroup.finiteIndex_of_le _ _ (G ⊓ torsionfreeUnits p) G ?_ inf_le_left
    constructor
    rw [← Subgroup.relIndex_mul_index inf_le_right, Subgroup.inf_relIndex_right, mul_ne_zero_iff]
    exact ⟨this, Subgroup.FiniteIndex.index_ne_zero⟩
  replace hf : (G' : Set (torsionfreeUnits p)).Infinite := by
    contrapose! hf
    suffices Nat.card G ≠ 0 from Nat.finite_of_card_ne_zero this
    replace hf : (Subgroup.map (torsionfreeUnits p).subtype G' : Set ℤ_[p]ˣ).Finite :=
      hf.image (torsionfreeUnits p).subtype
    simp_rw [G', Subgroup.subgroupOf_map_subtype] at hf
    have h := Subgroup.relIndex_inf_mul_relIndex ⊥ (torsionfreeUnits p) G
    simp_rw [bot_inf_eq, Subgroup.relIndex_bot_left] at h
    rw [← h, inf_comm, mul_ne_zero_iff]
    exact ⟨Nat.card_ne_zero.2 ⟨inferInstance, hf⟩,
      ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero
        (Subgroup.relIndex_dvd_index_of_normal (torsionfreeUnits p) G)⟩
  replace hG : IsClosed (G' : Set (torsionfreeUnits p)) :=
    hG.preimage (f := (torsionfreeUnits p).subtype) continuous_subtype_val
  let G'' := Subgroup.toAddSubgroup' (G'.comap (equivTorsionfreeUnits p).toMonoidHom)
  suffices G''.index ≠ 0 by
    simp_rw [G''] at this
    rwa [← AddSubgroup.index_toSubgroup, OrderIso.apply_symm_apply, Subgroup.index_comap,
      (equivTorsionfreeUnits p).toMonoidHom.range_eq_top_of_surjective
        (equivTorsionfreeUnits p).surjective, Subgroup.relIndex_top_right] at this
  replace hf : (G'' : Set ℤ_[p]).Infinite := by
    change (equivTorsionfreeUnits p ⁻¹' G').Infinite
    exact hf.preimage (by simp [(equivTorsionfreeUnits p).surjective.range_eq])
  replace hG : IsClosed (G'' : Set ℤ_[p]) := hG.preimage (equivTorsionfreeUnits p).continuous
  obtain ⟨I, hI⟩ := exists_eq_ideal_of_addSubgroup_of_isClosed p G'' hG
  rcases eq_or_ne I ⊥ with rfl | hx
  · simp_all
  obtain ⟨n, rfl⟩ := ideal_eq_span_pow_p hx
  suffices G''.index = p ^ n by simp [this, ‹Fact p.Prime›.out.ne_zero]
  rw [AddSubgroup.index, hI]
  change Nat.card (ℤ_[p] ⧸ Ideal.span {(p ^ n : ℤ_[p])}) = p ^ n
  rw [← ker_toZModPow, Nat.card_congr
    (RingHom.quotientKerEquivOfSurjective (toZModPow_surjective p n)).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card]

/-- TODO: go to mathlib -/
@[to_additive]
theorem _root_.CommGroup.torsion_le_comap_torsion {G H : Type*} [CommGroup G] [CommGroup H]
    (f : G →* H) : CommGroup.torsion G ≤ (CommGroup.torsion H).comap f := fun g hg ↦ by
  simp only [Subgroup.mem_comap, CommGroup.mem_torsion] at hg ⊢
  exact f.isOfFinOrder hg

/-- TODO: go to mathlib -/
@[to_additive]
theorem _root_.CommGroup.torsion_eq_comap_torsion_of_finite_ker {G H : Type*} [CommGroup G]
    [CommGroup H] (f : G →* H) [Finite f.ker] :
    CommGroup.torsion G = (CommGroup.torsion H).comap f := by
  refine (CommGroup.torsion_le_comap_torsion f).antisymm fun g hg ↦ ?_
  simp only [Subgroup.mem_comap, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one] at hg ⊢
  obtain ⟨n, hn, hg⟩ := hg
  rw [← map_pow, ← f.mem_ker] at hg
  obtain ⟨m, hm, h⟩ := (isOfFinOrder_of_finite (G := f.ker) ⟨_, hg⟩).exists_pow_eq_one
  exact ⟨n * m, by positivity, by simpa [pow_mul] using congr($h.1)⟩

/-- If there is a continuous group homomorphism from an infinite compact topological group `G`
to `ℤₚˣ` with finite kernel, then `G / Gₜₒᵣ ≃ ℤₚ`. -/
theorem nonempty_continuousMulEquiv_of_continuousMonoidHom_units_of_finite_ker
    (G : Type*) [Infinite G] [CommGroup G] [TopologicalSpace G] [CompactSpace G]
    (f : G →ₜ* ℤ_[p]ˣ) [Finite f.ker] :
    Nonempty (G ⧸ CommGroup.torsion G ≃ₜ* Multiplicative ℤ_[p]) := by
  let f0 := ((equivTorsionfreeUnits p).symm : torsionfreeUnits p →ₜ* Multiplicative ℤ_[p]).comp <|
    (ContinuousMonoidHom.fst _ _).comp
    (unitsContinuousEquivTorsionfreeProdTorsion p : ℤ_[p]ˣ →ₜ* torsionfreeUnits p × torsionUnits p)
  let f1 := f0.comp f
  have hf1ker : f1.ker = (torsionUnits p).comap f := by
    have : f0.ker = torsionUnits p := by ext; simp [f0]
    simpa only [← this] using MonoidHom.comap_ker f0.toMonoidHom f.toMonoidHom
  have : Finite f1.ker := by
    change (f1.ker : Set G).Finite
    rw [hf1ker]
    refine Set.Finite.preimage' (f := f) (s := torsionUnits p) (finite_torsionUnits p) fun x _ ↦ ?_
    by_cases hx : x ∈ Set.range f
    · obtain ⟨y, rfl⟩ := hx
      exact Finite.of_equiv _ (f.fiberEquivKer y).symm
    simp [Set.preimage_singleton_eq_empty.2 hx]
  have h2 : CommGroup.torsion G = f1.ker := by
    rw [hf1ker, torsionUnits_eq_torsion]
    exact CommGroup.torsion_eq_comap_torsion_of_finite_ker f.toMonoidHom
  rw [h2]
  let f2 := QuotientGroup.quotientKerEquivRange f1.toMonoidHom
  suffices Nonempty (f1.range ≃ₜ* Multiplicative ℤ_[p]) by
    obtain ⟨g⟩ := this; refine ⟨ContinuousMulEquiv.trans ?_ g⟩
    let f3 := (show Continuous f2 from
      f1.continuous.rangeFactorization.quotient_lift _).homeoOfEquivCompactToT2
    exact { f2, f3 with }
  have : Infinite f1.range := by
    rename Infinite G => hg
    contrapose! hg
    rw [← f2.finite_iff] at hg
    exact .of_subgroup_quotient f1.ker
  obtain ⟨I, hI⟩ := exists_eq_ideal_of_addSubgroup_of_isClosed p (Subgroup.toAddSubgroup' f1.range)
    (isCompact_range f1.continuous).isClosed
  rcases eq_or_ne I ⊥ with rfl | hI'
  · rw [show f1.range = ⊥ by simpa using hI, ← not_finite_iff_infinite] at this
    exact (this inferInstance).elim
  obtain ⟨i⟩ := IsDedekindDomain.nonempty_continuousLinearEquiv_of_ne_bot hI'
  suffices Nonempty (Subgroup.toAddSubgroup' f1.range ≃ₜ+ ℤ_[p]) by
    obtain ⟨g⟩ := this
    exact ⟨{ g with map_mul' := g.map_add' }⟩
  rw [hI]
  exact show Nonempty (I ≃ₜ+ ℤ_[p]) from ⟨{ i with }⟩

/-- If there is a continuous group embedding from an infinite compact topological group `G`
to `ℤₚˣ`, then `G / Gₜₒᵣ ≃ ℤₚ`. -/
theorem nonempty_continuousMulEquiv_of_continuousMonoidHom_units_of_injective
    (G : Type*) [Infinite G] [CommGroup G] [TopologicalSpace G] [CompactSpace G]
    (f : G →ₜ* ℤ_[p]ˣ) (hf : Function.Injective f) :
    Nonempty (G ⧸ CommGroup.torsion G ≃ₜ* Multiplicative ℤ_[p]) :=
  have : Finite f.ker := by
    rw [f.ker_eq_bot_iff.2 hf]
    infer_instance
  nonempty_continuousMulEquiv_of_continuousMonoidHom_units_of_finite_ker p G f

end PadicInt
