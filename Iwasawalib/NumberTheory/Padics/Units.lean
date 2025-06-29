/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.Finite.Basic
import Iwasawalib.NumberTheory.Padics.EquivMvZp
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Iwasawalib.Topology.Algebra.Group.Basic

/-!

# Structure of `ℤₚˣ`

-/

/-! ### Maybe these should be in mathlib -/

namespace MonoidHom

variable {B C : Type*} [CommGroup B] [Group C]
  (f : B →* C) (g : C →* B) (hfg : Function.LeftInverse f g)

/-- If a surjective group homomorphism `f : B →* C` has a section `g : C →* B`, then there is a
natural isomorphism of `B` to `ker(f) × im(g)`. We use `im(g)` instead of `C` since if `B`
has topology, then both of `ker(f)` and `im(g)` will also get topology automatically. -/
@[simps apply symm_apply]
def equivKerProdRangeOfLeftInverse : B ≃* f.ker × g.range where
  toFun b := (⟨b * (g (f b))⁻¹, by simp [hfg (f b)]⟩, ⟨g (f b), by simp⟩)
  invFun x := x.1.1 * x.2.1
  left_inv x := by simp
  right_inv x := by
    ext : 2 <;> (obtain ⟨y, hy⟩ := x.2.2; simp [MonoidHom.mem_ker.1 x.1.2, ← hy, hfg y])
  map_mul' x y := by
    ext : 2
    · simp only [map_mul, mul_inv_rev, Prod.mk_mul_mk, MulMemClass.mk_mul_mk]
      conv_lhs => rw [mul_assoc x y, mul_comm y]
      conv_rhs => rw [mul_comm y, mul_assoc x, ← mul_assoc _ _ y]
      congr 2
      rw [mul_comm]
    · simp

theorem continuous_equivKerProdRangeOfLeftInverse_symm [TopologicalSpace B] [ContinuousMul B] :
    Continuous (equivKerProdRangeOfLeftInverse f g hfg).symm := by
  dsimp [equivKerProdRangeOfLeftInverse]
  fun_prop

variable [TopologicalSpace B] [IsTopologicalGroup B] (hc : Continuous (g ∘ f))
include hc

theorem continuous_equivKerProdRangeOfLeftInverse :
    Continuous (equivKerProdRangeOfLeftInverse f g hfg) := by
  dsimp [equivKerProdRangeOfLeftInverse]
  continuity -- `fun_prop` does not work here, and `continuity` is slow

/-- Continuous version of `equivKerProdRangeOfLeftInverse`. -/
def continuousEquivKerProdRangeOfLeftInverse : B ≃ₜ* f.ker × g.range where
  toMulEquiv := equivKerProdRangeOfLeftInverse f g hfg
  continuous_toFun := continuous_equivKerProdRangeOfLeftInverse f g hfg hc
  continuous_invFun := continuous_equivKerProdRangeOfLeftInverse_symm f g hfg

@[simp]
theorem continuousEquivKerProdRangeOfLeftInverse_apply (x) :
    continuousEquivKerProdRangeOfLeftInverse f g hfg hc x =
      equivKerProdRangeOfLeftInverse f g hfg x := rfl

@[simp]
theorem continuousEquivKerProdRangeOfLeftInverse_symm_apply (x) :
    (continuousEquivKerProdRangeOfLeftInverse f g hfg hc).symm x =
      (equivKerProdRangeOfLeftInverse f g hfg).symm x := rfl

end MonoidHom

variable (p : ℕ) [Fact p.Prime] (n : ℕ) (x : ℤ_[p]ˣ)

namespace PadicInt

instance isLocalHom_toZMod : IsLocalHom (toZMod (p := p)) := by
  refine ⟨fun x hx ↦ ?_⟩
  simpa only [← IsLocalRing.notMem_maximalIdeal, ← ker_toZMod, RingHom.mem_ker] using hx.ne_zero

theorem zmod_cast_comp_toZModPow_eq_toZMod (n : ℕ) (h : n ≠ 0) :
    (ZMod.castHom (dvd_pow_self p h) (ZMod p)).comp (@toZModPow p _ n) = @toZMod p _ := by
  have h1 := congr((ZMod.castHom (show p ∣ p ^ 1 by simp) (ZMod p)).comp
    $(zmod_cast_comp_toZModPow (p := p) 1 n (Nat.one_le_iff_ne_zero.2 h)))
  rw [← RingHom.comp_assoc, ZMod.castHom_comp] at h1
  rw [h1]
  have hb := @ZMod.castHom_bijective (p ^ 1) (ZMod p) _
    (by rw [pow_one]; infer_instance) _ (by simp)
  apply ZMod.ringHom_eq_of_ker_eq
  suffices RingHom.ker (toZModPow (p := p) 1) = RingHom.ker toZMod by
    rw [← this]
    exact RingHom.ker_comp_of_injective _ hb.injective
  rw [ker_toZModPow, ker_toZMod, maximalIdeal_eq_span_p, pow_one]

instance isLocalHom_toZModPow [NeZero n] : IsLocalHom (toZModPow (p := p) n) := by
  have h := isLocalHom_toZMod p
  rw [← zmod_cast_comp_toZModPow_eq_toZMod p n NeZero.out] at h
  exact @isLocalHom_of_comp _ _ _ _ _ _ _ _ h

theorem unitsMap_toZMod_surjective :
    Function.Surjective (Units.map (toZMod (p := p)).toMonoidHom) :=
  IsLocalRing.surjective_units_map_of_local_ringHom _ (toZMod_surjective p) inferInstance

theorem unitsMap_toZModPow_surjective :
    Function.Surjective (Units.map (toZModPow (p := p) n).toMonoidHom) := by
  rcases eq_or_ne n 0 with rfl | h
  · convert Function.surjective_to_subsingleton _
    · infer_instance
    · simp only [Nat.pow_zero]
      infer_instance
  have := NeZero.mk h
  exact IsLocalRing.surjective_units_map_of_local_ringHom _ (toZModPow_surjective p n) inferInstance

/-! ### Some silly results for `ZMod` -/

theorem _root_.ZMod.units_eq_one_of_eq_two
    {q : ℕ} (hq : q = 2) (x : (ZMod q)ˣ) : x = 1 := by
  subst hq
  exact Subsingleton.elim x 1

theorem _root_.ZMod.units_eq_one_or_neg_one_of_eq_three
    {q : ℕ} (hq : q = 3) (x : (ZMod q)ˣ) : x = 1 ∨ x = -1 := by
  subst hq
  fin_cases x <;> decide

theorem _root_.ZMod.units_eq_one_or_neg_one_of_eq_four
    {q : ℕ} (hq : q = 4) (x : (ZMod q)ˣ) : x = 1 ∨ x = -1 := by
  subst hq
  fin_cases x <;> decide

theorem _root_.ZMod.units_eq_one_or_neg_one_of_eq_six
    {q : ℕ} (hq : q = 6) (x : (ZMod q)ˣ) : x = 1 ∨ x = -1 := by
  subst hq
  fin_cases x <;> decide

theorem _root_.ZMod.eq_one_of_eq_two_of_isUnit
    {q : ℕ} (hq : q = 2) (x : ZMod q) (hx : IsUnit x) : x = 1 :=
  congr($(ZMod.units_eq_one_of_eq_two hq hx.unit).1)

theorem _root_.ZMod.eq_one_or_neg_one_of_eq_three_of_isUnit
    {q : ℕ} (hq : q = 3) (x : ZMod q) (hx : IsUnit x) : x = 1 ∨ x = -1 := by
  rcases ZMod.units_eq_one_or_neg_one_of_eq_three hq hx.unit with h | h
  · exact Or.inl congr($(h).1)
  · exact Or.inr congr($(h).1)

theorem _root_.ZMod.eq_one_or_neg_one_of_eq_four_of_isUnit
    {q : ℕ} (hq : q = 4) (x : ZMod q) (hx : IsUnit x) : x = 1 ∨ x = -1 := by
  rcases ZMod.units_eq_one_or_neg_one_of_eq_four hq hx.unit with h | h
  · exact Or.inl congr($(h).1)
  · exact Or.inr congr($(h).1)

theorem _root_.ZMod.eq_one_or_neg_one_of_eq_six_of_isUnit
    {q : ℕ} (hq : q = 6) (x : ZMod q) (hx : IsUnit x) : x = 1 ∨ x = -1 := by
  rcases ZMod.units_eq_one_or_neg_one_of_eq_six hq hx.unit with h | h
  · exact Or.inl congr($(h).1)
  · exact Or.inr congr($(h).1)

/-! ### Teichmüller map -/

/-- The smallest integer `n` such that the subgroup `1 + pⁿℤₚ` of `ℤₚˣ` is torsion-free.
More explicitly, `n = 2` if `p = 2`, and `n = 1` otherwise. -/
def torsionfreeUnitsExponent : ℕ := if p = 2 then 2 else 1

theorem even_totient_p_pow_torsionfreeUnitsExponent :
    Even (p ^ torsionfreeUnitsExponent p).totient := by
  rw [torsionfreeUnitsExponent]
  split_ifs with hp
  · rw [hp]
    decide
  · rw [pow_one, Nat.totient_prime Fact.out]
    exact ‹Fact p.Prime›.out.even_sub_one hp

theorem existsUnique_pow_eq_one_and_unitsMap_toZModPow_one_eq (x : (ZMod (p ^ 1))ˣ) :
    ∃! y : ℤ_[p]ˣ, y ^ (p - 1) = 1 ∧ Units.map (toZModPow 1).toMonoidHom y = x := by
  obtain ⟨a, rfl⟩ := unitsMap_toZModPow_surjective p 1 x
  have hu : IsUnit (↑(p - 1) : ℤ_[p]) := by
    rw [← isUnit_map_iff toZMod, map_natCast, ZMod.isUnit_iff_coprime,
      ← Nat.coprime_self_sub_left (by simp), Nat.sub_sub_self ‹Fact p.Prime›.out.one_le]
    exact Nat.coprime_one_left p
  have h1 (a : ℤ_[p]ˣ) : ‖Polynomial.eval a.1 (Polynomial.X ^ (p - 1) - 1)‖ < 1 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    have : toZMod a.1 ≠ 0 := (a.map (toZMod (p := p)).toMonoidHom).ne_zero
    rw [norm_lt_one_iff_dvd, ← Ideal.mem_span_singleton, ← maximalIdeal_eq_span_p, ← ker_toZMod]
    simp [ZMod.pow_card_sub_one_eq_one this]
  have h2 (a : ℤ_[p]ˣ) :
      ‖Polynomial.eval a.1 (Polynomial.derivative (Polynomial.X ^ (p - 1) - 1))‖ = 1 := by
    simp [Polynomial.derivative_X_pow, isUnit_iff.1 hu]
  obtain ⟨z, hz1, hz2, -, hz3⟩ := hensels_lemma (F := Polynomial.X ^ (p - 1) - 1) (a := a.1) <| by
    simpa only [h2, one_pow] using h1 a
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, sub_eq_zero] at hz1 hz3
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

@[simp]
theorem principalUnits_zero : principalUnits p 0 = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  simp [principalUnits, Subsingleton.elim _ (1 : (ZMod 1)ˣ)]

@[simp]
theorem principalUnits_two_one : principalUnits 2 1 = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  simp [principalUnits, Subsingleton.elim _ (1 : (ZMod 2)ˣ)]

/-- The subgroup `1 + pⁿℤₚ` of `ℤₚˣ` where `n = 2` if `p = 2`, and `n = 1` otherwise. -/
noncomputable def torsionfreeUnits : Subgroup ℤ_[p]ˣ :=
  principalUnits p (torsionfreeUnitsExponent p)

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
theorem unitsContinuousEquivTorsionfreeProdTorsion_apply (x : ℤ_[p]ˣ) :
    unitsContinuousEquivTorsionfreeProdTorsion p x =
      MonoidHom.equivKerProdRangeOfLeftInverse
        (Units.map (toZModPow (torsionfreeUnitsExponent p)).toMonoidHom)
        (teichmuller p)
        (leftInverse_unitsMap_toZModPow_teichmuller p) x := rfl

@[simp]
theorem unitsContinuousEquivTorsionfreeProdTorsion_symm_apply
    (x : torsionfreeUnits p × torsionUnits p) :
    (unitsContinuousEquivTorsionfreeProdTorsion p).symm x =
      (MonoidHom.equivKerProdRangeOfLeftInverse
        (Units.map (toZModPow (torsionfreeUnitsExponent p)).toMonoidHom)
        (teichmuller p)
        (leftInverse_unitsMap_toZModPow_teichmuller p)).symm x := rfl

#exit

theorem mem_torsionUnits_iff : x ∈ torsionUnits p ↔ ∃ n, 0 < n ∧ x ^ n = 1 := by
  simp only [torsionUnits, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]

theorem mem_torsionfreeUnits_iff :
    x ∈ torsionfreeUnits p ↔ (p ^ if p = 2 then 2 else 1 : ℤ_[p]) ∣ x - 1 := by
  sorry

theorem torsionUnits_eq_rootsOfUnity :
    torsionUnits p = rootsOfUnity (p ^ if p = 2 then 2 else 1) _ := by
  sorry

theorem card_torsionUnits :
    Nat.card (torsionUnits p) = (p ^ if p = 2 then 2 else 1).totient := by
  sorry

theorem hasEnoughRootsOfUnity_iff :
    HasEnoughRootsOfUnity ℤ_[p] n ↔ n ∣ p ^ if p = 2 then 2 else 1 := by
  sorry

theorem disjoint_torsionUnits_torsionfreeUnits :
    Disjoint (torsionUnits p) (torsionfreeUnits p) := by
  sorry

theorem torsionUnits_sup_torsionfreeUnits :
    torsionUnits p ⊔ torsionfreeUnits p = ⊤ := by
  sorry

end PadicInt
