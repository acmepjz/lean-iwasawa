/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Iwasawalib.NumberTheory.Padics.ForMathlib1
public import Mathlib.RingTheory.Localization.Cardinality
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.Topology.Algebra.Module.Cardinality

@[expose] public section

/-! ### Maybe these should be in mathlib -/

theorem Nat.totient_pow_mul_of_prime_of_dvd {p n : ℕ} (hp : Prime p) (h : p ∣ n) (m : ℕ) :
    (p ^ m * n).totient = p ^ m * n.totient := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, totient_mul_of_prime_of_dvd hp (Nat.dvd_mul_left_of_dvd h (p ^ m)),
      ih, mul_assoc]

instance hasEnoughRootsOfUnity_two (R : Type*) [CommRing R] [IsDomain R] [NeZero (2 : R)] :
    HasEnoughRootsOfUnity R 2 := by
  refine ⟨⟨-1, by simp, fun n hn ↦ ?_⟩, inferInstance⟩
  have hneq : (-1 : R) ≠ 1 := fun h' ↦ ‹NeZero (2 : R)›.out <| by linear_combination -h'
  rwa [neg_one_pow_eq_one_iff_even hneq, even_iff_two_dvd] at hn

@[to_additive]
theorem IsCyclic.cardinalMk_le_aleph0 (G : Type*) [Pow G ℤ] [IsCyclic G] :
    Cardinal.mk G ≤ Cardinal.aleph0 := by
  simpa using Cardinal.lift_mk_le_lift_mk_of_surjective (exists_zpow_surjective G).choose_spec

@[simp]
theorem Padic.cardinalMk_eq_continuum (p : ℕ) [Fact p.Prime] :
    Cardinal.mk ℚ_[p] = Cardinal.continuum :=
  le_antisymm (Cardinal.mk_quotient_le.trans <| (Cardinal.mk_subtype_le _).trans <|
    by simp) (continuum_le_cardinal_of_nontriviallyNormedField _)

@[simp]
theorem PadicInt.cardinalMk_eq_continuum (p : ℕ) [Fact p.Prime] :
    Cardinal.mk ℤ_[p] = Cardinal.continuum := by
  rw [← IsFractionRing.cardinalMk ℤ_[p] ℚ_[p], Padic.cardinalMk_eq_continuum]

theorem Field.isAddCyclic_iff (F : Type*) [Field F] : IsAddCyclic F ↔ (Nat.card F).Prime := by
  obtain ⟨p, _ | ⟨hp⟩⟩ := ExpChar.exists F
  · suffices ¬IsAddCyclic F by simp [this, Nat.not_prime_zero]
    rintro ⟨a, hsurj⟩
    have ha : a ≠ 0 := by
      rintro rfl
      refine not_subsingleton F ⟨fun x y ↦ ?_⟩
      obtain ⟨_, rfl⟩ := hsurj x
      obtain ⟨_, rfl⟩ := hsurj y
      simp
    obtain ⟨n, hn⟩ := hsurj ((2⁻¹ : ℚ) • a)
    simp_rw [← algebraMap_smul ℚ n a] at hn
    replace hn := congr(2 * $(smul_left_injective ℚ ha hn))
    simp only [algebraMap_int_eq, eq_intCast, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_inv_cancel₀] at hn
    norm_cast at hn
    omega
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · convert hp
    have := Fact.mk hp
    let _ := ZMod.algebra F p
    have hrank : Module.rank (ZMod p) F = 1 := by
      refine le_antisymm (rank_le_one_iff.2 ?_) (Cardinal.one_le_iff_pos.2 Module.rank_pos_of_free)
      obtain ⟨a, hsurj⟩ := exists_zsmul_surjective F
      refine ⟨a, fun v ↦ ?_⟩
      obtain ⟨n, hn⟩ := hsurj v
      use algebraMap _ _ n
      simp_rw [← hn, algebraMap_smul]
    have : Module.Finite (ZMod p) F := Module.rank_lt_aleph0_iff.1 (by simp [hrank])
    have := congr(Cardinal.toNat
      $(lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank (ZMod p) F))
    simpa [hrank] using this
  · have := Fact.mk h
    exact isAddCyclic_of_prime_card rfl

theorem Field.not_isAddCyclic_of_infinite (F : Type*) [Field F] [Infinite F] : ¬IsAddCyclic F := by
  simp [isAddCyclic_iff, Nat.not_prime_zero]

theorem PadicInt.not_isAddCyclic (p : ℕ) [Fact p.Prime] : ¬IsAddCyclic ℤ_[p] := fun _ ↦ by
  have := IsAddCyclic.cardinalMk_le_aleph0 ℤ_[p]
  rw [cardinalMk_eq_continuum] at this
  exact this.not_gt Cardinal.aleph0_lt_continuum

namespace MonoidHom

variable {B C : Type*} [CommGroup B] [Group C]
  (f : B →* C) (g : C →* B) (hfg : Function.LeftInverse f g)

/-- If a surjective group homomorphism `f : B →* C` has a section `g : C →* B`, then there is a
natural isomorphism of `B` to `ker(f) × im(g)`. We use `im(g)` instead of `C` since if `B`
has topology, then both of `ker(f)` and `im(g)` will also get topology automatically. -/
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

@[simp]
theorem val_fst_equivKerProdRangeOfLeftInverse_apply (x) :
    (equivKerProdRangeOfLeftInverse f g hfg x).1.1 = x * (g (f x))⁻¹ := rfl

@[simp]
theorem val_snd_equivKerProdRangeOfLeftInverse_apply (x) :
    (equivKerProdRangeOfLeftInverse f g hfg x).2.1 = g (f x) := rfl

@[simp]
theorem equivKerProdRangeOfLeftInverse_symm_apply (x) :
    (equivKerProdRangeOfLeftInverse f g hfg).symm x = x.1.1 * x.2.1 := rfl

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
theorem val_fst_continuousEquivKerProdRangeOfLeftInverse_apply (x) :
    (continuousEquivKerProdRangeOfLeftInverse f g hfg hc x).1.1 = x * (g (f x))⁻¹ := rfl

@[simp]
theorem val_snd_continuousEquivKerProdRangeOfLeftInverse_apply (x) :
    (continuousEquivKerProdRangeOfLeftInverse f g hfg hc x).2.1 = g (f x) := rfl

@[simp]
theorem continuousEquivKerProdRangeOfLeftInverse_symm_apply (x) :
    (continuousEquivKerProdRangeOfLeftInverse f g hfg hc).symm x = x.1.1 * x.2.1 := rfl

end MonoidHom

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

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
