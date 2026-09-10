/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.NumberTheory.AbsoluteValue.InertiaSubgroup
public import Iwasawalib.NumberTheory.AbsoluteValue.RamificationIndex

@[expose] public section

/-!

# Residue field of a place (`AbsoluteValue`)

(To be written)

-/

namespace AbsoluteValue

section Defs

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)

/-- The valuation subring `O_v = {x | v x ≤ 1}` of a nonarchimedean absolute value `v`. -/
noncomputable abbrev valuationSubring : ValuationSubring K := (v.toValuation hv).valuationSubring

@[simp]
theorem mem_valuationSubring_iff {x : K} : x ∈ v.valuationSubring hv ↔ v x ≤ 1 := by
  rw [valuationSubring, Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe, NNReal.coe_one]
  exact Iff.rfl

/-- The residue field `k_v = O_v / m_v` of a nonarchimedean absolute value `v`. -/
abbrev ResidueField : Type _ := IsLocalRing.ResidueField (v.valuationSubring hv)

theorem residue_valuationSubring_eq_zero_iff (x : v.valuationSubring hv) :
    IsLocalRing.residue _ x = (0 : v.ResidueField hv) ↔ v (x : K) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff, ← NNReal.coe_lt_coe,
    NNReal.coe_one]
  exact Iff.rfl

theorem not_isUnit_iff_apply_lt_one {x : v.valuationSubring hv} :
    ¬IsUnit x ↔ v (x : K) < 1 := by
  rw [← v.residue_valuationSubring_eq_zero_iff hv x, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

end Defs

section Tower

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) (hv : IsNonarchimedean v)
  (hw : IsNonarchimedean w) [w.LiesOver v]

@[simp]
theorem apply_algebraMap_of_liesOver (x : K) : w (algebraMap K L x) = v x := by
  simpa using congr($(LiesOver.comp_eq w v) x)

/-- If `w` lies over `v`, then the inclusion `K → L` restricts to a ring homomorphism
`O_v → O_w`. -/
noncomputable def integerMap : v.valuationSubring hv →+* w.valuationSubring hw :=
  ((algebraMap K L).comp (SubringClass.subtype (v.valuationSubring hv))).codRestrict _ fun x ↦ by
    rw [mem_valuationSubring_iff, RingHom.comp_apply, SubringClass.coe_subtype,
      apply_algebraMap_of_liesOver v w]
    exact (mem_valuationSubring_iff v hv).1 x.2

@[simp]
theorem coe_integerMap (x : v.valuationSubring hv) :
    (integerMap v w hv hw x : L) = algebraMap K L (x : K) := by
  rw [integerMap, RingHom.codRestrict_apply, RingHom.comp_apply, SubringClass.coe_subtype]

instance : IsLocalHom (integerMap v w hv hw) := by
  refine ⟨fun x hx ↦ by_contra fun h ↦ ?_⟩
  rw [not_isUnit_iff_apply_lt_one] at h
  refine (not_isUnit_iff_apply_lt_one (v := w) (hv := hw)).2 ?_ hx
  rw [coe_integerMap, apply_algebraMap_of_liesOver v w]
  exact h

/-- If `w` lies over `v`, then the induced map on residue fields `k_v → k_w`. -/
noncomputable def residueFieldMap : v.ResidueField hv →+* w.ResidueField hw :=
  IsLocalRing.ResidueField.map (integerMap v w hv hw)

noncomputable instance instAlgebraResidueField :
    Algebra (v.ResidueField hv) (w.ResidueField hw) :=
  (residueFieldMap v w hv hw).toAlgebra

@[simp]
theorem algebraMap_residue (x : v.valuationSubring hv) :
    algebraMap (v.ResidueField hv) (w.ResidueField hw) (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (integerMap v w hv hw x) := rfl

end Tower

section Splits

open Polynomial

variable {L : Type*} [Field L] (w : AbsoluteValue L ℝ) (hw : IsNonarchimedean w)

include hw in
theorem apply_sub_le_max (a b : L) : w (a - b) ≤ max (w a) (w b) := by
  have h := hw a (-b)
  rwa [← sub_eq_add_neg, map_neg'] at h

include hw in
/-- If `P = (X - C β) * Q` where all coefficients of `P` are `w`-integral and `w β > 1`, then
all coefficients of `Q` are of absolute value at most `(w β)⁻¹`. -/
theorem apply_mul_coeff_le_one_of_eq_X_sub_C_mul {P Q : L[X]} {β : L} (hβ : 1 < w β)
    (hPQ : P = (X - C β) * Q) (hP : ∀ k, w (P.coeff k) ≤ 1) (k : ℕ) :
    w β * w (Q.coeff k) ≤ 1 := by
  induction k with
  | zero =>
    have h0 : P.coeff 0 = -(β * Q.coeff 0) := by
      rw [hPQ, mul_coeff_zero]; simp
    have h := hP 0
    rwa [h0, map_neg', map_mul] at h
  | succ k ih =>
    have hk : w (Q.coeff k) ≤ 1 := by nlinarith [w.nonneg (Q.coeff k)]
    have h1 : β * Q.coeff (k + 1) = Q.coeff k - P.coeff (k + 1) := by
      rw [hPQ, sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]; ring
    calc w β * w (Q.coeff (k + 1)) = w (β * Q.coeff (k + 1)) := (map_mul ..).symm
      _ = w (Q.coeff k - P.coeff (k + 1)) := by rw [h1]
      _ ≤ max (w (Q.coeff k)) (w (P.coeff (k + 1))) := apply_sub_le_max w hw _ _
      _ ≤ 1 := max_le hk (hP _)

/-- **Key lemma**: if a polynomial with coefficients in the valuation ring `O_w` splits in `L`,
then its reduction modulo the maximal ideal splits in the residue field `k_w`. -/
theorem splits_map_residue (P : (w.valuationSubring hw)[X])
    (hsp : (P.map (SubringClass.subtype (w.valuationSubring hw))).Splits) :
    (P.map (IsLocalRing.residue (w.valuationSubring hw))).Splits := by
  have hιinj : Function.Injective (SubringClass.subtype (w.valuationSubring hw)) :=
    Subtype.val_injective
  suffices H : ∀ (n : ℕ) (P : (w.valuationSubring hw)[X]), P.natDegree ≤ n →
      (P.map (SubringClass.subtype (w.valuationSubring hw))).Splits →
      (P.map (IsLocalRing.residue (w.valuationSubring hw))).Splits from
    H P.natDegree P le_rfl hsp
  intro n
  induction n with
  | zero =>
    intro P hP _
    exact Splits.of_natDegree_le_one (le_trans natDegree_map_le (by omega))
  | succ n ih =>
    intro P hP hsp
    by_cases hle : P.natDegree ≤ n
    · exact ih P hle hsp
    have hdeg : P.natDegree = n + 1 := le_antisymm hP (by omega)
    have hP0 : P ≠ 0 := fun h ↦ by simp [h] at hdeg
    have hmap0 : P.map (SubringClass.subtype (w.valuationSubring hw)) ≠ 0 := fun h ↦
      hP0 (Polynomial.map_injective _ hιinj (by simpa using h))
    have hdegmap : (P.map (SubringClass.subtype (w.valuationSubring hw))).natDegree = n + 1 := by
      rw [natDegree_map_eq_of_injective hιinj, hdeg]
    obtain ⟨β, hβ⟩ := hsp.exists_eval_eq_zero (by
      rw [degree_eq_natDegree hmap0, hdegmap]
      exact_mod_cast Nat.succ_ne_zero n)
    have hPcoeff : ∀ k,
        w ((P.map (SubringClass.subtype (w.valuationSubring hw))).coeff k) ≤ 1 := by
      intro k
      rw [coeff_map, SubringClass.coe_subtype]
      exact (mem_valuationSubring_iff w hw).1 (P.coeff k).2
    rcases le_or_gt (w β) 1 with hb | hb
    · -- `β` is `w`-integral: divide by the monic factor `X - C β` inside `O_w[X]`
      set b : w.valuationSubring hw := ⟨β, (mem_valuationSubring_iff w hw).2 hb⟩ with hbdef
      have hroot : P.IsRoot b := by
        have h : (SubringClass.subtype (w.valuationSubring hw)) (P.eval b) = 0 := by
          rw [← eval₂_hom, ← eval_map]
          exact hβ
        simpa using hιinj (by simpa using h)
      obtain ⟨Q, hQ⟩ := (dvd_iff_isRoot.2 hroot)
      have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ; exact hP0 hQ
      have hQdeg : Q.natDegree ≤ n := by
        have h := congrArg natDegree hQ
        rw [natDegree_mul (X_sub_C_ne_zero b) hQ0, natDegree_X_sub_C] at h
        omega
      have hQsp : (Q.map (SubringClass.subtype (w.valuationSubring hw))).Splits := by
        refine hsp.of_dvd hmap0 ⟨(X - C β), ?_⟩
        rw [hQ, Polynomial.map_mul]
        simp only [Polynomial.map_sub, map_C, map_X, SubringClass.coe_subtype, hbdef]
        ring
      have := ih Q hQdeg hQsp
      rw [hQ, Polynomial.map_mul, Polynomial.map_sub, map_C, map_X]
      exact (Splits.X_sub_C _).mul this
    · -- `β⁻¹` is in the maximal ideal: the reduction loses this root
      have hβ0 : β ≠ 0 := fun h ↦ by simp [h] at hb; linarith [hb]
      have hγ : w β⁻¹ < 1 := by
        rw [map_inv₀]
        rw [inv_lt_one₀ (by linarith [w.nonneg β] : (0:ℝ) < w β)]
        exact hb
      set c : w.valuationSubring hw := ⟨β⁻¹, (mem_valuationSubring_iff w hw).2 hγ.le⟩ with hcdef
      set Q₁ : L[X] := (P.map (SubringClass.subtype (w.valuationSubring hw))) /ₘ (X - C β) with hQ₁
      have hfac : (X - C β) * Q₁ = P.map (SubringClass.subtype (w.valuationSubring hw)) :=
        mul_divByMonic_eq_iff_isRoot.2 hβ
      have hQ₂ : ∀ k, w ((C β * Q₁).coeff k) ≤ 1 := by
        intro k
        rw [coeff_C_mul, map_mul]
        exact apply_mul_coeff_le_one_of_eq_X_sub_C_mul w hw hb hfac.symm hPcoeff k
      obtain ⟨Q, hQ⟩ : ∃ Q : (w.valuationSubring hw)[X],
          Q.map (SubringClass.subtype (w.valuationSubring hw)) = C β * Q₁ := by
        obtain ⟨Q, hQ⟩ := (Polynomial.lifts_iff_coeff_lifts
          (f := SubringClass.subtype (w.valuationSubring hw)) (C β * Q₁)).2 fun k ↦
            ⟨⟨_, (mem_valuationSubring_iff w hw).2 (hQ₂ k)⟩, rfl⟩
        exact ⟨Q, by simpa using hQ⟩
      have hUQ : P = (C c * X - 1) * Q := by
        refine Polynomial.map_injective _ hιinj ?_
        rw [Polynomial.map_mul, hQ, Polynomial.map_sub, Polynomial.map_mul, map_C, map_X,
          Polynomial.map_one, ← hfac, SubringClass.coe_subtype]
        have hc : (c : L) = β⁻¹ := rfl
        have h1 : C β⁻¹ * C β = (1 : L[X]) := by rw [← C_mul, inv_mul_cancel₀ hβ0, C_1]
        rw [hc]
        linear_combination (-(X * Q₁)) * h1
      have hQ0 : Q ≠ 0 := by rintro rfl; simp at hUQ; exact hP0 hUQ
      have hc0 : c ≠ 0 := by
        simp only [hcdef, ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero]
        exact inv_ne_zero hβ0
      have hUdeg : (C c * X - 1 : (w.valuationSubring hw)[X]).natDegree = 1 := by
        rw [← C_1, natDegree_sub_C, natDegree_C_mul_X _ hc0]
      have hU0 : (C c * X - 1 : (w.valuationSubring hw)[X]) ≠ 0 := fun h ↦ by
        rw [h] at hUdeg; simp at hUdeg
      have hQdeg : Q.natDegree ≤ n := by
        have h := congrArg natDegree hUQ
        rw [natDegree_mul hU0 hQ0, hUdeg] at h
        omega
      have hQsp : (Q.map (SubringClass.subtype (w.valuationSubring hw))).Splits := by
        rw [hQ]
        refine Splits.C_mul ?_ _
        exact hsp.of_dvd hmap0 ⟨(X - C β), by rw [← hfac]; ring⟩
      have hind := ih Q hQdeg hQsp
      have hρc : IsLocalRing.residue (w.valuationSubring hw) c = 0 :=
        (residue_valuationSubring_eq_zero_iff w hw c).2 hγ
      have hUmap : ((C c * X - 1 : (w.valuationSubring hw)[X]).map
          (IsLocalRing.residue (w.valuationSubring hw))) = C (-1) := by
        rw [Polynomial.map_sub, Polynomial.map_mul, map_C, map_X, Polynomial.map_one, hρc]
        simp
      rw [hUQ, Polynomial.map_mul, hUmap]
      exact (Splits.C _).mul hind

end Splits

section Main

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) (hv : IsNonarchimedean v)
  (hw : IsNonarchimedean w) [w.LiesOver v]

theorem algebraMap_comp_residue :
    (algebraMap (v.ResidueField hv) (w.ResidueField hw)).comp
        (IsLocalRing.residue (v.valuationSubring hv)) =
      (IsLocalRing.residue (w.valuationSubring hw)).comp (integerMap v w hv hw) :=
  RingHom.ext fun x ↦ algebraMap_residue v w hv hw x

theorem subtype_comp_integerMap :
    (SubringClass.subtype (w.valuationSubring hw)).comp (integerMap v w hv hw) =
      (algebraMap K L).comp (SubringClass.subtype (v.valuationSubring hv)) :=
  RingHom.ext fun x ↦ by
    rw [RingHom.comp_apply, RingHom.comp_apply, SubringClass.coe_subtype,
      SubringClass.coe_subtype, coe_integerMap]

/-- Given an element `a` of the valuation ring `O_w` which is algebraic over `K`, there is a
polynomial `G` with coefficients in `O_v`, which is a `K`-multiple of the minimal polynomial of
`a` over `K`, whose reduction modulo `m_v` is nonzero and kills the residue of `a`. -/
theorem exists_lift_minpoly (a : w.valuationSubring hw) (ha : IsIntegral K (a : L)) :
    ∃ (G : (v.valuationSubring hv)[X]) (c : K), c ≠ 0 ∧
      G.map (SubringClass.subtype (v.valuationSubring hv)) = C c * minpoly K (a : L) ∧
      G.map (IsLocalRing.residue (v.valuationSubring hv)) ≠ 0 ∧
      Polynomial.aeval (IsLocalRing.residue (w.valuationSubring hw) a)
        (G.map (IsLocalRing.residue (v.valuationSubring hv))) = 0 := by
  have hvinj : Function.Injective (SubringClass.subtype (v.valuationSubring hv)) :=
    Subtype.val_injective
  have hwinj : Function.Injective (SubringClass.subtype (w.valuationSubring hw)) :=
    Subtype.val_injective
  set f := minpoly K (a : L) with hf
  have hf0 : f ≠ 0 := minpoly.ne_zero ha
  obtain ⟨j, hj, hjmax⟩ := f.support.exists_max_image (fun i ↦ v (f.coeff i))
    (Polynomial.support_nonempty.2 hf0)
  have hcj : f.coeff j ≠ 0 := Polynomial.mem_support_iff.1 hj
  set c : K := (f.coeff j)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hcj
  have hvcj : 0 < v (f.coeff j) := v.pos hcj
  have hbound : ∀ i, v ((C c * f).coeff i) ≤ 1 := by
    intro i
    rw [coeff_C_mul, map_mul, hc, map_inv₀]
    rcases eq_or_ne (f.coeff i) 0 with h | h
    · simp [h]
    · rw [inv_mul_le_iff₀ hvcj, mul_one]
      exact hjmax i (Polynomial.mem_support_iff.2 h)
  obtain ⟨G, hG⟩ : ∃ G : (v.valuationSubring hv)[X],
      G.map (SubringClass.subtype (v.valuationSubring hv)) = C c * f := by
    obtain ⟨G, hG⟩ := (Polynomial.lifts_iff_coeff_lifts
      (f := SubringClass.subtype (v.valuationSubring hv)) (C c * f)).2 fun k ↦
        ⟨⟨_, (mem_valuationSubring_iff v hv).2 (hbound k)⟩, rfl⟩
    exact ⟨G, by simpa using hG⟩
  have hGj : G.coeff j = 1 := by
    have h := congrArg (fun p ↦ Polynomial.coeff p j) hG
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul, hc, inv_mul_cancel₀ hcj] at h
    exact hvinj (by simpa using h)
  refine ⟨G, c, hc0, hG, ?_, ?_⟩
  · intro h
    have := congrArg (fun p ↦ Polynomial.coeff p j) h
    simp only [Polynomial.coeff_map, hGj, map_one, Polynomial.coeff_zero] at this
    exact one_ne_zero this
  · -- evaluate the reduction at the residue of `a`
    have h1 : (G.map (IsLocalRing.residue (v.valuationSubring hv))).map
        (algebraMap (v.ResidueField hv) (w.ResidueField hw)) =
        (G.map (integerMap v w hv hw)).map (IsLocalRing.residue (w.valuationSubring hw)) := by
      rw [Polynomial.map_map, Polynomial.map_map, algebraMap_comp_residue]
    have h2 : (G.map (integerMap v w hv hw)).eval a = 0 := by
      refine hwinj ?_
      rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, Polynomial.map_map,
        subtype_comp_integerMap, ← Polynomial.map_map, hG, Polynomial.map_mul, map_C,
        Polynomial.eval_mul, Polynomial.eval_C, SubringClass.coe_subtype]
      have hz : Polynomial.eval ((a : L)) (f.map (algebraMap K L)) = 0 := by
        rw [← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def, hf]
        exact minpoly.aeval K (a : L)
      rw [hz, mul_zero]
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, h1, Polynomial.eval_map,
      Polynomial.eval₂_hom, h2, map_zero]

/-- If `L / K` is algebraic and `w` lies over `v`, then the residue field extension
`k_w / k_v` is algebraic. -/
theorem isAlgebraic_residueField [Algebra.IsAlgebraic K L] :
    Algebra.IsAlgebraic (v.ResidueField hv) (w.ResidueField hw) := by
  refine ⟨fun ξ ↦ ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective ξ
  obtain ⟨G, c, hc0, hG, hGne, hGeval⟩ := exists_lift_minpoly v w hv hw a
    (Algebra.IsAlgebraic.isAlgebraic (R := K) (a : L)).isIntegral
  exact ⟨_, hGne, hGeval⟩

/-- **The residue field extension of a normal extension is normal.** If `L / K` is a normal
extension and `w` is a nonarchimedean place of `L` lying over the place `v` of `K`, then the
residue field extension `k_w / k_v` is normal. -/
theorem normal_residueField [Normal K L] :
    Normal (v.ResidueField hv) (w.ResidueField hw) := by
  rw [normal_iff]
  intro ξ
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective ξ
  obtain ⟨G, c, hc0, hG, hGne, hGeval⟩ := exists_lift_minpoly v w hv hw a
    (Algebra.IsAlgebraic.isAlgebraic (R := K) (a : L)).isIntegral
  have halg : IsAlgebraic (v.ResidueField hv)
      (IsLocalRing.residue (w.valuationSubring hw) a) := ⟨_, hGne, hGeval⟩
  refine ⟨halg.isIntegral, ?_⟩
  have hsplits : ((G.map (IsLocalRing.residue (v.valuationSubring hv))).map
      (algebraMap (v.ResidueField hv) (w.ResidueField hw))).Splits := by
    rw [Polynomial.map_map, algebraMap_comp_residue, ← Polynomial.map_map]
    refine splits_map_residue w hw _ ?_
    rw [Polynomial.map_map, subtype_comp_integerMap, ← Polynomial.map_map, hG,
      Polynomial.map_mul, map_C]
    exact Splits.C_mul (Normal.splits ‹Normal K L› (a : L)) _
  refine hsplits.of_dvd (fun h ↦ hGne ?_) (Polynomial.map_dvd _ (minpoly.dvd _ _ hGeval))
  exact Polynomial.map_injective _
    (algebraMap (v.ResidueField hv) (w.ResidueField hw)).injective (by simpa using h)

section Action

variable {F L : Type*} [Field F] [Field L] [Algebra F L] (w : AbsoluteValue L ℝ)
  (hw : IsNonarchimedean w)

/-- An element `σ` of the decomposition subgroup `D_w(L/F)` preserves the valuation ring `O_w`,
hence induces a ring automorphism of `O_w`. -/
def integerAut (σ : w.decompositionSubgroup F) : RingAut (w.valuationSubring hw) where
  toFun x := ⟨σ.1 x, by
    rw [mem_valuationSubring_iff, w.apply_eq_of_mem_decompositionSubgroup σ.2]
    exact (mem_valuationSubring_iff w hw).1 x.2⟩
  invFun x := ⟨σ.1.symm x, by
    rw [mem_valuationSubring_iff, ← w.apply_eq_of_mem_decompositionSubgroup σ.2,
      AlgEquiv.apply_symm_apply]
    exact (mem_valuationSubring_iff w hw).1 x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[simp]
theorem coe_integerAut (σ : w.decompositionSubgroup F) (x : w.valuationSubring hw) :
    (integerAut w hw σ x : L) = σ.1 x := rfl

@[simp]
theorem integerAut_one : integerAut w hw (1 : w.decompositionSubgroup F) = 1 :=
  RingEquiv.ext fun _ ↦ Subtype.ext rfl

@[simp]
theorem integerAut_mul (σ τ : w.decompositionSubgroup F) :
    integerAut w hw (σ * τ) = integerAut w hw σ * integerAut w hw τ :=
  RingEquiv.ext fun _ ↦ Subtype.ext rfl

/-- The natural group homomorphism from the decomposition subgroup `D_w(L/F)` to the group of
ring automorphisms of the residue field `k_w`. Its kernel is the inertia subgroup
`I_w(L/F)`; see `AbsoluteValue.ker_residueAutHom`. -/
noncomputable def residueAutHom : w.decompositionSubgroup F →* RingAut (w.ResidueField hw) where
  toFun σ := IsLocalRing.ResidueField.mapAut (integerAut w hw σ)
  map_one' := by rw [integerAut_one, map_one]
  map_mul' σ τ := by rw [integerAut_mul, map_mul]

@[simp]
theorem residueAutHom_residue (σ : w.decompositionSubgroup F) (x : w.valuationSubring hw) :
    residueAutHom w hw σ (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (integerAut w hw σ x) := rfl

/-- The kernel of the action of the decomposition subgroup on the residue field is exactly the
inertia subgroup. -/
theorem ker_residueAutHom :
    (residueAutHom w hw (F := F)).ker =
      (w.inertiaSubgroup F).comap (w.decompositionSubgroup F).subtype := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.coe_subtype,
    mem_inertiaSubgroup_iff_of_isNonarchimedean w hw]
  constructor
  · refine fun h ↦ ⟨σ.2, fun x hx ↦ ?_⟩
    have h2 := congr($h (IsLocalRing.residue _ ⟨x, (mem_valuationSubring_iff w hw).2 hx⟩))
    rw [residueAutHom_residue, RingAut.one_apply, ← sub_eq_zero, ← map_sub,
      residue_valuationSubring_eq_zero_iff] at h2
    exact h2
  · refine fun h ↦ RingEquiv.ext fun ξ ↦ ?_
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective ξ
    rw [residueAutHom_residue, RingAut.one_apply, ← sub_eq_zero, ← map_sub,
      residue_valuationSubring_eq_zero_iff]
    exact h.2 (x : L) ((mem_valuationSubring_iff w hw).1 x.2)

end Action

section TowerAction

variable {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [Algebra K L]
  [IsScalarTower F K L] [Normal F K]
  (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) (hv : IsNonarchimedean v)
  (hw : IsNonarchimedean w) [w.LiesOver v] {τ : L ≃ₐ[F] L}

/-- If `τ` is in the decomposition subgroup of `w`, then its restriction to `K` is in the
decomposition subgroup of `v`. -/
theorem restrictNormalHom_mem_decompositionSubgroup (hτ : τ ∈ w.decompositionSubgroup F) :
    AlgEquiv.restrictNormalHom K τ ∈ v.decompositionSubgroup F := by
  rw [mem_decompositionSubgroup_iff_forall_apply_eq]
  intro x
  rw [← apply_algebraMap_of_liesOver v w, ← apply_algebraMap_of_liesOver v w (x := x),
    AlgEquiv.algebraMap_restrictNormalHom_apply]
  exact w.apply_eq_of_mem_decompositionSubgroup hτ _

/-- The action of `τ` on the residue field `k_w` restricts, on the image of `k_v`, to the action
of the restriction of `τ` to `K` on `k_v`. -/
theorem residueAutHom_algebraMap (hτ : τ ∈ w.decompositionSubgroup F) (x : v.valuationSubring hv) :
    residueAutHom w hw ⟨τ, hτ⟩ (algebraMap (v.ResidueField hv) (w.ResidueField hw)
        (IsLocalRing.residue _ x)) =
      algebraMap (v.ResidueField hv) (w.ResidueField hw) (IsLocalRing.residue _
        (integerAut v hv ⟨_, restrictNormalHom_mem_decompositionSubgroup v w hτ⟩ x)) := by
  rw [algebraMap_residue, residueAutHom_residue, algebraMap_residue]
  congr 1
  refine Subtype.ext ?_
  rw [coe_integerMap, coe_integerAut, coe_integerAut, coe_integerMap]
  exact (AlgEquiv.algebraMap_restrictNormalHom_apply K τ x).symm

/-- The automorphism of `k_w` induced by `τ ∈ D_w(L/F)` fixes the subfield `k_v` pointwise if
and only if the restriction of `τ` to `K` lies in the inertia subgroup `I_v(K/F)`. This is the
statement that `τ` maps into `Aut(k_w / k_v)` exactly when `τ|_K` is inertial. -/
theorem forall_residueAutHom_algebraMap_eq_iff (hτ : τ ∈ w.decompositionSubgroup F) :
    (∀ ξ : v.ResidueField hv, residueAutHom w hw ⟨τ, hτ⟩
        (algebraMap (v.ResidueField hv) (w.ResidueField hw) ξ) =
      algebraMap (v.ResidueField hv) (w.ResidueField hw) ξ) ↔
      AlgEquiv.restrictNormalHom K τ ∈ v.inertiaSubgroup F := by
  have hinj := (algebraMap (v.ResidueField hv) (w.ResidueField hw)).injective
  rw [mem_inertiaSubgroup_iff_of_isNonarchimedean v hv]
  constructor
  · refine fun h ↦ ⟨restrictNormalHom_mem_decompositionSubgroup v w hτ, fun x hx ↦ ?_⟩
    have hx' : x ∈ v.valuationSubring hv := (mem_valuationSubring_iff v hv).2 hx
    have h2 := h (IsLocalRing.residue _ ⟨x, hx'⟩)
    rw [residueAutHom_algebraMap v w hv hw hτ ⟨x, hx'⟩] at h2
    replace h2 := hinj h2
    rw [← sub_eq_zero, ← map_sub, residue_valuationSubring_eq_zero_iff] at h2
    exact h2
  · refine fun h ξ ↦ ?_
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective ξ
    rw [residueAutHom_algebraMap v w hv hw hτ x]
    congr 1
    rw [← sub_eq_zero, ← map_sub, residue_valuationSubring_eq_zero_iff]
    exact h.2 (x : K) ((mem_valuationSubring_iff v hv).1 x.2)

end TowerAction

end Main

end AbsoluteValue
