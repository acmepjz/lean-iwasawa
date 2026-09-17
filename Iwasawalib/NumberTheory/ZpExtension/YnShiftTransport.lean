/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.XnIsomQuot

@[expose] public section

/-!
# Transport from a shifted extension to the original ambient Galois group

This file identifies the ambient Galois group after shifting the base to `K_n` with the
subgroup of the original ambient group that fixes `K_n`. It also records compatibility with
`Xinf` and transports places between the two presentations of `Linf`.
-/

open IntermediateField Module NumberField
open scoped Pointwise commutatorElement

namespace IntermediateField.Internal

variable {A B L : Type*} [Field A] [Field B] [Field L]
variable [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]

private theorem autCongr_equivOfEq_eq_galContinuousMulEquivCongr
    {E E' : IntermediateField B L} (h : E = E') :
    AlgEquiv.autCongr (equivOfEq h) =
      (galContinuousMulEquivCongr h).toMulEquiv := by
  subst h
  rfl

private theorem restrictScalarsAutEquiv_autCongr_equivOfEq
    {E E' : IntermediateField B L} (h : E = E')
    (sigma : Gal(↥(E.restrictScalars A)/A)) :
    restrictScalarsAutEquiv A E'
        (AlgEquiv.autCongr
          (equivOfEq (congrArg (IntermediateField.restrictScalars A) h)) sigma) =
      AlgEquiv.autCongr ((equivOfEq h).restrictScalars A)
        (restrictScalarsAutEquiv A E sigma) := by
  subst h
  rfl

private theorem galContinuousMulEquivCongr_restrictScalars
    {E E' : IntermediateField B L} (h : E = E') (tau : Gal(↥E/B)) :
    AlgEquiv.autCongr ((equivOfEq h).restrictScalars A) (tau.restrictScalars A) =
      (galContinuousMulEquivCongr h tau).restrictScalars A := by
  subst h
  rfl

private theorem restrictScalarsAutEquiv_autCongr_eq_galContinuousMulEquivCongr
    {E E' : IntermediateField B L} (h : E = E')
    (sigma : Gal(↥(E.restrictScalars A)/A)) (tau : Gal(↥E/B))
    (hsigma : restrictScalarsAutEquiv A E sigma = tau.restrictScalars A) :
    restrictScalarsAutEquiv A E'
        (AlgEquiv.autCongr
          (equivOfEq (congrArg (IntermediateField.restrictScalars A) h)) sigma) =
      (galContinuousMulEquivCongr h tau).restrictScalars A := by
  rw [restrictScalarsAutEquiv_autCongr_equivOfEq h sigma, hsigma,
    galContinuousMulEquivCongr_restrictScalars h tau]

private theorem restrictScalars_restrictScalars
    {R S T L' : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Semiring L'] [Algebra R S] [Algebra S T] [Algebra T L']
    [Algebra R T] [Algebra R L'] [Algebra S L']
    [IsScalarTower R S T] [IsScalarTower S T L']
    [IsScalarTower R T L'] [IsScalarTower R S L']
    (f : L' ≃ₐ[T] L') :
    (f.restrictScalars S).restrictScalars R = f.restrictScalars R := by
  rfl

end IntermediateField.Internal

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable {H : MvZpExtension p ι K Kinf}

/-- The subgroup of the original ambient Galois group fixing `K_n`. -/
noncomputable def GGOverKn (n : ℕ) : Subgroup H.GG :=
  (H.Γpow n : Subgroup H.Γ).comap H.toGamma

namespace Internal

noncomputable def ggShiftToLinfMulEquiv (n : ℕ) :
    (H.shift n).GG ≃* Gal(↥H.Linf/↥(H.Kn n)) :=
  (AlgEquiv.autCongr
    (IntermediateField.equivOfEq
      (congrArg (IntermediateField.restrictScalars (H.Kn n)) (H.Linf_shift n)))).trans
    (IntermediateField.restrictScalarsAutEquiv (H.Kn n) H.Linf)

private theorem ggShiftToLinfMulEquiv_eq (n : ℕ) :
    ggShiftToLinfMulEquiv (H := H) n =
      (AlgEquiv.autCongr
        (IntermediateField.equivOfEq
          (congrArg (IntermediateField.restrictScalars (H.Kn n))
            (H.Linf_shift n)))).trans
        (IntermediateField.restrictScalarsAutEquiv (H.Kn n) H.Linf) := rfl

noncomputable def linfRestrictKnHom (n : ℕ) :
    Gal(↥H.Linf/↥(H.Kn n)) →* Gal(↥H.Linf/K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

end Internal

/-- The canonical restriction map from the shifted ambient Galois group. -/
noncomputable def ggShiftRestrictHom (n : ℕ) : (H.shift n).GG →* H.GG := by
  exact (IntermediateField.restrictScalarsAutEquiv K H.Linf).symm.toMonoidHom.comp
    ((Internal.linfRestrictKnHom (H := H) n).comp
      (Internal.ggShiftToLinfMulEquiv (H := H) n).toMonoidHom)

namespace Internal

private theorem toGamma_action_in_Linf (σ : H.GG) (x : Kinf) :
    (algebraMap Kinf (SeparableClosure Kinf) (H.toGamma σ x)) =
      ((IntermediateField.restrictScalarsAutEquiv K H.Linf σ)
        (algebraMap Kinf ↥H.Linf x) : SeparableClosure Kinf) := by
  let y : H.KinfIn := H.kinfInEquiv.symm x
  have hy : H.kinfInEquiv y = x := H.kinfInEquiv.apply_symm_apply x
  have bridge (z : H.KinfIn) :
      algebraMap Kinf ↥H.Linf (H.kinfInEquiv z) =
        IntermediateField.restrictScalarsAlgEquiv K H.Linf
          (algebraMap H.KinfIn ↥(H.Linf.restrictScalars K) z) :=
    DFunLike.congr_fun H.algebraMap_comp_kinfInEquiv z
  rw [← hy]
  rw [IsScalarTower.algebraMap_apply Kinf ↥H.Linf (SeparableClosure Kinf)]
  simp only [toGamma, MonoidHom.coe_comp, Function.comp_apply]
  have hact :
      H.kinfInEquiv.autCongr.toMonoidHom
          (AlgEquiv.restrictNormalHom H.KinfIn σ) (H.kinfInEquiv y) =
        H.kinfInEquiv ((AlgEquiv.restrictNormalHom H.KinfIn σ) y) := by
    change H.kinfInEquiv.autCongr
      (AlgEquiv.restrictNormalHom H.KinfIn σ) (H.kinfInEquiv y) = _
    simp [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]
  rw [hact]
  rw [bridge, bridge]
  simp [IntermediateField.restrictScalarsAutEquiv, AlgEquiv.autCongr_apply]

private theorem mem_GGOverKn_iff_fixes_Kn (n : ℕ) (σ : H.GG) :
    σ ∈ H.GGOverKn n ↔
      ∀ x : H.Kn n,
        (IntermediateField.restrictScalarsAutEquiv K H.Linf σ)
            (algebraMap (H.Kn n) ↥H.Linf x) =
          algebraMap (H.Kn n) ↥H.Linf x := by
  rw [GGOverKn, Subgroup.mem_comap, ← H.fixingSubgroup_Kn n,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply ↥(H.Kn n) Kinf ↥H.Linf]
    rw [IntermediateField.algebraMap_apply]
    rw [← Internal.toGamma_action_in_Linf (H := H)]
    change algebraMap Kinf (SeparableClosure Kinf) (H.toGamma σ x) =
      algebraMap Kinf (SeparableClosure Kinf) (x : Kinf)
    exact congrArg (algebraMap Kinf (SeparableClosure Kinf)) (h x x.2)
  · intro h x hx
    have hx' := h ⟨x, hx⟩
    have hx'' := congrArg Subtype.val hx'
    rw [IsScalarTower.algebraMap_apply ↥(H.Kn n) Kinf ↥H.Linf] at hx''
    rw [IntermediateField.algebraMap_apply] at hx''
    rw [← Internal.toGamma_action_in_Linf (H := H)] at hx''
    exact (algebraMap Kinf (SeparableClosure Kinf)).injective (by
      rw [IsScalarTower.algebraMap_apply Kinf ↥H.Linf (SeparableClosure Kinf)]
      exact hx'')

private theorem restrictScalarsAutEquiv_ggShiftRestrictHom (n : ℕ)
    (τ : (H.shift n).GG) :
    IntermediateField.restrictScalarsAutEquiv K H.Linf
        (H.ggShiftRestrictHom n τ) =
      Internal.linfRestrictKnHom (H := H) n
        (Internal.ggShiftToLinfMulEquiv (H := H) n τ) := by
  exact (IntermediateField.restrictScalarsAutEquiv K H.Linf).apply_symm_apply _

omit [NumberField K] in
private theorem linfRestrictKnHom_injective (n : ℕ) :
    Function.Injective (Internal.linfRestrictKnHom (H := H) n) := by
  intro σ τ h
  apply AlgEquiv.ext
  intro x
  exact congrFun (congrArg DFunLike.coe h) x

theorem ggShiftRestrictHom_injective (n : ℕ) :
    Function.Injective (H.ggShiftRestrictHom n) := by
  intro σ τ h
  apply (Internal.ggShiftToLinfMulEquiv (H := H) n).injective
  apply Internal.linfRestrictKnHom_injective (H := H) n
  rw [← Internal.restrictScalarsAutEquiv_ggShiftRestrictHom (H := H) n,
    ← Internal.restrictScalarsAutEquiv_ggShiftRestrictHom (H := H) n, h]

theorem range_ggShiftRestrictHom (n : ℕ) :
    (H.ggShiftRestrictHom n).range = H.GGOverKn n := by
  ext σ
  rw [MonoidHom.mem_range, Internal.mem_GGOverKn_iff_fixes_Kn (H := H)]
  constructor
  · rintro ⟨τ, rfl⟩ x
    rw [Internal.restrictScalarsAutEquiv_ggShiftRestrictHom (H := H) n]
    exact (Internal.ggShiftToLinfMulEquiv (H := H) n τ).commutes x
  · intro hσ
    let σL : Gal(↥H.Linf/K) :=
      IntermediateField.restrictScalarsAutEquiv K H.Linf σ
    let σn : Gal(↥H.Linf/↥(H.Kn n)) :=
      { σL with commutes' := hσ }
    refine ⟨(Internal.ggShiftToLinfMulEquiv (H := H) n).symm σn, ?_⟩
    apply (IntermediateField.restrictScalarsAutEquiv K H.Linf).injective
    rw [Internal.restrictScalarsAutEquiv_ggShiftRestrictHom (H := H) n,
      (Internal.ggShiftToLinfMulEquiv (H := H) n).apply_symm_apply]
    apply AlgEquiv.ext
    intro x
    rfl

end Internal

/-- T1: restriction identifies the shifted ambient group with `GGOverKn n`. -/
noncomputable def ggShiftMulEquiv (n : ℕ) : (H.shift n).GG ≃* H.GGOverKn n :=
  (MulEquiv.ofBijective (H.ggShiftRestrictHom n).rangeRestrict
    ⟨fun σ τ h ↦ Internal.ggShiftRestrictHom_injective (H := H) n
        (congrArg Subtype.val h),
      fun y ↦ by
        obtain ⟨σ, hσ⟩ := y.2
        exact ⟨σ, Subtype.ext hσ⟩⟩).trans
    (MulEquiv.subgroupCongr (Internal.range_ggShiftRestrictHom (H := H) n))

/-- T1: the ambient equivalence has the canonical restriction map as its underlying map. -/
theorem coe_ggShiftMulEquiv (n : ℕ) (σ : (H.shift n).GG) :
    ((H.ggShiftMulEquiv n σ : H.GGOverKn n) : H.GG) =
      H.ggShiftRestrictHom n σ := by
  change (((MulEquiv.subgroupCongr (Internal.range_ggShiftRestrictHom (H := H) n))
    ((H.ggShiftRestrictHom n).rangeRestrict σ) : H.GGOverKn n) : H.GG) = _
  rfl

namespace Internal

omit [NumberField K] in
private theorem restrictScalarsAutEquiv_coe_Xinf (x : H.Xinf) :
    IntermediateField.restrictScalarsAutEquiv K H.Linf (x : H.GG) =
      (H.xinfHom x).restrictScalars K := by
  apply AlgEquiv.ext
  intro z
  rfl

set_option maxHeartbeats 1000000 in
private theorem coe_xinfShiftMulEquiv_eq_ggShiftRestrictHom (n : ℕ)
    (x : (H.shift n).Xinf) :
    ((H.xinfShiftMulEquiv n x : H.Xinf) : H.GG) =
      H.ggShiftRestrictHom n (x : (H.shift n).GG) := by
  apply (IntermediateField.restrictScalarsAutEquiv K H.Linf).injective
  rw [Internal.restrictScalarsAutEquiv_coe_Xinf (H := H),
    Internal.restrictScalarsAutEquiv_ggShiftRestrictHom (H := H)]
  have hsigma :
      IntermediateField.restrictScalarsAutEquiv (H.Kn n) (H.shift n).Linf
          (x : (H.shift n).GG) =
        ((H.shift n).xinfHom x).restrictScalars (H.Kn n) := by
    apply AlgEquiv.ext
    intro z
    rfl
  have hnat :=
    IntermediateField.Internal.restrictScalarsAutEquiv_autCongr_eq_galContinuousMulEquivCongr
      (A := H.Kn n) (B := Kinf) (L := SeparableClosure Kinf)
      (H.Linf_shift n) (x : (H.shift n).GG) ((H.shift n).xinfHom x) hsigma
  have hcore :
      Internal.ggShiftToLinfMulEquiv (H := H) n (x : (H.shift n).GG) =
        (H.galLinfShiftContinuousMulEquiv n ((H.shift n).xinfHom x)).restrictScalars
          (H.Kn n) := by
    rw [Internal.ggShiftToLinfMulEquiv_eq (H := H) n,
      H.galLinfShiftContinuousMulEquiv_eq n]
    exact hnat
  rw [H.xinfHom_xinfShiftMulEquiv]
  change (H.galLinfShiftContinuousMulEquiv n ((H.shift n).xinfHom x)).restrictScalars K =
    (Internal.ggShiftToLinfMulEquiv (H := H) n
      (x : (H.shift n).GG)).restrictScalars K
  rw [hcore]
  exact (IntermediateField.Internal.restrictScalars_restrictScalars
    (H.galLinfShiftContinuousMulEquiv n ((H.shift n).xinfHom x))).symm

noncomputable def shiftLinfRingEquiv (n : ℕ) :
    ↥((H.shift n).Linf.restrictScalars (H.Kn n)) ≃+*
      ↥(H.Linf.restrictScalars K) :=
  (IntermediateField.equivOfEq (H.Linf_shift n)).toRingEquiv

end Internal

/-- T2: the ambient shift carries shifted `Xinf` onto the old `Xinf` inside `GGOverKn`. -/
theorem ggShiftMulEquiv_Xinf (n : ℕ) :
    Subgroup.map (H.ggShiftMulEquiv n).toMonoidHom (H.shift n).Xinf =
      H.Xinf.subgroupOf (H.GGOverKn n) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ((H.ggShiftMulEquiv n x : H.GGOverKn n) : H.GG) ∈ H.Xinf
    rw [H.coe_ggShiftMulEquiv,
      ← Internal.coe_xinfShiftMulEquiv_eq_ggShiftRestrictHom (H := H) n ⟨x, hx⟩]
    exact (H.xinfShiftMulEquiv n ⟨x, hx⟩).2
  · intro hy
    let yX : H.Xinf := ⟨(y : H.GG), hy⟩
    let x : (H.shift n).Xinf := (H.xinfShiftMulEquiv n).symm yX
    refine ⟨(x : (H.shift n).GG), x.2, ?_⟩
    apply Subtype.ext
    change ((H.ggShiftMulEquiv n (x : (H.shift n).GG) : H.GGOverKn n) : H.GG) =
      (y : H.GG)
    rw [H.coe_ggShiftMulEquiv,
      ← Internal.coe_xinfShiftMulEquiv_eq_ggShiftRestrictHom (H := H) n x]
    exact congrArg Subtype.val ((H.xinfShiftMulEquiv n).apply_symm_apply yX)

/-- The old `Xinf` element represented by an element of shifted `Xinf`, via ambient transport. -/
noncomputable def xinfOfGGOverKn (n : ℕ) (x : (H.shift n).Xinf) : H.Xinf :=
  ⟨((H.ggShiftMulEquiv n (x : (H.shift n).GG) : H.GGOverKn n) : H.GG), by
    rw [H.coe_ggShiftMulEquiv,
      ← Internal.coe_xinfShiftMulEquiv_eq_ggShiftRestrictHom (H := H) n x]
    exact (H.xinfShiftMulEquiv n x).2⟩

/-- T2: ambient transport and the established `Xinf` transport agree elementwise. -/
theorem ggShiftMulEquiv_xinf_compat (n : ℕ) (x : (H.shift n).Xinf) :
    H.xinfShiftMulEquiv n x = H.xinfOfGGOverKn n x := by
  apply Subtype.ext
  change ((H.xinfShiftMulEquiv n x : H.Xinf) : H.GG) =
    ((H.ggShiftMulEquiv n (x : (H.shift n).GG) : H.GGOverKn n) : H.GG)
  rw [H.coe_ggShiftMulEquiv,
    Internal.coe_xinfShiftMulEquiv_eq_ggShiftRestrictHom (H := H)]

/-- T3: transport a place of shifted `Linf` back to the original `Linf/K` presentation. -/
noncomputable def shiftPlaceEquiv (n : ℕ) :
    AbsoluteValue ((H.shift n).Linf.restrictScalars (H.Kn n)) ℝ ≃
      AbsoluteValue (H.Linf.restrictScalars K) ℝ where
  toFun w := w.comp (f := (Internal.shiftLinfRingEquiv (H := H) n).symm.toRingHom)
    (Internal.shiftLinfRingEquiv (H := H) n).symm.injective
  invFun w := w.comp (f := (Internal.shiftLinfRingEquiv (H := H) n).toRingHom)
    (Internal.shiftLinfRingEquiv (H := H) n).injective
  left_inv w := by
    ext x
    simp [AbsoluteValue.comp_apply]
  right_inv w := by
    ext x
    simp [AbsoluteValue.comp_apply]

/-- T3: restriction of a transported place to `Kinf` agrees with shifted `placeBelow`. -/
theorem placeBelow_shiftPlaceEquiv (n : ℕ)
    (w : AbsoluteValue ((H.shift n).Linf.restrictScalars (H.Kn n)) ℝ) :
    (H.shift n).placeBelow w = H.placeBelow (H.shiftPlaceEquiv n w) := by
  ext x
  rfl

end MvZpExtension
