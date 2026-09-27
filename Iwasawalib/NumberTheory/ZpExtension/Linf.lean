/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.ConjugateAction
public import Iwasawalib.NumberTheory.ZpExtension.LnTower

@[expose] public section

/-!

# The field `L∞` and the Galois groups `G` and `X∞`

Let `K∞ / K` be a `ℤₚᵈ`-extension of number fields with layers `Kₙ`, and let `Lₙ` be the maximal
unramified abelian `p`-extension of `Kₙ` (`MvZpExtension.Ln`). This file constructs

* `MvZpExtension.Ln'`, the compositum `K∞ Lₙ`, as an intermediate field of `K∞`;
* `MvZpExtension.Linf`, the field `L∞ = ⋃ₙ Lₙ = ⨆ₙ K∞ Lₙ`, as an intermediate field of `K∞`;
* `MvZpExtension.Xinf`, the group `X∞ = Gal(L∞/K∞)`, as a normal subgroup of
  `G = Gal(L∞/K)`.

These are the blueprint node `Zp-ext-L-inf`.

-/

open IntermediateField NumberField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-! ### The layers `K∞ Lₙ` -/

/-- The compositum `K∞ Lₙ`, an intermediate field of the separable closure of `K∞` over `K∞`. -/
noncomputable def Ln' (n : ℕ) : IntermediateField Kinf (SeparableClosure Kinf) :=
  IntermediateField.adjoin Kinf (H.Ln n : Set (SeparableClosure Kinf))

theorem Ln_subset_Ln' (n : ℕ) :
    (H.Ln n : Set (SeparableClosure Kinf)) ⊆ (H.Ln' n : Set (SeparableClosure Kinf)) :=
  IntermediateField.subset_adjoin _ _

instance isAbelianGalois_Ln' (n : ℕ) : IsAbelianGalois Kinf (H.Ln' n) :=
  IntermediateField.isAbelianGalois_adjoin (F := H.Kn n) (H.Ln n)

instance isSExtension_Ln' (n : ℕ) : IsSExtension Kinf (H.Ln' n) {p} :=
  IntermediateField.isSExtension_singleton_adjoin (F := H.Kn n) (H.Ln n)

instance isUnramifiedEverywhere_Ln' (n : ℕ) :
    NumberField.IsUnramifiedEverywhere Kinf (H.Ln' n) :=
  NumberField.isUnramifiedEverywhere_adjoin (F := H.Kn n) (H.Ln n)

theorem monotone_Ln' : Monotone H.Ln' := fun _ _ h ↦
  IntermediateField.adjoin_le_iff.2 fun _ hx ↦ H.Ln_subset_Ln' _ (H.Ln_mono h hx)

/-! ### The field `L∞` -/

/-- `L∞ = ⋃ₙ Lₙ`, as an intermediate field of the separable closure of `K∞` over `K∞`. -/
noncomputable def Linf : IntermediateField Kinf (SeparableClosure Kinf) := ⨆ n, H.Ln' n

theorem Ln'_le_Linf (n : ℕ) : H.Ln' n ≤ H.Linf := le_iSup _ n

theorem Ln_subset_Linf (n : ℕ) :
    (H.Ln n : Set (SeparableClosure Kinf)) ⊆ (H.Linf : Set (SeparableClosure Kinf)) :=
  (H.Ln_subset_Ln' n).trans (H.Ln'_le_Linf n)

instance isGalois_Linf : IsGalois Kinf (H.Linf) := by
  rw [Linf]
  exact ⟨⟩

instance isAbelianGalois_Linf : IsAbelianGalois Kinf (H.Linf) := by
  rw [← IntermediateField.le_maximalAbelianExtension_iff]
  exact IntermediateField.iSup_le_maximalAbelianExtension fun n ↦
    IntermediateField.le_maximalAbelianExtension _

instance isSExtension_Linf : IsSExtension Kinf (H.Linf) {p} := by
  rw [Linf]
  infer_instance

/-! ### `L∞` as an extension of `K` -/

/-- Every element of `K∞` lies in some `Lₙ`. -/
theorem exists_algebraMap_mem_Ln (x : Kinf) :
    ∃ n, algebraMap Kinf (SeparableClosure Kinf) x ∈ H.Ln n := by
  have : FiniteDimensional K K⟮x⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K) x)
  obtain ⟨n, hn⟩ := H.le_Kn_of_finiteDimensional K⟮x⟯
  have hx : x ∈ H.Kn n := hn (mem_adjoin_simple_self K x)
  refine ⟨n, ?_⟩
  have h2 := (H.Ln n).algebraMap_mem ⟨x, hx⟩
  rw [IsScalarTower.algebraMap_apply (H.Kn n) Kinf (SeparableClosure Kinf) ⟨x, hx⟩] at h2
  simpa using h2

/-- `L∞` is the supremum of the `Lₙ`, computed in the lattice of intermediate fields over `K`:
the extra generators `K∞` are already there. -/
theorem restrictScalars_Linf :
    H.Linf.restrictScalars K = ⨆ n, (H.Ln n).restrictScalars K := by
  refine le_antisymm ?_ (iSup_le fun n x hx ↦ H.Ln_subset_Linf n hx)
  set T : IntermediateField K (SeparableClosure Kinf) := ⨆ n, (H.Ln n).restrictScalars K with hT
  have hmem : ∀ x : Kinf, algebraMap Kinf (SeparableClosure Kinf) x ∈ T.toSubfield := by
    intro x
    obtain ⟨n, hn⟩ := H.exists_algebraMap_mem_Ln x
    exact (le_iSup (fun n ↦ (H.Ln n).restrictScalars K) n) hn
  refine (?_ : H.Linf ≤ T.toSubfield.toIntermediateField hmem)
  refine iSup_le fun n ↦ IntermediateField.adjoin_le_iff.2 fun x hx ↦ ?_
  exact (le_iSup (fun n ↦ (H.Ln n).restrictScalars K) n) hx

instance isGalois_K_restrictScalars_Ln (n : ℕ) : IsGalois K ((H.Ln n).restrictScalars K) :=
  H.isGalois_K_Ln n

instance normal_K_Linf : Normal K (H.Linf.restrictScalars K) := by
  rw [H.restrictScalars_Linf]
  exact IntermediateField.normal_iSup K _ fun n ↦ (H.Ln n).restrictScalars K

instance isSepClosure_K_sepClosure : IsSepClosure K (SeparableClosure Kinf) :=
  IsSepClosure.ofSeparable K Kinf (SeparableClosure Kinf)

instance isGalois_K_Linf : IsGalois K (H.Linf.restrictScalars K) :=
  haveI : Algebra.IsSeparable K (H.Linf.restrictScalars K) :=
    Algebra.isSeparable_tower_bot_of_isSeparable K _ (SeparableClosure Kinf)
  ⟨⟩

/-! ### The Galois groups `G` and `X∞` -/

/-- `G = Gal(L∞/K)`. -/
abbrev GG := Gal(↥(H.Linf.restrictScalars K)/K)

/-- `K∞`, viewed as an intermediate field of `L∞ / K`. -/
noncomputable def KinfIn : IntermediateField K ↥(H.Linf.restrictScalars K) :=
  (⊥ : IntermediateField Kinf ↥H.Linf).restrictScalars K

theorem mem_KinfIn_iff (x : ↥(H.Linf.restrictScalars K)) :
    x ∈ H.KinfIn ↔ ∃ r : Kinf, algebraMap Kinf ↥H.Linf r = x := Iff.rfl

/-- `K∞`, viewed inside `L∞`, is isomorphic to `K∞`. -/
noncomputable def kinfInEquiv : ↥H.KinfIn ≃ₐ[K] Kinf :=
  (IntermediateField.botEquiv Kinf ↥H.Linf).restrictScalars K

instance isGalois_K_KinfIn : IsGalois K H.KinfIn :=
  H.kinfInEquiv.transfer_galois.2 inferInstance

/-- `X∞ = Gal(L∞/K∞)`, as a subgroup of `G = Gal(L∞/K)`. -/
noncomputable def Xinf : Subgroup H.GG := H.KinfIn.fixingSubgroup

instance normal_Xinf : H.Xinf.Normal :=
  IsGalois.fixingSubgroup_normal_of_isGalois (E := H.KinfIn)

/-- An element of `X∞` is exactly a `K∞`-automorphism of `L∞`. -/
noncomputable def xinfHom : H.Xinf →* Gal(↥H.Linf/Kinf) where
  toFun σ :=
    { (σ : H.GG).toRingEquiv with
      commutes' := fun r ↦ σ.2 ⟨algebraMap Kinf ↥H.Linf r, ⟨r, rfl⟩⟩ }
  map_one' := rfl
  map_mul' _ _ := rfl

theorem xinfHom_injective : Function.Injective H.xinfHom := by
  intro a b hab
  refine Subtype.ext (AlgEquiv.ext fun x ↦ ?_)
  exact congr($hab x)

/-- `X∞` is abelian. -/
theorem mul_comm_Xinf (a : H.GG) (ha : a ∈ H.Xinf) (b : H.GG) (hb : b ∈ H.Xinf) :
    a * b = b * a := by
  have := congrArg (Subtype.val (p := fun x ↦ x ∈ H.Xinf))
    (H.xinfHom_injective (a₁ := ⟨a, ha⟩ * ⟨b, hb⟩) (a₂ := ⟨b, hb⟩ * ⟨a, ha⟩) (by
      rw [map_mul, map_mul]
      exact IsMulCommutative.is_comm.comm _ _))
  exact this

/-! ### The exact sequence `1 → X∞ → G → Γ → 1` -/

/-- The restriction map `G = Gal(L∞/K) → Gal(K∞/K) = Γ`. -/
noncomputable def toGamma : H.GG →* Gal(Kinf/K) :=
  (AlgEquiv.autCongr H.kinfInEquiv).toMonoidHom.comp
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(H.Linf.restrictScalars K)) (↥H.KinfIn))

theorem toGamma_surjective : Function.Surjective H.toGamma :=
  (AlgEquiv.autCongr H.kinfInEquiv).surjective.comp
    (AlgEquiv.restrictNormalHom_surjective (F := K) (E := ↥(H.Linf.restrictScalars K))
      (K₁ := ↥H.KinfIn))

theorem ker_toGamma : H.toGamma.ker = H.Xinf := by
  have h : H.toGamma.ker = (AlgEquiv.restrictNormalHom (F := K)
      (K₁ := ↥(H.Linf.restrictScalars K)) (↥H.KinfIn)).ker := by
    ext σ
    simp [toGamma, MonoidHom.mem_ker, map_eq_one_iff _ (MulEquiv.injective _)]
  rw [h, IntermediateField.restrictNormalHom_ker]
  rfl

/-- `Γ = G ⧸ X∞`: the blueprint's exact sequence `1 → X∞ → G → Γ → 1`. -/
noncomputable def gammaMulEquiv : H.GG ⧸ H.Xinf ≃* Gal(Kinf/K) :=
  (QuotientGroup.quotientMulEquivOfEq H.ker_toGamma.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ H.toGamma_surjective)

/-! ### The `Γ`-action on `X∞` -/

/-- The conjugation action of `Γ = G ⧸ X∞` on `X∞`, i.e. the blueprint node `conjugate-action`
applied to `1 → X∞ → G → Γ → 1`. -/
noncomputable def XinfConjQuotient : H.GG ⧸ H.Xinf →* MulAut H.Xinf :=
  Subgroup.conjQuotient H.Xinf H.mul_comm_Xinf

/-- The conjugation action of `Γ` on `X∞` is continuous
(blueprint node `conjugate-action-cont`). -/
theorem continuous_XinfConjQuotient :
    Continuous fun σx : (H.GG ⧸ H.Xinf) × H.Xinf ↦ (H.XinfConjQuotient σx.1 σx.2 : H.Xinf) :=
  Subgroup.continuous_conjQuotient H.Xinf H.mul_comm_Xinf

end MvZpExtension
