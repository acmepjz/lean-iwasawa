/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.FieldTheory.Galois.InverseLimit
public import Iwasawalib.FieldTheory.IntermediateField.FixingSubgroup
public import Iwasawalib.FieldTheory.IntermediateField.RestrictScalars
public import Iwasawalib.NumberTheory.ZpExtension.GaloisGroupProP
public import Iwasawalib.NumberTheory.ZpExtension.Linf

@[expose] public section

/-!
# `X∞ = lim Xₙ` — blueprint node `X-inf-is-proj-lim`

Let `K∞ / K` be a `ℤₚᵈ`-extension of number fields, `Lₙ` the maximal unramified abelian
`p`-extension of the layer `Kₙ`, `K∞Lₙ` the compositum (`MvZpExtension.Ln'`) and
`L∞ = ⨆ₙ K∞Lₙ` (`MvZpExtension.Linf`).  Write `Xₙ = Gal(K∞Lₙ/K∞)`.  This file proves

`X∞ = Gal(L∞/K∞) ≅ lim Xₙ`

as topological groups, using the general theorem
`IntermediateField.galContinuousMulEquivInvLimit`.

Two identifications are needed and are proved here.

* The `K∞Lₙ` are intermediate fields of the *separable closure of `K∞`*, while the general
  theorem wants intermediate fields of `L∞`.  `MvZpExtension.Ln'In` is the transport, and
  `MvZpExtension.XnMulEquiv` says the two readings of `Xₙ` agree.
* `MvZpExtension.Xinf` is a *subgroup of `G = Gal(L∞/K)`*, namely the fixing subgroup of `K∞`,
  and `MvZpExtension.xinfHom` embeds it into `Gal(L∞/K∞)`.  That embedding is onto
  (`MvZpExtension.xinfHom_surjective`): a `K∞`-automorphism of `L∞` restricts scalars to a
  `K`-automorphism, and moving that across
  `IntermediateField.restrictScalarsAutEquiv` lands it in `G`.  Without the
  `restrictScalars` bridge this step is the kernel trap described in
  `Iwasawalib.FieldTheory.IntermediateField.RestrictScalars`.

## Main results

* `MvZpExtension.xinfContinuousMulEquivInvLimit`: `Gal(L∞/K∞) ≃ₜ* lim Xₙ`.
* `MvZpExtension.xinfContinuousMulEquiv`: `X∞ ≃ₜ* Gal(L∞/K∞)`, and
  `MvZpExtension.xinfMulEquiv` for the underlying group isomorphism.
* `MvZpExtension.xinfContinuousMulEquivLimit`: `X∞ ≃ₜ* lim Xₙ`, the two combined.
* `MvZpExtension.XnMulEquiv`: `Gal(K∞Lₙ/K∞)` computed inside `L∞` is `Xₙ`.
-/

open IntermediateField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-! ### The layers, viewed inside `L∞` -/

/-- `K∞Lₙ`, viewed as an intermediate field of `L∞ / K∞`. -/
noncomputable def Ln'In (n : ℕ) : IntermediateField Kinf ↥H.Linf :=
  IntermediateField.restrict (H.Ln'_le_Linf n)

/-- Membership in `MvZpExtension.Ln'In` is membership in `MvZpExtension.Ln'`. -/
theorem mem_Ln'In (n : ℕ) (x : ↥H.Linf) :
    x ∈ H.Ln'In n ↔ (x : SeparableClosure Kinf) ∈ H.Ln' n :=
  IntermediateField.mem_restrict _ x

/-- The layers increase. -/
theorem monotone_Ln'In : Monotone H.Ln'In := fun m n h x hx ↦
  (H.mem_Ln'In n x).2 (H.monotone_Ln' h ((H.mem_Ln'In m x).1 hx))

instance isGalois_Ln'In (n : ℕ) : IsGalois Kinf ↥(H.Ln'In n) :=
  (IntermediateField.restrict_algEquiv (H.Ln'_le_Linf n)).transfer_galois.1 inferInstance

/-- The layers exhaust `L∞`. -/
theorem iSup_Ln'In : ⨆ n, H.Ln'In n = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  have hx : (x : SeparableClosure Kinf) ∈ (⨆ n, H.Ln' n : IntermediateField Kinf _) := x.2
  rw [← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed H.monotone_Ln'.directed_le,
    Set.mem_iUnion] at hx
  obtain ⟨n, hn⟩ := hx
  exact le_iSup H.Ln'In n ((H.mem_Ln'In n x).2 hn)

/-- `Xₙ` computed inside `L∞` is `Xₙ = Gal(K∞Lₙ/K∞)`. -/
noncomputable def XnMulEquiv (n : ℕ) : Gal(↥(H.Ln'In n)/Kinf) ≃* Gal(↥(H.Ln' n)/Kinf) :=
  AlgEquiv.autCongr (IntermediateField.restrict_algEquiv (H.Ln'_le_Linf n)).symm

/-! ### `X∞` as an inverse limit -/

/-- **Blueprint node `X-inf-is-proj-lim`.**  `X∞ = Gal(L∞/K∞)` is the inverse limit of the
`Xₙ = Gal(K∞Lₙ/K∞)`, as a topological group. -/
noncomputable def xinfContinuousMulEquivInvLimit :
    Gal(↥H.Linf/Kinf) ≃ₜ* ↥(galInvLimit H.Ln'In H.monotone_Ln'In) :=
  IntermediateField.galContinuousMulEquivInvLimit H.Ln'In H.monotone_Ln'In H.iSup_Ln'In

/-! ### `X∞ ⊆ G` is all of `Gal(L∞/K∞)` -/

/-- Every `K∞`-automorphism of `L∞` comes from `X∞ ⊆ G`.  The `K`-automorphism it produces is
manufactured with `IntermediateField.restrictScalarsAutEquiv`. -/
theorem xinfHom_surjective : Function.Surjective H.xinfHom := by
  intro σ
  set τ : H.GG := (restrictScalarsAutEquiv K H.Linf).symm (σ.restrictScalars K) with hτ
  have hval : ∀ x : ↥(H.Linf.restrictScalars K),
      ((τ x : ↥(H.Linf.restrictScalars K)) : SeparableClosure Kinf)
        = ((σ ⟨x.1, x.2⟩ : ↥H.Linf) : SeparableClosure Kinf) := fun x ↦ rfl
  have hmem : τ ∈ H.Xinf := by
    show τ ∈ H.KinfIn.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨r, hr⟩ := (H.mem_KinfIn_iff y).1 hy
    refine Subtype.ext ?_
    rw [hval]
    have h2 : (σ ⟨y.1, y.2⟩ : ↥H.Linf) = ⟨y.1, y.2⟩ := by
      have h3 : (⟨y.1, y.2⟩ : ↥H.Linf) = algebraMap Kinf ↥H.Linf r :=
        Subtype.ext (congrArg Subtype.val hr).symm
      rw [h3, AlgEquiv.commutes]
    rw [h2]
  exact ⟨⟨τ, hmem⟩, AlgEquiv.ext fun x ↦ Subtype.ext rfl⟩

/-- **`X∞ = Gal(L∞/K∞)`**: the subgroup `X∞ ⊆ G` is the full Galois group of `L∞ / K∞`. -/
noncomputable def xinfMulEquiv : H.Xinf ≃* Gal(↥H.Linf/Kinf) :=
  MulEquiv.ofBijective H.xinfHom ⟨H.xinfHom_injective, H.xinfHom_surjective⟩

/-- `MvZpExtension.xinfMulEquiv` is `MvZpExtension.xinfHom`. -/
@[simp]
theorem xinfMulEquiv_apply (x : H.Xinf) : H.xinfMulEquiv x = H.xinfHom x := rfl

/-- `MvZpExtension.xinfHom` is continuous: a `K∞`-automorphism of `L∞` is determined near `1`
by its effect on a primitive element of a finite subextension, and adjoining that element to
`K` — not to `K∞` — gives an open subgroup of `G`. -/
theorem continuous_xinfHom : Continuous H.xinfHom := by
  refine continuous_of_continuousAt_one _ (continuousAt_def.2 fun N hN ↦ ?_)
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨E, hEfin, hEN⟩ := hN
  obtain ⟨α, hα⟩ := IntermediateField.exists_adjoin_simple_eq Kinf ↥H.Linf E
  set α' : ↥(H.Linf.restrictScalars K) :=
    (IntermediateField.restrictScalarsAlgEquiv K H.Linf).symm α with hα'
  haveI : FiniteDimensional K K⟮α'⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K) α')
  have hopen : IsOpen ((Subtype.val ⁻¹' (K⟮α'⟯.fixingSubgroup : Set H.GG)) : Set ↥H.Xinf) :=
    (IntermediateField.fixingSubgroup_isOpen K⟮α'⟯).preimage continuous_subtype_val
  refine Filter.mem_of_superset (hopen.mem_nhds (by simp)) fun σ hσ ↦ ?_
  refine hEN ?_
  rw [← hα]
  refine IntermediateField.mem_fixingSubgroup_adjoin_simple ?_
  refine Subtype.ext ?_
  have h1 : ((H.xinfHom σ α : ↥H.Linf) : SeparableClosure Kinf)
      = (((σ : H.GG) ⟨α.1, α.2⟩ : ↥(H.Linf.restrictScalars K)) : SeparableClosure Kinf) := rfl
  rw [h1]
  have hσ' : (σ : H.GG) ∈ K⟮α'⟯.fixingSubgroup := hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ'
  have h2 : (σ : H.GG) α' = α' := hσ' α' (IntermediateField.mem_adjoin_simple_self K α')
  have h3 : (⟨α.1, α.2⟩ : ↥(H.Linf.restrictScalars K)) = α' := rfl
  rw [h3, h2]
  rfl

/-- **`X∞ = Gal(L∞/K∞)` as topological groups.** -/
noncomputable def xinfContinuousMulEquiv : ↥H.Xinf ≃ₜ* Gal(↥H.Linf/Kinf) :=
  letI e : ↥H.Xinf ≃ Gal(↥H.Linf/Kinf) :=
    Equiv.ofBijective _ ⟨H.xinfHom_injective, H.xinfHom_surjective⟩
  letI h : ↥H.Xinf ≃ₜ Gal(↥H.Linf/Kinf) :=
    H.continuous_xinfHom.homeoOfEquivCompactToT2 (f := e)
  { toEquiv := e
    map_mul' := map_mul H.xinfHom
    continuous_toFun := h.continuous_toFun
    continuous_invFun := h.continuous_invFun }

/-- **Blueprint node `X-inf-is-proj-lim`, final form.**  `X∞ ⊆ G` is the inverse limit of the
`Xₙ`, as a topological group. -/
noncomputable def xinfContinuousMulEquivLimit :
    ↥H.Xinf ≃ₜ* ↥(galInvLimit H.Ln'In H.monotone_Ln'In) :=
  H.xinfContinuousMulEquiv.trans H.xinfContinuousMulEquivInvLimit

end MvZpExtension
