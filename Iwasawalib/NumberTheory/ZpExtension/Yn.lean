/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.XinfInvLimit

@[expose] public section

/-!
# The submodules `Yₙ` and `Xₙ = X∞ / Yₙ`

Let `K∞ / K` be a `ℤₚᵈ`-extension of number fields, `Lₙ` the maximal unramified abelian
`p`-extension of the layer `Kₙ`, `K∞Lₙ` the compositum, `L∞ = ⋃ₙ K∞Lₙ`, and
`X∞ = Gal(L∞/K∞)`, `Xₙ = Gal(K∞Lₙ/K∞)`.  This file introduces

`Yₙ = Gal(L∞/K∞Lₙ) ⊆ X∞`

and proves `Xₙ = X∞ / Yₙ`.  This is the field-theoretic side of Step 2 of blueprint node
`Xn-isom-qout-of-totally-ramified`, whose module-theoretic side
(`IwasawaAlgebra.nu_smul_topologicalClosure_sup_span`, `Yₙ = ν_{n,e} Y`) is already available.
It is also the description of `Xₙ` that `MvZpExtension.xinfContinuousMulEquivInvLimit`
(`X∞ = lim Xₙ`) refines: `Yₙ` is exactly the kernel of the `n`-th projection of that inverse
limit, and `⋂ₙ Yₙ = 1`.

## Main definitions

* `MvZpExtension.Yn`: `Yₙ = Gal(L∞/K∞Lₙ)`, a subgroup of `X∞ = Gal(L∞/K∞)`.
* `MvZpExtension.xinfQuotientYnMulEquiv`: `X∞ / Yₙ ≅ Xₙ`.

## Main results

* `MvZpExtension.antitone_Yn`, `MvZpExtension.iInf_Yn`: the `Yₙ` decrease to `1`.
-/

open IntermediateField NumberField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- **`Yₙ = Gal(L∞/K∞Lₙ)`**, a subgroup of `X∞ = Gal(L∞/K∞)`. -/
noncomputable def Yn (n : ℕ) : Subgroup Gal(↥H.Linf/Kinf) :=
  (H.Ln'In n).fixingSubgroup

instance normal_Yn (n : ℕ) : (H.Yn n).Normal :=
  IsGalois.fixingSubgroup_normal_of_isGalois (E := H.Ln'In n)

theorem mem_Yn_iff (n : ℕ) (σ : Gal(↥H.Linf/Kinf)) :
    σ ∈ H.Yn n ↔ ∀ x ∈ H.Ln'In n, σ x = x :=
  IntermediateField.mem_fixingSubgroup_iff _ _

/-- `Yₙ` is the kernel of the restriction `X∞ → Xₙ`. -/
theorem Yn_eq_ker (n : ℕ) :
    H.Yn n = (AlgEquiv.restrictNormalHom (F := Kinf) (K₁ := ↥H.Linf) ↥(H.Ln'In n)).ker :=
  (IntermediateField.restrictNormalHom_ker (H.Ln'In n)).symm

/-- **`Xₙ = X∞ / Yₙ`**, with `Xₙ` read inside `L∞`. -/
noncomputable def xinfQuotientYnMulEquiv (n : ℕ) :
    Gal(↥H.Linf/Kinf) ⧸ H.Yn n ≃* Gal(↥(H.Ln'In n)/Kinf) :=
  (QuotientGroup.quotientMulEquivOfEq (H.Yn_eq_ker n)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (AlgEquiv.restrictNormalHom_surjective (F := Kinf) (E := ↥H.Linf)
        (K₁ := ↥(H.Ln'In n))))

/-- **`Xₙ = X∞ / Yₙ`**, with `Xₙ` read as `Gal(K∞Lₙ/K∞)`. -/
noncomputable def xinfQuotientYnMulEquiv' (n : ℕ) :
    Gal(↥H.Linf/Kinf) ⧸ H.Yn n ≃* Gal(↥(H.Ln' n)/Kinf) :=
  (xinfQuotientYnMulEquiv H n).trans (H.XnMulEquiv n)

/-- The `Yₙ` decrease. -/
theorem antitone_Yn : Antitone H.Yn := fun _ _ h ↦
  IntermediateField.fixingSubgroup_le (H.monotone_Ln'In h)

/-- `⋂ₙ Yₙ = 1`: the layers `K∞Lₙ` exhaust `L∞`. -/
theorem iInf_Yn : ⨅ n, H.Yn n = ⊥ := by
  refine le_antisymm (fun σ hσ ↦ ?_) bot_le
  rw [Subgroup.mem_bot]
  refine AlgEquiv.ext fun x ↦ ?_
  have hx : x ∈ (⨆ n, H.Ln'In n : IntermediateField Kinf ↥H.Linf) := by
    rw [H.iSup_Ln'In]; trivial
  rw [← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed H.monotone_Ln'In.directed_le,
    Set.mem_iUnion] at hx
  obtain ⟨n, hn⟩ := hx
  have := (H.mem_Yn_iff n σ).1 (Subgroup.mem_iInf.1 hσ n) x hn
  simpa using this

/-- `Yₙ`, as a subgroup of `X∞ ⊆ G = Gal(L∞/K)`. -/
noncomputable def YnIn (n : ℕ) : Subgroup ↥H.Xinf :=
  (H.Yn n).comap (H.xinfMulEquiv : ↥H.Xinf →* Gal(↥H.Linf/Kinf))

theorem mem_YnIn_iff (n : ℕ) (σ : ↥H.Xinf) :
    σ ∈ H.YnIn n ↔ H.xinfHom σ ∈ H.Yn n := Iff.rfl

/-- `X∞ / Yₙ ≅ Xₙ`, with `X∞` read as the subgroup of `G = Gal(L∞/K)`. -/
noncomputable def xinfInQuotientYnMulEquiv (n : ℕ) :
    letI : (H.YnIn n).Normal := Subgroup.normal_comap _
    ↥H.Xinf ⧸ H.YnIn n ≃* Gal(↥(H.Ln' n)/Kinf) :=
  letI : (H.YnIn n).Normal := Subgroup.normal_comap _
  (QuotientGroup.congr (H.YnIn n) (H.Yn n) H.xinfMulEquiv
    (Subgroup.map_comap_eq_self_of_surjective
      (f := (H.xinfMulEquiv : ↥H.Xinf →* Gal(↥H.Linf/Kinf))) H.xinfHom_surjective _)).trans
      (xinfQuotientYnMulEquiv' H n)

end MvZpExtension
