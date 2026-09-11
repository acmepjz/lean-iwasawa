/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.XinfSubmodule
public import Iwasawalib.RingTheory.IwasawaAlgebra.ProPFgTorsion

@[expose] public section

/-!
# `X∞` is a finitely generated torsion `Λ`-module — Step 3 on `X∞`

`Iwasawalib.RingTheory.IwasawaAlgebra.FgTorsionSpan` proves Step 3 of blueprint node
`Xn-isom-qout-of-totally-ramified` for an abstract profinite `Λ`-module.  This file transports
it to `X∞ = Gal(L∞/K∞)` across `MvZpExtension.XinfLambdaModule`.

What has to be supplied is the plumbing that the abstract statements assume and that
`Additive ↥X∞` does not carry on its own:

* `MvZpExtension.isScalarTower_Xinf`: `MvZpExtension.XinfLambdaModule` extends
  `MvZpExtension.XinfZpModule`;
* `MvZpExtension.coe_span_X_smul_top_Xinf`: the submodule `T · Additive X∞` is the subgroup
  `T X∞` of blueprint node `commutator-eq` (`Subgroup.gammaSubOne`);
* `MvZpExtension.finite_quotient_xinfSubmoduleOfSubgroup`: the `Λ`-quotient by a closed
  subgroup is finite as soon as the group quotient is.

## Main results

* `MvZpExtension.isScalarTower_Xinf`, `MvZpExtension.coe_span_X_smul_top_Xinf`.
* `MvZpExtension.moduleFinite_and_isTorsion_Xinf`: **`X∞` is a finitely generated torsion
  `Λ`-module**, from the geometric data of Step 3.
-/

open Filter Topology PowerSeries
open scoped Pointwise
open scoped PowerSeries.WithPiTopology

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf) (γ : H.GG ⧸ H.Xinf)

/-! ### The scalar tower -/

/-- **`MvZpExtension.XinfLambdaModule` extends `MvZpExtension.XinfZpModule`.**  Every statement
of `Iwasawalib.RingTheory.IwasawaAlgebra.FgTorsion` and
`Iwasawalib.RingTheory.IwasawaAlgebra.FgTorsionSpan` is stated over this tower. -/
theorem isScalarTower_Xinf :
    letI := H.XinfZpModule
    letI := H.XinfLambdaModule γ
    IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ (Additive ↥H.Xinf) :=
  letI := H.XinfUniformSpace
  haveI : IsUniformGroup ↥H.Xinf := isUniformGroup_of_commGroup
  ProP.isScalarTower_gammaLambdaModule H.isProP_Xinf' H.XinfConjQuotient
    H.continuous_XinfConjQuotient γ (H.tendsto_pow_gammaQuotient γ)

/-! ### `T · Additive X∞ = T X∞` -/

/-- **The submodule `T · Additive X∞` is the subgroup `T X∞`** of blueprint node
`commutator-eq` (`Subgroup.gammaSubOne`).  This is what makes the hypothesis `T X∞ ⊆ Y` of
`MvZpExtension.xinfSubmoduleOfSubgroup` the same as the module-theoretic `ω_0 X∞ ⊆ Y`. -/
theorem coe_span_X_smul_top_Xinf :
    letI := H.XinfLambdaModule γ
    ((Ideal.span {(X : ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ (Additive ↥H.Xinf)) :
        Submodule ℤ_[p]⟦X⟧ (Additive ↥H.Xinf)) : Set (Additive ↥H.Xinf))
      = ((Subgroup.toAddSubgroup (Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ) :
          AddSubgroup (Additive ↥H.Xinf)) : Set (Additive ↥H.Xinf)) := by
  letI := H.XinfUniformSpace
  haveI : IsUniformGroup ↥H.Xinf := isUniformGroup_of_commGroup
  refine Eq.trans (ProP.coe_span_X_smul_top_additive H.isProP_Xinf' H.XinfConjQuotient
    H.continuous_XinfConjQuotient γ (H.tendsto_pow_gammaQuotient γ)) ?_
  ext w
  simp only [Set.mem_range, SetLike.mem_coe]
  constructor
  · rintro ⟨g, rfl⟩
    rw [Subgroup.ofMul_mem_toAddSubgroup]
    rw [div_eq_mul_inv]
    exact Subgroup.conjAct_mul_inv_mem_gammaSubOne H.Xinf H.mul_comm_Xinf' γ g
  · intro hw
    obtain ⟨g, hg⟩ := (Subgroup.mem_gammaSubOne_iff H.Xinf H.mul_comm_Xinf' γ
      (Additive.toMul w)).1 hw
    refine ⟨g, ?_⟩
    rw [div_eq_mul_inv]
    exact congrArg Additive.ofMul hg

/-! ### Closed subgroups of `X∞` are `ℤ_p`-submodules -/

/-- **A closed subgroup of `X∞` is stable under the `ℤ_p`-action.**  This is
`IwasawaAlgebra.C_smul_mem_of_isClosed` — `ℤ` is dense in `ℤ_p` — read through
`MvZpExtension.XinfLambdaModule_C_smul`.  No stability under `Γ` is needed, which is the point:
`Y_n = Gal(L∞/K∞L_n)` is a `Λ`-submodule only by an extra argument, but it is a
`ℤ_p`-submodule for free, and that is all Step 3 uses. -/
theorem padicSMul_mem_toAddSubgroup_of_isClosed (S : Subgroup ↥H.Xinf)
    (hS : IsClosed (S : Set ↥H.Xinf)) (a : ℤ_[p]) {x : Additive ↥H.Xinf}
    (hx : x ∈ Subgroup.toAddSubgroup S) :
    letI := H.XinfZpModule
    a • x ∈ Subgroup.toAddSubgroup S := by
  letI := H.XinfZpModule
  letI := H.XinfLambdaModule (1 : H.GG ⧸ H.Xinf)
  haveI := H.continuousSMul_XinfLambdaModule (1 : H.GG ⧸ H.Xinf)
  have h := IwasawaAlgebra.C_smul_mem_of_isClosed (M := Additive ↥H.Xinf)
    (S := Subgroup.toAddSubgroup S) (Subgroup.isClosed_toAddSubgroup hS) hx a
  rwa [H.XinfLambdaModule_C_smul (1 : H.GG ⧸ H.Xinf) a x] at h

/-- **The `ℤ_p`-submodule of `Additive X∞` attached to a closed subgroup of `X∞`**, with the
same carrier.  Compare `MvZpExtension.xinfSubmoduleOfSubgroup`, which produces a
`Λ`-submodule but needs the extra hypothesis `T X∞ ⊆ S`. -/
noncomputable def xinfZpSubmoduleOfSubgroup (S : Subgroup ↥H.Xinf)
    (hS : IsClosed (S : Set ↥H.Xinf)) :
    letI := H.XinfZpModule
    Submodule ℤ_[p] (Additive ↥H.Xinf) :=
  letI := H.XinfZpModule
  { carrier := (Subgroup.toAddSubgroup S : AddSubgroup (Additive ↥H.Xinf))
    add_mem' := (Subgroup.toAddSubgroup S).add_mem
    zero_mem' := (Subgroup.toAddSubgroup S).zero_mem
    smul_mem' := fun a _ hx ↦ H.padicSMul_mem_toAddSubgroup_of_isClosed S hS a hx }

theorem mem_xinfZpSubmoduleOfSubgroup (S : Subgroup ↥H.Xinf)
    (hS : IsClosed (S : Set ↥H.Xinf)) (x : ↥H.Xinf) :
    letI := H.XinfZpModule
    Additive.ofMul x ∈ H.xinfZpSubmoduleOfSubgroup S hS ↔ x ∈ S := Iff.rfl

theorem coe_xinfZpSubmoduleOfSubgroup (S : Subgroup ↥H.Xinf)
    (hS : IsClosed (S : Set ↥H.Xinf)) :
    letI := H.XinfZpModule
    ((H.xinfZpSubmoduleOfSubgroup S hS : Submodule ℤ_[p] (Additive ↥H.Xinf)) :
        Set (Additive ↥H.Xinf))
      = ((Subgroup.toAddSubgroup S : AddSubgroup (Additive ↥H.Xinf)) : Set (Additive ↥H.Xinf)) :=
  rfl

/-- The `ℤ_p`-quotient of `Additive X∞` by a closed subgroup is the group quotient, so it is
finite as soon as the group quotient is. -/
theorem finite_quotient_xinfZpSubmoduleOfSubgroup (S : Subgroup ↥H.Xinf)
    (hS : IsClosed (S : Set ↥H.Xinf)) (hfin : Finite (↥H.Xinf ⧸ S)) :
    letI := H.XinfZpModule
    Finite ((Additive ↥H.Xinf) ⧸ H.xinfZpSubmoduleOfSubgroup S hS) := by
  letI := H.XinfZpModule
  haveI := hfin
  haveI : Finite (Additive ↥H.Xinf ⧸ Subgroup.toAddSubgroup S) :=
    Finite.of_equiv _ (Subgroup.additiveQuotientEquiv S).symm
  exact Finite.of_equiv _ (IwasawaAlgebra.quotientEquivQuotientAddSubgroupOfCoe
    (H.xinfZpSubmoduleOfSubgroup S hS) (Subgroup.toAddSubgroup S)
    (H.coe_xinfZpSubmoduleOfSubgroup S hS)).symm

/-! ### Finiteness of the `Λ`-quotient by `Y_n` -/

/-- The `Λ`-quotient of `Additive X∞` by a closed subgroup containing `T X∞` is finite as soon
as the group quotient is; cf. `MvZpExtension.card_quotient_xinfSubmoduleOfSubgroup`. -/
theorem finite_quotient_xinfSubmoduleOfSubgroup (S : Subgroup ↥H.Xinf)
    (hS : IsClosed (S : Set ↥H.Xinf))
    (hTS : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ S)
    (hfin : Finite (↥H.Xinf ⧸ S)) :
    letI := H.XinfLambdaModule γ
    Finite ((Additive ↥H.Xinf) ⧸ H.xinfSubmoduleOfSubgroup γ S hS hTS) := by
  letI := H.XinfLambdaModule γ
  haveI := H.continuousSMul_XinfLambdaModule γ
  haveI := hfin
  haveI : Finite (Additive ↥H.Xinf ⧸ Subgroup.toAddSubgroup S) :=
    Finite.of_equiv _ (Subgroup.additiveQuotientEquiv S).symm
  exact Finite.of_equiv _
    (IwasawaAlgebra.quotientEquivQuotientAddSubgroup (Subgroup.toAddSubgroup S)
      (Subgroup.isClosed_toAddSubgroup hS) (H.X_smul_mem_of_gammaSubOne_le γ hTS)).symm

/-! ### From topological to algebraic generation -/

set_option synthInstance.maxHeartbeats 800000 in
/-- **The blueprint's topological generation hypothesis suffices.**  In the blueprint `Y_e` is
defined as the *closure* of the subgroup generated by `ω_e X∞` and `a₂, …, a_s`; this lemma
converts `Y ⊆ closure(ℤ_p·a + ω_e X∞)` into the algebraic containment `Y ⊆ ℤ_p·a + ω_e X∞`
that `MvZpExtension.moduleFinite_and_isTorsion_Xinf` asks for.  The point is
`IwasawaAlgebra.isClosed_coe_span_sup`: `ℤ_p·a` is compact because `ℤ_p` is, and `ω_e X∞` is
compact because `X∞` is. -/
theorem xinfZpSubmoduleOfSubgroup_le_span_sup_of_le_topologicalClosure (S : Subgroup ↥H.Xinf)
    (hS : IsClosed (S : Set ↥H.Xinf)) (a : Finset (Additive ↥H.Xinf)) (e : ℕ)
    (h : letI := H.XinfZpModule
      letI := H.XinfLambdaModule γ
      haveI := H.isScalarTower_Xinf γ
      haveI := H.continuousSMul_XinfZpModule
      H.xinfZpSubmoduleOfSubgroup S hS ≤
        (Submodule.span ℤ_[p] (a : Set (Additive ↥H.Xinf)) ⊔
          ((Ideal.span {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ e) : Polynomial ℤ_[p]) :
              ℤ_[p]⟦X⟧)} •
            (⊤ : Submodule ℤ_[p]⟦X⟧ (Additive ↥H.Xinf))).restrictScalars
              ℤ_[p])).topologicalClosure) :
    letI := H.XinfZpModule
    letI := H.XinfLambdaModule γ
    haveI := H.isScalarTower_Xinf γ
    H.xinfZpSubmoduleOfSubgroup S hS ≤
      Submodule.span ℤ_[p] (a : Set (Additive ↥H.Xinf)) ⊔
        ((Ideal.span {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ e) : Polynomial ℤ_[p]) :
            ℤ_[p]⟦X⟧)} •
          (⊤ : Submodule ℤ_[p]⟦X⟧ (Additive ↥H.Xinf))).restrictScalars ℤ_[p]) := by
  letI := H.XinfZpModule
  letI := H.XinfLambdaModule γ
  haveI := H.isScalarTower_Xinf γ
  haveI := H.continuousSMul_XinfZpModule
  haveI := H.continuousSMul_XinfLambdaModule γ
  haveI := H.t2Space_additive_Xinf
  exact IwasawaAlgebra.le_span_sup_of_le_topologicalClosure _ a _ h

/-! ### Step 3 on `X∞` -/

set_option synthInstance.maxHeartbeats 800000 in
/-- **Blueprint node `Xn-isom-qout-of-totally-ramified`, Step 3, on `X∞`.**  Let `e : ℕ`, let
`Y` be a closed subgroup of `X∞` of finite index, let `a` be a finite subset of `Additive X∞`
with `Y ⊆ ℤ_p·a + ω_e X∞`, and suppose `X∞ / ν_{n,e} Y` is finite for every `n ≥ e`.  Then
`Additive X∞` is a finitely generated torsion `Λ`-module.

`Y` is not assumed stable under `Γ`: closedness alone makes it a `ℤ_p`-submodule
(`MvZpExtension.xinfZpSubmoduleOfSubgroup`), and that is all Step 3 needs.  In the blueprint
`e` is a layer above which `K∞ / K_e` is totally ramified, `Y` is `Gal(L∞/L_e K∞) = Y_e`, `a`
is `a₂, …, a_s` (one element for each ramified prime beyond the first), `ν_{n,e} Y_e = Y_n` is
Step 2, and `X∞ / Y_n ≅ X_n = Gal(K∞ L_n / K∞)` is finite by class field theory
(`MvZpExtension.finite_quotient_YnIn`). -/
theorem moduleFinite_and_isTorsion_Xinf (e : ℕ)
    (Y : Subgroup ↥H.Xinf) (hYcl : IsClosed (Y : Set ↥H.Xinf))
    (a : Finset (Additive ↥H.Xinf))
    (hMY : Finite (↥H.Xinf ⧸ Y))
    (hY : letI := H.XinfZpModule
      letI := H.XinfLambdaModule γ
      haveI := H.isScalarTower_Xinf γ
      H.xinfZpSubmoduleOfSubgroup Y hYcl ≤
        Submodule.span ℤ_[p] (a : Set (Additive ↥H.Xinf)) ⊔
          ((Ideal.span {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ e) : Polynomial ℤ_[p]) :
              ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ (Additive ↥H.Xinf))).restrictScalars ℤ_[p]))
    (hfin : letI := H.XinfZpModule
      letI := H.XinfLambdaModule γ
      haveI := H.isScalarTower_Xinf γ
      ∀ n : ℕ, e ≤ n → Finite ((Additive ↥H.Xinf) ⧸ Submodule.map
        (IwasawaAlgebra.lsmulZp (Additive ↥H.Xinf)
          ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧))
        (H.xinfZpSubmoduleOfSubgroup Y hYcl))) :
    letI := H.XinfZpModule
    letI := H.XinfLambdaModule γ
    Module.Finite ℤ_[p]⟦X⟧ (Additive ↥H.Xinf) ∧
      Module.IsTorsion ℤ_[p]⟦X⟧ (Additive ↥H.Xinf) := by
  letI := H.XinfZpModule
  letI := H.XinfLambdaModule γ
  haveI := H.isScalarTower_Xinf γ
  haveI := H.continuousSMul_XinfLambdaModule γ
  haveI := H.t2Space_additive_Xinf
  exact IwasawaAlgebra.moduleFinite_and_isTorsion_of_le_span
    (H.xinfZpSubmoduleOfSubgroup Y hYcl) a e
    (H.finite_quotient_xinfZpSubmoduleOfSubgroup Y hYcl hMY) hY hfin

/-! ### `Y_n`, and the class-field-theoretic input `X_n` is finite -/

/-- **`X∞ / Y_n ≅ X_n = Gal(K∞L_n/K∞)` is finite.**

**Warning**: like `MvZpExtension.finrank_Ln`, this depends on the class field theory `sorry`s
in `Iwasawalib.NumberTheory.NumberField.HilbertClassField.ClassFieldTheory`, through
`MvZpExtension.finiteDimensional_Ln'`.  It is the only class-field-theoretic input of
`MvZpExtension.moduleFinite_and_isTorsion_Xinf_Yn`; the theorem
`MvZpExtension.moduleFinite_and_isTorsion_Xinf` itself is free of it. -/
theorem finite_quotient_YnIn (n : ℕ) : Finite (↥H.Xinf ⧸ H.YnIn n) :=
  Finite.of_equiv _ (H.xinfInQuotientYnMulEquiv n).toEquiv.symm

/-- **`Finite (Additive X∞ ⧸ Y_n)`**: the quotient of `Additive X∞` by the closed
`ℤ_p`-submodule `Y_n` is finite.  Same class field theory warning as
`MvZpExtension.finite_quotient_YnIn`. -/
theorem finite_quotient_YnZpSubmodule (n : ℕ) :
    letI := H.XinfZpModule
    Finite ((Additive ↥H.Xinf) ⧸ H.xinfZpSubmoduleOfSubgroup (H.YnIn n) (H.isClosed_YnIn n)) :=
  H.finite_quotient_xinfZpSubmoduleOfSubgroup (H.YnIn n) (H.isClosed_YnIn n)
    (H.finite_quotient_YnIn n)

/-- **`Finite (Additive X∞ ⧸ Y_n)` for the `Λ`-submodule `Y_n`.**  Same class field theory
warning as `MvZpExtension.finite_quotient_YnIn`. -/
theorem finite_quotient_YnSubmodule (n : ℕ)
    (hTY : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ H.YnIn n) :
    letI := H.XinfLambdaModule γ
    Finite ((Additive ↥H.Xinf) ⧸ H.YnSubmodule γ n hTY) :=
  H.finite_quotient_xinfSubmoduleOfSubgroup γ (H.YnIn n) (H.isClosed_YnIn n) hTY
    (H.finite_quotient_YnIn n)

set_option synthInstance.maxHeartbeats 800000 in
/-- **Blueprint node `Xn-isom-qout-of-totally-ramified`, Step 3, with `Y = Y_e`.**  Exactly two
hypotheses remain:

* `hY`: `Y_e ⊆ ℤ_p·a + ω_e X∞` — the blueprint's description of `Y_e` as topologically
  generated over `ℤ_p` by `ω_e X∞` and the `s - 1` elements `a₂, …, a_s`, in the only form
  Step 3 uses;
* `hstep2`: `ν_{n,e} Y_e = Y_n`, which is Step 2 of the node.  It is discharged from the same
  generator description, by `MvZpExtension.hstep2_of_generators`.

  Two claims this docstring previously made about `hstep2` were wrong, and are corrected here.
  Its core is **not** `MvZpExtension.nu_smul_topologicalClosure_sup_span_Xinf` /
  `IwasawaAlgebra.nu_smul_sup_span`: those are `Λ`-span statements, whereas `hstep2` is a
  `ℤ_p`-span statement about `Submodule.map (IwasawaAlgebra.lsmulZp ν)`; the usable partner is
  `IwasawaAlgebra.map_lsmulZp_span_sup`.  And the remark that modulo `ν_{n,e} ω_e X∞` the
  elements `ν_{n,e} a_i` are `γ`-fixed is **not needed** for `hstep2` as stated -- that remark
  is the blueprint's device for matching a closed `Λ`-submodule with a closed subgroup, and at
  the `ℤ_p` level its role is taken by
  `IwasawaAlgebra.topologicalClosure_closure_union_eq_span_sup`.

The finiteness of `X∞ / Y_n`, which in the blueprint is `X_n ≅ A_n` finite, is discharged here
by `MvZpExtension.finite_quotient_YnIn`; it is class field theory, and it is the reason this
theorem — unlike `MvZpExtension.moduleFinite_and_isTorsion_Xinf` — depends on the `sorry`s of
`Iwasawalib.NumberTheory.NumberField.HilbertClassField.ClassFieldTheory`. -/
theorem moduleFinite_and_isTorsion_Xinf_Yn (e : ℕ) (a : Finset (Additive ↥H.Xinf))
    (hY : letI := H.XinfZpModule
      letI := H.XinfLambdaModule γ
      haveI := H.isScalarTower_Xinf γ
      H.xinfZpSubmoduleOfSubgroup (H.YnIn e) (H.isClosed_YnIn e) ≤
        Submodule.span ℤ_[p] (a : Set (Additive ↥H.Xinf)) ⊔
          ((Ideal.span {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ e) : Polynomial ℤ_[p]) :
              ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ (Additive ↥H.Xinf))).restrictScalars ℤ_[p]))
    (hstep2 : letI := H.XinfZpModule
      letI := H.XinfLambdaModule γ
      haveI := H.isScalarTower_Xinf γ
      ∀ n : ℕ, e ≤ n → Submodule.map
          (IwasawaAlgebra.lsmulZp (Additive ↥H.Xinf)
            ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧))
          (H.xinfZpSubmoduleOfSubgroup (H.YnIn e) (H.isClosed_YnIn e))
        = H.xinfZpSubmoduleOfSubgroup (H.YnIn n) (H.isClosed_YnIn n)) :
    letI := H.XinfZpModule
    letI := H.XinfLambdaModule γ
    Module.Finite ℤ_[p]⟦X⟧ (Additive ↥H.Xinf) ∧
      Module.IsTorsion ℤ_[p]⟦X⟧ (Additive ↥H.Xinf) := by
  letI := H.XinfZpModule
  letI := H.XinfLambdaModule γ
  haveI := H.isScalarTower_Xinf γ
  refine H.moduleFinite_and_isTorsion_Xinf γ e (H.YnIn e) (H.isClosed_YnIn e) a
    (H.finite_quotient_YnIn e) hY fun n hn ↦ ?_
  rw [hstep2 n hn]
  exact H.finite_quotient_YnZpSubmodule n

end MvZpExtension
