/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.XinfInertia
public import Iwasawalib.NumberTheory.ZpExtension.XinfLambda
public import Iwasawalib.NumberTheory.ZpExtension.Yn
public import Iwasawalib.RingTheory.IwasawaAlgebra.ClosedSubmodule
public import Iwasawalib.RingTheory.IwasawaAlgebra.NuSubmodule

@[expose] public section

/-!
# The subgroup ↔ `Λ`-submodule dictionary for `X∞`

`MvZpExtension.Yn` and `MvZpExtension.YnIn` are `Subgroup`s of a *multiplicative* Galois group,
while the `Λ`-module structure of blueprint node `X-has-Gamma-action`
(`MvZpExtension.XinfLambdaModule`) lives on `Additive ↥H.Xinf`.  Step 2 of blueprint node
`Xn-isom-qout-of-totally-ramified` (`Y_n = ν_{n,e} Y`,
`IwasawaAlgebra.nu_smul_topologicalClosure_sup_span`) is a statement about `Λ`-submodules.  This
file is the dictionary between the two.

The content is `IwasawaAlgebra.smul_mem_of_isClosed_of_X_smul_mem`: a *closed* additive subgroup
stable under the single scalar `X` is a `Λ`-submodule.  On `X∞` the scalar `X` acts as
`x ↦ (γ x γ⁻¹) x⁻¹` (`MvZpExtension.XinfLambdaModule_X_smul`), so `X`-stability of a subgroup
`S ⊆ X∞` is exactly the containment `T X∞ ⊆ S` of blueprint node `commutator-eq`, i.e.
`Subgroup.gammaSubOne H.Xinf _ γ ≤ S` — the same hypothesis that
`MvZpExtension.xinfQuotientMulEquivOfPlace'` already asks for.  So **every closed subgroup of
`X∞` containing `T X∞` is a closed `Λ`-submodule of `Additive X∞`, with the same carrier and
the same quotient**.

Closedness is what makes this work: it is used twice, to run the `ℤ ⊆ ℤ_p` limit and the
polynomial-density limit in `IwasawaAlgebra.smul_mem_of_isClosed_of_X_smul_mem`.

## Main definitions

* `MvZpExtension.xinfSubmoduleOfSubgroup`: the `Λ`-submodule attached to a closed subgroup of
  `X∞` containing `T X∞`.
* `MvZpExtension.YnSubmodule`: the case `S = Y_n`.

## Main results

* `MvZpExtension.X_smul_mem_of_gammaSubOne_le`: `T X∞ ⊆ S` gives `X`-stability.
* `MvZpExtension.card_quotient_xinfSubmoduleOfSubgroup`: the `Λ`-quotient and the group
  quotient have the same cardinality.
* `MvZpExtension.nu_smul_topologicalClosure_sup_span_Xinf`: blueprint node
  `Xn-isom-qout-of-totally-ramified`, Step 2, transported to `Additive X∞`.
* `MvZpExtension.isClosed_YnIn`: `Y_n` is closed in `X∞`.
-/

open Filter Topology PowerSeries
open scoped PowerSeries.WithPiTopology

/-! ### Multiplicative subgroups as additive subgroups -/

namespace Subgroup

variable {G : Type*} [Group G]

theorem mem_toAddSubgroup (S : Subgroup G) (x : Additive G) :
    x ∈ Subgroup.toAddSubgroup S ↔ Additive.toMul x ∈ S := Iff.rfl

theorem ofMul_mem_toAddSubgroup (S : Subgroup G) (x : G) :
    Additive.ofMul x ∈ Subgroup.toAddSubgroup S ↔ x ∈ S := Iff.rfl

theorem isClosed_toAddSubgroup [TopologicalSpace G] {S : Subgroup G}
    (hS : IsClosed (S : Set G)) :
    IsClosed ((Subgroup.toAddSubgroup S : AddSubgroup (Additive G)) : Set (Additive G)) := hS

/-- The quotient of `Additive G` by `S.toAddSubgroup` is the quotient of `G` by `S`. -/
def additiveQuotientEquiv (S : Subgroup G) :
    (Additive G ⧸ Subgroup.toAddSubgroup S) ≃ (G ⧸ S) :=
  Quotient.congr (Equiv.refl G) fun a b ↦ by
    rw [QuotientAddGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    exact Iff.rfl

theorem card_additiveQuotient (S : Subgroup G) :
    Nat.card (Additive G ⧸ Subgroup.toAddSubgroup S) = Nat.card (G ⧸ S) :=
  Nat.card_congr (additiveQuotientEquiv S)

end Subgroup

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf) (γ : H.GG ⧸ H.Xinf)

/-! ### `X`-stability -/

/-- **`T X∞ ⊆ S` is exactly `X`-stability of `S`.**  `X` acts on `Additive X∞` as
`x ↦ (γ x γ⁻¹) x⁻¹` (`MvZpExtension.XinfLambdaModule_X_smul`), and those elements are by
definition the elements of `T X∞ = Subgroup.gammaSubOne`. -/
theorem X_smul_mem_of_gammaSubOne_le {S : Subgroup ↥H.Xinf}
    (hTS : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ S)
    (x : Additive ↥H.Xinf) (hx : x ∈ Subgroup.toAddSubgroup S) :
    letI := H.XinfLambdaModule γ
    (X : ℤ_[p]⟦X⟧) • x ∈ Subgroup.toAddSubgroup S := by
  letI := H.XinfLambdaModule γ
  obtain ⟨y, rfl⟩ : ∃ y : ↥H.Xinf, Additive.ofMul y = x := ⟨Additive.toMul x, rfl⟩
  rw [H.XinfLambdaModule_X_smul γ y, Subgroup.ofMul_mem_toAddSubgroup]
  have hmem : (H.XinfConjQuotient γ y : ↥H.Xinf) / y ∈
      Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ := by
    rw [div_eq_mul_inv]
    exact Subgroup.conjAct_mul_inv_mem_gammaSubOne H.Xinf H.mul_comm_Xinf' γ y
  exact hTS hmem

/-! ### The dictionary -/

/-- **The `Λ`-submodule of `Additive X∞` attached to a closed subgroup `S ⊆ X∞` containing
`T X∞`**, with the same carrier. -/
noncomputable def xinfSubmoduleOfSubgroup (S : Subgroup ↥H.Xinf)
    (hS : IsClosed (S : Set ↥H.Xinf))
    (hTS : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ S) :
    letI := H.XinfLambdaModule γ
    Submodule ℤ_[p]⟦X⟧ (Additive ↥H.Xinf) :=
  letI := H.XinfLambdaModule γ
  haveI := H.continuousSMul_XinfLambdaModule γ
  IwasawaAlgebra.submoduleOfAddSubgroup (Subgroup.toAddSubgroup S)
    (Subgroup.isClosed_toAddSubgroup hS) (H.X_smul_mem_of_gammaSubOne_le γ hTS)

theorem mem_xinfSubmoduleOfSubgroup (S : Subgroup ↥H.Xinf)
    (hS : IsClosed (S : Set ↥H.Xinf))
    (hTS : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ S) (x : ↥H.Xinf) :
    letI := H.XinfLambdaModule γ
    Additive.ofMul x ∈ H.xinfSubmoduleOfSubgroup γ S hS hTS ↔ x ∈ S := Iff.rfl

theorem isClosed_xinfSubmoduleOfSubgroup (S : Subgroup ↥H.Xinf)
    (hS : IsClosed (S : Set ↥H.Xinf))
    (hTS : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ S) :
    letI := H.XinfLambdaModule γ
    IsClosed ((H.xinfSubmoduleOfSubgroup γ S hS hTS : Submodule ℤ_[p]⟦X⟧ (Additive ↥H.Xinf)) :
      Set (Additive ↥H.Xinf)) := hS

/-- **The `Λ`-quotient is the group quotient.**  This is the form in which the dictionary feeds
the hypothesis `hcard` of `MvZpExtension.exists_multiplicity_classNumber_of_card_eq`. -/
theorem card_quotient_xinfSubmoduleOfSubgroup (S : Subgroup ↥H.Xinf)
    (hS : IsClosed (S : Set ↥H.Xinf))
    (hTS : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ S) :
    letI := H.XinfLambdaModule γ
    Nat.card ((Additive ↥H.Xinf) ⧸ H.xinfSubmoduleOfSubgroup γ S hS hTS)
      = Nat.card (↥H.Xinf ⧸ S) := by
  letI := H.XinfLambdaModule γ
  haveI := H.continuousSMul_XinfLambdaModule γ
  refine Eq.trans ?_ (Subgroup.card_additiveQuotient S)
  exact IwasawaAlgebra.card_quotient_submoduleOfAddSubgroup _ _ _

end MvZpExtension

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-! ### `Yₙ` is closed -/

/-- `Yₙ = Gal(L∞/K∞Lₙ)` is a closed subgroup of `Gal(L∞/K∞)`. -/
theorem isClosed_Yn (n : ℕ) : IsClosed ((H.Yn n : Subgroup Gal(↥H.Linf/Kinf)) :
    Set Gal(↥H.Linf/Kinf)) :=
  InfiniteGalois.fixingSubgroup_isClosed (H.Ln'In n)

/-- **`Yₙ` is a closed subgroup of `X∞`**, `X∞` being read inside `G = Gal(L∞/K)`.  This is one
of the two hypotheses of `MvZpExtension.xinfSubmoduleOfSubgroup`. -/
theorem isClosed_YnIn (n : ℕ) : IsClosed ((H.YnIn n : Subgroup ↥H.Xinf) : Set ↥H.Xinf) :=
  (H.isClosed_Yn n).preimage H.continuous_xinfHom

end MvZpExtension

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf) (γ : H.GG ⧸ H.Xinf)

/-! ### `Yₙ` as a `Λ`-submodule -/

/-- **`Yₙ` as a closed `Λ`-submodule of `Additive X∞`.**  The hypothesis `hTY` is the blueprint's
prerequisite that `K∞Lₙ / Kₙ` be abelian, in the form `T X∞ ⊆ Yₙ`; it is the same hypothesis
that `MvZpExtension.xinfQuotientMulEquivOfPlace'` asks for. -/
noncomputable def YnSubmodule (n : ℕ)
    (hTY : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ H.YnIn n) :
    letI := H.XinfLambdaModule γ
    Submodule ℤ_[p]⟦X⟧ (Additive ↥H.Xinf) :=
  H.xinfSubmoduleOfSubgroup γ (H.YnIn n) (H.isClosed_YnIn n) hTY

theorem mem_YnSubmodule (n : ℕ)
    (hTY : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ H.YnIn n) (x : ↥H.Xinf) :
    letI := H.XinfLambdaModule γ
    Additive.ofMul x ∈ H.YnSubmodule γ n hTY ↔ x ∈ H.YnIn n := Iff.rfl

theorem isClosed_YnSubmodule (n : ℕ)
    (hTY : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ H.YnIn n) :
    letI := H.XinfLambdaModule γ
    IsClosed ((H.YnSubmodule γ n hTY : Submodule ℤ_[p]⟦X⟧ (Additive ↥H.Xinf)) :
      Set (Additive ↥H.Xinf)) :=
  H.isClosed_xinfSubmoduleOfSubgroup γ (H.YnIn n) (H.isClosed_YnIn n) hTY

/-- **`X∞ / Yₙ = Xₙ`, counted.**  The `Λ`-module quotient `Additive X∞ / Yₙ` has the
cardinality of `Xₙ = Gal(K∞Lₙ/K∞)`.  This is the shape in which the dictionary feeds the
hypothesis `hcard` of `MvZpExtension.exists_multiplicity_classNumber_of_card_eq`. -/
theorem card_quotient_YnSubmodule (n : ℕ)
    (hTY : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ H.YnIn n) :
    letI := H.XinfLambdaModule γ
    Nat.card ((Additive ↥H.Xinf) ⧸ H.YnSubmodule γ n hTY)
      = Nat.card Gal(↥(H.Ln' n)/Kinf) := by
  letI := H.XinfLambdaModule γ
  letI : (H.YnIn n).Normal := Subgroup.normal_comap _
  refine Eq.trans (H.card_quotient_xinfSubmoduleOfSubgroup γ (H.YnIn n) (H.isClosed_YnIn n) hTY) ?_
  exact Nat.card_congr (H.xinfInQuotientYnMulEquiv n).toEquiv

end MvZpExtension

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf) (γ : H.GG ⧸ H.Xinf)

/-! ### Step 2 of `Xn-isom-qout-of-totally-ramified`, transported to `X∞` -/

set_option synthInstance.maxHeartbeats 400000 in
/-- The topological instances that `IwasawaAlgebra.nu_smul_topologicalClosure_sup_span` needs on
`Additive X∞`, collected so that they are found once rather than searched for at each use.  The
`T2Space` instance in particular has to be handed over from `↥X∞` explicitly: searching for it
directly on the type synonym `Additive ↥X∞` exhausts the synthesis budget. -/
theorem t2Space_additive_Xinf : T2Space (Additive ↥H.Xinf) :=
  (inferInstance : T2Space ↥H.Xinf)

open scoped Pointwise in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Blueprint node `Xn-isom-qout-of-totally-ramified`, Step 2, on `X∞`.**
`ν_{n,e} · Y = Yₙ`, where `Y` is the closed `Λ`-submodule of `Additive X∞` generated by
`ω_e X∞` and a set `A`, and `Yₙ` the one generated by `ω_n X∞` and `ν_{n,e} · A`.  This is
`IwasawaAlgebra.nu_smul_topologicalClosure_sup_span` transported across
`MvZpExtension.XinfLambdaModule`. -/
theorem nu_smul_topologicalClosure_sup_span_Xinf (A : Set (Additive ↥H.Xinf)) {n e : ℕ}
    (h : e ≤ n) :
    letI := H.XinfLambdaModule γ
    haveI := H.continuousSMul_XinfLambdaModule γ
    haveI := H.t2Space_additive_Xinf
    ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) •
        ((Ideal.span {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ e) : Polynomial ℤ_[p]) :
              ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ (Additive ↥H.Xinf))) ⊔
            Submodule.span ℤ_[p]⟦X⟧ A).topologicalClosure
      = ((Ideal.span {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) :
            ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ (Additive ↥H.Xinf))) ⊔
          Submodule.span ℤ_[p]⟦X⟧
            (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • A)
          ).topologicalClosure :=
  letI := H.XinfLambdaModule γ
  haveI := H.continuousSMul_XinfLambdaModule γ
  haveI := H.t2Space_additive_Xinf
  IwasawaAlgebra.nu_smul_topologicalClosure_sup_span A h

end MvZpExtension
