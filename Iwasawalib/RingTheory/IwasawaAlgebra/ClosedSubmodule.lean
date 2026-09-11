/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.LambdaTopology
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Module.Basic

@[expose] public section

/-!
# A closed `X`-stable subgroup of a topological `Λ`-module is a `Λ`-submodule

Over `Λ = ℤ_p⟦X⟧` a *closed* additive subgroup `S` of a topological `Λ`-module needs only one
extra property to be a `Λ`-submodule: stability under the single scalar `X`.  Indeed the set of
`r` with `r • x ∈ S` is closed, contains the constants (because `ℤ` is dense in `ℤ_p` and `S` is
a closed subgroup), and is stable under multiplication by `X`; so it contains every polynomial,
and polynomials are dense in `ℤ_p⟦X⟧` (`PowerSeries.WithPiTopology.denseRange_toPowerSeries`).

This is the coefficient-side half of the dictionary that lets the closed *subgroups* `Y_n` of a
Galois group be read as closed `Λ`-*submodules*, which is what blueprint node
`Xn-isom-qout-of-totally-ramified`, Step 2, needs in order to apply
`IwasawaAlgebra.nu_smul_topologicalClosure_sup_span`.  The group-side half is
`MvZpExtension.xinfSubmoduleOfSubgroup`.

## Main results

* `IwasawaAlgebra.C_smul_mem_of_isClosed`: a closed additive subgroup is `ℤ_p`-stable.
* `IwasawaAlgebra.smul_mem_of_isClosed_of_X_smul_mem`: a closed `X`-stable additive subgroup is
  `Λ`-stable.
* `IwasawaAlgebra.submoduleOfAddSubgroup`: the resulting `Λ`-submodule.
-/

open Filter Topology PowerSeries
open scoped PowerSeries.WithPiTopology

namespace IwasawaAlgebra

variable {p : ℕ} [Fact p.Prime]
variable {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M] [TopologicalSpace M]
  [ContinuousSMul ℤ_[p]⟦X⟧ M]

/-- For a fixed `x`, the set of scalars carrying `x` into a closed set is closed. -/
theorem isClosed_setOf_smul_mem {S : Set M} (hS : IsClosed S) (x : M) :
    IsClosed {r : ℤ_[p]⟦X⟧ | r • x ∈ S} :=
  hS.preimage (continuous_id.smul continuous_const)

/-- **A closed additive subgroup of a topological `Λ`-module is stable under the constants
`ℤ_p ⊆ Λ`.**  The integers are dense in `ℤ_p` and an additive subgroup is stable under them. -/
theorem C_smul_mem_of_isClosed {S : AddSubgroup M} (hS : IsClosed (S : Set M))
    {x : M} (hx : x ∈ S) (a : ℤ_[p]) : (C a : ℤ_[p]⟦X⟧) • x ∈ S := by
  have hcl : IsClosed {a : ℤ_[p] | (C a : ℤ_[p]⟦X⟧) • x ∈ S} :=
    (isClosed_setOf_smul_mem hS x).preimage WithPiTopology.continuous_C
  have hrange : Set.range ((↑) : ℤ → ℤ_[p]) ⊆ {a : ℤ_[p] | (C a : ℤ_[p]⟦X⟧) • x ∈ S} := by
    rintro _ ⟨k, rfl⟩
    have hCk : (C ((k : ℤ) : ℤ_[p]) : ℤ_[p]⟦X⟧) = ((k : ℤ) : ℤ_[p]⟦X⟧) :=
      map_intCast (C : ℤ_[p] →+* ℤ_[p]⟦X⟧) k
    show (C ((k : ℤ) : ℤ_[p]) : ℤ_[p]⟦X⟧) • x ∈ S
    rw [hCk, Int.cast_smul_eq_zsmul]
    exact S.zsmul_mem hx k
  have := closure_minimal hrange hcl
  rw [PadicInt.denseRange_intCast.closure_range] at this
  exact this (Set.mem_univ a)

/-- **A closed `X`-stable additive subgroup of a topological `Λ`-module is a `Λ`-submodule.**
Polynomials are dense in `ℤ_p⟦X⟧`, and the polynomials carrying `x` into `S` already form
everything: the constants by `IwasawaAlgebra.C_smul_mem_of_isClosed`, the powers of `X` by
hypothesis. -/
theorem smul_mem_of_isClosed_of_X_smul_mem {S : AddSubgroup M} (hS : IsClosed (S : Set M))
    (hX : ∀ x ∈ S, (X : ℤ_[p]⟦X⟧) • x ∈ S) {x : M} (hx : x ∈ S) (r : ℤ_[p]⟦X⟧) :
    r • x ∈ S := by
  have hXn : ∀ n : ℕ, ((X : ℤ_[p]⟦X⟧) ^ n) • x ∈ S := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
        rw [pow_succ', mul_smul]
        exact hX _ ih
  have hpoly : ∀ q : Polynomial ℤ_[p], ((q : ℤ_[p]⟦X⟧)) • x ∈ S := by
    intro q
    induction q using Polynomial.induction_on' with
    | add f g hf hg => rw [Polynomial.coe_add, add_smul]; exact S.add_mem hf hg
    | monomial n a =>
        rw [Polynomial.coe_monomial, PowerSeries.monomial_eq_C_mul_X_pow, mul_smul]
        exact C_smul_mem_of_isClosed hS (hXn n) a
  have hrange : Set.range (Polynomial.toPowerSeries (R := ℤ_[p])) ⊆
      {r : ℤ_[p]⟦X⟧ | r • x ∈ S} := by
    rintro _ ⟨q, rfl⟩
    exact hpoly q
  have := closure_minimal hrange (isClosed_setOf_smul_mem hS x)
  rw [(WithPiTopology.denseRange_toPowerSeries ℤ_[p]).closure_range] at this
  exact this (Set.mem_univ r)

/-- **The `Λ`-submodule attached to a closed `X`-stable additive subgroup**, with the same
carrier. -/
def submoduleOfAddSubgroup (S : AddSubgroup M) (hS : IsClosed (S : Set M))
    (hX : ∀ x ∈ S, (X : ℤ_[p]⟦X⟧) • x ∈ S) : Submodule ℤ_[p]⟦X⟧ M where
  carrier := S
  add_mem' := S.add_mem
  zero_mem' := S.zero_mem
  smul_mem' r _ hx := smul_mem_of_isClosed_of_X_smul_mem hS hX hx r

@[simp]
theorem mem_submoduleOfAddSubgroup {S : AddSubgroup M} {hS : IsClosed (S : Set M)}
    {hX : ∀ x ∈ S, (X : ℤ_[p]⟦X⟧) • x ∈ S} {x : M} :
    x ∈ submoduleOfAddSubgroup S hS hX ↔ x ∈ S := Iff.rfl

@[simp]
theorem coe_submoduleOfAddSubgroup (S : AddSubgroup M) (hS : IsClosed (S : Set M))
    (hX : ∀ x ∈ S, (X : ℤ_[p]⟦X⟧) • x ∈ S) :
    (submoduleOfAddSubgroup S hS hX : Set M) = (S : Set M) := rfl

/-- The quotient of `M` by `IwasawaAlgebra.submoduleOfAddSubgroup S` is, as a type, the
quotient of `M` by the additive subgroup `S`. -/
noncomputable def quotientEquivQuotientAddSubgroup (S : AddSubgroup M) (hS : IsClosed (S : Set M))
    (hX : ∀ x ∈ S, (X : ℤ_[p]⟦X⟧) • x ∈ S) :
    (M ⧸ submoduleOfAddSubgroup S hS hX) ≃ (M ⧸ S) :=
  Quotient.congr (Equiv.refl M) fun a b ↦ by
    rw [Submodule.quotientRel_def, QuotientAddGroup.leftRel_apply]
    show a - b ∈ S ↔ -a + b ∈ S
    rw [neg_add_eq_sub]
    constructor
    · intro h; simpa using S.neg_mem h
    · intro h; simpa using S.neg_mem h

theorem card_quotient_submoduleOfAddSubgroup (S : AddSubgroup M) (hS : IsClosed (S : Set M))
    (hX : ∀ x ∈ S, (X : ℤ_[p]⟦X⟧) • x ∈ S) :
    Nat.card (M ⧸ submoduleOfAddSubgroup S hS hX) = Nat.card (M ⧸ S) :=
  Nat.card_congr (quotientEquivQuotientAddSubgroup S hS hX)

theorem isClosed_submoduleOfAddSubgroup (S : AddSubgroup M) (hS : IsClosed (S : Set M))
    (hX : ∀ x ∈ S, (X : ℤ_[p]⟦X⟧) • x ∈ S) :
    IsClosed ((submoduleOfAddSubgroup S hS hX : Submodule ℤ_[p]⟦X⟧ M) : Set M) := hS

end IwasawaAlgebra
