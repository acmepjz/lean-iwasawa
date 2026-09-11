/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.FreeQuotientCard
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

@[expose] public section

/-!
# Quotient of a power series ring by a distinguished polynomial

Let `A` be a complete local ring and `g` a distinguished polynomial of degree `d` over `A`
(`Polynomial.IsDistinguishedAt`). We show that `A⟦X⟧ ⧸ (g)` is a free `A`-module with basis
`1, X, ..., X ^ (d - 1)`. This is blueprint node `quotient-by-distinguished` (i).

## Main results

* `Polynomial.Monic.basisQuotient`: for monic `g`, a basis of `A[X] ⧸ (g)`.
* `Polynomial.IsDistinguishedAt.basisQuotientPowerSeries`: for distinguished `g`, a basis of
  `A⟦X⟧ ⧸ (g)`.
* `Polynomial.IsDistinguishedAt.finrank_quotient_powerSeries`: its rank is `g.natDegree`.
-/

open Polynomial PowerSeries

namespace Polynomial

/-- `AdjoinRoot g` is by definition `A[X] ⧸ (g)`; this is the identity isomorphism between
the two spellings. -/
@[simps! apply]
def adjoinRootAlgEquivQuotient {A : Type*} [CommRing A] (g : A[X]) :
    AdjoinRoot g ≃ₐ[A] (A[X] ⧸ Ideal.span {g}) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- For a monic polynomial `g` of degree `d` over a commutative ring `A`, the quotient
`A[X] ⧸ (g)` is a free `A`-module with basis `1, X, ..., X ^ (d - 1)`. -/
noncomputable def Monic.basisQuotient {A : Type*} [CommRing A] {g : A[X]} (hg : g.Monic) :
    Module.Basis (Fin g.natDegree) A (A[X] ⧸ Ideal.span {g}) :=
  ((AdjoinRoot.powerBasis' hg).basis.map
    (adjoinRootAlgEquivQuotient g).toLinearEquiv).reindex (finCongr (by simp))

theorem Monic.basisQuotient_apply {A : Type*} [CommRing A] {g : A[X]} (hg : g.Monic)
    (i : Fin g.natDegree) :
    hg.basisQuotient i = Ideal.Quotient.mk _ (X ^ (i : ℕ)) := by
  rw [Monic.basisQuotient, Module.Basis.reindex_apply, Module.Basis.map_apply,
    PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen]
  simp only [AdjoinRoot.root, AdjoinRoot.mk, adjoinRootAlgEquivQuotient, map_pow]
  rfl

namespace IsDistinguishedAt

variable {A : Type*} [CommRing A] {I : Ideal A} {g : A[X]} (H : g.IsDistinguishedAt I)
  [IsAdicComplete I A]

include H

/-- If `g` is a distinguished polynomial of degree `d` over a complete local ring `A`, then
`A⟦X⟧ ⧸ (g)` is a free `A`-module with basis `1, X, ..., X ^ (d - 1)`. -/
noncomputable def basisQuotientPowerSeries :
    Module.Basis (Fin g.natDegree) A (A⟦X⟧ ⧸ Ideal.span {(g : A⟦X⟧)}) :=
  H.monic.basisQuotient.map H.algEquivQuotient.toLinearEquiv

theorem basisQuotientPowerSeries_apply (i : Fin g.natDegree) :
    H.basisQuotientPowerSeries i = Ideal.Quotient.mk _ ((PowerSeries.X : A⟦X⟧) ^ (i : ℕ)) := by
  rw [basisQuotientPowerSeries, Module.Basis.map_apply, H.monic.basisQuotient_apply]
  simp

@[simp]
theorem algEquivQuotient_mk (f : A[X]) :
    H.algEquivQuotient (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (f : A⟦X⟧) := rfl

theorem free_quotient_powerSeries : Module.Free A (A⟦X⟧ ⧸ Ideal.span {(g : A⟦X⟧)}) :=
  .of_basis H.basisQuotientPowerSeries

theorem finite_quotient_powerSeries : Module.Finite A (A⟦X⟧ ⧸ Ideal.span {(g : A⟦X⟧)}) :=
  .of_basis H.basisQuotientPowerSeries

theorem finrank_quotient_powerSeries [Nontrivial A] :
    Module.finrank A (A⟦X⟧ ⧸ Ideal.span {(g : A⟦X⟧)}) = g.natDegree := by
  rw [Module.finrank_eq_card_basis H.basisQuotientPowerSeries, Fintype.card_fin]

/-- If `x` is an element of `A⟦X⟧ ⧸ (g)` which is divisible by `a ^ n` for all `n`, where
`a` is an element of `A` such that `⋂ n, (a ^ n) = 0` in `A`, then `x = 0`. This is the
separatedness input needed for the Iwasawa algebra isomorphism. -/
theorem eq_zero_of_forall_mem_smul_pow {a : A}
    (ha : ∀ c : A, (∀ n : ℕ, c ∈ Ideal.span {a ^ n}) → c = 0)
    (x : A⟦X⟧ ⧸ Ideal.span {(g : A⟦X⟧)})
    (hx : ∀ n : ℕ, ∃ y, x = a ^ n • y) : x = 0 := by
  classical
  have key : ∀ i, H.basisQuotientPowerSeries.repr x i = 0 := by
    intro i
    refine ha _ fun n ↦ ?_
    obtain ⟨y, hy⟩ := hx n
    rw [hy, map_smul, Finsupp.smul_apply, smul_eq_mul, Ideal.mem_span_singleton]
    exact Dvd.intro _ rfl
  have : H.basisQuotientPowerSeries.repr x = 0 := by ext i; exact key i
  simpa using congr(H.basisQuotientPowerSeries.repr.symm $this)

/-- **Blueprint node `quotient-by-distinguished` (ii)**: if `g` is a distinguished polynomial
of degree `d` over a complete local ring `A` with principal maximal ideal `(a)`, then
`#(A⟦X⟧ ⧸ (a, g)) = #(A ⧸ (a)) ^ d`. For `A = ℤ_p` and `a = p ^ m` this says
`ord_p #(Λ ⧸ (p ^ m, g)) = m * d`. -/
theorem card_quotient_span_pair (a : A) :
    Nat.card (A⟦X⟧ ⧸ Ideal.span {algebraMap A A⟦X⟧ a, (g : A⟦X⟧)}) =
      Nat.card (A ⧸ Ideal.span {a}) ^ g.natDegree := by
  classical
  have hsplit : Ideal.span {algebraMap A A⟦X⟧ a, (g : A⟦X⟧)} =
      Ideal.span {(g : A⟦X⟧)} ⊔ Ideal.span {algebraMap A A⟦X⟧ a} := by
    rw [Ideal.span_insert, sup_comm]
  have hmap : Ideal.map (Ideal.Quotient.mk (Ideal.span {(g : A⟦X⟧)}))
      (Ideal.span {algebraMap A A⟦X⟧ a}) =
      Ideal.span {algebraMap A (A⟦X⟧ ⧸ Ideal.span {(g : A⟦X⟧)}) a} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [hsplit, ← Nat.card_congr (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {(g : A⟦X⟧)})
    (Ideal.span {algebraMap A A⟦X⟧ a})).toEquiv, hmap,
    Nat.card_congr (Ideal.quotientEquivQuotientOfCarrierEq _ (Ideal.span {a} • ⊤)
      (Ideal.coe_span_algebraMap_eq a)),
    H.basisQuotientPowerSeries.card_quotient_smul_top, Fintype.card_fin]

end IsDistinguishedAt

end Polynomial
