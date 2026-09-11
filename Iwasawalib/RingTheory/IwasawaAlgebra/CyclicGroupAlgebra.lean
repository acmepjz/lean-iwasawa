/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.QuotientDistinguished
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# The group algebra of a finite cyclic group

For a commutative ring `A` and `m ≠ 0` we construct the isomorphism of `A`-algebras
`A[Multiplicative (ZMod m)] ≃ₐ[A] A[X] ⧸ (X ^ m - 1)` sending the group element `k` to
`X ^ k.val`.
-/

open Polynomial

namespace ZMod

/-- For `m ≠ 0`, the equivalence `ZMod m ≃ Fin m` given by `a ↦ a.val`. -/
def equivFinVal (m : ℕ) [NeZero m] : ZMod m ≃ Fin m where
  toFun a := ⟨a.val, ZMod.val_lt a⟩
  invFun i := ((i : ℕ) : ZMod m)
  left_inv a := by simp
  right_inv i := by ext; simp [ZMod.val_natCast_of_lt i.2]

@[simp]
theorem equivFinVal_apply {m : ℕ} [NeZero m] (a : ZMod m) :
    ((equivFinVal m a : Fin m) : ℕ) = a.val := rfl

end ZMod

namespace MonoidAlgebra

variable {M : Type*} [Monoid M]

/-- If `u ^ m = 1` in a monoid `M`, then `k ↦ u ^ k.val` is a monoid homomorphism
`Multiplicative (ZMod m) →* M`. -/
def zmodPowHom (m : ℕ) [NeZero m] (u : M) (hu : u ^ m = 1) : Multiplicative (ZMod m) →* M where
  toFun k := u ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    show u ^ (ZMod.val (Multiplicative.toAdd a + Multiplicative.toAdd b)) = _
    rw [← pow_add]
    exact pow_eq_pow_of_modEq (by rw [ZMod.val_add]; exact Nat.mod_modEq _ _) hu

@[simp]
theorem zmodPowHom_apply (m : ℕ) [NeZero m] (u : M) (hu : u ^ m = 1)
    (k : Multiplicative (ZMod m)) :
    zmodPowHom m u hu k = u ^ (Multiplicative.toAdd k).val := rfl

end MonoidAlgebra

namespace CyclicGroupAlgebra

open MonoidAlgebra

variable (A : Type*) [CommRing A] (m : ℕ) [NeZero m]

/-- The polynomial `X ^ m - 1`. -/
theorem monic_X_pow_sub_one : (X ^ m - 1 : A[X]).Monic := by
  simpa using monic_X_pow_sub_C (1 : A) (NeZero.ne m)

omit [NeZero m] in
theorem natDegree_X_pow_sub_one [Nontrivial A] : (X ^ m - 1 : A[X]).natDegree = m := by
  simpa using natDegree_X_pow_sub_C (R := A) (n := m) (r := 1)

/-- The class of `X` in `A[X] ⧸ (X ^ m - 1)`. -/
noncomputable def xClass : A[X] ⧸ Ideal.span {(X ^ m - 1 : A[X])} :=
  Ideal.Quotient.mk _ X

omit [NeZero m] in
theorem xClass_pow_eq_one : xClass A m ^ m = 1 := by
  rw [xClass, ← map_pow, show (1 : A[X] ⧸ Ideal.span {(X ^ m - 1 : A[X])})
    = Ideal.Quotient.mk _ 1 from rfl, Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

/-- The `A`-algebra homomorphism `A[Multiplicative (ZMod m)] → A[X] ⧸ (X ^ m - 1)`
sending the group element `k` to `X ^ k.val`. -/
noncomputable def toQuotient :
    A[Multiplicative (ZMod m)] →ₐ[A] (A[X] ⧸ Ideal.span {(X ^ m - 1 : A[X])}) :=
  MonoidAlgebra.lift A _ _ (zmodPowHom m (xClass A m) (xClass_pow_eq_one A m))

@[simp]
theorem toQuotient_single (k : Multiplicative (ZMod m)) :
    toQuotient A m (MonoidAlgebra.single k 1) =
      Ideal.Quotient.mk _ (X ^ (Multiplicative.toAdd k).val) := by
  rw [toQuotient, ← MonoidAlgebra.of_apply, MonoidAlgebra.lift_of, zmodPowHom_apply, xClass,
    ← map_pow]

theorem toQuotient_bijective [Nontrivial A] : Function.Bijective (toQuotient A m) := by
  classical
  set b1 : Module.Basis (Multiplicative (ZMod m)) A A[Multiplicative (ZMod m)] :=
    MonoidAlgebra.basis _ _ with hb1
  set b2 := (monic_X_pow_sub_one A m).basisQuotient with hb2
  set e : Multiplicative (ZMod m) ≃ Fin (X ^ m - 1 : A[X]).natDegree :=
    (ZMod.equivFinVal m).trans (finCongr (natDegree_X_pow_sub_one A m).symm) with he
  have hmap : ∀ k, toQuotient A m (b1 k) = b2 (e k) := by
    intro k
    rw [hb1, MonoidAlgebra.basis_apply, toQuotient_single, hb2,
      Polynomial.Monic.basisQuotient_apply]
    congr 2
  have hlin : (toQuotient A m).toLinearMap =
      (b1.equiv b2 e : A[Multiplicative (ZMod m)] →ₗ[A] _) := by
    refine b1.ext fun k ↦ ?_
    simp only [AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply]
    exact hmap k
  have hfun : ⇑(toQuotient A m) = ⇑(b1.equiv b2 e) := congrArg DFunLike.coe hlin
  rw [hfun]
  exact (b1.equiv b2 e).bijective

/-- **The group algebra of a finite cyclic group**:
`A[Multiplicative (ZMod m)] ≃ₐ[A] A[X] ⧸ (X ^ m - 1)`. -/
noncomputable def algEquiv [Nontrivial A] :
    A[Multiplicative (ZMod m)] ≃ₐ[A] (A[X] ⧸ Ideal.span {(X ^ m - 1 : A[X])}) :=
  AlgEquiv.ofBijective (toQuotient A m) (toQuotient_bijective A m)

@[simp]
theorem algEquiv_single [Nontrivial A] (k : Multiplicative (ZMod m)) :
    algEquiv A m (MonoidAlgebra.single k 1) =
      Ideal.Quotient.mk _ (X ^ (Multiplicative.toAdd k).val) :=
  toQuotient_single A m k

end CyclicGroupAlgebra
