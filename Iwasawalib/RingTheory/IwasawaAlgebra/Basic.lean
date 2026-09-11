/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.CyclicGroupAlgebra
public import Iwasawalib.RingTheory.IwasawaAlgebra.InverseLimitOmega
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section

/-!
# The Iwasawa algebra

This file proves that the inverse limit of the group algebras `A[ZMod (p ^ n)]` is isomorphic
to the power series ring `A⟦X⟧`, where the group element `1` corresponds to `1 + X`.
This is blueprint node `Iwasawa-alg-isom`.
-/

open Polynomial PowerSeries

namespace IwasawaAlgebra

variable (A : Type*) [CommRing A] [Nontrivial A] (p : ℕ) [Fact p.Prime]

instance (n : ℕ) : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

section

variable (n : ℕ)

omit [Nontrivial A] [Fact p.Prime] in
/-- The automorphism `X ↦ X + 1` of `A[X]` carries `X ^ (p ^ n) - 1` to `ω_n`. -/
theorem map_span_X_pow_sub_one :
    Ideal.map (algEquivAevalXAddC (1 : A) : A[X] →+* A[X])
      (Ideal.span {(Polynomial.X ^ (p ^ n) - 1 : A[X])}) =
      Ideal.span {Polynomial.oneAddXPowSubOne A (p ^ n)} := by
  rw [Ideal.map_span]
  congr 1
  rw [Set.image_singleton]
  simp only [RingHom.coe_coe, map_sub, map_pow, algEquivAevalXAddC_apply, map_one]
  rw [Polynomial.oneAddXPowSubOne_def, aeval_X, add_comm]

omit [Nontrivial A] in
/-- `A[X] ⧸ (X ^ (p ^ n) - 1) ≃ₐ[A] A[X] ⧸ (ω_n)`, induced by `X ↦ X + 1`. -/
noncomputable def quotXPowSubOneEquivQuotOmega :
    (A[X] ⧸ Ideal.span {(Polynomial.X ^ (p ^ n) - 1 : A[X])}) ≃ₐ[A]
      (A[X] ⧸ Ideal.span {Polynomial.oneAddXPowSubOne A (p ^ n)}) :=
  Ideal.quotientEquivAlg _ _ (algEquivAevalXAddC (1 : A)) (map_span_X_pow_sub_one A p n).symm

omit [Nontrivial A] [Fact p.Prime] in
@[simp]
theorem quotXPowSubOneEquivQuotOmega_mk (f : A[X]) :
    quotXPowSubOneEquivQuotOmega A p n (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (algEquivAevalXAddC (1 : A) f) := rfl

end

omit [Nontrivial A] in
/-- Two `A`-algebra homomorphisms out of a monoid algebra `A[M]` agree if they agree on the
group elements. -/
theorem _root_.MonoidAlgebra.algHom_ext_single {M B : Type*} [Monoid M] [CommRing B] [Algebra A B]
    {φ₁ φ₂ : MonoidAlgebra A M →ₐ[A] B}
    (h : ∀ k : M, φ₁ (MonoidAlgebra.single k 1) = φ₂ (MonoidAlgebra.single k 1)) : φ₁ = φ₂ :=
  (MonoidAlgebra.lift A B M).symm.injective (MonoidHom.ext h)

variable [IsAdicComplete (Ideal.span {(p : A)}) A] (n : ℕ)

omit [Nontrivial A] [IsAdicComplete (Ideal.span {(p : A)}) A] in
/-- The level-`n` isomorphism `A[ZMod (p ^ n)] ≃ₐ[A] A⟦X⟧ ⧸ (ω_n)`, sending the group element
`k` to `(1 + X) ^ k`. -/
noncomputable def levelEquiv :
    MonoidAlgebra A (Multiplicative (ZMod (p ^ n))) ≃ₐ[A]
      (A⟦X⟧ ⧸ PowerSeries.omegaIdeal A p n) :=
  (CyclicGroupAlgebra.algEquiv A (p ^ n)).trans
    ((quotXPowSubOneEquivQuotOmega A p n).trans
      (Polynomial.isDistinguishedAt_oneAddXPowSubOne A p n).algEquivQuotient)

theorem levelEquiv_single (k : Multiplicative (ZMod (p ^ n))) :
    levelEquiv A p n (MonoidAlgebra.single k 1) =
      Ideal.Quotient.mk _ ((1 + PowerSeries.X) ^ (Multiplicative.toAdd k).val) := by
  rw [levelEquiv]
  simp only [AlgEquiv.trans_apply, CyclicGroupAlgebra.algEquiv_single,
    quotXPowSubOneEquivQuotOmega_mk, map_pow, algEquivAevalXAddC_apply, aeval_X,
    ]
  simp only [Polynomial.IsDistinguishedAt.algEquivQuotient_mk]
  congr 2
  push_cast
  rw [map_one, add_comm]

omit [Nontrivial A] [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : A)}) A] in
/-- The class of `1 + X` in `A⟦X⟧ ⧸ (ω_n)` has order dividing `p ^ n`. -/
theorem one_add_X_pow_eq_one :
    (Ideal.Quotient.mk (PowerSeries.omegaIdeal A p n) (1 + PowerSeries.X)) ^ p ^ n = 1 := by
  rw [← map_pow, show (1 : A⟦X⟧ ⧸ PowerSeries.omegaIdeal A p n)
    = Ideal.Quotient.mk _ 1 from rfl, Ideal.Quotient.eq]
  refine Ideal.subset_span ?_
  rw [Set.mem_singleton_iff, PowerSeries.omega, Polynomial.oneAddXPowSubOne_def]
  push_cast
  rw [add_comm]

variable {p}

theorem val_castHom_modEq {n m : ℕ} (h : n ≤ m) (k : ZMod (p ^ m)) :
    ((ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n))) k).val ≡ k.val [MOD p ^ n] := by
  rw [ZMod.castHom_apply, ← ZMod.natCast_val k, ZMod.val_natCast]
  exact Nat.mod_modEq _ _

variable (p)

/-- The transition map `ZMod (p ^ m) → ZMod (p ^ n)` for `n ≤ m`, multiplicatively. -/
def zmodTransHom {n m : ℕ} (h : n ≤ m) :
    Multiplicative (ZMod (p ^ m)) →* Multiplicative (ZMod (p ^ n)) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n))).toAddMonoidHom

/-- The transition maps of the inverse system `(A[ZMod (p ^ n)])_n`. -/
noncomputable def groupTrans ⦃n m : ℕ⦄ (h : n ≤ m) :
    MonoidAlgebra A (Multiplicative (ZMod (p ^ m))) →ₐ[A]
      MonoidAlgebra A (Multiplicative (ZMod (p ^ n))) :=
  MonoidAlgebra.mapDomainAlgHom A A (zmodTransHom p h)

/-- The level isomorphisms are compatible with the transition maps. -/
theorem levelEquiv_comp ⦃n m : ℕ⦄ (h : n ≤ m) :
    (PowerSeries.omegaFactor A p h).comp (levelEquiv A p m : _ →ₐ[A] _) =
      (levelEquiv A p n : _ →ₐ[A] _).comp (groupTrans A p h) := by
  refine MonoidAlgebra.algHom_ext_single A fun k ↦ ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
    levelEquiv_single, groupTrans, MonoidAlgebra.mapDomainAlgHom_apply]
  rw [MonoidAlgebra.mapDomain_single]
  rw [levelEquiv_single]
  show PowerSeries.omegaFactor A p h _ = _
  rw [PowerSeries.omegaFactor, map_pow]
  refine pow_eq_pow_of_modEq ?_ (one_add_X_pow_eq_one A p n)
  exact (val_castHom_modEq h (Multiplicative.toAdd k)).symm

/-- **The Iwasawa algebra isomorphism**: the inverse limit of the group algebras
`A[ZMod (p ^ n)]` is isomorphic to `A⟦X⟧`, with the group element `1` at each level
corresponding to `1 + X`. -/
noncomputable def inverseLimitEquiv :
    Algebra.InverseLimit (groupTrans A p) ≃ₐ[A] A⟦X⟧ :=
  (Algebra.InverseLimit.congr (PowerSeries.omegaFactor A p) (groupTrans A p) (levelEquiv A p)
    (levelEquiv_comp A p)).trans
    (PowerSeries.equivInverseLimitOmega A p).symm

section PadicInt

variable (p : ℕ) [Fact p.Prime]

instance isAdicComplete_span_p : IsAdicComplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] :=
  PadicInt.maximalIdeal_eq_span_p (p := p) ▸
    (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p])

theorem toZModPow_surjective (m : ℕ) :
    Function.Surjective (PadicInt.toZModPow m : ℤ_[p] →+* ZMod (p ^ m)) := fun a ↦
  ⟨((a.val : ℕ) : ℤ_[p]), by rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]⟩

/-- `ℤ_p ⧸ (p ^ m)` has exactly `p ^ m` elements. -/
theorem card_quotient_padicInt_span_p_pow (m : ℕ) :
    Nat.card (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m}) = p ^ m := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [← PadicInt.ker_toZModPow m,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (toZModPow_surjective p m)).toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-- **Blueprint node `quotient-by-distinguished` (ii)** for the Iwasawa algebra:
`ord_p #(Λ ⧸ (p ^ m, F)) = m * deg F` for a distinguished polynomial `F`. -/
theorem card_quotient_span_p_pow_distinguished {F : ℤ_[p][X]}
    (H : F.IsDistinguishedAt (Ideal.span {(p : ℤ_[p])})) (m : ℕ) :
    Nat.card (ℤ_[p]⟦X⟧ ⧸ Ideal.span
      {algebraMap ℤ_[p] ℤ_[p]⟦X⟧ ((p : ℤ_[p]) ^ m), (F : ℤ_[p]⟦X⟧)}) =
      p ^ (m * F.natDegree) := by
  rw [H.card_quotient_span_pair, card_quotient_padicInt_span_p_pow, ← pow_mul]

/-- **The Iwasawa algebra** `Λ = ℤ_p[[Γ]]`, for `Γ ≅ ℤ_p` presented as the inverse limit of
the finite cyclic groups `ZMod (p ^ n)`, is isomorphic to `ℤ_p⟦X⟧`, the topological
generator corresponding to `1 + X`. This is blueprint node `Iwasawa-alg-isom`. -/
noncomputable def padicInverseLimitEquiv :
    Algebra.InverseLimit (groupTrans ℤ_[p] p) ≃ₐ[ℤ_[p]] ℤ_[p]⟦X⟧ :=
  inverseLimitEquiv ℤ_[p] p

end PadicInt

end IwasawaAlgebra
