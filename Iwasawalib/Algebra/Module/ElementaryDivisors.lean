/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

/-!
# Elementary divisors and the cardinality of a cokernel

Let `u` be an injective endomorphism of a free `ℤ_p`-module `M` of finite rank. By the theory
of elementary divisors (Smith normal form over a PID, available in Mathlib as
`Submodule.quotientEquivPiSpan`) the cokernel of `u` is finite of cardinality
`p ^ v(det u)`, where `v` is the `p`-adic valuation.

This is the linear algebra input of blueprint node `quotient-by-distinguished` (iii).

## Main results

* `PadicInt.card_quotient_span_pow`, `PadicInt.card_quotient_span_singleton`: the cardinality of
  `ℤ_p ⧸ (a)`.
* `Submodule.associated_det_prod_smithNormalFormCoeffs`: over a PID, the determinant of an
  isomorphism `M ≃ N ⊆ M` onto a submodule of the same rank is associated to the product of
  the Smith normal form coefficients.
* `PadicInt.card_quotient_range`: `#coker(u) = p ^ v(det u)`.
-/

open Module Submodule

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

theorem toZModPow_surjective (n : ℕ) :
    Function.Surjective (toZModPow n : ℤ_[p] →+* ZMod (p ^ n)) := fun a ↦
  ⟨((a.val : ℕ) : ℤ_[p]), by rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]⟩

theorem card_quotient_span_pow (n : ℕ) :
    Nat.card (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ n}) = p ^ n := by
  rw [← ker_toZModPow n, Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (toZModPow_surjective n)).toEquiv, Nat.card_zmod]

theorem card_quotient_span_singleton {a : ℤ_[p]} (ha : a ≠ 0) :
    Nat.card (ℤ_[p] ⧸ Ideal.span {a}) = p ^ a.valuation := by
  have hspan : Ideal.span {a} = Ideal.span {(p : ℤ_[p]) ^ a.valuation} := by
    conv_lhs => rw [unitCoeff_spec ha]
    rw [Ideal.span_singleton_mul_left_unit (unitCoeff ha).isUnit]
  rw [hspan, card_quotient_span_pow]

end PadicInt

namespace Submodule

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [IsDomain R] [IsPrincipalIdealRing R] [Fintype ι] [DecidableEq ι]

theorem det_smithNormalFormEquiv (b : Basis ι R M) {N : Submodule R M}
    (h : Module.finrank R N = Module.finrank R M) :
    LinearMap.det (N.subtype ∘ₗ
        ((smithNormalFormTopBasis b h).equiv (smithNormalFormBotBasis b h)
          (Equiv.refl ι) : M →ₗ[R] N)) = ∏ i, smithNormalFormCoeffs b h i := by
  set a := smithNormalFormCoeffs b h with ha
  set b' := smithNormalFormTopBasis b h with hb'
  set ab := smithNormalFormBotBasis b h with hab
  set f : M →ₗ[R] M := N.subtype ∘ₗ (b'.equiv ab (Equiv.refl ι) : M →ₗ[R] N) with hf
  have hfb : ∀ i, f (b' i) = a i • b' i := by
    intro i
    show ((b'.equiv ab (Equiv.refl ι) (b' i) : N) : M) = _
    rw [Basis.equiv_apply, Equiv.refl_apply]
    exact smithNormalFormBotBasis_def b h i
  rw [← LinearMap.det_toMatrix b' f]
  have : LinearMap.toMatrix b' b' f = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, hfb, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  rw [this, Matrix.det_diagonal]

theorem associated_det_prod_smithNormalFormCoeffs (b : Basis ι R M) {N : Submodule R M}
    (e : M ≃ₗ[R] N) (h : Module.finrank R N = Module.finrank R M) :
    Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N)))
      (∏ i, smithNormalFormCoeffs b h i) := by
  rw [← det_smithNormalFormEquiv b h]
  exact LinearMap.associated_det_comp_equiv _ _ _

end Submodule

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

theorem valuation_eq_zero_of_isUnit {x : ℤ_[p]} (hx : IsUnit x) : x.valuation = 0 := by
  obtain ⟨u, rfl⟩ := hx
  have h1 : (u : ℤ_[p]) ≠ 0 := u.ne_zero
  have h2 : ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ≠ 0 := (u⁻¹).ne_zero
  have := valuation_mul h1 h2
  rw [Units.mul_inv, valuation_one] at this
  omega

theorem valuation_eq_of_associated {x y : ℤ_[p]} (h : Associated x y) :
    x.valuation = y.valuation := by
  obtain ⟨u, rfl⟩ := h
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [valuation_mul hx u.ne_zero, valuation_eq_zero_of_isUnit u.isUnit, add_zero]

theorem valuation_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ_[p]) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).valuation = ∑ i ∈ s, (f i).valuation := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    have h0 : ∏ i ∈ s, f i ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert has, Finset.sum_insert has,
      valuation_mul (hf a (Finset.mem_insert_self a s)) h0,
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

end PadicInt

section Coker

open Module

variable {p : ℕ} [Fact p.Prime] {ι M : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [Module ℤ_[p] M]

/-- **Elementary divisors**: if `u` is an injective endomorphism of a free `ℤ_p`-module of
finite rank, then `#coker(u) = p ^ v(det u)`. -/
theorem PadicInt.card_quotient_range (b : Basis ι ℤ_[p] M) (u : M →ₗ[ℤ_[p]] M)
    (hu : Function.Injective u) :
    Nat.card (M ⧸ LinearMap.range u) = p ^ (LinearMap.det u).valuation := by
  haveI : Module.Finite ℤ_[p] M := Module.Finite.of_basis b
  set N := LinearMap.range u with hN
  have h : Module.finrank ℤ_[p] N = Module.finrank ℤ_[p] M :=
    (LinearEquiv.ofInjective u hu).finrank_eq.symm
  set a := Submodule.smithNormalFormCoeffs b h with ha
  have hane : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h
  have hdet : Associated (LinearMap.det u) (∏ i, a i) := by
    have he : N.subtype ∘ₗ ((LinearEquiv.ofInjective u hu) : M →ₗ[ℤ_[p]] N) = u :=
      LinearMap.ext fun x ↦ rfl
    rw [← he]
    exact Submodule.associated_det_prod_smithNormalFormCoeffs b _ h
  rw [PadicInt.valuation_eq_of_associated hdet,
    PadicInt.valuation_prod _ _ (fun i _ ↦ hane i),
    Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]
  rw [Finset.prod_congr rfl (fun i _ ↦ PadicInt.card_quotient_span_singleton (hane i)),
    ← Finset.prod_pow_eq_pow_sum]

end Coker
