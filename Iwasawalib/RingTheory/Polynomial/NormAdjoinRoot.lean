/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Norm.Basic

@[expose] public section

/-!
# The norm of an element of `AdjoinRoot F` for a monic polynomial `F`

Let `F` be a monic polynomial over a commutative ring `R` and let `G : R[X]`. The quotient
`R[X] ⧸ (F)`, spelled `AdjoinRoot F`, is a free `R`-module with basis `1, X, ..., X ^ (d - 1)`
where `d = deg F`, so that the multiplication by the class of `G` has a determinant, namely
`Algebra.norm R (AdjoinRoot.mk F G)`.

This file proves the two facts about that determinant which are needed for blueprint node
`quotient-by-distinguished` (iii):

* it is computed by an explicit matrix (`AdjoinRoot.norm_mk_eq_det_mulMatrix`) whose entries
  are polynomial coefficients, so that it commutes with base change along an arbitrary ring
  homomorphism (`AdjoinRoot.map_norm_mk`);
* over an algebraically closed field it equals `∏_α G(α)`, the product being over the roots of
  `F` counted with multiplicity (`AdjoinRoot.norm_mk_eq_prod_roots`).
-/

open Polynomial Matrix

namespace AdjoinRoot

section Matrix

variable {R : Type*} [CommRing R]

/-- The matrix of the multiplication by `G` on `R[X] ⧸ (F)`, in the basis
`1, X, ..., X ^ (d - 1)`: its `(i, j)` entry is the `i`-th coefficient of `G * X ^ j mod F`. -/
noncomputable def mulMatrix (F G : R[X]) : Matrix (Fin F.natDegree) (Fin F.natDegree) R :=
  Matrix.of fun i j ↦ ((G * X ^ (j : ℕ)) %ₘ F).coeff (i : ℕ)

theorem mulMatrix_apply (F G : R[X]) (i j : Fin F.natDegree) :
    mulMatrix F G i j = ((G * X ^ (j : ℕ)) %ₘ F).coeff (i : ℕ) := rfl

/-- The norm of `G` in `R[X] ⧸ (F)` is the determinant of the explicit matrix `mulMatrix F G`. -/
theorem norm_mk_eq_det_mulMatrix {F : R[X]} (hF : F.Monic) (G : R[X]) :
    Algebra.norm R (mk F G) = (mulMatrix F G).det := by
  classical
  rw [Algebra.norm_eq_matrix_det (powerBasis' hF).basis]
  congr 1
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, mulMatrix_apply]
  have hbj : (powerBasis' hF).basis j = mk F (X ^ (j : ℕ)) := by
    simp only [PowerBasis.coe_basis, powerBasis'_gen]
    rw [root, ← map_pow]
  rw [hbj, ← map_mul]
  exact congrArg (fun q ↦ Polynomial.coeff q (i : ℕ)) (modByMonicHom_mk hF _)

/-- The matrix `mulMatrix` commutes with base change. -/
theorem mulMatrix_map {S : Type*} [CommRing S] [Nontrivial S] (φ : R →+* S) {F : R[X]}
    (hF : F.Monic)
    (G : R[X]) (i j : Fin F.natDegree) :
    ((mulMatrix F G).map φ) i j =
      (mulMatrix (F.map φ) (G.map φ))
        ((finCongr (hF.natDegree_map φ).symm) i) ((finCongr (hF.natDegree_map φ).symm) j) := by
  rw [Matrix.map_apply, mulMatrix_apply, mulMatrix_apply, ← Polynomial.coeff_map,
    Polynomial.map_modByMonic φ hF]
  simp

/-- The norm of `G` in `R[X] ⧸ (F)` commutes with base change along any ring homomorphism. -/
theorem map_norm_mk {S : Type*} [CommRing S] [Nontrivial S] (φ : R →+* S) {F : R[X]}
    (hF : F.Monic) (G : R[X]) :
    φ (Algebra.norm R (mk F G)) = Algebra.norm S (mk (F.map φ) (G.map φ)) := by
  rw [norm_mk_eq_det_mulMatrix hF, norm_mk_eq_det_mulMatrix (hF.map φ), RingHom.map_det,
    ← Matrix.det_submatrix_equiv_self (finCongr (hF.natDegree_map φ).symm)
      (mulMatrix (F.map φ) (G.map φ))]
  congr 1
  ext i j
  exact mulMatrix_map φ hF G i j

end Matrix

section Field

variable {K : Type*} [Field K] {F : K[X]} (hF : F.Monic)

include hF

theorem finrank_adjoinRoot : Module.finrank K (AdjoinRoot F) = F.natDegree := by
  haveI : Module.Finite K (AdjoinRoot F) := Module.Finite.of_basis (powerBasis' hF).basis
  rw [(powerBasis' hF).finrank, powerBasis'_dim]

/-- The characteristic polynomial of the multiplication by `root F` is `F` itself. -/
theorem charpoly_lmul_root [Module.Free K (AdjoinRoot F)] [Module.Finite K (AdjoinRoot F)] :
    LinearMap.charpoly (Algebra.lmul K (AdjoinRoot F) (root F)) = F := by
  set c := LinearMap.charpoly (Algebra.lmul K (AdjoinRoot F) (root F)) with hc
  have hcm : c.Monic := LinearMap.charpoly_monic _
  have hcd : c.natDegree = F.natDegree := by
    rw [hc, LinearMap.charpoly_natDegree, finrank_adjoinRoot hF]
  have hmin : minpoly K (root F) = F := by
    have := minpoly_powerBasis_gen_of_monic (K := K) hF hF.ne_zero
    rwa [powerBasis_gen] at this
  have hdvd : F ∣ c := by
    rw [← hmin]
    exact minpoly.dvd _ _ (Algebra.aeval_self_charpoly_lmul (root F))
  obtain ⟨e, he⟩ := hdvd
  have hene : e ≠ 0 := by
    rintro rfl
    exact hcm.ne_zero (by simp [he])
  have : e.natDegree = 0 := by
    have := congrArg Polynomial.natDegree he
    rw [Polynomial.natDegree_mul hF.ne_zero hene] at this
    omega
  have hemonic : e.Monic := hF.of_mul_monic_left (he ▸ hcm)
  rw [he, hemonic.natDegree_eq_zero.mp this, mul_one]

/-- The norm of `root F - β` is `(-1) ^ d * F(β)`. -/
theorem norm_root_sub_algebraMap (β : K) :
    Algebra.norm K (root F - algebraMap K (AdjoinRoot F) β) =
      (-1) ^ F.natDegree * F.eval β := by
  haveI : Module.Free K (AdjoinRoot F) := Module.Free.of_basis (powerBasis' hF).basis
  haveI : Module.Finite K (AdjoinRoot F) := Module.Finite.of_basis (powerBasis' hF).basis
  have heq : (algebraMap K (Module.End K (AdjoinRoot F))) β
      - Algebra.lmul K (AdjoinRoot F) (root F)
      = Algebra.lmul K (AdjoinRoot F) (algebraMap K (AdjoinRoot F) β - root F) := by
    ext x
    simp [Algebra.smul_def]
  have key : F.eval β = Algebra.norm K (algebraMap K (AdjoinRoot F) β - root F) := by
    rw [Algebra.norm_apply, ← heq, ← LinearMap.eval_charpoly, charpoly_lmul_root hF]
  rw [key, show root F - algebraMap K (AdjoinRoot F) β =
      (-1 : AdjoinRoot F) * (algebraMap K (AdjoinRoot F) β - root F) by ring,
    map_mul, show (-1 : AdjoinRoot F) = algebraMap K (AdjoinRoot F) (-1) by simp,
    Algebra.norm_algebraMap, finrank_adjoinRoot hF]

variable [IsAlgClosed K]

omit hF in
theorem card_roots : Multiset.card F.roots = F.natDegree :=
  Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits F)

/-- **The determinant formula**: over an algebraically closed field, the norm of `G` in
`K[X] ⧸ (F)` is the product of the values of `G` at the roots of `F`, counted with
multiplicity. -/
theorem norm_mk_eq_prod_roots (G : K[X]) :
    Algebra.norm K (mk F G) = (F.roots.map G.eval).prod := by
  rcases Nat.eq_zero_or_pos F.natDegree with hd | hd
  · have hr : F.roots = 0 := Multiset.card_eq_zero.mp (by rw [card_roots, hd])
    rw [norm_mk_eq_det_mulMatrix hF, hr, Matrix.det_eq_one_of_card_eq_zero (by simp [hd])]
    simp
  haveI : Module.Free K (AdjoinRoot F) := Module.Free.of_basis (powerBasis' hF).basis
  haveI : Module.Finite K (AdjoinRoot F) := Module.Finite.of_basis (powerBasis' hF).basis
  have hcard : 0 < Multiset.card F.roots := by rw [card_roots]; exact hd
  have hstep : ∀ a : K, Algebra.norm K (mk F (X - C a)) = (-1) ^ F.natDegree * F.eval a := by
    intro a
    rw [show mk F (X - C a) = root F - algebraMap K (AdjoinRoot F) a by
      rw [map_sub]; rfl, norm_root_sub_algebraMap hF]
  have hprodstep : ∀ a : K,
      (F.roots.map fun α ↦ α - a).prod = (-1) ^ F.natDegree * F.eval a := by
    intro a
    rw [(IsAlgClosed.splits F).eval_eq_prod_roots_of_monic hF a,
      show (fun α ↦ α - a) = (fun α ↦ (-1 : K) * (a - α)) by funext α; ring,
      Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, card_roots]
  rcases eq_or_ne G 0 with rfl | hG
  · obtain ⟨α, hα⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
    haveI : Nontrivial (AdjoinRoot F) :=
      AdjoinRoot.nontrivial F (by
        rw [Polynomial.degree_eq_natDegree hF.ne_zero]; exact_mod_cast hd.ne')
    rw [map_zero, Algebra.norm_zero]
    exact (Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨α, hα, by simp⟩)).symm
  set c := G.leadingCoeff with hc
  have hGsplit : G = C c * (G.roots.map fun a ↦ X - C a).prod :=
    (IsAlgClosed.splits G).eq_prod_roots
  have h1 : mk F G = mk F (C c) * (G.roots.map fun a ↦ mk F (X - C a)).prod := by
    conv_lhs => rw [hGsplit]
    rw [map_mul, map_multiset_prod, Multiset.map_map]
    rfl
  have h2 : Algebra.norm K (mk F (C c)) = c ^ F.natDegree := by
    rw [show mk F (C c) = algebraMap K (AdjoinRoot F) c from rfl, Algebra.norm_algebraMap,
      finrank_adjoinRoot hF]
  have hrhs : (F.roots.map G.eval).prod
      = c ^ F.natDegree * (F.roots.map fun α ↦ (G.roots.map fun a ↦ α - a).prod).prod := by
    rw [Multiset.map_congr rfl (fun α _ ↦ (IsAlgClosed.splits G).eval_eq_prod_roots α),
      Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, card_roots]
  rw [h1, map_mul, map_multiset_prod, Multiset.map_map, h2]
  simp only [Function.comp_def]
  rw [Multiset.map_congr rfl (fun a _ ↦ hstep a), hrhs,
    Multiset.prod_map_prod_map F.roots G.roots (f := fun α a ↦ α - a),
    Multiset.map_congr rfl (fun a _ ↦ hprodstep a)]

/-- A cross-check of `norm_mk_eq_prod_roots`, in particular of the sign in
`norm_root_sub_algebraMap`: combined with Mathlib's independent computation of the norm of the
generator of `AdjoinRoot F` through the constant coefficient of its minimal polynomial, it
yields the classical formula `∏_α α = (-1) ^ d * F(0)` for the product of the roots of a monic
polynomial. -/
theorem prod_roots_eq_neg_one_pow_mul_coeff_zero :
    (F.roots.map (Polynomial.eval · (X : K[X]))).prod = (-1) ^ F.natDegree * F.coeff 0 := by
  rw [← norm_mk_eq_prod_roots hF X]
  have h1 : mk F X = (powerBasis hF.ne_zero).gen := by rw [powerBasis_gen]; rfl
  rw [h1, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    minpoly_powerBasis_gen_of_monic hF, powerBasis_dim]

end Field

end AdjoinRoot
