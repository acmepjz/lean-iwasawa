/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.GenericDeterminant
public import Mathlib.Data.Matrix.Basis

@[expose] public section

/-!
# The Noether–Deuring theorem, in matrix form

Let `k ⊆ K` be an extension of fields with `k` infinite and let `G` be a finite group whose
order is invertible in `k`.  Two matrix representations `A, B : G → GLₙ(k)` which become
conjugate over `K` are already conjugate over `k`:

`Matrix.exists_conj_of_conj_map`.

This is the **Noether–Deuring theorem** `M ⊗_k K ≅ N ⊗_k K ⟹ M ≅ N` for finite-dimensional
`k[G]`-modules, in the concrete form in which it is applied.  Mathlib does not contain it in
any form as of this writing.

## Proof

The usual textbook proof passes through `Hom_{k[G]}(M, N) ⊗_k K = Hom_{K[G]}(M_K, N_K)`,
which is a flat-base-change statement about a kernel.  The proof here replaces that kernel by
an *image*, for which base change is trivial: the **Reynolds operator**

`e(X) = #G⁻¹ ∑_{g} A g * X * B g⁻¹`  (`Matrix.reynolds`)

is a `k`-linear projector of the space of all matrices onto the space of intertwiners of `A`
and `B` (`Matrix.reynolds_intertwines`, `Matrix.reynolds_eq_self`), and it is defined by a
formula with coefficients in `k`, so it commutes with extension of scalars
(`Matrix.map_reynolds`).  The image of a linear map is spanned by the images of any spanning
family, and the elementary matrices `Matrix.single p q 1` are a spanning family defined over
`k`; hence every `K`-intertwiner is a `K`-linear combination of the finitely many
`k`-intertwiners `e (single p q 1)`.

An invertible `K`-intertwiner therefore witnesses that the generic determinant
`Matrix.genericDet` of the family `e (single p q 1)` is a nonzero polynomial over `k`, and
`k` being infinite that polynomial has a nonvanishing `k`-point
(`Matrix.exists_det_ne_zero_of_det_map_ne_zero`), i.e. an invertible `k`-intertwiner.

## Main definitions

* `Matrix.reynolds`

## Main statements

* `Matrix.reynolds_intertwines`, `Matrix.reynolds_eq_self`, `Matrix.map_reynolds`
* `Matrix.mem_span_reynolds_single` : every `K`-intertwiner is a `K`-combination of the
  `k`-intertwiners `e (single p q 1)`.
* `Matrix.exists_conj_of_conj_map` : **Noether–Deuring**.
-/

noncomputable section

open scoped BigOperators

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Group G] [Fintype G]

/-! ## The Reynolds operator -/

section Reynolds

variable {k : Type*} [Field k] (A B : G → Matrix n n k)

/-- The **Reynolds operator** `X ↦ #G⁻¹ ∑_g A g * X * B g⁻¹` attached to two matrix
representations `A` and `B` of a finite group `G`.  It is a projector of the space of all
matrices onto the space of intertwiners of `A` and `B`. -/
def reynolds : Matrix n n k →ₗ[k] Matrix n n k where
  toFun X := (Fintype.card G : k)⁻¹ • ∑ g : G, A g * X * B g⁻¹
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib, smul_add]
  map_smul' c X := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum,
      smul_comm ((Fintype.card G : k)⁻¹) c]

omit [DecidableEq n] in
theorem reynolds_apply (X : Matrix n n k) :
    reynolds A B X = (Fintype.card G : k)⁻¹ • ∑ g : G, A g * X * B g⁻¹ := rfl

variable {A B}
variable (hA : ∀ g h : G, A (g * h) = A g * A h) (hB : ∀ g h : G, B (g * h) = B g * B h)

include hA hB

omit [DecidableEq n] in
/-- The Reynolds operator lands in the intertwiners. -/
theorem reynolds_intertwines (X : Matrix n n k) (h : G) :
    A h * reynolds A B X = reynolds A B X * B h := by
  rw [reynolds_apply, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  refine (Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g ↦ ?_).symm
  show A g * X * B g⁻¹ * B h = A h * (A (h⁻¹ * g) * X * B ((h⁻¹ * g)⁻¹))
  have h₁ : A h * A (h⁻¹ * g) = A g := by rw [← hA, mul_inv_cancel_left]
  have hgg : (h⁻¹ * g)⁻¹ = g⁻¹ * h := by group
  have h₂ : B ((h⁻¹ * g)⁻¹) = B g⁻¹ * B h := by rw [hgg, hB]
  rw [h₂]
  simp only [← mul_assoc, h₁]

end Reynolds

section ReynoldsProj

variable {k : Type*} [Field k] {A B : G → Matrix n n k}

/-- The Reynolds operator fixes the intertwiners.  (This is where `#G` must be invertible in
`k`.) -/
theorem reynolds_eq_self (hB1 : B 1 = 1) (hBmul : ∀ g h : G, B (g * h) = B g * B h)
    (hchar : (Fintype.card G : k) ≠ 0) {X : Matrix n n k}
    (hX : ∀ g : G, A g * X = X * B g) : reynolds A B X = X := by
  have hBinv : ∀ g : G, B g * B g⁻¹ = 1 := by
    intro g; rw [← hBmul, mul_inv_cancel, hB1]
  have : ∀ g : G, A g * X * B g⁻¹ = X := by
    intro g; rw [hX g, mul_assoc, hBinv g, Matrix.mul_one]
  rw [reynolds_apply, Finset.sum_congr rfl fun g _ ↦ this g, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hchar, one_smul]

end ReynoldsProj

/-! ## Base change -/

section BaseChange

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {A B : G → Matrix n n k}

omit [DecidableEq n] in
/-- The Reynolds operator commutes with extension of scalars. -/
theorem map_reynolds (X : Matrix n n k) :
    (reynolds A B X).map (algebraMap k K) =
      reynolds (fun g ↦ (A g).map (algebraMap k K)) (fun g ↦ (B g).map (algebraMap k K))
        (X.map (algebraMap k K)) := by
  rw [reynolds_apply, reynolds_apply]
  have h1 : ((Fintype.card G : k)⁻¹ • ∑ g : G, A g * X * B g⁻¹).map (algebraMap k K)
      = (algebraMap k K ((Fintype.card G : k)⁻¹)) •
        (∑ g : G, A g * X * B g⁻¹).map (algebraMap k K) := by
    ext p q; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [h1, map_inv₀, map_natCast]
  congr 1
  have h2 : (∑ g : G, A g * X * B g⁻¹).map (algebraMap k K)
      = ∑ g : G, (A g * X * B g⁻¹).map (algebraMap k K) := by
    ext p q
    simp [Matrix.map_apply, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun g _ ↦ by rw [← Matrix.map_mul, ← Matrix.map_mul]; rfl
  rw [h2]
  exact Finset.sum_congr rfl fun g _ ↦ by rw [Matrix.map_mul, Matrix.map_mul]

/-- Every `K`-intertwiner of two representations defined over `k` is a `K`-linear combination
of the `k`-intertwiners `e (Matrix.single p q 1)`. -/
theorem mem_span_reynolds_single (hB1 : B 1 = 1) (hBmul : ∀ g h : G, B (g * h) = B g * B h)
    (hchar : (Fintype.card G : k) ≠ 0) (Y : Matrix n n K)
    (hY : ∀ g : G, (A g).map (algebraMap k K) * Y = Y * (B g).map (algebraMap k K)) :
    Y = ∑ pq : n × n, Y pq.1 pq.2 •
      (reynolds A B (Matrix.single pq.1 pq.2 1)).map (algebraMap k K) := by
  set AK : G → Matrix n n K := fun g ↦ (A g).map (algebraMap k K) with hAK
  set BK : G → Matrix n n K := fun g ↦ (B g).map (algebraMap k K) with hBK
  have hBK1 : BK 1 = 1 := by rw [hBK]; simp [hB1]
  have hBKmul : ∀ g h : G, BK (g * h) = BK g * BK h := by
    intro g h; simp [hBK, hBmul, Matrix.map_mul]
  have hcharK : (Fintype.card G : K) ≠ 0 := by
    intro h
    exact hchar (by
      have : algebraMap k K (Fintype.card G : k) = 0 := by rw [map_natCast]; exact h
      exact (map_eq_zero_iff _ (algebraMap k K).injective).1 this)
  have hself : reynolds AK BK Y = Y := reynolds_eq_self hBK1 hBKmul hcharK hY
  conv_lhs => rw [← hself]
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
  rw [show (∑ p : n, ∑ q : n, Matrix.single p q (Y p q)) =
      ∑ pq : n × n, Y pq.1 pq.2 • Matrix.single pq.1 pq.2 (1 : K) by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by
      rw [Matrix.smul_single]; simp]
  rw [map_sum]
  refine Finset.sum_congr rfl fun pq _ ↦ ?_
  rw [LinearMap.map_smul]
  congr 1
  rw [map_reynolds (K := K) (A := A) (B := B)]
  congr 1
  rw [Matrix.map_single]
  simp

end BaseChange

/-! ## The theorem -/

section Main

variable {k K : Type*} [Field k] [Infinite k] [Field K] [Algebra k K]

/-- **The Noether–Deuring theorem.**  Two matrix representations `A, B : G → GLₙ(k)` of a
finite group over an infinite field `k` in which `#G` is invertible, which are conjugate over
an extension field `K`, are conjugate over `k` itself. -/
theorem exists_conj_of_conj_map {A B : G → Matrix n n k}
    (hA : ∀ g h : G, A (g * h) = A g * A h) (hB1 : B 1 = 1)
    (hB : ∀ g h : G, B (g * h) = B g * B h) (hchar : (Fintype.card G : k) ≠ 0)
    (Y : Matrix n n K) (hYdet : Y.det ≠ 0)
    (hY : ∀ g : G, (A g).map (algebraMap k K) * Y = Y * (B g).map (algebraMap k K)) :
    ∃ X : Matrix n n k, X.det ≠ 0 ∧ ∀ g : G, A g * X = X * B g := by
  classical
  set b : n × n → Matrix n n k := fun pq ↦ reynolds A B (Matrix.single pq.1 pq.2 1) with hb
  have hYspan : Y = ∑ pq : n × n, Y pq.1 pq.2 • (b pq).map (algebraMap k K) :=
    mem_span_reynolds_single hB1 hB hchar Y hY
  have hne : (∑ pq : n × n, Y pq.1 pq.2 • (b pq).map (algebraMap k K)).det ≠ 0 := by
    rw [← hYspan]; exact hYdet
  obtain ⟨x, hx⟩ := Matrix.exists_det_ne_zero_of_det_map_ne_zero b (fun pq ↦ Y pq.1 pq.2) hne
  refine ⟨∑ pq : n × n, x pq • b pq, hx, fun g ↦ ?_⟩
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun pq _ ↦ ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, hb]
  exact congrArg _ (reynolds_intertwines hA hB _ g)

end Main

end Matrix
