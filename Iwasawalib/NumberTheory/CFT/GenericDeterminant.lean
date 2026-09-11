/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The generic determinant of a family of matrices

Let `b : ρ → Matrix n n R` be a finite family of square matrices.  Its **generic determinant**
`Matrix.genericDet b` is the polynomial

`det (∑ i, X i • b i) ∈ MvPolynomial ρ R`,

the determinant of the matrix whose `(p, q)` entry is the linear form `∑ i, X i * b i p q`.

Its point is the following *rationality* statement, which is the analytic heart of the
Noether–Deuring theorem of
`Iwasawalib/NumberTheory/CFT/NoetherDeuring.lean`: if some `K`-linear combination of the
`b i` is invertible, where `K` is an extension of an **infinite** field `k` over which the
`b i` are defined, then already some `k`-linear combination is invertible
(`Matrix.exists_det_ne_zero_of_det_map_ne_zero`).  Indeed the generic determinant is a
polynomial over `k` which, by hypothesis, does not vanish at a `K`-point; hence it is a
nonzero polynomial; hence, `k` being infinite, it does not vanish at some `k`-point.

This is a Zariski-density argument, and `MvPolynomial.funext` is the form in which Mathlib
supplies the density of `kⁿ` in the affine space over `K`.

## Main definitions

* `Matrix.genericDet`

## Main statements

* `Matrix.eval_genericDet` : `eval x (genericDet b) = det (∑ i, x i • b i)`.
* `Matrix.map_genericDet` : the generic determinant commutes with a ring map.
* `Matrix.exists_det_ne_zero_of_det_map_ne_zero` : the rationality statement above.
-/

noncomputable section

open scoped BigOperators

namespace Matrix

variable {n ρ : Type*} [Fintype n] [DecidableEq n] [Fintype ρ]
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The **generic determinant** of a finite family of square matrices: the determinant of
`∑ i, X i • b i`, a polynomial in the variables `X i`. -/
def genericDet (b : ρ → Matrix n n R) : MvPolynomial ρ R :=
  Matrix.det (Matrix.of fun p q ↦ ∑ i : ρ, MvPolynomial.X i * MvPolynomial.C (b i p q))

/-- Evaluating the generic determinant at `x` gives the determinant of `∑ i, x i • b i`. -/
theorem eval_genericDet (b : ρ → Matrix n n R) (x : ρ → R) :
    MvPolynomial.eval x (genericDet b) = (∑ i, x i • b i).det := by
  rw [genericDet, RingHom.map_det]
  congr 1
  ext p q
  simp [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- The generic determinant is compatible with a ring map applied to the entries. -/
theorem map_genericDet (f : R →+* S) (b : ρ → Matrix n n R) :
    MvPolynomial.map f (genericDet b) = genericDet fun i ↦ (b i).map f := by
  rw [genericDet, genericDet, RingHom.map_det]
  congr 1
  ext p q
  simp [Matrix.map_apply, map_sum]

variable {k K : Type*} [Field k] [Infinite k] [CommRing K] [Algebra k K]

/-- **Rational points of a nonvanishing generic determinant.**  If some `K`-linear combination
of matrices defined over an infinite field `k` is invertible, then some `k`-linear combination
of them is invertible. -/
theorem exists_det_ne_zero_of_det_map_ne_zero (b : ρ → Matrix n n k) (y : ρ → K)
    (hy : (∑ i, y i • (b i).map (algebraMap k K)).det ≠ 0) :
    ∃ x : ρ → k, (∑ i, x i • b i).det ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hzero : genericDet b = 0 := by
    refine MvPolynomial.funext fun x ↦ ?_
    rw [eval_genericDet, hcon x, map_zero]
  apply hy
  have : MvPolynomial.eval y (genericDet fun i ↦ (b i).map (algebraMap k K)) = 0 := by
    rw [← map_genericDet (algebraMap k K) b, hzero, map_zero, map_zero]
  rwa [eval_genericDet] at this

end Matrix
