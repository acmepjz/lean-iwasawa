/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.NoetherDeuring
public import Iwasawalib.NumberTheory.CFT.HerbrandLattice
public import Mathlib.Algebra.Algebra.Rat

@[expose] public section

/-!
# Two `ℚ`-forms of one real representation have the same Herbrand quotient

Let `G = ⟨σ⟩` be a finite cyclic group acting `K`-linearly on a `K`-vector space `V`, where
`K` is a field of characteristic zero (`ℝ` in the application).  Let `v₁` and `v₂` be two
`K`-bases of `V` in each of which the action of `G` is given by *integer* matrices, and let
`Λ₁`, `Λ₂` be the lattices they span.  Then

`h(Λ₁) = h(Λ₂)`  (`CyclicTate.herbrand_intLattice_eq`).

This is the step that the commensurability criterion
`CyclicTate.herbrand_eq_of_commensurable` cannot supply on its own: two `G`-stable lattices
spanning the same *real* representation need not be commensurable — `ℤ` and `√2 ℤ` in `ℝ`
are not — and the `S`-unit lattice is a lattice of exactly that transcendental kind inside
`(∏_{p ∈ S} ℝ)⁰`.  What is true is that the two `ℚ[G]`-modules `ℚ ⊗ Λ₁` and `ℚ ⊗ Λ₂` are
isomorphic, by the **Noether–Deuring theorem** of
`Iwasawalib/NumberTheory/CFT/NoetherDeuring.lean`, and then the lattices *are*
commensurable after transporting one of them along that isomorphism.

## Proof

Write `A g` and `B g` for the integer matrices of `g` in the two bases, and `Y` for the change
of basis matrix, which conjugates `A` into `B` over `K`.  `Matrix.exists_conj_of_conj_map`
produces a conjugating matrix `X` over `ℚ`.  The `K`-linear map `ψ` whose matrix from `v₂` to
`v₁` is `X` is then `G`-equivariant and bijective, so `h(Λ₂) = h(ψ Λ₂)`; and `ψ Λ₂` and `Λ₁`
are commensurable because a single common denominator `N` of the entries of `X` and `X⁻¹`
works for all of the (finitely many) basis vectors.

## Main definitions

* `NoetherDeuring.intLattice` : the lattice `∑ ℤ · v i` spanned by a basis.

## Main statements

* `NoetherDeuring.exists_equivariant_equiv` : the `ℚ`-rational conjugating map `ψ`.
* `CyclicTate.herbrand_intLattice_eq` : `h(Λ₁) = h(Λ₂)`.
-/

noncomputable section

open Module
open scoped BigOperators

namespace NoetherDeuring

/-! ## A common denominator for a finite family of rationals -/

/-- Every finite family of rational numbers has a common denominator. -/
theorem exists_nat_mul_isInt {ι : Type*} [Fintype ι] (q : ι → ℚ) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ i, ∃ z : ℤ, (N : ℚ) * q i = (z : ℚ) := by
  classical
  refine ⟨∏ i : ι, (q i).den, Finset.prod_ne_zero_iff.2 fun i _ ↦ (q i).den_nz, fun i ↦ ?_⟩
  obtain ⟨m, hm⟩ : ((q i).den : ℕ) ∣ ∏ j : ι, (q j).den :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨m * (q i).num, ?_⟩
  rw [hm]
  push_cast
  rw [mul_comm ((q i).den : ℚ) (m : ℚ), mul_assoc, Rat.den_mul_eq_num, mul_comm]

/-! ## The lattice spanned by a basis -/

section Lattice

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {n : Type*} [Fintype n]

/-- The lattice `∑_i ℤ · v i` spanned by a family of vectors. -/
def intLattice (v : n → V) : AddSubgroup V := (Submodule.span ℤ (Set.range v)).toAddSubgroup

omit [Fintype n] in
theorem mem_intLattice {v : n → V} {x : V} :
    x ∈ intLattice v ↔ x ∈ Submodule.span ℤ (Set.range v) := Iff.rfl

omit [Fintype n] in
theorem self_mem_intLattice (v : n → V) (i : n) : v i ∈ intLattice v :=
  Submodule.subset_span ⟨i, rfl⟩

theorem zsmul_sum_mem_intLattice (v : n → V) (z : n → ℤ) :
    ∑ i, z i • v i ∈ intLattice v :=
  Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

instance moduleFinite_intLattice (v : n → V) : Module.Finite ℤ (intLattice v) :=
  Module.Finite.span_of_finite ℤ (Set.finite_range v)

/-- A vector whose coordinates in a basis are integers lies in the lattice of that basis. -/
theorem mem_intLattice_of_repr (v : Basis n K V) {x : V} {z : n → ℤ}
    (h : ∀ i, v.repr x i = (z i : K)) : x ∈ intLattice (v : n → V) := by
  have hx : x = ∑ i, z i • v i := by
    conv_lhs => rw [← v.sum_repr x]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [h i, Int.cast_smul_eq_zsmul]
  rw [hx]
  exact zsmul_sum_mem_intLattice _ _

end Lattice


/-! ## The rational conjugating map -/

section Form

variable {G : Type*} [Group G] [Fintype G]
variable {K : Type*} [Field K] [CharZero K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable [DistribMulAction G V] [SMulCommClass G K V]
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- A family of vectors all of whose members lie in a subgroup spans a lattice inside it. -/
theorem intLattice_le {v : n → V} {H : AddSubgroup V} (h : ∀ i, v i ∈ H) :
    intLattice v ≤ H := by
  intro x hx
  refine Submodule.span_induction (p := fun y _ ↦ y ∈ H) ?_ H.zero_mem
    (fun a b _ _ ha hb ↦ H.add_mem ha hb) (fun c a _ ha ↦ H.zsmul_mem ha c) hx
  rintro _ ⟨i, rfl⟩
  exact h i

omit [Fintype G] [CharZero K] in
/-- If the action of `G` in the basis `v` is by integer matrices, the lattice of `v` is
`G`-stable. -/
theorem isStableSubgroup_intLattice (v : Basis n K V) (A : G → Matrix n n ℤ)
    (hA : ∀ g : G, LinearMap.toMatrix v v (DistribSMul.toLinearMap K V g)
      = (A g).map (Int.cast : ℤ → K)) :
    CyclicTate.IsStableSubgroup G (intLattice (v : n → V)) where
  smul_mem g {x} hx := by
    refine intLattice_le (v := (v : n → V))
      (H := AddSubgroup.comap (DistribSMul.toAddMonoidHom V g) (intLattice (v : n → V)))
      (fun i ↦ ?_) hx
    show g • v i ∈ intLattice (v : n → V)
    refine mem_intLattice_of_repr v (z := fun j ↦ A g j i) fun j ↦ ?_
    have : (LinearMap.toMatrix v v (DistribSMul.toLinearMap K V g)) j i
        = v.repr (g • v i) j := LinearMap.toMatrix_apply _ _ _ _ _
    rw [← this, hA g]
    rfl

/-- A vector space over a field of characteristic zero has no `ℤ`-torsion. -/
theorem noZeroSMulDivisors_int (K : Type*) [Field K] [CharZero K] {V : Type*} [AddCommGroup V]
    [Module K V] : NoZeroSMulDivisors ℤ V := by
  refine ⟨fun {m x} h ↦ ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · exact Or.inl rfl
  · refine Or.inr ?_
    have hk : (m : K) ≠ 0 := Int.cast_ne_zero.2 hm
    have h' : (m : K) • x = 0 := by rwa [Int.cast_smul_eq_zsmul]
    exact (smul_eq_zero.1 h').resolve_left hk

omit [Fintype n] [CharZero K] in
/-- The coordinates, in a basis `v`, of a vector in the lattice of `v` are integers. -/
theorem exists_int_repr (v : Basis n K V) {x : V} (hx : x ∈ intLattice (v : n → V)) (i : n) :
    ∃ z : ℤ, v.repr x i = (z : K) := by
  have hmem : x ∈ AddSubgroup.comap
      ((Finsupp.applyAddHom i).comp ((v.repr : V →ₗ[K] (n →₀ K)).toAddMonoidHom))
      (⊥ : Subring K).toAddSubgroup := by
    refine intLattice_le (v := (v : n → V)) (fun j ↦ ?_) hx
    show v.repr (v j) i ∈ (⊥ : Subring K)
    rw [v.repr_self, Finsupp.single_apply]
    split
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨z, hz⟩ := Subring.mem_bot.1 (show v.repr x i ∈ (⊥ : Subring K) from hmem)
  exact ⟨z, hz.symm⟩

omit [Fintype G] [CharZero K] in
/-- If the lattice of a basis `v` is `G`-stable, then the action of `G` is given by integer
matrices in the basis `v`. -/
theorem exists_int_matrix (v : Basis n K V)
    [CyclicTate.IsStableSubgroup G (intLattice (v : n → V))] :
    ∃ A : G → Matrix n n ℤ, ∀ g : G,
      LinearMap.toMatrix v v (DistribSMul.toLinearMap K V g) = (A g).map (Int.cast : ℤ → K) := by
  choose z hz using fun (g : G) (j : n) (i : n) ↦ exists_int_repr v
    (CyclicTate.smul_mem_of_isStableSubgroup g (self_mem_intLattice (v : n → V) j)) i
  refine ⟨fun g ↦ Matrix.of fun i j ↦ z g j i, fun g ↦ ?_⟩
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact hz g j i

variable (v₁ v₂ : Basis n K V) (A B : G → Matrix n n ℤ)

/-- **The `ℚ`-rational intertwiner.**  If the action of a finite group `G` on `V` is given by
integer matrices in each of two `K`-bases `v₁`, `v₂` (`K` of characteristic zero), then there
is a `G`-equivariant `K`-linear automorphism `ψ` of `V` carrying the lattice of `v₂` into the
lattice of `v₁` up to a bounded denominator `N`, and conversely.  This is the Noether–Deuring
descent: `ψ` is given by a matrix with *rational* entries. -/
theorem exists_equivariant_equiv
    (hA : ∀ g : G, LinearMap.toMatrix v₁ v₁ (DistribSMul.toLinearMap K V g)
      = (A g).map (Int.cast : ℤ → K))
    (hB : ∀ g : G, LinearMap.toMatrix v₂ v₂ (DistribSMul.toLinearMap K V g)
      = (B g).map (Int.cast : ℤ → K)) :
    ∃ (ψ : V ≃ₗ[K] V) (N : ℕ), (∀ (g : G) (x : V), ψ (g • x) = g • ψ x) ∧ N ≠ 0 ∧
      (∀ i, (N : ℤ) • ψ (v₂ i) ∈ intLattice (v₁ : n → V)) ∧
      (∀ i, ∃ y ∈ intLattice (v₂ : n → V), ψ y = (N : ℤ) • v₁ i) := by
  classical
  have hcast : Function.Injective (Int.cast : ℤ → K) := Int.cast_injective
  have hmulK : ∀ P Q : Matrix n n ℤ, (P * Q).map (Int.cast : ℤ → K)
      = P.map (Int.cast : ℤ → K) * Q.map (Int.cast : ℤ → K) := fun P Q ↦ by
    simpa using Matrix.map_mul (f := Int.castRingHom K) (L := P) (M := Q)
  have hmulQ : ∀ P Q : Matrix n n ℤ, (P * Q).map (Int.cast : ℤ → ℚ)
      = P.map (Int.cast : ℤ → ℚ) * Q.map (Int.cast : ℤ → ℚ) := fun P Q ↦ by
    simpa using Matrix.map_mul (f := Int.castRingHom ℚ) (L := P) (M := Q)
  -- the matrices are multiplicative
  have hmul : ∀ (w : Basis n K V) (C : G → Matrix n n ℤ),
      (∀ g : G, LinearMap.toMatrix w w (DistribSMul.toLinearMap K V g)
        = (C g).map (Int.cast : ℤ → K)) →
      (∀ g h : G, C (g * h) = C g * C h) ∧ C 1 = 1 := by
    intro w C hC
    constructor
    · intro g h
      refine Matrix.map_injective hcast ?_
      show (C (g * h)).map (Int.cast : ℤ → K) = (C g * C h).map (Int.cast : ℤ → K)
      rw [hmulK, ← hC, ← hC, ← hC, ← LinearMap.toMatrix_comp w w w]
      congr 1
      ext x
      exact mul_smul g h x
    · refine Matrix.map_injective hcast ?_
      show (C 1).map (Int.cast : ℤ → K) = (1 : Matrix n n ℤ).map (Int.cast : ℤ → K)
      rw [Matrix.map_one _ Int.cast_zero Int.cast_one, ← hC,
        show (DistribSMul.toLinearMap K V (1 : G)) = LinearMap.id by ext x; exact one_smul G x]
      exact LinearMap.toMatrix_id w
  obtain ⟨hAmul, -⟩ := hmul v₁ A hA
  obtain ⟨hBmul, hB1⟩ := hmul v₂ B hB
  -- the rational matrices
  set A' : G → Matrix n n ℚ := fun g ↦ (A g).map (Int.cast : ℤ → ℚ) with hA'def
  set B' : G → Matrix n n ℚ := fun g ↦ (B g).map (Int.cast : ℤ → ℚ) with hB'def
  have hmapA : ∀ g : G, (A' g).map (algebraMap ℚ K) = (A g).map (Int.cast : ℤ → K) := by
    intro g; ext p q; simp [hA'def, Matrix.map_apply, map_intCast]
  have hmapB : ∀ g : G, (B' g).map (algebraMap ℚ K) = (B g).map (Int.cast : ℤ → K) := by
    intro g; ext p q; simp [hB'def, Matrix.map_apply, map_intCast]
  have hA'mul : ∀ g h : G, A' (g * h) = A' g * A' h := by
    intro g h; show (A (g * h)).map _ = _; rw [hAmul g h, hmulQ]
  have hB'mul : ∀ g h : G, B' (g * h) = B' g * B' h := by
    intro g h; show (B (g * h)).map _ = _; rw [hBmul g h, hmulQ]
  have hB'1 : B' 1 = 1 := by
    show (B 1).map (Int.cast : ℤ → ℚ) = 1
    rw [hB1]
    exact Matrix.map_one _ Int.cast_zero Int.cast_one
  -- the change of basis matrix conjugates one into the other over `K`
  set Y : Matrix n n K := LinearMap.toMatrix v₂ v₁ LinearMap.id with hYdef
  have hYmul : Y * LinearMap.toMatrix v₁ v₂ LinearMap.id = 1 := by
    rw [hYdef, ← LinearMap.toMatrix_comp v₁ v₂ v₁, LinearMap.id_comp, LinearMap.toMatrix_id]
  have hYdet : Y.det ≠ 0 := by
    intro h0
    have hd := congrArg Matrix.det hYmul
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at hd
    exact zero_ne_one hd
  have hconj : ∀ g : G, (A' g).map (algebraMap ℚ K) * Y = Y * (B' g).map (algebraMap ℚ K) := by
    intro g
    rw [hmapA, hmapB, ← hA g, ← hB g, hYdef, ← LinearMap.toMatrix_comp v₂ v₁ v₁,
      ← LinearMap.toMatrix_comp v₂ v₂ v₁]
    congr 1
  -- Noether-Deuring
  have hcard : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  obtain ⟨X, hXdet, hXconj⟩ :=
    Matrix.exists_conj_of_conj_map hA'mul hB'1 hB'mul hcard Y hYdet hconj
  have hXu : IsUnit X.det := isUnit_iff_ne_zero.2 hXdet
  set W : Matrix n n K := X.map (algebraMap ℚ K) with hWdef
  set W' : Matrix n n K := X⁻¹.map (algebraMap ℚ K) with hW'def
  have hWW' : W * W' = 1 := by
    rw [hWdef, hW'def, ← Matrix.map_mul, Matrix.mul_nonsing_inv X hXu]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hW'W : W' * W = 1 := by
    rw [hWdef, hW'def, ← Matrix.map_mul, Matrix.nonsing_inv_mul X hXu]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  -- the linear automorphism
  have hcomp₁ : (Matrix.toLin v₂ v₁ W) ∘ₗ (Matrix.toLin v₁ v₂ W') = LinearMap.id := by
    rw [← Matrix.toLin_mul v₁ v₂ v₁, hWW', Matrix.toLin_one]
  have hcomp₂ : (Matrix.toLin v₁ v₂ W') ∘ₗ (Matrix.toLin v₂ v₁ W) = LinearMap.id := by
    rw [← Matrix.toLin_mul v₂ v₁ v₂, hW'W, Matrix.toLin_one]
  set ψ : V ≃ₗ[K] V :=
    LinearEquiv.ofLinear (Matrix.toLin v₂ v₁ W) (Matrix.toLin v₁ v₂ W') hcomp₁ hcomp₂ with hψdef
  have hψapp : ∀ x, ψ x = Matrix.toLin v₂ v₁ W x := fun x ↦ rfl
  -- equivariance
  have hequiv : ∀ (g : G) (x : V), ψ (g • x) = g • ψ x := by
    have key : ∀ g : G, (Matrix.toLin v₂ v₁ W) ∘ₗ (DistribSMul.toLinearMap K V g)
        = (DistribSMul.toLinearMap K V g) ∘ₗ (Matrix.toLin v₂ v₁ W) := by
      intro g
      refine (LinearMap.toMatrix v₂ v₁).injective ?_
      rw [LinearMap.toMatrix_comp v₂ v₂ v₁, LinearMap.toMatrix_comp v₂ v₁ v₁,
        LinearMap.toMatrix_toLin, hA g, hB g, ← hmapA g, ← hmapB g,
        hWdef, ← Matrix.map_mul, ← Matrix.map_mul, hXconj g]
    intro g x
    have := congrArg (fun f ↦ (f : V →ₗ[K] V) x) (key g)
    simpa [hψapp] using this
  -- a common denominator
  obtain ⟨N, hN, hNint⟩ := exists_nat_mul_isInt
    (Sum.elim (fun pq : n × n ↦ X pq.1 pq.2) (fun pq : n × n ↦ X⁻¹ pq.1 pq.2))
  refine ⟨ψ, N, hequiv, hN, fun i ↦ ?_, fun i ↦ ?_⟩
  · have hzz : ∀ j : n, ∃ w : ℤ, (N : ℚ) * X j i = (w : ℚ) := fun j ↦ by
      simpa using hNint (Sum.inl (j, i))
    choose z hz using hzz
    have hval : (N : ℤ) • ψ (v₂ i) = ∑ j, z j • v₁ j := by
      rw [hψapp, Matrix.toLin_self, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [smul_comm, ← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K, smul_smul]
      congr 1
      have : W j i * ((N : ℤ) : K) = algebraMap ℚ K ((N : ℚ) * X j i) := by
        rw [hWdef]; push_cast [Matrix.map_apply, map_mul]; ring
      rw [this, hz j]
      simp
    rw [hval]
    exact zsmul_sum_mem_intLattice _ _
  · have hzz : ∀ j : n, ∃ w : ℤ, (N : ℚ) * X⁻¹ j i = (w : ℚ) := fun j ↦ by
      simpa using hNint (Sum.inr (j, i))
    choose z hz using hzz
    refine ⟨∑ j, z j • v₂ j, zsmul_sum_mem_intLattice _ _, ?_⟩
    have hφ : (N : ℤ) • (Matrix.toLin v₁ v₂ W') (v₁ i) = ∑ j, z j • v₂ j := by
      rw [Matrix.toLin_self, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [smul_comm, ← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K, smul_smul]
      congr 1
      have : W' j i * ((N : ℤ) : K) = algebraMap ℚ K ((N : ℚ) * X⁻¹ j i) := by
        rw [hW'def]; push_cast [Matrix.map_apply, map_mul]; ring
      rw [this, hz j]
      simp
    rw [← hφ, map_zsmul]
    congr 1
    have := congrArg (fun f ↦ (f : V →ₗ[K] V) (v₁ i)) hcomp₁
    simpa [hψapp] using this

end Form

end NoetherDeuring

/-! ## The Herbrand quotient of the two lattices -/

namespace CyclicTate

open NoetherDeuring

variable {G : Type*} [Group G] [Fintype G] {σ : G}
variable {K : Type*} [Field K] [CharZero K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable [DistribMulAction G V] [SMulCommClass G K V]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Two `ℚ`-forms of one representation have the same Herbrand quotient.**  If a finite
cyclic group `G = ⟨σ⟩` acts on a characteristic-zero vector space `V` by integer matrices in
each of two bases `v₁`, `v₂`, then the two lattices spanned by those bases have the same
Herbrand quotient — even though they need not be commensurable inside `V`.

This is the Noether–Deuring descent of
`Iwasawalib/NumberTheory/CFT/NoetherDeuring.lean` in the form in which the computation of
`h(O_{L,S}^×)` needs it: the `S`-unit logarithm lattice and the trace-zero permutation
lattice `ℤ[S_L]⁰` span the same real representation, and this says their Herbrand quotients
agree. -/
theorem herbrand_intLattice_eq (hgen : ∀ g : G, ∃ m : ℕ, σ ^ m = g)
    (v₁ v₂ : Basis n K V) (A B : G → Matrix n n ℤ)
    (hA : ∀ g : G, LinearMap.toMatrix v₁ v₁ (DistribSMul.toLinearMap K V g)
      = (A g).map (Int.cast : ℤ → K))
    (hB : ∀ g : G, LinearMap.toMatrix v₂ v₂ (DistribSMul.toLinearMap K V g)
      = (B g).map (Int.cast : ℤ → K))
    [IsStableSubgroup G (intLattice (v₁ : n → V))]
    [IsStableSubgroup G (intLattice (v₂ : n → V))] :
    herbrand G (intLattice (v₁ : n → V)) σ = herbrand G (intLattice (v₂ : n → V)) σ := by
  classical
  haveI : NoZeroSMulDivisors ℤ V := noZeroSMulDivisors_int K
  obtain ⟨ψ, N, hequiv, hN, h1, h2⟩ := exists_equivariant_equiv v₁ v₂ A B hA hB
  set f : V →+ V := ψ.toLinearMap.toAddMonoidHom with hf
  have hfapp : ∀ x, f x = ψ x := fun _ ↦ rfl
  have hfinj : Function.Injective f := ψ.injective
  set L₂' : AddSubgroup V := (intLattice (v₂ : n → V)).map f with hL₂'
  haveI hstab : IsStableSubgroup G L₂' := by
    refine ⟨fun g {x} hx ↦ ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨g • y, smul_mem_of_isStableSubgroup g hy, by rw [hfapp, hfapp, hequiv]⟩
  set e : intLattice (v₂ : n → V) ≃+ L₂' :=
    AddSubgroup.equivMapOfInjective _ f hfinj with he
  haveI : Module.Finite ℤ L₂' := Module.Finite.equiv e.toIntLinearEquiv
  have hherb₂ : herbrand G (intLattice (v₂ : n → V)) σ = herbrand G L₂' σ := by
    refine herbrand_eq_of_addEquiv e (fun g a ↦ ?_) σ
    refine Subtype.ext ?_
    show f (g • (a : V)) = g • (f (a : V))
    rw [hfapp, hfapp, hequiv]
  rw [hherb₂]
  -- the two lattices are commensurable
  set mulN : V →+ V := AddMonoidHom.mk' (fun x ↦ (N : ℤ) • x) (fun a b ↦ smul_add _ a b) with hmulN
  have hmulNapp : ∀ x, mulN x = (N : ℤ) • x := fun _ ↦ rfl
  have hNne : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hN
  refine herbrand_eq_of_commensurable hgen (fun x hx ↦ ⟨(N : ℤ), hNne, ?_⟩)
    (fun x hx ↦ ⟨(N : ℤ), hNne, ?_⟩)
  · refine intLattice_le (v := (v₁ : n → V)) (H := AddSubgroup.comap mulN L₂') (fun i ↦ ?_) hx
    show (N : ℤ) • v₁ i ∈ L₂'
    obtain ⟨y, hy, hyeq⟩ := h2 i
    exact ⟨y, hy, by rw [hfapp, hyeq]⟩
  · obtain ⟨y, hy, rfl⟩ := hx
    refine intLattice_le (v := (v₂ : n → V))
      (H := AddSubgroup.comap (mulN.comp f) (intLattice (v₁ : n → V))) (fun i ↦ ?_) hy
    show (N : ℤ) • f (v₂ i) ∈ intLattice (v₁ : n → V)
    rw [hfapp]
    exact h1 i

/-- **Two `G`-stable lattices spanning one and the same representation of a finite cyclic
group have the same Herbrand quotient.**  No commensurability hypothesis is needed: the two
lattices may be as incommensurable as `ℤ` and `√2 ℤ` inside `ℝ`.  The only hypothesis is that
each lattice is spanned by a `K`-basis of `V` and is `G`-stable.

This is the form in which the Noether–Deuring descent
(`Matrix.exists_conj_of_conj_map`) enters the computation of the Herbrand quotient of the
`S`-unit group. -/
theorem herbrand_intLattice_eq_of_stable (hgen : ∀ g : G, ∃ m : ℕ, σ ^ m = g)
    (v₁ v₂ : Basis n K V)
    [IsStableSubgroup G (intLattice (v₁ : n → V))]
    [IsStableSubgroup G (intLattice (v₂ : n → V))] :
    herbrand G (intLattice (v₁ : n → V)) σ = herbrand G (intLattice (v₂ : n → V)) σ := by
  obtain ⟨A, hA⟩ := exists_int_matrix (G := G) v₁
  obtain ⟨B, hB⟩ := exists_int_matrix (G := G) v₂
  exact herbrand_intLattice_eq hgen v₁ v₂ A B hA hB

end CyclicTate
