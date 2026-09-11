/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.HerbrandProduct
public import Mathlib.GroupTheory.FiniteAbelian.Basic

@[expose] public section

/-!
# The Herbrand quotient of a lattice

A `G`-**lattice** is a `G`-module which is finitely generated over `ℤ`.  For a finite cyclic
`G = ⟨σ⟩` the Tate cohomology of a lattice is automatically finite, so the Herbrand quotient
is defined, and it is a *commensurability invariant*: two `G`-stable lattices in a common
ambient group which contain each other up to bounded denominators have the same Herbrand
quotient.  This is the form in which the statement "the Herbrand quotient of a lattice depends
only on `M ⊗ ℚ` as a `ℚ[G]`-module" is used: two `G`-stable lattices spanning the same
rational representation are commensurable.

## Contents

* `CyclicTate.card_nsmul_tateH0_eq_zero`, `CyclicTate.card_nsmul_tateH1_eq_zero`: both Tate
  groups are killed by `#G`.
* `CyclicTate.finite_tateH0_of_moduleFinite`, `CyclicTate.finite_tateH1_of_moduleFinite`: the
  Tate cohomology of a lattice is finite (finitely generated and of finite exponent).
* `CyclicTate.herbrand_eq_of_commensurable`: **the Herbrand quotient is a commensurability
  invariant of `G`-stable lattices.**

The remaining step towards `h(O_{L,S}^×)`, namely that two `ℤ[G]`-lattices with isomorphic
`ℝ[G]`-scalar extensions are commensurable inside that common real representation (the
Noether–Deuring descent from `ℝ` to `ℚ`), is *not* proved here.
-/

noncomputable section

namespace CyclicTate

/-! ## The exponent of the Tate groups divides `#G` -/

section Exponent

variable {G : Type*} [Group G] [Fintype G] {M : Type*} [AddCommGroup M]
  [DistribMulAction G M] {σ : G}

omit [Fintype G] in
/-- If `σ` generates `G`, a `σ`-invariant element is `G`-invariant. -/
theorem smul_eq_of_smul_eq (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) {x : M} (hx : σ • x = x)
    (g : G) : g • x = x := by
  obtain ⟨k, rfl⟩ := hgen g
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_smul, hx, ih]

/-- The norm of a `σ`-invariant element is `#G` times it. -/
theorem normHom_eq_nsmul (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) {x : M} (hx : σ • x = x) :
    normHom G M x = Nat.card G • x := by
  rw [normHom_apply, Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) ↦
    smul_eq_of_smul_eq hgen hx g, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- **`Ĥ⁰` is killed by `#G`.** -/
theorem card_nsmul_tateH0_eq_zero (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) (t : TateH0 G M σ) :
    Nat.card G • t = 0 := by
  obtain ⟨x, hx, rfl⟩ := TateH0.mk_surjective t
  have h : Nat.card G • TateH0.mk σ hx
      = TateH0.mk σ (x := Nat.card G • x) (by rw [smul_comm, hx]) := rfl
  rw [h, TateH0.mk_eq_zero_iff]
  exact ⟨x, normHom_eq_nsmul hgen hx⟩

omit [Fintype G] in
/-- `σ ^ k • x - x` is always in the image of `σ - 1`. -/
theorem pow_smul_sub_mem_rangeSub (k : ℕ) (x : M) : σ ^ k • x - x ∈ rangeSub G M σ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : σ • (σ ^ k • x) - σ ^ k • x ∈ rangeSub G M σ :=
        mem_rangeSub.2 ⟨σ ^ k • x, rfl⟩
      have h2 := (rangeSub G M σ).add_mem h1 ih
      rw [show σ • (σ ^ k • x) - σ ^ k • x + (σ ^ k • x - x) = σ • (σ ^ k • x) - x by abel] at h2
      rwa [pow_succ', mul_smul]

/-- **`Ĥ¹` is killed by `#G`.** -/
theorem card_nsmul_tateH1_eq_zero (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) (t : TateH1 G M σ) :
    Nat.card G • t = 0 := by
  obtain ⟨x, hx, rfl⟩ := TateH1.mk_surjective t
  have h : Nat.card G • TateH1.mk σ hx
      = TateH1.mk σ (x := Nat.card G • x) (by rw [map_nsmul, hx, smul_zero]) := rfl
  rw [h, TateH1.mk_eq_zero_iff]
  have hsum : ∑ g : G, (g • x - x) = -(Nat.card G • x) := by
    rw [Finset.sum_sub_distrib, ← normHom_apply, hx, Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card, zero_sub]
  have hmem : ∑ g : G, (g • x - x) ∈ rangeSub G M σ :=
    AddSubgroup.sum_mem _ fun g _ ↦ by
      obtain ⟨k, rfl⟩ := hgen g
      exact pow_smul_sub_mem_rangeSub k x
  rw [hsum] at hmem
  exact mem_rangeSub.1 (neg_mem_iff.1 hmem)

end Exponent

/-! ## The Tate cohomology of a lattice is finite -/

section Lattice

variable {G : Type*} [Group G] [Fintype G] {M : Type*} [AddCommGroup M]
  [DistribMulAction G M] {σ : G} [Module.Finite ℤ M]

omit [Fintype G] in
theorem moduleFinite_kerSub : Module.Finite ℤ (kerSub G M σ) :=
  Module.Finite.of_injective ((kerSub G M σ).subtype.toIntLinearMap) fun _ _ h ↦ Subtype.ext h

theorem moduleFinite_kerNorm : Module.Finite ℤ (kerNorm G M) :=
  Module.Finite.of_injective ((kerNorm G M).subtype.toIntLinearMap) fun _ _ h ↦ Subtype.ext h

/-- **The `Ĥ⁰` of a lattice is finite.** -/
theorem finite_tateH0_of_moduleFinite (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) :
    Finite (TateH0 G M σ) := by
  haveI := moduleFinite_kerSub (G := G) (M := M) (σ := σ)
  haveI : Module.Finite ℤ (TateH0 G M σ) :=
    Module.Finite.of_surjective
      ((QuotientAddGroup.mk' ((rangeNorm G M).addSubgroupOf (kerSub G M σ))).toIntLinearMap)
      (QuotientAddGroup.mk'_surjective _)
  refine Module.finite_of_fg_torsion _ fun t ↦ ?_
  refine ⟨⟨(Nat.card G : ℤ), mem_nonZeroDivisors_of_ne_zero (by
    exact_mod_cast Nat.card_pos.ne')⟩, ?_⟩
  show (Nat.card G : ℤ) • t = 0
  rw [natCast_zsmul]
  exact card_nsmul_tateH0_eq_zero hgen t

/-- **The `Ĥ¹` of a lattice is finite.** -/
theorem finite_tateH1_of_moduleFinite (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) :
    Finite (TateH1 G M σ) := by
  haveI := moduleFinite_kerNorm (G := G) (M := M)
  haveI : Module.Finite ℤ (TateH1 G M σ) :=
    Module.Finite.of_surjective
      ((QuotientAddGroup.mk' ((rangeSub G M σ).addSubgroupOf (kerNorm G M))).toIntLinearMap)
      (QuotientAddGroup.mk'_surjective _)
  refine Module.finite_of_fg_torsion _ fun t ↦ ?_
  refine ⟨⟨(Nat.card G : ℤ), mem_nonZeroDivisors_of_ne_zero (by
    exact_mod_cast Nat.card_pos.ne')⟩, ?_⟩
  show (Nat.card G : ℤ) • t = 0
  rw [natCast_zsmul]
  exact card_nsmul_tateH1_eq_zero hgen t

end Lattice

/-! ## Commensurable lattices have the same Herbrand quotient -/

section Commensurable

variable {G : Type*} [Group G] [Fintype G] {σ : G} {A : Type*} [AddCommGroup A]
  [DistribMulAction G A]

/-- **A common denominator.**  If every element of a finitely generated subgroup `M` has some
nonzero multiple in `N`, then a single nonzero `k` works for all of `M`. -/
theorem exists_zsmul_mem (M N : AddSubgroup A) [Module.Finite ℤ M]
    (h : ∀ x ∈ M, ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ N) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ x ∈ M, k • x ∈ N := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := (M : Type _))
  choose d hd hdmem using fun y : M ↦ h (y : A) y.2
  refine ⟨∏ y ∈ s, d y, Finset.prod_ne_zero_iff.2 fun y _ ↦ hd y, fun x hx ↦ ?_⟩
  have hmem : (⟨x, hx⟩ : M) ∈ Submodule.span ℤ (s : Set M) := by rw [hs]; trivial
  have key : ∀ y : M, y ∈ Submodule.span ℤ (s : Set M) → (∏ z ∈ s, d z) • (y : A) ∈ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        have hfac : (∏ z ∈ s.erase y, d z) * d y = ∏ z ∈ s, d z :=
          Finset.prod_erase_mul s d hy
        rw [← hfac, mul_smul]
        exact AddSubgroup.zsmul_mem _ (hdmem y) _
    | zero => simp
    | add a b _ _ ha hb =>
        rw [AddSubgroup.coe_add, smul_add]
        exact N.add_mem ha hb
    | smul c a _ ha =>
        rw [AddSubgroup.coe_zsmul, smul_comm]
        exact AddSubgroup.zsmul_mem _ ha c
  exact key _ hmem

/-- Multiplication by `k`, as an equivariant map between two stable subgroups. -/
def zsmulStableHom {M N : AddSubgroup A} [IsStableSubgroup G M] [IsStableSubgroup G N] (k : ℤ)
    (h : ∀ x ∈ M, k • x ∈ N) : M →+[G] N where
  toFun x := ⟨k • (x : A), h (x : A) x.2⟩
  map_smul' g x := Subtype.ext (by
    show k • ((g • x : M) : A) = ((g • (⟨k • (x : A), _⟩ : N) : N) : A)
    rw [coe_smul_stableSubgroup, coe_smul_stableSubgroup, smul_comm])
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by
    show k • ((x + y : M) : A) = ((⟨k • (x : A), _⟩ + ⟨k • (y : A), _⟩ : N) : A)
    rw [AddSubgroup.coe_add, AddSubgroup.coe_add, smul_add])

omit [Fintype G] in
@[simp] theorem coe_zsmulStableHom {M N : AddSubgroup A} [IsStableSubgroup G M]
    [IsStableSubgroup G N] (k : ℤ) (h : ∀ x ∈ M, k • x ∈ N) (x : M) :
    ((zsmulStableHom (G := G) k h x : N) : A) = k • (x : A) := rfl

/-- **A `ℚ`-isogeny of lattices preserves the Herbrand quotient.**  An injective equivariant
map between two lattices whose cokernel is torsion — i.e. an isomorphism after tensoring with
`ℚ`, presented by an actual map — does not change the Herbrand quotient. -/
theorem herbrand_eq_of_injective_of_torsion_coker (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g)
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [DistribMulAction G M]
    [DistribMulAction G N] [Module.Finite ℤ M] [Module.Finite ℤ N] (f : M →+[G] N)
    (hinj : Function.Injective f)
    (htor : ∀ y : N, ∃ d : ℤ, d ≠ 0 ∧ d • y ∈ f.toAddMonoidHom.range) :
    herbrand G M σ = herbrand G N σ := by
  haveI : Finite (f.toAddMonoidHom.ker) := by
    haveI : Subsingleton (f.toAddMonoidHom.ker) :=
      ⟨fun a b ↦ Subtype.ext (hinj ((show f (a : M) = 0 from a.2).trans
        (show f (b : M) = 0 from b.2).symm))⟩
    infer_instance
  haveI : Finite (N ⧸ f.toAddMonoidHom.range) := by
    haveI : Module.Finite ℤ (N ⧸ f.toAddMonoidHom.range) :=
      Module.Finite.of_surjective
        ((QuotientAddGroup.mk' f.toAddMonoidHom.range).toIntLinearMap)
        (QuotientAddGroup.mk'_surjective _)
    refine Module.finite_of_fg_torsion _ fun t ↦ ?_
    induction t using QuotientAddGroup.induction_on with | _ y =>
    obtain ⟨d, hd, hdmem⟩ := htor y
    refine ⟨⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩, ?_⟩
    show d • (QuotientAddGroup.mk y : N ⧸ f.toAddMonoidHom.range) = 0
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
    exact hdmem
  haveI := finite_tateH0_of_moduleFinite (G := G) (M := M) (σ := σ) hgen
  haveI := finite_tateH1_of_moduleFinite (G := G) (M := M) (σ := σ) hgen
  exact herbrand_eq_of_finite_ker_coker f σ

/-- **The Herbrand quotient is a commensurability invariant of `G`-stable lattices.**  If `M`
and `N` are `G`-stable, finitely generated subgroups of a torsion-free `G`-module, and each is
contained in the other up to bounded denominators, then `h(M) = h(N)`.  Two `G`-stable
lattices spanning the same rational representation satisfy these hypotheses, which is the
sense in which `h` depends only on `M ⊗ ℚ`. -/
theorem herbrand_eq_of_commensurable (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g)
    [NoZeroSMulDivisors ℤ A] {M N : AddSubgroup A} [IsStableSubgroup G M] [IsStableSubgroup G N]
    [Module.Finite ℤ M] [Module.Finite ℤ N]
    (h₁ : ∀ x ∈ M, ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ N)
    (h₂ : ∀ x ∈ N, ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ M) :
    herbrand G M σ = herbrand G N σ := by
  obtain ⟨k, hk, hkmem⟩ := exists_zsmul_mem M N h₁
  refine herbrand_eq_of_injective_of_torsion_coker hgen (zsmulStableHom (G := G) k hkmem)
    (fun x y hxy ↦ ?_) (fun y ↦ ?_)
  · exact Subtype.ext (smul_right_injective A hk (congrArg Subtype.val hxy))
  · obtain ⟨d, hd, hdmem⟩ := h₂ (y : A) y.2
    refine ⟨k * d, mul_ne_zero hk hd, ⟨⟨d • (y : A), hdmem⟩, Subtype.ext ?_⟩⟩
    show k • (d • (y : A)) = (k * d) • (y : A)
    rw [smul_smul]

end Commensurable

/-! ## Lattices in a rational representation -/

section Rational

variable {G : Type*} [Group G] [Fintype G] {σ : G} {V : Type*} [AddCommGroup V] [Module ℚ V]
  [DistribMulAction G V]

/-- A `ℚ`-vector space is torsion free over `ℤ`. -/
theorem noZeroSMulDivisors_int_of_module_rat : NoZeroSMulDivisors ℤ V := by
  refine ⟨fun {n x} h ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · exact Or.inl rfl
  · refine Or.inr ?_
    have hq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have h' : (n : ℚ) • x = 0 := by rwa [Int.cast_smul_eq_zsmul]
    have := congrArg (fun y ↦ ((n : ℚ)⁻¹ • y)) h'
    simpa [smul_smul, inv_mul_cancel₀ hq] using this

variable (M : AddSubgroup V)

/-- The set of vectors with a nonzero integer multiple in `M`, as a `ℚ`-submodule.  It is the
`ℚ`-span of `M`. -/
def denomSubmodule : Submodule ℚ V where
  carrier := {x : V | ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ M}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro x y ⟨d, hd, hdx⟩ ⟨e, he, hey⟩
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    have hxy : (d * e) • (x + y) = e • (d • x) + d • (e • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm e d]
    rw [hxy]
    exact M.add_mem (AddSubgroup.zsmul_mem _ hdx e) (AddSubgroup.zsmul_mem _ hey d)
  smul_mem' := by
    rintro q x ⟨d, hd, hdx⟩
    refine ⟨d * (q.den : ℤ), mul_ne_zero hd (by exact_mod_cast q.den_nz), ?_⟩
    have hq : ((q.den : ℤ) • (q • x)) = (q.num : ℤ) • x := by
      rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
      norm_num [Rat.den_mul_eq_num]
    have hmul : (d * (q.den : ℤ)) • (q • x) = (q.num : ℤ) • (d • x) := by
      rw [mul_smul, hq, smul_smul, smul_smul, mul_comm]
    rw [hmul]
    exact AddSubgroup.zsmul_mem _ hdx _

@[simp] theorem mem_denomSubmodule {x : V} :
    x ∈ denomSubmodule M ↔ ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ M := Iff.rfl

/-- If `M` spans `V` over `ℚ`, every vector has a nonzero integer multiple in `M`. -/
theorem exists_zsmul_mem_of_span_eq_top (h : Submodule.span ℚ (M : Set V) = ⊤) (x : V) :
    ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ M := by
  have hle : Submodule.span ℚ (M : Set V) ≤ denomSubmodule M :=
    Submodule.span_le.2 fun y hy ↦ ⟨1, one_ne_zero, by simpa using hy⟩
  exact hle (h ▸ Submodule.mem_top)

/-- **The Herbrand quotient of a `G`-stable lattice spanning a rational representation depends
only on the representation.**  This is the `ℚ[G]`-invariance of the Herbrand quotient, for two
lattices inside one and the same `ℚ[G]`-module `V`. -/
theorem herbrand_eq_of_span_eq_top (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) (N : AddSubgroup V)
    [IsStableSubgroup G M] [IsStableSubgroup G N] [Module.Finite ℤ M] [Module.Finite ℤ N]
    (hM : Submodule.span ℚ (M : Set V) = ⊤) (hN : Submodule.span ℚ (N : Set V) = ⊤) :
    herbrand G M σ = herbrand G N σ := by
  haveI := noZeroSMulDivisors_int_of_module_rat (V := V)
  exact herbrand_eq_of_commensurable hgen
    (fun x _ ↦ exists_zsmul_mem_of_span_eq_top N hN x)
    (fun x _ ↦ exists_zsmul_mem_of_span_eq_top M hM x)

end Rational

end CyclicTate
