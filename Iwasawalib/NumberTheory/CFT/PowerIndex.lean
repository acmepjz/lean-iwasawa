/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.Herbrand
public import Mathlib.GroupTheory.IndexNSmul
public import Mathlib.GroupTheory.FiniteAbelian.Basic

@[expose] public section

/-!
# The absolute index `[A : nA]` and the `n`-torsion `A[n]`

Chevalley's algebraic proof of the first fundamental inequality is a count of indices of
`n`-th powers: `[K_v^× : (K_v^×)^ℓ]`, `[E_S : E_S^ℓ]`, `[𝕀_{K,S} : 𝕀_{K,S}^ℓ]`.  The Herbrand
quotient machinery of `Iwasawalib/GroupCohomology/Herbrand.lean` computes *ratios* of such
numbers for a nontrivial Galois action; this file supplies the *absolute* numbers, by the
observation that the pair

`([A : nA], #A[n])`

is exactly the pair `(#Ĥ⁰, #Ĥ¹)` of Tate cohomology groups of a cyclic group of order `n`
acting **trivially** on `A`.  Every tool already proved for the Tate groups of a cyclic group
therefore applies verbatim, and in particular the Tate hexagon gives the six-term counting
identity of a short exact sequence with no finiteness hypothesis whatsoever.

## Main definitions

* `PowerIndex.powIndex n A` : `[A : nA]`, the index of the image of `x ↦ n • x`.  In
  multiplicative notation on a commutative group `A`, `powIndex n (Additive A) = [A : A^n]`.
* `PowerIndex.powKer n A` : `#A[n]`, the number of elements killed by `n`.

## Main statements

* `PowerIndex.card_tateH0_trivialAction`, `PowerIndex.card_tateH1_trivialAction` : the bridge.
  For the cyclic group of order `n` acting trivially, `#Ĥ⁰ = [A : nA]` and `#Ĥ¹ = #A[n]`.
* `PowerIndex.powIndex_mul_powIndex_mul_powKer` : **the six-term identity.**  For a short exact
  sequence `0 → A → B → C → 0` of abelian groups and any `n`,

  `[A : nA] · [C : nC] · #B[n] = [B : nB] · #A[n] · #C[n]`.

  No finiteness is assumed anywhere (`Nat.card` is `0` on an infinite type, and the identity
  holds in that degenerate form too).
* `PowerIndex.powIndex_eq_powKer_of_finite` : `[A : nA] = #A[n]` for a finite group `A`.
* `PowerIndex.powIndex_mul_powKer_of_surjective`,
  `PowerIndex.powIndex_mul_powKer_of_injective`,
  `PowerIndex.powIndex_mul_powKer_of_finiteIndex` : **invariance.**  If `f : A →+ B` is
  surjective with finite kernel, or injective with finite cokernel, then
  `[A : nA] · #B[n] = [B : nB] · #A[n]`.  (The general "finite kernel *and* finite cokernel"
  statement is not proved here; only these two cases are, and they are the ones used.)
* `PowerIndex.powIndex_eq_powKer_mul_of_finiteIndex` : `[A : nA] = #A[n] · [N : nN]` for a
  subgroup `N` of finite index with no `n`-torsion.
* `PowerIndex.powIndex_eq_pow_finrank_mul_powKer_of_surjective` : if `f : A →+ B` is
  surjective with finite kernel and `B` is free of finite rank `r` over `ℤ`, then
  `[A : nA] = n ^ r · #A[n]`.  This is the shape in which the `S`-unit index is used
  (`Iwasawalib/NumberTheory/CFT/SUnitPowerIndex.lean`).
* `PowerIndex.powIndex_eq_pow_finrank_mul_powKer` : the same for any finitely generated `A`,
  with `r = rank_ℤ A`: `[A : nA] = n ^ rank(A) · #A[n]`.
* `PowerIndex.mem_nsmul_range_additive`, `PowerIndex.mem_nsmul_ker_additive` : the two
  subgroups, read in multiplicative notation on a commutative group `G`, are the `n`-th powers
  and the `n`-th roots of unity.
-/

noncomputable section

open CyclicTate Module

namespace PowerIndex

/-! ## The two numbers -/

section Defs

variable (n : ℕ) (A : Type*) [AddCommGroup A]

/-- `[A : nA]`, the index of the subgroup `n • A`.  Written multiplicatively on a commutative
group `A`, this is the index `[A : A ^ n]` of the subgroup of `n`-th powers. -/
def powIndex : ℕ := (nsmulAddMonoidHom (α := A) n).range.index

/-- `#A[n]`, the number of elements of `A` killed by `n`. -/
def powKer : ℕ := Nat.card (nsmulAddMonoidHom (α := A) n).ker

variable {n A}

theorem mem_nsmul_range {x : A} :
    x ∈ (nsmulAddMonoidHom (α := A) n).range ↔ ∃ y : A, n • y = x := Iff.rfl

theorem mem_nsmul_ker {x : A} :
    x ∈ (nsmulAddMonoidHom (α := A) n).ker ↔ n • x = 0 := AddMonoidHom.mem_ker

/-- `A[n]` in the sense of `AddSubgroup.torsionBy` is the kernel of `x ↦ n • x`. -/
theorem nsmul_ker_eq_torsionBy :
    (nsmulAddMonoidHom (α := A) n).ker = AddSubgroup.torsionBy A (n : ℤ) := by
  ext x
  rw [mem_nsmul_ker, AddSubgroup.torsionBy.nsmul_iff]

theorem powKer_eq_card_torsionBy :
    powKer n A = Nat.card (AddSubgroup.torsionBy A (n : ℤ)) := by
  rw [powKer, nsmul_ker_eq_torsionBy]

end Defs

/-! ## The cyclic group of order `n` acting trivially -/

section Trivial

/-- The cyclic group of order `n`, written multiplicatively. -/
abbrev cyc (n : ℕ) : Type := Multiplicative (ZMod n)

/-- The trivial action of any monoid on any additive monoid. -/
@[instance_reducible] def trivialAction (G : Type*) [Monoid G] (A : Type*) [AddMonoid A] : DistribMulAction G A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

attribute [local instance] trivialAction

@[simp] theorem trivial_smul {G : Type*} [Monoid G] {A : Type*} [AddMonoid A] (g : G) (a : A) :
    g • a = a := rfl

variable (n : ℕ) [NeZero n] (A : Type*) [AddCommGroup A]

theorem card_cyc : Nat.card (cyc n) = n := by
  simp [cyc, Nat.card_eq_fintype_card]

/-- The generator of `cyc n`. -/
abbrev cycGen (n : ℕ) : cyc n := Multiplicative.ofAdd (1 : ZMod n)

variable {n A}

/-- For the trivial action, the norm endomorphism is `x ↦ n • x`. -/
theorem normHom_trivialAction :
    normHom (cyc n) A = nsmulAddMonoidHom (α := A) n := by
  ext x
  rw [normHom_apply]
  simp only [trivial_smul, Finset.sum_const, Finset.card_univ]
  have hc : Fintype.card (cyc n) = n := by simp [cyc]
  rw [hc]
  rfl

omit [NeZero n] in
/-- For the trivial action, `σ - 1` is zero. -/
theorem subHom_trivialAction (σ : cyc n) : subHom (M := A) σ = 0 := by
  ext x
  simp

omit [NeZero n] in
theorem kerSub_trivialAction (σ : cyc n) : kerSub (cyc n) A σ = ⊤ := by
  ext x
  simp

omit [NeZero n] in
theorem rangeSub_trivialAction (σ : cyc n) : rangeSub (cyc n) A σ = ⊥ := by
  ext x
  rw [mem_rangeSub]
  simp [eq_comm]

theorem rangeNorm_trivialAction :
    rangeNorm (cyc n) A = (nsmulAddMonoidHom (α := A) n).range := by
  rw [rangeNorm, normHom_trivialAction]

theorem kerNorm_trivialAction :
    kerNorm (cyc n) A = (nsmulAddMonoidHom (α := A) n).ker := by
  rw [kerNorm, normHom_trivialAction]

/-- **`#Ĥ⁰ = [A : nA]`** for the cyclic group of order `n` acting trivially on `A`. -/
theorem card_tateH0_trivialAction (σ : cyc n) :
    Nat.card (TateH0 (cyc n) A σ) = powIndex n A := by
  show (rangeNorm (cyc n) A).relIndex (kerSub (cyc n) A σ) = _
  rw [rangeNorm_trivialAction, kerSub_trivialAction, AddSubgroup.relIndex_top_right, powIndex]

/-- **`#Ĥ¹ = #A[n]`** for the cyclic group of order `n` acting trivially on `A`. -/
theorem card_tateH1_trivialAction (σ : cyc n) :
    Nat.card (TateH1 (cyc n) A σ) = powKer n A := by
  show ((rangeSub (cyc n) A σ).addSubgroupOf (kerNorm (cyc n) A)).index = _
  rw [rangeSub_trivialAction, AddSubgroup.bot_addSubgroupOf, AddSubgroup.index_bot,
    kerNorm_trivialAction, powKer]

/-- The Herbrand quotient of the trivial action of `cyc n` is `[A : nA] / #A[n]`. -/
theorem herbrand_trivialAction (σ : cyc n) :
    herbrand (cyc n) A σ = (powIndex n A : ℚ) / (powKer n A : ℚ) := by
  rw [herbrand_def, card_tateH0_trivialAction, card_tateH1_trivialAction]

end Trivial


/-! ## The six-term counting identity -/

section Exact

open scoped Classical in
attribute [local instance] trivialAction

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- An additive homomorphism is equivariant for the trivial actions. -/
def toEquivariant (n : ℕ) (f : A →+ B) : A →+[cyc n] B where
  toFun := f
  map_smul' _ _ := rfl
  map_zero' := f.map_zero
  map_add' := f.map_add

@[simp] theorem toEquivariant_apply (n : ℕ) (f : A →+ B) (a : A) :
    toEquivariant n f a = f a := rfl

/-- **The six-term counting identity.**  For a short exact sequence `0 → A → B → C → 0` of
abelian groups and any `n`,

`[A : nA] · [C : nC] · #B[n] = [B : nB] · #A[n] · #C[n]`.

This is the Tate hexagon of `Iwasawalib/GroupCohomology/TateHexagon.lean` for the cyclic group
of order `n` acting trivially.  **No finiteness hypothesis of any kind.** -/
theorem powIndex_mul_powIndex_mul_powKer {n : ℕ} (hn : n ≠ 0) (i : A →+ B) (p : B →+ C)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : ∀ b : B, p b = 0 ↔ ∃ a : A, i a = b) :
    powIndex n A * powIndex n C * powKer n B
      = powIndex n B * powKer n A * powKer n C := by
  haveI : NeZero n := ⟨hn⟩
  have hse : CyclicTate.IsShortExact (toEquivariant n i) (toEquivariant n p) :=
    ⟨hi, hp, hex⟩
  have := hse.card_tate_alternating (σ := cycGen n)
  rwa [card_tateH0_trivialAction, card_tateH0_trivialAction, card_tateH1_trivialAction,
    card_tateH0_trivialAction, card_tateH1_trivialAction, card_tateH1_trivialAction] at this

/-- The six-term identity for the short exact sequence `0 → N → A → A / N → 0`. -/
theorem powIndex_mul_powIndex_quotient_mul_powKer {n : ℕ} (hn : n ≠ 0) (N : AddSubgroup A) :
    powIndex n N * powIndex n (A ⧸ N) * powKer n A
      = powIndex n A * powKer n N * powKer n (A ⧸ N) :=
  powIndex_mul_powIndex_mul_powKer hn N.subtype (QuotientAddGroup.mk' N)
    (fun _ _ h ↦ Subtype.ext h) (QuotientAddGroup.mk'_surjective N)
    (fun b ↦ ⟨fun hb ↦ ⟨⟨b, (QuotientAddGroup.eq_zero_iff b).1 hb⟩, rfl⟩,
      fun ⟨a, ha⟩ ↦ ha ▸ (QuotientAddGroup.eq_zero_iff _).2 a.2⟩)

end Exact

/-! ## The finite case -/

section Finite

attribute [local instance] trivialAction

variable (n : ℕ) (A : Type*) [AddCommGroup A] [Finite A]

/-- **`[A : nA] = #A[n]` for a finite abelian group.**  Both counts are the order of the same
Tate cohomology group of the trivial action. -/
theorem powIndex_eq_powKer_of_finite (hn : n ≠ 0) : powIndex n A = powKer n A := by
  haveI : NeZero n := ⟨hn⟩
  rw [← card_tateH0_trivialAction (A := A) (cycGen n), ← card_tateH1_trivialAction (A := A)
    (cycGen n)]
  exact card_tateH0_eq_card_tateH1 _

theorem powKer_pos : 0 < powKer n A :=
  Nat.card_pos_iff.2 ⟨⟨0⟩, inferInstance⟩

theorem powIndex_pos (hn : n ≠ 0) : 0 < powIndex n A := by
  rw [powIndex_eq_powKer_of_finite n A hn]
  exact powKer_pos n A

end Finite

/-! ## Invariance under maps with finite kernel or cokernel -/

section Invariance

attribute [local instance] trivialAction

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] {n : ℕ}

/-- **Invariance along a surjection with finite kernel.**  If `f : A →+ B` is surjective with
finite kernel then `[A : nA] · #B[n] = [B : nB] · #A[n]`. -/
theorem powIndex_mul_powKer_of_surjective (hn : n ≠ 0) (f : A →+ B)
    (hf : Function.Surjective f) [Finite f.ker] :
    powIndex n A * powKer n B = powIndex n B * powKer n A := by
  have h := powIndex_mul_powIndex_mul_powKer (A := f.ker) (B := A) (C := B) hn
    f.ker.subtype f (fun _ _ h ↦ Subtype.ext h) hf
    (fun b ↦ ⟨fun hb ↦ ⟨⟨b, hb⟩, rfl⟩, fun ⟨a, ha⟩ ↦ ha ▸ a.2⟩)
  rw [powIndex_eq_powKer_of_finite n f.ker hn] at h
  have hk : 0 < powKer n (f.ker) := powKer_pos n _
  refine Nat.eq_of_mul_eq_mul_left hk ?_
  rw [show powKer n (f.ker) * (powIndex n A * powKer n B)
      = powIndex n A * powKer n (f.ker) * powKer n B from by ring, ← h]
  ring

/-- **Invariance along an injection with finite cokernel.**  If `f : A →+ B` is injective with
finite cokernel then `[A : nA] · #B[n] = [B : nB] · #A[n]`. -/
theorem powIndex_mul_powKer_of_injective (hn : n ≠ 0) (f : A →+ B)
    (hf : Function.Injective f) [Finite (B ⧸ f.range)] :
    powIndex n A * powKer n B = powIndex n B * powKer n A := by
  have h := powIndex_mul_powIndex_mul_powKer (A := A) (B := B) (C := B ⧸ f.range) hn
    f (QuotientAddGroup.mk' f.range) hf (QuotientAddGroup.mk'_surjective _)
    (fun b ↦ ⟨fun hb ↦ (QuotientAddGroup.eq_zero_iff b).1 hb,
      fun ⟨a, ha⟩ ↦ (QuotientAddGroup.eq_zero_iff b).2 ⟨a, ha⟩⟩)
  rw [powIndex_eq_powKer_of_finite n (B ⧸ f.range) hn] at h
  have hc : 0 < powKer n (B ⧸ f.range) := powKer_pos n _
  refine Nat.eq_of_mul_eq_mul_right hc ?_
  calc powIndex n A * powKer n B * powKer n (B ⧸ f.range)
      = powIndex n A * powKer n (B ⧸ f.range) * powKer n B := by ring
    _ = powIndex n B * powKer n A * powKer n (B ⧸ f.range) := h

/-- A subgroup of finite index has the same `[· : n ·] / #·[n]` ratio as the whole group. -/
theorem powIndex_mul_powKer_of_finiteIndex (hn : n ≠ 0) (N : AddSubgroup A) [Finite (A ⧸ N)] :
    powIndex n N * powKer n A = powIndex n A * powKer n N := by
  haveI : Finite (A ⧸ N.subtype.range) := by
    rwa [AddSubgroup.range_subtype]
  exact powIndex_mul_powKer_of_injective hn N.subtype (fun _ _ h ↦ Subtype.ext h)

/-- If `f : A →+ B` is injective and every `n`-torsion element of `B` is in its image, then `A`
and `B` have the same `n`-torsion.  (Typical use: `A = 𝒪ˣ ⊆ B = Fˣ` for a valued field — every
root of unity is a unit of the valuation ring.) -/
theorem powKer_eq_of_injective_of_torsion_le (f : A →+ B) (hf : Function.Injective f)
    (h : ∀ b : B, n • b = 0 → ∃ a : A, f a = b) : powKer n A = powKer n B := by
  have hmemA : ∀ a : A, a ∈ (nsmulAddMonoidHom (α := A) n).ker ↔ n • a = 0 :=
    fun _ ↦ mem_nsmul_ker
  have hmemB : ∀ b : B, b ∈ (nsmulAddMonoidHom (α := B) n).ker ↔ n • b = 0 :=
    fun _ ↦ mem_nsmul_ker
  refine Nat.card_congr (Equiv.ofBijective
    (fun a : (nsmulAddMonoidHom (α := A) n).ker ↦
      (⟨f (a : A), (hmemB _).2 (by rw [← map_nsmul, (hmemA _).1 a.2, map_zero])⟩ :
        (nsmulAddMonoidHom (α := B) n).ker)) ⟨?_, ?_⟩)
  · intro a a' haa
    have hval : f (a : A) = f (a' : A) := by simpa using haa
    exact Subtype.ext (hf hval)
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := h b ((hmemB _).1 hb)
    refine ⟨⟨a, (hmemA _).2 (hf ?_)⟩, rfl⟩
    rw [map_nsmul, (hmemB _).1 hb, map_zero]

/-- **The index of `n`-th powers is computed on any torsion-free subgroup of finite index.**
If `N ≤ A` has finite index and no `n`-torsion, then

`[A : nA] = #A[n] · [N : nN]`.

This is the shape of the local computation `[𝒪^× : (𝒪^×)^n] = #μ_n · [U^{(m)} : (U^{(m)})^n]`:
the principal units `U^{(m)}` of high level form a torsion-free subgroup of finite index of
`𝒪^×`, and the `p`-adic logarithm identifies them with `(𝒪, +)`, on which the `n`-th power
index is `|n|^{-1}`. -/
theorem powIndex_eq_powKer_mul_of_finiteIndex (hn : n ≠ 0) (N : AddSubgroup A)
    [Finite (A ⧸ N)] (hN : powKer n N = 1) :
    powIndex n A = powKer n A * powIndex n N := by
  have h := powIndex_mul_powKer_of_finiteIndex (A := A) hn N
  rw [hN, mul_one] at h
  rw [← h, mul_comm]

end Invariance

/-! ## Free and finitely generated groups -/

section FG

open Module

variable (n : ℕ) (A : Type*) [AddCommGroup A]

/-- For a torsion-free group there is no `n`-torsion: `#A[n] = 1` for `n ≠ 0`. -/
theorem powKer_eq_one_of_isTorsionFree [IsTorsionFree ℤ A] (hn : n ≠ 0) : powKer n A = 1 := by
  have hbot : (nsmulAddMonoidHom (α := A) n).ker = ⊥ :=
    (AddMonoidHom.ker_eq_bot_iff _).2
      (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hn)
  rw [powKer, hbot]
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨0⟩⟩

/-- **`[A : nA] = n ^ rank A` for a free finitely generated group.**  This is
`AddSubgroup.index_range_nsmul`, stated in the present notation. -/
theorem powIndex_of_free [Module.Free ℤ A] [Module.Finite ℤ A] :
    powIndex n A = n ^ finrank ℤ A :=
  AddSubgroup.index_range_nsmul A n

theorem powKer_of_free [Module.Free ℤ A] (hn : n ≠ 0) : powKer n A = 1 :=
  powKer_eq_one_of_isTorsionFree n A hn

variable {n A}

/-- **The index of `n`-th powers of a group with a free finitely generated quotient by a finite
subgroup.**  If `f : A →+ B` is surjective with finite kernel and `B` is free of finite rank `r`
over `ℤ`, then

`[A : nA] = n ^ r · #A[n]`.

This is the form in which the `S`-unit index is computed: `B` is the `S`-unit lattice, of rank
`#S - 1`, and the kernel is the finite group of roots of unity. -/
theorem powIndex_eq_pow_finrank_mul_powKer_of_surjective (hn : n ≠ 0)
    {B : Type*} [AddCommGroup B] [Module.Free ℤ B] [Module.Finite ℤ B]
    (f : A →+ B) (hf : Function.Surjective f) [Finite f.ker] :
    powIndex n A = n ^ finrank ℤ B * powKer n A := by
  have h := powIndex_mul_powKer_of_surjective hn f hf
  rwa [powKer_of_free n B hn, mul_one, powIndex_of_free n B] at h

/-- A finite abelian group has `ℤ`-rank zero. -/
theorem finrank_int_eq_zero_of_finite (D : Type*) [AddCommGroup D] [Finite D] :
    finrank ℤ D = 0 := by
  classical
  cases nonempty_fintype D
  refine Module.finrank_eq_zero_of_not_faithfulSMul ?_
  intro h
  have key : ∀ x : D, (Fintype.card D : ℤ) • x = (0 : ℤ) • x := by
    intro x
    rw [zero_smul, natCast_zsmul]
    exact card_nsmul_eq_zero
  have h1 : (Fintype.card D : ℤ) = 0 := eq_of_smul_eq_smul (α := D) key
  have h2 : Fintype.card D = 0 := by exact_mod_cast h1
  exact absurd h2 Fintype.card_ne_zero

/-- For `F` free finitely generated and `D` finite, `rank (F × D) = rank F`. -/
theorem finrank_prod_finite (F D : Type*) [AddCommGroup F] [AddCommGroup D]
    [Module.Free ℤ F] [Module.Finite ℤ F] [Finite D] :
    finrank ℤ (F × D) = finrank ℤ F := by
  haveI : Module.Finite ℤ D := Module.Finite.of_finite
  set N : Submodule ℤ (F × D) := LinearMap.ker (LinearMap.fst ℤ F D) with hN
  haveI : Finite N := Finite.of_injective (fun x : N ↦ ((x : F × D).2 : D)) (by
    rintro ⟨⟨a, b⟩, ha⟩ ⟨⟨a', b'⟩, ha'⟩ h
    have ha0 : a = 0 := ha
    have ha0' : a' = 0 := ha'
    simp_all)
  have hq : ((F × D) ⧸ N) ≃ₗ[ℤ] F :=
    LinearMap.quotKerEquivOfSurjective (LinearMap.fst ℤ F D) (fun y ↦ ⟨(y, 0), rfl⟩)
  have := Submodule.finrank_quotient_add_finrank (R := ℤ) N
  rw [hq.finrank_eq, finrank_int_eq_zero_of_finite N, Nat.add_zero] at this
  exact this.symm

/-- **`[A : nA] = n ^ rank(A) · #A[n]` for a finitely generated abelian group.**

This is the absolute index that the Herbrand quotient cannot see: the Herbrand quotient of a
finite module is `1`, so cohomological methods give the ratio `[A : nA] / #A[n]` and nothing
more, and this theorem evaluates that ratio as `n ^ rank(A)`.  For the `S`-units of a number
field, of rank `#S - 1`, it gives `[E_S : E_S^n] = n ^ (#S - 1) · #μ_n`. -/
theorem powIndex_eq_pow_finrank_mul_powKer {n : ℕ} (hn : n ≠ 0) (A : Type*) [AddCommGroup A]
    [AddGroup.FG A] : powIndex n A = n ^ finrank ℤ A * powKer n A := by
  classical
  obtain ⟨m, ι, fι, p, hp, e, ⟨φ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  haveI : ∀ i, NeZero (p i ^ e i) := fun i ↦ ⟨pow_ne_zero _ (hp i).pos.ne'⟩
  haveI : ∀ i, Finite (ZMod (p i ^ e i)) := fun i ↦ inferInstance
  haveI : Finite (DirectSum ι fun i ↦ ZMod (p i ^ e i)) :=
    Finite.of_equiv _ (DFinsupp.equivFunOnFintype (β := fun i ↦ ZMod (p i ^ e i))).symm
  set D := DirectSum ι fun i ↦ ZMod (p i ^ e i) with hD
  set F := (Fin m →₀ ℤ) with hF
  let f : A →+ F := (AddMonoidHom.fst F D).comp φ.toAddMonoidHom
  have hfapp : ∀ a : A, f a = (φ a).1 := fun a ↦ rfl
  have hfsurj : Function.Surjective f := fun y ↦ ⟨φ.symm (y, 0), by
    rw [hfapp, φ.apply_symm_apply]⟩
  haveI : Finite f.ker := Finite.of_injective (fun x : f.ker ↦ ((φ (x : A)).2 : D)) (by
    rintro ⟨a, ha⟩ ⟨a', ha'⟩ h
    have h1 : (φ a).1 = 0 := ha
    have h2 : (φ a').1 = 0 := ha'
    refine Subtype.ext (φ.injective (Prod.ext ?_ h))
    rw [h1, h2])
  have h2 : finrank ℤ (Fin m →₀ ℤ) = m := by simp
  have hAfin : finrank ℤ A = m := by
    have h1 : finrank ℤ A = finrank ℤ (F × D) := φ.toIntLinearEquiv.finrank_eq
    have h3 : finrank ℤ (F × D) = finrank ℤ F := finrank_prod_finite F D
    have h4 : finrank ℤ F = m := h2
    rw [h1, h3, h4]
  rw [powIndex_eq_pow_finrank_mul_powKer_of_surjective hn f hfsurj, hAfin,
    show finrank ℤ F = m from h2]

/-- `[ℤ : nℤ] = n`. -/
@[simp] theorem powIndex_int (n : ℕ) : powIndex n ℤ = n := by
  rw [powIndex_of_free n ℤ, Module.finrank_self, pow_one]

/-- `ℤ` has no `n`-torsion for `n ≠ 0`. -/
@[simp] theorem powKer_int {n : ℕ} (hn : n ≠ 0) : powKer n ℤ = 1 :=
  powKer_eq_one_of_isTorsionFree n ℤ hn

end FG

/-! ## Multiplicative notation -/

section Mul

variable (G : Type*) [CommGroup G] (n : ℕ)

/-- The subgroup measured by `powIndex n (Additive G)` is the subgroup of `n`-th powers. -/
theorem mem_nsmul_range_additive {x : G} :
    Additive.ofMul x ∈ (nsmulAddMonoidHom (α := Additive G) n).range ↔ ∃ y : G, y ^ n = x := by
  rw [mem_nsmul_range]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨Additive.toMul y, by
      rw [← toMul_nsmul, hy, toMul_ofMul]⟩,
    fun ⟨y, hy⟩ ↦ ⟨Additive.ofMul y, by
      refine Additive.toMul.injective ?_
      rw [toMul_nsmul, toMul_ofMul, toMul_ofMul, hy]⟩⟩

/-- The subgroup measured by `powKer n (Additive G)` is the group of `n`-th roots of unity. -/
theorem mem_nsmul_ker_additive {x : G} :
    Additive.ofMul x ∈ (nsmulAddMonoidHom (α := Additive G) n).ker ↔ x ^ n = 1 := by
  rw [mem_nsmul_ker]
  constructor
  · intro h
    have := congrArg Additive.toMul h
    rwa [toMul_nsmul, toMul_ofMul, toMul_zero] at this
  · intro h
    refine Additive.toMul.injective ?_
    rw [toMul_nsmul, toMul_ofMul, toMul_zero, h]

end Mul

end PowerIndex
