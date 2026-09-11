/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.CyclicTate
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

/-!
# `Ĥ⁰` of a cyclic group in a tower, and the reduction to prime degree

Let `M` be a module over a finite cyclic group `G = ⟨σ⟩` of order `n`, and let
`T : AddMonoid.End M` be the action of `σ`.  Then `T ^ n = 1`, and for every `a ∣ n` the
subgroup `H_a = ⟨σ ^ a⟩` has invariants

`M ^ H_a = ker (T ^ a - 1) = CyclicTate.invSub T a`.

For `a` and `b`, the *relative norm* from level `a * b` to level `a` is
`1 + T ^ a + ⋯ + T ^ (a * (b - 1)) = CyclicTate.powSum (T ^ a) b`; it carries `M ^ H_{a*b}` into
`M ^ H_a`, and the index of its image is

`CyclicTate.relTateH0 T a b = #Ĥ⁰(H_a / H_{a*b}, M ^ H_{a*b})`,

the order of the Tate group of the cyclic quotient of order `b` acting on `M ^ H_{a*b}`.  For
`a = 1` and `b = n` this is `#Ĥ⁰(G, M)` itself
(`CyclicTate.card_tateH0_eq_relTateH0`).

## Main statements

Everything in this file is unconditional.

* `CyclicTate.relTateH0_dvd_tower` : `relTateH0 T a (b * c) ∣ relTateH0 T a b * relTateH0 T (a*b) c`.
  The exact content is that `#Ĥ⁰` of the whole is the product of `#Ĥ⁰` of the quotient by the
  index of a subgroup that is a quotient of `#Ĥ⁰` of the subgroup — inflation and restriction,
  written out by hand for a cyclic group, with no spectral sequence.
* `CyclicTate.relTateH0_dvd_chainBound`, `CyclicTate.relTateH0_le_prod` : the iteration of the
  tower inequality along a chain of degrees.
* `CyclicTate.nsmul_eq_zero_of_relTateH0` : the degree-`b` relative `Ĥ⁰` is killed by `b`.
* `CyclicTate.card_tateH0_le_of_chain`, `CyclicTate.card_tateH0_le_of_primeFactors` : if every
  step of a chain (for instance the prime factorisation of `|G|`) has `#Ĥ⁰` finite and at most
  its degree, then `#Ĥ⁰(G, M) ≤ |G|`.

## Why this is the reduction to prime degree

For `M = C_L` and `G = Gal(L/K)` cyclic, `M ^ H_a = C_{L ^ H_a}` (see
`Iwasawalib/NumberTheory/CFT/TateTowerIntermediate.lean`), and `relTateH0 T a b` is the norm
index of the degree-`b` step `L ^ H_{a*b} / L ^ H_a`.  So
`CyclicTate.card_tateH0_le_of_primeFactors` says: the first fundamental inequality for a cyclic
extension follows from the first fundamental inequality for each cyclic **prime-degree** step of
any tower refining it.  That is step 1 of Chevalley's algebraic proof, and it is proved here
with no hypothesis at all.
-/

noncomputable section

namespace CyclicTate

open Finset

variable {M : Type*} [AddCommGroup M]

/-! ## Geometric sums of an additive endomorphism -/

/-- `powSum T n = 1 + T + ⋯ + T ^ (n - 1)`, the norm of the cyclic group `⟨T⟩` of order `n`. -/
def powSum (T : AddMonoid.End M) (n : ℕ) : AddMonoid.End M := ∑ i ∈ range n, T ^ i

@[simp] theorem powSum_zero (T : AddMonoid.End M) : powSum T 0 = 0 := by simp [powSum]

@[simp] theorem powSum_one (T : AddMonoid.End M) : powSum T 1 = 1 := by simp [powSum]

theorem powSum_succ (T : AddMonoid.End M) (n : ℕ) : powSum T (n + 1) = powSum T n + T ^ n := by
  simp [powSum, Finset.sum_range_succ]

theorem powSum_add (T : AddMonoid.End M) (m n : ℕ) :
    powSum T (m + n) = powSum T m + T ^ m * powSum T n := by
  simp only [powSum, Finset.sum_range_add, Finset.mul_sum, pow_add]

/-- The key factorisation `1 + T + ⋯ + T ^ (ab - 1) = (1 + T ^ a + ⋯) (1 + T + ⋯ + T ^ (a-1))`. -/
theorem powSum_mul (T : AddMonoid.End M) (a b : ℕ) :
    powSum T (a * b) = powSum (T ^ a) b * powSum T a := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Nat.mul_succ, powSum_add, ih, powSum_succ, add_mul, ← pow_mul]

theorem commute_powSum (T : AddMonoid.End M) (m n p q : ℕ) :
    Commute (powSum (T ^ m) p) (powSum (T ^ n) q) := by
  unfold powSum
  refine Commute.sum_left _ _ _ fun i _ ↦ Commute.sum_right _ _ _ fun j _ ↦ ?_
  rw [← pow_mul, ← pow_mul]
  exact (Commute.refl T).pow_pow _ _

/-- `(T ^ a - 1) * powSum (T ^ a) b = T ^ (a * b) - 1`. -/
theorem sub_one_mul_powSum (T : AddMonoid.End M) (a b : ℕ) :
    (T ^ a - 1) * powSum (T ^ a) b = T ^ (a * b) - 1 := by
  induction b with
  | zero => simp
  | succ b ih =>
      have h : (T : AddMonoid.End M) ^ a * T ^ (a * b) = T ^ (a * (b + 1)) := by
        rw [← pow_add, Nat.mul_succ, Nat.add_comm]
      rw [powSum_succ, mul_add, ih, ← pow_mul, sub_mul, one_mul, h]
      abel

/-! ## Invariants and relative norms -/

theorem pow_apply_eq_self {S : AddMonoid.End M} {x : M} (h : S x = x) :
    ∀ c : ℕ, (S ^ c) x = x
  | 0 => rfl
  | (c + 1) => by rw [pow_succ]; show (S ^ c) (S x) = x; rw [h, pow_apply_eq_self h c]

/-- `invSub T a` is the kernel of `T ^ a - 1`.  When `T` is the action of a generator `σ` of a
finite cyclic group `G`, this is `M ^ H` for `H = ⟨σ ^ a⟩`. -/
def invSub (T : AddMonoid.End M) (a : ℕ) : AddSubgroup M := AddMonoidHom.ker (T ^ a - 1)

theorem mem_invSub {T : AddMonoid.End M} {a : ℕ} {x : M} :
    x ∈ invSub T a ↔ (T ^ a) x = x := by
  rw [invSub, AddMonoidHom.mem_ker]
  show (T ^ a) x - x = 0 ↔ _
  rw [sub_eq_zero]

theorem invSub_mono {T : AddMonoid.End M} {a b : ℕ} (h : a ∣ b) : invSub T a ≤ invSub T b := by
  obtain ⟨c, rfl⟩ := h
  intro x hx
  rw [mem_invSub] at hx ⊢
  rw [pow_mul]
  exact pow_apply_eq_self hx c

/-- The image in `M ^ ⟨T ^ a⟩` of `M ^ ⟨T ^ (a * b)⟩` under the relative norm
`1 + T ^ a + ⋯ + T ^ (a * (b - 1))`. -/
def relNorm (T : AddMonoid.End M) (a b : ℕ) : AddSubgroup M :=
  (invSub T (a * b)).map (powSum (T ^ a) b)

/-- The relative `Ĥ⁰` of the cyclic quotient `⟨T ^ a⟩ / ⟨T ^ (a * b)⟩`, of order `b`, acting on
`M ^ ⟨T ^ (a * b)⟩`: the index of the relative norms inside the invariants. -/
def relTateH0 (T : AddMonoid.End M) (a b : ℕ) : ℕ := (relNorm T a b).relIndex (invSub T a)

theorem relTateH0_eq_card (T : AddMonoid.End M) (a b : ℕ) :
    relTateH0 T a b
      = Nat.card (invSub T a ⧸ (relNorm T a b).addSubgroupOf (invSub T a)) := rfl

theorem relNorm_le (T : AddMonoid.End M) (a b : ℕ) : relNorm T a b ≤ invSub T a := by
  rintro _ ⟨y, hy, rfl⟩
  replace hy : y ∈ invSub T (a * b) := hy
  rw [mem_invSub] at hy ⊢
  have h : (T ^ a) ((powSum (T ^ a) b) y) - (powSum (T ^ a) b) y
      = ((T : AddMonoid.End M) ^ (a * b)) y - y :=
    congrArg (fun f : AddMonoid.End M ↦ f y) (sub_one_mul_powSum T a b)
  rw [hy, sub_self, sub_eq_zero] at h
  exact h

theorem map_one_eq (A : AddSubgroup M) : A.map (1 : AddMonoid.End M) = A := by
  ext x
  exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun h ↦ ⟨x, h, rfl⟩⟩

@[simp] theorem relNorm_self_one (T : AddMonoid.End M) (a : ℕ) : relNorm T a 1 = invSub T a := by
  rw [relNorm, mul_one, powSum_one, map_one_eq]

@[simp] theorem relTateH0_self_one (T : AddMonoid.End M) (a : ℕ) : relTateH0 T a 1 = 1 := by
  rw [relTateH0, relNorm_self_one, AddSubgroup.relIndex_self]

/-! ## The exponent of the relative `Ĥ⁰` -/

/-- On the invariants at level `a`, the relative norm to level `a * b` is multiplication by
`b`. -/
theorem powSum_apply_of_mem_invSub (T : AddMonoid.End M) (a b : ℕ) {x : M}
    (hx : x ∈ invSub T a) : (powSum (T ^ a) b) x = b • x := by
  rw [mem_invSub] at hx
  induction b with
  | zero => simp
  | succ b ih =>
      rw [powSum_succ]
      show (powSum (T ^ a) b) x + ((T ^ a) ^ b) x = _
      rw [ih, pow_apply_eq_self hx b, succ_nsmul]

/-- **The relative `Ĥ⁰` of a step of degree `b` is killed by `b`.** -/
theorem nsmul_mem_relNorm (T : AddMonoid.End M) (a b : ℕ) {x : M} (hx : x ∈ invSub T a) :
    b • x ∈ relNorm T a b :=
  ⟨x, invSub_mono (Dvd.intro b rfl) hx, powSum_apply_of_mem_invSub T a b hx⟩

/-- **`Ĥ⁰` of the degree-`b` step is a `ℤ/b`-module.** -/
theorem nsmul_eq_zero_of_relTateH0 (T : AddMonoid.End M) (a b : ℕ)
    (y : invSub T a ⧸ (relNorm T a b).addSubgroupOf (invSub T a)) : b • y = 0 := by
  induction y using QuotientAddGroup.induction_on with | _ x =>
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact nsmul_mem_relNorm T a b x.2

/-! ## The tower inequality -/

theorem powSum_mul_comm (T : AddMonoid.End M) (a b c : ℕ) :
    powSum (T ^ a) (b * c) = powSum (T ^ a) b * powSum (T ^ (a * b)) c := by
  rw [powSum_mul (T ^ a) b c, ← pow_mul]
  exact commute_powSum T (a * b) a c b

/-- The relative norms from level `a * b * c` down to level `a` factor through level `a * b`. -/
theorem relNorm_tower (T : AddMonoid.End M) (a b c : ℕ) :
    relNorm T a (b * c) = (relNorm T (a * b) c).map (powSum (T ^ a) b) := by
  rw [relNorm, relNorm, AddSubgroup.map_map, ← mul_assoc, powSum_mul_comm]
  rfl

/-- A homomorphic image can only collapse a relative index. -/
theorem relIndex_map_dvd {N : Type*} [AddCommGroup N] (f : M →+ N) {A B : AddSubgroup M}
    (h : A ≤ B) : (A.map f).relIndex (B.map f) ∣ A.relIndex B := by
  have hsup : B ⊔ (A ⊔ f.ker) = B ⊔ f.ker := by
    rw [← sup_assoc, sup_of_le_left h]
  have h1 : (A.map f).relIndex (B.map f) = ((A ⊔ f.ker) ⊓ B).relIndex B := by
    rw [AddSubgroup.relIndex_map_map, AddSubgroup.inf_relIndex_right, ← hsup,
      AddSubgroup.relIndex_sup_right]
  rw [h1]
  exact Dvd.intro_left _ (AddSubgroup.relIndex_mul_relIndex A ((A ⊔ f.ker) ⊓ B) B
    (le_inf le_sup_left h) inf_le_right)

/-- **The tower inequality for `Ĥ⁰`.**  For a cyclic group `⟨T ^ a⟩ / ⟨T ^ (a * b * c)⟩` of order
`b * c` acting on `M ^ ⟨T ^ (a * b * c)⟩`, the order of `Ĥ⁰` divides the product of the orders of
`Ĥ⁰` for the quotient of order `b` and for the subgroup of order `c`. -/
theorem relTateH0_dvd_tower (T : AddMonoid.End M) (a b c : ℕ) :
    relTateH0 T a (b * c) ∣ relTateH0 T a b * relTateH0 T (a * b) c := by
  set f := powSum (T ^ a) b with hf
  have hRB : relNorm T (a * b) c ≤ invSub T (a * b) := relNorm_le T (a * b) c
  have hQP : relNorm T a (b * c) ≤ relNorm T a b := by
    rw [relNorm_tower, relNorm]
    exact AddSubgroup.map_mono hRB
  have hPA : relNorm T a b ≤ invSub T a := relNorm_le T a b
  have hsplit : relTateH0 T a (b * c)
      = (relNorm T a (b * c)).relIndex (relNorm T a b) * relTateH0 T a b :=
    (AddSubgroup.relIndex_mul_relIndex _ _ _ hQP hPA).symm
  rw [hsplit, mul_comm (relTateH0 T a b)]
  refine Nat.mul_dvd_mul ?_ dvd_rfl
  rw [relNorm_tower, relNorm]
  exact relIndex_map_dvd f hRB

/-! ## Chains of steps -/

/-- The bound coming from a chain of successive steps `a, a * p₁, a * p₁ * p₂, …`. -/
def chainBound (T : AddMonoid.End M) : ℕ → List ℕ → ℕ
  | _, [] => 1
  | a, (p :: l) => relTateH0 T a p * chainBound T (a * p) l

@[simp] theorem chainBound_nil (T : AddMonoid.End M) (a : ℕ) : chainBound T a [] = 1 := rfl

@[simp] theorem chainBound_cons (T : AddMonoid.End M) (a p : ℕ) (l : List ℕ) :
    chainBound T a (p :: l) = relTateH0 T a p * chainBound T (a * p) l := rfl

/-- **The order of `Ĥ⁰` divides the product of the orders along any chain of subgroups.** -/
theorem relTateH0_dvd_chainBound (T : AddMonoid.End M) :
    ∀ (a : ℕ) (l : List ℕ), relTateH0 T a l.prod ∣ chainBound T a l
  | a, [] => by simp
  | a, (p :: l) => by
      rw [List.prod_cons, chainBound_cons]
      exact (relTateH0_dvd_tower T a p l.prod).trans
        (Nat.mul_dvd_mul dvd_rfl (relTateH0_dvd_chainBound T (a * p) l))

/-- Every step of the chain is finite and bounded by its degree. -/
def ChainLe (T : AddMonoid.End M) : ℕ → List ℕ → Prop
  | _, [] => True
  | a, (p :: l) => 0 < relTateH0 T a p ∧ relTateH0 T a p ≤ p ∧ ChainLe T (a * p) l

@[simp] theorem chainLe_nil (T : AddMonoid.End M) (a : ℕ) : ChainLe T a [] ↔ True := Iff.rfl

theorem chainLe_cons (T : AddMonoid.End M) (a p : ℕ) (l : List ℕ) :
    ChainLe T a (p :: l) ↔
      (0 < relTateH0 T a p ∧ relTateH0 T a p ≤ p ∧ ChainLe T (a * p) l) := Iff.rfl

theorem chainBound_pos (T : AddMonoid.End M) :
    ∀ (a : ℕ) (l : List ℕ), ChainLe T a l → 0 < chainBound T a l
  | _, [], _ => Nat.one_pos
  | a, (p :: l), h => by
      rw [chainBound_cons]
      exact Nat.mul_pos h.1 (chainBound_pos T (a * p) l h.2.2)

theorem chainBound_le_prod (T : AddMonoid.End M) :
    ∀ (a : ℕ) (l : List ℕ), ChainLe T a l → chainBound T a l ≤ l.prod
  | _, [], _ => le_of_eq (by simp)
  | a, (p :: l), h => by
      rw [chainBound_cons, List.prod_cons]
      exact Nat.mul_le_mul h.2.1 (chainBound_le_prod T (a * p) l h.2.2)

/-- **The reduction to the steps of a chain.**  If every step of a chain of cyclic subquotients
has `#Ĥ⁰` finite and at most its degree, then `#Ĥ⁰` of the whole is at most the total degree. -/
theorem relTateH0_le_prod (T : AddMonoid.End M) (a : ℕ) (l : List ℕ) (h : ChainLe T a l) :
    relTateH0 T a l.prod ≤ l.prod :=
  le_trans (Nat.le_of_dvd (chainBound_pos T a l h) (relTateH0_dvd_chainBound T a l))
    (chainBound_le_prod T a l h)

/-! ## Comparison with `CyclicTate.TateH0` -/

section Module

variable {G : Type*} [Group G] [Fintype G] [DistribMulAction G M] {σ : G}

/-- The action of a group element as an additive endomorphism of the module. -/
def actEnd (σ : G) : AddMonoid.End M := DistribSMul.toAddMonoidHom M σ

omit [Fintype G] in
@[simp] theorem actEnd_apply (σ : G) (x : M) : actEnd (M := M) σ x = σ • x := rfl

omit [Fintype G] in
theorem actEnd_pow_apply (σ : G) (i : ℕ) (x : M) :
    ((actEnd (M := M) σ) ^ i) x = (σ ^ i) • x := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [pow_succ']
      show (actEnd (M := M) σ) (((actEnd (M := M) σ) ^ i) x) = _
      rw [ih, actEnd_apply, ← mul_smul, ← pow_succ']

omit [Fintype G] in
theorem powSum_actEnd_apply (σ : G) (n : ℕ) (x : M) :
    (powSum (actEnd (M := M) σ) n) x = ∑ i ∈ range n, (σ ^ i) • x := by
  induction n with
  | zero => simp [powSum]
  | succ n ih =>
      rw [powSum_succ, Finset.sum_range_succ, ← ih, ← actEnd_pow_apply]
      rfl

omit [Fintype G] in
theorem actEnd_pow (σ : G) (a : ℕ) : (actEnd (M := M) σ) ^ a = actEnd (σ ^ a) := by
  ext x
  rw [actEnd_pow_apply, actEnd_apply]

omit [Fintype G] in
/-- Membership in the `⟨σ ^ a⟩`-invariants, in terms of the action. -/
theorem mem_invSub_actEnd {σ : G} {a : ℕ} {x : M} :
    x ∈ invSub (actEnd (M := M) σ) a ↔ (σ ^ a) • x = x := by
  rw [mem_invSub, actEnd_pow_apply]

omit [Fintype G] in
/-- Membership in the image of the relative norm from level `a * b` to level `a`, in terms of
the action: `x` is a sum `∑ i < b, σ ^ (a * i) • y` over a `⟨σ ^ (a * b)⟩`-invariant `y`. -/
theorem mem_relNorm_actEnd {σ : G} {a b : ℕ} {x : M} :
    x ∈ relNorm (actEnd (M := M) σ) a b ↔
      ∃ y : M, (σ ^ (a * b)) • y = y ∧ ∑ i ∈ range b, (σ ^ (a * i)) • y = x := by
  rw [relNorm]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, mem_invSub_actEnd.1 hy, ?_⟩
    rw [actEnd_pow, powSum_actEnd_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← pow_mul]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, mem_invSub_actEnd.2 hy, ?_⟩
    rw [actEnd_pow, powSum_actEnd_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← pow_mul]

omit [Fintype G] in
theorem kerSub_eq_invSub (σ : G) : kerSub G M σ = invSub (actEnd (M := M) σ) 1 := by
  ext x
  rw [mem_kerSub, mem_invSub, pow_one, actEnd_apply]

variable (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)

include hσ

omit [Fintype G] hσ in
theorem invSub_card_eq_top : invSub (actEnd (M := M) σ) (Nat.card G) = ⊤ := by
  ext x
  simp only [AddSubgroup.mem_top, iff_true, mem_invSub, actEnd_pow_apply]
  rw [pow_card_eq_one', one_smul]

theorem normHom_eq_powSum : normHom G M = powSum (actEnd (M := M) σ) (Nat.card G) := by
  ext x
  rw [normHom_apply, powSum_actEnd_apply]
  have hord : orderOf σ = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hσ
  have hbij : Function.Bijective (fun i : Fin (Nat.card G) ↦ σ ^ (i : ℕ)) := by
    refine Fintype.bijective_iff_injective_and_card _ |>.2 ⟨?_, ?_⟩
    · intro i j hij
      have hi : (i : ℕ) ∈ Set.Iio (orderOf σ) := by rw [hord]; exact i.2
      have hj : (j : ℕ) ∈ Set.Iio (orderOf σ) := by rw [hord]; exact j.2
      exact Fin.ext (pow_injOn_Iio_orderOf hi hj hij)
    · simp [Nat.card_eq_fintype_card]
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦ (σ ^ i) • x) (Nat.card G)]
  exact (Fintype.sum_bijective _ hbij (fun i : Fin (Nat.card G) ↦ (σ ^ (i : ℕ)) • x)
    (fun g ↦ g • x) (fun i ↦ rfl)).symm

/-- `Ĥ⁰(G, M)` for `G = ⟨σ⟩` is the first step of the tower calculus. -/
theorem rangeNorm_eq_relNorm : rangeNorm G M = relNorm (actEnd (M := M) σ) 1 (Nat.card G) := by
  rw [rangeNorm, relNorm, one_mul, pow_one, invSub_card_eq_top, normHom_eq_powSum hσ]
  ext x
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, AddSubgroup.mem_top y, hy⟩, fun ⟨y, _, hy⟩ ↦ ⟨y, hy⟩⟩

/-- **`#Ĥ⁰(G, M) = relTateH0 T 1 |G|`** for `T` the action of a generator `σ` of `G`. -/
theorem card_tateH0_eq_relTateH0 :
    Nat.card (TateH0 G M σ) = relTateH0 (actEnd (M := M) σ) 1 (Nat.card G) := by
  rw [relTateH0, ← rangeNorm_eq_relNorm hσ, ← kerSub_eq_invSub σ]
  rfl

/-- **The first fundamental inequality, reduced to a chain of subquotients.**  If `l` is a list
of degrees with product `|G|`, and every step of the corresponding chain of cyclic subquotients
has finite `Ĥ⁰` of order at most its degree, then `#Ĥ⁰(G, M) ≤ |G|`. -/
theorem card_tateH0_le_of_chain (l : List ℕ) (hl : l.prod = Nat.card G)
    (h : ChainLe (actEnd (M := M) σ) 1 l) :
    Nat.card (TateH0 G M σ) ≤ Nat.card G := by
  rw [card_tateH0_eq_relTateH0 hσ, ← hl]
  exact relTateH0_le_prod _ 1 l h

/-- **The reduction to prime degree.**  If every prime step of the tower attached to the prime
factorisation of `|G|` has finite `Ĥ⁰` of order at most that prime, then `#Ĥ⁰(G, M) ≤ |G|`. -/
theorem card_tateH0_le_of_primeFactors
    (h : ChainLe (actEnd (M := M) σ) 1 (Nat.card G).primeFactorsList) :
    Nat.card (TateH0 G M σ) ≤ Nat.card G :=
  card_tateH0_le_of_chain hσ _ (Nat.prod_primeFactorsList Nat.card_pos.ne') h

/-- If every step of the chain has trivial `Ĥ⁰`, then `Ĥ⁰(G, M) = 0`. -/
theorem subsingleton_tateH0_of_chainBound_eq_one (l : List ℕ) (hl : l.prod = Nat.card G)
    (h1 : chainBound (actEnd (M := M) σ) 1 l = 1) :
    Subsingleton (TateH0 G M σ) := by
  have hdvd := relTateH0_dvd_chainBound (actEnd (M := M) σ) 1 l
  rw [h1, hl, ← card_tateH0_eq_relTateH0 hσ, Nat.dvd_one] at hdvd
  exact (Nat.card_eq_one_iff_unique.1 hdvd).1

end Module

end CyclicTate
