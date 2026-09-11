/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.CyclicTate
public import Iwasawalib.GroupCohomology.CyclicCocycle

@[expose] public section

/-!
# The 1-cocycle attached to an element of norm one

`Iwasawalib/GroupCohomology/CyclicCocycle.lean` proves one half of the comparison between
`Ĥ¹` and `H¹` for a finite cyclic group `G = ⟨σ⟩`: if every element of norm `1` is of the form
`σ • y / y`, then every multiplicative 1-cocycle is a coboundary
(`CyclicCocycle.isMulCoboundary₁_of_mulNorm`).  This file proves the converse half, which is
the direction needed to *deduce* the vanishing of `Ĥ¹` from a statement about cocycles.

Given `x : M` with `∏_{g ∈ G} g • x = 1`, the partial products

`f (σ ^ i) = ∏_{j < i} σ ^ j • x`

are well defined — the norm hypothesis is exactly periodicity `f (σ ^ (i + #G)) = f (σ ^ i)` —
and form a 1-cocycle `f` with `f σ = x`.  So a hypothesis "every 1-cocycle with values in `N`
is trivialised inside `N`" yields "every `x ∈ N` of norm `1` is `σ • y / y` with `y ∈ N`",
which is `CyclicTate.tateH1_subsingleton_iff`.

The comparison in `Iwasawalib/NumberTheory/CFT/CyclicTateComparison.lean` is not usable here:
it requires the acting group to be a `CommGroup` *as an instance*, whereas the applications
below have `G = Gal(L/K)` with cyclicity only as a hypothesis `∀ g, g ∈ Subgroup.zpowers σ`.

## Main definitions

* `CyclicCocycle.partialMulNorm`: the partial products `∏_{j < i} σ ^ j • x`.
* `CyclicCocycle.cocycleOfMulNorm`: the 1-cocycle attached to an element of norm one.

## Main statements

* `CyclicCocycle.isMulCocycle₁_cocycleOfMulNorm`, `CyclicCocycle.cocycleOfMulNorm_generator`:
  it is a 1-cocycle, and its value at `σ` is `x`.
* `CyclicCocycle.exists_smul_div_of_forall_isMulCocycle₁`: the converse of
  `CyclicCocycle.isMulCoboundary₁_of_mulNorm`, in the subgroup form.
-/

noncomputable section

open Finset

namespace CyclicCocycle

section PartialMulNorm

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

variable (σ : G) (x : M) in
/-- The partial product `∏_{j < i} σ ^ j • x`. -/
def partialMulNorm (i : ℕ) : M := ∏ j ∈ range i, (σ ^ j) • x

variable {σ : G} {x : M}

theorem partialMulNorm_zero : partialMulNorm σ x 0 = 1 := prod_range_zero _

theorem partialMulNorm_one : partialMulNorm σ x 1 = x := by
  rw [partialMulNorm, prod_range_one, pow_zero, one_smul]

/-- The partial products are multiplicative in the twisted sense: this is the 1-cocycle
relation. -/
theorem partialMulNorm_add (a b : ℕ) :
    partialMulNorm σ x (a + b) = partialMulNorm σ x a * (σ ^ a) • partialMulNorm σ x b := by
  rw [partialMulNorm, partialMulNorm, partialMulNorm, prod_range_add, smul_prod']
  refine congrArg _ (prod_congr rfl fun j _ ↦ ?_)
  rw [smul_smul, ← pow_add]

variable [Fintype G]

theorem partialMulNorm_card (hg : ∀ g : G, g ∈ Subgroup.zpowers σ) (hx : mulNorm (G := G) x = 1) :
    partialMulNorm σ x (Nat.card G) = 1 := by
  rw [partialMulNorm, ← mulNorm_eq_prod_range hg x, hx]

theorem partialMulNorm_add_card (hg : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hx : mulNorm (G := G) x = 1) (a : ℕ) :
    partialMulNorm σ x (a + Nat.card G) = partialMulNorm σ x a := by
  rw [partialMulNorm_add, partialMulNorm_card hg hx, smul_one, mul_one]

theorem partialMulNorm_add_mul_card (hg : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hx : mulNorm (G := G) x = 1) (a m : ℕ) :
    partialMulNorm σ x (a + Nat.card G * m) = partialMulNorm σ x a := by
  induction m with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ m ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, partialMulNorm_add_card hg hx, ih]

/-- **The partial products depend only on `σ ^ i`, not on `i`**, when `x` has norm one. -/
theorem partialMulNorm_congr (hg : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hx : mulNorm (G := G) x = 1) {a b : ℕ} (hab : σ ^ a = σ ^ b) :
    partialMulNorm σ x a = partialMulNorm σ x b := by
  have key : ∀ c d : ℕ, c ≤ d → σ ^ c = σ ^ d →
      partialMulNorm σ x c = partialMulNorm σ x d := by
    intro c d hcd hσcd
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hcd
    have he : σ ^ e = 1 := by
      have : σ ^ c * σ ^ e = σ ^ c * 1 := by rw [← pow_add, mul_one, ← hσcd]
      exact mul_left_cancel this
    have hdvd : Nat.card G ∣ e := by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
      exact orderOf_dvd_of_pow_eq_one he
    obtain ⟨m, rfl⟩ := hdvd
    exact (partialMulNorm_add_mul_card hg hx c m).symm
  rcases le_total a b with h | h
  · exact key a b h hab
  · exact (key b a h hab.symm).symm

end PartialMulNorm

/-! ## The cocycle -/

section OfMulNorm

variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M] {σ : G}

theorem exists_pow_eq (hg : ∀ g : G, g ∈ Subgroup.zpowers σ) (g : G) : ∃ i : ℕ, σ ^ i = g :=
  (Submonoid.mem_powers_iff g σ).1 (mem_powers_iff_mem_zpowers.2 (hg g))

/-- A choice of natural number `i` with `σ ^ i = g`. -/
def expOf (hg : ∀ g : G, g ∈ Subgroup.zpowers σ) (g : G) : ℕ :=
  (exists_pow_eq hg g).choose

theorem pow_expOf (hg : ∀ g : G, g ∈ Subgroup.zpowers σ) (g : G) : σ ^ expOf hg g = g :=
  (exists_pow_eq hg g).choose_spec

variable (hg : ∀ g : G, g ∈ Subgroup.zpowers σ) {x : M} (hx : mulNorm (G := G) x = 1)

/-- **The 1-cocycle attached to an element of norm one**, for a finite cyclic group `G = ⟨σ⟩`:
`f (σ ^ i) = ∏_{j < i} σ ^ j • x`. -/
def cocycleOfMulNorm (g : G) : M := partialMulNorm σ x (expOf hg g)

include hx

theorem cocycleOfMulNorm_pow (i : ℕ) :
    cocycleOfMulNorm hg (x := x) (σ ^ i) = partialMulNorm σ x i :=
  partialMulNorm_congr hg hx (pow_expOf hg (σ ^ i))

@[simp]
theorem cocycleOfMulNorm_generator : cocycleOfMulNorm hg (x := x) σ = x :=
  (partialMulNorm_congr hg hx (by rw [pow_one]; exact pow_expOf hg σ)).trans partialMulNorm_one

theorem isMulCocycle₁_cocycleOfMulNorm :
    groupCohomology.IsMulCocycle₁ (cocycleOfMulNorm hg (x := x)) := by
  intro g h
  rw [show g = σ ^ expOf hg g from (pow_expOf hg g).symm,
    show h = σ ^ expOf hg h from (pow_expOf hg h).symm, ← pow_add,
    cocycleOfMulNorm_pow hg hx, cocycleOfMulNorm_pow hg hx, cocycleOfMulNorm_pow hg hx,
    partialMulNorm_add, mul_comm]

end OfMulNorm

section Mem

variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M] {σ : G}
variable (hg : ∀ g : G, g ∈ Subgroup.zpowers σ) {x : M}

/-- The cocycle takes its values in any `G`-stable subgroup containing `x`. -/
theorem cocycleOfMulNorm_mem {N : Subgroup M}
    (hN : ∀ (g : G) (y : M), y ∈ N → g • y ∈ N) (hxN : x ∈ N) (g : G) :
    cocycleOfMulNorm hg (x := x) g ∈ N := by
  show ∏ j ∈ range (expOf hg g), (σ ^ j) • x ∈ N
  exact Subgroup.prod_mem _ fun j _ ↦ hN _ _ hxN

end Mem

/-! ## From cocycles to `Ĥ¹` -/

section Transfer

variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M] {σ : G}

/-- **The converse of `CyclicCocycle.isMulCoboundary₁_of_mulNorm`, in the subgroup form.**  If
every multiplicative 1-cocycle with values in a `G`-stable subgroup `N` is trivialised by an
element of `N`, then every element of `N` of norm one is of the form `σ • y / y` with
`y ∈ N`. -/
theorem exists_smul_div_of_forall_isMulCocycle₁ (hg : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {N : Subgroup M} (hN : ∀ (g : G) (y : M), y ∈ N → g • y ∈ N)
    (H : ∀ f : G → M, groupCohomology.IsMulCocycle₁ f → (∀ g, f g ∈ N) →
      ∃ b ∈ N, ∀ g, g • b / b = f g)
    {x : M} (hxN : x ∈ N) (hx : mulNorm (G := G) x = 1) :
    ∃ y ∈ N, σ • y / y = x := by
  obtain ⟨b, hbN, hb⟩ := H (cocycleOfMulNorm hg (x := x))
    (isMulCocycle₁_cocycleOfMulNorm hg hx) (cocycleOfMulNorm_mem hg hN hxN)
  exact ⟨b, hbN, (hb σ).trans (cocycleOfMulNorm_generator hg hx)⟩

end Transfer

end CyclicCocycle
