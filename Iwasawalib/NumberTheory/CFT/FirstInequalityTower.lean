/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.TateTower
public import Iwasawalib.NumberTheory.CFT.FirstInequality
public import Iwasawalib.NumberTheory.CFT.IdeleClassNormIndex

@[expose] public section

/-!
# The first fundamental inequality, reduced to prime degree

For a cyclic extension of number fields `L / K` with `Gal(L/K) = ⟨σ⟩` of order `n`, the first
fundamental inequality is the bound

`#Ĥ⁰(Gal(L/K), C_L) ≤ n`,

equivalently (`NumberField.subsingleton_tateH1_ideleClassGroup_iff_everywhere`) the vanishing
`Ĥ¹(Gal(L/K), C_L) = 0`.  This file carries out, unconditionally, the first step of Chevalley's
algebraic proof: the **reduction to prime degree**.

`Iwasawalib/NumberTheory/CFT/TateTower.lean` proves the tower inequality for the Tate group
`Ĥ⁰` of a finite cyclic group in a purely algebraic form.  Writing `T` for the action of `σ` on
`M = C_L` (additively), for divisors the subgroup `H_a = ⟨σ ^ a⟩` has invariants
`M ^ H_a = ker (T ^ a - 1) = CyclicTate.invSub T a`, which by
`NumberField.IdeleClassGroup.range_baseChange_eq_setOf_fixed` applied to `L / L ^ H_a` is the
idele class group of the intermediate field `L ^ H_a`; and `CyclicTate.relTateH0 T a b` is the
order of `Ĥ⁰` of the cyclic subquotient `H_a / H_{a*b}` of order `b` acting on it, i.e. the norm
index `[C_{L ^ H_a} : N C_{L ^ H_{a*b}}]` of the degree-`b` step `L ^ H_{a*b} / L ^ H_a`.

The theorem `CyclicTate.relTateH0_dvd_tower` — proved with no hypothesis whatsoever — says that
this index is multiplicative-with-divisibility in towers, and
`CyclicTate.relTateH0_le_prod` iterates it along a chain.  Consequently:

## Main statements

* `NumberField.card_tateH0_ideleClassGroup_le_of_chain` : `#Ĥ⁰(Gal(L/K), C_L) ≤ [L : K]`
  whenever every step of a chain of cyclic subquotients whose degrees multiply to `[L : K]`
  satisfies the bound for its own degree.  **This is the only place where an unproved input
  enters**: the hypothesis is a `CyclicTate.ChainLe`, and for a chain of primes it is exactly
  the first inequality in the prime-degree case, which is what Chevalley's Kummer-theoretic
  argument supplies and which is *not* proved in this repository.
* `NumberField.card_tateH0_ideleClassGroup_le_of_primeFactors` : the same with the chain taken
  to be the prime factorisation of `[L : K]`.
* `NumberField.subsingleton_tateH1_ideleClassGroup_of_chain` : the first fundamental inequality
  in the form `Ĥ¹(Gal(L/K), C_L) = 0`, for an extension unramified at every place (where the
  Herbrand quotient of `C_L` is known to be `[L : K]`).
* `NumberField.subsingleton_groupCohomology_one_ideleClassGroup_of_chain` : the same in
  Mathlib's `groupCohomology`.

## The shape of the remaining input

`CyclicTate.ChainLe T a (p :: l)` unfolds to `0 < relTateH0 T a p ∧ relTateH0 T a p ≤ p ∧
ChainLe T (a * p) l`, and `CyclicTate.mem_invSub_actEnd` and `CyclicTate.mem_relNorm_actEnd`
describe the two subgroups involved entirely in terms of the action of powers of `σ` on `C_L`:
`relTateH0 T a p` is the index, inside `{c | σ ^ a • c = c}`, of the set of elements of the form
`∑ i < p, σ ^ (a * i) • d` with `σ ^ (a * p) • d = d`.  In multiplicative notation on `C_L` that
is exactly `[C_{L ^ H_a} : N_{L ^ H_{a p} / L ^ H_a} C_{L ^ H_{a p}}]`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MulAction CyclicTate
open NumberField.InfiniteAdeleRing

namespace NumberField

attribute [local instance] NumberField.galInfiniteAdeleMulSemiringAction
  NumberField.galIdeleMulDistribMulAction Units.mulDistribMulActionRight
  NumberField.galIdeleClassMulDistribMulAction

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {σ : L ≃ₐ[K] L} [IsGalois K L]

omit [IsGalois K L] in
/-- **The first fundamental inequality, granted the steps of a chain.**

If `l` is a list of degrees whose product is `[L : K]` and, for each step of the corresponding
chain of cyclic subquotients of `Gal(L/K)`, the relative `Ĥ⁰` is finite of order at most the
degree of that step, then `#Ĥ⁰(Gal(L/K), C_L) ≤ [L : K]`.

No hypothesis on ramification, and no hypothesis on the places of `K`, is needed: this is the
tower calculus of `Iwasawalib/NumberTheory/CFT/TateTower.lean` transported to `C_L`. -/
theorem card_tateH0_ideleClassGroup_le_of_chain
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (l : List ℕ) (hl : l.prod = Nat.card (L ≃ₐ[K] L))
    (hchain : CyclicTate.ChainLe
      (CyclicTate.actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) 1 l) :
    Nat.card (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      ≤ Nat.card (L ≃ₐ[K] L) := by
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  exact CyclicTate.card_tateH0_le_of_chain hσ l hl hchain

omit [IsGalois K L] in
/-- **The reduction to prime degree.**  Taking the chain to be the prime factorisation of
`[L : K]`, the first fundamental inequality for `L / K` follows from the first fundamental
inequality for each cyclic prime-degree step of the tower. -/
theorem card_tateH0_ideleClassGroup_le_of_primeFactors
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (hchain : CyclicTate.ChainLe
      (CyclicTate.actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) 1
      (Nat.card (L ≃ₐ[K] L)).primeFactorsList) :
    Nat.card (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      ≤ Nat.card (L ≃ₐ[K] L) :=
  card_tateH0_ideleClassGroup_le_of_chain hgen _
    (Nat.prod_primeFactorsList Nat.card_pos.ne') hchain

/-! ## The two inequalities in classical norm-index language

`NumberField.IdeleClassGroup.card_tateH0_eq_index_normSubgroup` identifies
`#Ĥ⁰(Gal(L/K), C_L)` with the norm index `[C_K : N_{L/K} C_L]`, so the statements above can be
read as the classical ones. -/

/-- **The first fundamental inequality `[C_K : N_{L/K} C_L] ≤ [L : K]`**, granted the steps of a
chain. -/
theorem index_normSubgroup_le_of_chain
    (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (l : List ℕ) (hl : l.prod = Nat.card (L ≃ₐ[K] L))
    (hchain : CyclicTate.ChainLe
      (CyclicTate.actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) 1 l) :
    (IdeleClassGroup.normSubgroup K L).index ≤ Nat.card (L ≃ₐ[K] L) := by
  rw [← IdeleClassGroup.card_tateH0_eq_index_normSubgroup hgen]
  exact card_tateH0_ideleClassGroup_le_of_chain hgen l hl hchain

/-! ## The vanishing of `Ĥ¹`

To turn the bound on `#Ĥ⁰` into the vanishing of `Ĥ¹` one needs the Herbrand quotient
`h(C_L) = [L : K]`, which this repository proves for extensions unramified at every place
(`NumberField.herbrand_ideleClassGroup_eq_card_of_unramified_everywhere`). -/

section Everywhere

variable
  (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
  (w₁ : ∀ v : InfinitePlace K, Fibre L v)
  [∀ v : InfinitePlace K, Subsingleton (stabilizer (L ≃ₐ[K] L) (w₁ v))]
  (w₂ : ∀ v : HeightOneSpectrum (𝓞 K), placesOver K L v)
  (τ₂ : ∀ v : HeightOneSpectrum (𝓞 K),
    decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L)))
  (hτ₂ : ∀ (v : HeightOneSpectrum (𝓞 K))
    (d : decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L))),
    d ∈ Subgroup.zpowers (τ₂ v))
  (hram : ∀ v : HeightOneSpectrum (𝓞 K),
    v.asIdeal.ramificationIdx' (w₂ v : HeightOneSpectrum (𝓞 L)).asIdeal = 1)

include hgen w₁ w₂ τ₂ hτ₂ hram

/-- **The first fundamental inequality `Ĥ¹(Gal(L/K), C_L) = 0`**, for a cyclic extension
unramified at every place, granted the steps of a chain. -/
theorem subsingleton_tateH1_ideleClassGroup_of_chain
    (l : List ℕ) (hl : l.prod = Nat.card (L ≃ₐ[K] L))
    (hchain : CyclicTate.ChainLe
      (CyclicTate.actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) 1 l) :
    Subsingleton (CyclicTate.TateH1 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ) :=
  (subsingleton_tateH1_ideleClassGroup_iff_everywhere hgen w₁ w₂ τ₂ hτ₂ hram).2
    (card_tateH0_ideleClassGroup_le_of_chain hgen l hl hchain)

/-- **`#Ĥ⁰(Gal(L/K), C_L) = [L : K]`**, for a cyclic extension unramified at every place,
granted the steps of a chain: the two fundamental inequalities together. -/
theorem card_tateH0_ideleClassGroup_eq_of_chain
    (l : List ℕ) (hl : l.prod = Nat.card (L ≃ₐ[K] L))
    (hchain : CyclicTate.ChainLe
      (CyclicTate.actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) 1 l) :
    Nat.card (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      = Nat.card (L ≃ₐ[K] L) :=
  le_antisymm (card_tateH0_ideleClassGroup_le_of_chain hgen l hl hchain)
    (card_tateH0_ideleClassGroup_ge_everywhere hgen w₁ w₂ τ₂ hτ₂ hram)

/-- **`H¹(Gal(L/K), C_L) = 0` in Mathlib's `groupCohomology`**, for a cyclic extension
unramified at every place, granted the steps of a chain. -/
theorem subsingleton_groupCohomology_one_ideleClassGroup_of_chain
    (l : List ℕ) (hl : l.prod = Nat.card (L ≃ₐ[K] L))
    (hchain : CyclicTate.ChainLe
      (CyclicTate.actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) 1 l) :
    letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
    Subsingleton (groupCohomology
      (CyclicTate.rep (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L))) 1 : ModuleCat ℤ) := by
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  rw [subsingleton_groupCohomology_one_ideleClassGroup_iff hgen w₁ w₂ τ₂ hτ₂ hram]
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  rw [← CyclicTate.card_tateH0_eq (M := Additive (IdeleClassGroup (𝓞 L) L)) σ hσ 2 (by decide)]
  exact card_tateH0_ideleClassGroup_le_of_chain hgen l hl hchain

/-- **The second fundamental inequality `[L : K] ≤ [C_K : N_{L/K} C_L]`** in classical
norm-index language, for a cyclic extension unramified at every place.  This direction is
unconditional here. -/
theorem le_index_normSubgroup_everywhere :
    Nat.card (L ≃ₐ[K] L) ≤ (IdeleClassGroup.normSubgroup K L).index := by
  rw [← IdeleClassGroup.card_tateH0_eq_index_normSubgroup hgen]
  exact card_tateH0_ideleClassGroup_ge_everywhere hgen w₁ w₂ τ₂ hτ₂ hram

/-- **`[C_K : N_{L/K} C_L] = [L : K]`**, for a cyclic extension unramified at every place,
granted the steps of a chain: the fundamental equality of class field theory for `L / K`. -/
theorem index_normSubgroup_eq_of_chain
    (l : List ℕ) (hl : l.prod = Nat.card (L ≃ₐ[K] L))
    (hchain : CyclicTate.ChainLe
      (CyclicTate.actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) 1 l) :
    (IdeleClassGroup.normSubgroup K L).index = Nat.card (L ≃ₐ[K] L) := by
  rw [← IdeleClassGroup.card_tateH0_eq_index_normSubgroup hgen]
  exact card_tateH0_ideleClassGroup_eq_of_chain hgen w₁ w₂ τ₂ hτ₂ hram l hl hchain

end Everywhere

end NumberField
