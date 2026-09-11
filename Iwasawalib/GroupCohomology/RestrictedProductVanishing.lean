/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.ProductVanishing
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

@[expose] public section

/-!
# `H¹` of a restricted product

Let `G` be a **finite** group acting factorwise on a restricted product
`Πʳ i, [M i, N i]` of commutative groups `M i` with respect to `G`-stable subgroups `N i`.
Then `H¹(G, Πʳ i, [M i, N i]) = 0` as soon as

* every multiplicative 1-cocycle `G → M i` is a 1-coboundary, for **every** `i`; and
* for **almost every** `i`, a 1-cocycle `G → M i` whose values lie in `N i` is a 1-coboundary
  *with a witness in `N i`*.

The proof is the standard one.  A 1-cocycle `f : G → Πʳ i, [M i, N i]` has components which are
1-cocycles; since `G` is finite and each `f g` lies in the restricted product, the values
`f g i` lie in `N i` for all `g` simultaneously, for almost every `i`.  For those `i` the second
hypothesis produces a witness inside `N i`; for the finitely many remaining `i` the first
hypothesis produces a witness in `M i`.  The resulting family lies in `N i` for almost every
`i`, hence is an element of the restricted product, and it trivialises `f`.

This is the "`H¹` commutes with the restricted product" step in the computation of
`H¹(Gal(L/K), 𝕀_L)`.  The second hypothesis is the arithmetic input that is *not* supplied
here: for the ideles it says that `H¹(D_w, O_w^×) = 0` for almost all `w`, i.e. at the
unramified places.

## Main definitions

* `RestrictedProduct.mulDistribMulAction`: the factorwise action of `G`.

## Main statements

* `RestrictedProduct.isMulCoboundary₁_of_forall`: the cocycle statement.
* `RestrictedProduct.isZero_H1`: `H¹(G, Πʳ i, [M i, N i]) = 0`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Filter
open scoped RestrictedProduct

namespace RestrictedProduct

variable {G ι : Type} [Group G] {M : ι → Type} [∀ i, CommGroup (M i)]
  [∀ i, MulDistribMulAction G (M i)] {N : ∀ i, Subgroup (M i)}

/-- The factorwise action of `G` on a restricted product taken with respect to a family of
`G`-stable subgroups. -/
@[instance_reducible] def mulDistribMulAction (hN : ∀ (i : ι) (g : G) {x : M i}, x ∈ N i → g • x ∈ N i) :
    MulDistribMulAction G (Πʳ i, [M i, N i]) where
  smul g x := ⟨fun i ↦ g • x i, by filter_upwards [x.2] with i hi using hN i g hi⟩
  one_smul x := by ext i; exact one_smul G (x i)
  mul_smul g h x := by ext i; exact mul_smul g h (x i)
  smul_one g := by ext i; exact smul_one g
  smul_mul g x y := by ext i; exact smul_mul' g (x i) (y i)

section

variable [MulDistribMulAction G (Πʳ i, [M i, N i])]

/-- The compatibility of a given action of `G` on the restricted product with the factorwise
actions.  It holds by `rfl` for `RestrictedProduct.mulDistribMulAction`. -/
abbrev IsFactorwise : Prop :=
  ∀ (g : G) (x : Πʳ i, [M i, N i]) (i : ι), (g • x) i = g • x i

variable (hsmul : IsFactorwise (G := G) (N := N))

include hsmul

/-- The components of a 1-cocycle with values in a restricted product are 1-cocycles. -/
theorem isMulCocycle₁_apply {f : G → Πʳ i, [M i, N i]} (hf : groupCohomology.IsMulCocycle₁ f)
    (i : ι) : groupCohomology.IsMulCocycle₁ fun g ↦ f g i := by
  intro g h
  have h1 : f (g * h) i = (g • f h * f g) i := by rw [hf g h]
  rwa [show ((g • f h) * f g) i = (g • f h) i * (f g) i from rfl, hsmul] at h1

/-- **A 1-cocycle into a restricted product is a 1-coboundary.**  For a finite group `G`, if
every 1-cocycle into `M i` is a 1-coboundary and, for almost every `i`, every `N i`-valued
1-cocycle is a 1-coboundary with a witness in `N i`, then every 1-cocycle into the restricted
product is a 1-coboundary. -/
theorem isMulCoboundary₁_of_forall [Finite G]
    (ha : ∀ (i : ι) (f : G → M i), groupCohomology.IsMulCocycle₁ f →
      groupCohomology.IsMulCoboundary₁ f)
    (hb : ∀ᶠ i in cofinite, ∀ f : G → M i, groupCohomology.IsMulCocycle₁ f →
      (∀ g, f g ∈ N i) → ∃ b ∈ N i, ∀ g, g • b / b = f g)
    (f : G → Πʳ i, [M i, N i]) (hf : groupCohomology.IsMulCocycle₁ f) :
    groupCohomology.IsMulCoboundary₁ f := by
  have hfin : ∀ᶠ i in cofinite, ∀ g : G, f g i ∈ N i :=
    eventually_all.2 fun g ↦ (f g).2
  have hmain : ∀ᶠ i in cofinite, ∃ b ∈ N i, ∀ g : G, g • b / b = f g i := by
    filter_upwards [hfin, hb] with i h1 h2
    exact h2 _ (isMulCocycle₁_apply hsmul hf i) h1
  have hex : ∀ i : ι, ∃ b : M i, (∀ g : G, g • b / b = f g i) ∧
      ((∃ b' ∈ N i, ∀ g : G, g • b' / b' = f g i) → b ∈ N i) := by
    intro i
    by_cases hi : ∃ b' ∈ N i, ∀ g : G, g • b' / b' = f g i
    · obtain ⟨b, hbN, hb'⟩ := hi
      exact ⟨b, hb', fun _ ↦ hbN⟩
    · obtain ⟨b, hb'⟩ := ha i _ (isMulCocycle₁_apply hsmul hf i)
      exact ⟨b, hb', fun h ↦ absurd h hi⟩
  choose b hb1 hb2 using hex
  have hbmem : ∀ᶠ i in cofinite, b i ∈ N i := by
    filter_upwards [hmain] with i hi using hb2 i hi
  have hdiv : ∀ (x y : Πʳ i, [M i, N i]) (i : ι), (x / y) i = x i / y i := fun _ _ _ ↦ rfl
  refine ⟨⟨b, hbmem⟩, fun g ↦ ?_⟩
  ext i
  rw [hdiv, hsmul]
  exact hb1 i g

/-- **`H¹` of a restricted product vanishes.**  For a finite group `G` acting factorwise on
`Πʳ i, [M i, N i]`, if `H¹(G, M i) = 0` for every `i` and, for almost every `i`, every
`N i`-valued 1-cocycle is trivialised inside `N i`, then `H¹(G, Πʳ i, [M i, N i]) = 0`. -/
theorem isZero_H1 [Finite G]
    (ha : ∀ i : ι, IsZero (groupCohomology (Rep.ofMulDistribMulAction G (M i)) 1))
    (hb : ∀ᶠ i in cofinite, ∀ f : G → M i, groupCohomology.IsMulCocycle₁ f →
      (∀ g, f g ∈ N i) → ∃ b ∈ N i, ∀ g, g • b / b = f g) :
    IsZero (groupCohomology
      (Rep.ofMulDistribMulAction G (Πʳ i, [M i, N i])) 1) :=
  groupCohomology.isZero_H1_ofMulDistribMulAction_iff.2 fun f hf ↦
    isMulCoboundary₁_of_forall hsmul
      (fun i ↦ groupCohomology.isZero_H1_ofMulDistribMulAction_iff.1 (ha i)) hb f hf

end

end RestrictedProduct
