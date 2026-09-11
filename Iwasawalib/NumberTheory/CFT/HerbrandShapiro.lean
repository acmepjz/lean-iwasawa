/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.CyclicTateComparison
public import Iwasawalib.GroupCohomology.FamilyShapiro

@[expose] public section

/-!
# Shapiro's lemma for the Herbrand quotient

Let `G = ⟨σ⟩` be a finite cyclic group acting transitively on `Ω`, let `M : Ω → Type` be a
compatible family of commutative rings (`EquivariantFamily`), let `w₀ : Ω` and let
`D = Stab_G(w₀) = ⟨τ⟩`.  Then

`h_G((∏ w : Ω, M w)ˣ) = h_D((M w₀)ˣ)`   (`CyclicTate.herbrand_piUnits`)

and the same for the additive groups (`CyclicTate.herbrand_pi_of_family`).

This is the **dependent** form of Shapiro's lemma for the Herbrand quotient, with the
coefficients varying over `Ω` — the form needed for `h(𝕀_{L,S}) = ∏_{v ∈ S} h(L_wˣ)`, where
the factors `L_w` are genuinely different fields.  `CyclicTate.herbrand_pi` handles only a
constant family.

The proof is not a new computation: `EquivariantFamily.shapiroUnits` already gives
`Hⁿ(G, (∏ w, M w)ˣ) ≅ Hⁿ(D, (M w₀)ˣ)` in Mathlib's `groupCohomology`, and
`Iwasawalib/NumberTheory/CFT/CyclicTateComparison.lean` identifies `CyclicTate.herbrand` with
the ratio `#H² / #H¹` of those groups.  Before that comparison existed, the two sides of the
displayed equation could not be connected at all.
-/

noncomputable section

open CategoryTheory MulAction

namespace CyclicTate

/-- The additive copy of a commutative group carrying a `MulDistribMulAction` is a module for
the same group. -/
instance Additive.distribMulActionOfMulDistrib (G A : Type*) [Monoid G] [CommGroup A]
    [MulDistribMulAction G A] : DistribMulAction G (Additive A) where
  smul g a := Additive.ofMul (g • a.toMul)
  one_smul a := congrArg Additive.ofMul (one_smul G a.toMul)
  mul_smul g h a := congrArg Additive.ofMul (mul_smul g h a.toMul)
  smul_zero g := congrArg Additive.ofMul (smul_one g)
  smul_add g a b := congrArg Additive.ofMul (smul_mul' g a.toMul b.toMul)

theorem rep_additive_eq (G A : Type) [CommGroup G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] : Rep.ofMulDistribMulAction G A = rep G (Additive A) := rfl

attribute [local instance] Units.mulDistribMulActionRight

variable {G Ω : Type} [CommGroup G] [Fintype G] [MulAction G Ω] {M : Ω → Type}
  [∀ w, CommRing (M w)] (F : EquivariantFamily G Ω M) {w₀ : Ω}
  [MulSemiringAction G (∀ w : Ω, M w)] [MulSemiringAction (stabilizer G w₀) (M w₀)]
  [IsPretransitive G Ω] [Fintype (stabilizer G w₀)]

/-- **Shapiro's lemma for the Herbrand quotient of a dependent family, additively.** -/
theorem herbrand_pi_of_family (hstab : F.IsStabilizerAction (w₀ := w₀)) (hpi : F.IsPiAction)
    {σ : G} (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {τ : stabilizer G w₀} (hτ : ∀ d : stabilizer G w₀, d ∈ Subgroup.zpowers τ) :
    herbrand G (∀ w : Ω, M w) σ = herbrand (stabilizer G w₀) (M w₀) τ := by
  rw [herbrand_eq_card_groupCohomology (M := ∀ w : Ω, M w) σ hσ,
    herbrand_eq_card_groupCohomology (M := M w₀) τ hτ]
  have h : ∀ n : ℕ, Nat.card (groupCohomology (rep G (∀ w : Ω, M w)) n : ModuleCat ℤ)
      = Nat.card (groupCohomology (rep (stabilizer G w₀) (M w₀)) n : ModuleCat ℤ) := fun n ↦
    Nat.card_congr (F.shapiro hstab hpi n).toLinearEquiv.toEquiv
  rw [h 2, h 1]

/-- **Shapiro's lemma for the Herbrand quotient of the units of a dependent family of
rings**: `h_G((∏ w : Ω, M w)ˣ) = h_{Stab(w₀)}((M w₀)ˣ)`. -/
theorem herbrand_piUnits (hstab : F.IsStabilizerAction (w₀ := w₀)) (hpi : F.IsPiAction)
    {σ : G} (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {τ : stabilizer G w₀} (hτ : ∀ d : stabilizer G w₀, d ∈ Subgroup.zpowers τ) :
    herbrand G (Additive (∀ w : Ω, M w)ˣ) σ
      = herbrand (stabilizer G w₀) (Additive (M w₀)ˣ) τ := by
  rw [herbrand_eq_card_groupCohomology (M := Additive (∀ w : Ω, M w)ˣ) σ hσ,
    herbrand_eq_card_groupCohomology (M := Additive (M w₀)ˣ) τ hτ]
  have h : ∀ n : ℕ,
      Nat.card (groupCohomology (rep G (Additive (∀ w : Ω, M w)ˣ)) n : ModuleCat ℤ)
        = Nat.card (groupCohomology (rep (stabilizer G w₀) (Additive (M w₀)ˣ)) n :
            ModuleCat ℤ) := fun n ↦
    Nat.card_congr (F.shapiroUnits hstab hpi n).toLinearEquiv.toEquiv
  rw [h 2, h 1]

end CyclicTate
