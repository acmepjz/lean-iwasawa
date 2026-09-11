/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.CyclicCocycleNorm
public import Iwasawalib.NumberTheory.LocalCFT.LocalUnits
public import Iwasawalib.GroupCohomology.Hilbert90

@[expose] public section

/-!
# Hilbert 90 in Tate form: `Ĥ¹(G, Fˣ) = 0` for a faithful cyclic action

`Iwasawalib/GroupCohomology/Hilbert90.lean` proves Noether's form of Hilbert 90 for an
arbitrary faithful action of a finite group `G` on a field `F`: every multiplicative
1-cocycle `G → Fˣ` is a coboundary
(`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_faithful`).  When `G = ⟨σ⟩` is cyclic
this is equivalent to the vanishing of the first *Tate* cohomology group in the explicit
two-periodic model of `Iwasawalib/GroupCohomology/CyclicTate.lean`, and the translation is
`CyclicCocycle.exists_smul_div_of_forall_isMulCocycle₁` of
`Iwasawalib/NumberTheory/LocalCFT/CyclicCocycleNorm.lean` applied to the subgroup `N = ⊤`.

The Tate form is what the Herbrand-quotient machinery consumes, and it is the missing
denominator in the local invariant map: once `Ĥ¹(G, L_wˣ) = 0`, the Herbrand quotient
`h(L_wˣ) = n` says outright that `#Ĥ⁰(G, L_wˣ) = n`, i.e. that the local norm index is the
degree.  See `Iwasawalib/NumberTheory/LocalCFT/ArchimedeanHerbrand.lean` for the archimedean
instance of exactly that argument.

## Main statements

* `LocalCFT.exists_smul_div_of_mulNorm_eq_one_of_faithful`: an element of norm one is
  `σ • y / y`.
* `LocalCFT.subsingleton_tateH1_units_of_faithful`: `Ĥ¹(G, Fˣ) = 0`.
* `LocalCFT.card_tateH1_units_of_faithful`: `#Ĥ¹(G, Fˣ) = 1`.
* `LocalCFT.card_tateH0_units_of_faithful_of_herbrand`: if moreover `h(Fˣ) = n` then
  `#Ĥ⁰(G, Fˣ) = n`.
-/

noncomputable section

open CyclicCocycle

namespace LocalCFT

section Faithful

variable {G F : Type} [Group G] [Fintype G] [Field F] [MulSemiringAction G F] {σ : G}

attribute [local instance] Units.mulDistribMulActionRight

variable (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)
  (hG : Function.Injective fun (g : G) ↦ (fun x : F ↦ g • x))

include hσ hG

/-- **Hilbert 90, cyclic form.**  For a faithful action of a finite cyclic group `G = ⟨σ⟩` on a
field `F`, every `x : Fˣ` with `∏_{g ∈ G} g • x = 1` is of the form `σ • y / y`. -/
theorem exists_smul_div_of_mulNorm_eq_one_of_faithful {x : Fˣ}
    (hx : mulNorm (G := G) x = 1) : ∃ y : Fˣ, σ • y / y = x := by
  obtain ⟨y, -, hy⟩ := CyclicCocycle.exists_smul_div_of_forall_isMulCocycle₁ hσ
    (N := (⊤ : Subgroup Fˣ)) (fun _ _ _ ↦ Subgroup.mem_top _)
    (fun f hf _ ↦ by
      obtain ⟨b, hb⟩ :=
        groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_faithful hG f hf
      exact ⟨b, Subgroup.mem_top _, hb⟩)
    (Subgroup.mem_top x) hx
  exact ⟨y, hy⟩

/-- **`Ĥ¹(G, Fˣ) = 0`** for a faithful action of a finite cyclic group on a field. -/
theorem subsingleton_tateH1_units_of_faithful :
    Subsingleton (CyclicTate.TateH1 G (Additive Fˣ) σ) := by
  rw [CyclicTate.tateH1_subsingleton_iff]
  intro x hx
  rw [normHom_additive] at hx
  obtain ⟨y, hy⟩ := exists_smul_div_of_mulNorm_eq_one_of_faithful hσ hG
    (x := x.toMul) (by simpa using hx)
  exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩

/-- `#Ĥ¹(G, Fˣ) = 1` for a faithful action of a finite cyclic group on a field. -/
theorem card_tateH1_units_of_faithful :
    Nat.card (CyclicTate.TateH1 G (Additive Fˣ) σ) = 1 := by
  haveI := subsingleton_tateH1_units_of_faithful hσ hG
  exact Nat.card_eq_one_iff_unique.2 ⟨‹_›, ⟨0⟩⟩

/-- **The Herbrand quotient computes the local norm index.**  If the action is faithful and
`h(Fˣ) = n`, then `#Ĥ⁰(G, Fˣ) = #(F^G)ˣ / N Fˣ = n`, because the denominator `#Ĥ¹` is `1`. -/
theorem card_tateH0_units_of_faithful_of_herbrand {n : ℕ}
    (hn : CyclicTate.herbrand G (Additive Fˣ) σ = (n : ℚ)) :
    Nat.card (CyclicTate.TateH0 G (Additive Fˣ) σ) = n := by
  rw [CyclicTate.herbrand_def, card_tateH1_units_of_faithful hσ hG] at hn
  norm_num at hn
  exact_mod_cast hn

end Faithful

end LocalCFT
