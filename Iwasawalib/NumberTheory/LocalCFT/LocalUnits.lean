/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.FiniteResidue
public import Iwasawalib.NumberTheory.LocalCFT.ResidueAction
public import Iwasawalib.NumberTheory.CFT.HerbrandShapiro

@[expose] public section

/-!
# The units of an unramified complete discretely valued field are cohomologically trivial

Let `F` be a complete field with a valuation `v : F → ℤᵐ⁰`, `𝒪` its valuation ring, and let a
finite cyclic group `G = ⟨σ⟩` act on `𝒪` by valuation-preserving ring automorphisms.  Assume

* there is a **`G`-fixed uniformizer** `π` (`v π = exp (-1)`, `g • π = π`);
* the residue field `𝒪/𝔪` is **finite** and `G` acts on it **faithfully**.

Then `Ĥ⁰(G, 𝒪ˣ) = Ĥ¹(G, 𝒪ˣ) = 0`, and consequently the Herbrand quotient of `𝒪ˣ` is `1`.

This is the local input of the first fundamental inequality of class field theory at an
unramified place: for `L_w / K_v` unramified with `G = D_w` the decomposition group, a
uniformizer of `K_v` is a uniformizer of `L_w` and `D_w` acts faithfully on the residue
extension, so `H¹(D_w, O_wˣ) = 0`.

## Main statements

* `LocalCFT.exists_smul_div_of_mulNorm_eq_one_of_finiteResidue`: `Ĥ¹(G, 𝒪ˣ) = 0`.
* `LocalCFT.exists_mulNorm_eq_of_smul_eq_of_finiteResidue`: `Ĥ⁰(G, 𝒪ˣ) = 0`.
* `LocalCFT.isMulCoboundary₁_of_finiteResidue`: every 1-cocycle `G → 𝒪ˣ` is a coboundary.
* `LocalCFT.herbrand_units_eq_one`: `h(𝒪ˣ) = 1`.
-/

noncomputable section

open WithZero CyclicCocycle IsLocalRing

namespace LocalCFT

/-! ## The additive norm of a multiplicative module -/

section Additive

variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem normHom_additive (x : Additive A) :
    CyclicTate.normHom G (Additive A) x = Additive.ofMul (mulNorm (G := G) x.toMul) := by
  rw [CyclicTate.normHom_apply, mulNorm_def, ofMul_prod]
  rfl

omit [Fintype G] in
theorem smul_additive_eq_iff {σ : G} (x : Additive A) :
    σ • x = x ↔ σ • x.toMul = x.toMul :=
  Iff.rfl

end Additive

/-! ## The vanishing theorems -/

section Main

variable {F : Type} [Field F] [hv : Valued F ℤᵐ⁰] [CompleteSpace F]
variable {G : Type} [Group G] [Fintype G] [MulSemiringAction G (integers (F := F))]
variable {σ : G}

attribute [local instance] Units.mulDistribMulActionRight residueMulSemiringAction

variable [Finite (ResidueField (integers (F := F)))]
  [FaithfulSMul G (ResidueField (integers (F := F)))]

variable (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)
  (hG : ∀ (g : G) (a : integers (F := F)),
    Valued.v ((g • a : integers (F := F)) : F) = Valued.v ((a : integers (F := F)) : F))
  {π : integers (F := F)} (hπ : Valued.v ((π : integers (F := F)) : F) = exp (-1 : ℤ))
  (hπG : ∀ g : G, g • π = π)

include hσ hG hπ hπG

omit [Finite (ResidueField (integers (F := F)))] in
/-- **`Ĥ¹(G, 𝒪ˣ) = 0` at an unramified place.** -/
theorem exists_smul_div_of_mulNorm_eq_one_of_finiteResidue {x : (integers (F := F))ˣ}
    (hx : mulNorm (G := G) x = 1) : ∃ y : (integers (F := F))ˣ, σ • y / y = x :=
  (isLocalData_residue hG π hπ hπG).exists_smul_div_of_mulNorm_eq_one
    (fun _ h ↦ exists_smul_div_units_of_faithful hσ h)
    (fun _ h ↦ exists_smul_sub_of_faithful hσ h) hx

/-- **`Ĥ⁰(G, 𝒪ˣ) = 0` at an unramified place.** -/
theorem exists_mulNorm_eq_of_smul_eq_of_finiteResidue {x : (integers (F := F))ˣ}
    (hx : σ • x = x) : ∃ y : (integers (F := F))ˣ, mulNorm (G := G) y = x :=
  (isLocalData_residue hG π hπ hπG).exists_mulNorm_eq_of_smul_eq
    (fun _ h ↦ exists_mulNorm_units_of_faithful hσ h)
    (fun _ h ↦ exists_normHom_of_faithful hσ h) hx

omit [Finite (ResidueField (integers (F := F)))] in
/-- **Every multiplicative 1-cocycle `G → 𝒪ˣ` is a coboundary** at an unramified place. -/
theorem isMulCoboundary₁_of_finiteResidue {f : G → (integers (F := F))ˣ}
    (hf : groupCohomology.IsMulCocycle₁ f) : groupCohomology.IsMulCoboundary₁ f :=
  CyclicCocycle.isMulCoboundary₁_of_mulNorm hσ
    (fun _ hx ↦ exists_smul_div_of_mulNorm_eq_one_of_finiteResidue hσ hG hπ hπG hx) hf

/-- **The Herbrand quotient of `𝒪ˣ` is `1`** at an unramified place. -/
theorem herbrand_units_eq_one :
    CyclicTate.herbrand G (Additive (integers (F := F))ˣ) σ = 1 := by
  have h0 : Subsingleton (CyclicTate.TateH0 G (Additive (integers (F := F))ˣ) σ) := by
    rw [CyclicTate.tateH0_subsingleton_iff]
    intro x hx
    obtain ⟨y, hy⟩ := exists_mulNorm_eq_of_smul_eq_of_finiteResidue hσ hG hπ hπG hx
    exact ⟨Additive.ofMul y, by rw [normHom_additive]; exact congrArg Additive.ofMul hy⟩
  have h1 : Subsingleton (CyclicTate.TateH1 G (Additive (integers (F := F))ˣ) σ) := by
    rw [CyclicTate.tateH1_subsingleton_iff]
    intro x hx
    rw [normHom_additive] at hx
    obtain ⟨y, hy⟩ := exists_smul_div_of_mulNorm_eq_one_of_finiteResidue hσ hG hπ hπG
      (x := x.toMul) (by simpa using hx)
    exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩
  exact CyclicTate.herbrand_eq_one_of_subsingleton σ

end Main

end LocalCFT
