/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.Induced
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Algebra.GroupWithZero.Action.Pi

@[expose] public section

/-!
# `H¹` of a product of multiplicative modules

`H¹(G, ∏ᵢ Mᵢ) = 0` as soon as `H¹(G, Mᵢ) = 0` for every `i`, for an arbitrary index type: a
1-cocycle with values in a product is a family of 1-cocycles, each of which is a 1-coboundary,
and the resulting family of witnesses is a witness for the product.

This is the "`H¹` commutes with products" step of the computation of `H¹(G, 𝕀_L)`, where the
ideles are a restricted product of the semilocal factors `∏_{w ∣ v} L_w^×`.

## Main statements

* `groupCohomology.isZero_H1_ofMulDistribMulAction_iff`: `H¹(G, M) = 0` if and only if every
  multiplicative 1-cocycle `G → M` is a 1-coboundary.
* `groupCohomology.isMulCoboundary₁_pi`: a 1-cocycle into a product is a 1-coboundary as soon
  as each of its components is.
* `groupCohomology.isZero_H1_pi`: `H¹(G, ∏ᵢ Mᵢ) = 0` when every `H¹(G, Mᵢ) = 0`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace groupCohomology

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- `H¹(G, M) = 0` if and only if every multiplicative 1-cocycle is a 1-coboundary. -/
theorem isZero_H1_ofMulDistribMulAction_iff :
    IsZero (groupCohomology (Rep.ofMulDistribMulAction G M) 1) ↔
      ∀ f : G → M, IsMulCocycle₁ f → IsMulCoboundary₁ f := by
  constructor
  · intro h f hf
    have : Subsingleton (groupCohomology (Rep.ofMulDistribMulAction G M) 1) :=
      ModuleCat.subsingleton_of_isZero h
    exact isMulCoboundary₁_of_mem_coboundaries₁ f
      ((H1π_eq_zero_iff (cocyclesOfIsMulCocycle₁ hf)).1 (Subsingleton.elim _ _))
  · intro h
    have hzero : ∀ x : groupCohomology (Rep.ofMulDistribMulAction G M) 1, x = 0 := fun x ↦
      H1_induction_on x fun y ↦ (H1π_eq_zero_iff _).2 <|
        (coboundariesOfIsMulCoboundary₁
          (h _ (isMulCocycle₁_of_mem_cocycles₁ (M := M) _ y.2))).2
    have : Subsingleton (groupCohomology (Rep.ofMulDistribMulAction G M) 1) :=
      ⟨fun x y ↦ by rw [hzero x, hzero y]⟩
    exact ModuleCat.isZero_of_subsingleton _

variable {ι : Type} {N : ι → Type} [∀ i, CommGroup (N i)] [∀ i, MulDistribMulAction G (N i)]

/-- The components of a multiplicative 1-cocycle with values in a product are 1-cocycles. -/
theorem isMulCocycle₁_apply {f : G → ∀ i, N i} (hf : IsMulCocycle₁ f) (i : ι) :
    IsMulCocycle₁ fun g ↦ f g i := fun g h ↦ congrFun (hf g h) i

/-- A multiplicative 1-cocycle with values in a product is a 1-coboundary as soon as each of
its components is. -/
theorem isMulCoboundary₁_pi {f : G → ∀ i, N i} (hf : IsMulCocycle₁ f)
    (h : ∀ (i : ι) (fi : G → N i), IsMulCocycle₁ fi → IsMulCoboundary₁ fi) :
    IsMulCoboundary₁ f := by
  choose b hb using fun i ↦ h i _ (isMulCocycle₁_apply hf i)
  exact ⟨fun i ↦ b i, fun g ↦ funext fun i ↦ hb i g⟩

/-- **`H¹` commutes with products.**  If `H¹(G, Nᵢ) = 0` for every `i`, then
`H¹(G, ∏ᵢ Nᵢ) = 0`. -/
theorem isZero_H1_pi
    (h : ∀ i : ι, IsZero (groupCohomology (Rep.ofMulDistribMulAction G (N i)) 1)) :
    IsZero (groupCohomology (Rep.ofMulDistribMulAction G (∀ i, N i)) 1) :=
  isZero_H1_ofMulDistribMulAction_iff.2 fun _ hf ↦
    isMulCoboundary₁_pi hf fun i ↦ isZero_H1_ofMulDistribMulAction_iff.1 (h i)

/-! ## Transport along an equivariant multiplicative equivalence -/

section Congr

variable {N : Type} [CommGroup N] [MulDistribMulAction G N]

/-- Cohomology is transported along an equivariant multiplicative equivalence. -/
def mulDistribCongr (e : M ≃* N) (he : ∀ (g : G) (m : M), e (g • m) = g • e m) (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction G M) n ≅
      groupCohomology (Rep.ofMulDistribMulAction G N) n :=
  mapIso (MulEquiv.refl G) (MulEquiv.toAdditive e).toIntLinearEquivOfModule
    (fun g ↦ LinearMap.ext fun m ↦ congrArg Additive.ofMul (he g (Additive.toMul m))) n

/-- `H¹` vanishing is transported along an equivariant multiplicative equivalence. -/
theorem isZero_H1_of_mulEquiv (e : M ≃* N) (he : ∀ (g : G) (m : M), e (g • m) = g • e m)
    (h : IsZero (groupCohomology (Rep.ofMulDistribMulAction G N) 1)) :
    IsZero (groupCohomology (Rep.ofMulDistribMulAction G M) 1) :=
  h.of_iso (mulDistribCongr e he 1)

/-- **`H¹` of a binary product.**  If `H¹(G, M) = 0` and `H¹(G, N) = 0` then
`H¹(G, M × N) = 0`. -/
theorem isZero_H1_prod (hM : IsZero (groupCohomology (Rep.ofMulDistribMulAction G M) 1))
    (hN : IsZero (groupCohomology (Rep.ofMulDistribMulAction G N) 1)) :
    IsZero (groupCohomology (Rep.ofMulDistribMulAction G (M × N)) 1) := by
  refine isZero_H1_ofMulDistribMulAction_iff.2 fun f hf ↦ ?_
  obtain ⟨a, ha⟩ := isZero_H1_ofMulDistribMulAction_iff.1 hM (fun g ↦ (f g).1)
    (fun g h ↦ congrArg Prod.fst (hf g h))
  obtain ⟨b, hb⟩ := isZero_H1_ofMulDistribMulAction_iff.1 hN (fun g ↦ (f g).2)
    (fun g h ↦ congrArg Prod.snd (hf g h))
  exact ⟨(a, b), fun g ↦ Prod.ext (ha g) (hb g)⟩

/-- **`H¹` of a binary product, converse.**  `H¹(G, M × N) = 0` implies `H¹(G, M) = 0`. -/
theorem isZero_H1_of_prod_left
    (h : IsZero (groupCohomology (Rep.ofMulDistribMulAction G (M × N)) 1)) :
    IsZero (groupCohomology (Rep.ofMulDistribMulAction G M) 1) := by
  refine isZero_H1_ofMulDistribMulAction_iff.2 fun f hf ↦ ?_
  obtain ⟨a, ha⟩ := isZero_H1_ofMulDistribMulAction_iff.1 h (fun g ↦ (f g, 1))
    (fun g h ↦ Prod.ext (hf g h) (by simp))
  exact ⟨a.1, fun g ↦ congrArg Prod.fst (ha g)⟩

/-- **`H¹` of a binary product, converse.**  `H¹(G, M × N) = 0` implies `H¹(G, N) = 0`. -/
theorem isZero_H1_of_prod_right
    (h : IsZero (groupCohomology (Rep.ofMulDistribMulAction G (M × N)) 1)) :
    IsZero (groupCohomology (Rep.ofMulDistribMulAction G N) 1) := by
  refine isZero_H1_ofMulDistribMulAction_iff.2 fun f hf ↦ ?_
  obtain ⟨a, ha⟩ := isZero_H1_ofMulDistribMulAction_iff.1 h (fun g ↦ (1, f g))
    (fun g h ↦ Prod.ext (by simp) (hf g h))
  exact ⟨a.2, fun g ↦ congrArg Prod.snd (ha g)⟩

end Congr

end groupCohomology
