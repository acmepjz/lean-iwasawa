/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.Induced
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

@[expose] public section

/-!
# Hilbert's Theorem 90 for a faithful finite action

**Noether's form of Hilbert 90 is already in Mathlib**, as
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units` and
`groupCohomology.H1ofAutOnUnitsUnique : Unique (H¹(Aut_K(L), Lˣ))`, for a finite extension of
fields `L / K` and the *full* automorphism group `Aut_K(L)`.

The local factors of the ideles need a version for a group which is not presented as a full
automorphism group: the decomposition group `D_w ≤ Gal(L/K)` acting on the completion `L_w`.
The only property of `Aut_K(L)` used in Noether's argument is that its elements are *distinct*
field endomorphisms of `L`, so that Dedekind's independence of characters applies.  We
therefore reprove the statement for an arbitrary finite group acting faithfully on a field,
which contains Mathlib's version and applies verbatim to `D_w` acting on `L_w`.

## Main statements

* `groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_faithful`: a multiplicative 1-cocycle
  `f : G → Fˣ` for a faithful action of a finite group `G` on a field `F` is a 1-coboundary.
* `groupCohomology.H1_units_eq_zero`: `H¹(G, Fˣ) = 0`.
-/

noncomputable section

open Finset

attribute [local instance] Units.mulDistribMulActionRight

namespace groupCohomology

variable {G F : Type} [Group G] [Field F] [MulSemiringAction G F]

/-- **Dedekind's independence of characters** in the form needed here: if a group `G` acts
faithfully on a field `F` by ring automorphisms, then the functions `x ↦ g • x` are linearly
independent over `F`. -/
theorem linearIndependent_smul_of_faithful
    (hG : Function.Injective fun (g : G) ↦ (fun x : F ↦ g • x)) :
    LinearIndependent F fun (g : G) ↦ (fun x : F ↦ g • x) :=
  (linearIndependent_monoidHom F F).comp
    (fun g : G ↦ MulDistribMulAction.toMonoidHom F g)
    (fun _ _ hgg' ↦ hG (funext fun x ↦ congrFun (congrArg DFunLike.coe hgg') x))

variable [Finite G]

set_option maxHeartbeats 1000000 in
/-- **Hilbert's Theorem 90** (Noether's form), for an arbitrary faithful action of a finite
group `G` on a field `F`: every multiplicative 1-cocycle `f : G → Fˣ` is a 1-coboundary, i.e.
there is `β : Fˣ` with `g • β / β = f g` for all `g`. -/
theorem isMulCoboundary₁_of_isMulCocycle₁_of_faithful
    (hG : Function.Injective fun (g : G) ↦ (fun x : F ↦ g • x))
    (f : G → Fˣ) (hf : IsMulCocycle₁ f) : IsMulCoboundary₁ f := by
  cases nonempty_fintype G
  -- The "resolvent" `b z = ∑_h f(h) · h(z)` is not identically zero, by independence of
  -- characters, since its coefficients `f h` are units.
  have hbne : ∃ z : F, ∑ h : G, (f h : F) * h • z ≠ 0 := by
    by_contra hc
    push Not at hc
    have hsum : ∑ h : G, (f h : F) • (fun x : F ↦ h • x) = 0 := by
      funext z
      rw [Finset.sum_apply, Pi.zero_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact hc z
    exact (f 1).ne_zero
      (Fintype.linearIndependent_iff.1 (linearIndependent_smul_of_faithful hG)
        (fun h ↦ (f h : F)) hsum 1)
  obtain ⟨z, hz⟩ := hbne
  set b : F := ∑ h : G, (f h : F) * h • z with hbdef
  -- The cocycle relation says exactly that `g • b = f(g)⁻¹ · b`.
  have key : ∀ g : G, g • b = ((f g)⁻¹ : Fˣ) * b := by
    intro g
    have h₁ : g • b = ∑ h : G, ((f (g * h) : F) * ((f g)⁻¹ : Fˣ)) * ((g * h) • z) := by
      rw [hbdef, smul_sum]
      refine Finset.sum_congr rfl fun h _ ↦ ?_
      rw [smul_mul', smul_smul]
      congr 1
      have := hf g h
      rw [this]
      push_cast
      rw [mul_assoc, mul_inv_cancel₀ (f g).ne_zero, mul_one]
    have h₂ : ∀ h : G, (f (g * h) : F) * ((f g)⁻¹ : Fˣ) * ((g * h) • z) =
        ((f g)⁻¹ : Fˣ) * ((f (g * h) : F) * ((g * h) • z)) := by
      intro h; ring
    rw [h₁]
    simp only [h₂, ← Finset.mul_sum]
    congr 1
    exact Fintype.sum_bijective (fun h ↦ g * h) (Group.mulLeft_bijective g) _ _ fun _ ↦ rfl
  refine ⟨(Units.mk0 b hz)⁻¹, fun g ↦ ?_⟩
  refine Units.ext ?_
  have hgb : g • b⁻¹ = (g • b)⁻¹ := map_inv₀ (MulSemiringAction.toRingHom G F g) b
  have : ((g • (Units.mk0 b hz)⁻¹ / (Units.mk0 b hz)⁻¹ : Fˣ) : F) = (g • b⁻¹) * b := rfl
  rw [this, hgb, key g]
  field_simp
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- **`H¹(G, Fˣ) = 0`** for any faithful action of a finite group `G` on a field `F`. -/
theorem H1_units_eq_zero
    (hG : Function.Injective fun (g : G) ↦ (fun x : F ↦ g • x))
    (x : H1 (Rep.ofMulDistribMulAction G Fˣ)) : x = 0 :=
  H1_induction_on x fun y => (H1π_eq_zero_iff _).2 <| by
    refine (coboundariesOfIsMulCoboundary₁ ?_).2
    obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_faithful hG _
      (isMulCocycle₁_of_mem_cocycles₁ _ y.2)
    exact ⟨β, hβ⟩

/-- `H¹(G, Fˣ)` is trivial for any faithful action of a finite group `G` on a field `F`. -/
theorem subsingleton_H1_units
    (hG : Function.Injective fun (g : G) ↦ (fun x : F ↦ g • x)) :
    Subsingleton (H1 (Rep.ofMulDistribMulAction G Fˣ)) :=
  ⟨fun x y ↦ by rw [H1_units_eq_zero hG x, H1_units_eq_zero hG y]⟩

end groupCohomology
