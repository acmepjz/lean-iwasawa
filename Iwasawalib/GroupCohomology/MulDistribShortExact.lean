/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

@[expose] public section

/-!
# Short exact sequences of multiplicative `G`-modules

Group cohomology in Mathlib is stated for `Rep k G`, and a commutative group `A` with a
`MulDistribMulAction M A` becomes the `ℤ`-linear representation `Rep.ofMulDistribMulAction M A`
on `Additive A`.  This file supplies the missing bridge: an `M`-equivariant group homomorphism
is a morphism of representations, and a short exact sequence of `M`-groups
`1 → A → B → C → 1` is a short exact sequence in `Rep ℤ M`.

This is what lets the long exact sequence in group cohomology
(`Mathlib/RepresentationTheory/Homological/GroupCohomology/LongExactSequence.lean`) be applied
to multiplicatively written exact sequences such as `1 → Lˣ → 𝕀_L → C_L → 1`.

## Main definitions

* `Rep.ofMulDistribHom`: an equivariant `A →* B` as a morphism
  `ofMulDistribMulAction M A ⟶ ofMulDistribMulAction M B`.
* `Rep.mulShortComplex`: the short complex attached to an equivariant `A →* B →* C`.

## Main statements

* `Rep.mulShortComplex_shortExact`: it is short exact when `A →* B` is injective, `B →* C` is
  surjective, and the range of the first is the kernel of the second.
-/

noncomputable section

universe u v w

open CategoryTheory ShortComplex

namespace Rep

/-! ## A criterion for short exactness in `Rep k G`

`Rep ℤ G` is a `ConcreteCategory`, but the instance cannot be *synthesised* at `k = ℤ`,
because the `Module ℤ V` instance found by typeclass search is `AddCommGroup.toIntModule`
rather than the one stored in the representation.  The criterion below is therefore proved
once for a general coefficient ring, where `forget₂ (Rep k G) (ModuleCat k)` does elaborate,
and then *applied* at `k = ℤ`, where the instances come from unification. -/

section Criterion

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

/-- A short complex of representations is short exact as soon as it is injective, surjective
and exact on underlying elements. -/
theorem shortExact_of_exact (X : ShortComplex (Rep.{w} k G))
    (hinj : Function.Injective X.f.hom) (hsurj : Function.Surjective X.g.hom)
    (hker : ∀ b : X.X₂, X.g.hom b = 0 → ∃ a : X.X₁, X.f.hom a = b) : X.ShortExact where
  exact := (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 hker
  mono_f := (Rep.mono_iff_injective X.f).2 hinj
  epi_g := (Rep.epi_iff_surjective X.g).2 hsurj

end Criterion

/-! ## Multiplicative short exact sequences -/

variable {M : Type u} [Monoid M] {A B C : Type u} [CommGroup A] [CommGroup B] [CommGroup C]
  [MulDistribMulAction M A] [MulDistribMulAction M B] [MulDistribMulAction M C]

/-- An `M`-equivariant group homomorphism `A →* B` between commutative `M`-groups, as a
morphism of the associated `ℤ`-linear representations. -/
def ofMulDistribHom (f : A →* B) (hf : ∀ (m : M) (a : A), f (m • a) = m • f a) :
    ofMulDistribMulAction M A ⟶ ofMulDistribMulAction M B :=
  ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((MonoidHom.toAdditive f).toIntLinearMap)
    fun m a ↦ congrArg Additive.ofMul (hf m a.toMul)

@[simp]
theorem ofMulDistribHom_hom_apply (f : A →* B) (hf : ∀ (m : M) (a : A), f (m • a) = m • f a)
    (a : Additive A) :
    (ofMulDistribHom (M := M) f hf).hom a = Additive.ofMul (f a.toMul) := rfl

/-- The short complex `A → B → C` in `Rep ℤ M` attached to a pair of composable equivariant
homomorphisms of commutative `M`-groups whose composite is trivial. -/
@[simps X₁ X₂ X₃ f g]
def mulShortComplex (f : A →* B) (hf : ∀ (m : M) (a : A), f (m • a) = m • f a)
    (g : B →* C) (hg : ∀ (m : M) (b : B), g (m • b) = m • g b)
    (hfg : ∀ a : A, g (f a) = 1) : ShortComplex (Rep ℤ M) where
  X₁ := ofMulDistribMulAction M A
  X₂ := ofMulDistribMulAction M B
  X₃ := ofMulDistribMulAction M C
  f := ofMulDistribHom f hf
  g := ofMulDistribHom g hg
  zero := by
    ext a
    exact congrArg Additive.ofMul (hfg a.toMul)

/-- **A short exact sequence of commutative `M`-groups is a short exact sequence in
`Rep ℤ M`.** -/
theorem mulShortComplex_shortExact (f : A →* B) (hf : ∀ (m : M) (a : A), f (m • a) = m • f a)
    (g : B →* C) (hg : ∀ (m : M) (b : B), g (m • b) = m • g b)
    (hfg : ∀ a : A, g (f a) = 1) (hinj : Function.Injective f)
    (hsurj : Function.Surjective g) (hker : ∀ b : B, g b = 1 → ∃ a : A, f a = b) :
    (mulShortComplex f hf g hg hfg).ShortExact :=
  by
  refine shortExact_of_exact (mulShortComplex f hf g hg hfg) (fun _ _ h ↦ hinj h) ?_ ?_
  · intro c
    obtain ⟨b, hb⟩ := hsurj (Additive.toMul (show Additive C from c))
    exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  · intro b hb
    obtain ⟨a, ha⟩ := hker (Additive.toMul (show Additive B from b)) hb
    exact ⟨Additive.ofMul a, congrArg Additive.ofMul ha⟩

end Rep

/-! ## A vanishing criterion from the long exact sequence -/

namespace groupCohomology

open CategoryTheory Limits

variable {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep.{u} k G)}

/-- **A vanishing criterion in the long exact sequence.**  If `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is a
short exact sequence of representations, `Hⁿ(G, X₂) = 0`, and `Hⁿ⁺¹(G, X₁) ⟶ Hⁿ⁺¹(G, X₂)` is
injective, then `Hⁿ(G, X₃) = 0`.

Indeed the connecting map `δ : Hⁿ(G, X₃) ⟶ Hⁿ⁺¹(G, X₁)` is mono because `Hⁿ(G, X₂) = 0`, and
it is zero because its composite with the injective map `Hⁿ⁺¹(G, X₁) ⟶ Hⁿ⁺¹(G, X₂)` is zero. -/
theorem isZero_of_isZero_of_mono (hX : X.ShortExact) (n : ℕ)
    (h₂ : IsZero (groupCohomology X.X₂ n))
    (hmono : Mono (map (MonoidHom.id G) X.f (n + 1))) :
    IsZero (groupCohomology X.X₃ n) := by
  have hδ : δ hX n (n + 1) rfl = 0 := by
    rw [← cancel_mono (map (MonoidHom.id G) X.f (n + 1)), zero_comp]
    exact (mapShortComplex₁ hX (i := n) (j := n + 1) rfl).zero
  have hmono' : Mono (δ hX n (n + 1) rfl) :=
    (ShortComplex.exact_iff_mono _ (h₂.eq_zero_of_src _)).1 (mapShortComplex₃_exact hX rfl)
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (δ hX n (n + 1) rfl), hδ, comp_zero, zero_comp]

end groupCohomology
