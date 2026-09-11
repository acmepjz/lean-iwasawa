/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.LocalNormIndex
public import Iwasawalib.GroupCohomology.TateHexagon

@[expose] public section

/-!
# The local invariant map as an isomorphism `Ĥ⁰(D_w, L_wˣ) ≃ ℤ/n`
-/

noncomputable section

namespace CyclicTate

namespace IsShortExact

variable {G : Type*} [Group G] [Fintype G] {A B C : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
  {i : A →+[G] B} {p : B →+[G] C} (h : IsShortExact i p) (σ : G)

include h

/-- **If `Ĥ⁰(A) = 0` then `Ĥ⁰(B) → Ĥ⁰(C)` is injective**: exactness at `Ĥ⁰(B)`
(`CyclicTate.IsShortExact.ker_tateH0Map_p`) identifies the kernel with the image of `Ĥ⁰(A)`. -/
theorem injective_tateH0Map_p [Subsingleton (TateH0 G A σ)] :
    Function.Injective (tateH0Map p σ) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, h.ker_tateH0Map_p σ]
  refine eq_bot_iff.2 ?_
  rintro _ ⟨t, rfl⟩
  rw [Subsingleton.elim t 0, map_zero]
  exact AddSubgroup.zero_mem _

/-- **If `Ĥ¹(A) = 0` then `Ĥ⁰(B) → Ĥ⁰(C)` is surjective**: exactness at `Ĥ⁰(C)`
(`CyclicTate.IsShortExact.ker_delta0`) identifies the image with the kernel of the connecting
map `δ⁰ : Ĥ⁰(C) → Ĥ¹(A)`, which is everything. -/
theorem surjective_tateH0Map_p [Subsingleton (TateH1 G A σ)] :
    Function.Surjective (tateH0Map p σ) := by
  rw [← AddMonoidHom.range_eq_top, ← h.ker_delta0 σ]
  exact eq_top_iff.2 fun t _ ↦ by
    rw [AddMonoidHom.mem_ker]
    exact Subsingleton.elim _ _

/-- **`Ĥ⁰(B) ≃ Ĥ⁰(C)` when the sub-module `A` is cohomologically trivial.**  This is the
mechanism behind the local invariant map: for `0 → 𝒪ˣ → Fˣ → ℤ → 0` at an unramified place
both Tate groups of `𝒪ˣ` vanish, so `Ĥ⁰(Fˣ) ≃ Ĥ⁰(ℤ) = ℤ/#G`. -/
def tateH0Equiv [Subsingleton (TateH0 G A σ)] [Subsingleton (TateH1 G A σ)] :
    TateH0 G B σ ≃+ TateH0 G C σ :=
  AddEquiv.ofBijective (tateH0Map p σ)
    ⟨h.injective_tateH0Map_p σ, h.surjective_tateH0Map_p σ⟩

@[simp] theorem tateH0Equiv_apply [Subsingleton (TateH0 G A σ)] [Subsingleton (TateH1 G A σ)]
    (t : TateH0 G B σ) : h.tateH0Equiv σ t = tateH0Map p σ t := rfl

end IsShortExact

end CyclicTate

namespace LocalCFT

open CyclicTate MulAction

/-- Transport of `ZMod` along an equality of moduli. -/
def zmodCongr {m n : ℕ} (h : m = n) : ZMod m ≃+ ZMod n := h ▸ AddEquiv.refl (ZMod m)

@[simp] theorem zmodCongr_refl {n : ℕ} : zmodCongr (rfl : n = n) = AddEquiv.refl (ZMod n) := rfl

section PermLatticeUnit

variable {G : Type*} [Group G] [Fintype G] {σ : G}

theorem card_stabilizer_unit : Nat.card (stabilizer G (() : Unit)) = Nat.card G := by
  rw [show stabilizer G (() : Unit) = ⊤ by ext g; simp [MulAction.mem_stabilizer_iff],
    Nat.card_congr (Subgroup.topEquiv (G := G)).toEquiv]

/-- **`Ĥ⁰(G, ℤ) ≃ ℤ/#G` for the trivial `G`-module `ℤ`**, presented as `PermLattice G Unit`.

This is the target of the local invariant map.  It is `NumberField.PermLattice.tateH0Equiv` at
the one-point `G`-set, whose stabiliser is all of `G`; only the lemmas of
`Iwasawalib/NumberTheory/CFT/PermutationLattice.lean` are used. -/
def permLatticeUnitTateH0Equiv (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) :
    TateH0 G (PermLattice G Unit) σ ≃+ ZMod (Nat.card G) :=
  (PermLattice.tateH0Equiv hgen (() : Unit)).trans (zmodCongr card_stabilizer_unit)

/-- `#Ĥ⁰(G, ℤ) = #G` for the trivial `G`-module `ℤ`. -/
theorem card_permLatticeUnitTateH0 (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) :
    Nat.card (TateH0 G (PermLattice G Unit) σ) = Nat.card G :=
  (PermLattice.card_tateH0 hgen (() : Unit)).trans card_stabilizer_unit

end PermLatticeUnit

/-! ## The invariant map of a complete discretely valued field -/

section LocalField

open WithZero

variable {F : Type*} [Field F] [Valued F ℤᵐ⁰]
variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G F]
  [MulSemiringAction G (integers (F := F))]
  (hG : ∀ (g : G) (x : F), (Valued.v (g • x) : ℤᵐ⁰) = Valued.v x)
  (hcompat : ∀ (g : G) (a : integers (F := F)),
    ((g • a : integers (F := F)) : F) = g • (a : F))

attribute [local instance] Units.mulDistribMulActionRight

/-- **The local invariant map, as an isomorphism `Ĥ⁰(G, Fˣ) ≃ ℤ/#G`.**

`G = ⟨σ⟩` is a finite cyclic group of valuation-preserving automorphisms of a complete
discretely valued field `F` whose valuation is surjective (`hπ` gives a uniformiser), and the
unit group `𝒪ˣ` is assumed cohomologically trivial — both Tate groups vanish, which is the
situation at an **unramified** place.  The valuation sequence `0 → 𝒪ˣ → Fˣ → ℤ → 0` of
`LocalCFT.isShortExact_valHom` then makes `Ĥ⁰(Fˣ) → Ĥ⁰(ℤ) = ℤ/#G` an isomorphism, and the map
is literally "take the valuation of a norm-class representative".

Note the order statement `#Ĥ⁰(G, Fˣ) = #G` alone does **not** give this: a group of order `n`
need not be cyclic.  It is the cohomological triviality of `𝒪ˣ` that pins down the group. -/
def invariantMapEquiv (hπ : ∃ π : F, (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) {σ : G}
    (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g)
    [Subsingleton (TateH0 G (Additive (integers (F := F))ˣ) σ)]
    [Subsingleton (TateH1 G (Additive (integers (F := F))ˣ) σ)] :
    TateH0 G (Additive Fˣ) σ ≃+ ZMod (Nat.card G) :=
  ((isShortExact_valHom hG hcompat hπ).tateH0Equiv σ).trans (permLatticeUnitTateH0Equiv hgen)

/-- A generator of a finite cyclic group generates the underlying additive group. -/
theorem mem_zmultiples_ofMul {H : Type*} [Group H] {τ : H}
    (hgen : ∀ g : H, ∃ k : ℕ, τ ^ k = g) (x : Additive H) :
    x ∈ AddSubgroup.zmultiples (Additive.ofMul τ) := by
  obtain ⟨k, hk⟩ := hgen x.toMul
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨(k : ℤ), ?_⟩
  rw [natCast_zsmul, ← ofMul_pow, hk]
  rfl

/-- **Local reciprocity at an unramified place**: `Fˣ^G / N(Fˣ) ≅ G`.

Composing the invariant map `LocalCFT.invariantMapEquiv` with the identification of a finite
cyclic group with `ℤ/#G` gives an isomorphism of `Ĥ⁰(G, Fˣ) = (F^G)ˣ / N(Fˣ)` with `G` itself
— the local Artin isomorphism, in the unramified situation where `𝒪ˣ` is cohomologically
trivial.  The generator `σ` corresponds to the class of a uniformiser. -/
def localReciprocityEquiv (hπ : ∃ π : F, (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) {σ : G}
    (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g)
    [Subsingleton (TateH0 G (Additive (integers (F := F))ˣ) σ)]
    [Subsingleton (TateH1 G (Additive (integers (F := F))ˣ) σ)] :
    TateH0 G (Additive Fˣ) σ ≃+ Additive G :=
  (invariantMapEquiv hG hcompat hπ hgen).trans
    (zmodAddEquivOfGenerator (G := Additive G) (mem_zmultiples_ofMul hgen) rfl)

end LocalField

end LocalCFT

/-! ## The invariant map at an unramified finite place of a number field -/

namespace NumberField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero LocalCFT CyclicTate

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] decompositionIntegersMulSemiringAction
  IsLocalRing.residueMulSemiringAction Units.mulDistribMulActionRight

variable [Fintype (decompositionGroup K L w)] {σ : decompositionGroup K L w}

theorem exists_pow_eq_of_mem_zpowers
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ)
    (d : decompositionGroup K L w) : ∃ k : ℕ, σ ^ k = d := by
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff d σ).1 (mem_powers_iff_mem_zpowers.2 (hσ d))
  exact ⟨k, hk⟩

/-- **The local invariant map at an unramified place**:
`inv_w : Ĥ⁰(D_w, L_wˣ) ≃ ℤ / n_w`, with `n_w = #D_w = [L_w : K_v]`.

Equivalently `K_vˣ / N(L_wˣ) ≅ ℤ/n_w` is *cyclic* of order `n_w`, which is strictly more than
the order statement `NumberField.card_tateH0_adicCompletionUnits_unramified`.  The isomorphism
is induced by the valuation, using that the unit group `O_wˣ` is cohomologically trivial at an
unramified place (`NumberField.subsingleton_tateH0_units`,
`NumberField.subsingleton_tateH1_units`). -/
def invAdicCompletionUnits (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) :
    TateH0 (decompositionGroup K L w) (Additive (w.adicCompletion L)ˣ) σ
      ≃+ ZMod (Nat.card (decompositionGroup K L w)) :=
  haveI := subsingleton_tateH0_units v w h hσ
  haveI := subsingleton_tateH1_units v w h hσ
  LocalCFT.invariantMapEquiv (F := w.adicCompletion L) (G := decompositionGroup K L w)
    (valued_decomposition_smul w) (fun _ _ ↦ rfl)
    (valuedAdicCompletion_surjective (K := L) w (exp (-1 : ℤ)))
    (exists_pow_eq_of_mem_zpowers w hσ)

end NumberField
