/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.Hypothesis
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.UnramifiedTransport
public import Iwasawalib.NumberTheory.ZpExtension.IwasawaTheorem

@[expose] public section

/-!
# Iwasawa's theorem from the Hilbert class field theorems

Let `K∞ / K` be a `ℤₚ`-extension of a number field with layers `Kₙ`, let `Lₙ` be the maximal
unramified abelian `p`-extension of `Kₙ` (`MvZpExtension.Ln`) and `K∞ Lₙ` its compositum with
`K∞` (`MvZpExtension.Ln'`). This file proves Iwasawa's theorem
`ord_p #Cl(Kₙ) = μ pⁿ + λ n + ν` (for all large `n`) from the two classical statements of Hilbert
class field theory, `NumberField.HilbertClassFieldUpperBound` and
`NumberField.HilbertClassFieldExistence`, taken as explicit hypotheses. Nothing here depends on
`sorryAx`.

The proof is the assembly `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_eventual_Yn_generators`
(`Iwasawalib/NumberTheory/ZpExtension/IwasawaTheorem.lean`), applied to the generator description
`MvZpExtension.exists_eventual_Yn_generators` (with the local input
`MvZpExtension.exists_restrictNormalHom_pow_eq_one_of_liesOver_adicAbv`) and to the eventual
cardinality bridge `MvZpExtension.EventualClassNumberCardinalityBridge`. Class field theory
enters only through the bridge, which is proved here from the two hypotheses: they give the
finiteness and the degree of `Lₙ / Kₙ` and of `K∞ Lₙ / K∞`, and the existence of a ramified
place, which makes `Lₙ` and `K∞` linearly disjoint over `Kₙ` for large `n`
(`MvZpExtension.exists_eventually_linearDisjoint_Ln_Kinf_of_ramified_of_finite`). The finiteness
of `Lₙ / Kₙ` and of `K∞ Lₙ / K∞` is not available as an instance (it is class field theory), so
it is supplied by hand from the hypotheses.

Both hypotheses are only used at the universe `Kinf : Type u` (`.{u, u}`): they are applied to
the layers `Kₙ` and to the separable closure of `K∞`, all of which live in `Type u`. For the
existence of a ramified place, the upper bound is applied to `K∞ / K₀` rather than to `K∞ / K`,
so that no other universe is needed.

## Main statements

* `MvZpExtension.finiteDimensional_Ln_of_hcf`: `Lₙ / Kₙ` is finite.
* `MvZpExtension.finrank_Ln_of_hcf`: `[Lₙ : Kₙ] = p ^ ord_p(h_{Kₙ})`.
* `MvZpExtension.finiteDimensional_Ln'_of_hcf`: `K∞ Lₙ / K∞` is finite.
* `MvZpExtension.exists_inertiaSubgroup_ne_bot_of_hcf`: some place of `K∞` ramifies in `K∞ / K`.
* `MvZpExtension.card_gal_Ln'_eq_classNumber_pow_of_linearDisjoint_of_hcf`:
  `#Gal(K∞ Lₙ / K∞) = p ^ ord_p(h_{Kₙ})` when `Lₙ` and `K∞` are linearly disjoint over `Kₙ`.
* `MvZpExtension.exists_eventualClassNumberCardinalityBridge_of_hcf`: the eventual cardinality
  bridge `MvZpExtension.EventualClassNumberCardinalityBridge`.
* `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf`: **Iwasawa's theorem**, assuming the
  two Hilbert class field theorems.
-/

universe u

open IntermediateField NumberField

namespace MvZpExtension

section Layers

variable {p : ℕ} [Fact p.Prime] {ι K : Type*} {Kinf : Type u} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]
variable (H : MvZpExtension p ι K Kinf)

/-- Assuming the upper-bound half of the Hilbert class field theorem, `Lₙ / Kₙ` is finite: `Lₙ` is
isomorphic to an intermediate field of the maximal unramified abelian extension of `Kₙ`, which is
finite by `NumberField.finiteDimensional_maximalUnramifiedAbelianExtension_of_hcf`. -/
theorem finiteDimensional_Ln_of_hcf (hU : HilbertClassFieldUpperBound.{u, u}) (n : ℕ) :
    FiniteDimensional (H.Kn n) (H.Ln n) :=
  haveI := finiteDimensional_maximalUnramifiedAbelianExtension_of_hcf hU (H.Kn n)
    (SeparableClosure Kinf)
  (IntermediateField.liftAlgEquiv <| IntermediateField.maximalGaloisSExtension (H.Kn n)
    (NumberField.maximalUnramifiedAbelianExtension (H.Kn n) (SeparableClosure Kinf))
      {p}).toLinearEquiv.finiteDimensional

/-- **`[Lₙ : Kₙ] = p ^ ord_p(h_{Kₙ})`**, assuming both halves of the Hilbert class field theorem
(blueprint node `Xn-isom-An`). The degree of the maximal unramified abelian extension is
`NumberField.finrank_maximalUnramifiedAbelianExtension_eq_classNumber_of_hcf`. -/
theorem finrank_Ln_of_hcf (hU : HilbertClassFieldUpperBound.{u, u})
    (hE : HilbertClassFieldExistence.{u, u}) (n : ℕ) :
    Module.finrank (H.Kn n) (H.Ln n) =
      p ^ multiplicity p (NumberField.classNumber (H.Kn n)) := by
  have := finiteDimensional_maximalUnramifiedAbelianExtension_of_hcf hU (H.Kn n)
    (SeparableClosure Kinf)
  rw [Ln, ← (IntermediateField.liftAlgEquiv <| IntermediateField.maximalGaloisSExtension (H.Kn n)
    (NumberField.maximalUnramifiedAbelianExtension (H.Kn n) (SeparableClosure Kinf))
      {p}).toLinearEquiv.finrank_eq,
    IntermediateField.finrank_maximalGaloisSExtension_singleton_bot,
    finrank_maximalUnramifiedAbelianExtension_eq_classNumber_of_hcf hU hE,
    Nat.multiplicity_eq_factorization Fact.out (NumberField.classNumber_ne_zero _)]

/-- Assuming the upper-bound half of the Hilbert class field theorem, `K∞ Lₙ / K∞` is finite. -/
theorem finiteDimensional_Ln'_of_hcf (hU : HilbertClassFieldUpperBound.{u, u}) (n : ℕ) :
    FiniteDimensional Kinf (H.Ln' n) :=
  haveI := H.finiteDimensional_Ln_of_hcf hU n
  IntermediateField.finiteDimensional_adjoin_of_isGalois (F := H.Kn n) (H.Ln n)

include H in
/-- **At least one place of `K∞` ramifies in `K∞ / K`**, assuming the upper-bound half of the
Hilbert class field theorem.

If no place ramified, then `K∞ / K` would be everywhere unramified, hence so would be the abelian
extension `K∞ / K₀`; by `NumberField.finiteDimensional_of_hilbertClassFieldUpperBound` it would be
finite, and then `K∞ / K` would be finite, which it is not. The bound is applied over `K₀` rather
than over `K` so that it is only needed at the universe of `K∞`. -/
theorem exists_inertiaSubgroup_ne_bot_of_hcf (hU : HilbertClassFieldUpperBound.{u, u})
    [Unique ι] : ∃ w : AbsoluteValue Kinf ℝ, w.inertiaSubgroup K ≠ ⊥ := by
  by_contra hcon
  have hc : ∀ w : AbsoluteValue Kinf ℝ, w.inertiaSubgroup K = ⊥ := fun w ↦ by
    by_contra h
    exact hcon ⟨w, h⟩
  have := H.isGalois (⊤ : IntermediateField K Kinf)
  have : NumberField.IsUnramifiedEverywhere K ↥(⊤ : IntermediateField K Kinf) :=
    AbsoluteValue.isUnramifiedEverywhere_of_inertiaSubgroup_le_fixingSubgroup K ⊤
      fun w ↦ by rw [hc w]; exact bot_le
  have : NumberField.IsUnramifiedEverywhere K Kinf :=
    IsUnramifiedEverywhere.of_algEquiv (IntermediateField.topEquiv (F := K) (E := Kinf))
  have : NumberField.IsUnramifiedEverywhere (H.Kn 0) Kinf :=
    IsUnramifiedEverywhere.tower_top K (H.Kn 0) Kinf
  have : IsAbelianGalois (H.Kn 0) Kinf := (H.shift 0).isAbelianGalois_Kinf
  have : FiniteDimensional (H.Kn 0) Kinf :=
    finiteDimensional_of_hilbertClassFieldUpperBound hU (H.Kn 0) Kinf
  exact H.infinite_dimensional (Module.Finite.trans (H.Kn 0) Kinf)

/-- If `Lₙ` and `K∞` are linearly disjoint over `Kₙ`, then
`#Gal(K∞ Lₙ / K∞) = p ^ ord_p(h_{Kₙ})`, assuming both halves of the Hilbert class field theorem.
-/
theorem card_gal_Ln'_eq_classNumber_pow_of_linearDisjoint_of_hcf
    (hU : HilbertClassFieldUpperBound.{u, u}) (hE : HilbertClassFieldExistence.{u, u}) (n : ℕ)
    (hld : (H.Ln n).LinearDisjoint Kinf) :
    Nat.card Gal(↥(H.Ln' n) / Kinf) =
      p ^ multiplicity p (NumberField.classNumber (H.Kn n)) := by
  have := H.finiteDimensional_Ln_of_hcf hU n
  have := H.finiteDimensional_Ln'_of_hcf hU n
  rw [IsGalois.card_aut_eq_finrank, ← H.finrank_Ln_of_hcf hU hE n]
  exact IntermediateField.finrank_adjoin_eq_finrank_of_linearDisjoint (H.Ln n) hld

/-- **The eventual class-number cardinality bridge**, assuming both halves of the Hilbert class
field theorem: for a `ℤₚ`-extension `K∞ / K` there is a layer `e` such that
`#Gal(K∞ Lₙ / K∞) = p ^ ord_p(h_{Kₙ})` for all `n ≥ e`. A ramified place
(`MvZpExtension.exists_inertiaSubgroup_ne_bot_of_hcf`) makes `Lₙ` and `K∞` linearly disjoint
over `Kₙ` for large `n`
(`MvZpExtension.exists_eventually_linearDisjoint_Ln_Kinf_of_ramified_of_finite`). -/
theorem exists_eventualClassNumberCardinalityBridge_of_hcf
    (hU : HilbertClassFieldUpperBound.{u, u}) (hE : HilbertClassFieldExistence.{u, u})
    [Unique ι] : ∃ e : ℕ, EventualClassNumberCardinalityBridge H e := by
  obtain ⟨w, hw⟩ := H.exists_inertiaSubgroup_ne_bot_of_hcf hU
  obtain ⟨e, he⟩ := H.exists_eventually_linearDisjoint_Ln_Kinf_of_ramified_of_finite
    (fun n ↦ H.finiteDimensional_Ln_of_hcf hU n) w hw
  exact ⟨e, ⟨fun n hn ↦
    H.card_gal_Ln'_eq_classNumber_pow_of_linearDisjoint_of_hcf hU hE n (he n hn)⟩⟩

end Layers

/-- **Iwasawa's theorem** on the growth of class groups in a `ℤₚ`-extension of number fields
(Washington, *Introduction to cyclotomic fields*, Theorem 13.13), **assuming the two classical
statements of Hilbert class field theory**: the upper bound
`NumberField.HilbertClassFieldUpperBound` (a finite abelian everywhere unramified extension of a
number field `F` has degree at most `h_F`) and the existence statement
`NumberField.HilbertClassFieldExistence` (the Hilbert class field of `F`, of degree `h_F`, exists
inside any separably closed field containing `F`), both at the universe of `K∞`.

For a `ℤₚ`-extension `K∞ / K` of a number field with layers `Kₙ` there are natural numbers `μ`,
`λ`, an integer `ν` and a bound `N` such that `ord_p #Cl(Kₙ) = μ pⁿ + λ n + ν` for all `n > N`.
This theorem does not depend on `sorryAx`: its axioms are `propext`, `Classical.choice` and
`Quot.sound`. The two hypotheses are discharged, from the external `sorry`-free class field
theory library `ClassFieldTheory` (n-yamaguchi-0729/ClassFieldTheory), in the separate
non-module package `IwasawalibCFT` (directory `IwasawalibCFT/`, built with
`cd IwasawalibCFT && lake build`), which states the theorem without hypotheses
(`MvZpExtension.multiplicity_classNumber_Kn_eq₁` in `IwasawalibCFT/IwasawalibCFT/Iwasawa.lean`,
not part of `Iwasawalib`). -/
theorem multiplicity_classNumber_Kn_eq₁_of_hcf
    (hU : NumberField.HilbertClassFieldUpperBound.{u, u})
    (hE : NumberField.HilbertClassFieldExistence.{u, u})
    {p : ℕ} [Fact p.Prime] {ι K : Type*} {Kinf : Type u}
    [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]
    (H : MvZpExtension p ι K Kinf) [Unique ι] :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n > N,
      multiplicity p (NumberField.classNumber (H.Kn n)) = mu * p ^ n + lambda * n + nu := by
  obtain ⟨γ, hγ, e₁, a, hgen⟩ := H.exists_eventual_Yn_generators
    H.exists_restrictNormalHom_pow_eq_one_of_liesOver_adicAbv
  obtain ⟨e₂, hbridge⟩ := H.exists_eventualClassNumberCardinalityBridge_of_hcf hU hE
  exact H.multiplicity_classNumber_Kn_eq₁_of_eventual_Yn_generators γ hγ a hgen hbridge

end MvZpExtension
