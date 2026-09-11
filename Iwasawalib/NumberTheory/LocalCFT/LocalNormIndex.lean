/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.FaithfulHilbert90
public import Iwasawalib.NumberTheory.LocalCFT.TameRamified
public import Iwasawalib.GroupCohomology.LocalHilbert90

@[expose] public section

/-!
# The local norm index `#(K_v^× / N L_w^×) = [L_w : K_v]`

The two halves of the local invariant map are

* the **denominator**, `Ĥ¹(D_w, L_w^×) = 0`, which is Hilbert 90 and holds at *every* finite
  place: the decomposition group acts faithfully on the completion
  (`NumberField.decompositionGroup_smul_injective`), so
  `Iwasawalib/NumberTheory/LocalCFT/FaithfulHilbert90.lean` applies with no hypothesis on the
  ramification;
* the **numerator**, `#Ĥ⁰(D_w, L_w^×) = #D_w`, which needs the Herbrand quotient
  `h(L_w^×) = #D_w` and is therefore only available where that is: at unramified places
  (`NumberField.herbrand_adicCompletion_units_eq_card`) and at places whose decomposition group
  has order prime to the residue characteristic
  (`NumberField.herbrand_adicCompletion_units_eq_card_tame`).

Since `Ĥ⁰(D_w, L_w^×) = (L_w^×)^{D_w} / N(L_w^×)` and `(L_w^×)^{D_w} = K_v^×`, the second
statement is the **local norm index**: the index of the norm subgroup in `K_v^×` is the local
degree.  It is the order statement underlying the local invariant map
`inv_w : H²(Gal(L_w/K_v), L_w^×) ≅ (1/n)ℤ / ℤ`, and it is the local input that a global Hasse
principle argument sums over the places.

**Scope.**  The vanishing of `Ĥ¹` is unconditional.  The order of `Ĥ⁰` is proved here in the
unramified and the tame cases only; the wild case `p ∣ #D_w` is blocked on `h(O_w^×) = 1`.

*Correction (2026-09-11).*  This paragraph used to say that `h(O_w^×) = 1` needs only the
`p`-adic logarithm isomorphism `1 + 𝔪^m ≅ 𝔪^m`.  That was incomplete: the logarithm computes
`h(O_w^×)` from `h(O_w⁺)`, and the latter is *not* trivial to come by, since no uniformiser of
a ramified `L_w` is `D_w`-fixed and `O_w` itself is `O_v[D_w]`-free only in the tame case
(Noether).  What it needs is a `D_w`-stable `O_v`-lattice in `L_w` isomorphic to `O_v[D_w]`
together with commensurability-invariance of the Herbrand quotient — the local normal basis
theorem for lattices.

That half is now available, unconditionally and at every finite place:
`NumberField.herbrand_adicCompletionIntegers_eq_one` in
`Iwasawalib/NumberTheory/LocalCFT/IntegralNormalBasis.lean` proves `h(D_w, O_w⁺) = 1`, built on
the normal basis of `L_w / K_v` indexed by the decomposition group
(`Iwasawalib/NumberTheory/LocalCFT/LocalNormalBasis.lean`) and on the vanishing of the Tate
cohomology of a regularly induced module
(`Iwasawalib/GroupCohomology/InducedTate.lean`).  So the remaining obstruction in the wild case
is *exactly* the multiplicative–additive comparison `U^(m) ≅ 𝔪^m`, and nothing else; the
reduction is recorded in `Iwasawalib/NumberTheory/LocalCFT/WildNormIndex.lean`.  See also the
scope discussion in `Iwasawalib/NumberTheory/LocalCFT/TameRamified.lean`.

## Main statements

* `NumberField.subsingleton_tateH1_adicCompletionUnits`: `Ĥ¹(D_w, L_w^×) = 0`, unconditional.
* `NumberField.card_tateH1_adicCompletionUnits`: `#Ĥ¹(D_w, L_w^×) = 1`, unconditional.
* `NumberField.card_tateH0_adicCompletionUnits_unramified`: `#Ĥ⁰(D_w, L_w^×) = #D_w` at an
  unramified place.
* `NumberField.card_tateH0_adicCompletionUnits_tame`: the same at a place whose decomposition
  group has order prime to the residue characteristic.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero LocalCFT
open scoped WithZero

namespace NumberField

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] decompositionIntegersMulSemiringAction
  Units.mulDistribMulActionRight

variable [Fintype (decompositionGroup K L w)] {σ : decompositionGroup K L w}

/-! ## Hilbert 90 in Tate form, at every finite place -/

omit [NumberField K] [IsGalois K L] [w.asIdeal.LiesOver v.asIdeal] in
/-- **`Ĥ¹(D_w, L_w^×) = 0` at every finite place.**  No hypothesis on the ramification: this is
Hilbert 90 for the faithful action of `D_w` on `L_w`, in the two-periodic Tate model. -/
theorem subsingleton_tateH1_adicCompletionUnits
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) :
    Subsingleton (CyclicTate.TateH1 (decompositionGroup K L w)
      (Additive (w.adicCompletion L)ˣ) σ) :=
  LocalCFT.subsingleton_tateH1_units_of_faithful hσ (decompositionGroup_smul_injective w)

omit [NumberField K] [IsGalois K L] [w.asIdeal.LiesOver v.asIdeal] in
/-- `#Ĥ¹(D_w, L_w^×) = 1` at every finite place. -/
theorem card_tateH1_adicCompletionUnits
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) :
    Nat.card (CyclicTate.TateH1 (decompositionGroup K L w)
      (Additive (w.adicCompletion L)ˣ) σ) = 1 :=
  LocalCFT.card_tateH1_units_of_faithful hσ (decompositionGroup_smul_injective w)

/-! ## The norm index -/

/-- **The local norm index at an unramified place**:
`#Ĥ⁰(D_w, L_w^×) = #(K_v^× / N L_w^×) = #D_w = [L_w : K_v]`. -/
theorem card_tateH0_adicCompletionUnits_unramified
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) :
    Nat.card (CyclicTate.TateH0 (decompositionGroup K L w)
      (Additive (w.adicCompletion L)ˣ) σ) = Nat.card (decompositionGroup K L w) :=
  LocalCFT.card_tateH0_units_of_faithful_of_herbrand hσ
    (decompositionGroup_smul_injective w)
    (herbrand_adicCompletion_units_eq_card v w h hσ)

omit [IsGalois K L] in
/-- **The local norm index at a place whose decomposition group has order prime to the residue
characteristic**: `#Ĥ⁰(D_w, L_w^×) = #(K_v^× / N L_w^×) = #D_w = [L_w : K_v]`.  This covers
every tamely ramified place, and is the ramified case of the local norm index. -/
theorem card_tateH0_adicCompletionUnits_tame
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ)
    {p : ℕ} (hp : (p : 𝓞 L) ∈ w.asIdeal)
    {a b : ℤ} (hab : a * (Nat.card (decompositionGroup K L w)) + b * p = 1) :
    Nat.card (CyclicTate.TateH0 (decompositionGroup K L w)
      (Additive (w.adicCompletion L)ˣ) σ) = Nat.card (decompositionGroup K L w) :=
  LocalCFT.card_tateH0_units_of_faithful_of_herbrand hσ
    (decompositionGroup_smul_injective w)
    (herbrand_adicCompletion_units_eq_card_tame w hσ hp hab)

end NumberField
