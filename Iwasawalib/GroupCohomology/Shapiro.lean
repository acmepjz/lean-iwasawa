/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.Induced
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

@[expose] public section

/-!
# Shapiro's lemma in right-equivariant form

**Shapiro's lemma is already in Mathlib**, as
`groupCohomology.coindIso : Hⁿ(G, Coind_S^G A) ≅ Hⁿ(S, A)`
(`Mathlib/RepresentationTheory/Homological/GroupCohomology/Shapiro.lean`).  This file only
transports it along the isomorphism `Rep.rcoindIsoCoind` of
`Iwasawalib/GroupCohomology/Induced.lean`, so that it applies directly to induced modules
presented in the right-equivariant form `F (g * h) = h⁻¹ • F g` which the number-theoretic
constructions produce, and packages the transport in the form that is actually used: *if a
`G`-module `B` admits a `G`-equivariant isomorphism onto `Ind_H^G A`, then
`Hⁿ(G, B) ≅ Hⁿ(H, A)`*.

## Main definitions

* `groupCohomology.rcoindIso A n : Hⁿ(G, rcoind H A) ≅ Hⁿ(H, A)`.
* `groupCohomology.shapiroOfEquiv`: the same conclusion for any `G`-module `B` equivariantly
  isomorphic to `rcoind H A`.
-/

noncomputable section

universe u

namespace groupCohomology

open CategoryTheory Rep Representation

variable {k G : Type u} [CommRing k] [Group G] {H : Subgroup G}

/-- **Shapiro's lemma**, for the right-equivariant model of the coinduced module:
`Hⁿ(G, Ind_H^G A) ≅ Hⁿ(H, A)`.  This is Mathlib's `groupCohomology.coindIso` transported
along `Rep.rcoindIsoCoind`. -/
def rcoindIso (A : Rep.{u} k H) (n : ℕ) :
    groupCohomology (Rep.rcoind.{u, u, u} H A) n ≅ groupCohomology A n :=
  mapIso (MulEquiv.refl G) (Representation.rcoindEquivCoindₗ H A.ρ)
      (fun σ ↦ LinearMap.ext fun F ↦
        Representation.rcoindEquivCoindₗ_equivariant σ F) n ≪≫
    coindIso A n

/-- Shapiro's lemma in the form in which it is applied: a `G`-module `B` equipped with a
`G`-equivariant isomorphism onto `Ind_H^G A` has `Hⁿ(G, B) ≅ Hⁿ(H, A)`. -/
def shapiroOfEquiv (A : Rep.{u} k H) (B : Rep.{u} k G)
    (e : B.V ≃ₗ[k] (Rep.rcoind.{u, u, u} H A).V)
    (he : ∀ (σ : G) (b : B), e (B.ρ σ b) = (Rep.rcoind.{u, u, u} H A).ρ σ (e b)) (n : ℕ) :
    groupCohomology B n ≅ groupCohomology A n :=
  mapIso (MulEquiv.refl G) e (fun σ ↦ LinearMap.ext fun b ↦ he σ b) n ≪≫ rcoindIso A n

end groupCohomology
