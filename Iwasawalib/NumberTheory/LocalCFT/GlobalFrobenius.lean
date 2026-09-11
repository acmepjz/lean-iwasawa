/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.ArtinFrobenius
public import Mathlib.FieldTheory.Galois.Abelian

@[expose] public section

/-!
# The Frobenius of an abelian extension depends only on the prime below

`NumberField.IsUnramifiedEverywhere.artinMap_spec` in
`Iwasawalib/NumberTheory/NumberField/HilbertClassField/ClassFieldTheory.lean` asserts that the
Artin map sends the class of a prime `p` of `𝓞 F` to `arithFrobAt (𝓞 F) Gal(K/F) P.asIdeal` for
*any* prime `P` of `𝓞 K` above `p`.  Both the Artin map and that theorem are still `sorry`.
This file proves the part of that specification which does not mention the Artin map, and which
any construction of it will have to consume:

* the right-hand side does not depend on `P` (`NumberField.arithFrobAt_eq_of_under_eq`), so
  there is a well-defined map `p ↦ Frob_p` on primes of the base
  (`NumberField.exists_globalFrob`);
* at an unramified place that element is what the *local* Artin map of
  `Iwasawalib/NumberTheory/LocalCFT/InvariantRestriction.lean` computes from a uniformiser of
  `K_v` (`NumberField.coe_localArtinAdicCompletionUnits_mk_uniformizer_eq_arithFrobAt`), for any
  place `w` above `v`.

Mathlib's `arithFrobAt` is only well defined up to conjugacy — `isConj_arithFrobAt` is all that
holds in general — which is why the first statement needs `IsAbelianGalois K L`.

## Main statements

* `NumberField.arithFrobAt_eq_of_under_eq`
* `NumberField.exists_heightOneSpectrum_under_eq`
* `NumberField.exists_globalFrob`
* `NumberField.coe_localArtinAdicCompletionUnits_mk_uniformizer_eq_arithFrobAt`

## Scope

What is *not* here is the remaining, deep, half of `artinMap_spec`: that `p ↦ Frob_p`
factors through the ideal class group.  That is Artin reciprocity, and it is not available from
the local computations in `Iwasawalib/NumberTheory/LocalCFT/`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero LocalCFT CyclicTate
open scoped Pointwise

namespace NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] Ideal.Quotient.field IsDedekindDomain.HeightOneSpectrum.isMaximal

/-- **In an abelian extension the arithmetic Frobenius depends only on the prime below.**
Mathlib's `arithFrobAt` is only well defined up to conjugacy (`isConj_arithFrobAt`); in an
abelian Galois group conjugacy is equality. -/
theorem arithFrobAt_eq_of_under_eq [IsAbelianGalois K L]
    (P P' : HeightOneSpectrum (𝓞 L))
    (h : P.asIdeal.under (𝓞 K) = P'.asIdeal.under (𝓞 K)) :
    arithFrobAt (𝓞 K) Gal(L/K) P.asIdeal = arithFrobAt (𝓞 K) Gal(L/K) P'.asIdeal := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_arithFrobAt (𝓞 K) Gal(L/K) P.asIdeal P'.asIdeal h)
  rw [← hc, mul_comm' c, mul_assoc, mul_inv_cancel, mul_one]

omit [NumberField K] [NumberField L] in
variable (K L) in
/-- Every prime of `𝓞 K` lies under a prime of `𝓞 L`, in the `HeightOneSpectrum` formalism. -/
theorem exists_heightOneSpectrum_under_eq (p : HeightOneSpectrum (𝓞 K)) :
    ∃ P : HeightOneSpectrum (𝓞 L), P.asIdeal.under (𝓞 K) = p.asIdeal := by
  haveI : p.asIdeal.IsPrime := p.isPrime
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ := p.asIdeal.nonempty_primesOver (S := 𝓞 L)
  exact ⟨⟨Q, hQ1, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q⟩, (Ideal.over_def Q p.asIdeal).symm⟩

variable (K L) in
/-- **The right-hand side of `NumberField.IsUnramifiedEverywhere.artinMap_spec` is a function of
the prime of the base field alone.**  For an abelian extension there is a map
`p ↦ Frob_p` on the primes of `𝓞 K` whose value at `p` is the arithmetic Frobenius at *every*
prime `P` of `𝓞 L` above `p`.  Any map `ClassGroup (𝓞 K) →* Gal(L/K)` satisfying
`artinMap_spec` must therefore send the class of `p` to `globalFrob K L p`; this is the part of
that specification which does not mention the (still unconstructed)
`NumberField.IsUnramifiedEverywhere.artinMap`. -/
theorem exists_globalFrob [IsAbelianGalois K L] :
    ∃ f : HeightOneSpectrum (𝓞 K) → Gal(L/K), ∀ (p : HeightOneSpectrum (𝓞 K))
      (P : HeightOneSpectrum (𝓞 L)), P.asIdeal.under (𝓞 K) = p.asIdeal →
        f p = arithFrobAt (𝓞 K) Gal(L/K) P.asIdeal := by
  choose F hF using exists_heightOneSpectrum_under_eq K L
  exact ⟨fun p ↦ arithFrobAt (𝓞 K) Gal(L/K) (F p).asIdeal, fun p P hP ↦
    arithFrobAt_eq_of_under_eq _ _ ((hF p).trans hP.symm)⟩

section LocalArtinComputation

/-!
The local-Artin computation below is deliberately restricted to `Type`.  At `Type*` the
elaborator diverges: the `isDefEq` check inside
`coe_localArtinAdicCompletionUnits_mk_uniformizer_eq_arithFrobAt` exceeds 200000 heartbeats,
because the local Artin machinery stacks universe-polymorphic completions.  The three results
above, which are what a construction of the Artin map has to consume, are stated at `Type*`
and are unaffected -- `NumberField.IsUnramifiedEverywhere.artinMap` quantifies over `Type*`,
so a `Type`-only statement would not apply to it at all.
-/

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] decompositionIntegersMulSemiringAction
  IsLocalRing.residueMulSemiringAction Units.mulDistribMulActionRight

/-- **The local Artin map at an unramified place `w` of an abelian extension, applied to a
uniformiser of `K_v`, computes the arithmetic Frobenius at every prime `P` above `v`** — in
particular the value does not depend on which place above `v` the local computation is made at.
This is the local computation of the element that
`NumberField.IsUnramifiedEverywhere.artinMap_spec` prescribes at the class of `v`, stated
without reference to `NumberField.IsUnramifiedEverywhere.artinMap`. -/
theorem coe_localArtinAdicCompletionUnits_mk_uniformizer_eq_arithFrobAt
    [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [Fintype (decompositionGroup K L w)]
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    {π : v.adicCompletion K} (hv : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ))
    {u : (w.adicCompletion L)ˣ}
    (hu : (u : w.adicCompletion L) = adicCompletionComap K L v w π)
    (P : HeightOneSpectrum (𝓞 L)) (hP : P.asIdeal.under (𝓞 K) = v.asIdeal) :
    (((localArtinAdicCompletionUnits v w h (mem_zpowers_arithFrobDecomposition v w h)
        (TateH0.mk _ (smul_ofMul_unit_of_eq_adicCompletionComap v w hu
          (arithFrobDecomposition (K := K) w)))).toMul : decompositionGroup K L w) : L ≃ₐ[K] L)
      = arithFrobAt (𝓞 K) Gal(L/K) P.asIdeal := by
  rw [coe_localArtinAdicCompletionUnits_mk_uniformizer_arithFrob v w h hv hu]
  exact arithFrobAt_eq_of_under_eq w P
    (((Ideal.over_def w.asIdeal v.asIdeal).symm).trans hP.symm)

end LocalArtinComputation

end NumberField
