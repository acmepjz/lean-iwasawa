/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.InvariantRestriction
public import Iwasawalib.NumberTheory.LocalCFT.ResidueFrobenius

@[expose] public section

/-!
# The local Artin map sends a uniformiser to the arithmetic Frobenius

`Iwasawalib/NumberTheory/LocalCFT/InvariantRestriction.lean` builds, at an unramified finite
place `w | v` of a finite Galois extension of number fields, the local Artin isomorphism
`NumberField.localArtinAdicCompletionUnits : Ĥ⁰(D_w, L_w^×) ≃+ Additive D_w`, and proves that
it sends the class of a uniformiser of `K_v` to the chosen generator `σ` of `D_w`
(`NumberField.localArtinAdicCompletionUnits_mk_uniformizer`).  That statement is about an
*arbitrary* generator, so it does not yet identify the value with a Frobenius element.

`Iwasawalib/NumberTheory/LocalCFT/ResidueFrobenius.lean` supplies the missing input: at an
unramified place Mathlib's arithmetic Frobenius `arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal` *is* a
generator of `D_w` (`NumberField.mem_zpowers_arithFrobDecomposition`).  Taking it as the
generator, the local Artin map sends the class of a uniformiser of `K_v` to it:
`NumberField.localArtinAdicCompletionUnits_mk_uniformizer_arithFrob`, and in the coerced form
`NumberField.coe_localArtinAdicCompletionUnits_mk_uniformizer_arithFrob` the value is literally
the term `arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal` appearing on the right-hand side of
`NumberField.IsUnramifiedEverywhere.artinMap_spec`.

## Scope

This is the *local* half of `NumberField.IsUnramifiedEverywhere.artinMap_spec`.  That theorem
also needs the global Artin map `NumberField.IsUnramifiedEverywhere.artinMap`, which is still a
`sorry`, and the comparison of its value on the ideal class of `p` with the local Artin map at a
place above `p`; neither is done here, and nothing below mentions `artinMap`.

## Main statements

* `NumberField.localArtinAdicCompletionUnits_mk_uniformizer_arithFrob`
* `NumberField.coe_localArtinAdicCompletionUnits_mk_uniformizer_arithFrob`
* `NumberField.exists_uniformizer_unit`: the hypotheses of the two statements above are
  satisfiable, so they are not vacuous.
-/

noncomputable section

namespace NumberField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero LocalCFT CyclicTate

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal] [Fintype (decompositionGroup K L w)]

attribute [local instance] decompositionIntegersMulSemiringAction
  IsLocalRing.residueMulSemiringAction Units.mulDistribMulActionRight

/-- **The local Artin map at an unramified finite place sends the class of a uniformiser of
`K_v` to the arithmetic Frobenius `arithFrobAt` of `w`.** -/
theorem localArtinAdicCompletionUnits_mk_uniformizer_arithFrob
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    {π : v.adicCompletion K} (hv : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ))
    {u : (w.adicCompletion L)ˣ}
    (hu : (u : w.adicCompletion L) = adicCompletionComap K L v w π) :
    localArtinAdicCompletionUnits v w h (mem_zpowers_arithFrobDecomposition v w h)
        (TateH0.mk _ (smul_ofMul_unit_of_eq_adicCompletionComap v w hu
          (arithFrobDecomposition (K := K) w)))
      = Additive.ofMul (arithFrobDecomposition (K := K) w) :=
  localArtinAdicCompletionUnits_mk_uniformizer v w h _ hv hu


omit [IsGalois K L] [Fintype (decompositionGroup K L w)] in
/-- There is a uniformiser of `K_v`, and its image in `L_w` is a unit: the hypotheses of
`NumberField.localArtinAdicCompletionUnits_mk_uniformizer_arithFrob` are satisfiable. -/
theorem exists_uniformizer_unit :
    ∃ (π : v.adicCompletion K) (u : (w.adicCompletion L)ˣ),
      (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ) ∧
        (u : w.adicCompletion L) = adicCompletionComap K L v w π := by
  obtain ⟨π, hπ⟩ := valuedAdicCompletion_surjective (K := K) v (exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact exp_ne_zero hπ.symm
  have h0 : adicCompletionComap K L v w π ≠ 0 :=
    fun hc ↦ hπ0 ((adicCompletionComap K L v w).injective (by rw [hc, map_zero]))
  exact ⟨π, Units.mk0 _ h0, hπ, rfl⟩

/-- **The local Artin map at an unramified finite place sends the class of a uniformiser of `K_v`
to `arithFrobAt`**, in the shape that
`NumberField.IsUnramifiedEverywhere.artinMap_spec` consumes: the underlying automorphism of
`L / K` is literally `arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal`. -/
theorem coe_localArtinAdicCompletionUnits_mk_uniformizer_arithFrob
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    {π : v.adicCompletion K} (hv : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ))
    {u : (w.adicCompletion L)ˣ}
    (hu : (u : w.adicCompletion L) = adicCompletionComap K L v w π) :
    (((localArtinAdicCompletionUnits v w h (mem_zpowers_arithFrobDecomposition v w h)
        (TateH0.mk _ (smul_ofMul_unit_of_eq_adicCompletionComap v w hu
          (arithFrobDecomposition (K := K) w)))).toMul : decompositionGroup K L w) : L ≃ₐ[K] L)
      = arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal := by
  rw [localArtinAdicCompletionUnits_mk_uniformizer_arithFrob v w h hv hu]
  rfl

end NumberField
