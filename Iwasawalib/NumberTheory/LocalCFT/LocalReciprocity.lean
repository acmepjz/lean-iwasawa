/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.ArtinFrobenius
public import Iwasawalib.NumberTheory.GlobalCFT.IdeleFrobenius

@[expose] public noncomputable section

/-!
# The normalized unramified local reciprocity homomorphism

This file packages the existing normalized local Artin equivalence as a homomorphism from the
base completion units to the decomposition group.  Its normalization is arithmetic: an element
of order one maps to arithmetic Frobenius, with no inversion.

This is only the local package.  It contains no global fundamental class, idele-class
reciprocity map, or local-global compatibility assertion.
-/

namespace NumberField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero LocalCFT CyclicTate

variable {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [IsGalois F L]
variable (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal] [Fintype (decompositionGroup F L w)]

attribute [local instance] decompositionIntegersMulSemiringAction
  IsLocalRing.residueMulSemiringAction Units.mulDistribMulActionRight

/-- The multiplicative map on completion units induced by `F_v -> L_w`. -/
def localCompletionUnitsHom :
    (v.adicCompletion F)ˣ →* (w.adicCompletion L)ˣ :=
  Units.map (adicCompletionComap F L v w).toMonoidHom

/-- The image of a base completion unit, regarded as an element fixed by arithmetic Frobenius
in the additive Galois module of `L_w`-units. -/
def localCompletionUnitsInvariantHom :
    Additive (v.adicCompletion F)ˣ →+
      kerSub (decompositionGroup F L w) (Additive (w.adicCompletion L)ˣ)
        (arithFrobDecomposition (K := F) w) :=
  AddMonoidHom.codRestrict
    (MonoidHom.toAdditive (localCompletionUnitsHom v w)) _ fun x =>
      mem_kerSub.2
        (smul_ofMul_unit_of_eq_adicCompletionComap v w
          (π := x.toMul) (u := localCompletionUnitsHom v w x.toMul) rfl
          (arithFrobDecomposition (K := F) w))

/-- The canonical class of a base completion unit in local Tate cohomology. -/
def localTateClassHom
    (_h : v.asIdeal.ramificationIdx' w.asIdeal = 1) :
    Additive (v.adicCompletion F)ˣ →+
      TateH0 (decompositionGroup F L w)
        (Additive (w.adicCompletion L)ˣ)
        (arithFrobDecomposition (K := F) w) :=
  (QuotientAddGroup.mk' _).comp (localCompletionUnitsInvariantHom v w)

/-- A base completion unit maps to the Tate class of its image in the extension completion. -/
@[simp] theorem localTateClassHom_apply
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (x : (v.adicCompletion F)ˣ) :
    localTateClassHom v w h (Additive.ofMul x) =
      TateH0.mk (arithFrobDecomposition (K := F) w)
        (smul_ofMul_unit_of_eq_adicCompletionComap v w
          (π := x) (u := localCompletionUnitsHom v w x) rfl
          (arithFrobDecomposition (K := F) w)) := by
  rfl

/-- The normalized unramified local Artin homomorphism `F_v^x -> D_w`, obtained from the
canonical Tate class and the existing local Artin equivalence. -/
def localArtinHom
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1) :
    (v.adicCompletion F)ˣ →* decompositionGroup F L w :=
  MonoidHom.toAdditive.symm
    ((localArtinAdicCompletionUnits v w h
        (mem_zpowers_arithFrobDecomposition v w h)).toAddMonoidHom.comp
      (localTateClassHom v w h))

/-- The normalized local Artin homomorphism sends every element to arithmetic Frobenius raised
to its normalized order.  In particular, the exponent is `ordCompletion`, not its negative. -/
@[simp] theorem localArtinHom_apply
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (x : (v.adicCompletion F)ˣ) :
    localArtinHom v w h x =
      arithFrobDecomposition (K := F) w ^
        v.ordCompletion F (x : v.adicCompletion F) := by
  rw [localArtinHom]
  change (localArtinAdicCompletionUnits v w h
      (mem_zpowers_arithFrobDecomposition v w h)
      (localTateClassHom v w h (Additive.ofMul x))).toMul = _
  apply Additive.toMul.injective
  change localArtinAdicCompletionUnits v w h
      (mem_zpowers_arithFrobDecomposition v w h)
      (localTateClassHom v w h (Additive.ofMul x)) = Additive.ofMul _
  rw [localTateClassHom_apply, localArtinAdicCompletionUnits,
    LocalCFT.localArtinEquiv_mk]
  have hval : LocalCFT.valZ (localCompletionUnitsHom v w x) =
      Multiplicative.ofAdd (WithZero.log (Valued.v (x : v.adicCompletion F))) := by
    apply WithZero.coe_injective
    rw [LocalCFT.coe_valZ]
    change (Valued.v (adicCompletionComap F L v w (x : v.adicCompletion F)) : ℤᵐ⁰) = _
    rw [valued_adicCompletionComap_of_ramificationIdx_eq_one F L v w h,
      ← WithZero.exp_eq_coe_ofAdd]
    exact (WithZero.exp_log ((Valuation.ne_zero_iff _).2 x.ne_zero)).symm
  simp only [toMul_ofMul]
  rw [LocalCFT.ordZ, HeightOneSpectrum.ordCompletion, hval,
    toAdd_ofAdd]

/-- The normalized unramified local Artin homomorphism is surjective. -/
theorem localArtinHom_surjective
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1) :
    Function.Surjective (localArtinHom v w h) := by
  intro d
  obtain ⟨n, hn⟩ := exists_pow_eq_arithFrobDecomposition v w h d
  obtain ⟨π, _, hπ, _⟩ := exists_uniformizer_unit v w
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact exp_ne_zero hπ.symm
  let x : (v.adicCompletion F)ˣ := Units.mk0 π hπ0
  have hx : v.ordCompletion F (x : v.adicCompletion F) = 1 := by
    show -WithZero.log (Valued.v π) = 1
    rw [hπ, WithZero.log_exp, neg_neg]
  refine ⟨x ^ n, ?_⟩
  rw [map_pow, localArtinHom_apply, hx, zpow_one, hn]

/-- An element of normalized order one maps, after inclusion in `Gal(L/F)`, to arithmetic
Frobenius at `w`. -/
theorem coe_localArtinHom_uniformizer
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (x : (v.adicCompletion F)ˣ)
    (hx : v.ordCompletion F (x : v.adicCompletion F) = 1) :
    ((localArtinHom v w h x : decompositionGroup F L w) : L ≃ₐ[F] L) =
      arithFrobAt (𝓞 F) (L ≃ₐ[F] L) w.asIdeal := by
  rw [localArtinHom_apply, hx, zpow_one]
  rfl

/-- A local unit of normalized order zero lies in the kernel of the normalized unramified local
Artin homomorphism. -/
theorem localArtinHom_unit
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (x : (v.adicCompletion F)ˣ)
    (hx : v.ordCompletion F (x : v.adicCompletion F) = 0) :
    localArtinHom v w h x = 1 := by
  rw [localArtinHom_apply, hx, zpow_zero]

end NumberField
