/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.PlaceFibreStabilizer
public import Iwasawalib.NumberTheory.CFT.TateTransport
public import Iwasawalib.NumberTheory.CFT.SIdeleSemilocal
public import Iwasawalib.NumberTheory.CFT.SecondInequality
public import Iwasawalib.NumberTheory.LocalCFT.LocalHerbrand
public import Iwasawalib.NumberTheory.LocalCFT.Unramified

@[expose] public section

/-!
# The semilocal integral units are an induced module

Let `L / K` be a Galois extension of number fields and `v` a finite place of `K`.  The group

`∏_{w ∣ v} O_w^×`  (`NumberField.localProductIntegerUnits K L v`)

is the factor of the `S`-ideles at a place `v ∉ S`, and the computation of `h(𝕀_{L,S})` in
`Iwasawalib/NumberTheory/CFT/SIdeleHerbrand.lean` needs its Tate cohomology to **vanish**, not
merely to have Herbrand quotient `1`: the product over the places outside `S` is infinite.

This file supplies exactly that.  The family `w ↦ O_w` over the fibre `{w ∣ v}` is an
`EquivariantFamily`, so `∏_{w ∣ v} O_w` is the module induced from `O_{w₀}` for the
decomposition group of any `w₀ ∣ v`, and Shapiro's lemma
(`EquivariantFamily.subsingleton_tateH0_piUnits`) transports the local vanishing supplied by
`Iwasawalib/NumberTheory/LocalCFT/Unramified.lean` to the semilocal group.

The local vanishing is stated there for `NumberField.decompositionGroup K L w₀`, and Shapiro's
lemma produces a statement for `MulAction.stabilizer (L ≃ₐ[K] L) w₀`.  These are the same
subgroup of `Gal(L/K)` (`NumberField.stabilizer_placesOver_eq`) but not the same Lean type, and
the passage between them is `CyclicTate.subsingleton_tateH0_of_groupEquiv`.

## Main definitions

* `NumberField.pushAdicIntegers` : the isomorphism `O_w ≃+* O_{w'}` attached to `σ` with
  `σ • w = w'`.
* `NumberField.localIntegerFamily` : the family `w ↦ O_w` over `{w ∣ v}` as an
  `EquivariantFamily`.
* `NumberField.localProductIntegersEquivPi` : `∏_{w ∣ v} O_w` in its two descriptions.

## Main statements

* `NumberField.subsingleton_tateH0_localProductIntegerUnits`,
  `NumberField.subsingleton_tateH1_localProductIntegerUnits` : **the vanishing**, at an
  unramified place.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MulAction CyclicTate WithZero
open scoped WithZero

namespace NumberField

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]

/-! ## The isomorphism of local integers attached to a Galois element -/

omit [NumberField K] in
/-- If `σ` carries `w` to `w'`, then `σ` carries the `w`-adic valuation to the `w'`-adic
valuation. -/
theorem valuation_of_push_smul {σ : L ≃ₐ[K] L} {w w' : HeightOneSpectrum (𝓞 L)}
    (h : σ • w = w') (y : L) : w'.valuation L (σ y) = w.valuation L y := by
  subst h
  rw [valuation_inv_smul σ (σ • w) y, inv_smul_smul]

variable (σ : L ≃ₐ[K] L) {w w' : HeightOneSpectrum (𝓞 L)}

omit [NumberField K] in
/-- The isomorphism `L_w ≃+* L_{w'}` attached to `σ : Gal(L/K)` with `σ • w = w'`. -/
def pushAdicCompletion (h : σ • w = w') : w.adicCompletion L ≃+* w'.adicCompletion L :=
  adicCompletionCongr ((σ : L ≃ₐ[K] L) : L ≃+* L) w w' (valuation_of_push_smul h)

omit [NumberField K] in
theorem valued_pushAdicCompletion (h : σ • w = w') (z : w.adicCompletion L) :
    (Valued.v (pushAdicCompletion σ h z) : ℤᵐ⁰) = Valued.v z :=
  valued_adicCompletionCongr _ _ _ _ z

omit [NumberField K] in
theorem valued_pushAdicCompletion_symm (h : σ • w = w') (z : w'.adicCompletion L) :
    (Valued.v ((pushAdicCompletion σ h).symm z) : ℤᵐ⁰) = Valued.v z := by
  conv_rhs => rw [← (pushAdicCompletion σ h).apply_symm_apply z]
  exact (valued_pushAdicCompletion σ h _).symm

omit [NumberField K] in
/-- **The isomorphism `O_w ≃+* O_{w'}` attached to `σ : Gal(L/K)` with `σ • w = w'`.**  It is
the restriction of `NumberField.pushAdicCompletion`, which preserves the valuation. -/
def pushAdicIntegers (h : σ • w = w') :
    (w.adicCompletionIntegers L) ≃+* (w'.adicCompletionIntegers L) where
  toFun a := ⟨pushAdicCompletion σ h (a : w.adicCompletion L), by
    rw [mem_adicCompletionIntegers, valued_pushAdicCompletion, ← mem_adicCompletionIntegers]
    exact a.2⟩
  invFun b := ⟨(pushAdicCompletion σ h).symm (b : w'.adicCompletion L), by
    rw [mem_adicCompletionIntegers, valued_pushAdicCompletion_symm, ← mem_adicCompletionIntegers]
    exact b.2⟩
  left_inv a := Subtype.ext ((pushAdicCompletion σ h).symm_apply_apply _)
  right_inv b := Subtype.ext ((pushAdicCompletion σ h).apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul (pushAdicCompletion σ h) _ _)
  map_add' a b := Subtype.ext (map_add (pushAdicCompletion σ h) _ _)

omit [NumberField K] in
@[simp]
theorem coe_pushAdicIntegers (h : σ • w = w') (a : w.adicCompletionIntegers L) :
    (pushAdicIntegers σ h a : w'.adicCompletion L)
      = pushAdicCompletion σ h (a : w.adicCompletion L) := rfl

/-! ## The family of local integers over the fibre -/

variable (K L)

/-- **The family `w ↦ O_w` over the places above `v`, as an `EquivariantFamily`.**  This is what
makes `∏_{w ∣ v} O_w` an induced module for the decomposition group, so that Shapiro's lemma
applies to it. -/
def localIntegerFamily (v : HeightOneSpectrum (𝓞 K)) :
    EquivariantFamily (L ≃ₐ[K] L) ↥(placesOver K L v)
      (fun w ↦ ((w : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L)) where
  push σ h := pushAdicIntegers σ (congrArg Subtype.val h)
  push_one _ _ := Subtype.ext (adicCompletionCongr_id _ _ _ (fun _ ↦ rfl) _)
  push_mul _ _ h h' h'' _ := Subtype.ext
    (adicCompletionCongr_comp _ _ _ _ _ (valuation_of_push_smul (congrArg Subtype.val h))
      (valuation_of_push_smul (congrArg Subtype.val h'))
      (valuation_of_push_smul (congrArg Subtype.val h'')) _)

end NumberField

/-! ## `∏_{w ∣ v} O_w` in its two descriptions -/

namespace NumberField

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]

attribute [local instance] Units.mulDistribMulActionRight

variable (K L)

/-- The subring `∏_{w ∣ v} O_w` of `∏_{w ∣ v} L_w` is the plain product of the rings `O_w`. -/
def localProductIntegersEquivPi (v : HeightOneSpectrum (𝓞 K)) :
    (localProductIntegers K L v)
      ≃+* (∀ w : placesOver K L v, ((w : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L)) where
  toFun x w := ⟨(x : LocalProduct K L v) w, x.2 w⟩
  invFun y := ⟨fun w ↦ (y w : (w : HeightOneSpectrum (𝓞 L)).adicCompletion L), fun w ↦ (y w).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- **`∏_{w ∣ v} O_w^×` in its two descriptions**: as the subgroup of integral semilocal units
inside `(∏_{w ∣ v} L_w)^×`, and as the unit group of the product ring `∏_{w ∣ v} O_w`. -/
def localProductIntegerUnitsEquivPiUnits (v : HeightOneSpectrum (𝓞 K)) :
    (localProductIntegerUnits K L v)
      ≃* (∀ w : placesOver K L v, ((w : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L))ˣ :=
  (Submonoid.unitsEquivUnitsType _).trans
    (Units.mapEquiv (localProductIntegersEquivPi K L v).toMulEquiv)

variable {K L}

theorem coe_localProductIntegerUnitsEquivPiUnits (v : HeightOneSpectrum (𝓞 K))
    (x : localProductIntegerUnits K L v) (w : placesOver K L v) :
    ((localProductIntegerUnitsEquivPiUnits K L v x : ∀ w : placesOver K L v,
        ((w : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L)) w
        : (w : HeightOneSpectrum (𝓞 L)).adicCompletion L)
      = ((x : (LocalProduct K L v)ˣ) : LocalProduct K L v) w := rfl

end NumberField

/-! ## The action of `Gal(L/K)` on the two descriptions agrees -/

namespace NumberField

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]

attribute [local instance] Units.mulDistribMulActionRight

variable (K L)

/-- The `Gal(L/K)`-action on `∏_{w ∣ v} O_w` coming from the family. -/
@[instance_reducible] def localIntegerPiAction (v : HeightOneSpectrum (𝓞 K)) :
    MulSemiringAction (L ≃ₐ[K] L)
      (∀ w : placesOver K L v, ((w : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L)) :=
  (localIntegerFamily K L v).piMulSemiringAction

/-- The action of the stabiliser of `w₀` on `O_{w₀}` coming from the family. -/
@[instance_reducible] def localIntegerStabilizerAction {v : HeightOneSpectrum (𝓞 K)}
    (w₀ : placesOver K L v) :
    MulSemiringAction (stabilizer (L ≃ₐ[K] L) w₀)
      ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L) :=
  (localIntegerFamily K L v).stabilizerMulSemiringAction w₀

attribute [local instance] localIntegerPiAction localIntegerStabilizerAction

variable {K L}

theorem localIntegerFamily_isPiAction (v : HeightOneSpectrum (𝓞 K)) :
    (localIntegerFamily K L v).IsPiAction := fun _ _ _ ↦ rfl

theorem localIntegerFamily_isStabilizerAction {v : HeightOneSpectrum (𝓞 K)}
    (w₀ : placesOver K L v) :
    (localIntegerFamily K L v).IsStabilizerAction (w₀ := w₀) := fun _ _ ↦ rfl

/-- **The identification of the two descriptions of `∏_{w ∣ v} O_w^×` is `Gal(L/K)`-equivariant.**
-/
theorem localProductIntegerUnitsEquivPiUnits_smul (v : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L) (x : localProductIntegerUnits K L v) :
    localProductIntegerUnitsEquivPiUnits K L v (σ • x)
      = σ • localProductIntegerUnitsEquivPiUnits K L v x :=
  Units.ext (funext fun w ↦ Subtype.ext rfl)

end NumberField

/-! ## The vanishing of the Tate cohomology of `∏_{w ∣ v} O_w^×` -/

namespace NumberField

open LocalCFT

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]

attribute [local instance] Units.mulDistribMulActionRight localIntegerPiAction
  localIntegerStabilizerAction decompositionIntegersMulSemiringAction
  IsLocalRing.residueMulSemiringAction

/-- The action of the decomposition group on `O_w`, written with `adicCompletionIntegers`
rather than with `LocalCFT.integers`.  The two types are definitionally equal; this alias
exists so that instance search finds the action on the form of the ring that
`NumberField.localIntegerFamily` produces. -/
@[instance_reducible] def adicIntegersDecompositionAction (w : HeightOneSpectrum (𝓞 L)) :
    MulSemiringAction (decompositionGroup K L w) (w.adicCompletionIntegers L) :=
  decompositionIntegersMulSemiringAction w

attribute [local instance] adicIntegersDecompositionAction

variable [IsGalois K L] {v : HeightOneSpectrum (𝓞 K)} (w₀ : placesOver K L v)
  [Fintype (stabilizer (L ≃ₐ[K] L) w₀)]
  [Fintype (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))]

/-- **`Ĥ⁰(Gal(L/K), ∏_{w ∣ v} O_w^×) = 0` at an unramified place.**  Shapiro's lemma reduces it
to `Ĥ⁰(D_{w₀}, O_{w₀}^×) = 0`, which is
`NumberField.subsingleton_tateH0_units`. -/
theorem subsingleton_tateH0_localProductIntegerUnits
    (hram : v.asIdeal.ramificationIdx' (w₀ : HeightOneSpectrum (𝓞 L)).asIdeal = 1)
    {σ : L ≃ₐ[K] L} (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    {τ : decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L))}
    (hτ : ∀ d : decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)),
      d ∈ Subgroup.zpowers τ) :
    Subsingleton (TateH0 (L ≃ₐ[K] L) (Additive (localProductIntegerUnits K L v)) σ) := by
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  haveI : (w₀ : HeightOneSpectrum (𝓞 L)).asIdeal.LiesOver v.asIdeal := ⟨w₀.2.symm⟩
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  set e := MulEquiv.subgroupCongr (stabilizer_placesOver_eq w₀).symm with he_def
  haveI hloc : Subsingleton (TateH0 (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))
      (Additive ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L)ˣ) τ) :=
    subsingleton_tateH0_units v (w₀ : HeightOneSpectrum (𝓞 L)) hram hτ
  haveI hstab : Subsingleton (TateH0 (stabilizer (L ≃ₐ[K] L) w₀)
      (Additive ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L)ˣ) (e τ)) :=
    subsingleton_tateH0_of_groupEquiv e (fun _ _ ↦ rfl)
  have hτ' : ∀ d : stabilizer (L ≃ₐ[K] L) w₀, d ∈ Subgroup.zpowers (e τ) := fun d ↦ by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hτ (e.symm d))
    refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
    rw [← map_zpow e τ m, hm, e.apply_symm_apply]
  haveI := (localIntegerFamily K L v).subsingleton_tateH0_piUnits
    (localIntegerFamily_isStabilizerAction w₀) (localIntegerFamily_isPiAction v) hσ hτ'
  exact subsingleton_tateH0_of_moduleEquiv (localProductIntegerUnitsEquivPiUnits K L v).symm
    (fun g a ↦ (localProductIntegerUnitsEquivPiUnits K L v).injective (by
      rw [MulEquiv.apply_symm_apply, localProductIntegerUnitsEquivPiUnits_smul,
        MulEquiv.apply_symm_apply]))

/-- **`Ĥ¹(Gal(L/K), ∏_{w ∣ v} O_w^×) = 0` at an unramified place.** -/
theorem subsingleton_tateH1_localProductIntegerUnits
    (hram : v.asIdeal.ramificationIdx' (w₀ : HeightOneSpectrum (𝓞 L)).asIdeal = 1)
    {σ : L ≃ₐ[K] L} (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    {τ : decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L))}
    (hτ : ∀ d : decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)),
      d ∈ Subgroup.zpowers τ) :
    Subsingleton (TateH1 (L ≃ₐ[K] L) (Additive (localProductIntegerUnits K L v)) σ) := by
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  haveI : (w₀ : HeightOneSpectrum (𝓞 L)).asIdeal.LiesOver v.asIdeal := ⟨w₀.2.symm⟩
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  set e := MulEquiv.subgroupCongr (stabilizer_placesOver_eq w₀).symm with he_def
  haveI hloc : Subsingleton (TateH1 (decompositionGroup K L (w₀ : HeightOneSpectrum (𝓞 L)))
      (Additive ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L)ˣ) τ) :=
    subsingleton_tateH1_units v (w₀ : HeightOneSpectrum (𝓞 L)) hram hτ
  haveI hstab : Subsingleton (TateH1 (stabilizer (L ≃ₐ[K] L) w₀)
      (Additive ((w₀ : HeightOneSpectrum (𝓞 L)).adicCompletionIntegers L)ˣ) (e τ)) :=
    subsingleton_tateH1_of_groupEquiv e (fun _ _ ↦ rfl)
  have hτ' : ∀ d : stabilizer (L ≃ₐ[K] L) w₀, d ∈ Subgroup.zpowers (e τ) := fun d ↦ by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hτ (e.symm d))
    refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
    rw [← map_zpow e τ m, hm, e.apply_symm_apply]
  haveI := (localIntegerFamily K L v).subsingleton_tateH1_piUnits
    (localIntegerFamily_isStabilizerAction w₀) (localIntegerFamily_isPiAction v) hσ hτ'
  exact subsingleton_tateH1_of_moduleEquiv (localProductIntegerUnitsEquivPiUnits K L v).symm
    (fun g a ↦ (localProductIntegerUnitsEquivPiUnits K L v).injective (by
      rw [MulEquiv.apply_symm_apply, localProductIntegerUnitsEquivPiUnits_smul,
        MulEquiv.apply_symm_apply]))

end NumberField
