/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.FiniteIdeleVanishing
public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

/-!
# `H¹(Gal(L/K), 𝕀_L) = 0`: the local input at almost every place

`Iwasawalib/GroupCohomology/FiniteIdeleVanishing.lean` reduces `H¹(Gal(L/K), 𝕀_L) = 0` to one
statement about almost every finite place `v` of `K`
(`NumberField.IsUnramifiedAlmostEverywhere`): a 1-cocycle with values in the integral units
`(∏_{w ∣ v} O_w)^×` must be trivialised *inside* `(∏_{w ∣ v} O_w)^×`.  This file proves it.

The route avoids an induced-module argument with an integrality constraint.  `H¹` of
`(∏_{w ∣ v} L_w)^×` already vanishes at *every* place, by Shapiro plus local Hilbert 90
(`NumberField.isZero_H1_repLocalProductUnits`), so the cocycle is a coboundary `g • b / b`; the
only issue is that the witness `b` need not be integral.  Its valuation, however, is forced:

* `g • b / b` is an integral unit, so `Valued.v (b w)` is constant along the `Gal(L/K)`-orbit of
  the places above `v`, which is all of them;
* at an **unramified** place a uniformizer `π` of `K` at `v` has valuation `exp (-1)` in *every*
  `L_w` (`IsDedekindDomain.HeightOneSpectrum.valuation_liesOver` with `e(w|v) = 1`), and its
  diagonal image in `∏_{w ∣ v} L_w` is `Gal(L/K)`-invariant.

So `b` may be rescaled by an invariant power of `π` to a unit of `∏_{w ∣ v} O_w` without
changing the coboundary.  Finally all but finitely many places are unramified, because a
ramified prime divides the different ideal
(`Mathlib`'s `not_dvd_differentIdeal_iff`, `Ideal.finite_factors`).

## Main statements

* `NumberField.diagLocalProduct`: the diagonal `K → ∏_{w ∣ v} L_w`, and
  `NumberField.smul_diagLocalProduct`: it is `Gal(L/K)`-invariant.
* `NumberField.exists_integral_trivialisation`: the local input at an unramified place.
* `NumberField.eventually_ramificationIdx_eq_one`: almost every place is unramified.
* `NumberField.isUnramifiedAlmostEverywhere`: `NumberField.IsUnramifiedAlmostEverywhere K L`.
* `NumberField.isZero_H1_repIdele`, `NumberField.isZero_H1_finiteIdele`:
  `H¹(Gal(L/K), 𝕀_L) = 0`, unconditionally.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Filter WithZero
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.galIdeleMulDistribMulAction NumberField.galIdeleClassMulDistribMulAction

namespace NumberField

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-! ## Valuations on the semilocal factor -/

variable (K L) in
/-- The diagonal embedding `K → ∏_{w ∣ v} L_w`. -/
def diagLocalProduct (v : HeightOneSpectrum (𝓞 K)) : K →+* LocalProduct K L v :=
  RingHom.pi fun w ↦
    (algebraMap L ((w : HeightOneSpectrum (𝓞 L)).adicCompletion L)).comp (algebraMap K L)

theorem diagLocalProduct_apply {v : HeightOneSpectrum (𝓞 K)} (k : K) (w : placesOver K L v) :
    diagLocalProduct K L v k w
      = algebraMap L ((w : HeightOneSpectrum (𝓞 L)).adicCompletion L) (algebraMap K L k) := rfl

/-- **The diagonal image of `K` is `Gal(L/K)`-invariant.** -/
theorem smul_diagLocalProduct {v : HeightOneSpectrum (𝓞 K)} (σ : L ≃ₐ[K] L) (k : K) :
    σ • diagLocalProduct K L v k = diagLocalProduct K L v k := by
  funext w
  rw [localProduct_smul_apply, diagLocalProduct_apply, diagLocalProduct_apply]
  show adicCompletionCongr ((σ : L ≃ₐ[K] L) : L ≃+* L) _ _ _
      ((algebraMap K L k : L) : (invSmulPlace σ w : HeightOneSpectrum (𝓞 L)).adicCompletion L)
    = ((algebraMap K L k : L) : (w : HeightOneSpectrum (𝓞 L)).adicCompletion L)
  rw [adicCompletionCongr_coe,
    show ((σ : L ≃ₐ[K] L) : L ≃+* L) (algebraMap K L k) = algebraMap K L k from σ.commutes k]

/-- The valuation of the diagonal image of `k : K` at a place `w ∣ v` is `v(k)^{e(w|v)}`. -/
theorem valued_diagLocalProduct {v : HeightOneSpectrum (𝓞 K)} (k : K) (w : placesOver K L v) :
    (Valued.v (diagLocalProduct K L v k w) : ℤᵐ⁰)
      = (w : HeightOneSpectrum (𝓞 L)).valuation L (algebraMap K L k) :=
  valuedAdicCompletion_eq_valuation' (v := (w : HeightOneSpectrum (𝓞 L))) _

/-- The valuation of the `w`-component of `σ • x` is the valuation of the `σ⁻¹ • w`-component
of `x`. -/
theorem valued_localProduct_smul {v : HeightOneSpectrum (𝓞 K)} (σ : L ≃ₐ[K] L)
    (x : LocalProduct K L v) (w : placesOver K L v) :
    (Valued.v ((σ • x) w) : ℤᵐ⁰) = Valued.v (x (invSmulPlace σ w)) := by
  rw [localProduct_smul_apply]
  exact valued_adicCompletionCongr _ _ _ _ _

/-- The components of a unit of `∏_{w ∣ v} L_w` have nonzero valuation. -/
theorem valued_units_ne_zero {v : HeightOneSpectrum (𝓞 K)} (u : (LocalProduct K L v)ˣ)
    (w : placesOver K L v) : (Valued.v ((u : LocalProduct K L v) w) : ℤᵐ⁰) ≠ 0 := by
  intro h
  have h1 : ((u : LocalProduct K L v) w) * ((↑u⁻¹ : LocalProduct K L v) w) = 1 :=
    congrFun u.mul_inv w
  have := congrArg (fun z ↦ (Valued.v z : ℤᵐ⁰)) h1
  simp only [map_mul, map_one, h, zero_mul] at this
  exact zero_ne_one this

/-- An integral unit has valuation one at every place. -/
theorem valued_eq_one_of_mem_localProductIntegerUnits {v : HeightOneSpectrum (𝓞 K)}
    {u : (LocalProduct K L v)ˣ} (hu : u ∈ localProductIntegerUnits K L v)
    (w : placesOver K L v) : (Valued.v ((u : LocalProduct K L v) w) : ℤᵐ⁰) = 1 := by
  have h1 : (Valued.v ((u : LocalProduct K L v) w) : ℤᵐ⁰) ≤ 1 := hu.1 w
  have h2 : (Valued.v ((↑u⁻¹ : LocalProduct K L v) w) : ℤᵐ⁰) ≤ 1 := hu.2 w
  have h3 : ((u : LocalProduct K L v) w) * ((↑u⁻¹ : LocalProduct K L v) w) = 1 :=
    congrFun u.mul_inv w
  have h4 : (Valued.v ((u : LocalProduct K L v) w) : ℤᵐ⁰)
      * (Valued.v ((↑u⁻¹ : LocalProduct K L v) w) : ℤᵐ⁰) = 1 := by
    rw [← map_mul, h3, map_one]
  refine le_antisymm h1 ?_
  calc (1 : ℤᵐ⁰) = _ * _ := h4.symm
    _ ≤ (Valued.v ((u : LocalProduct K L v) w) : ℤᵐ⁰) * 1 := by gcongr
    _ = _ := mul_one _


/-- A unit of `∏_{w ∣ v} L_w` all of whose components have valuation one is an integral
unit. -/
theorem mem_localProductIntegerUnits_of_valued_eq_one {v : HeightOneSpectrum (𝓞 K)}
    {u : (LocalProduct K L v)ˣ}
    (hu : ∀ w : placesOver K L v, (Valued.v ((u : LocalProduct K L v) w) : ℤᵐ⁰) = 1) :
    u ∈ localProductIntegerUnits K L v := by
  have hinv : ∀ w : placesOver K L v,
      (Valued.v ((↑u⁻¹ : LocalProduct K L v) w) : ℤᵐ⁰) = 1 := by
    intro w
    have h3 : ((u : LocalProduct K L v) w) * ((↑u⁻¹ : LocalProduct K L v) w) = 1 :=
      congrFun u.mul_inv w
    have h4 := congrArg (fun z ↦ (Valued.v z : ℤᵐ⁰)) h3
    simp only [map_mul, map_one, hu w, one_mul] at h4
    exact h4
  exact ⟨fun w ↦ le_of_eq (hu w), fun w ↦ le_of_eq (hinv w)⟩

/-! ## The local input at an unramified place -/

variable [IsGalois K L]

/-- **The local input of `H¹(Gal(L/K), 𝕀_L) = 0` at an unramified place.**  If every place of
`L` above `v` is unramified, then a 1-cocycle with values in `(∏_{w ∣ v} O_w)^×` is trivialised
by an element of `(∏_{w ∣ v} O_w)^×`. -/
theorem exists_integral_trivialisation (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), w ∈ placesOver K L v →
      v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (f : (L ≃ₐ[K] L) → (LocalProduct K L v)ˣ)
    (hf : groupCohomology.IsMulCocycle₁ f)
    (hint : ∀ g, f g ∈ localProductIntegerUnits K L v) :
    ∃ b ∈ localProductIntegerUnits K L v, ∀ g, g • b / b = f g := by
  obtain ⟨b, hb⟩ := groupCohomology.isZero_H1_ofMulDistribMulAction_iff.1
    (isZero_H1_repLocalProductUnits K L v) f hf
  obtain ⟨w₀, hw₀⟩ := nonempty_placesOver (K := K) (L := L) v
  -- The valuation of `b` is the same at every place above `v`.
  have hbv : ∀ w : placesOver K L v,
      (Valued.v ((b : LocalProduct K L v) ⟨w₀, hw₀⟩) : ℤᵐ⁰)
        = Valued.v ((b : LocalProduct K L v) w) := by
    intro w
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_under_eq (K := K) w₀ (w : HeightOneSpectrum (𝓞 L))
      (hw₀.trans (mem_placesOver.1 w.2).symm)
    have hconv : invSmulPlace σ w = (⟨w₀, hw₀⟩ : placesOver K L v) := by
      refine Subtype.ext ?_
      rw [invSmulPlace_coe, ← hσ, inv_smul_smul]
    have heq : (σ • b : (LocalProduct K L v)ˣ) = f σ * b := div_eq_iff_eq_mul.1 (hb σ)
    have hleft : (Valued.v (((σ • b : (LocalProduct K L v)ˣ) : LocalProduct K L v) w) : ℤᵐ⁰)
        = Valued.v ((b : LocalProduct K L v) (invSmulPlace σ w)) :=
      valued_localProduct_smul σ (b : LocalProduct K L v) w
    rw [heq] at hleft
    have hright : (Valued.v ((((f σ * b : (LocalProduct K L v)ˣ)) : LocalProduct K L v) w) : ℤᵐ⁰)
        = Valued.v ((b : LocalProduct K L v) w) := by
      show (Valued.v (((f σ : LocalProduct K L v) * (b : LocalProduct K L v)) w) : ℤᵐ⁰) = _
      rw [show (((f σ : LocalProduct K L v) * (b : LocalProduct K L v)) w)
          = (f σ : LocalProduct K L v) w * (b : LocalProduct K L v) w from rfl, map_mul,
        valued_eq_one_of_mem_localProductIntegerUnits (hint σ) w, one_mul]
    rw [hconv] at hleft
    rw [← hleft, hright]
  set c : ℤ := log (Valued.v ((b : LocalProduct K L v) ⟨w₀, hw₀⟩)) with hc
  have hbexp : ∀ w : placesOver K L v,
      (Valued.v ((b : LocalProduct K L v) w) : ℤᵐ⁰) = exp c := by
    intro w
    rw [hc, ← hbv w, exp_log (valued_units_ne_zero b _)]
  -- A uniformizer of `K` at `v`, raised to the power `c`, as a global unit.
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact exp_ne_zero hπ.symm
  set x : Kˣ := Units.mk0 π hπ0 ^ c with hx
  have hxval : v.valuation K (x : K) = exp (-c) := by
    rw [hx, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀, hπ, ← exp_zsmul, smul_eq_mul,
      mul_neg_one]
  set u : (LocalProduct K L v)ˣ :=
    Units.map (diagLocalProduct K L v : K →* LocalProduct K L v) x with hu
  have hucoe : (u : LocalProduct K L v) = diagLocalProduct K L v (x : K) := rfl
  have huval : ∀ w : placesOver K L v,
      (Valued.v ((u : LocalProduct K L v) w) : ℤᵐ⁰) = exp (-c) := by
    intro w
    haveI : (w : HeightOneSpectrum (𝓞 L)).asIdeal.LiesOver v.asIdeal :=
      ⟨(mem_placesOver.1 w.2).symm⟩
    rw [hucoe, valued_diagLocalProduct,
      ← valuation_liesOver L v (w : HeightOneSpectrum (𝓞 L)) (x : K),
      ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal
        (w : HeightOneSpectrum (𝓞 L)).asIdeal v.ne_bot, hv _ w.2, pow_one, hxval]
  have husmul : ∀ g : L ≃ₐ[K] L, g • u = u := fun g ↦
    Units.ext (smul_diagLocalProduct g (x : K))
  refine ⟨b * u, mem_localProductIntegerUnits_of_valued_eq_one fun w ↦ ?_, fun g ↦ ?_⟩
  · show (Valued.v (((b : LocalProduct K L v) * (u : LocalProduct K L v)) w) : ℤᵐ⁰) = 1
    rw [show (((b : LocalProduct K L v) * (u : LocalProduct K L v)) w)
        = (b : LocalProduct K L v) w * (u : LocalProduct K L v) w from rfl, map_mul,
      hbexp w, huval w, ← exp_add, add_neg_cancel, exp_zero]
  · rw [smul_mul', husmul, mul_div_mul_right_eq_div, hb g]

/-! ## Almost every place is unramified -/

/-- **All but finitely many finite places of `K` are unramified in `L`.**  A ramified prime
divides the different ideal, and only finitely many primes divide a nonzero ideal. -/
theorem eventually_ramificationIdx_eq_one :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      ∀ w : HeightOneSpectrum (𝓞 L), w ∈ placesOver K L v →
        v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset
    ((Ideal.finite_factors (R := 𝓞 L) (I := differentIdeal (𝓞 K) (𝓞 L))
      (by simpa using differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))).image
        (fun w ↦ w.under (𝓞 K))) ?_
  rintro v hv
  simp only [Set.mem_ofPred_eq, not_forall] at hv
  obtain ⟨w, hwv, hne⟩ := hv
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨(mem_placesOver.1 hwv).symm⟩
  refine ⟨w, ?_, HeightOneSpectrum.ext (mem_placesOver.1 hwv)⟩
  by_contra hdvd
  haveI := w.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := not_dvd_differentIdeal_iff.mp hdvd
  exact hne (by rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt])

/-! ## `H¹(Gal(L/K), 𝕀_L) = 0` -/

variable (K L) in
/-- **The local input at almost every place holds.**  This discharges the hypothesis of
`NumberField.isZero_H1_finiteIdele_of`. -/
theorem isUnramifiedAlmostEverywhere : IsUnramifiedAlmostEverywhere K L := by
  filter_upwards [eventually_ramificationIdx_eq_one (K := K) (L := L)] with v hv f hf hint
  exact exists_integral_trivialisation v hv f hf hint

variable (K L) in
/-- **`H¹(Gal(L/K), (𝔸_L^f)^×) = 0`**, unconditionally. -/
theorem isZero_H1_finiteIdele :
    IsZero (groupCohomology
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (FiniteAdeleRing (𝓞 L) L)ˣ) 1) :=
  isZero_H1_finiteIdele_of K L (isUnramifiedAlmostEverywhere K L)

variable (K L) in
/-- **`H¹(Gal(L/K), 𝕀_L) = 0`**, unconditionally. -/
theorem isZero_H1_repIdele : IsZero (groupCohomology (repIdele K L) 1) :=
  isZero_H1_repIdele_of K L (isUnramifiedAlmostEverywhere K L)

/-- **`H¹(H, 𝕀_L) = 0` for a subgroup `H ≤ Gal(L/K)`**, unconditionally. -/
theorem isZero_H1_subgroup_repIdele (H : Subgroup (L ≃ₐ[K] L)) :
    IsZero (groupCohomology (Rep.ofMulDistribMulAction H (IdeleGroup (𝓞 L) L)) 1) :=
  isZero_H1_subgroup_repIdele_of (K := K) (L := L) H
    (isUnramifiedAlmostEverywhere (IntermediateField.fixedField H) L)

/-- **`H¹(Gal(L/K), C_L) = 0`**, modulo the injectivity of
`H²(Gal(L/K), Lˣ) ⟶ H²(Gal(L/K), 𝕀_L)`. -/
theorem isZero_H1_repIdeleClass
    (hmono : Mono ((groupCohomology.functor ℤ (L ≃ₐ[K] L) 2).map
      (ideleShortComplex K L).f)) :
    IsZero (groupCohomology (repIdeleClass K L) 1) :=
  isZero_H1_repIdeleClass_of' K L (isUnramifiedAlmostEverywhere K L) hmono

end NumberField
