/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Topology.Algebra.Valued.ValuedField

@[expose] public section

/-!
# Functoriality of adic completions under isomorphisms

Let `A` and `B` be Dedekind domains with fraction fields `K` and `L`, and let `e : A ≃+* B`
and `f : K ≃+* L` be compatible isomorphisms.  Then `e` induces a bijection
`IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e` on height one spectra, and for each
`v` the map `f` is an isometry from `K` with the `v`-adic valuation to `L` with the
`(e v)`-adic valuation.  Consequently `f` extends to a ring isomorphism of adic completions.

This is the local input needed to define the Galois action on the finite adele ring.

## Main results

* `Valued.uniformContinuous_of_valuation` : a valuation-preserving ring isomorphism between
  valued rings is uniformly continuous.
* `IsDedekindDomain.HeightOneSpectrum.intValuation_equivOfRingEquiv`,
  `IsDedekindDomain.HeightOneSpectrum.valuation_equivOfRingEquiv` : the adic valuations are
  preserved.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr` : the induced isomorphism of adic
  completions, and `adicCompletionCongr_valued` saying that it preserves the valuation.
-/

noncomputable section

open Filter Topology MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
open scoped WithZero

/-! ## A valuation-preserving isomorphism is uniformly continuous -/

/-- A valuation-preserving ring isomorphism between valued rings with the same value monoid
is uniformly continuous. -/
theorem Valued.uniformContinuous_of_valuation {A B Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [Ring A] [Ring B] [Valued A Γ₀] [Valued B Γ₀]
    (g : A ≃+* B) (hg : ∀ x, (Valued.v (g x) : Γ₀) = Valued.v x) :
    UniformContinuous (g : A → B) := by
  refine uniformContinuous_of_continuousAt_zero ((g : A →+* B) : A →+ B) ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  rw [Valued.is_topological_valuation s] at hs
  obtain ⟨γ, hγ⟩ := hs
  obtain ⟨r, t, hr, ht, hrt⟩ := Valuation.exists_div_eq_of_unit (Valued.v (R := B)) γ
  have hr' : (Valued.v (g.symm r) : Γ₀) = Valued.v r := by
    rw [← hg (g.symm r), RingEquiv.apply_symm_apply]
  have ht' : (Valued.v (g.symm t) : Γ₀) = Valued.v t := by
    rw [← hg (g.symm t), RingEquiv.apply_symm_apply]
  have hemb : ValueGroup₀.embedding γ.1 = (Valued.v r : Γ₀) / Valued.v t := by
    rw [← hrt, map_div₀, Valuation.embedding_restrict, Valuation.embedding_restrict]
  set δ := (Valued.v (R := A)).restrict (g.symm r) / (Valued.v (R := A)).restrict (g.symm t)
    with hδdef
  have hδ0 : δ ≠ 0 := by
    rw [hδdef]
    refine div_ne_zero ?_ ?_ <;> simp only [ne_eq, Valuation.restrict_eq_zero_iff]
    · rw [hr']; exact hr.ne'
    · rw [ht']; exact ht.ne'
  have hembδ : ValueGroup₀.embedding δ = (Valued.v r : Γ₀) / Valued.v t := by
    rw [hδdef, map_div₀, Valuation.embedding_restrict, Valuation.embedding_restrict, hr', ht']
  rw [Filter.mem_map, Valued.is_topological_valuation]
  refine ⟨Units.mk0 δ hδ0, fun x hx => hγ ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hx ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  rw [hembδ] at hx
  rw [hemb]
  calc (Valued.v (g x) : Γ₀) = Valued.v x := hg x
    _ < _ := hx

/-! ## `Ideal.map` along an isomorphism -/

/-- `Ideal.map` along a ring equivalence, as a multiplicative equivalence. -/
def Ideal.mapMulEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Ideal A ≃* Ideal B where
  toFun := Ideal.map e
  invFun := Ideal.map e.symm
  left_inv I := by rw [Ideal.map_symm, ← Ideal.comap_symm]; exact Ideal.comap_of_equiv e
  right_inv I := by
    rw [Ideal.map_symm]
    exact Ideal.map_comap_of_surjective (e : A →+* B) e.surjective I
  map_mul' I J := Ideal.map_mul _ _ _

@[simp]
theorem Ideal.mapMulEquiv_apply {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (I : Ideal A) : Ideal.mapMulEquiv e I = Ideal.map e I := rfl

namespace IsDedekindDomain.HeightOneSpectrum

/-! ## Equivariance of the adic valuations -/

section Spectrum

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]

omit [IsDedekindDomain A] [IsDedekindDomain B] in
theorem asIdeal_equivOfRingEquiv (e : A ≃+* B) (v : HeightOneSpectrum A) :
    (equivOfRingEquiv e v).asIdeal = Ideal.map e v.asIdeal := by
  show v.asIdeal.comap e.symm = _
  rw [Ideal.comap_symm]

/-- The `v`-adic valuation on `A` matches the `(e v)`-adic valuation on `B`. -/
theorem intValuation_equivOfRingEquiv (e : A ≃+* B) (v : HeightOneSpectrum A) (a : A) :
    (equivOfRingEquiv e v).intValuation (e a) = v.intValuation a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have hea : e a ≠ 0 := by simpa using ha
    rw [intValuation_eq_exp_neg_multiplicity _ ha, intValuation_eq_exp_neg_multiplicity _ hea]
    have h2 : Ideal.span {e a} = Ideal.map e (Ideal.span {a}) := by
      rw [Ideal.map_span]; simp
    rw [asIdeal_equivOfRingEquiv, h2]
    have := multiplicity_map_eq (Ideal.mapMulEquiv e) (a := v.asIdeal) (b := Ideal.span {a})
    simp only [Ideal.mapMulEquiv_apply] at this
    rw [this]

end Spectrum

section Fraction

variable {A B K L : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L] [IsFractionRing B L]

/-- The `v`-adic valuation on the fraction field `K` matches the `(e v)`-adic valuation
on `L`, along a compatible pair of isomorphisms. -/
theorem valuation_equivOfRingEquiv (e : A ≃+* B) (f : K ≃+* L)
    (hef : ∀ a : A, f (algebraMap A K a) = algebraMap B L (e a)) (v : HeightOneSpectrum A)
    (x : K) : (equivOfRingEquiv e v).valuation L (f x) = v.valuation K x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  rw [map_div₀, hef, hef, map_div₀, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap, intValuation_equivOfRingEquiv,
    intValuation_equivOfRingEquiv]

end Fraction

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

section Completion

open WithZeroTopology
open scoped WithZero

variable {A B K L : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L] [IsFractionRing B L]
  (f : K ≃+* L) (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)

/-- `f`, viewed as a map from `K` with the `v`-adic valuation to `L` with the `w`-adic
valuation. -/
def withValCongr : WithVal (v.valuation K) ≃+* WithVal (w.valuation L) :=
  WithVal.congr _ _ f

@[simp]
theorem withValCongr_apply (x : WithVal (v.valuation K)) :
    withValCongr f v w x = WithVal.toVal _ (f x.ofVal) := rfl

variable (hfv : ∀ x : K, w.valuation L (f x) = v.valuation K x)

include hfv

theorem valued_withValCongr (x : WithVal (v.valuation K)) :
    (Valued.v (withValCongr f v w x) : ℤᵐ⁰) = Valued.v x := by
  rw [withValCongr_apply, WithVal.valued_toVal, ← WithVal.apply_ofVal]
  exact hfv x.ofVal

theorem valued_withValCongr_symm (y : WithVal (w.valuation L)) :
    (Valued.v ((withValCongr f v w).symm y) : ℤᵐ⁰) = Valued.v y := by
  obtain ⟨x, rfl⟩ := (withValCongr f v w).surjective y
  rw [RingEquiv.symm_apply_apply]
  exact (valued_withValCongr f v w hfv x).symm

theorem uniformContinuous_withValCongr : UniformContinuous (withValCongr f v w) :=
  Valued.uniformContinuous_of_valuation _ (valued_withValCongr f v w hfv)

theorem uniformContinuous_withValCongr_symm : UniformContinuous (withValCongr f v w).symm :=
  Valued.uniformContinuous_of_valuation _ (valued_withValCongr_symm f v w hfv)

/-- The isomorphism from the `v`-adic completion of `K` to the `w`-adic completion of `L`
induced by an isomorphism `f : K ≃+* L` carrying the `v`-adic valuation to the `w`-adic
valuation. -/
def adicCompletionCongr : v.adicCompletion K ≃+* w.adicCompletion L :=
  ((adicCompletion.equiv K v).trans
      (UniformSpace.Completion.mapRingEquiv (withValCongr f v w)
        (uniformContinuous_withValCongr f v w hfv).continuous
        (uniformContinuous_withValCongr_symm f v w hfv).continuous)).trans
    (adicCompletion.equiv L w).symm

theorem adicCompletionCongr_apply (x : v.adicCompletion K) :
    adicCompletionCongr f v w hfv x =
      adicCompletion.ofCompletion
        (UniformSpace.Completion.map (withValCongr f v w) x.toCompletion) := rfl

theorem continuous_adicCompletionCongr : Continuous (adicCompletionCongr f v w hfv) := by
  simp only [continuous_def]
  refine fun s hs => ?_
  have : (adicCompletionCongr f v w hfv) ⁻¹' s =
      (adicCompletion.toCompletion (K := K) (v := v)) ⁻¹'
        ((UniformSpace.Completion.map (withValCongr f v w)) ⁻¹'
          ((adicCompletion.ofCompletion (K := L) (v := w)) ⁻¹' s)) := rfl
  rw [this]
  exact ((hs.preimage (adicCompletion.continuous_ofCompletion L _)).preimage
    UniformSpace.Completion.continuous_map).preimage
      (adicCompletion.continuous_toCompletion K v)

@[simp]
theorem adicCompletionCongr_coe (k : K) :
    adicCompletionCongr f v w hfv (k : v.adicCompletion K) = ((f k : L) : w.adicCompletion L) := by
  rw [adicCompletionCongr_apply]
  congr 1
  exact UniformSpace.Completion.map_coe (uniformContinuous_withValCongr f v w hfv) _

/-- The isomorphism of adic completions preserves the valuation. -/
theorem valued_adicCompletionCongr (x : v.adicCompletion K) :
    (Valued.v (adicCompletionCongr f v w hfv x) : ℤᵐ⁰) = Valued.v x := by
  have hcont₁ : Continuous fun x : v.adicCompletion K ↦
      (Valued.v (adicCompletionCongr f v w hfv x) : ℤᵐ⁰) :=
    (Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective L w)).comp
      (continuous_adicCompletionCongr f v w hfv)
  have hcont₂ : Continuous fun x : v.adicCompletion K ↦ (Valued.v x : ℤᵐ⁰) :=
    Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective K v)
  have := Continuous.ext_on (denseRange_algebraMap (R := A) (K := K) (v := v))
    hcont₁ hcont₂ ?_
  · exact congrFun this x
  · rintro _ ⟨k, rfl⟩
    show (Valued.v (adicCompletionCongr f v w hfv ((k : K) : v.adicCompletion K)) : ℤᵐ⁰)
        = (Valued.v ((k : K) : v.adicCompletion K) : ℤᵐ⁰)
    rw [adicCompletionCongr_coe, adicCompletion.valued_coe, adicCompletion.valued_coe]
    exact hfv k

theorem adicCompletionCongr_mapsTo_integers :
    Set.MapsTo (adicCompletionCongr f v w hfv) (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) := by
  intro x hx
  rw [SetLike.mem_coe, mem_adicCompletionIntegers, valued_adicCompletionCongr]
  exact hx

end Completion

end IsDedekindDomain.HeightOneSpectrum
