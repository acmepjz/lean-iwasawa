/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.ClassGroup.Basic

@[expose] public section

/-!
# The `ℤ`-valued adic valuation of a Dedekind domain

Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuation` takes values in `ℤₘ₀`, and
`FractionalIdeal.count` records the exponent of `v` in the factorisation of a fractional ideal.
This file introduces the `ℤ`-valued valuation

`IsDedekindDomain.HeightOneSpectrum.ord v x = - WithZero.log (v.valuation K x)`

and proves the bridge between the two:
`IsDedekindDomain.HeightOneSpectrum.ord_eq_count`, `ord v x = count v (x)`.

The bridge is what makes the divisor of an element computable, and it is used to prove the
main result of this file:

* `IsDedekindDomain.HeightOneSpectrum.exists_ord_eq_card_classGroup_smul` : if the class group
  of `R` is finite of order `h`, then for every finitely supported `n : HeightOneSpectrum R → ℤ`
  there is an `x ∈ Kˣ` whose divisor is `h • n`.  In other words, the divisor map
  `Kˣ → ⨁_v ℤ` has image of index dividing `h^{#S}` in every coordinate subgroup.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal WithZero
open scoped nonZeroDivisors

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

/-- The `ℤ`-valued `v`-adic valuation (the order of vanishing at `v`) of an element of `K`.
It is normalised so that a uniformiser at `v` has `ord` equal to `1`; the junk value at `0`
is `0`. -/
def ord (x : K) : ℤ := - WithZero.log (v.valuation K x)

variable {K v}

theorem valuation_ne_zero {x : K} (hx : x ≠ 0) : v.valuation K x ≠ 0 := by
  simpa using (Valuation.ne_zero_iff (v.valuation K)).2 hx

theorem ord_eq_zero_iff {x : K} (hx : x ≠ 0) : v.ord K x = 0 ↔ v.valuation K x = 1 := by
  have h0 : v.valuation K x ≠ 0 := valuation_ne_zero hx
  rw [ord, neg_eq_zero]
  constructor
  · intro h
    rw [← WithZero.exp_log h0, h, WithZero.exp_zero]
  · intro h; rw [h]; simp

theorem ord_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    v.ord K (x * y) = v.ord K x + v.ord K y := by
  rw [ord, ord, ord, map_mul, WithZero.log_mul (valuation_ne_zero hx) (valuation_ne_zero hy),
    neg_add]

@[simp] theorem ord_one : v.ord K (1 : K) = 0 := by simp [ord]

@[simp] theorem ord_zero : v.ord K (0 : K) = 0 := by simp [ord]

theorem ord_inv (x : K) : v.ord K x⁻¹ = - v.ord K x := by
  rw [ord, ord, map_inv₀, WithZero.log_inv, neg_neg]

theorem ord_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    v.ord K (x / y) = v.ord K x - v.ord K y := by
  rw [div_eq_mul_inv, ord_mul hx (inv_ne_zero hy), ord_inv, sub_eq_add_neg]

open scoped Classical in
/-- **The `ℤ`-valued adic valuation is the exponent of `v` in the factorisation of the
principal fractional ideal `(x)`.** -/
theorem ord_eq_count {x : K} (hx : x ≠ 0) :
    v.ord K x = FractionalIdeal.count K v (spanSingleton R⁰ x) := by
  obtain ⟨⟨n, d⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ x
  have hd_ne_zero : (algebraMap R K) (d : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) d.property
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hx
  have h0 : spanSingleton R⁰ (IsLocalization.mk' K n d) ≠ 0 := by
    rwa [spanSingleton_ne_zero_iff]
  have hI : spanSingleton R⁰ (IsLocalization.mk' K n d) =
      spanSingleton R⁰ ((algebraMap R K) (d : R))⁻¹ * ↑(Ideal.span {n} : Ideal R) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined K v h0 hI, ord, valuation_of_mk',
    intValuation_if_neg _ hn, intValuation_if_neg _ (nonZeroDivisors.ne_zero d.2),
    ← WithZero.exp_sub, WithZero.log_exp]
  ring

variable (K) in
/-- The divisor of a nonzero element of `K` is supported on finitely many places. -/
theorem ord_eventually_eq_zero {x : K} (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, v.ord K x = 0 := by
  have h := FractionalIdeal.finite_factors (R := R) (K := K) (spanSingleton R⁰ x)
  refine h.mono fun v hv ↦ ?_
  rw [ord_eq_count hx, hv]

/-! ## The divisor map and the class group -/

variable (K) in
/-- A finitely supported family of exponents defines a nonzero fractional ideal. -/
theorem finprod_asIdeal_zpow_ne_zero (n : HeightOneSpectrum R → ℤ) :
    (∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ n v) ≠ 0 :=
  finprod_induction (fun I : FractionalIdeal R⁰ K ↦ I ≠ 0) one_ne_zero
    (fun _ _ ha hb ↦ mul_ne_zero ha hb)
    fun v ↦ zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

variable (K) in
/-- A fractional ideal whose class is trivial is principal, generated by a unit of `K`. -/
theorem exists_spanSingleton_eq_of_classGroup_mk_eq_one {I : (FractionalIdeal R⁰ K)ˣ}
    (h : ClassGroup.mk K I = 1) :
    ∃ x : Kˣ, spanSingleton R⁰ (x : K) = (I : FractionalIdeal R⁰ K) := by
  rw [ClassGroup.mk_eq_one_iff] at h
  obtain ⟨x, hx⟩ := h
  have hI : (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ x := by
    refine FractionalIdeal.coeToSubmodule_injective ?_
    simpa only [FractionalIdeal.coe_spanSingleton] using hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [spanSingleton_zero] at hI
    exact I.ne_zero hI
  exact ⟨Units.mk0 x hx0, hI.symm⟩

variable (K) in
/-- **The divisor map `Kˣ → ⨁_v ℤ` has image containing `h · (⨁_v ℤ)`**, where `h` is the
order of the class group of `R`.  Concretely: for every finitely supported family `n` of
exponents there is an element `x` of `Kˣ` whose order of vanishing at `v` is `h * n v` for
every `v`.

This is the ideal-theoretic input to Dirichlet's `S`-unit theorem: it says that the divisor
map from the `S`-units onto the lattice `ℤ^S` has image of finite index. -/
theorem exists_ord_eq_card_classGroup_smul [Fintype (ClassGroup R)]
    (n : HeightOneSpectrum R → ℤ)
    (hn : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, n v = 0) :
    ∃ x : Kˣ, ∀ v : HeightOneSpectrum R,
      v.ord K (x : K) = (Fintype.card (ClassGroup R) : ℤ) * n v := by
  classical
  set h := Fintype.card (ClassGroup R) with hh
  set I : FractionalIdeal R⁰ K := ∏ᶠ v : HeightOneSpectrum R,
    (v.asIdeal : FractionalIdeal R⁰ K) ^ n v with hIdef
  have hI0 : I ≠ 0 := finprod_asIdeal_zpow_ne_zero K n
  have hcls : ClassGroup.mk K (Units.mk0 I hI0 ^ h) = 1 := by
    rw [map_pow, hh]
    exact pow_card_eq_one
  obtain ⟨x, hx⟩ := exists_spanSingleton_eq_of_classGroup_mk_eq_one K hcls
  refine ⟨x, fun v ↦ ?_⟩
  have hcoe : ((Units.mk0 I hI0 ^ h : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = I ^ h := by
    push_cast
    rfl
  rw [ord_eq_count (x.ne_zero : (x : K) ≠ 0), hx, hcoe, FractionalIdeal.count_pow, hIdef,
    FractionalIdeal.count_finprod K v n hn]

/-! ## Divisor classes -/

variable (K)

/-- A choice of nonzero integral ideal representing each ideal class. -/
def classRep (c : ClassGroup R) : (Ideal R)⁰ := Classical.choose (ClassGroup.mk0_surjective c)

omit [Field K] [Algebra R K] [IsFractionRing R K] in
theorem classGroup_mk0_classRep (c : ClassGroup R) : ClassGroup.mk0 (classRep c) = c :=
  Classical.choose_spec (ClassGroup.mk0_surjective c)

/-- The finite set of places dividing one of the chosen class representatives. -/
def classRepSupport : Set (HeightOneSpectrum R) :=
  {w | ∃ c : ClassGroup R,
    FractionalIdeal.count K w ((classRep c : Ideal R) : FractionalIdeal R⁰ K) ≠ 0}

theorem finite_classRepSupport [Finite (ClassGroup R)] : (classRepSupport (R := R) K).Finite := by
  have h : classRepSupport (R := R) K = ⋃ c : ClassGroup R,
      {w : HeightOneSpectrum R |
        FractionalIdeal.count K w ((classRep c : Ideal R) : FractionalIdeal R⁰ K) ≠ 0} := by
    ext w; simp [classRepSupport]
  rw [h]
  refine Set.finite_iUnion fun c ↦ ?_
  have := FractionalIdeal.finite_factors (R := R) (K := K)
    ((classRep c : Ideal R) : FractionalIdeal R⁰ K)
  rwa [Filter.eventually_cofinite] at this

theorem count_classRep_eq_zero {w : HeightOneSpectrum R} (hw : w ∉ classRepSupport K (R := R))
    (c : ClassGroup R) :
    FractionalIdeal.count K w ((classRep c : Ideal R) : FractionalIdeal R⁰ K) = 0 := by
  by_contra h
  exact hw ⟨c, h⟩

/-- **Every divisor is equivalent, modulo principal divisors, to one supported on the fixed
finite set `classRepSupport`.**  This is the statement that the ideal class group is finite,
in divisorial form. -/
theorem exists_ord_eq_of_notMem_classRepSupport (d : HeightOneSpectrum R → ℤ)
    (hd : ∀ᶠ w : HeightOneSpectrum R in Filter.cofinite, d w = 0) :
    ∃ x : Kˣ, ∀ w : HeightOneSpectrum R, w ∉ classRepSupport K (R := R) →
      w.ord K (x : K) = d w := by
  classical
  set I : FractionalIdeal R⁰ K := ∏ᶠ w : HeightOneSpectrum R,
    (w.asIdeal : FractionalIdeal R⁰ K) ^ d w with hIdef
  have hI0 : I ≠ 0 := finprod_asIdeal_zpow_ne_zero K d
  set U : (FractionalIdeal R⁰ K)ˣ := Units.mk0 I hI0 with hU
  set c : ClassGroup R := ClassGroup.mk K U with hc
  set V : (FractionalIdeal R⁰ K)ˣ := FractionalIdeal.mk0 K (classRep c) with hV
  have hVc : ClassGroup.mk K V = c := by rw [hV, ClassGroup.mk_mk0, classGroup_mk0_classRep]
  have h1 : ClassGroup.mk K (U * V⁻¹) = 1 := by
    rw [map_mul, map_inv, hVc, ← hc, mul_inv_cancel]
  obtain ⟨x, hx⟩ := exists_spanSingleton_eq_of_classGroup_mk_eq_one K h1
  refine ⟨x, fun w hw ↦ ?_⟩
  have hVne : ((V : FractionalIdeal R⁰ K)) ≠ 0 := V.ne_zero
  have hcoe : ((U * V⁻¹ : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K)
      = I * (V : FractionalIdeal R⁰ K)⁻¹ := by
    push_cast
    rfl
  rw [ord_eq_count (Units.ne_zero x), hx, hcoe,
    FractionalIdeal.count_mul K w hI0 (inv_ne_zero hVne), FractionalIdeal.count_inv,
    hIdef, FractionalIdeal.count_finprod K w d hd]
  have : FractionalIdeal.count K w (V : FractionalIdeal R⁰ K) = 0 := by
    rw [hV, FractionalIdeal.coe_mk0]
    exact count_classRep_eq_zero K hw c
  rw [this, neg_zero, add_zero]


end IsDedekindDomain.HeightOneSpectrum
