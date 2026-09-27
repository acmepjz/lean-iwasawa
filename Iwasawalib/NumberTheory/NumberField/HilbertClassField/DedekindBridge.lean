/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.AbsoluteValue.InfiniteInertia
public import Iwasawalib.NumberTheory.LocalCFT.PlaceDedekind
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Unramified

@[expose] public section

/-!
# Unramified everywhere: the place formalism and the Dedekind formalism agree

`NumberField.IsUnramifiedEverywhere F E` (see
`Iwasawalib.NumberTheory.NumberField.HilbertClassField.Basic`) says that every nontrivial
absolute value `v : AbsoluteValue E ℝ` is unramified over `F` (for Galois `E / F`, equivalently:
has trivial inertia subgroup in the sense of `AbsoluteValue.inertiaSubgroup`).  Mathlib, and class field theory libraries built
on it, express the same condition ideal-theoretically: every height-one prime `P` of `𝓞 E`
satisfies `Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal`, and every infinite place is unramified
(`IsUnramifiedAtInfinitePlaces F E`).  This file proves that the two notions agree for a finite
Galois extension of number fields.

* At a finite place the translation goes through `NumberField.inertiaSubgroup_eq_inertia`
  (`Iwasawalib.NumberTheory.LocalCFT.PlaceDedekind`) and Mathlib's characterisation
  `Ideal.ramificationIdx_eq_one_iff` of `Algebra.IsUnramifiedAt` by ramification index one
  (the residue fields are finite, hence perfect).  For the converse, a nontrivial
  nonarchimedean absolute value `v` of `E` determines the prime `{y ∈ 𝓞 E | v y < 1}`, whose
  Dedekind inertia group contains the inertia subgroup of `v`
  (`NumberField.exists_heightOneSpectrum_inertiaSubgroup_le`); no normalisation of `v` is needed.
* At an infinite place, the inertia subgroup of an archimedean absolute value is its
  decomposition subgroup, which for the absolute value underlying an infinite place is Mathlib's
  stabiliser of the place (`NumberField.InfinitePlace.stabilizer_eq_inertiaSubgroup`).  Every
  archimedean absolute value is equivalent to an infinite place by the Gelfand-Tornheim theorem
  `AbsoluteValue.exists_ringHom_complex_of_not_isNonarchimedean`, and Mathlib characterises
  unramified infinite places of a Galois extension by triviality of the stabiliser
  (`NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot`).

## Main statements

* `NumberField.isUnramifiedAt_of_isUnramifiedEverywhere`: an extension unramified everywhere in
  the place formalism is unramified at every prime of `𝓞 E`.
* `NumberField.isUnramifiedAtInfinitePlaces_of_isUnramifiedEverywhere`: it is unramified at every
  infinite place in the sense of Mathlib.
* `NumberField.isUnramifiedEverywhere_of_isUnramifiedAt`: the converse.
* `NumberField.isUnramifiedEverywhere_iff_isUnramifiedAt`: the resulting equivalence.

Auxiliary statements:

* `NumberField.InfinitePlace.mem_stabilizer_iff_mem_decompositionSubgroup`,
  `NumberField.InfinitePlace.not_isNonarchimedean`,
  `NumberField.InfinitePlace.stabilizer_eq_inertiaSubgroup`: infinite places.
* `NumberField.apply_le_one_of_isNonarchimedean`,
  `NumberField.exists_heightOneSpectrum_inertiaSubgroup_le`,
  `NumberField.inertia_eq_bot_of_isUnramifiedAt`: finite places.
-/

open IsDedekindDomain

namespace NumberField

/-! ### Infinite places -/

section InfinitePlace

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The stabiliser of an infinite place in `Gal(E/F)` (for Mathlib's action on infinite places)
is the decomposition subgroup of the underlying absolute value. -/
theorem InfinitePlace.mem_stabilizer_iff_mem_decompositionSubgroup (w : InfinitePlace E)
    (σ : E ≃ₐ[F] E) :
    σ ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ↔ σ ∈ w.1.decompositionSubgroup F := by
  rw [MulAction.mem_stabilizer_iff, AbsoluteValue.decompositionSubgroup,
    MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    ext x
    have := congr($h x)
    rw [InfinitePlace.smul_apply] at this
    simpa [InfinitePlace.coe_apply] using this
  · intro h
    refine InfinitePlace.ext _ _ fun x ↦ ?_
    rw [InfinitePlace.smul_apply]
    simpa [InfinitePlace.coe_apply] using congr($h x)

/-- The absolute value underlying an infinite place is archimedean. -/
theorem InfinitePlace.not_isNonarchimedean (w : InfinitePlace E) : ¬IsNonarchimedean w.1 := by
  rw [AbsoluteValue.isNonarchimedean_iff_forall_apply_natCast_le_one]
  intro h
  have h2 := h 2
  have : w.1 (2 : ℕ) = 2 := by
    rw [← InfinitePlace.coe_apply, InfinitePlace.map_natCast]
    norm_num
  rw [this] at h2
  norm_num at h2

/-- The stabiliser of an infinite place in `Gal(E/F)` is the inertia subgroup of the underlying
absolute value (which, the place being archimedean, is its decomposition subgroup). -/
theorem InfinitePlace.stabilizer_eq_inertiaSubgroup (w : InfinitePlace E) :
    MulAction.stabilizer (E ≃ₐ[F] E) w = w.1.inertiaSubgroup F := by
  ext σ
  rw [InfinitePlace.mem_stabilizer_iff_mem_decompositionSubgroup,
    AbsoluteValue.inertiaSubgroup_eq_decompositionSubgroup_of_not_isNonarchimedean _ _
      (InfinitePlace.not_isNonarchimedean w)]

end InfinitePlace

/-! ### Finite places -/

section FinitePlace

variable {E : Type*} [Field E]

/-- A nonarchimedean absolute value on a field `E` is at most `1` on the ring of integers `𝓞 E`
(the integral closure of `ℤ` in `E`). -/
theorem apply_le_one_of_isNonarchimedean {v : AbsoluteValue E ℝ} (hna : IsNonarchimedean v)
    (y : 𝓞 E) : v (y : E) ≤ 1 := by
  let V := (v.toValuation hna).valuationSubring
  have hx : IsIntegral V (y : E) := y.isIntegral_coe.tower_top
  rw [IsIntegrallyClosedIn.isIntegral_iff] at hx
  obtain ⟨z, hz⟩ := hx
  rw [← hz]
  change v (z : E) ≤ 1
  exact_mod_cast z.2

variable [NumberField E]

/-- For a nontrivial nonarchimedean absolute value `v` on a number field `E`, there is a
height-one prime `P` of `𝓞 E` (in the proof, `{y | v y < 1}`) whose inertia subgroup in
`Gal(E/F)` contains the inertia subgroup of `v`. -/
theorem exists_heightOneSpectrum_inertiaSubgroup_le (F : Type*) [Field F] [Algebra F E]
    (v : AbsoluteValue E ℝ) (hv : v.IsNontrivial) (hna : IsNonarchimedean v) :
    ∃ P : HeightOneSpectrum (𝓞 E), v.inertiaSubgroup F ≤ P.asIdeal.inertia (E ≃ₐ[F] E) := by
  let V := (v.toValuation hna).valuationSubring
  have hle := apply_le_one_of_isNonarchimedean hna
  let i : 𝓞 E →+* V := (algebraMap (𝓞 E) E).codRestrict V fun x ↦ by
    change (v.toValuation hna) (x : E) ≤ 1
    exact_mod_cast hle x
  let Q : Ideal (𝓞 E) := (IsLocalRing.maximalIdeal V).comap i
  have hQmem (x : 𝓞 E) : x ∈ Q ↔ v (x : E) < 1 := by
    rw [Ideal.mem_comap, Valuation.mem_maximalIdeal_iff]
    rfl
  have hQprime : Q.IsPrime := Ideal.comap_isPrime i _
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have h1 : ∀ y : 𝓞 E, y ≠ 0 → v (y : E) = 1 := by
      intro y hy
      refine le_antisymm (hle y) (not_lt.1 fun hlt ↦ hy ?_)
      rw [← Ideal.mem_bot, ← hbot, hQmem]
      exact hlt
    obtain ⟨x, hx0, hx1⟩ := hv
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    have ha : a ≠ 0 := by
      rintro rfl
      simp at hx0
    refine hx1 ?_
    rw [map_div₀, h1 a ha, h1 b (nonZeroDivisors.ne_zero hb), div_one]
  refine ⟨⟨Q, hQprime, hQne⟩, fun σ hσ ↦ ?_⟩
  rw [Ideal.inertia, AddSubgroup.mem_inertia]
  intro y
  change σ • y - y ∈ Q
  rw [hQmem]
  exact AbsoluteValue.apply_sub_lt_one_of_mem_inertiaSubgroup_of_isNonarchimedean v hσ hna
    (hle y)

variable (F : Type*) [Field F] [NumberField F] [Algebra F E]

/-- A prime of `𝓞 E` which is unramified over `𝓞 F` has trivial inertia subgroup in
`Gal(E/F)`. -/
theorem inertia_eq_bot_of_isUnramifiedAt [IsGalois F E] (P : HeightOneSpectrum (𝓞 E))
    [Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal] : P.asIdeal.inertia (E ≃ₐ[F] E) = ⊥ := by
  have h1 : P.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one _ _
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (HeightOneSpectrum.under (𝓞 F) P).ne_bot]
    at h1
  have h2 := (adicAbv_isUnramified_iff P (HeightOneSpectrum.under (𝓞 F) P)).2 h1
  rwa [AbsoluteValue.isUnramified_iff_inertiaSubgroup_eq_bot, inertiaSubgroup_eq_inertia] at h2

end FinitePlace

/-! ### The comparison -/

section Comparison

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

/-- **Finite places.** In a finite Galois extension of number fields which is unramified
everywhere in the place formalism, every height-one prime of `𝓞 E` is unramified over `𝓞 F`. -/
theorem isUnramifiedAt_of_isUnramifiedEverywhere [NumberField F] [NumberField E] [IsGalois F E]
    [IsUnramifiedEverywhere F E] (P : HeightOneSpectrum (𝓞 E)) :
    Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal := by
  have h := ramificationIdx'_under_eq_one_of_isUnramifiedEverywhere (K := F) P
  have hne : (HeightOneSpectrum.under (𝓞 F) P).asIdeal ≠ ⊥ :=
    (HeightOneSpectrum.under (𝓞 F) P).ne_bot
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hne] at h
  have : Finite ((𝓞 F) ⧸ P.asIdeal.under (𝓞 F)) := Ring.HasFiniteQuotients.finiteQuotient hne
  have : PerfectField (P.asIdeal.under (𝓞 F)).ResidueField := PerfectField.ofFinite
  exact Ideal.ramificationIdx_eq_one_iff.1 h

/-- **Infinite places.** A Galois extension which is unramified everywhere in the place
formalism is unramified at every infinite place in the sense of Mathlib. -/
theorem isUnramifiedAtInfinitePlaces_of_isUnramifiedEverywhere [IsGalois F E]
    [IsUnramifiedEverywhere F E] : IsUnramifiedAtInfinitePlaces F E := by
  refine ⟨fun w ↦ ?_⟩
  rw [InfinitePlace.isUnramified_iff_stabilizer_eq_bot,
    InfinitePlace.stabilizer_eq_inertiaSubgroup]
  exact AbsoluteValue.inertiaSubgroup_eq_bot_of_isUnramifiedEverywhere F w.1

/-- **The converse.** A finite Galois extension of number fields which is unramified at every
height-one prime of `𝓞 E` and at every infinite place is unramified everywhere in the place
formalism. -/
theorem isUnramifiedEverywhere_of_isUnramifiedAt [NumberField F] [NumberField E] [IsGalois F E]
    (hfin : ∀ P : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal)
    [IsUnramifiedAtInfinitePlaces F E] : IsUnramifiedEverywhere F E := by
  rw [isUnramifiedEverywhere_iff]
  intro v hv
  rw [AbsoluteValue.isUnramified_iff_inertiaSubgroup_eq_bot, eq_bot_iff]
  by_cases hna : IsNonarchimedean v
  · obtain ⟨P, hP⟩ := exists_heightOneSpectrum_inertiaSubgroup_le F v hv hna
    have := hfin P
    exact hP.trans (inertia_eq_bot_of_isUnramifiedAt F P).le
  · obtain ⟨φ, hφ⟩ := AbsoluteValue.exists_ringHom_complex_of_not_isNonarchimedean v hna
    have h1 := (InfinitePlace.mk φ).isUnramified F
    rw [InfinitePlace.isUnramified_iff_stabilizer_eq_bot, eq_bot_iff] at h1
    refine (AbsoluteValue.inertiaSubgroup_le_decompositionSubgroup F v).trans (le_trans ?_ h1)
    intro σ hσ
    rw [InfinitePlace.mem_stabilizer_iff_mem_decompositionSubgroup]
    change σ ∈ (place φ).decompositionSubgroup F
    rwa [AbsoluteValue.decompositionSubgroup_eq_of_equiv F hφ]

/-- **Unramified everywhere: the place formalism and the Dedekind formalism agree.** A finite
Galois extension of number fields is unramified everywhere in the sense of absolute values if and
only if it is unramified at every height-one prime of `𝓞 E` and at every infinite place. -/
theorem isUnramifiedEverywhere_iff_isUnramifiedAt [NumberField F] [NumberField E] [IsGalois F E] :
    IsUnramifiedEverywhere F E ↔
      (∀ P : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal) ∧
        IsUnramifiedAtInfinitePlaces F E :=
  ⟨fun _ ↦ ⟨isUnramifiedAt_of_isUnramifiedEverywhere F E,
      isUnramifiedAtInfinitePlaces_of_isUnramifiedEverywhere F E⟩,
    fun ⟨hfin, _⟩ ↦ isUnramifiedEverywhere_of_isUnramifiedAt F E hfin⟩

end Comparison

end NumberField
