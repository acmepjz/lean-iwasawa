/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.ResidueAction
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

@[expose] public section

/-!
# The residue field of an adic completion

For a Dedekind domain `R` with fraction field `K` and a height one prime `v`, the residue field
of the valuation ring `𝒪_v = v.adicCompletionIntegers K` is canonically the residue field
`R ⧸ v` of the *global* ring at `v`.

The nontrivial half is surjectivity of `R → 𝒪_v / 𝔪_v`: an element of `𝒪_v` is approximated by
an element of `K` because `K` is dense in `K_v`
(`IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap`), and an element of `K` of valuation
at most one is approximated by an element of `R`
(`IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer`).

## Main statements

* `IsDedekindDomain.HeightOneSpectrum.exists_algebraMap_sub_lt`: density of `K` in `K_v`
  in valuation form.
* `IsDedekindDomain.HeightOneSpectrum.exists_algebraMap_integer_sub_lt_one`: an element of
  `𝒪_v` is congruent mod `𝔪_v` to an element of `R`.
* `IsDedekindDomain.HeightOneSpectrum.residueFieldHom`: the ring map
  `R →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K)`, and
  `residueFieldHom_surjective`, `ker_residueFieldHom`.
* `IsDedekindDomain.HeightOneSpectrum.quotientEquivResidueField`:
  `R ⧸ v ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers K)`.
* `IsDedekindDomain.HeightOneSpectrum.finite_residueField`: for a number field, the residue
  field of `𝒪_v` is finite.
-/

noncomputable section

open IsLocalRing WithZero
open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/-! ## Approximation -/

/-- **`K` is dense in `K_v`**, in valuation form: every element of the completion is within
any prescribed nonzero distance of an element of `K`. -/
theorem exists_algebraMap_sub_lt (x : v.adicCompletion K) {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    ∃ k : K, Valued.v (algebraMap K (v.adicCompletion K) k - x) < γ := by
  obtain ⟨a, ha⟩ := valuedAdicCompletion_surjective (K := K) v γ
  have ha0 : Valued.v.restrict a ≠ (0 : MonoidWithZeroHom.ValueGroup₀ _) := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, ha]; exact hγ
  have hnhd : {y : v.adicCompletion K | Valued.v (y - x) < γ} ∈ nhds x := by
    rw [Valued.mem_nhds]
    refine ⟨Units.mk0 _ ha0, fun y hy ↦ ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_mk0] at hy ⊢
    rw [Valuation.restrict_lt_iff, ha] at hy
    exact hy
  obtain ⟨z, ⟨k, rfl⟩, hz⟩ := Dense.inter_nhds_nonempty (denseRange_algebraMap K v) hnhd
  exact ⟨k, hz⟩

/-- **`R` is dense in `𝒪_v`.**  Every element of the valuation ring of the completion is
congruent, modulo the maximal ideal, to the image of an element of `R`. -/
theorem exists_algebraMap_integer_sub_lt_one {x : v.adicCompletion K}
    (hx : Valued.v x ≤ (1 : ℤᵐ⁰)) :
    ∃ a : R, Valued.v (algebraMap R (v.adicCompletion K) a - x) < 1 := by
  obtain ⟨k, hk⟩ := exists_algebraMap_sub_lt v x (γ := 1) one_ne_zero
  have hkle : v.valuation K k ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation' (v := v) k]
    calc Valued.v (algebraMap K (v.adicCompletion K) k)
        = Valued.v ((algebraMap K (v.adicCompletion K) k - x) + x) := by ring_nf
      _ ≤ max (Valued.v (algebraMap K (v.adicCompletion K) k - x)) (Valued.v x) :=
          Valuation.map_add _ _ _
      _ ≤ 1 := max_le hk.le hx
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hkle 1
  refine ⟨a, ?_⟩
  have h1 : Valued.v (algebraMap R (v.adicCompletion K) a
      - algebraMap K (v.adicCompletion K) k) < 1 := by
    have : algebraMap R (v.adicCompletion K) a - algebraMap K (v.adicCompletion K) k
        = algebraMap K (v.adicCompletion K) (algebraMap R K a - k) := by
      rw [map_sub, ← IsScalarTower.algebraMap_apply]
    rw [this, show Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a - k))
        = v.valuation K (algebraMap R K a - k) from
      valuedAdicCompletion_eq_valuation' (v := v) _]
    simpa using ha
  calc Valued.v (algebraMap R (v.adicCompletion K) a - x)
      = Valued.v ((algebraMap R (v.adicCompletion K) a
          - algebraMap K (v.adicCompletion K) k)
        + (algebraMap K (v.adicCompletion K) k - x)) := by ring_nf
    _ ≤ max (Valued.v (algebraMap R (v.adicCompletion K) a
          - algebraMap K (v.adicCompletion K) k))
        (Valued.v (algebraMap K (v.adicCompletion K) k - x)) := Valuation.map_add _ _ _
    _ < 1 := max_lt h1 hk

/-! ## The residue field -/

section ResidueField

variable (K)

/-- An element of `𝒪_v` reduces to zero exactly when its valuation is `< 1`. -/
theorem residue_eq_zero_iff_lt_one (a : v.adicCompletionIntegers K) :
    residue (v.adicCompletionIntegers K) a = 0 ↔
      Valued.v ((a : v.adicCompletionIntegers K) : v.adicCompletion K) < 1 :=
  LocalCFT.residue_eq_zero_iff_valued_lt_one (F := v.adicCompletion K) a

/-- **The reduction map `R → 𝒪_v / 𝔪_v`.** -/
def residueFieldHom : R →+* ResidueField (v.adicCompletionIntegers K) :=
  (residue (v.adicCompletionIntegers K)).comp (algebraMap R (v.adicCompletionIntegers K))

@[simp] theorem residueFieldHom_apply (a : R) :
    residueFieldHom K v a = residue _ (algebraMap R (v.adicCompletionIntegers K) a) := rfl

/-- **`R → 𝒪_v / 𝔪_v` is surjective**: the global integers are dense in the local ones. -/
theorem residueFieldHom_surjective : Function.Surjective (residueFieldHom K v) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := exists_algebraMap_integer_sub_lt_one v (x := (x : v.adicCompletion K)) x.2
  refine ⟨a, ?_⟩
  have hz : residue (v.adicCompletionIntegers K)
      (algebraMap R (v.adicCompletionIntegers K) a - x) = 0 := by
    rw [residue_eq_zero_iff_lt_one]
    exact ha
  rw [map_sub, sub_eq_zero] at hz
  exact hz

/-- **The kernel of the reduction map is `v`.** -/
theorem ker_residueFieldHom : RingHom.ker (residueFieldHom K v) = v.asIdeal := by
  ext a
  rw [RingHom.mem_ker, residueFieldHom_apply, residue_eq_zero_iff_lt_one,
    algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation' (v := v)]
  exact v.valuation_lt_one_iff_mem (K := K) a

/-- **`R ⧸ v ≃+* 𝒪_v / 𝔪_v`.**  The residue field of the completion at `v` is the residue
field of `R` at `v`. -/
def quotientEquivResidueField :
    (R ⧸ v.asIdeal) ≃+* ResidueField (v.adicCompletionIntegers K) :=
  (Ideal.quotEquivOfEq (ker_residueFieldHom K v).symm).trans
    (RingHom.quotientKerEquivOfSurjective (residueFieldHom_surjective K v))

@[simp] theorem quotientEquivResidueField_mk (a : R) :
    quotientEquivResidueField K v (Ideal.Quotient.mk v.asIdeal a) = residueFieldHom K v a := rfl

/-- **The residue field of `𝒪_v` is finite** for a number field. -/
instance finite_residueField {F : Type*} [Field F] [NumberField F]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Finite (ResidueField (w.adicCompletionIntegers F)) :=
  Finite.of_equiv _ (quotientEquivResidueField F w).toEquiv

end ResidueField

end IsDedekindDomain.HeightOneSpectrum
