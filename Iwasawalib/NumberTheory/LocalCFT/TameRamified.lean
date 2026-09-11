/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.TameUnits
public import Iwasawalib.NumberTheory.LocalCFT.LocalHerbrand

@[expose] public section

/-!
# The local units at a tamely ramified place

`Iwasawalib/NumberTheory/LocalCFT/Unramified.lean` computes the cohomology of `O_w^×` at an
**unramified** place, where a `D_w`-fixed uniformizer exists.  This file instantiates the
`p`-free computation of `Iwasawalib/NumberTheory/LocalCFT/TameUnits.lean` at an arbitrary —
possibly **ramified** — finite place `w` of `L` whose decomposition group has order prime to
the residue characteristic:

`h(D_w, O_w^×) = 1`  and  `h(D_w, L_w^×) = #D_w = [L_w : K_v]`.

The hypothesis is a natural number `p` lying in `w` (in practice the residue characteristic)
together with a Bézout relation `a · #D_w + b · p = 1`.  This covers every tamely ramified
place with `p ∤ f(w|v)`, and in particular reproves the unramified statement whenever
`p ∤ #D_w`.

**What is not covered.**  When `p ∣ #D_w` — in particular the wildly ramified case `p ∣ e` —
the graded pieces of the unit filtration are `p`-groups on which `p` no longer acts
invertibly, and the classical argument replaces the filtration by the `p`-adic logarithm
isomorphism `1 + 𝔪^m ≅ 𝔪^m`.  Mathlib has no nonarchimedean `exp`/`log` for a complete
discretely valued field of mixed characteristic — only the real, complex and Banach-algebra
exponentials — so that route is not available here and `h(O_w^×) = 1` remains open in the wild
case.

## Main statements

* `NumberField.herbrand_adicCompletionIntegers_units_eq_one_tame`: `h(D_w, O_w^×) = 1`.
* `NumberField.herbrand_adicCompletion_units_eq_card_tame`: `h(D_w, L_w^×) = #D_w`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero LocalCFT
open scoped WithZero

namespace NumberField

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] decompositionIntegersMulSemiringAction
  Units.mulDistribMulActionRight

/-- The decomposition group acts on `O_w` by valuation-preserving ring automorphisms. -/
instance isIsometricSMul_decompositionGroup :
    LocalCFT.IsIsometricSMul (w.adicCompletion L) (decompositionGroup K L w) where
  valued_smul := valued_decomposition_smul_integers w

/-- A natural number lying in `w` has valuation at most `exp (-1)` in `L_w`. -/
theorem valued_natCast_le_of_mem {p : ℕ} (hp : (p : 𝓞 L) ∈ w.asIdeal) :
    (Valued.v ((p : w.adicCompletion L)) : ℤᵐ⁰) ≤ exp (-1 : ℤ) := by
  rw [LocalCFT.le_exp_neg_one_iff_lt_one,
    show ((p : w.adicCompletion L))
      = algebraMap (𝓞 L) (w.adicCompletion L) (p : 𝓞 L) from
      (map_natCast (algebraMap (𝓞 L) (w.adicCompletion L)) p).symm,
    valuedAdicCompletion_eq_valuation (R := 𝓞 L) (K := L) w (p : 𝓞 L)]
  exact (w.valuation_lt_one_iff_mem (K := L) (p : 𝓞 L)).2 hp

variable [Fintype (decompositionGroup K L w)] {σ : decompositionGroup K L w}

omit [NumberField K] [IsGalois K L] in
/-- **`h(D_w, O_w^×) = 1` at a place whose decomposition group has order prime to the residue
characteristic.**  No `D_w`-fixed uniformizer is needed, so this holds at ramified places. -/
theorem herbrand_adicCompletionIntegers_units_eq_one_tame
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ)
    {p : ℕ} (hp : (p : 𝓞 L) ∈ w.asIdeal)
    {a b : ℤ} (hab : a * (Nat.card (decompositionGroup K L w)) + b * p = 1) :
    CyclicTate.herbrand (decompositionGroup K L w)
      (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ = 1 := by
  haveI : Finite (IsLocalRing.ResidueField
      (LocalCFT.integers (F := w.adicCompletion L))) :=
    HeightOneSpectrum.finite_residueField (F := L) w
  haveI := LocalCFT.finite_quotient_unitFiltration_one (F := w.adicCompletion L)
  exact LocalCFT.herbrand_units_eq_one_tame (G := decompositionGroup K L w) hσ
    (valued_natCast_le_of_mem w hp) hab

omit [IsGalois K L] in
/-- **`h(D_w, L_w^×) = #D_w = [L_w : K_v]` at a place whose decomposition group has order prime
to the residue characteristic.**  This is the local input to the second fundamental inequality,
now available at ramified places as well. -/
theorem herbrand_adicCompletion_units_eq_card_tame
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ)
    {p : ℕ} (hp : (p : 𝓞 L) ∈ w.asIdeal)
    {a b : ℤ} (hab : a * (Nat.card (decompositionGroup K L w)) + b * p = 1) :
    CyclicTate.herbrand (decompositionGroup K L w) (Additive (w.adicCompletion L)ˣ) σ
      = (Nat.card (decompositionGroup K L w) : ℚ) := by
  haveI : Finite (IsLocalRing.ResidueField
      (LocalCFT.integers (F := w.adicCompletion L))) :=
    HeightOneSpectrum.finite_residueField (F := L) w
  haveI := LocalCFT.finite_quotient_unitFiltration_one (F := w.adicCompletion L)
  haveI := LocalCFT.finite_tateH0_units_tame (G := decompositionGroup K L w) hσ
    (valued_natCast_le_of_mem w hp) hab
  haveI := LocalCFT.finite_tateH1_units_tame (G := decompositionGroup K L w) hσ
    (valued_natCast_le_of_mem w hp) hab
  have hgen : ∀ d : decompositionGroup K L w, ∃ k : ℕ, σ ^ k = d := by
    intro d
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff d σ).1
      (mem_powers_iff_mem_zpowers.2 (hσ d))
    exact ⟨k, hk⟩
  have hπ : ∃ π : w.adicCompletion L, (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ) :=
    valuedAdicCompletion_surjective (K := L) w (exp (-1 : ℤ))
  rw [LocalCFT.herbrand_units_eq_mul (F := w.adicCompletion L)
      (G := decompositionGroup K L w) (valued_decomposition_smul w)
      (fun d a ↦ rfl) hgen hπ,
    herbrand_adicCompletionIntegers_units_eq_one_tame w hσ hp hab, one_mul]

end NumberField
