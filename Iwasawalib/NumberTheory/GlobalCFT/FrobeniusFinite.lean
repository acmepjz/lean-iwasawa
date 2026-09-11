/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.GlobalFrobenius
public import Iwasawalib.NumberTheory.LocalCFT.PlaceDedekind
public import Mathlib.NumberTheory.NumberField.ClassNumber

@[expose] public section

/-!
# The Frobenius element of a finite unramified abelian extension

Let `L / F` be a **finite** unramified abelian extension of number fields.  Mathlib's
`arithFrobAt (𝓞 F) Gal(L/F) P.asIdeal` is a Frobenius element at a prime `P` of `𝓞 L`, chosen
by `Classical.choose` and characterised only up to conjugacy in general.  This file shows that
in the present situation it is canonical in both respects.

## Main statements

* `NumberField.globalFrobAt` : `Frob_p ∈ Gal(L/F)` for `p` a prime of `𝓞 F`, together with
  `NumberField.globalFrobAt_eq`, which says it is `arithFrobAt (𝓞 F) Gal(L/F) P.asIdeal` for
  *every* prime `P` of `𝓞 L` above `p`.  Independence of `P` is
  `NumberField.arithFrobAt_eq_of_under_eq` of
  `Iwasawalib/NumberTheory/LocalCFT/GlobalFrobenius.lean`, restated here without the
  `Type`-universe restriction of that file.
* `NumberField.inertia_eq_bot_of_isUnramifiedEverywhere` : the inertia subgroup at a prime of an
  everywhere unramified extension is trivial.  This consumes the place/Dedekind ramification
  bridge `NumberField.ramificationIdx'_under_eq_one_of_isUnramifiedEverywhere` of
  `Iwasawalib/NumberTheory/LocalCFT/PlaceDedekind.lean`.
* `NumberField.eq_globalFrobAt_of_isArithFrobAt` : consequently `Frob_p` is the **unique**
  element of `Gal(L/F)` which is an arithmetic Frobenius at a prime above `p`.  This uniqueness,
  and not the `Classical.choose` of `arithFrobAt`, is what makes the Frobenius computable in a
  tower (`Iwasawalib/NumberTheory/GlobalCFT/FrobeniusTower.lean`) and hence extendable to
  infinite extensions (`Iwasawalib/NumberTheory/GlobalCFT/FrobeniusInfinite.lean`).
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped IsMulCommutative nonZeroDivisors

namespace NumberField

variable (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

/-- Every prime of `𝓞 F` lies under a prime of `𝓞 L` (universe-polymorphic restatement of
`NumberField.exists_heightOneSpectrum_under_eq`). -/
theorem exists_heightOneSpectrum_under_eq' (p : HeightOneSpectrum (𝓞 F)) :
    ∃ P : HeightOneSpectrum (𝓞 L), P.asIdeal.under (𝓞 F) = p.asIdeal := by
  haveI : p.asIdeal.IsPrime := p.isPrime
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ := p.asIdeal.nonempty_primesOver (S := 𝓞 L)
  exact ⟨⟨Q, hQ1, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q⟩, (Ideal.over_def Q p.asIdeal).symm⟩

variable [IsAbelianGalois F L]

/-- In an abelian extension the arithmetic Frobenius depends only on the prime below
(universe-polymorphic restatement of `NumberField.arithFrobAt_eq_of_under_eq`). -/
theorem arithFrobAt_eq_of_under_eq' (P P' : HeightOneSpectrum (𝓞 L))
    (h : P.asIdeal.under (𝓞 F) = P'.asIdeal.under (𝓞 F)) :
    arithFrobAt (𝓞 F) Gal(L/F) P.asIdeal = arithFrobAt (𝓞 F) Gal(L/F) P'.asIdeal := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_arithFrobAt (𝓞 F) Gal(L/F) P.asIdeal P'.asIdeal h)
  rw [← hc, mul_comm' c, mul_assoc, mul_inv_cancel, mul_one]

/-- **The global Frobenius at a prime of the base field** of a finite abelian extension of
number fields: the arithmetic Frobenius at any prime of `𝓞 L` above `p`. -/
def globalFrobAt (p : HeightOneSpectrum (𝓞 F)) : Gal(L/F) :=
  arithFrobAt (𝓞 F) Gal(L/F) (exists_heightOneSpectrum_under_eq' F L p).choose.asIdeal

theorem globalFrobAt_eq (p : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 L))
    (h : P.asIdeal.under (𝓞 F) = p.asIdeal) :
    globalFrobAt F L p = arithFrobAt (𝓞 F) Gal(L/F) P.asIdeal :=
  arithFrobAt_eq_of_under_eq' F L _ _
    (((exists_heightOneSpectrum_under_eq' F L p).choose_spec).trans h.symm)

theorem isArithFrobAt_globalFrobAt (p : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 L))
    (h : P.asIdeal.under (𝓞 F) = p.asIdeal) :
    IsArithFrobAt (𝓞 F) (globalFrobAt F L p) P.asIdeal := by
  rw [globalFrobAt_eq F L p P h]
  exact IsArithFrobAt.arithFrobAt (𝓞 F) Gal(L/F) P.asIdeal

/-! ### Uniqueness of the Frobenius at an unramified prime -/

variable [IsUnramifiedEverywhere F L]

/-- At an unramified prime the inertia subgroup is trivial. -/
theorem inertia_eq_bot_of_isUnramifiedEverywhere (P : HeightOneSpectrum (𝓞 L)) :
    P.asIdeal.inertia Gal(L/F) = ⊥ := by
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : (under (𝓞 F) P).asIdeal.IsPrime := (under (𝓞 F) P).isPrime
  rw [← Subgroup.card_eq_one]
  rw [Ideal.card_inertia_eq_ramificationIdxIn (under (𝓞 F) P).asIdeal P.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx (under (𝓞 F) P).asIdeal P.asIdeal Gal(L/F),
    ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (under (𝓞 F) P).ne_bot]
  exact ramificationIdx'_under_eq_one_of_isUnramifiedEverywhere P

/-- **The Frobenius at an unramified prime is unique.** -/
theorem eq_globalFrobAt_of_isArithFrobAt (p : HeightOneSpectrum (𝓞 F))
    (P : HeightOneSpectrum (𝓞 L)) (h : P.asIdeal.under (𝓞 F) = p.asIdeal)
    (σ : Gal(L/F)) (hσ : IsArithFrobAt (𝓞 F) σ P.asIdeal) : σ = globalFrobAt F L p := by
  have key : σ * (globalFrobAt F L p)⁻¹ ∈ P.asIdeal.inertia Gal(L/F) :=
    hσ.mul_inv_mem_inertia (isArithFrobAt_globalFrobAt F L p P h)
  rw [inertia_eq_bot_of_isUnramifiedEverywhere F L P, Subgroup.mem_bot, mul_inv_eq_one] at key
  exact key

end NumberField
