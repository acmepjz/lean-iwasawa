/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.GlobalCFT.FrobeniusFinite

@[expose] public section

/-!
# The Frobenius is compatible with restriction

Let `F ⊆ M ⊆ L` be a tower of number fields with `L / F` finite, abelian and unramified
everywhere.  Then the Frobenius of `L / F` at a prime `p` of `𝓞 F` restricts to the Frobenius of
`M / F` at `p`:

`NumberField.restrictNormalHom_globalFrobAt`.

The proof is the uniqueness statement `NumberField.eq_globalFrobAt_of_isArithFrobAt`: the
defining congruence `σ x ≡ x ^ #(𝓞 F / p)` for `x : 𝓞 L` restricts to the same congruence for
`x : 𝓞 M` modulo `P ∩ 𝓞 M`, and at an unramified prime there is only one element of the Galois
group satisfying it.  Nothing of the sort can be read off `arithFrobAt` directly, which is a
`Classical.choose`.

The auxiliary `NumberField.algebraMap_restrictNormalHom_smul` is the equivariance of
`𝓞 M → 𝓞 L` for `AlgEquiv.restrictNormalHom`; it is `AlgEquiv.restrictNormal_commutes`
transported from the fields to their rings of integers.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped IsMulCommutative nonZeroDivisors

namespace NumberField

variable (F M L : Type*) [Field F] [NumberField F] [Field M] [NumberField M]
  [Field L] [NumberField L] [Algebra F M] [Algebra M L] [Algebra F L] [IsScalarTower F M L]
  [IsAbelianGalois F L] [IsUnramifiedEverywhere F L]
  [IsAbelianGalois F M] [IsUnramifiedEverywhere F M]

variable {F M L} in
/-- The inclusion `𝓞 M → 𝓞 L` is equivariant for the restriction `Gal(L/F) → Gal(M/F)`. -/
theorem algebraMap_restrictNormalHom_smul (σ : Gal(L/F)) (x : 𝓞 M) :
    algebraMap (𝓞 M) (𝓞 L) (AlgEquiv.restrictNormalHom M σ • x) =
      σ • algebraMap (𝓞 M) (𝓞 L) x := by
  apply RingOfIntegers.coe_injective (K := L)
  have hl : algebraMap (𝓞 L) L (algebraMap (𝓞 M) (𝓞 L) (AlgEquiv.restrictNormalHom M σ • x))
      = algebraMap M L (algebraMap (𝓞 M) M (AlgEquiv.restrictNormalHom M σ • x)) := by
    rw [← IsScalarTower.algebraMap_apply (𝓞 M) (𝓞 L) L, IsScalarTower.algebraMap_apply (𝓞 M) M L]
  have hr : algebraMap (𝓞 L) L (σ • algebraMap (𝓞 M) (𝓞 L) x)
      = σ (algebraMap M L (algebraMap (𝓞 M) M x)) := by
    show σ (algebraMap (𝓞 L) L (algebraMap (𝓞 M) (𝓞 L) x)) = _
    rw [← IsScalarTower.algebraMap_apply (𝓞 M) (𝓞 L) L, IsScalarTower.algebraMap_apply (𝓞 M) M L]
  rw [hl, hr]
  show algebraMap M L ((AlgEquiv.restrictNormalHom M σ) (algebraMap (𝓞 M) M x)) = _
  exact AlgEquiv.restrictNormal_commutes σ M _

/-- **The Frobenius is compatible with restriction along a tower.** -/
theorem restrictNormalHom_globalFrobAt (p : HeightOneSpectrum (𝓞 F)) :
    AlgEquiv.restrictNormalHom M (globalFrobAt F L p) = globalFrobAt F M p := by
  obtain ⟨P, hP⟩ := exists_heightOneSpectrum_under_eq' F L p
  have hQ : (under (𝓞 M) P).asIdeal.under (𝓞 F) = p.asIdeal := by
    show (P.asIdeal.under (𝓞 M)).under (𝓞 F) = p.asIdeal
    rw [Ideal.under_under]; exact hP
  refine eq_globalFrobAt_of_isArithFrobAt F M p (under (𝓞 M) P) hQ _ fun x => ?_
  have hs := isArithFrobAt_globalFrobAt F L p P hP (algebraMap (𝓞 M) (𝓞 L) x)
  rw [hP] at hs
  show AlgEquiv.restrictNormalHom M (globalFrobAt F L p) • x - x ^ _ ∈ _
  rw [hQ]
  show _ ∈ Ideal.comap (algebraMap (𝓞 M) (𝓞 L)) P.asIdeal
  rw [Ideal.mem_comap, map_sub, map_pow, algebraMap_restrictNormalHom_smul]
  exact hs

end NumberField
