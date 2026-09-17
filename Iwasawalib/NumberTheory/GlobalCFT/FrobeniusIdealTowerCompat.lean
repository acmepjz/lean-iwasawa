module

public import Iwasawalib.NumberTheory.GlobalCFT.ArtinMap

@[expose] public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped IsMulCommutative nonZeroDivisors

namespace NumberField

/-- The Frobenius homomorphism on fractional ideals is compatible with restriction to every
finite intermediate field. -/
theorem restrictNormalHom_frobIdealHom
    (F K : Type*) [Field F] [NumberField F] [Field K] [Algebra F K]
    [IsAbelianGalois F K] [IsUnramifiedEverywhere F K]
    (E : IntermediateField F K) [FiniteDimensional F E]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    AlgEquiv.restrictNormalHom E (frobIdealHom F K I) = frobIdealHom F E I := by
  classical
  let r : Gal(K/F) →* Gal(E/F) := AlgEquiv.restrictNormalHom (F := F) E
  change r (∏ᶠ p : HeightOneSpectrum (𝓞 F),
      frobAt (K := K) p ^ FractionalIdeal.count F p
        (I : FractionalIdeal (𝓞 F)⁰ F)) =
    ∏ᶠ p : HeightOneSpectrum (𝓞 F),
      frobAt (K := E) p ^ FractionalIdeal.count F p
        (I : FractionalIdeal (𝓞 F)⁰ F)
  rw [MonoidHom.map_finprod r (finite_mulSupport_frobAt_zpow F K
    (I : FractionalIdeal (𝓞 F)⁰ F))]
  apply finprod_congr
  intro p
  rw [map_zpow, restrictNormalHom_frobAt (K := K) p E]
  rw [frobAt_eq_globalFrobAt (F := F) (K := E) p]

end NumberField
