/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.GlobalReciprocity
public import Iwasawalib.NumberTheory.LocalCFT.LocalReciprocity

set_option maxHeartbeats 8000000

/-!
# Local-global normalization of abstract global reciprocity

This file states the available global arithmetic compatibility contract for the abstract
Tate--Nakayama reciprocity map.  Local compatibility at a single finite place and equality on
all ideles are deliberately separate assertions: the latter also controls the order-zero and
archimedean components and does not follow from an algebraic finite-product argument.

Existence of a datum satisfying these fields is the remaining deep global class-field-theory
boundary and is deliberately not asserted here.
-/

@[expose] public noncomputable section

namespace NumberField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [IsAbelianGalois F L] [FiniteDimensional F L] [IsUnramifiedEverywhere F L]

/-- Local-global compatibility for the abstract reciprocity map attached to one fixed
idele-class formation datum.  At every finite place, its value on a single-place idele agrees
with the normalized local Artin map, after inclusion of the decomposition group into
`Gal(L/F)`.

This proposition is only the single-place compatibility square.  It makes no assertion about
general ideles or about their order-zero and archimedean components. -/
structure GlobalReciprocityMapLocalCompatibility
    (D : IdeleClassFormationData F L) : Prop where
  singleIdele_localArtin :
    ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
      (w : HeightOneSpectrum (NumberField.RingOfIntegers L))
      [w.asIdeal.LiesOver v.asIdeal] [Fintype (decompositionGroup F L w)]
      (x : (v.adicCompletion F)ˣ),
      globalReciprocityMap F L D
          (IdeleClassGroup.mk (NumberField.RingOfIntegers F) F
            (IdeleGroup.singleIdele v x)) =
        ((localArtinHom v w
            (ramificationIdx'_eq_one_of_isUnramifiedEverywhere w v) x :
              decompositionGroup F L w) : Gal(L/F))

/-- The local-global compatibility square gives the arithmetic-Frobenius formula on a single
finite-place idele.  The exponent is the normalized `ordCompletion`, with no inversion. -/
theorem globalReciprocityMap_singleIdele
    (D : IdeleClassFormationData F L)
    (hD : GlobalReciprocityMapLocalCompatibility F L D)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (x : (v.adicCompletion F)ˣ) :
    globalReciprocityMap F L D
        (IdeleClassGroup.mk (NumberField.RingOfIntegers F) F
          (IdeleGroup.singleIdele v x)) =
      frobAt (K := L) v ^ v.ordCompletion F (x : v.adicCompletion F) := by
  obtain ⟨w, hw⟩ := exists_heightOneSpectrum_under_eq' F L v
  letI : w.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩
  letI : Fintype (decompositionGroup F L w) := Fintype.ofFinite _
  let hram := ramificationIdx'_eq_one_of_isUnramifiedEverywhere w v
  have hlocal := hD.singleIdele_localArtin v w x
  have hArtin :
      ((localArtinHom v w hram x : decompositionGroup F L w) : Gal(L/F)) =
        (arithFrobAt (NumberField.RingOfIntegers F) Gal(L/F) w.asIdeal) ^
          v.ordCompletion F (x : v.adicCompletion F) := by
    exact congrArg (fun g : decompositionGroup F L w => (g : Gal(L/F)))
      (localArtinHom_apply v w hram x)
  have hFrob :
      arithFrobAt (NumberField.RingOfIntegers F) Gal(L/F) w.asIdeal =
        frobAt (K := L) v := by
    exact (globalFrobAt_eq F L v w hw).symm.trans
      (frobAt_eq_globalFrobAt (F := F) (K := L) v).symm
  calc
    globalReciprocityMap F L D
        (IdeleClassGroup.mk (NumberField.RingOfIntegers F) F
          (IdeleGroup.singleIdele v x)) =
        ((localArtinHom v w hram x : decompositionGroup F L w) : Gal(L/F)) := hlocal
    _ = (arithFrobAt (NumberField.RingOfIntegers F) Gal(L/F) w.asIdeal) ^
          v.ordCompletion F (x : v.adicCompletion F) := hArtin
    _ = frobAt (K := L) v ^ v.ordCompletion F (x : v.adicCompletion F) :=
      congrArg (fun g : Gal(L/F) => g ^ v.ordCompletion F (x : v.adicCompletion F)) hFrob

/-- A normalized global idele-class formation datum.

The only map in this structure is the canonical `globalReciprocityMap F L D` constructed from
the same field `D`.  The local field records the single-place local-global square, while
`globalReciprocityMap_mk` is the genuinely stronger equality on every idele, including
order-zero and archimedean components.  This structure does not assert that such a datum exists. -/
structure NormalizedIdeleClassFormationData where
  toIdeleClassFormationData : IdeleClassFormationData F L
  localCompatibility :
    GlobalReciprocityMapLocalCompatibility F L toIdeleClassFormationData
  globalReciprocityMap_mk :
    ∀ a : IdeleGroup (NumberField.RingOfIntegers F) F,
      globalReciprocityMap F L toIdeleClassFormationData
          (IdeleClassGroup.mk (NumberField.RingOfIntegers F) F a) =
        frobIdeleHom F L a

end NumberField
