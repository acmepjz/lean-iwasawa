/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.Hilbert90
public import Iwasawalib.GroupCohomology.LocalShapiro

@[expose] public section

/-!
# Hilbert 90 for the local factors of the ideles

Combining `Iwasawalib/GroupCohomology/Hilbert90.lean` (Hilbert 90 for a faithful action of a
finite group on a field) with `Iwasawalib/GroupCohomology/LocalShapiro.lean` (Shapiro's lemma
for `∏_{w ∣ v} L_w`) gives the vanishing of

`H¹(Gal(L/K), ∏_{w ∣ v} L_w^×)`,

the local input at `v` to the first fundamental inequality of class field theory.

The decomposition group `D_{w₀}` acts faithfully on the completion `L_{w₀}`, because `L` is
dense in `L_{w₀}` — concretely, because an element of `D_{w₀}` acting trivially on `L_{w₀}`
acts trivially on the image of `L`, which is injective in `L_{w₀}`.  Hilbert 90 therefore
applies to `D_{w₀}` acting on `L_{w₀}` even though `D_{w₀}` is not presented as the full
automorphism group of a field extension.

## Main statements

* `NumberField.decompositionGroup_smul_injective`: `D_{w₀}` acts faithfully on `L_{w₀}`.
* `NumberField.H1_adicCompletionUnits_eq_zero`: `H¹(D_{w₀}, L_{w₀}^×) = 0`.
* `NumberField.H1_localProductUnits_eq_zero`: `H¹(Gal(L/K), ∏_{w ∣ v} L_w^×) = 0`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CategoryTheory

attribute [local instance] Units.mulDistribMulActionRight

namespace NumberField

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois K L] {v : HeightOneSpectrum (𝓞 K)} {w₀ : HeightOneSpectrum (𝓞 L)}

omit [NumberField K] [IsGalois K L] in
/-- The decomposition group of `w₀` acts faithfully on the completion `L_{w₀}`: an element
acting trivially on `L_{w₀}` acts trivially on `L`, hence is the identity. -/
theorem decompositionGroup_smul_injective (w₀ : HeightOneSpectrum (𝓞 L)) :
    Function.Injective
      fun (d : decompositionGroup K L w₀) ↦ (fun x : w₀.adicCompletion L ↦ d • x) := by
  intro d d' h
  refine Subtype.ext (AlgEquiv.ext fun y ↦ ?_)
  have hy : (d : decompositionGroup K L w₀) • ((y : L) : w₀.adicCompletion L)
      = (d' : decompositionGroup K L w₀) • ((y : L) : w₀.adicCompletion L) := congrFun h _
  rw [decomposition_smul_coe, decomposition_smul_coe] at hy
  exact (algebraMap L (w₀.adicCompletion L)).injective hy

omit [IsGalois K L] in
/-- **Hilbert 90 for the local field `L_{w₀}` and the decomposition group**:
`H¹(D_{w₀}, L_{w₀}^×) = 0`. -/
theorem H1_adicCompletionUnits_eq_zero (w₀ : HeightOneSpectrum (𝓞 L))
    (x : groupCohomology (repAdicCompletionUnits K L w₀) 1) : x = 0 :=
  groupCohomology.H1_units_eq_zero (decompositionGroup_smul_injective w₀) x

/-- **The local factor of the ideles at `v` has trivial `H¹`**:
`H¹(Gal(L/K), ∏_{w ∣ v} L_w^×) = 0`.  This is Hilbert 90 for the local fields `L_w` together
with Shapiro's lemma, and is the local input at `v` to the first fundamental inequality. -/
theorem H1_localProductUnits_eq_zero (hw₀ : w₀ ∈ placesOver K L v)
    (x : groupCohomology (repLocalProductUnits K L v) 1) : x = 0 := by
  set e := localProductUnitsShapiro hw₀ 1 with he
  have hx : e.hom.hom x = 0 := H1_adicCompletionUnits_eq_zero w₀ _
  have hinv : e.inv.hom (e.hom.hom x) = x := Iso.hom_inv_id_apply e x
  rw [← hinv, hx, map_zero]

end NumberField
