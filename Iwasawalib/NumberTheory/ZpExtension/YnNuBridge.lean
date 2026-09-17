/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.XinfYeGenerators
public import Iwasawalib.NumberTheory.ZpExtension.ClassNumberGrowth

@[expose] public section

/-!
# The nu bridge for the Yn filtration

This file converts the Z_p-linear-map form of multiplication by nu into scalar
multiplication of the corresponding Lambda-submodules.
-/

open PowerSeries
open scoped Pointwise

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- Convert the `ℤ_p`-linear-map form of multiplication by `ν` into scalar
multiplication of the corresponding `Λ`-submodules. -/
theorem nu_smul_YnSubmodule_eq_of_map_lsmulZp_eq
    (γ : H.GG ⧸ H.Xinf) (e n : ℕ)
    (hTYe : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ H.YnIn e)
    (hTYn : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ H.YnIn n)
    (hmap : letI := H.XinfZpModule
      letI := H.XinfLambdaModule γ
      haveI := H.isScalarTower_Xinf γ
      Submodule.map
        (IwasawaAlgebra.lsmulZp (Additive ↑H.Xinf)
          ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧))
        (H.xinfZpSubmoduleOfSubgroup (H.YnIn e) (H.isClosed_YnIn e)) =
        H.xinfZpSubmoduleOfSubgroup (H.YnIn n) (H.isClosed_YnIn n)) :
    letI := H.XinfLambdaModule γ
    ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) •
      H.YnSubmodule γ e hTYe = H.YnSubmodule γ n hTYn := by
  letI := H.XinfZpModule
  letI := H.XinfLambdaModule γ
  haveI := H.isScalarTower_Xinf γ
  apply Submodule.restrictScalars_injective ℤ_[p]
  rw [← IwasawaAlgebra.map_lsmulZp_restrictScalars_smul]
  calc
    Submodule.map
        (IwasawaAlgebra.lsmulZp (Additive ↑H.Xinf)
          ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧))
        ((H.YnSubmodule γ e hTYe).restrictScalars ℤ_[p]) =
      Submodule.map
        (IwasawaAlgebra.lsmulZp (Additive ↑H.Xinf)
          ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧))
        (H.xinfZpSubmoduleOfSubgroup (H.YnIn e) (H.isClosed_YnIn e)) := by
          congr 1
    _ = H.xinfZpSubmoduleOfSubgroup (H.YnIn n) (H.isClosed_YnIn n) := hmap
    _ = (H.YnSubmodule γ n hTYn).restrictScalars ℤ_[p] := by
      ext x
      rfl


end MvZpExtension
