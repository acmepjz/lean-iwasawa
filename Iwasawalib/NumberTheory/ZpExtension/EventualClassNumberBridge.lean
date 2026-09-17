module

import Iwasawalib.NumberTheory.ZpExtension.XnIsomQuot
import Iwasawalib.NumberTheory.ZpExtension.ClassNumberGrowth

open Module PowerSeries
open scoped Pointwise

namespace MvZpExtension

variable {p : ℕ} [hp : Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf]
  [IsGalois K Kinf]
variable (H : MvZpExtension p ι K Kinf)

structure EventualClassNumberCardinalityBridge (e : ℕ) : Prop where
  card_gal_Ln'_eq_classNumber_pow :
    ∀ n : ℕ, e ≤ n →
      Nat.card Gal(↥(H.Ln' n) / Kinf) =
        p ^ multiplicity p (NumberField.classNumber (H.Kn n))

theorem multiplicity_classNumber_Kn_eq₁_of_eventual_card_bridge
    [Unique ι] {M : Type*}
    [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M]
    [Module.Finite ℤ_[p]⟦X⟧ M]
    (hM : Module.IsTorsion ℤ_[p]⟦X⟧ M)
    (Y : Submodule ℤ_[p]⟦X⟧ M) [Finite (M ⧸ Y)] (e : ℕ)
    (hfin : ∀ n, e ≤ n → Finite (M ⧸
      (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y)))
    (hcard : ∀ n, e ≤ n → Nat.card (M ⧸
      (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y)) =
      p ^ multiplicity p (NumberField.classNumber (H.Kn n))) :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n > N,
      multiplicity p (NumberField.classNumber (H.Kn n)) =
        mu * p ^ n + lambda * n + nu := by
  exact H.exists_multiplicity_classNumber_of_card_eq hM Y e hfin hcard

end MvZpExtension
