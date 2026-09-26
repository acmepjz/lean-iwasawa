module

public import Iwasawalib.NumberTheory.GlobalCFT.ArtinMap
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.ClassFieldTheory
public import Iwasawalib.NumberTheory.ZpExtension.ClassNumberGrowth
public import Iwasawalib.NumberTheory.ZpExtension.XinfSubmodule

@[expose] public section

/-!
# Conditional adapters — **do not build on this file**

**Warning.** The hypotheses packaged here are **false in general**, and nothing downstream
should depend on them.

* `MvZpExtension.ClassNumberCardinalityBridge` demands
  `Nat.card Gal(L_n' / K∞) = p ^ multiplicity p (classNumber K_n)` for **all** `n`, including
  `n = 0`.  This fails whenever `K₁ / K` is unramified: then the Hilbert `p`-class field of `K`
  meets `K∞` nontrivially and the equality already breaks at `n = 0`.  The correct statement is
  only *eventual* (for `n ≥ e`, once the relevant places are totally ramified in `K∞ / K_e`).
* The hypotheses `hTYe` / `hTYn` of
  `MvZpExtension.card_nu_smul_YnSubmodule_eq_classNumber_pow_of_bridge` say that
  `γ - 1` kills `X∞` modulo `Y_n`, i.e. that `Γ` acts trivially on `X_n`, i.e. that
  `Gal(K∞ L_n / K)` is abelian.  This is false in general.

The interface actually used by the class-number formula is
`MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_eventual_Yn_data` in
`Iwasawalib/NumberTheory/ZpExtension/EventualClassNumberBridge.lean`, which is formulated with
an eventual bridge (`MvZpExtension.EventualClassNumberCardinalityBridge`) and the
`ν_{n,e} Y` presentation.  This file is kept only so that earlier experiments still compile.
-/

open Module PowerSeries
open scoped Pointwise

namespace NumberField

structure UnramifiedCFTInput
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [NumberField F] [IsAbelianGalois F K]
    [IsUnramifiedEverywhere F K] : Prop where
  reciprocity : NumberField.IsArtinReciprocal F K
  frobenius_surjective :
    Function.Surjective (NumberField.frobIdealHom F K)
  artin_injective :
    Function.Injective
      (NumberField.artinMapOfReciprocal F K reciprocity)

end NumberField

namespace MvZpExtension

variable {p : ℕ} [hp : Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf]
  [IsGalois K Kinf]
variable (H : MvZpExtension p ι K Kinf)

structure ClassNumberCardinalityBridge : Prop where
  card_gal_Ln'_eq_classNumber_pow :
    ∀ n : ℕ,
      Nat.card Gal(↥(H.Ln' n) / Kinf) =
        p ^ multiplicity p (NumberField.classNumber (H.Kn n))

theorem card_nu_smul_YnSubmodule_eq_classNumber_pow_of_bridge
    (γ : H.GG ⧸ H.Xinf) (e n : ℕ)
    (hTYe : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ H.YnIn e)
    (hTYn : Subgroup.gammaSubOne H.Xinf H.mul_comm_Xinf' γ ≤ H.YnIn n)
    (hnu :
      letI := H.XinfLambdaModule γ
      (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) •
          H.YnSubmodule γ e hTYe) = H.YnSubmodule γ n hTYn)
    (hbridge : ClassNumberCardinalityBridge H) :
    letI := H.XinfLambdaModule γ
    Nat.card ((Additive ↥H.Xinf) ⧸
      (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) •
        H.YnSubmodule γ e hTYe)) =
      p ^ multiplicity p (NumberField.classNumber (H.Kn n)) := by
  letI := H.XinfLambdaModule γ
  rw [hnu, H.card_quotient_YnSubmodule γ n hTYn,
    hbridge.card_gal_Ln'_eq_classNumber_pow n]

theorem multiplicity_classNumber_Kn_eq₁_of_card_bridge
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
