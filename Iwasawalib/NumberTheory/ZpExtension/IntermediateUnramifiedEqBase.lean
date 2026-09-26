module

public import Iwasawalib.NumberTheory.ZpExtension.RamifiedFamily
public import Iwasawalib.NumberTheory.ZpExtension.Ln
public import Iwasawalib.NumberTheory.ZpExtension.LinearDisjoint

@[expose] public section

open IntermediateField

universe u v

namespace IntermediateField

/- An everywhere-unramified intermediate field of a totally ramified layer is
   the base field.  The conclusion is expressed as `⊥` over the layer base. -/
theorem intermediateField_eq_bot_of_totallyRamified_of_isUnramifiedEverywhere
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (A : IntermediateField F L) [IsGalois F A]
    [FiniteDimensional F A]
    [NumberField.IsUnramifiedEverywhere F A]
    (htot : ∀ w : AbsoluteValue A ℝ, w.inertiaSubgroup F = ⊤) :
    A = ⊥ := by
  classical
  have hbot : ∀ w : AbsoluteValue A ℝ, w.inertiaSubgroup F = ⊥ :=
    fun w ↦ AbsoluteValue.inertiaSubgroup_eq_bot_of_isUnramifiedEverywhere F w
  have hgal : (⊤ : Subgroup (Gal(↥A / F))) = ⊥ := by
    let w : AbsoluteValue A ℝ := AbsoluteValue.trivial
    exact (htot w).symm.trans (hbot w)
  haveI : Subsingleton (Gal(↥A / F)) := by
    constructor
    intro σ τ
    have hσ : σ ∈ (⊥ : Subgroup (Gal(↥A / F))) := by
      rw [← hgal]
      exact Subgroup.mem_top _
    have hτ : τ ∈ (⊥ : Subgroup (Gal(↥A / F))) := by
      rw [← hgal]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_bot.mp hσ).trans (Subgroup.mem_bot.mp hτ).symm
  apply finrank_eq_one_iff.mp
  rw [← IsGalois.card_aut_eq_finrank F A]
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩

/- Once the intermediate field is the base, the generic Mathlib bridge gives
   the corresponding linear-disjointness conclusion. -/
theorem linearDisjoint_of_intermediateField_eq_bot
    {F E' : Type*} [Field F] [Field E'] [Algebra F E']
    (A B : IntermediateField F E')
  [IsGalois F A] [FiniteDimensional F A] [FiniteDimensional F B]
  (hB : B = ⊥) : A.LinearDisjoint B := by
  rw [hB]
  exact IntermediateField.LinearDisjoint.bot_right A

end IntermediateField
