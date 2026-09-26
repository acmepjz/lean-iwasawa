module

public import Iwasawalib.NumberTheory.ZpExtension.Ln
public import Iwasawalib.NumberTheory.GlobalCFT.ArtinMap

@[expose] public section

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf]
  [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

omit [Fact p.Prime] in
theorem natCard_gal_of_finrank_eq
    {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsGalois F L]
    (hdegree : Module.finrank F L =
      p ^ multiplicity p (NumberField.classNumber F)) :
    Nat.card Gal(L / F) =
      p ^ multiplicity p (NumberField.classNumber F) := by
  rw [IsGalois.card_aut_eq_finrank, hdegree]

end MvZpExtension

namespace NumberField

theorem natCard_gal_eq_classNumber_of_artin_bijective
    {F K : Type*} [Field F] [NumberField F] [Field K] [Algebra F K]
    [IsAbelianGalois F K] [IsUnramifiedEverywhere F K]
    (hrec : NumberField.IsArtinReciprocal F K)
    (hgen : Function.Surjective (NumberField.frobIdealHom F K))
    (hinj : Function.Injective (NumberField.artinMapOfReciprocal F K hrec)) :
    Nat.card Gal(K / F) = NumberField.classNumber F := by
  have hbij : Function.Bijective (NumberField.artinMapOfReciprocal F K hrec) :=
    ⟨hinj, NumberField.surjective_artinMapOfReciprocal F K hrec hgen⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  simp [NumberField.classNumber, Nat.card_eq_fintype_card]

end NumberField
