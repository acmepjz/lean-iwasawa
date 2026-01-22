/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.FieldTheory.Galois.Abelian
public import Iwasawalib.GroupTheory.Torsion

@[expose] public section

/-!

# Maximal abelian subextension

-/

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

namespace IntermediateField

/-! ### Maximal abelian subextension -/

/-- The maximal abelian subextension of `K / F` is the compositum of all
abelian subextension of `K / F`. -/
def maximalAbelianExtension : IntermediateField F K := sSup {E | IsAbelianGalois F E}

instance isAbelianGalois_maximalAbelianExtension :
    IsAbelianGalois F (maximalAbelianExtension F K) := by
  rw [maximalAbelianExtension, sSup_eq_iSup']
  have (E : {E : IntermediateField F K | IsAbelianGalois F E}) : IsAbelianGalois F E.1 := E.2
  exact IntermediateField.isAbelianGalois_iSup Subtype.val

theorem le_maximalAbelianExtension (E : IntermediateField F K) [IsAbelianGalois F E] :
    E ≤ maximalAbelianExtension F K :=
  le_sSup ‹_›

/-! ### Maximal abelian `p`-subextension -/

variable (p : ℕ)

/-- The maximal abelian `p`-subextension of `K / F` is the compositum of all
abelian subextension of `K / F` whose degree is a power of `p`. -/
def maximalAbelianPExtension : IntermediateField F K :=
  sSup {E | IsAbelianGalois F E ∧ ∃ n, Module.finrank F E = p ^ n}

instance isAbelianGalois_maximalAbelianPExtension :
    IsAbelianGalois F (maximalAbelianPExtension F K p) := by
  rw [maximalAbelianPExtension, sSup_eq_iSup']
  have (E : {E : IntermediateField F K | IsAbelianGalois F E ∧
    ∃ n, Module.finrank F E = p ^ n}) : IsAbelianGalois F E.1 := E.2.1
  exact IntermediateField.isAbelianGalois_iSup Subtype.val

theorem le_maximalAbelianPExtension (E : IntermediateField F K) [IsAbelianGalois F E]
    (h : ∃ n, Module.finrank F E = p ^ n) : E ≤ maximalAbelianPExtension F K p :=
  le_sSup ⟨‹_›, h⟩

variable [Fact p.Prime] [FiniteDimensional F K]

theorem exists_finrank_maximalAbelianPExtension_eq :
    ∃ n, Module.finrank F (maximalAbelianPExtension F K p) = p ^ n := by
  simp_rw [← IsGalois.card_aut_eq_finrank, ← IsPGroup.iff_card, maximalAbelianPExtension]
  rw [sSup_eq_iSup']
  refine fun g ↦ ⟨orderOf g, ?_⟩
  have (E : {E : IntermediateField F K | IsAbelianGalois F E ∧
    ∃ n, Module.finrank F E = p ^ n}) : IsAbelianGalois F E.1 := E.2.1
  let f := IntermediateField.piRestrictNormalHom' fun E : {E : IntermediateField F K |
    IsAbelianGalois F E ∧ ∃ n, Module.finrank F E = p ^ n} ↦ E.1
  have hf : Function.Injective f := IntermediateField.injective_piRestrictNormalHom' _
  apply_fun f using hf
  ext1 E
  simp only [map_pow, Pi.pow_apply, map_one, Pi.one_apply, ← orderOf_dvd_iff_pow_eq_one]
  have h1 : orderOf (f g E) ≤ orderOf g := Nat.le_of_dvd (Nat.pos_of_ne_zero <|
    orderOf_ne_zero_iff.2 <| isOfFinOrder_of_finite g) <| by rw [orderOf_dvd_iff_pow_eq_one,
      ← orderOf_injective f hf g, ← Pi.pow_apply, pow_orderOf_eq_one, Pi.one_apply]
  replace h1 := h1.trans (Nat.lt_pow_self ‹Fact p.Prime›.out.one_lt).le
  obtain ⟨n, hn⟩ := E.2.2
  rw [← IsGalois.card_aut_eq_finrank] at hn
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Fact.out).1 (hn ▸ orderOf_dvd_natCard (f g E))
  rw [hm] at h1 ⊢
  rwa [Nat.pow_dvd_pow_iff_pow_le_pow ‹Fact p.Prime›.out.pos]

variable [IsAbelianGalois F K]

theorem not_dvd_finrank_maximalAbelianPExtension :
    ¬p ∣ Module.finrank (maximalAbelianPExtension F K p) K := fun H ↦ by
  sorry

theorem fixingSubgroup_maximalAbelianPExtension :
    (maximalAbelianPExtension F K p).fixingSubgroup = CommGroup.primeToComponent Gal(K/F) p := by
  sorry

end IntermediateField
