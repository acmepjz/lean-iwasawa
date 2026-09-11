/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.NormIndexIdele
public import Iwasawalib.NumberTheory.CFT.TateTower

@[expose] public section

/-!
# The single step of the chain, in classical norm-index language

`Iwasawalib/NumberTheory/CFT/FirstInequalityTower.lean` reduces the first fundamental
inequality for a cyclic extension to a `CyclicTate.ChainLe` hypothesis, one step per prime
factor of `[L : K]`.  This file translates the **one-element** chain — which is the whole of the
hypothesis when `[L : K]` is itself prime — into the classical statement

`[C_K : N_{L/K} C_L] ≤ [L : K]`,

and then combines it with the idele-theoretic reduction of
`Iwasawalib/NumberTheory/CFT/NormIndexIdele.lean`: the chain condition follows from the
existence of a subgroup `D ≤ 𝕀_K` of ideles whose classes are norms and for which
`[𝕀_K : K^× · D]` is finite and at most `[L : K]`.  Producing such a `D` is Chevalley's
Kummer-theoretic count, and it is **not** proved here; everything in this file is
unconditional, and the missing input appears as explicit hypotheses `hD`, `hpos`, `hle`.

## Main statements

* `NumberField.IdeleClassGroup.chainLe_singleton_iff` :
  `ChainLe T 1 [n] ↔ 0 < [C_K : N C_L] ∧ [C_K : N C_L] ≤ n`, for `n = #Gal(L/K)`.  An
  equivalence, so the chain condition is neither more nor less than the classical inequality.
* `NumberField.IdeleClassGroup.chainLe_singleton_of_index_sup_le` : the chain condition from a
  subgroup of norm ideles.
* `NumberField.IdeleClassGroup.card_tateH0_le_of_index_sup_le` :
  `#Ĥ⁰(Gal(L/K), C_L) ≤ [L : K]` from the same data.
-/

noncomputable section

open IsDedekindDomain CyclicTate

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.galIdeleMulDistribMulAction NumberField.galIdeleClassMulDistribMulAction
  CyclicTate.Additive.distribMulActionOfMulDistrib

namespace NumberField.IdeleClassGroup

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L] {σ : L ≃ₐ[K] L} {n : ℕ}

/-- **The one-step chain hypothesis is the classical first inequality.**

For a cyclic extension `L / K` with `Gal(L/K) = ⟨σ⟩` of order `n`, the chain condition
`CyclicTate.ChainLe T 1 [n]` — the input to
`NumberField.card_tateH0_ideleClassGroup_le_of_chain` for the one-element chain — holds exactly
when the norm index `[C_K : N_{L/K} C_L]` is finite and at most `n`. -/
theorem chainLe_singleton_iff (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (hcard : Nat.card (L ≃ₐ[K] L) = n) :
    ChainLe (actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) 1 [n] ↔
      (0 < (normSubgroup K L).index ∧ (normSubgroup K L).index ≤ n) := by
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  have hrel : relTateH0 (actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) 1 n
      = (normSubgroup K L).index := by
    rw [← hcard, ← card_tateH0_eq_relTateH0 (M := Additive (IdeleClassGroup (𝓞 L) L)) hσ]
    exact card_tateH0_eq_index_normSubgroup hgen
  rw [chainLe_cons, hrel]
  simp

/-- **The first inequality in prime degree, granted a subgroup of local norms.**

If `D ≤ 𝕀_K` is a subgroup of ideles whose classes in `C_K` are norms from `C_L`, and
`[𝕀_K : K^× · D]` is finite and at most `n = #Gal(L/K)`, then the one-step chain condition
holds, so `NumberField.card_tateH0_ideleClassGroup_le_of_chain` applies. -/
theorem chainLe_singleton_of_index_sup_le (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (hcard : Nat.card (L ≃ₐ[K] L) = n) (D : Subgroup (IdeleGroup (𝓞 K) K))
    (hD : ∀ u ∈ D, ∃ d : IdeleClassGroup (𝓞 L) L,
      ∏ g : L ≃ₐ[K] L, g • d = baseChange K L (IdeleClassGroup.mk (𝓞 K) K u))
    (hpos : 0 < (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ D).index)
    (hle : (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ D).index ≤ n) :
    ChainLe (actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) 1 [n] := by
  have hdvd := index_normSubgroup_dvd_index_sup (L := L) D hD
  refine (chainLe_singleton_iff hgen hcard).2 ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (normSubgroup K L).index with h | h
    · rw [h] at hdvd
      exact absurd (Nat.eq_zero_of_zero_dvd hdvd) hpos.ne'
    · exact h
  · exact le_trans (Nat.le_of_dvd hpos hdvd) hle

/-- **The first fundamental inequality for `L / K`, granted a subgroup of local norms.**

`#Ĥ⁰(Gal(L/K), C_L) ≤ [L : K]` for a cyclic `L / K`, from the same data. -/
theorem card_tateH0_le_of_index_sup_le (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (D : Subgroup (IdeleGroup (𝓞 K) K))
    (hD : ∀ u ∈ D, ∃ d : IdeleClassGroup (𝓞 L) L,
      ∏ g : L ≃ₐ[K] L, g • d = baseChange K L (IdeleClassGroup.mk (𝓞 K) K u))
    (hpos : 0 < (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ D).index)
    (hle : (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ D).index ≤ Nat.card (L ≃ₐ[K] L)) :
    Nat.card (TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      ≤ Nat.card (L ≃ₐ[K] L) :=
  by
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  exact CyclicTate.card_tateH0_le_of_chain hσ [Nat.card (L ≃ₐ[K] L)] (by simp)
    (chainLe_singleton_of_index_sup_le hgen rfl D hD hpos hle)

/-- **The one-step chain condition from a subgroup of norms of ideles.**

The form in which Chevalley's argument delivers its input: `D` consists of ideles that are
norms `∏_{g} g · b` of ideles of `L` — which is what a place-by-place construction from local
norms produces — and `[𝕀_K : K^× · D]` is finite and at most `n = [L : K]`. -/
theorem chainLe_singleton_of_idele_norms (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
    (hcard : Nat.card (L ≃ₐ[K] L) = n) (D : Subgroup (IdeleGroup (𝓞 K) K))
    (hD : ∀ u ∈ D, ∃ b : IdeleGroup (𝓞 L) L,
      ∏ g : L ≃ₐ[K] L, g • b = IdeleGroup.baseChange K L u)
    (hpos : 0 < (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ D).index)
    (hle : (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ D).index ≤ n) :
    ChainLe (actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) 1 [n] :=
  chainLe_singleton_of_index_sup_le hgen hcard D
    (fun u hu ↦ let ⟨b, hb⟩ := hD u hu; mk_mem_normSubgroupMul_of_prod_smul u b hb) hpos hle

end NumberField.IdeleClassGroup

end
