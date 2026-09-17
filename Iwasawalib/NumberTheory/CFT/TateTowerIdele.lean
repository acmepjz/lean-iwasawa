/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.NormIndexIdele
public import Iwasawalib.NumberTheory.CFT.TateTowerIntermediate

@[expose] public section

/-!
# The interior steps of the chain, bounded by an index of ideles

`Iwasawalib/NumberTheory/CFT/FirstInequalityPrime.lean` bounds the **one-element** chain
`ChainLe T 1 [n]` — the whole of a cyclic extension `L / K` — by an index of ideles of `K`.
`Iwasawalib/NumberTheory/CFT/FirstInequalityTower.lean` however needs the chain condition at
every interior level `a` of the tower `K ⊆ L^⟨σ^a⟩ ⊆ L`, one step per prime factor of
`[L : K]`, and there the relevant idele group is that of the intermediate field
`F = L^⟨σ^a⟩`, not of `K`.

This file does for an arbitrary level `a` what
`NumberField.IdeleClassGroup.index_normSubgroup_dvd_index_sup_of_idele` does for `a = 1`:
the subgroup of `C_F` measured by `CyclicTate.relTateH0 T a p`
(`NumberField.IdeleClassGroup.relTateH0_eq_index_comap`) has index dividing
`[𝕀_F : F^× · D]` for every subgroup `D ≤ 𝕀_F` whose elements are relative norms
`∏_{i < p} σ^{a i} · v` of ideles `v ∈ 𝕀_L` fixed by `σ^{a p}` — that is, of ideles of the next
field up in the tower, `L^⟨σ^{a p}⟩`.

Nothing here identifies the relative norm `∏_{i < p} σ^{a i} · -` with the norm of the
extension `L^⟨σ^{a p}⟩ / L^⟨σ^a⟩`; that is a Galois-correspondence computation and it is not
done in this file.  Everything below is unconditional, and the missing input is the explicit
hypothesis `hD`.

## Main definitions

* `NumberField.IdeleClassGroup.relNormSubgroupMul` : the subgroup of `C_F` measured by
  `relTateH0 T a b`, written multiplicatively.

## Main statements

* `NumberField.IdeleClassGroup.mem_relNormSubgroupMul_iff`,
  `NumberField.IdeleClassGroup.index_relNormSubgroupMul` : its membership and its index.
* `NumberField.IdeleClassGroup.mk_mem_relNormSubgroupMul_of_prod_smul` : the class of a
  relative norm of ideles is a relative norm of classes.
* `NumberField.IdeleClassGroup.relTateH0_dvd_index_sup` : **`relTateH0 T a b` divides
  `[𝕀_F : F^× · D]`** for every subgroup `D` of ideles of `F` whose classes are relative norms.
* `NumberField.IdeleClassGroup.relTateH0_dvd_index_sup_of_idele` : the same from relative norms
  of *ideles*, which is what a place-by-place construction from local norms produces.
* `NumberField.IdeleClassGroup.chainLe_cons_of_idele_norms` : consequently the chain condition
  at level `a`, `ChainLe T a (p :: l)`, follows from such a `D` with
  `[𝕀_F : F^× · D] ≤ p` together with the chain condition at level `a * p`.
-/

noncomputable section

open IsDedekindDomain CyclicTate

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.galIdeleMulDistribMulAction NumberField.galIdeleClassMulDistribMulAction
  CyclicTate.Additive.distribMulActionOfMulDistrib

namespace NumberField.IdeleClassGroup

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **The subgroup of `C_{L^⟨σ^a⟩}` whose index is `CyclicTate.relTateH0 T a b`**, written
multiplicatively: the classes whose image in `C_L` is a relative norm
`∏_{i < b} σ^{a i} · d` of a `σ^{a b}`-invariant class `d`. -/
def relNormSubgroupMul (σ : L ≃ₐ[K] L) (a b : ℕ) :
    Subgroup (IdeleClassGroup (𝓞 (towerField σ a)) (towerField σ a)) :=
  AddSubgroup.toSubgroup'
    ((relNorm (actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) a b).comap
      (baseChangeAdd (towerField σ a) L))

omit [IsGalois K L] in
@[simp] theorem mem_relNormSubgroupMul_iff (σ : L ≃ₐ[K] L) (a b : ℕ)
    (c : IdeleClassGroup (𝓞 (towerField σ a)) (towerField σ a)) :
    c ∈ relNormSubgroupMul σ a b ↔ ∃ d : IdeleClassGroup (𝓞 L) L,
      (σ ^ (a * b)) • d = d ∧
        ∏ i ∈ Finset.range b, (σ ^ (a * i)) • d = baseChange (towerField σ a) L c := by
  rw [relNormSubgroupMul, AddSubgroup.mem_toSubgroup', mem_comap_relNorm_iff]
  rfl

omit [IsGalois K L] in
@[simp] theorem index_relNormSubgroupMul (σ : L ≃ₐ[K] L) (a b : ℕ) :
    (relNormSubgroupMul σ a b).index =
      ((relNorm (actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) a b).comap
        (baseChangeAdd (towerField σ a) L)).index := by
  rw [← Subgroup.index_toAddSubgroup]
  rfl

omit [IsGalois K L] in
/-- **The class of a relative norm of ideles is a relative norm of classes.** -/
theorem mk_mem_relNormSubgroupMul_of_prod_smul (σ : L ≃ₐ[K] L) (a b : ℕ)
    (u : IdeleGroup (𝓞 (towerField σ a)) (towerField σ a)) (v : IdeleGroup (𝓞 L) L)
    (hinv : (σ ^ (a * b)) • v = v)
    (hv : ∏ i ∈ Finset.range b, (σ ^ (a * i)) • v = IdeleGroup.baseChange (towerField σ a) L u) :
    IdeleClassGroup.mk (𝓞 (towerField σ a)) (towerField σ a) u ∈ relNormSubgroupMul σ a b := by
  refine (mem_relNormSubgroupMul_iff σ a b _).2 ⟨IdeleClassGroup.mk (𝓞 L) L v, ?_, ?_⟩
  · rw [show (σ ^ (a * b)) • IdeleClassGroup.mk (𝓞 L) L v
        = IdeleClassGroup.mk (𝓞 L) L ((σ ^ (a * b)) • v) from
      (galIdeleClassAut_mk (σ ^ (a * b)) v).symm, hinv]
  · rw [baseChange_mk, ← hv, map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ (galIdeleClassAut_mk (σ ^ (a * i)) v).symm

/-- **`relTateH0 T a b` is bounded by an index of ideles of `L^⟨σ^a⟩`.**

If every idele in `D ≤ 𝕀_F`, `F = L^⟨σ^a⟩`, has a class in `C_F` that is a relative norm
`∏_{i < b} σ^{a i} · d` of a `σ^{a b}`-invariant class `d ∈ C_L`, then
`relTateH0 T a b` divides `[𝕀_F : F^× · D]`. -/
theorem relTateH0_dvd_index_sup (σ : L ≃ₐ[K] L) (a b : ℕ)
    (D : Subgroup (IdeleGroup (𝓞 (towerField σ a)) (towerField σ a)))
    (hD : ∀ u ∈ D, ∃ d : IdeleClassGroup (𝓞 L) L, (σ ^ (a * b)) • d = d ∧
      ∏ i ∈ Finset.range b, (σ ^ (a * i)) • d =
        baseChange (towerField σ a) L
          (IdeleClassGroup.mk (𝓞 (towerField σ a)) (towerField σ a) u)) :
    relTateH0 (actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) a b ∣
      (IdeleGroup.principalSubgroup (𝓞 (towerField σ a)) (towerField σ a) ⊔ D).index := by
  rw [relTateH0_eq_index_comap, ← index_relNormSubgroupMul]
  have h := Subgroup.index_dvd_index_sup_ker
    (IdeleClassGroup.mk (𝓞 (towerField σ a)) (towerField σ a))
    (IdeleClassGroup.mk_surjective (𝓞 (towerField σ a)) (towerField σ a))
    (relNormSubgroupMul σ a b) D fun u hu ↦ (mem_relNormSubgroupMul_iff σ a b _).2 (hD u hu)
  rwa [IdeleClassGroup.ker_mk] at h

/-- **`relTateH0 T a b` is bounded by an index of ideles, from relative norms of ideles.**

The convenient form of `NumberField.IdeleClassGroup.relTateH0_dvd_index_sup`: it suffices that
every `u ∈ D` be the relative norm `∏_{i < b} σ^{a i} · v` of an *idele* `v ∈ 𝕀_L` fixed by
`σ^{a b}`, i.e. of an idele of `L^⟨σ^{a b}⟩`. -/
theorem relTateH0_dvd_index_sup_of_idele (σ : L ≃ₐ[K] L) (a b : ℕ)
    (D : Subgroup (IdeleGroup (𝓞 (towerField σ a)) (towerField σ a)))
    (hD : ∀ u ∈ D, ∃ v : IdeleGroup (𝓞 L) L, (σ ^ (a * b)) • v = v ∧
      ∏ i ∈ Finset.range b, (σ ^ (a * i)) • v = IdeleGroup.baseChange (towerField σ a) L u) :
    relTateH0 (actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) a b ∣
      (IdeleGroup.principalSubgroup (𝓞 (towerField σ a)) (towerField σ a) ⊔ D).index :=
  relTateH0_dvd_index_sup σ a b D fun u hu ↦
    let ⟨v, hinv, hv⟩ := hD u hu
    (mem_relNormSubgroupMul_iff σ a b _).1
      (mk_mem_relNormSubgroupMul_of_prod_smul σ a b u v hinv hv)

/-- **The chain condition at an interior level, granted a subgroup of norm ideles.**

The interior-level analogue of
`NumberField.IdeleClassGroup.chainLe_singleton_of_idele_norms`: at level `a` of the tower the
chain step `p` follows from a subgroup `D ≤ 𝕀_F`, `F = L^⟨σ^a⟩`, of relative norms of ideles of
`L^⟨σ^{a p}⟩` with `[𝕀_F : F^× · D]` finite and at most `p`. -/
theorem chainLe_cons_of_idele_norms (σ : L ≃ₐ[K] L) (a p : ℕ) (l : List ℕ)
    (D : Subgroup (IdeleGroup (𝓞 (towerField σ a)) (towerField σ a)))
    (hD : ∀ u ∈ D, ∃ v : IdeleGroup (𝓞 L) L, (σ ^ (a * p)) • v = v ∧
      ∏ i ∈ Finset.range p, (σ ^ (a * i)) • v = IdeleGroup.baseChange (towerField σ a) L u)
    (hpos : 0 < (IdeleGroup.principalSubgroup (𝓞 (towerField σ a)) (towerField σ a) ⊔ D).index)
    (hle : (IdeleGroup.principalSubgroup (𝓞 (towerField σ a)) (towerField σ a) ⊔ D).index ≤ p)
    (hchain : ChainLe (actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) (a * p) l) :
    ChainLe (actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) a (p :: l) := by
  have hdvd := relTateH0_dvd_index_sup_of_idele σ a p D hD
  refine (chainLe_cons _ a p l).2 ⟨?_, ?_, hchain⟩
  · rcases Nat.eq_zero_or_pos
      (relTateH0 (actEnd (M := Additive (IdeleClassGroup (𝓞 L) L)) σ) a p) with h | h
    · rw [h] at hdvd
      exact absurd (Nat.eq_zero_of_zero_dvd hdvd) hpos.ne'
    · exact h
  · exact le_trans (Nat.le_of_dvd hpos hdvd) hle

end NumberField.IdeleClassGroup

end
