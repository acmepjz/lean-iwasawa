/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Algebra.Group.TypeTags.Basic

@[expose] public section

/-!
# Pro-`p` topological groups

A topological group `G` is *pro-`p`* when every neighbourhood `U` of `1` contains `g ^ p ^ n`
for every `g : G`, for some `n` depending only on `U`.  For a profinite group this is
equivalent to the usual definition (every open normal subgroup has `p`-power index): the
quotient by an open normal subgroup is a finite `p`-group, hence killed by `p ^ n` with
`p ^ n` its order, and conversely.  The formulation below is the *uniform* one, which is the
one every analytic argument actually uses, and which is what one gets directly from the
Galois-theoretic side (see
`Iwasawalib.NumberTheory.ZpExtension.ProPGalois`).

Mathlib has no pro-`p` predicate as of 2026-09; this file supplies one.

## Main definitions

* `IsProP p G` and its additive version `IsAddProP p A`.
* `IsProP.exists_forall_le`: the exponent can be taken cofinally large.
* `isProP_additive_iff`: `Additive G` is pro-`p` iff `G` is.
-/

open Topology Filter

variable (p : ℕ)

/-- A topological group is *pro-`p`* if every neighbourhood of `1` contains `g ^ p ^ n` for
all `g`, for some `n` depending only on the neighbourhood. -/
@[to_additive IsAddProP /-- An additive topological group is *pro-`p`* if every
neighbourhood of `0` contains `p ^ n • x` for all `x`, for some `n` depending only on the
neighbourhood. -/]
def IsProP (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U ∈ 𝓝 (1 : G), ∃ n : ℕ, ∀ g : G, g ^ p ^ n ∈ U

variable {p}

namespace IsProP

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- In the definition of `IsProP` the exponent may be taken arbitrarily large. -/
@[to_additive /-- In the definition of `IsAddProP` the exponent
may be taken arbitrarily large. -/]
theorem exists_forall_le (hG : IsProP p G) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ g : G, g ^ p ^ n ∈ U := by
  obtain ⟨N, hN⟩ := hG U hU
  refine ⟨N, fun n hn g ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have : g ^ p ^ (N + k) = (g ^ p ^ k) ^ p ^ N := by
    rw [← pow_mul, ← pow_add, Nat.add_comm]
  rw [this]
  exact hN _

/-- In a pro-`p` group, `g ^ p ^ n → 1`.  This is the hypothesis `hγ` of
`IwasawaAlgebra.gammaLambdaModule`. -/
@[to_additive /-- In a pro-`p` additive group, `p ^ n • x → 0`.  This is the hypothesis `hγ`
of `IwasawaAlgebra.gammaLambdaModule`. -/]
theorem tendsto_pow (hG : IsProP p G) (g : G) :
    Filter.Tendsto (fun n : ℕ ↦ g ^ p ^ n) Filter.atTop (𝓝 (1 : G)) := by
  intro U hU
  obtain ⟨N, hN⟩ := hG.exists_forall_le hU
  exact Filter.mem_map.2 ((Filter.eventually_ge_atTop N).mono fun n hn ↦ hN n hn g)

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- Pro-`p` pulls back along a group homomorphism whose source topology is coarser than the
pullback topology at `1` — for instance along the inclusion of a subgroup. -/
@[to_additive /-- Pro-`p` pulls back along an additive group homomorphism whose source
topology is coarser than the pullback topology at `0`. -/]
theorem comap (hH : IsProP p H) (f : G →* H) (hf : Filter.comap f (𝓝 1) ≤ 𝓝 (1 : G)) :
    IsProP p G := by
  intro U hU
  obtain ⟨W, hW, hWU⟩ := Filter.mem_comap.1 (hf hU)
  obtain ⟨n, hn⟩ := hH W hW
  exact ⟨n, fun g ↦ hWU (by simpa only [Set.mem_preimage, map_pow] using hn (f g))⟩

/-- A subgroup of a pro-`p` group is pro-`p`. -/
@[to_additive /-- An additive subgroup of a pro-`p` additive group is pro-`p`. -/]
theorem subgroup (hG : IsProP p G) (K : Subgroup G) : IsProP p K := by
  refine hG.comap K.subtype ?_
  have h : 𝓝 (1 : K) = Filter.comap (Subtype.val : K → G) (𝓝 ((1 : K) : G)) :=
    IsInducing.subtypeVal.nhds_eq_comap (1 : K)
  simp only [Subgroup.coe_one] at h
  exact h.ge

/-- A continuous surjective image of a pro-`p` group is pro-`p`; in particular a topological
quotient of a pro-`p` group is pro-`p`. -/
@[to_additive /-- A continuous surjective image of a pro-`p` additive group is pro-`p`. -/]
theorem map (hG : IsProP p G) (f : G →* H) (hf : Continuous f)
    (hsurj : Function.Surjective f) : IsProP p H := by
  intro U hU
  have hpre : f ⁻¹' U ∈ 𝓝 (1 : G) := by
    refine hf.continuousAt (x := (1 : G)) ?_
    simpa using hU
  obtain ⟨n, hn⟩ := hG _ hpre
  refine ⟨n, fun h ↦ ?_⟩
  obtain ⟨g, rfl⟩ := hsurj h
  rw [← map_pow]
  exact hn g

end IsProP

/-- `Additive G` is pro-`p` exactly when `G` is. -/
theorem isAddProP_additive_iff {G : Type*} [Group G] [TopologicalSpace G] :
    IsAddProP p (Additive G) ↔ IsProP p G := Iff.rfl

/-- `Multiplicative A` is pro-`p` exactly when `A` is. -/
theorem isProP_multiplicative_iff {A : Type*} [AddGroup A] [TopologicalSpace A] :
    IsProP p (Multiplicative A) ↔ IsAddProP p A := Iff.rfl
