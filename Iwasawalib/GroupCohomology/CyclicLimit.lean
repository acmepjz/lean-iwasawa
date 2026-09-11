/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.CyclicCocycle

@[expose] public section

/-!
# Tate vanishing passes to the limit along a complete filtration

Let `G = ⟨σ⟩` be a finite cyclic group acting on a commutative group `M` which carries a
decreasing filtration by `G`-stable subgroups `M = U₀ ⊇ U₁ ⊇ U₂ ⊇ ⋯` which is *separated*
(`⋂ Uₙ = 1`) and *complete* (a sequence whose consecutive quotients lie in `Uₙ` has a limit).
If the Tate cohomology of every graded piece `Uₙ / Uₙ₊₁` vanishes, then the Tate cohomology of
`M` vanishes.

This is the successive-approximation step of the computation of the cohomology of the units of
a complete local field: for the filtration `O^× ⊇ 1 + 𝔪 ⊇ 1 + 𝔪² ⊇ ⋯`, whose graded pieces are
`k^×` and `k⁺`, the vanishing of the graded Tate cohomology is proved in
`Iwasawalib/GroupCohomology/FiniteFieldTate.lean` and
`Iwasawalib/GroupCohomology/TraceOne.lean`.  Completeness and separatedness are the two
properties of the ring of integers of a complete discretely valued field.

The hypotheses on the graded pieces are phrased elementarily, on representatives, exactly as
they come out of the vanishing statements for the graded pieces:

* `Ĥ¹` : `u ∈ Uₙ` of norm one admits `z ∈ Uₙ` with `u · (σ • z / z) ∈ Uₙ₊₁`;
* `Ĥ⁰` : `u ∈ Uₙ` fixed by `σ` admits `z ∈ Uₙ` with `u / N z ∈ Uₙ₊₁`.

## Main statements

* `CyclicLimit.exists_smul_div_of_mulNorm_eq_one`: `Ĥ¹(G, M) = 0`.
* `CyclicLimit.exists_mulNorm_eq_of_smul_eq`: `Ĥ⁰(G, M) = 0`.
-/

noncomputable section

open Finset CyclicCocycle

namespace CyclicLimit

/-! ## The multiplicative norm is a homomorphism -/

section Norm

variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]

@[simp] theorem mulNorm_mul (x y : M) :
    mulNorm (G := G) (x * y) = mulNorm (G := G) x * mulNorm (G := G) y := by
  simp [mulNorm_def, smul_mul', Finset.prod_mul_distrib]

@[simp] theorem mulNorm_inv (x : M) : mulNorm (G := G) x⁻¹ = (mulNorm (G := G) x)⁻¹ := by
  simp [mulNorm_def]

@[simp] theorem mulNorm_div (x y : M) :
    mulNorm (G := G) (x / y) = mulNorm (G := G) x / mulNorm (G := G) y := by
  rw [div_eq_mul_inv, mulNorm_mul, mulNorm_inv, div_eq_mul_inv]

@[simp] theorem mulNorm_one : mulNorm (G := G) (1 : M) = 1 := by simp [mulNorm_def]

/-- The norm is unchanged by precomposing with the action. -/
theorem mulNorm_smul (g : G) (x : M) : mulNorm (G := G) (g • x) = mulNorm (G := G) x := by
  simp only [mulNorm_def, smul_smul]
  exact Fintype.prod_equiv (Equiv.mulRight g) _ _ fun _ ↦ rfl

/-- The norm of an element is invariant. -/
theorem smul_mulNorm (g : G) (x : M) : g • mulNorm (G := G) x = mulNorm (G := G) x := by
  simp only [mulNorm_def, smul_prod', smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g) _ _ fun _ ↦ rfl

/-- A coboundary has norm one. -/
@[simp] theorem mulNorm_smul_div (g : G) (x : M) : mulNorm (G := G) (g • x / x) = 1 := by
  rw [mulNorm_div, mulNorm_smul, div_self']

end Norm

/-! ## The filtration -/

section Filtration

variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M] {σ : G}
  (U : ℕ → Subgroup M)

/-- The data of a decreasing, `G`-stable, separated and complete filtration of `M`. -/
structure IsCompleteFiltration : Prop where
  /-- the filtration starts at the whole group -/
  top : U 0 = ⊤
  /-- the filtration is decreasing -/
  antitone : ∀ n, U (n + 1) ≤ U n
  /-- every step is `G`-stable -/
  smul_mem : ∀ (n : ℕ) (g : G) {x : M}, x ∈ U n → g • x ∈ U n
  /-- the filtration is separated -/
  separated : ∀ x : M, (∀ n, x ∈ U n) → x = 1
  /-- the filtration is complete: a sequence with `f n / f (n+1) ∈ U n` has a limit -/
  complete : ∀ f : ℕ → M, (∀ n, f n / f (n + 1) ∈ U n) → ∃ y : M, ∀ n, y / f n ∈ U n

variable {U}

namespace IsCompleteFiltration

variable (hU : IsCompleteFiltration (G := G) U)

include hU

omit [Fintype G] in
theorem mem_of_le {m n : ℕ} (hmn : m ≤ n) {x : M} (hx : x ∈ U n) : x ∈ U m := by
  induction n with
  | zero => rwa [Nat.le_zero.1 hmn]
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hmn) with h | h
    · exact ih (Nat.lt_succ_iff.1 h) (hU.antitone n hx)
    · exact h ▸ hx

/-- The norm maps each step of the filtration to itself. -/
theorem mulNorm_mem {n : ℕ} {x : M} (hx : x ∈ U n) : mulNorm (G := G) x ∈ U n := by
  rw [mulNorm_def]
  exact Subgroup.prod_mem _ fun g _ ↦ hU.smul_mem n g hx

omit [Fintype G] in
/-- `σ • x / x` stays in each step of the filtration. -/
theorem smul_div_mem {n : ℕ} {x : M} (hx : x ∈ U n) : σ • x / x ∈ U n :=
  Subgroup.div_mem _ (hU.smul_mem n σ hx) hx

/-! ### `Ĥ¹(G, M) = 0` -/

/-- **Successive approximation for `Ĥ¹`.**  If every graded piece of a complete filtration has
vanishing `Ĥ¹`, then every element of norm one is of the form `σ • y / y`. -/
theorem exists_smul_div_of_mulNorm_eq_one
    (hvanish : ∀ (n : ℕ), ∀ u ∈ U n, mulNorm (G := G) u = 1 →
      ∃ z ∈ U n, u * (σ • z / z) ∈ U (n + 1))
    {x : M} (hx : mulNorm (G := G) x = 1) :
    ∃ y : M, σ • y / y = x := by
  classical
  choose! z hz₁ hz₂ using hvanish
  -- the approximating sequence
  set y : ℕ → M := fun n ↦ Nat.rec (1 : M)
    (fun k yk ↦ yk * z k ((σ • yk / yk) * x⁻¹)) n with hy
  have hy0 : y 0 = 1 := rfl
  have hysucc : ∀ n, y (n + 1) = y n * z n ((σ • y n / y n) * x⁻¹) := fun _ ↦ rfl
  -- the defect of the `n`-th approximation has norm one
  have hnorm : ∀ n : ℕ, mulNorm (G := G) ((σ • y n / y n) * x⁻¹) = 1 := by
    intro n
    rw [mulNorm_mul, mulNorm_smul_div, mulNorm_inv, hx, one_mul, inv_one]
  -- the defect of the `n`-th approximation lies in `U n`
  have hdefect : ∀ n : ℕ, (σ • y n / y n) * x⁻¹ ∈ U n := by
    intro n
    induction n with
    | zero => rw [hU.top]; exact Subgroup.mem_top _
    | succ n ih =>
      have hmem := hz₂ n _ ih (hnorm n)
      rw [hysucc n]
      have : σ • (y n * z n ((σ • y n / y n) * x⁻¹)) /
          (y n * z n ((σ • y n / y n) * x⁻¹)) * x⁻¹ =
          ((σ • y n / y n) * x⁻¹) *
            (σ • z n ((σ • y n / y n) * x⁻¹) / z n ((σ • y n / y n) * x⁻¹)) := by
        rw [smul_mul']
        simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
      rw [this]
      exact hmem
  -- consecutive approximations differ by an element of `U n`
  have hcauchy : ∀ n : ℕ, y n / y (n + 1) ∈ U n := by
    intro n
    rw [hysucc n]
    have : y n / (y n * z n ((σ • y n / y n) * x⁻¹)) =
        (z n ((σ • y n / y n) * x⁻¹))⁻¹ := by
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
    rw [this]
    exact Subgroup.inv_mem _ (hz₁ n _ (hdefect n) (hnorm n))
  obtain ⟨y₀, hy₀⟩ := hU.complete y hcauchy
  refine ⟨y₀, ?_⟩
  have hall : ∀ n : ℕ, (σ • y₀ / y₀) * x⁻¹ ∈ U n := by
    intro n
    have h₁ : (σ • (y₀ / y n) / (y₀ / y n)) ∈ U n := hU.smul_div_mem (hy₀ n)
    have h₂ : (σ • y₀ / y₀) * x⁻¹ =
        (σ • (y₀ / y n) / (y₀ / y n)) * ((σ • y n / y n) * x⁻¹) := by
      rw [smul_div']
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
    rw [h₂]
    exact Subgroup.mul_mem _ h₁ (hdefect n)
  have := hU.separated _ hall
  rwa [mul_inv_eq_one] at this

/-! ### `Ĥ⁰(G, M) = 0` -/

/-- **Successive approximation for `Ĥ⁰`.**  If every graded piece of a complete filtration has
vanishing `Ĥ⁰`, then every `σ`-invariant element is a norm. -/
theorem exists_mulNorm_eq_of_smul_eq
    (hvanish : ∀ (n : ℕ), ∀ u ∈ U n, σ • u = u → ∃ z ∈ U n, u / mulNorm (G := G) z ∈ U (n + 1))
    {x : M} (hx : σ • x = x) :
    ∃ y : M, mulNorm (G := G) y = x := by
  classical
  choose! z hz₁ hz₂ using hvanish
  set y : ℕ → M := fun n ↦ Nat.rec (1 : M)
    (fun k yk ↦ yk * z k (x / mulNorm (G := G) yk)) n with hy
  have hysucc : ∀ n, y (n + 1) = y n * z n (x / mulNorm (G := G) (y n)) := fun _ ↦ rfl
  have hinv : ∀ n : ℕ, σ • (x / mulNorm (G := G) (y n)) = x / mulNorm (G := G) (y n) := by
    intro n
    rw [smul_div', hx, smul_mulNorm]
  have hdefect : ∀ n : ℕ, x / mulNorm (G := G) (y n) ∈ U n := by
    intro n
    induction n with
    | zero => rw [hU.top]; exact Subgroup.mem_top _
    | succ n ih =>
      have hmem := hz₂ n _ ih (hinv n)
      rw [hysucc n, mulNorm_mul]
      have : x / (mulNorm (G := G) (y n) * mulNorm (G := G) (z n (x / mulNorm (G := G) (y n))))
          = (x / mulNorm (G := G) (y n)) / mulNorm (G := G) (z n (x / mulNorm (G := G) (y n))) := by
        simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_assoc]
      rw [this]
      exact hmem
  have hcauchy : ∀ n : ℕ, y n / y (n + 1) ∈ U n := by
    intro n
    rw [hysucc n]
    have : y n / (y n * z n (x / mulNorm (G := G) (y n))) =
        (z n (x / mulNorm (G := G) (y n)))⁻¹ := by
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
    rw [this]
    exact Subgroup.inv_mem _ (hz₁ n _ (hdefect n) (hinv n))
  obtain ⟨y₀, hy₀⟩ := hU.complete y hcauchy
  refine ⟨y₀, ?_⟩
  have hall : ∀ n : ℕ, x / mulNorm (G := G) y₀ ∈ U n := by
    intro n
    have h₁ : mulNorm (G := G) (y₀ / y n) ∈ U n := hU.mulNorm_mem (hy₀ n)
    have h₂ : x / mulNorm (G := G) y₀ =
        (mulNorm (G := G) (y₀ / y n))⁻¹ * (x / mulNorm (G := G) (y n)) := by
      rw [mulNorm_div]
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
    rw [h₂]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h₁) (hdefect n)
  exact (div_eq_one.1 (hU.separated _ hall)).symm

/-! ### Cocycles -/

/-- **Every multiplicative 1-cocycle is a coboundary** when the graded pieces of a complete
filtration have vanishing `Ĥ¹`.  This is the form in which the local condition at an
unramified place is stated. -/
theorem isMulCoboundary₁_of_isMulCocycle₁ (hg : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (hvanish : ∀ (n : ℕ), ∀ u ∈ U n, mulNorm (G := G) u = 1 →
      ∃ z ∈ U n, u * (σ • z / z) ∈ U (n + 1))
    {f : G → M} (hf : groupCohomology.IsMulCocycle₁ f) :
    groupCohomology.IsMulCoboundary₁ f :=
  isMulCoboundary₁_of_mulNorm hg
    (fun _ hxx ↦ hU.exists_smul_div_of_mulNorm_eq_one hvanish hxx) hf

end IsCompleteFiltration

end Filtration

end CyclicLimit
