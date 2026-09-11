/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.NumberTheory.NumberField.DedekindZeta

@[expose] public section

/-!
# L-series of a character of the ideal class group, and its behaviour at `s = 1`

This file builds the first analytic step of the classical analytic proof of the first
fundamental inequality of class field theory.

Mathlib defines the Dedekind zeta function `NumberField.dedekindZeta` as the `LSeries` of
`n ↦ #{I : Ideal (𝓞 K) | N I = n}` and proves the class number formula
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`.  It has **no** L-series attached to a
character, no Euler product over prime ideals and no ray class groups.  What it does have is
`NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop`: the number of integral ideals of norm
`≤ x` in a *fixed ideal class* is asymptotic to `κ_K x`, with `κ_K` independent of the class.
That is exactly the input needed to split `ζ_K` along the characters of the class group.

## Main definitions

* `NumberField.idealDensity` : the constant `κ_K = 2^{r₁} (2π)^{r₂} R_K / (w_K √|d_K|)`, the
  density of the integral ideals lying in one fixed ideal class.
* `NumberField.classCharCoeff` : the coefficients `a_n(χ) = ∑_{N I = n} χ([I])`.
* `NumberField.classCharLSeries` : the L-series `L(χ, s) = ∑_I χ([I]) N(I)^{-s}`.

## Main results

* `NumberField.tendsto_sub_one_mul_classCharLSeries` : `(s - 1) L(χ, s) → (∑_C χ(C)) κ_K` as
  `s → 1⁺`, for an arbitrary function `χ` on the class group.
* `NumberField.tendsto_sub_one_mul_classCharLSeries_of_ne_one` : for a **nontrivial** character
  `χ : Cl(K) →* ℂ`, `(s - 1) L(χ, s) → 0`; that is, `L(χ, ·)` has no pole at `s = 1`.
* `NumberField.classCharLSeries_one` : the trivial character gives back `dedekindZeta K`, and
  `NumberField.tendsto_sub_one_mul_classCharLSeries_one` : its `(s-1)`-multiple tends to
  `dedekindZeta_residue K ≠ 0`.  So the family really does separate the trivial character.

## What is *not* here, and why

The classical chain continues: Euler product over prime ideals, `log L(χ, s)` asymptotics,
`L(1, χ) ≠ 0` for `χ ≠ 1`, hence the equidistribution of the prime ideals among the ideal
classes, hence the norm-index bound.  None of the remaining steps is available:

* there is no Dirichlet series indexed by ideals in Mathlib, and no Euler product over prime
  ideals (`Mathlib/NumberTheory/EulerProduct/` is entirely `ℕ`-indexed and needs a
  *completely* multiplicative `ℕ →*₀ ℂ`, which `n ↦ #{I | N I = n}` is not);
* there is no analytic continuation of `ζ_K` or of any of these `L(χ, ·)` past `Re s = 1`
  (`NumberField.dedekindZeta` is only the Dirichlet series);
* consequently `L(1, χ) ≠ 0` for `χ ≠ 1` is not available for a number field — the only
  nonvanishing results Mathlib has are for Dirichlet characters over `ℚ`
  (`DirichletCharacter.LFunction_apply_one_ne_zero`).

Regularity at `s = 1` — proved here — is the one step of the chain that the existing Mathlib
asymptotics do supply.
-/

noncomputable section

open Filter Finset Ideal Topology Asymptotics
open NumberField NumberField.InfinitePlace NumberField.Units
open scoped Real nonZeroDivisors

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The density of the integral ideals lying in one fixed ideal class. -/
def idealDensity : ℝ :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K) /
    (torsionOrder K * Real.sqrt |discr K|)

/-- The set of nonzero integral ideals of `K` of norm `n` lying in the ideal class `C`. -/
def idealSetEq (C : ClassGroup (𝓞 K)) (n : ℕ) : Set (Ideal (𝓞 K))⁰ :=
  {I | absNorm (I : Ideal (𝓞 K)) = n ∧ ClassGroup.mk0 I = C}

/-- The set of nonzero integral ideals of `K` of norm at most `n` in the ideal class `C`. -/
def idealSetLE (C : ClassGroup (𝓞 K)) (n : ℕ) : Set (Ideal (𝓞 K))⁰ :=
  {I | absNorm (I : Ideal (𝓞 K)) ≤ n ∧ ClassGroup.mk0 I = C}

variable {K}

theorem finite_of_absNorm_le {p : (Ideal (𝓞 K))⁰ → Prop} {n : ℕ}
    (h : ∀ I, p I → absNorm (I : Ideal (𝓞 K)) ≤ n) : {I : (Ideal (𝓞 K))⁰ | p I}.Finite := by
  have hf : {I : (Ideal (𝓞 K))⁰ | absNorm (I : Ideal (𝓞 K)) ≤ n}.Finite :=
    Ideal.finite_setOfPred_absNorm_le₀ n
  exact hf.subset (fun I hI ↦ h I hI)

theorem finite_idealSetEq (C : ClassGroup (𝓞 K)) (n : ℕ) : (idealSetEq K C n).Finite :=
  finite_of_absNorm_le (n := n) (fun _ h ↦ h.1.le)

theorem finite_idealSetLE (C : ClassGroup (𝓞 K)) (n : ℕ) : (idealSetLE K C n).Finite :=
  finite_of_absNorm_le (n := n) (fun _ h ↦ h.1)

theorem idealSetLE_zero (C : ClassGroup (𝓞 K)) : idealSetLE K C 0 = ∅ := by
  ext I
  simp only [idealSetLE, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
    Nat.le_zero]
  exact fun h ↦ absurd h (Ideal.absNorm_ne_zero_of_nonZeroDivisors I)

theorem idealSetLE_succ (C : ClassGroup (𝓞 K)) (n : ℕ) :
    idealSetLE K C (n + 1) = idealSetLE K C n ∪ idealSetEq K C (n + 1) := by
  ext I
  simp only [idealSetLE, idealSetEq, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨h1, h2⟩
    rcases Nat.lt_or_ge (absNorm (I : Ideal (𝓞 K))) (n + 1) with h | h
    · exact Or.inl ⟨by omega, h2⟩
    · exact Or.inr ⟨by omega, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by omega, h2⟩

theorem disjoint_idealSetLE_idealSetEq (C : ClassGroup (𝓞 K)) (n : ℕ) :
    Disjoint (idealSetLE K C n) (idealSetEq K C (n + 1)) := by
  rw [Set.disjoint_left]
  rintro I ⟨h1, -⟩ ⟨h2, -⟩
  omega

/-- The number of nonzero integral ideals of norm at most `n` in a class is the sum over
`1 ≤ k ≤ n` of the number of those of norm exactly `k`. -/
theorem ncard_idealSetLE_eq_sum (C : ClassGroup (𝓞 K)) (n : ℕ) :
    (idealSetLE K C n).ncard = ∑ k ∈ Finset.Icc 1 n, (idealSetEq K C k).ncard := by
  induction n with
  | zero => simp [idealSetLE_zero]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ← ih, idealSetLE_succ,
        Set.ncard_union_eq (disjoint_idealSetLE_idealSetEq C n) (finite_idealSetLE C n)
          (finite_idealSetEq C (n + 1))]


/-! ## The density of the ideals of a fixed class -/

theorem tendsto_ncard_idealSetLE (C : ClassGroup (𝓞 K)) :
    Tendsto (fun n : ℕ ↦ ((idealSetLE K C n).ncard : ℝ) / n) atTop (𝓝 (idealDensity K)) := by
  have h := (NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop K C).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun n ↦ ?_
  simp only [Function.comp_apply]
  congr 1
  rw [← Nat.card_coe_set_eq]
  exact congrArg _ (Nat.card_congr (Equiv.subtypeEquivRight (fun I ↦ by
    simp [idealSetLE, Nat.cast_le])))

/-! ## L-series of a class-group character -/

variable (K) in
/-- The `n`-th coefficient `∑_{N I = n} χ([I])` of the L-series attached to a function `χ` on
the ideal class group of `K`. -/
def classCharCoeff (χ : ClassGroup (𝓞 K) → ℂ) (n : ℕ) : ℂ :=
  ∑ C, χ C * ((idealSetEq K C n).ncard : ℂ)

variable (K) in
/-- The L-series `L(χ, s) = ∑_I χ([I]) N(I)^{-s}` attached to a function `χ` on the ideal class
group of `K`, as a Dirichlet series in Mathlib's `LSeries` framework. -/
def classCharLSeries (χ : ClassGroup (𝓞 K) → ℂ) (s : ℂ) : ℂ := LSeries (classCharCoeff K χ) s

theorem sum_classCharCoeff (χ : ClassGroup (𝓞 K) → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, classCharCoeff K χ k = ∑ C, χ C * ((idealSetLE K C n).ncard : ℂ) := by
  simp_rw [classCharCoeff]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  rw [← Finset.mul_sum, ncard_idealSetLE_eq_sum, Nat.cast_sum]

theorem tendsto_sum_weighted_real (w : ClassGroup (𝓞 K) → ℝ) :
    Tendsto (fun n : ℕ ↦ (∑ C, w C * ((idealSetLE K C n).ncard : ℝ)) / n) atTop
      (𝓝 ((∑ C, w C) * idealDensity K)) := by
  simp_rw [Finset.sum_div, mul_div_assoc, Finset.sum_mul]
  exact tendsto_finsetSum _ fun C _ ↦ (tendsto_ncard_idealSetLE C).const_mul (w C)

theorem tendsto_sum_classCharCoeff (χ : ClassGroup (𝓞 K) → ℂ) :
    Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n, classCharCoeff K χ k) / n) atTop
      (𝓝 ((∑ C, χ C) * (idealDensity K : ℂ))) := by
  simp_rw [sum_classCharCoeff, Finset.sum_div, mul_div_assoc, Finset.sum_mul]
  refine tendsto_finsetSum _ fun C _ ↦ ?_
  refine Filter.Tendsto.const_mul (χ C) ?_
  exact ((tendsto_ncard_idealSetLE C).ofReal).congr fun n ↦ by push_cast; ring

theorem lSeriesSummable_classCharCoeff (χ : ClassGroup (𝓞 K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (classCharCoeff K χ) s := by
  have hle : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, ‖classCharCoeff K χ k‖
      ≤ ∑ C, ‖χ C‖ * ((idealSetLE K C n).ncard : ℝ) := by
    intro n
    calc ∑ k ∈ Finset.Icc 1 n, ‖classCharCoeff K χ k‖
        ≤ ∑ k ∈ Finset.Icc 1 n, ∑ C, ‖χ C‖ * ((idealSetEq K C k).ncard : ℝ) :=
          Finset.sum_le_sum fun k _ ↦
            (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun C _ ↦ by simp)
      _ = ∑ C, ‖χ C‖ * ((idealSetLE K C n).ncard : ℝ) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun C _ ↦ by
            rw [← Finset.mul_sum, ncard_idealSetLE_eq_sum, Nat.cast_sum]
  refine LSeriesSummable_of_sum_norm_bigO (r := 1) ?_ zero_le_one hs
  have hmaj : (fun n : ℕ ↦ ∑ C, ‖χ C‖ * ((idealSetLE K C n).ncard : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) :=
    isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (r := 1)
      (a := (∑ C, ‖χ C‖) * idealDensity K)
      (by simpa [Real.rpow_one] using tendsto_sum_weighted_real (fun C ↦ ‖χ C‖))
  refine Asymptotics.IsBigO.trans (Asymptotics.isBigO_of_le (g :=
    fun n : ℕ ↦ ∑ C, ‖χ C‖ * ((idealSetLE K C n).ncard : ℝ)) _ fun n ↦ ?_) hmaj
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
    abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity)]
  exact hle n

/-- **The behaviour at `s = 1` of the L-series of a class-group character.**

`(s - 1) L(χ, s)` tends to `(∑_C χ(C)) κ_K` as `s → 1⁺`, where `κ_K` is the density
`NumberField.idealDensity K` of the integral ideals lying in one fixed ideal class. -/
theorem tendsto_sub_one_mul_classCharLSeries (χ : ClassGroup (𝓞 K) → ℂ) :
    Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * classCharLSeries K χ s) (𝓝[>] 1)
      (𝓝 ((∑ C, χ C) * (idealDensity K : ℂ))) :=
  LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div (tendsto_sum_classCharCoeff χ)
    fun s hs ↦ lSeriesSummable_classCharCoeff χ (by simpa using hs)

/-- **The character sum of a nontrivial character of a finite group vanishes.** -/
theorem _root_.MonoidHom.sum_eq_zero_of_ne_one {G : Type*} [Group G] [Fintype G]
    {χ : G →* ℂ} (h : χ ≠ 1) : ∑ g, χ g = 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, χ a ≠ 1 := by
    by_contra hc
    push Not at hc
    exact h (MonoidHom.ext fun g ↦ by simp [hc g])
  have key : χ a * ∑ g, χ g = ∑ g, χ g := by
    rw [Finset.mul_sum]
    simp_rw [← map_mul]
    exact Fintype.sum_bijective (a * ·) (Group.mulLeft_bijective a) _ _ fun _ ↦ rfl
  have : (χ a - 1) * ∑ g, χ g = 0 := by rw [sub_mul, one_mul, key, sub_self]
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd (sub_eq_zero.1 h') ha
  · exact h'

/-- **The L-series of a class-group character with vanishing character sum has no pole at
`s = 1`.**  This is the case `χ ≠ 1` of a genuine character: see
`MonoidHom.sum_eq_zero_of_ne_one`. -/
theorem tendsto_sub_one_mul_classCharLSeries_of_sum_eq_zero
    (χ : ClassGroup (𝓞 K) → ℂ) (h : ∑ C, χ C = 0) :
    Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * classCharLSeries K χ s) (𝓝[>] 1) (𝓝 0) := by
  simpa [h] using tendsto_sub_one_mul_classCharLSeries χ

/-- **The L-series of a nontrivial character of the ideal class group has no pole at `s = 1`.**

This is the analytic input that distinguishes the trivial character from the others: for the
trivial character `(s - 1) L(χ, s)` tends to `h_K κ_K ≠ 0`
(`NumberField.tendsto_sub_one_mul_classCharLSeries_one`), while for every nontrivial character it
tends to `0`. -/
theorem tendsto_sub_one_mul_classCharLSeries_of_ne_one
    {χ : ClassGroup (𝓞 K) →* ℂ} (h : χ ≠ 1) :
    Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * classCharLSeries K (fun C ↦ χ C) s) (𝓝[>] 1) (𝓝 0) :=
  tendsto_sub_one_mul_classCharLSeries_of_sum_eq_zero _ (MonoidHom.sum_eq_zero_of_ne_one h)

/-! ## The trivial character gives the Dedekind zeta function -/

theorem ncard_setOfPred_absNorm_eq₀ (n : ℕ) :
    {I : (Ideal (𝓞 K))⁰ | absNorm (I : Ideal (𝓞 K)) = n}.ncard
      = ∑ C, (idealSetEq K C n).ncard := by
  have hU : {I : (Ideal (𝓞 K))⁰ | absNorm (I : Ideal (𝓞 K)) = n} = ⋃ C, idealSetEq K C n := by
    ext I
    simp [idealSetEq]
  rw [hU, Set.ncard_iUnion_of_finite (fun C ↦ finite_idealSetEq C n) ?_,
    finsum_eq_sum_of_fintype]
  intro C D hCD
  rw [Function.onFun, Set.disjoint_left]
  rintro I ⟨-, hC⟩ ⟨-, hD⟩
  exact hCD (hC.symm.trans hD)

/-- For `n ≠ 0` the integral ideals of norm `n` are exactly the nonzero ones. -/
def nonZeroIdealEquivOfNeZero {n : ℕ} (hn : n ≠ 0) :
    {I : Ideal (𝓞 K) // absNorm I = n} ≃
      {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n} where
  toFun I := ⟨⟨I.1, mem_nonZeroDivisors_of_ne_zero (fun h ↦ hn (by rw [← I.2, h]; simp))⟩, I.2⟩
  invFun I := ⟨(I.1 : Ideal (𝓞 K)), I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem classCharCoeff_one {n : ℕ} (hn : n ≠ 0) :
    classCharCoeff K (fun _ ↦ 1) n =
      (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ) := by
  simp only [classCharCoeff, one_mul]
  rw [← Nat.cast_sum, ← ncard_setOfPred_absNorm_eq₀]
  norm_cast
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_congr (nonZeroIdealEquivOfNeZero hn)).symm

/-- **The L-series of the trivial character of the ideal class group is the Dedekind zeta
function of `K`.** -/
theorem classCharLSeries_one (s : ℂ) :
    classCharLSeries K (fun _ ↦ 1) s = dedekindZeta K s :=
  LSeries_congr (fun {_} hn ↦ classCharCoeff_one hn) s

theorem dedekindZeta_residue_eq_classNumber_mul_idealDensity :
    dedekindZeta_residue K = classNumber K * idealDensity K := by
  rw [dedekindZeta_residue_def, idealDensity]
  ring

/-- **The trivial character does have a pole**: `(s - 1) ζ_K(s) → h_K κ_K` as `s → 1⁺`.  Together
with `NumberField.tendsto_sub_one_mul_classCharLSeries_of_ne_one` this separates the trivial
character from all the others, and it agrees with Mathlib's class number formula
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`. -/
theorem tendsto_sub_one_mul_classCharLSeries_one :
    Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * classCharLSeries K (fun _ ↦ 1) s) (𝓝[>] 1)
      (𝓝 ((dedekindZeta_residue K : ℂ))) := by
  have h := tendsto_sub_one_mul_classCharLSeries (K := K) (fun _ ↦ 1)
  rwa [show (∑ _C : ClassGroup (𝓞 K), (1 : ℂ)) * (idealDensity K : ℂ)
      = ((dedekindZeta_residue K : ℝ) : ℂ) by
    rw [dedekindZeta_residue_eq_classNumber_mul_idealDensity, classNumber]
    push_cast
    simp [Finset.card_univ]] at h

end NumberField
