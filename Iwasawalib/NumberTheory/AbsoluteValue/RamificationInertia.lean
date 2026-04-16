/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Iwasawalib.NumberTheory.AbsoluteValue.Archimedean
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Iwasawalib.Topology.Algebra.Group.Basic

@[expose] public section

/-!

# Ramification index and inertia subgroup for a place (`AbsoluteValue`)

(To be written)

References:

- [J. W. S. Cassels, A. Frohlich, editors, *Algebraic Number Theory*][cassels1967algebraic]

-/

/-! ### Lemmas should go mathlib -/

/-- If `a < b`, `b, c` are positive and `c ≠ 1`, then there are `m : ℕ` and `n : ℤ`
such that the power `c ^ n` is strictly between `a ^ m` and `b ^ m`.

TODO: go mathlib and add `exists_pow_btwn_pow_of_lt` -/
theorem exists_zpow_btwn_pow_of_lt {K : Type*} [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] [Archimedean K] [ExistsAddOfLE K] {a b c : K}
    (h : a < b) (hb₀ : 0 < b) (hc₀ : 0 < c) (hc₁ : c ≠ 1) :
    ∃ (m : ℕ) (n : ℤ), a ^ m < c ^ n ∧ c ^ n < b ^ m := by
  wlog hc' : c < 1 generalizing c
  · obtain ⟨m, n, h⟩ := this (inv_pos.2 hc₀) (by simpa)
      (inv_lt_one_of_one_lt₀ ((not_lt.1 hc').lt_of_ne' hc₁))
    use m, -n
    simpa using h
  rw [← div_lt_one hb₀] at h
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hc₀ h
  use m
  rw [div_pow, div_lt_iff₀' (pow_pos hb₀ m)] at hm
  exact exists_zpow_btwn_of_lt_mul hm (pow_pos hb₀ m) hc₀ hc'

/-- If `a < b`, `b, c` are positive and `c ≠ 1`, then there are `m : ℕ` and `n : ℤ`
such that `1` is strictly between `a ^ m * c ^ n` and `b ^ m * c ^ n`.

TODO: go mathlib -/
theorem exists_one_btwn_pow_mul_zpow_of_lt {K : Type*} [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] [Archimedean K] [ExistsAddOfLE K] {a b c : K}
    (h : a < b) (hb₀ : 0 < b) (hc₀ : 0 < c) (hc₁ : c ≠ 1) :
    ∃ (m : ℕ) (n : ℤ), a ^ m * c ^ n < 1 ∧ 1 < b ^ m * c ^ n := by
  obtain ⟨m, n, h⟩ := exists_zpow_btwn_pow_of_lt h hb₀ hc₀ hc₁
  use m, -n
  simpa [← GroupWithZero.div_eq_mul_inv, div_lt_one, one_lt_div, zpow_pos hc₀ n]

/-- TEST

TODO: go mathlib -/
theorem exists_pow_mul_zpow_lt_and_lt_pow_mul_zpow_of_lt {K : Type*} [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] [Archimedean K] [ExistsAddOfLE K] {a b c d : K} (e : K)
    (h : a < b) (hb₀ : 0 < b) (hc₀ : 0 < c) (hc₁ : c ≠ 1) (hd₀ : 0 < d) :
    ∃ (m : ℕ) (n : ℤ), a ^ m * c ^ n < d ∧ e < b ^ m * c ^ n := by
  sorry

namespace AbsoluteValue

/-! ### Action on absolute values -/

section MulAction

variable (F K S : Type*) [CommSemiring F] [Semiring K] [Algebra F K] [Semiring S] [PartialOrder S]

/-- Ring isomorphisms act on the left on the absolute values by `σ • v := v ∘ σ⁻¹`. -/
instance instMulActionRingEquiv : MulAction (K ≃+* K) (AbsoluteValue K S) where
  smul σ v := v.comp (f := σ.symm) σ.symm.injective
  mul_smul σ τ v := by ext; simp [HSMul.hSMul, show σ * τ = τ.trans σ from rfl]
  one_smul v := by ext; simp [HSMul.hSMul]

/-- Algebra isomorphisms act on the left on the absolute values by `σ • v := v ∘ σ⁻¹`. -/
instance instMulActionAlgEquiv : MulAction (K ≃ₐ[F] K) (AbsoluteValue K S) where
  smul σ v := v.comp (f := σ.symm) σ.symm.injective
  mul_smul σ τ v := by ext; simp [HSMul.hSMul, show σ * τ = τ.trans σ from rfl]
  one_smul v := by ext; simp [HSMul.hSMul]

variable {F K S}

theorem ringEquiv_smul_def (v : AbsoluteValue K S) (σ : K ≃+* K) :
    σ • v = v.comp (f := σ.symm) σ.symm.injective := rfl

@[simp]
theorem ringEquiv_smul_apply (v : AbsoluteValue K S) (σ : K ≃+* K) (x) :
    (σ • v) x = v (σ.symm x) := rfl

theorem algEquiv_smul_def (v : AbsoluteValue K S) (σ : K ≃ₐ[F] K) :
    σ • v = v.comp (f := σ.symm) σ.symm.injective := rfl

@[simp]
theorem algEquiv_smul_apply (v : AbsoluteValue K S) (σ : K ≃ₐ[F] K) (x) :
    (σ • v) x = v (σ.symm x) := rfl

theorem coe_algEquiv_smul_eq (v : AbsoluteValue K S) (σ : K ≃ₐ[F] K) :
    (σ : K ≃+* K) • v = σ • v := rfl

end MulAction

/-! ### Decomposition subgroup for a place -/

section General

variable (F K S : Type*) [CommSemiring F] [Semiring K] [Algebra F K] [Semiring S] [PartialOrder S]
  (v : AbsoluteValue K S) (σ : K ≃ₐ[F] K)

variable {K S}

/-- The decomposition subgroup `Dᵥ(K/F)` in `Gal(K/F)` for a place `v` of `K` consists of all `σ`
such that `v ∘ σ = v`. See [cassels1967algebraic], Chapter VII, §1.
This definition also works for infinite places.

Note: Here we use `def` but not `abbrev` because sometimes simp lemmas for `MulAction.stabilizer`
are not desired (will introduce `σ⁻¹`). -/
def decompositionSubgroup := MulAction.stabilizer (K ≃ₐ[F] K) v

theorem mem_decompositionSubgroup_iff :
    σ ∈ v.decompositionSubgroup F ↔ v.comp (f := σ) σ.injective = v := by
  rw [← inv_mem_iff, decompositionSubgroup, MulAction.mem_stabilizer_iff, algEquiv_smul_def]

theorem mem_decompositionSubgroup_iff_forall_apply_eq :
    σ ∈ v.decompositionSubgroup F ↔ ∀ x, v (σ x) = v x := by
  simp [mem_decompositionSubgroup_iff, AbsoluteValue.ext_iff]

theorem decompositionSubgroup_eq_top_of_not_isNontrivial (h : ¬v.IsNontrivial) :
    v.decompositionSubgroup F = ⊤ := by
  rw [eq_top_iff]
  rintro σ -
  rw [mem_decompositionSubgroup_iff]
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [not_isNontrivial_apply h, hx]

variable {σ}

theorem apply_eq_of_mem_decompositionSubgroup
    (h : σ ∈ v.decompositionSubgroup F) (x) : v (σ x) = v x :=
  (v.mem_decompositionSubgroup_iff_forall_apply_eq F σ).1 h x

/-- The elements in decomposition subgroup preserve the set `{x | v x ≤ y}` for all `y`. -/
theorem image_setOf_eq_of_mem_decompositionSubgroup
    (h : σ ∈ v.decompositionSubgroup F) (y) : σ '' {x | v x ≤ y} = {x | v x ≤ y} := by
  ext x
  obtain ⟨x', rfl⟩ := σ.surjective x
  simp [(mem_decompositionSubgroup_iff_forall_apply_eq ..).1 h x']

end General

section IsAlgebraic

variable (F K : Type*) [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
  (v : AbsoluteValue K ℝ) (σ : Gal(K/F))

variable {K}

/-- If `K / F` is algebraic, then the decomposition subgroup `Dᵥ(K/F)` is also the subgroup
consists of all `σ` preserving the set `{x | v x ≤ 1}`.

NOTE: This is not true if `K / F` is not algebraic, for example, when `K` is the fraction field of
the valuation ring $\bigcup_{n=1}^\infty F⟦X^{1/n}⟧$, `k ≥ 2` is a fixed positive integer, `σ` is
$X^{1/n} \mapsto X^{k/n}$, then it preserves the valuation ring but doesn't preserve the valuation.
-/
theorem mem_decompositionSubgroup_iff_image_setOf_eq :
    σ ∈ v.decompositionSubgroup F ↔ σ '' {x | v x ≤ 1} = {x | v x ≤ 1} := by
  refine ⟨fun h ↦ v.image_setOf_eq_of_mem_decompositionSubgroup F h 1, fun h ↦ ?_⟩
  replace h (x) (hx : x ∈ {x | v x ≤ 1}) : v (σ x) ≤ 1 := by
    simpa [h] using Set.mem_image_of_mem σ hx
  rw [mem_decompositionSubgroup_iff_forall_apply_eq]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  by_cases htriv : v.IsNontrivial
  · by_contra! H
    wlog H2 : v x < v (σ x) generalizing x
    · have H3 := H.lt_or_gt.resolve_right H2
      refine this x⁻¹ (by simp [hx]) (fun h' ↦ H (by simpa using h')) ?_
      simpa [inv_lt_inv₀ (v.pos _) (v.pos _), hx] using H3
    rw [← isNontrivial_iff_of_liesOver (v.comp (algebraMap F K).injective) v] at htriv
    obtain ⟨y, hy⟩ := htriv.exists_abv_gt_one
    obtain ⟨m, n, h1, h2⟩ := exists_one_btwn_pow_mul_zpow_of_lt H2 ((v.pos hx).trans H2)
      (zero_lt_one.trans hy) hy.ne'
    replace h1 := h1.le
    simp only [comp_apply, ← map_zpow₀, ← map_pow, ← map_mul] at h1 h2
    exact h2.not_ge (by simpa using h _ h1)
  simp [not_isNontrivial_apply htriv, hx]

omit [Algebra.IsAlgebraic F K] in
variable {σ} in
/-- The elements in decomposition subgroup are continuous in `v`-adic topology. -/
theorem continuous_of_mem_decompositionSubgroup
    (h : σ ∈ v.decompositionSubgroup F) : Continuous (WithAbs.congr v v σ) := by
  rw [mem_decompositionSubgroup_iff_forall_apply_eq] at h
  refine (AddMonoidHom.continuous_iff (WithAbs.congr v v σ).toAddMonoidHom).2 fun s h1 hs ↦ ?_
  obtain ⟨ε, hε1, hε2⟩ := Metric.isOpen_iff.1 hs _ h1
  refine ⟨Metric.ball 0 ε, Metric.mem_ball_self hε1, Metric.isOpen_ball, fun x hx ↦ ?_⟩
  apply Set.preimage_mono hε2
  simpa [WithAbs.norm_eq_apply_ofAbs, h x.ofAbs] using hx

/-- If `K / F` is algebraic, then an element is contained in the decomposition subgroup of `v`
if and only if it is continuous under the `v`-adic topology. -/
theorem mem_decompositionSubgroup_iff_continuous :
    σ ∈ v.decompositionSubgroup F ↔ Continuous (WithAbs.congr v v σ) := by
  refine ⟨fun h ↦ v.continuous_of_mem_decompositionSubgroup F h, fun h ↦ ?_⟩
  replace h (ε : ℝ) (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ x, v x < δ → v (σ x) < ε := by
    obtain ⟨s, h1, hs, hs2⟩ := (AddMonoidHom.continuous_iff (WithAbs.congr v v σ).toAddMonoidHom).1
      h (Metric.ball 0 ε) (Metric.mem_ball_self hε) Metric.isOpen_ball
    obtain ⟨δ, hδ1, hδ2⟩ := Metric.isOpen_iff.1 hs _ h1
    refine ⟨δ, hδ1, fun x hx ↦ ?_⟩
    replace hx : WithAbs.toAbs v x ∈ Metric.ball 0 δ := by simpa [WithAbs.norm_eq_apply_ofAbs]
    simpa [WithAbs.norm_eq_apply_ofAbs] using (hδ2.trans hs2) hx
  rw [mem_decompositionSubgroup_iff_forall_apply_eq]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  by_cases htriv : v.IsNontrivial
  · by_contra! H
    wlog H2 : v x < v (σ x) generalizing x
    · have H3 := H.lt_or_gt.resolve_right H2
      refine this x⁻¹ (by simp [hx]) (fun h' ↦ H (by simpa using h')) ?_
      simpa [inv_lt_inv₀ (v.pos _) (v.pos _), hx] using H3
    rw [← isNontrivial_iff_of_liesOver (v.comp (algebraMap F K).injective) v] at htriv
    obtain ⟨y, hy⟩ := htriv.exists_abv_gt_one
    obtain ⟨δ, hδ1, hδ2⟩ := h 1 one_pos
    obtain ⟨m, n, h1, h2⟩ := exists_pow_mul_zpow_lt_and_lt_pow_mul_zpow_of_lt 1 H2
      ((v.pos hx).trans H2) (zero_lt_one.trans hy) hy.ne' hδ1
    simp only [comp_apply, ← map_zpow₀, ← map_pow, ← map_mul] at h1 h2
    exact h2.not_gt (by simpa using hδ2 _ h1)
  simp [not_isNontrivial_apply htriv, hx]

#exit

/-- Our definition is the same as `ValuationSubring.decompositionSubgroup` for finite places. -/
theorem decompositionSubgroup_eq_of_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : IsNonarchimedean v) :
    v.decompositionSubgroup F = (v.toValuation h).valuationSubring.decompositionSubgroup F := by
  ext g
  simp only [mem_decompositionSubgroup_iff, MulAction.mem_stabilizer_iff, SetLike.ext'_iff]
  congr!

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Dᵥ(L/K) = Dᵥ(L/F) ⊓ Gal(L/K)`. -/
theorem decompositionSubgroup_eq_comap
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    v.decompositionSubgroup K = (v.decompositionSubgroup F).comap
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) := by
  ext
  simp [mem_decompositionSubgroup_iff, Set.ext_iff,
    IntermediateField.restrictRestrictAlgEquivMapHom]

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Iᵥ(L/K) ≤ Iᵥ(L/F)`. -/
theorem map_decompositionSubgroup_le
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    (v.decompositionSubgroup K).map
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) ≤ v.decompositionSubgroup F := by
  simpa only [Subgroup.map_le_iff_le_comap] using (v.decompositionSubgroup_eq_comap F K).le

/-- Decomposition subgroup for an infinite place is either trivial or `ℤ/2ℤ`. (Is this correct?) -/
theorem card_decompositionSubgroup_dvd_two_of_not_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : ¬IsNonarchimedean v) :
    Nat.card (v.decompositionSubgroup F) ∣ 2 := by
  sorry

/-! ### Inertia subgroup for a place -/

/-- The inertia subgroup `Iᵥ(K/F)` in `Gal(K/F)` for a finite place `v` of `K` consists of all `σ`
preserving the set `{x | v x ≤ 1}` and such that for all such `x`, `v (σ x - x) < 1`.
For infinite places `Iᵥ(K/F)` is just defined to be the decomposition subgroup `Dᵥ(K/F)`. -/
def inertiaSubgroup
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) :
    Subgroup Gal(K/F) where
  carrier := {σ | σ '' {x | v x ≤ 1} = {x | v x ≤ 1} ∧
    (¬IsNonarchimedean v ∨ ∀ x, v x ≤ 1 → v (σ x - x) < 1)}
  one_mem' := by simp
  mul_mem' {f} {g} hf hg := by
    by_cases h : IsNonarchimedean v
    · simp only [h, not_true_eq_false, false_or] at hf hg ⊢
      use (v.decompositionSubgroup F).mul_mem hf.1 hg.1
      intro x hx
      rw [AlgEquiv.mul_apply]
      replace hf := hf.2 _ (v.apply_le_one_of_mem_decompositionSubgroup hg.1 hx)
      replace hg := hg.2 _ hx
      simpa using (h (f (g x) - g x) (g x - x)).trans_lt (max_lt hf hg)
    simp only [h, not_false_eq_true, true_or, and_true] at hf hg ⊢
    exact (v.decompositionSubgroup F).mul_mem hf hg
  inv_mem' {f} hf := by
    by_cases h : IsNonarchimedean v
    · simp only [h, not_true_eq_false, false_or] at hf ⊢
      have h1 := (v.decompositionSubgroup F).inv_mem hf.1
      refine ⟨h1, fun x hx ↦ ?_⟩
      rw [← AbsoluteValue.map_neg]
      convert hf.2 _ (v.apply_le_one_of_mem_decompositionSubgroup h1 hx) using 2
      simp
    simp only [h, not_false_eq_true, true_or, and_true] at hf ⊢
    exact (v.decompositionSubgroup F).inv_mem hf

theorem mem_inertiaSubgroup_iff
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) (σ) :
    σ ∈ v.inertiaSubgroup F ↔ σ '' {x | v x ≤ 1} = {x | v x ≤ 1} ∧
      (¬IsNonarchimedean v ∨ ∀ x, v x ≤ 1 → v (σ x - x) < 1) := Iff.rfl

theorem mem_inertiaSubgroup_iff_of_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : IsNonarchimedean v) (σ) :
    σ ∈ v.inertiaSubgroup F ↔ σ '' {x | v x ≤ 1} = {x | v x ≤ 1} ∧
      ∀ x, v x ≤ 1 → v (σ x - x) < 1 := by
  simp [mem_inertiaSubgroup_iff, h]

theorem mem_inertiaSubgroup_iff_of_not_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : ¬IsNonarchimedean v) (σ) :
    σ ∈ v.inertiaSubgroup F ↔ σ '' {x | v x ≤ 1} = {x | v x ≤ 1} := by
  simp [mem_inertiaSubgroup_iff, h]

theorem inertiaSubgroup_eq_bot_of_not_isNontrivial
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : ¬v.IsNontrivial) : v.inertiaSubgroup F = ⊥ := by
  rw [eq_bot_iff]
  rintro σ hσ
  rw [Subgroup.mem_bot]
  ext x
  rw [v.mem_inertiaSubgroup_iff_of_isNonarchimedean F (by
    contrapose! h; exact isNontrivial_of_not_isNonarchimedean _ h)] at hσ
  replace hσ := hσ.2 x <| by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (not_isNontrivial_apply h hx).le
  replace hσ : σ x - x = 0 := by
    contrapose! hσ
    exact (not_isNontrivial_apply h hσ).ge
  simpa [sub_eq_zero] using hσ

theorem inertiaSubgroup_le_decompositionSubgroup
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) :
    v.inertiaSubgroup F ≤ v.decompositionSubgroup F := fun _ ↦ by
  simpa only [mem_inertiaSubgroup_iff, mem_decompositionSubgroup_iff] using And.left

theorem inertiaSubgroup_eq_decompositionSubgroup_of_not_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : ¬IsNonarchimedean v) :
    v.inertiaSubgroup F = v.decompositionSubgroup F := by
  ext
  simp only [v.mem_inertiaSubgroup_iff_of_not_isNonarchimedean F h, mem_decompositionSubgroup_iff]

theorem apply_le_one_of_mem_inertiaSubgroup
    {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) {σ}
    (h : σ ∈ v.inertiaSubgroup F) {x} (hx : v x ≤ 1) : v (σ x) ≤ 1 :=
  v.apply_le_one_of_mem_decompositionSubgroup (v.inertiaSubgroup_le_decompositionSubgroup F h) hx

theorem apply_le_one_iff_of_mem_inertiaSubgroup
    {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) {σ}
    (h : σ ∈ v.inertiaSubgroup F) {x} : v (σ x) ≤ 1 ↔ v x ≤ 1 :=
  v.apply_le_one_iff_of_mem_decompositionSubgroup (v.inertiaSubgroup_le_decompositionSubgroup F h)

theorem apply_sub_lt_one_of_mem_inertiaSubgroup_of_isNonarchimedean
    {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) {σ}
    (h : σ ∈ v.inertiaSubgroup F) (h2 : IsNonarchimedean v) {x} (hx : v x ≤ 1) : v (σ x - x) < 1 :=
  ((v.mem_inertiaSubgroup_iff_of_isNonarchimedean F h2 σ).1 h).2 x hx

/-- Our definition is the same as `ValuationSubring.inertiaSubgroup` for finite places. -/
theorem inertiaSubgroup_eq_of_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : IsNonarchimedean v) :
    v.inertiaSubgroup F =
      ((v.toValuation h).valuationSubring.inertiaSubgroup F).map (Subgroup.subtype _) := by
  ext g
  rw [Subgroup.mem_map]
  refine ⟨fun hg ↦ ?_, ?_⟩
  · have := v.inertiaSubgroup_le_decompositionSubgroup _ hg
    rw [v.decompositionSubgroup_eq_of_isNonarchimedean _ h] at this
    refine ⟨⟨g, this⟩, ?_, rfl⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    ext x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    change IsLocalRing.residue _ _ = IsLocalRing.residue _ _
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff,
      ← NNReal.coe_lt_coe, NNReal.coe_one]
    convert v.apply_sub_lt_one_of_mem_inertiaSubgroup_of_isNonarchimedean hg h y.2
  · rintro ⟨f, h1, h2⟩
    rw [v.mem_inertiaSubgroup_iff_of_isNonarchimedean F h]
    refine ⟨?_, fun x hx ↦ ?_⟩
    · rw [← v.mem_decompositionSubgroup_iff F, ← h2]
      have := v.decompositionSubgroup_eq_of_isNonarchimedean F h
      convert f.2
    · rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at h1
      replace h1 := congr($(h1) (IsLocalRing.residue _ ⟨x, hx⟩))
      change IsLocalRing.residue _ _ = IsLocalRing.residue _ _ at h1
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff,
        ← NNReal.coe_lt_coe, NNReal.coe_one] at h1
      rw [← h2]
      exact h1

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Iᵥ(L/K) = Iᵥ(L/F) ⊓ Gal(L/K)`. -/
theorem inertiaSubgroup_eq_comap
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    v.inertiaSubgroup K = (v.inertiaSubgroup F).comap
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) := by
  ext
  simp only [mem_inertiaSubgroup_iff, Subgroup.mem_comap]
  congr! <;> (ext; simp [IntermediateField.restrictRestrictAlgEquivMapHom])

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Iᵥ(L/K) ≤ Iᵥ(L/F)`. -/
theorem map_inertiaSubgroup_le
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    (v.inertiaSubgroup K).map
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) ≤ v.inertiaSubgroup F := by
  simpa only [Subgroup.map_le_iff_le_comap] using (v.inertiaSubgroup_eq_comap F K).le

/-! ### TODO: go mathlib -/

/-- TODO: go mathlib -/
theorem _root_.IntermediateField.restrictRestrictAlgEquivMapHom_injective_of_tower_top
    (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [Algebra K L]
    [IsScalarTower F K L] [Normal F L] :
    Function.Injective (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  ext x
  replace ha := congr($(ha) x)
  simpa [IntermediateField.restrictRestrictAlgEquivMapHom] using ha

/-- TODO: go mathlib -/
@[simp]
theorem _root_.AlgEquiv.algebraMap_restrictNormalHom_apply
    {F : Type*} [Field F] {K₁ : Type*} [Field K₁] [Algebra F K₁] (E : Type*) [Field E] [Algebra F E]
    [Algebra E K₁] [IsScalarTower F E K₁] [Normal F E] (φ : Gal(K₁/F)) (x : E) :
    algebraMap E K₁ (AlgEquiv.restrictNormalHom E φ x) = φ (algebraMap E K₁ x) := by
  simp [AlgEquiv.restrictNormalHom]

/-- TODO: go mathlib -/
@[simp]
theorem _root_.IntermediateField.alrebraMap_restrictRestrictAlgEquivMapHom_apply
    (F K L E : Type*) [Field F] [Field K] [Field L] [Field E] [Algebra F K] [Algebra F L]
    [Algebra F E] [Algebra K E] [Algebra L E] [IsScalarTower F K E] [IsScalarTower F L E]
    [Normal F K] (φ : Gal(E/L)) (x : K) :
    algebraMap K E (IntermediateField.restrictRestrictAlgEquivMapHom F K L E φ x) =
      φ (algebraMap K E x) := by
  simp [IntermediateField.restrictRestrictAlgEquivMapHom]

/-- TODO: go mathlib -/
theorem _root_.IntermediateField.restrictRestrictAlgEquivMapHom_comp_restrictRestrictAlgEquivMapHom
    (F K F' K' F'' K'' : Type*) [Field F] [Field K] [Field F'] [Field K'] [Field F''] [Field K'']
    [Algebra F K] [Algebra F' K'] [Algebra F'' K''] [Algebra F F'] [Algebra F' F''] [Algebra F F'']
    [Algebra F K'] [Algebra F' K''] [Algebra F K''] [Algebra K K'] [Algebra K' K''] [Algebra K K'']
    [IsScalarTower F K K'] [IsScalarTower F' K' K''] [IsScalarTower F F' K'] [IsScalarTower F K K'']
    [IsScalarTower F F'' K''] [IsScalarTower F' F'' K''] [IsScalarTower K K' K'']
    [Normal F K] [Normal F' K'] :
    (IntermediateField.restrictRestrictAlgEquivMapHom F K F' K').comp
      (IntermediateField.restrictRestrictAlgEquivMapHom F' K' F'' K'') =
        IntermediateField.restrictRestrictAlgEquivMapHom F K F'' K'' := by
  ext a x
  apply_fun _ using (algebraMap K K'').injective
  convert Eq.refl (a (algebraMap K K'' x))
  · simp [IsScalarTower.algebraMap_apply K K' K'']
  · simp

/-! ### Ramification index of a place for an extension -/

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then the
ramification index of `v` for `K / F` is defined to be the index of `Iᵥ(L/K)` in `Iᵥ(L/F)`
(`0` means infinite). Later we will show that this depends only on the place of `K` below `v`,
and is independent of the choice of `L` (`AbsoluteValue.ramificationIdx_spec`). -/
noncomputable def ramificationIdxOfIsScalarTower
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) : ℕ :=
    ((v.inertiaSubgroup K).map
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L)).relIndex (v.inertiaSubgroup F)

open IntermediateField in
theorem ramificationIdxOfIsScalarTower_mul_ramificationIdxOfIsScalarTower
    (F K M : Type*) [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [Algebra M L]
    [IsScalarTower F M L] [IsScalarTower K M L] [IsScalarTower F K L] [Normal F L] [Normal K L]
    (v : AbsoluteValue L ℝ) :
    v.ramificationIdxOfIsScalarTower F K * v.ramificationIdxOfIsScalarTower K M =
      v.ramificationIdxOfIsScalarTower F M := by
  simp only [ramificationIdxOfIsScalarTower]
  rw [mul_comm, ← Subgroup.relIndex_map_map_of_injective _ _
      (restrictRestrictAlgEquivMapHom_injective_of_tower_top F K L), Subgroup.map_map,
    restrictRestrictAlgEquivMapHom_comp_restrictRestrictAlgEquivMapHom]
  apply Subgroup.relIndex_mul_relIndex
  · rw [← restrictRestrictAlgEquivMapHom_comp_restrictRestrictAlgEquivMapHom F L K L M L,
      ← Subgroup.map_map]
    exact Subgroup.map_mono (v.map_inertiaSubgroup_le K M)
  · exact v.map_inertiaSubgroup_le F K

/-- If `K / F` is an algebraic extension, then any place `v` of `F` can be extended to `K`.
(Is this correct?) -/
theorem exists_liesOver
    {F : Type*} (K : Type*) [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue F ℝ) : ∃ w : AbsoluteValue K ℝ, w.LiesOver v := by
  sorry

/-- If `K / F` is an algebraic extension, `v` is a place of `K`, then the
ramification index of `v` for `K / F` is defined to be the ramification index of `w`
for `K / F`, where `w` is any extension of `v` to the algebraic closure of `K`. -/
noncomputable def ramificationIdx
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue K ℝ) : ℕ :=
  (v.exists_liesOver (AlgebraicClosure K)).choose.ramificationIdxOfIsScalarTower F K

/-- (Is this correct?) -/
theorem ramificationIdx_spec
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v] :
    haveI := Algebra.IsAlgebraic.tower_bot F K L
    v.ramificationIdx F = w.ramificationIdxOfIsScalarTower F K := by
  sorry

theorem ramificationIdx_mul_ramificationIdx
    (F K : Type*) {M : Type*} [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M] [Algebra.IsAlgebraic F M]
    (v : AbsoluteValue M ℝ) (w : AbsoluteValue K ℝ) [v.LiesOver w] :
    haveI := Algebra.IsAlgebraic.tower_top (K := F) (L := K) (A := M)
    haveI := Algebra.IsAlgebraic.tower_bot (K := F) (L := K) (A := M)
    w.ramificationIdx F * v.ramificationIdx K = v.ramificationIdx F := by
  have := Algebra.IsAlgebraic.tower_top (K := F) (L := K) (A := M)
  have := Algebra.IsAlgebraic.tower_bot (K := F) (L := K) (A := M)
  obtain ⟨v', _⟩ := v.exists_liesOver (AlgebraicClosure M)
  have := LiesOver.trans v' v w
  rw [ramificationIdx_spec F w v', ramificationIdx_spec K v v', ramificationIdx_spec F v v',
    ramificationIdxOfIsScalarTower_mul_ramificationIdxOfIsScalarTower]

/-! ### Assertion that a place is unramified for an extension -/

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then `v` is
called unramified for `K / F`, if `Iᵥ(L/F) ≤ Gal(L/K)`, or equivalently `Iᵥ(L/K) = Iᵥ(L/F)`
(`AbsoluteValue.isUnramifiedOfIsScalarTower_iff_map_inertiaSubgroup_eq`).
Later we will show that this depends only on the place of `K` below `v`, and is independent of the
choice of `L` (`AbsoluteValue.isUnramified_spec`). -/
def IsUnramifiedOfIsScalarTower
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) : Prop :=
    v.inertiaSubgroup F ≤ (IntermediateField.restrictRestrictAlgEquivMapHom F L K L).range

theorem isUnramifiedOfIsScalarTower_iff_map_inertiaSubgroup_eq
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    v.IsUnramifiedOfIsScalarTower F K ↔ (v.inertiaSubgroup K).map
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) = v.inertiaSubgroup F := by
  have h := congr($(v.inertiaSubgroup_eq_comap F K).map
    (IntermediateField.restrictRestrictAlgEquivMapHom F L K L))
  rw [Subgroup.map_comap_eq] at h
  rw [h, inf_eq_right, IsUnramifiedOfIsScalarTower]

theorem isUnramifiedOfIsScalarTower_iff_ramificationIdxOfIsScalarTower_eq_one
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    v.IsUnramifiedOfIsScalarTower F K ↔ v.ramificationIdxOfIsScalarTower F K = 1 := by
  rw [isUnramifiedOfIsScalarTower_iff_map_inertiaSubgroup_eq, le_antisymm_iff]
  simp [ramificationIdxOfIsScalarTower, v.map_inertiaSubgroup_le F K]

/-- If `K / F` is an algebraic extension, `v` is a place of `K`, then `v` is called
unramified for `K / F`, if `w` is unramified for `K / F`, where `w` is any extension of `v` to the
algebraic closure of `K`. -/
def IsUnramified
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue K ℝ) : Prop :=
  (v.exists_liesOver (AlgebraicClosure K)).choose.IsUnramifiedOfIsScalarTower F K

theorem isUnramified_iff_ramificationIdx_eq_one
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue K ℝ) :
    v.IsUnramified F ↔ v.ramificationIdx F = 1 :=
  isUnramifiedOfIsScalarTower_iff_ramificationIdxOfIsScalarTower_eq_one ..

theorem isUnramified_spec
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v] :
    haveI := Algebra.IsAlgebraic.tower_bot F K L
    v.IsUnramified F ↔ w.IsUnramifiedOfIsScalarTower F K := by
  rw [isUnramified_iff_ramificationIdx_eq_one, v.ramificationIdx_spec F w,
    isUnramifiedOfIsScalarTower_iff_ramificationIdxOfIsScalarTower_eq_one]

namespace IsUnramified

theorem tower_top
    {F : Type*} (K : Type*) {M : Type*} [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M] [Algebra.IsAlgebraic F M]
    {v : AbsoluteValue M ℝ} (H : v.IsUnramified F) :
    haveI := Algebra.IsAlgebraic.tower_top (K := F) (L := K) (A := M); v.IsUnramified K := by
  simp only [isUnramified_iff_ramificationIdx_eq_one] at H ⊢
  rw [← v.ramificationIdx_mul_ramificationIdx F K (v.comp (algebraMap K M).injective),
    mul_eq_one] at H
  exact H.2

theorem tower_bot
    {F K M : Type*} [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M] [Algebra.IsAlgebraic F M]
    {v : AbsoluteValue M ℝ} (H : v.IsUnramified F) (w : AbsoluteValue K ℝ) [v.LiesOver w] :
    haveI := Algebra.IsAlgebraic.tower_bot (K := F) (L := K) (A := M); w.IsUnramified F := by
  simp only [isUnramified_iff_ramificationIdx_eq_one] at H ⊢
  rw [← v.ramificationIdx_mul_ramificationIdx F K w, mul_eq_one] at H
  exact H.1

theorem trans
    {F K M : Type*} [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
    [Algebra.IsAlgebraic F K] [Algebra.IsAlgebraic K M]
    {v : AbsoluteValue M ℝ} {w : AbsoluteValue K ℝ} (H1 : w.IsUnramified F)
    (H2 : v.IsUnramified K) [v.LiesOver w] :
    haveI := Algebra.IsAlgebraic.trans F K M; v.IsUnramified F := by
  have := Algebra.IsAlgebraic.trans F K M
  simp only [isUnramified_iff_ramificationIdx_eq_one] at H1 H2 ⊢
  rw [← v.ramificationIdx_mul_ramificationIdx F K w, H1, H2, one_mul]

end IsUnramified

/-- If `L / K` is an algebraic extension, `L / F` is a field extension, `v` is a place of `F`, then
`v` is called unramified for `L / K`, if all place `w` of `L` above `v` is
unramified for `L / K`. -/
def IsUnramifiedIn
    {F : Type*} (K L : Type*) [Field F] [Field K] [Field L]
    [Algebra F L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue F ℝ) : Prop :=
    ∀ w : AbsoluteValue L ℝ, w.LiesOver v → w.IsUnramified K

@[simp]
theorem isUnramifiedIn_self_iff
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue K ℝ) :
    v.IsUnramifiedIn F K ↔ v.IsUnramified F := by
  simp [IsUnramifiedIn, liesOver_self_iff]

end AbsoluteValue
