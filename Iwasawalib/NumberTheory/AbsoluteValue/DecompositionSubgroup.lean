/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.Algebra.Algebra.Equiv
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Iwasawalib.NumberTheory.AbsoluteValue.GelfandTornheim
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Iwasawalib.Topology.Algebra.Group.Basic

@[expose] public section

/-!

# Decomposition subgroup for a place (`AbsoluteValue`)

(To be written)

References:

- [J. W. S. Cassels, A. Frohlich, editors, *Algebraic Number Theory*][cassels1967algebraic]
- [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

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

/-- TODO: go mathlib -/
theorem zpow_unbounded_of_ne_one {K : Type*} [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] [Archimedean K] [ExistsAddOfLE K] (x : K) {y : K}
    (hy0 : 0 < y) (hy1 : y ≠ 1) : ∃ (n : ℤ), x < y ^ n := by
  rcases hy1.lt_or_gt with hy1' | hy1'
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (one_lt_inv_iff₀.2 ⟨hy0, hy1'⟩)
    exact ⟨-n, by simpa using hn⟩
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x hy1'
    exact ⟨n, by simpa⟩

-- proof partially provided by AI
/-- If `a < b`, `b, c, d` are positive and `c ≠ 1`, `e` is any element, then there are
`m : ℕ` and `n : ℤ` such that `a ^ m * c ^ n < d` and `e < b ^ m * c ^ n`.

TODO: go mathlib -/
theorem exists_pow_mul_zpow_lt_and_lt_pow_mul_zpow_of_lt {K : Type*} [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] [Archimedean K] [ExistsAddOfLE K] {a b c d : K} (e : K)
    (h : a < b) (hb₀ : 0 < b) (hc₀ : 0 < c) (hc₁ : c ≠ 1) (hd₀ : 0 < d) :
    ∃ (m : ℕ) (n : ℤ), a ^ m * c ^ n < d ∧ e < b ^ m * c ^ n := by
  rcases le_or_gt a 0 with ha | ha
  · obtain ⟨n, hn⟩ := zpow_unbounded_of_ne_one (e / b) hc₀ hc₁
    rw [div_lt_iff₀' hb₀] at hn
    use 1, n
    simp only [pow_one]
    exact ⟨(mul_nonpos_of_nonpos_of_nonneg ha (zpow_pos hc₀ n).le).trans_lt hd₀, hn⟩
  · obtain ⟨m₀, n₀, hα, hβ⟩ := exists_one_btwn_pow_mul_zpow_of_lt h hb₀ hc₀ hc₁
    let α := a ^ m₀ * c ^ n₀
    let β := b ^ m₀ * c ^ n₀
    obtain ⟨k, hk₁, hk₂⟩ : ∃ k, α ^ k < d ∧ e < β ^ k := by
      obtain ⟨k₁, hk₁⟩ := exists_pow_lt_of_lt_one hd₀ hα
      obtain ⟨k₂, hk₂⟩ := pow_unbounded_of_one_lt e hβ
      exact ⟨max k₁ k₂, (pow_le_pow_of_le_one (by positivity) hα.le (by simp)).trans_lt hk₁,
        hk₂.trans_le (pow_le_pow_right₀ hβ.le (by simp))⟩
    use m₀ * k, n₀ * k
    simpa only [pow_mul, zpow_mul, zpow_natCast, ← mul_pow] using ⟨hk₁, hk₂⟩

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

variable {F} in
theorem mem_decompositionSubgroup_iff :
    σ ∈ v.decompositionSubgroup F ↔ v.comp (f := σ) σ.injective = v := by
  rw [← inv_mem_iff, decompositionSubgroup, MulAction.mem_stabilizer_iff, algEquiv_smul_def]

variable {F} in
theorem mem_decompositionSubgroup_iff_forall_apply_eq :
    σ ∈ v.decompositionSubgroup F ↔ ∀ x, v (σ x) = v x := by
  simp [mem_decompositionSubgroup_iff, AbsoluteValue.ext_iff]

variable {v} in
theorem decompositionSubgroup_eq_of_equiv {w : AbsoluteValue K S} (h : v ≈ w) :
    v.decompositionSubgroup F = w.decompositionSubgroup F := by
  ext σ
  simp [mem_decompositionSubgroup_iff_forall_apply_eq, AbsoluteValue.IsEquiv.eq_iff_eq h]

theorem decompositionSubgroup_eq_top_of_not_isNontrivial (h : ¬v.IsNontrivial) :
    v.decompositionSubgroup F = ⊤ := by
  rw [eq_top_iff]
  rintro σ -
  rw [mem_decompositionSubgroup_iff]
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [not_isNontrivial_apply h, hx]

variable {F σ}

theorem apply_eq_of_mem_decompositionSubgroup
    (h : σ ∈ v.decompositionSubgroup F) (x) : v (σ x) = v x :=
  (v.mem_decompositionSubgroup_iff_forall_apply_eq σ).1 h x

/-- The elements in decomposition subgroup preserve the set `{x | v x ≤ y}` for all `y`. -/
theorem image_setOf_eq_of_mem_decompositionSubgroup
    (h : σ ∈ v.decompositionSubgroup F) (y) : σ '' {x | v x ≤ y} = {x | v x ≤ y} := by
  ext x
  obtain ⟨x', rfl⟩ := σ.surjective x
  simp [(mem_decompositionSubgroup_iff_forall_apply_eq ..).1 h x']

theorem decompositionSubgroup_comp_algEquiv_eq_comap {K' : Type*} [Semiring K'] [Algebra F K']
    (f : K' ≃ₐ[F] K) :
    (v.comp (f := (f : K' →+* K)) f.injective).decompositionSubgroup F =
      (v.decompositionSubgroup F).comap f.autCongr := by
  ext σ
  simp only [mem_decompositionSubgroup_iff_forall_apply_eq, comp_apply, RingHom.coe_coe,
    Subgroup.mem_comap, MonoidHom.coe_coe, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]
  refine ⟨fun h ↦ by simp [h], fun h x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := f.symm.surjective x
  simp [h]

theorem decompositionSubgroup_comp_ringEquiv_eq_comap
    {F E : Type*} [CommSemiring F] [Semiring E] [Algebra F E]
    {M N : Type*} [CommSemiring M] [Semiring N] [Algebra M N]
    {f : F →+* M} {g : E ≃+* N} (v : AbsoluteValue N S)
    (hsurj : Function.Surjective f)
    (hcomp : (algebraMap M N).comp f = RingHom.comp g (algebraMap F E)) :
    (v.comp (f := (g : E →+* N)) g.injective).decompositionSubgroup F =
      (v.decompositionSubgroup M).comap (AlgEquiv.autCongrOfSurjective hsurj hcomp) := by
  ext σ
  simp only [mem_decompositionSubgroup_iff_forall_apply_eq, comp_apply, RingHom.coe_coe,
    Subgroup.mem_comap, MonoidHom.coe_coe, AlgEquiv.autCongrOfSurjective_apply_apply]
  refine ⟨fun h ↦ by simp [h], fun h x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := g.symm.surjective x
  simp [h]

open scoped Pointwise in
theorem decompositionSubgroup_comp_algEquiv_eq_smul (f : K ≃ₐ[F] K) :
    (v.comp (f := (f : K →+* K)) f.injective).decompositionSubgroup F =
      (MulAut.conj f)⁻¹ • v.decompositionSubgroup F := by
  rw [decompositionSubgroup_comp_algEquiv_eq_comap]
  ext σ
  simp only [Subgroup.mem_comap, MonoidHom.coe_coe, AlgEquiv.autCongr_apply,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, MulAut.smul_def, MulAut.conj_apply]
  rfl

end General

section IsAlgebraic

variable (F K : Type*) [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
  (v : AbsoluteValue K ℝ) (σ : Gal(K/F))

variable {F K}

/-- If `K / F` is algebraic, then the decomposition subgroup `Dᵥ(K/F)` is also the subgroup
consists of all `σ` preserving the set `{x | v x ≤ 1}`.

NOTE: This is not true if `K / F` is not algebraic, for example, when `K` is the fraction field of
the valuation ring $\bigcup_{n=1}^\infty F⟦X^{1/n}⟧$, `k ≥ 2` is a fixed positive integer, `σ` is
$X^{1/n} \mapsto X^{k/n}$, then it preserves the valuation ring but doesn't preserve the valuation.
-/
theorem mem_decompositionSubgroup_iff_image_setOf_eq :
    σ ∈ v.decompositionSubgroup F ↔ σ '' {x | v x ≤ 1} = {x | v x ≤ 1} := by
  refine ⟨fun h ↦ v.image_setOf_eq_of_mem_decompositionSubgroup h 1, fun h ↦ ?_⟩
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
  refine ⟨fun h ↦ v.continuous_of_mem_decompositionSubgroup h, fun h ↦ ?_⟩
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

variable (F)

/-- Our definition is the same as `ValuationSubring.decompositionSubgroup` for finite places. -/
theorem decompositionSubgroup_eq_of_isNonarchimedean (h : IsNonarchimedean v) :
    v.decompositionSubgroup F = (v.toValuation h).valuationSubring.decompositionSubgroup F := by
  ext g
  simp only [mem_decompositionSubgroup_iff_image_setOf_eq, MulAction.mem_stabilizer_iff,
    SetLike.ext'_iff]
  congr!

end IsAlgebraic

section IsScalarTower

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
  {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
  {S : Type*} [Semiring S] [PartialOrder S] (v : AbsoluteValue L S)

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Dᵥ(L/K) = Dᵥ(L/F) ⊓ Gal(L/K)`. -/
theorem decompositionSubgroup_eq_comap :
    v.decompositionSubgroup K = (v.decompositionSubgroup F).comap
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) := by
  ext
  simp [mem_decompositionSubgroup_iff, IntermediateField.restrictRestrictAlgEquivMapHom]

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Dᵥ(L/K) ≤ Dᵥ(L/F)`. -/
theorem map_decompositionSubgroup_le :
    (v.decompositionSubgroup K).map
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) ≤ v.decompositionSubgroup F := by
  simpa only [Subgroup.map_le_iff_le_comap] using (v.decompositionSubgroup_eq_comap F K).le

end IsScalarTower

/-- Decomposition subgroup for an infinite place is either trivial or `ℤ/2ℤ`. This is because the
decomposition subgroup can be viewed as Galois group of completions of fields with respect to
valuations (didn't formalized yet), in the archimedean case they must be `ℝ` or `ℂ`. -/
theorem card_decompositionSubgroup_dvd_two_of_not_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : ¬IsNonarchimedean v) :
    Nat.card (v.decompositionSubgroup F) ∣ 2 := by
  sorry

/-- If `v : ι → AbsoluteValue R S` is a finite collection of non-trivial and pairwise inequivalent
absolute values, then for any `ε > 0` and any `i : ι` there is some `z : R` such that
`v i (z - 1) < ε` and `v j z < ε` for all `j ≠ i`.

TODO: go mathlib -/
theorem exists_sub_one_lt_and_lt_of_not_isEquiv
    {R S : Type*} [Field R] [Field S] [LinearOrder S] [TopologicalSpace S] [IsStrictOrderedRing S]
    [Archimedean S] [OrderTopology S] {ι : Type*} [Finite ι]
    {v : ι → AbsoluteValue R S} (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) {ε : S} (hε : 0 < ε) (i : ι) :
    ∃ z, v i (z - 1) < ε ∧ ∀ j ≠ i, v j z < ε := by
  obtain ⟨a, ha1, ha2⟩ := exists_one_lt_lt_one_pi_of_not_isEquiv h hv i
  have ha : a ≠ 0 := fun H ↦ by simp only [H, map_zero] at ha1; exact ha1.not_ge zero_le_one
  have h1am (m : ℕ) (hm : m ≠ 0) : 1 + a ^ m ≠ 0 := fun H ↦ by
    rw [add_eq_zero_iff_eq_neg'] at H
    apply_fun v i at H
    simp only [map_pow, AbsoluteValue.map_neg, map_one] at H
    simpa [H] using one_lt_pow₀ ha1 hm
  obtain ⟨N1, hN1⟩ : ∃ N : ℕ, ∀ m ≥ N, v i (a ^ m / (1 + a ^ m) - 1) < ε := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 + ε⁻¹) ha1
    refine ⟨N + 1, fun m hm ↦ ?_⟩
    have hv1am : (v i (1 + a ^ m))⁻¹ < ε := by
      apply inv_lt_of_inv_lt₀ hε
      rw [add_comm]
      refine ((v i).le_add ..).trans_lt' ?_
      rw [map_one, lt_sub_iff_add_lt', map_pow]
      exact hN.trans (pow_lt_pow_right₀ ha1 hm)
    simpa [div_sub_one (h1am m (by linarith))]
  have h2 (j : {j : ι // j ≠ i}) : ∃ N : ℕ, ∀ m ≥ N, v j (a ^ m / (1 + a ^ m)) < ε := by
    have hε' : 0 < min (ε / 2) (1 / 2) := by positivity
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε' (ha2 j j.2)
    refine ⟨N + 1, fun m hm ↦ ?_⟩
    rw [map_div₀, div_lt_iff₀ ((v j).pos (h1am m (by linarith)))]
    have := (pow_lt_pow_right_of_lt_one₀ ((v j).pos ha) (ha2 j j.2) hm).trans hN
    trans ε * 2⁻¹
    · simpa [← div_eq_mul_inv] using this.trans_le (min_le_left ..)
    · rw [mul_lt_mul_iff_right₀ hε]
      refine ((v j).le_add ..).trans_lt' ?_
      rw [lt_sub_comm, map_one, map_pow]
      refine (this.trans_le (min_le_right ..)).trans_eq ?_
      norm_num
  choose N2 hN2 using h2
  let N := max N1 (⨆ j, N2 j)
  exact ⟨a ^ N / (1 + a ^ N), hN1 _ (le_max_left ..),
    fun j hj ↦ hN2 ⟨j, hj⟩ _ ((le_max_right ..).trans' (Finite.le_ciSup ..))⟩

/-- A version of **Approximation Theorem**: if `v : ι → AbsoluteValue R S` is a finite collection
of non-trivial and pairwise inequivalent absolute values, `a : ι → R` is a sequence of elements
in `R`, then for any `ε > 0` there is some `x : R` such that `v i (x - a i) < ε` for all `i`.
See [Neukirch1992], II.3.4.

TODO: go mathlib -/
theorem exists_sub_lt_of_not_isEquiv
    {R S : Type*} [Field R] [Field S] [LinearOrder S] [TopologicalSpace S] [IsStrictOrderedRing S]
    [Archimedean S] [OrderTopology S] {ι : Type*} [Finite ι]
    {v : ι → AbsoluteValue R S} (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) (a : ι → R) {ε : S} (hε : 0 < ε) :
    ∃ x, ∀ i, v i (x - a i) < ε := by
  classical
  let := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with _ | hnonempty
  · exact ⟨0, by simp⟩
  let M := (Finset.image (fun i : ι × ι ↦ v i.1 (a i.2)) .univ).max' (by simp)
  have hM (i j : ι) : v i (a j) ≤ M := Finset.le_max' _ _ (by simp)
  have hMnonneg : 0 ≤ M := ((v _).nonneg _).trans (hM hnonempty.some hnonempty.some)
  have hcard : 0 < Nat.card ι := Nat.card_pos
  have hε' : 0 < ε / (1 + M) / Nat.card ι := by positivity
  choose z hz using exists_sub_one_lt_and_lt_of_not_isEquiv h hv hε'
  use ∑ j, a j * z j
  intro i
  rw [← Finset.sum_compl_add_sum {i}, Finset.sum_singleton, add_sub_assoc, ← mul_sub_one]
  grw [(v i).add_le, (v i).sum_le]
  simp_rw [map_mul]
  calc
  _ ≤ ∑ x ∈ {i}ᶜ, M * (ε / (1 + M) / Nat.card ι) + M * (ε / (1 + M) / Nat.card ι) := by
    refine add_le_add ?_ (mul_le_mul_of_nonneg (hM i i) (hz i).1.le ((v i).nonneg _) hε'.le)
    gcongr 1 with x hx
    refine mul_le_mul_of_nonneg (hM i x) ((hz x).2 i (Ne.symm ?_)).le ((v i).nonneg _) hε'.le
    simpa using hx
  _ < _ := by
    rw [Finset.sum_const, nsmul_eq_mul, ← add_one_mul]
    norm_cast
    rw [← Finset.card_singleton i, Finset.card_compl_add_card, ← Nat.card_eq_fintype_card,
      ← mul_div_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ (by simp), ← mul_div_assoc,
      mul_div_right_comm]
    nth_rw 2 [← one_mul ε]
    refine mul_lt_mul ?_ le_rfl hε zero_le_one
    simp [div_lt_one₀ (show 0 < 1 + M by positivity)]

/-- If `K / F` is an algebraic extension, then any place `v` of `F` can be extended to `K`.
(Is this correct?) -/
theorem exists_liesOver
    {F : Type*} (K : Type*) [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue F ℝ) : ∃ w : AbsoluteValue K ℝ, w.LiesOver v := by
  sorry

/-- If `K / F` is a normal extension, then any two places of `K` which coincide when
restrict to `F` are conjugate by an element of `Gal(K/F)`.
See [Neukirch1992], II.9.1. -/
theorem exists_algEquiv_comp_eq_of_comp_eq
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Normal F K]
    {v w : AbsoluteValue K ℝ}
    (h : v.comp (algebraMap F K).injective = w.comp (algebraMap F K).injective) :
    ∃ σ : Gal(K/F), v.comp (f := σ) σ.injective = w := by
  -- proof uses the above `exists_sub_lt_of_not_isEquiv`
  sorry

/-- If `L / K / F` is an extension tower, `L / F` and `K / F` are Galois, `v` and `w` are places of
`K` and `L`, respectively, such that `w` lies over `v`, then the image of `D_w(L/F)` in `Gal(K/F)`
is equal to `Dᵥ(K/F)`. -/
theorem map_decompositionSubgroup_eq_of_liesOver
    (F : Type*) {K L : Type*} [Field F] [Field K] [Algebra F K] [Field L]
    [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F K] [Normal F L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v] :
    (w.decompositionSubgroup F).map (AlgEquiv.restrictNormalHom K) =
      v.decompositionSubgroup F := by
  ext σ
  simp only [← LiesOver.comp_eq w v, Subgroup.mem_map]
  refine ⟨fun ⟨τ, hτ, hτ2⟩ ↦ ?_, fun hσ ↦ ?_⟩
  · rw [← hτ2]
    rw [mem_decompositionSubgroup_iff_forall_apply_eq] at hτ ⊢
    intro x
    simpa [AlgEquiv.restrictNormalHom] using hτ (algebraMap K L x)
  · obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    have h : (w.comp (f := τ) τ.injective).comp (algebraMap K L).injective =
        w.comp (algebraMap K L).injective := by
      ext x
      rw [mem_decompositionSubgroup_iff_forall_apply_eq] at hσ
      simpa [AlgEquiv.restrictNormalHom] using hσ x
    have := Normal.tower_top_of_normal F K L
    obtain ⟨τ', hτ'⟩ := exists_algEquiv_comp_eq_of_comp_eq h
    use τ * IntermediateField.restrictRestrictAlgEquivMapHom F L K L τ'
    constructor
    · rw [mem_decompositionSubgroup_iff_forall_apply_eq]
      intro x
      simpa [IntermediateField.restrictRestrictAlgEquivMapHom] using congr($(hτ') x)
    · ext x
      rw [map_mul, AlgEquiv.mul_apply, EmbeddingLike.apply_eq_iff_eq]
      apply_fun _ using (algebraMap K L).injective
      simp only [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply, AlgEquiv.restrictNormal_commutes]
      simp [IntermediateField.restrictRestrictAlgEquivMapHom]

end AbsoluteValue
