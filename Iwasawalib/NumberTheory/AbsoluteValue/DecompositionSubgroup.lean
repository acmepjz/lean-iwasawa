/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.Algebra.Algebra.Equiv
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Iwasawalib.NumberTheory.AbsoluteValue.GelfandTornheim
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
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

/-- Decomposition subgroup for an infinite place is either trivial or `ℤ/2ℤ`. By the
Gelfand-Tornheim theorem the place comes from an embedding `φ : K →+* ℂ`; an element of the
decomposition subgroup does not change the place, hence composing it with `φ` gives back either
`φ` or its complex conjugate, and this assignment is injective. -/
theorem card_decompositionSubgroup_dvd_two_of_not_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : ¬IsNonarchimedean v) :
    Nat.card (v.decompositionSubgroup F) ∣ 2 := by
  classical
  obtain ⟨φ, hφ⟩ := v.exists_ringHom_complex_of_not_isNonarchimedean h
  obtain ⟨c, hc, hcv⟩ := isEquiv_iff_exists_rpow_eq.1 hφ
  -- every element of the decomposition subgroup composes `φ` into `φ` or into its conjugate
  have hmap : ∀ σ : v.decompositionSubgroup F,
      φ.comp ((σ : Gal(K/F)) : K →+* K) = φ ∨
        φ.comp ((σ : Gal(K/F)) : K →+* K) = NumberField.ComplexEmbedding.conjugate φ := by
    intro σ
    have hpl : NumberField.place (φ.comp ((σ : Gal(K/F)) : K →+* K)) = NumberField.place φ := by
      ext x
      have h1 : v ((σ : Gal(K/F)) x) = v x :=
        v.apply_eq_of_mem_decompositionSubgroup σ.2 x
      have h2 := congrFun hcv ((σ : Gal(K/F)) x)
      have h3 := congrFun hcv x
      have h4 : NumberField.place φ ((σ : Gal(K/F)) x) ^ c = NumberField.place φ x ^ c := by
        rw [h2, h3, h1]
      have h5 := congrArg (fun t : ℝ => t ^ c⁻¹) h4
      simp only [Real.rpow_rpow_inv ((NumberField.place φ).nonneg _) hc.ne'] at h5
      show ‖φ ((σ : Gal(K/F)) x)‖ = ‖φ x‖
      exact h5
    rcases NumberField.InfinitePlace.mk_eq_iff.1 (Subtype.ext hpl :
        NumberField.InfinitePlace.mk (φ.comp ((σ : Gal(K/F)) : K →+* K)) =
          NumberField.InfinitePlace.mk φ) with h1 | h1
    · exact Or.inl h1
    · right
      have h2 := congrArg NumberField.ComplexEmbedding.conjugate h1
      rwa [NumberField.ComplexEmbedding.involutive_conjugate K _] at h2
  -- hence the decomposition subgroup injects into a set with two elements
  have hinj : Function.Injective
      (fun σ : v.decompositionSubgroup F => decide (φ.comp ((σ : Gal(K/F)) : K →+* K) = φ)) := by
    intro σ τ hst
    have key : φ.comp ((σ : Gal(K/F)) : K →+* K) = φ.comp ((τ : Gal(K/F)) : K →+* K) := by
      by_cases hσ : φ.comp ((σ : Gal(K/F)) : K →+* K) = φ
      · have hτ : φ.comp ((τ : Gal(K/F)) : K →+* K) = φ := by
          simpa [hσ] using hst.symm
        rw [hσ, hτ]
      · have hτ : ¬ φ.comp ((τ : Gal(K/F)) : K →+* K) = φ := by
          simpa [hσ] using hst.symm
        rw [(hmap σ).resolve_left hσ, (hmap τ).resolve_left hτ]
    ext x
    have h1 := congr($key x)
    simpa using φ.injective h1
  have hfin : Finite (v.decompositionSubgroup F) := Finite.of_injective _ hinj
  have h2 : Nat.card (v.decompositionSubgroup F) ≤ 2 := by
    simpa using Nat.card_le_card_of_injective _ hinj
  have h1 : 0 < Nat.card (v.decompositionSubgroup F) := Nat.card_pos
  interval_cases hcard : Nat.card (v.decompositionSubgroup F) <;> simp

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

section Extension

open WithAbs

/-- The completion of a field with respect to a nonarchimedean absolute value is
an ultrametric normed field. -/
theorem isUltrametricDist_completion {F : Type*} [Field F] {v : AbsoluteValue F ℝ}
    (h : IsNonarchimedean v) : IsUltrametricDist v.Completion := by
  refine IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm ?_
  have hcl : IsClosed {p : v.Completion × v.Completion | ‖p.1 + p.2‖ ≤ max ‖p.1‖ ‖p.2‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hdense : DenseRange (Prod.map (UniformSpace.Completion.coe' (α := WithAbs v))
      (UniformSpace.Completion.coe' (α := WithAbs v))) :=
    UniformSpace.Completion.denseRange_coe.prodMap UniformSpace.Completion.denseRange_coe
  have hsub : Set.range (Prod.map (UniformSpace.Completion.coe' (α := WithAbs v))
      (UniformSpace.Completion.coe' (α := WithAbs v))) ⊆
      {p : v.Completion × v.Completion | ‖p.1 + p.2‖ ≤ max ‖p.1‖ ‖p.2‖} := by
    rintro p ⟨⟨x, y⟩, hp⟩
    subst hp
    simp only [Set.mem_ofPred_eq, Prod.map_apply]
    rw [← UniformSpace.Completion.coe_add]
    simp only [UniformSpace.Completion.norm_coe]
    exact h (ofAbs x) (ofAbs y)
  intro x y
  exact (hdense.closure_range ▸ (hcl.closure_subset_iff.2 hsub)) (Set.mem_univ (x, y))

/-- If `K / F` is an algebraic extension, then any nontrivial nonarchimedean place `v` of `F`
can be extended to `K`. This is proved by taking the spectral norm on an algebraic closure of
the completion of `F` at `v`. -/
theorem exists_liesOver_of_isNonarchimedean
    {F : Type*} (K : Type*) [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue F ℝ) (hna : IsNonarchimedean v) (hnt : v.IsNontrivial) :
    ∃ w : AbsoluteValue K ℝ, w.LiesOver v := by
  have hnorm : ∀ x : F, ‖algebraMap F v.Completion x‖ = v x := fun x =>
    UniformSpace.Completion.norm_coe (WithAbs.toAbs v x)
  letI : IsUltrametricDist v.Completion := isUltrametricDist_completion hna
  letI : NontriviallyNormedField v.Completion :=
    { (inferInstance : NormedField v.Completion) with
      non_trivial := by
        obtain ⟨y, hy⟩ := hnt.exists_abv_gt_one
        exact ⟨algebraMap F _ y, by rwa [hnorm]⟩ }
  let Ω := AlgebraicClosure v.Completion
  let ψ : K →ₐ[F] Ω := IsAlgClosed.lift
  have h1 : ∀ x : F,
      ψ (algebraMap F K x) = algebraMap v.Completion Ω (algebraMap F v.Completion x) := by
    intro x
    rw [AlgHom.commutes]
    exact IsScalarTower.algebraMap_apply F v.Completion Ω x
  letI : NormedField Ω := spectralNorm.normedField v.Completion Ω
  let W : AbsoluteValue Ω ℝ := NormedField.toAbsoluteValue Ω
  refine ⟨W.comp (f := (ψ : K →+* Ω)) (ψ : K →+* Ω).injective, ?_⟩
  rw [liesOver_iff]
  ext x
  show W (ψ (algebraMap F K x)) = v x
  rw [h1 x]
  show spectralNorm v.Completion Ω _ = v x
  rw [spectralNorm_extends]
  exact hnorm x

/-- If `K / F` is an algebraic extension, then any archimedean place `v` of `F`
can be extended to `K`. This is proved by the Gelfand-Tornheim theorem. -/
theorem exists_liesOver_of_not_isNonarchimedean
    {F : Type*} (K : Type*) [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue F ℝ) (h : ¬ IsNonarchimedean v) :
    ∃ w : AbsoluteValue K ℝ, w.LiesOver v := by
  obtain ⟨φ, hφ⟩ := v.exists_ringHom_complex_of_not_isNonarchimedean h
  letI : Algebra F ℂ := φ.toAlgebra
  let ψ : K →ₐ[F] ℂ := IsAlgClosed.lift
  let w₀ : AbsoluteValue K ℝ := NumberField.place (ψ : K →+* ℂ)
  have hres : w₀.comp (algebraMap F K).injective ≈ v := by
    refine IsEquiv.trans ?_ hφ
    have h1 : w₀.comp (algebraMap F K).injective = NumberField.place φ := by
      ext x
      show ‖ψ (algebraMap F K x)‖ = ‖φ x‖
      rw [AlgHom.commutes]
      rfl
    rw [h1]
    exact IsEquiv.rfl
  obtain ⟨w, -, hw⟩ := exists_equiv_and_liesOver_of_comp_equiv w₀ v hres
  exact ⟨w, hw⟩

/-- A trivial place of `F` extends to the trivial place of any extension field. -/
theorem exists_liesOver_of_not_isNontrivial
    {F : Type*} (K : Type*) [Field F] [Field K] [Algebra F K]
    (v : AbsoluteValue F ℝ) (h : ¬ v.IsNontrivial) :
    ∃ w : AbsoluteValue K ℝ, w.LiesOver v := by
  classical
  refine ⟨AbsoluteValue.trivial, ?_⟩
  rw [liesOver_iff]
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [comp_apply, AbsoluteValue.trivial_apply (by simpa using hx), not_isNontrivial_apply h hx]

/-- If `K / F` is an algebraic extension, then any place `v` of `F` can be extended to `K`. -/
theorem exists_liesOver
    {F : Type*} (K : Type*) [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue F ℝ) : ∃ w : AbsoluteValue K ℝ, w.LiesOver v := by
  by_cases hna : IsNonarchimedean v
  · by_cases hnt : v.IsNontrivial
    · exact exists_liesOver_of_isNonarchimedean K v hna hnt
    · exact exists_liesOver_of_not_isNontrivial K v hnt
  · exact exists_liesOver_of_not_isNonarchimedean K v hna

end Extension

section Conjugate

open Polynomial IntermediateField

/-- If two real absolute values on a field are equivalent and agree at one nonzero element
whose value is not `1`, then they are equal. -/
theorem eq_of_isEquiv_of_apply_eq {K : Type*} [Field K] {v w : AbsoluteValue K ℝ}
    (h : v.IsEquiv w) {t : K} (ht : v t = w t) (ht1 : v t ≠ 1) (ht0 : t ≠ 0) : v = w := by
  obtain ⟨c, hc, hcw⟩ := isEquiv_iff_exists_rpow_eq.1 h
  have h1 : v t ^ c = v t := by
    have h2 := congrFun hcw t
    rw [← ht] at h2
    exact h2
  have hvt : 0 < v t := v.pos ht0
  have hc1 : c = 1 := by
    have h2 := congrArg Real.log h1
    rw [Real.log_rpow hvt] at h2
    have hlog : Real.log (v t) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hvt ht1
    field_simp at h2
    tauto
  ext x
  have h2 := congrFun hcw x
  rw [hc1, Real.rpow_one] at h2
  exact h2

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem isNontrivial_smul {v : AbsoluteValue K ℝ} (σ : Gal(K/F)) (h : v.IsNontrivial) :
    (σ • v).IsNontrivial := by
  obtain ⟨x, hx0, hx1⟩ := h
  exact ⟨σ x, by simpa using hx0, by simpa using hx1⟩

theorem smul_comp_algebraMap (v : AbsoluteValue K ℝ) (σ : Gal(K/F)) :
    (σ • v).comp (algebraMap F K).injective = v.comp (algebraMap F K).injective := by
  ext x; simp

/-- Two absolute values of `K` which restrict to the same nontrivial absolute value of `F`
are equal as soon as they are equivalent. -/
theorem eq_of_isEquiv_of_comp_eq {v w : AbsoluteValue K ℝ}
    (hu : (v.comp (algebraMap F K).injective).IsNontrivial)
    (h : v.comp (algebraMap F K).injective = w.comp (algebraMap F K).injective)
    (he : v.IsEquiv w) : v = w := by
  obtain ⟨t, ht0, ht1⟩ := hu
  exact eq_of_isEquiv_of_apply_eq he (t := algebraMap F K t) (congr($h t)) ht1 (by simpa using ht0)

/-- If `K / F` is a finite normal extension, then any two places of `K` which coincide when
restricted to `F` are conjugate by an element of `Gal(K/F)`. This is the finite case of
[Neukirch1992], II.9.1; it is proved by the approximation theorem
`AbsoluteValue.exists_sub_lt_of_not_isEquiv` together with a comparison of the constant term of
the minimal polynomial. -/
theorem exists_smul_eq_of_comp_eq_of_finiteDimensional [Normal F K] [FiniteDimensional F K]
    {v w : AbsoluteValue K ℝ}
    (h : v.comp (algebraMap F K).injective = w.comp (algebraMap F K).injective) :
    ∃ σ : Gal(K/F), σ • v = w := by
  classical
  -- elementary facts on products of multisets of real numbers
  have one_le_prod : ∀ m : Multiset ℝ, (∀ y ∈ m, 1 ≤ y) → 1 ≤ m.prod := by
    intro m
    induction m using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      intro hm
      rw [Multiset.prod_cons]
      have h1 : 1 ≤ a := hm a (Multiset.mem_cons_self a t)
      have h2 : 1 ≤ t.prod := ih fun y hy => hm y (Multiset.mem_cons_of_mem hy)
      nlinarith
  have one_lt_prod : ∀ m : Multiset ℝ, m ≠ 0 → (∀ y ∈ m, 1 < y) → 1 < m.prod := by
    intro m hm hy
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hm
    obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
    rw [Multiset.prod_cons]
    have h1 : 1 < a := hy a (Multiset.mem_cons_self a t)
    have h2 : 1 ≤ t.prod := one_le_prod t fun y hy' => (hy y (Multiset.mem_cons_of_mem hy')).le
    nlinarith
  have prod_le_one : ∀ m : Multiset ℝ, (∀ y ∈ m, 0 ≤ y ∧ y ≤ 1) → m.prod ≤ 1 := by
    intro m
    induction m using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      intro hm
      rw [Multiset.prod_cons]
      obtain ⟨ha0, ha1⟩ := hm a (Multiset.mem_cons_self a t)
      have h2 := ih fun y hy => hm y (Multiset.mem_cons_of_mem hy)
      have h3 : 0 ≤ t.prod :=
        Multiset.prod_nonneg fun y hy => (hm y (Multiset.mem_cons_of_mem hy)).1
      nlinarith
  by_cases htriv : (v.comp (algebraMap F K).injective).IsNontrivial
  swap
  · -- if the restriction to `F` is trivial, then both `v` and `w` are trivial
    have hv : ¬ v.IsNontrivial := by
      rwa [← isNontrivial_iff_of_liesOver (v.comp (algebraMap F K).injective) v]
    have hw : ¬ w.IsNontrivial := by
      rw [← isNontrivial_iff_of_liesOver (w.comp (algebraMap F K).injective) w, ← h]
      exact htriv
    refine ⟨1, ?_⟩
    ext x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · simp [not_isNontrivial_apply hv, not_isNontrivial_apply hw, hx]
  have hv : v.IsNontrivial :=
    (isNontrivial_iff_of_liesOver (v.comp (algebraMap F K).injective) v).1 htriv
  have hw : w.IsNontrivial :=
    (isNontrivial_iff_of_liesOver (w.comp (algebraMap F K).injective) w).1 (h ▸ htriv)
  by_contra! H
  -- the `Gal(K/F)`-orbits of `v` and of `w` are disjoint
  have hdisj : ∀ σ τ : Gal(K/F), σ • v ≠ τ • w := fun σ τ hst =>
    H (τ⁻¹ * σ) (by rw [mul_smul, hst, ← mul_smul, inv_mul_cancel, one_smul])
  set S : Set (AbsoluteValue K ℝ) :=
    (Set.range fun σ : Gal(K/F) => σ • v) ∪ (Set.range fun σ : Gal(K/F) => σ • w) with hS
  have hSfin : S.Finite := (Set.finite_range _).union (Set.finite_range _)
  have : Finite ↥S := hSfin.to_subtype
  have hnt : ∀ p : ↥S, (p : AbsoluteValue K ℝ).IsNontrivial := by
    rintro ⟨p, (⟨σ, rfl⟩ | ⟨σ, rfl⟩)⟩
    · exact isNontrivial_smul σ hv
    · exact isNontrivial_smul σ hw
  have hcomp : ∀ p : ↥S, (p : AbsoluteValue K ℝ).comp (algebraMap F K).injective =
      v.comp (algebraMap F K).injective := by
    rintro ⟨p, (⟨σ, rfl⟩ | ⟨σ, rfl⟩)⟩
    · exact smul_comp_algebraMap v σ
    · rw [smul_comp_algebraMap w σ, h]
  have hpw : Pairwise fun p q : ↥S =>
      ¬ (p : AbsoluteValue K ℝ).IsEquiv (q : AbsoluteValue K ℝ) := by
    intro p q hpq he
    exact hpq (Subtype.ext (eq_of_isEquiv_of_comp_eq (by rw [hcomp p]; exact htriv)
      (by rw [hcomp p, hcomp q]) he))
  -- choose elements of large absolute value
  have hbig : ∀ p : ↥S, ∃ a : K, 2 < (p : AbsoluteValue K ℝ) a := by
    intro p
    obtain ⟨y, hy⟩ := (hnt p).exists_abv_gt_one
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hy
    exact ⟨y ^ n, by simpa using hn⟩
  choose big hbig using hbig
  obtain ⟨x, hx⟩ := exists_sub_lt_of_not_isEquiv (v := fun p : ↥S => (p : AbsoluteValue K ℝ))
    hnt hpw (fun p => if (∃ σ : Gal(K/F), (p : AbsoluteValue K ℝ) = σ • v) then big p else 0)
    one_pos
  have hA : ∀ σ : Gal(K/F), 1 < v (σ x) := by
    intro σ
    set p : ↥S := ⟨σ⁻¹ • v, Or.inl ⟨σ⁻¹, rfl⟩⟩ with hp
    have hPv : (∃ τ : Gal(K/F), (p : AbsoluteValue K ℝ) = τ • v) := ⟨σ⁻¹, rfl⟩
    have h1 := hx p
    rw [if_pos hPv] at h1
    have h2 : |(p : AbsoluteValue K ℝ) (big p) - (p : AbsoluteValue K ℝ) x| ≤
        (p : AbsoluteValue K ℝ) (big p - x) := AbsoluteValue.abs_abv_sub_le_abv_sub _ _ _
    rw [AbsoluteValue.map_sub] at h2
    have h3 := hbig p
    have h4 : 1 < (p : AbsoluteValue K ℝ) x := by
      have h6 := abs_le.1 h2
      linarith [h6.1, h6.2]
    have h5 : (p : AbsoluteValue K ℝ) x = v (σ x) := by
      simp only [hp, algEquiv_smul_apply]
      congr 1
    rwa [h5] at h4
  have hB : ∀ σ : Gal(K/F), w (σ x) < 1 := by
    intro σ
    set p : ↥S := ⟨σ⁻¹ • w, Or.inr ⟨σ⁻¹, rfl⟩⟩ with hp
    have hPv : ¬ (∃ τ : Gal(K/F), (p : AbsoluteValue K ℝ) = τ • v) := by
      rintro ⟨τ, hτ⟩
      exact hdisj τ σ⁻¹ hτ.symm
    have h1 := hx p
    rw [if_neg hPv] at h1
    have h5 : (p : AbsoluteValue K ℝ) (x - 0) = w (σ x) := by
      simp only [hp, algEquiv_smul_apply, sub_zero]
      congr 1
    rwa [h5] at h1
  -- compare the two absolute values on the constant term of the minimal polynomial of `x`
  have hxne : x ≠ 0 := by
    intro h0
    have h1 := hA 1
    rw [h0] at h1
    simp at h1
    linarith
  have hint : IsIntegral F x := IsIntegral.of_finite F x
  set q := (minpoly F x).map (algebraMap F K) with hq
  have hqm : q.Monic := (minpoly.monic hint).map _
  have hqs : q.Splits := Normal.splits ‹Normal F K› x
  have hq0 : q ≠ 0 := hqm.ne_zero
  have hroots : ∀ β ∈ q.roots, 1 < v β ∧ w β < 1 := by
    intro β hβ
    have hev : (aeval β) (minpoly F x) = 0 := by
      have h1 := (mem_roots hq0).1 hβ
      rw [IsRoot, hq, eval_map, ← aeval_def] at h1
      exact h1
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (K := F) (L := K)
      (Algebra.IsAlgebraic.isAlgebraic x) hev
    have hβ' : β = σ⁻¹ x := by rw [← hσ]; simp
    rw [hβ']
    exact ⟨hA σ⁻¹, hB σ⁻¹⟩
  have hrne : q.roots ≠ 0 := by
    intro h0
    have h1 := hqs.natDegree_eq_card_roots
    rw [h0] at h1
    simp only [Multiset.card_zero] at h1
    have hd : 0 < q.natDegree := by
      rw [hq, natDegree_map]
      exact minpoly.natDegree_pos hint
    omega
  have hc0 : q.coeff 0 = (-1) ^ q.natDegree * q.roots.prod :=
    hqs.coeff_zero_eq_prod_roots_of_monic hqm
  have hvq : 1 < v (q.coeff 0) := by
    rw [hc0, map_mul, map_pow, AbsoluteValue.map_neg, map_one, one_pow, one_mul,
      map_multiset_prod]
    refine one_lt_prod _ (by simpa using hrne) ?_
    intro y hy
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hy
    exact (hroots β hβ).1
  have hwq : w (q.coeff 0) ≤ 1 := by
    rw [hc0, map_mul, map_pow, AbsoluteValue.map_neg, map_one, one_pow, one_mul,
      map_multiset_prod]
    refine prod_le_one _ ?_
    intro y hy
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hy
    exact ⟨w.nonneg _, (hroots β hβ).2.le⟩
  have hvw : v (q.coeff 0) = w (q.coeff 0) := by
    have h1 : q.coeff 0 = algebraMap F K ((minpoly F x).coeff 0) := by rw [hq, coeff_map]
    rw [h1]
    exact congr($h ((minpoly F x).coeff 0))
  linarith

/-- If `K / F` is a normal extension, then any two places of `K` which coincide when restricted
to `F` are conjugate by an `F`-algebra homomorphism of `K`. The general case is deduced from the
finite case `AbsoluteValue.exists_smul_eq_of_comp_eq_of_finiteDimensional` by Zorn's lemma. -/
theorem exists_algHom_apply_eq_of_comp_eq [Normal F K] {v w : AbsoluteValue K ℝ}
    (h : v.comp (algebraMap F K).injective = w.comp (algebraMap F K).injective) :
    ∃ τ : K →ₐ[F] K, ∀ x, v (τ x) = w x := by
  classical
  set P : Set (Lifts F K K) :=
    {ϕ | Normal F ϕ.carrier ∧ ∀ x : ϕ.carrier, v (ϕ.emb x) = w (x : K)} with hP
  -- the condition on the embedding is automatic on the bottom field
  have hcond : ∀ (ϕ : Lifts F K K) (x : ϕ.carrier), (x : K) ∈ (⊥ : IntermediateField F K) →
      v (ϕ.emb x) = w (x : K) := by
    intro ϕ x hx
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 hx
    have hx' : x = algebraMap F ϕ.carrier y := Subtype.ext hy.symm
    rw [hx', AlgHom.commutes]
    exact congr($h y)
  have hbot : (⊥ : Lifts F K K) ∈ P := by
    refine ⟨?_, fun x => hcond _ x ?_⟩
    · show Normal F (⊥ : IntermediateField F K)
      infer_instance
    · exact x.2
  have key : ∀ c ⊆ P, IsChain (· ≤ ·) c → ∃ ub ∈ P, ∀ z ∈ c, z ≤ ub := by
    intro c hcP hc
    rcases Set.eq_empty_or_nonempty c with rfl | ⟨ϕ₀, hϕ₀⟩
    · exact ⟨⊥, hbot, by simp⟩
    refine ⟨Lifts.union c hc, ⟨?_, ?_⟩, fun z hz => Lifts.le_union c hc hz⟩
    · rw [Lifts.carrier_union]
      have : ∀ i : c, Normal F (i : Lifts F K K).carrier := fun i => (hcP i.2).1
      have : Nonempty c := ⟨⟨ϕ₀, hϕ₀⟩⟩
      exact IntermediateField.normal_iSup F K _
    · intro x
      have hdir : Directed (· ≤ ·) (fun i : c => (i : Lifts F K K).carrier) :=
        (hc.directedOn.directed_val).mono_comp _ (fun _ _ hxy => hxy.1)
      have : Nonempty c := ⟨⟨ϕ₀, hϕ₀⟩⟩
      have hx : (x : K) ∈ ⨆ i : c, (i : Lifts F K K).carrier :=
        le_of_eq (Lifts.carrier_union c hc) x.2
      rw [← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed hdir, Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      have hle := Lifts.le_union c hc i.2
      have h2 := hle.2 ⟨(x : K), hi⟩
      have h3 : (Lifts.union c hc).emb x = (i : Lifts F K K).emb ⟨(x : K), hi⟩ := by
        rw [← h2]; rfl
      rw [h3]
      exact (hcP i.2).2 ⟨(x : K), hi⟩
  obtain ⟨ϕ, hϕ⟩ := zorn_le₀ P key
  have hcar : ϕ.carrier = ⊤ := by
    by_contra hne
    obtain ⟨α, -, hα⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hne)
    haveI hEnormal : Normal F ϕ.carrier := hϕ.1.1
    set E := ϕ.carrier with hE
    -- extend the embedding to the whole of `K`
    set τ₀ : K →ₐ[F] K := ϕ.emb.liftNormal K with hτ₀
    have hτ₀E : ∀ x : E, τ₀ (x : K) = ϕ.emb x := by
      intro x
      have h1 := ϕ.emb.liftNormal_commutes (E := K) x
      simpa using h1
    -- `N` is the finite normal extension of `E` generated by the conjugates of `α`
    set p := minpoly F α with hp
    have hαint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
    have hp0 : p ≠ 0 := minpoly.ne_zero hαint
    have hsplits : (p.map (algebraMap F K)).Splits := Normal.splits ‹Normal F K› α
    have hrs : (p.map (algebraMap F E)).rootSet K = p.rootSet K := by
      simp [Polynomial.rootSet, Polynomial.aroots, Polynomial.map_map,
        ← IsScalarTower.algebraMap_eq]
    set N : IntermediateField E K := adjoin E (p.rootSet K) with hN
    have hsp : ((p.map (algebraMap F E)).map (algebraMap E K)).Splits := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]; exact hsplits
    haveI hNsf : IsSplittingField E N (p.map (algebraMap F E)) := by
      have h6 := adjoin_rootSet_isSplittingField (K := E) (L := K) hsp
      rwa [hrs] at h6
    haveI hNnormal : Normal E N := Normal.of_isSplittingField (p.map (algebraMap F E))
    haveI hNfin : FiniteDimensional E N := by
      refine finiteDimensional_adjoin ?_
      intro y _
      exact (Algebra.IsIntegral.isIntegral (R := F) y).tower_top
    -- apply the finite case to the two absolute values of `N`
    set a : AbsoluteValue N ℝ := v.comp (f := (τ₀ : K →+* K).comp (algebraMap N K))
      (((τ₀ : K →+* K).comp (algebraMap N K)).injective) with ha
    set b : AbsoluteValue N ℝ := w.comp (algebraMap N K).injective with hb
    have hab : a.comp (algebraMap E N).injective = b.comp (algebraMap E N).injective := by
      ext y
      show v (τ₀ ((algebraMap E N y : N) : K)) = w ((algebraMap E N y : N) : K)
      show v (τ₀ (y : K)) = w (y : K)
      rw [hτ₀E y]
      exact hϕ.1.2 y
    obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_comp_eq_of_finiteDimensional (F := E) (K := N) hab
    have hρ' : ∀ x : N, v (τ₀ ((ρ.symm x : N) : K)) = w ((x : N) : K) := fun x => congr($hρ x)
    -- this contradicts the maximality of `ϕ`
    set ψ : Lifts F K K := ⟨N.restrictScalars F,
      (τ₀.comp ((IntermediateField.val N).restrictScalars F)).comp
        ((ρ.symm).restrictScalars F).toAlgHom⟩ with hψ
    have hcarle : E ≤ N.restrictScalars F := by
      rw [hN, IntermediateField.restrictScalars_adjoin_eq_sup]
      exact le_sup_left
    have hψP : ψ ∈ P := by
      constructor
      · show Normal F (N.restrictScalars F)
        rw [hN, IntermediateField.restrictScalars_adjoin_eq_sup]
        haveI : Normal F (adjoin F (p.rootSet K)) :=
          Normal.of_isSplittingField (E := adjoin F (p.rootSet K)) p
            (hFEp := adjoin_rootSet_isSplittingField hsplits)
        exact IntermediateField.normal_sup F K _ _
      · intro x
        exact hρ' x
    have hle : ϕ ≤ ψ := by
      refine ⟨hcarle, fun y => ?_⟩
      show τ₀ ((ρ.symm (⟨(y : K), hcarle y.2⟩ : N) : N) : K) = ϕ.emb y
      have h7 : (⟨(y : K), hcarle y.2⟩ : N) = algebraMap E N y := rfl
      rw [h7, AlgEquiv.commutes]
      show τ₀ ((y : K)) = ϕ.emb y
      exact hτ₀E y
    have hmem : α ∈ ψ.carrier := by
      show α ∈ N.restrictScalars F
      show α ∈ N
      rw [hN]
      exact subset_adjoin _ _ (mem_rootSet.2 ⟨hp0, minpoly.aeval F α⟩)
    exact hα ((hϕ.2 hψP hle).1 hmem)
  refine ⟨ϕ.emb.comp (((IntermediateField.equivOfEq hcar).trans IntermediateField.topEquiv).symm :
    K →ₐ[F] ϕ.carrier), fun x => ?_⟩
  have h1 := hϕ.1.2 (((IntermediateField.equivOfEq hcar).trans IntermediateField.topEquiv).symm x)
  simpa using h1

end Conjugate

/-- If `K / F` is a normal extension, then any two places of `K` which coincide when
restrict to `F` are conjugate by an element of `Gal(K/F)`.
See [Neukirch1992], II.9.1. -/
theorem exists_algEquiv_comp_eq_of_comp_eq
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Normal F K]
    {v w : AbsoluteValue K ℝ}
    (h : v.comp (algebraMap F K).injective = w.comp (algebraMap F K).injective) :
    ∃ σ : Gal(K/F), v.comp (f := σ) σ.injective = w := by
  obtain ⟨τ, hτ⟩ := exists_algHom_apply_eq_of_comp_eq h
  refine ⟨AlgEquiv.ofBijective τ (Algebra.IsAlgebraic.algHom_bijective τ), ?_⟩
  ext x
  exact hτ x

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
    simpa [AlgEquiv.restrictNormalHom, AbsoluteValue.under] using hτ (algebraMap K L x)
  · obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    have h : (w.comp (f := τ) τ.injective).comp (algebraMap K L).injective =
        w.comp (algebraMap K L).injective := by
      ext x
      rw [mem_decompositionSubgroup_iff_forall_apply_eq] at hσ
      simpa [AlgEquiv.restrictNormalHom, AbsoluteValue.under] using hσ x
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
