/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.NumberTheory.Padics.ForMathlib1
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Ring.Compact

@[expose] public section

/-!

# Some convenient results on neighborhood basis of `ℤₚ` around `0`

-/

variable (ι : Type*) [Finite ι] (p : ℕ) [Fact p.Prime] (n : ℕ)

/-! ## Open ideal of `ℤₚ` -/

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] [IsDedekindDomain R]

theorem isOpen_span_singleton_of_ne_zero {x : R} (hx : x ≠ 0) :
    IsOpen (Ideal.span {x} : Set R) := by
  apply isOpen_of_ne_bot
  simp [hx]

theorem isOpen_span_singleton_pow_of_irreducible
    {p : R} (hp : Irreducible p) (n : ℕ) : IsOpen (Ideal.span {p ^ n} : Set R) := by
  apply isOpen_span_singleton_of_ne_zero
  simp [hp.ne_zero]

/-- If `x ≠ 0`, then `R ≃ ⟨x⟩`, `a ↦ x * a` is an isomorphism of topological module. -/
noncomputable def continuousLinearEquivOfNeZero {x : R} (hx : x ≠ 0) : R ≃L[R] Ideal.span {x} :=
  letI f1 : R ≃ₗ[R] LinearMap.range (LinearMap.mul R R x) := .ofInjective (.mul R R x) <| by
    simp [injective_iff_map_eq_zero, hx]
  haveI hc : Continuous f1 := continuous_mul.curry_right.rangeFactorization
  letI f2 : R ≃ₜ LinearMap.range (LinearMap.mul R R x) := hc.homeoOfEquivCompactToT2 (f := f1)
  letI f3 : R ≃L[R] LinearMap.range (LinearMap.mul R R x) := { f1, f2 with }
  f3.trans <| .ofEq _ _ (Ideal.range_mul' x)

@[simp]
theorem coe_continuousLinearEquivOfNeZero_apply {x : R} (hx : x ≠ 0) (a : R) :
    continuousLinearEquivOfNeZero hx a = x * a := rfl

theorem nonempty_continuousLinearEquiv_of_ne_bot
    [IsPrincipalIdealRing R] {I : Ideal R} (hI : I ≠ ⊥) : Nonempty (I ≃L[R] R) := by
  obtain ⟨x, h⟩ := IsPrincipalIdealRing.principal I
  rw [Ideal.submodule_span_eq] at h
  refine ⟨((continuousLinearEquivOfNeZero ?_).trans <| .ofEq _ _ h.symm).symm⟩
  rintro rfl
  simp_all

end IsDedekindDomain

theorem PadicInt.isOpen_span_p_pow : IsOpen (Ideal.span {(p ^ n : ℤ_[p])} : Set ℤ_[p]) :=
  IsDedekindDomain.isOpen_span_singleton_pow_of_irreducible PadicInt.irreducible_p n

theorem PadicInt.isOpen_pi_span_p_pow :
    IsOpen (Ideal.pi fun _ : ι ↦ Ideal.span {(p ^ n : ℤ_[p])} : Set (ι → ℤ_[p])) := by
  convert isOpen_set_pi (ι := ι) Set.finite_univ (fun _ _ ↦ isOpen_span_p_pow p n)
  ext
  simp [-Ideal.pi_span, Ideal.mem_pi]

/-! ## Index of ideals of `ℤₚ` -/

theorem PadicInt.index_span_p_pow :
    (Ideal.span {(p ^ n : ℤ_[p])}).toAddSubgroup.index = p ^ n := by
  rw [AddSubgroup.index_eq_card]
  change Nat.card (ℤ_[p] ⧸ Ideal.span {(p ^ n : ℤ_[p])}) = _
  convert Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (toZModPow_surjective p n)).toEquiv <;> simp [ker_toZModPow]

theorem PadicInt.index_pi_span_p_pow :
    (Ideal.pi fun _ : ι ↦ Ideal.span {(p ^ n : ℤ_[p])}).toAddSubgroup.index =
      p ^ (n * Nat.card ι) := by
  have h2 : (AddSubgroup.pi (Set.univ : Set ι)
      fun _ ↦ (Ideal.span {(p ^ n : ℤ_[p])}).toAddSubgroup).index = p ^ (n * Nat.card ι) := by
    let _ := Fintype.ofFinite ι
    simp [index_span_p_pow p n, pow_mul]
  convert h2
  ext
  simp [-Ideal.pi_span, Ideal.mem_pi, AddSubgroup.mem_pi]

/-! ## Neighborhood basis of `ℤₚ` around `0` -/

theorem PadicInt.nhds_zero_hasAntitoneBasis_span_p_pow :
    (nhds (0 : ℤ_[p])).HasAntitoneBasis (fun n : ℕ ↦ Ideal.span {(p ^ n : ℤ_[p])}) where
  toHasBasis := by
    have hp : p.Prime := Fact.out
    have hp2 := hp.two_le
    let r : ℝ := 1 / p
    have hr0 : 0 < r := by positivity
    have hr1 : r < 1 := by
      simp_rw [r, one_div]
      apply inv_lt_one_of_one_lt₀
      norm_cast
    have h1 := Metric.nhds_basis_ball_pow (x := (0 : ℤ_[p])) hr0 hr1
    replace h1 : (nhds (0 : ℤ_[p])).HasBasis (fun (_ : ℕ) ↦ True)
        fun n ↦ Metric.ball 0 (r ^ (n - 1 : ℤ)) := by
      refine ⟨fun s ↦ ?_⟩
      rw [h1.mem_iff]
      refine ⟨fun ⟨i, _, h⟩ ↦ ⟨i + 1, trivial, by simpa⟩,
        fun ⟨i, _, h⟩ ↦ ⟨i, trivial, (Metric.ball_subset_ball ?_).trans h⟩⟩
      rw [← zpow_natCast]
      apply zpow_le_zpow_right_of_le_one₀ hr0 hr1.le
      simp
    convert h1 with n
    ext
    simp_rw [SetLike.mem_coe,
      ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_le_pow_iff_norm_lt_pow_add_one,
      Metric.mem_ball, dist_zero_right, r, one_div, inv_zpow, ← zpow_neg]
    congr! 2
    ring
  antitone := antitone_nat_of_succ_le fun n ↦ Ideal.span_singleton_le_span_singleton.2 <| by
    simp [pow_succ]

theorem PadicInt.nhds_zero_hasAntitoneBasis_pi_span_p_pow :
    (nhds (0 : ι → ℤ_[p])).HasAntitoneBasis
      (fun n : ℕ ↦ Ideal.pi fun _ : ι ↦ Ideal.span {(p ^ n : ℤ_[p])}) where
  toHasBasis := by
    let _ := Fintype.ofFinite ι
    have hp : p.Prime := Fact.out
    have hp2 := hp.two_le
    let r : ℝ := 1 / p
    have hr0 : 0 < r := by positivity
    have hr1 : r < 1 := by
      simp_rw [r, one_div]
      apply inv_lt_one_of_one_lt₀
      norm_cast
    have h1 := Metric.nhds_basis_ball_pow (x := (0 : ι → ℤ_[p])) hr0 hr1
    replace h1 : (nhds (0 : ι → ℤ_[p])).HasBasis (fun (_ : ℕ) ↦ True)
        fun n ↦ Metric.ball 0 (r ^ (n - 1 : ℤ)) := by
      refine ⟨fun s ↦ ?_⟩
      rw [h1.mem_iff]
      refine ⟨fun ⟨i, _, h⟩ ↦ ⟨i + 1, trivial, by simpa⟩,
        fun ⟨i, _, h⟩ ↦ ⟨i, trivial, (Metric.ball_subset_ball ?_).trans h⟩⟩
      rw [← zpow_natCast]
      apply zpow_le_zpow_right_of_le_one₀ hr0 hr1.le
      simp
    convert h1 with n
    rw [ball_pi _ (zpow_pos hr0 _)]
    ext
    simp_rw [SetLike.mem_coe, Ideal.mem_pi, Pi.zero_apply, Set.mem_pi, Set.mem_univ, forall_const]
    congr! 1
    simp_rw [← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_le_pow_iff_norm_lt_pow_add_one,
      Metric.mem_ball, dist_zero_right, r, one_div, inv_zpow, ← zpow_neg]
    congr! 2
    ring
  antitone := antitone_nat_of_succ_le fun n x ↦ by
    simp only [SetLike.mem_coe, Ideal.mem_pi]
    have hle : Ideal.span {(p ^ (n + 1) : ℤ_[p])} ≤ Ideal.span {(p ^ n : ℤ_[p])} :=
      Ideal.span_singleton_le_span_singleton.2 (by simp [pow_succ])
    exact fun h i ↦ hle (h i)

/-! ## Open and closed subgroups of `ℤₚ` -/

theorem PadicInt.denseRange_of_not_dvd (a b : ℕ) (hb : ¬p ∣ b) :
    DenseRange fun x : ℕ ↦ (a + b * x : ℤ_[p]) := by
  intro x
  suffices ∀ n : ℕ, ∃ k : ℕ, x - (a + b * k) ∈ Ideal.span {(p ^ n : ℤ_[p])} by
    simp_rw [Metric.mem_closure_range_iff, dist_eq_norm]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_neg_lt p hε
    obtain ⟨k, hk⟩ := this n
    use k
    apply lt_of_le_of_lt _ hn
    rwa [norm_le_pow_iff_mem_span_pow]
  intro n
  simp_rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_add, map_mul, map_natCast]
  replace hb : IsUnit (b : ZMod (p ^ n)) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rwa [Nat.coprime_comm, ‹Fact p.Prime›.out.coprime_iff_not_dvd]
  use hb.unit.inv.val * (toZModPow n x - a).val
  simp [← mul_assoc]

theorem PadicInt.smul_mem_of_isClosed (G : AddSubsemigroup ℤ_[p])
    (hG : IsClosed (G : Set ℤ_[p])) (c : ℤ_[p]) {x : ℤ_[p]} (hx : x ∈ G) : c • x ∈ G := by
  have hcont : Continuous fun a : ℤ_[p] ↦ a • x := by fun_prop
  let s := Set.range fun x : ℕ ↦ (1 + x : ℤ_[p])
  have hs : Dense s := by
    simpa using PadicInt.denseRange_of_not_dvd p 1 1 ‹Fact p.Prime›.out.not_dvd_one
  have hm : s.MapsTo (fun a : ℤ_[p] ↦ a • x) G := fun a ha ↦ by
    obtain ⟨b, rfl⟩ := ha
    dsimp only [smul_eq_mul]
    induction b with
    | zero => simp [hx]
    | succ b ih =>
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc, add_mul, one_mul]
      exact add_mem ih hx
  simpa [hG.closure_eq] using map_mem_closure hcont (hs c) hm

theorem PadicInt.exists_eq_ideal_of_addSubsemigroup_of_isClosed (G : AddSubsemigroup ℤ_[p])
    (hne : Set.Nonempty (G : Set ℤ_[p])) (hG : IsClosed (G : Set ℤ_[p])) :
    ∃ (I : Ideal ℤ_[p]), G = I.toAddSubsemigroup := by
  let I : Ideal ℤ_[p] := {
    __ := G
    zero_mem' := by simpa using smul_mem_of_isClosed p G hG 0 hne.some_mem
    smul_mem' c x hx := smul_mem_of_isClosed p G hG c hx
  }
  exact ⟨I, rfl⟩

theorem PadicInt.exists_eq_ideal_of_addSubmonoid_of_isClosed (G : AddSubmonoid ℤ_[p])
    (hG : IsClosed (G : Set ℤ_[p])) : ∃ (I : Ideal ℤ_[p]), G = I.toAddSubmonoid := by
  let I : Ideal ℤ_[p] := {
    __ := G
    smul_mem' c x hx := smul_mem_of_isClosed p G.toAddSubsemigroup hG c hx
  }
  exact ⟨I, rfl⟩

theorem PadicInt.exists_eq_ideal_of_addSubgroup_of_isClosed (G : AddSubgroup ℤ_[p])
    (hG : IsClosed (G : Set ℤ_[p])) : ∃ (I : Ideal ℤ_[p]), G = I.toAddSubgroup := by
  let I : Ideal ℤ_[p] := {
    __ := G
    smul_mem' c x hx := smul_mem_of_isClosed p G.toAddSubsemigroup hG c hx
  }
  exact ⟨I, rfl⟩

theorem PadicInt.exists_eq_span_p_pow_of_isOpen (G : AddSubgroup ℤ_[p])
    (hG : IsOpen (G : Set ℤ_[p])) :
    ∃ (n : ℕ), G = (Ideal.span {(p ^ n : ℤ_[p])}).toAddSubgroup := by
  obtain ⟨I, rfl⟩ := PadicInt.exists_eq_ideal_of_addSubgroup_of_isClosed p G
    (G.isClosed_of_isOpen hG)
  change IsOpen (I : Set ℤ_[p]) at hG
  rw [IsDiscreteValuationRing.isOpen_iff] at hG
  obtain ⟨n, rfl⟩ := PadicInt.ideal_eq_span_pow_p hG
  exact ⟨n, rfl⟩
