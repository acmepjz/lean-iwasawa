/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.Algebra.Module.FinrankPi
public import Iwasawalib.RingTheory.IwasawaAlgebra.KrullDim
public import Iwasawalib.RingTheory.IwasawaAlgebra.LambdaStructure
public import Iwasawalib.RingTheory.Polynomial.NuDistinguished

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# The `ℤ_p`-ranks of `X ⧸ F X` and `X[F]` are bounded independently of `F`

This file proves blueprint node `torsion-rank-bounded` in the form in which it is used in
`p:rank-growth`: for a finitely generated torsion `Λ`-module `X` there is a constant `c`,
depending only on `X`, with `rank_{ℤ_p}(X ⧸ FX) ≤ c` and `rank_{ℤ_p}(X[F]) ≤ c` for *every*
distinguished polynomial `F`.

## Main results

* `Polynomial.IsDistinguishedAt.pow`: a power of a distinguished polynomial is distinguished.
* `IwasawaAlgebra.finite_quotient_span_pow_powerSeries`: `Λ ⧸ (F ^ e)` is a finite free
  `ℤ_p`-module for `F` distinguished.
* `IwasawaAlgebra.exists_bound_of_isTorsion`: **blueprint node `torsion-rank-bounded`**.
-/

open Function Module PowerSeries
open scoped Pointwise

instance PadicInt.instInfinite (p : ℕ) [Fact p.Prime] : Infinite ℤ_[p] :=
  Infinite.of_injective (Nat.cast : ℕ → ℤ_[p]) Nat.cast_injective

namespace Polynomial.IsDistinguishedAt

variable {R : Type*} [CommRing R] {I : Ideal R} {F : R[X]}

/-- A power of a distinguished polynomial is distinguished. -/
theorem pow (hF : F.IsDistinguishedAt I) : ∀ e : ℕ, (F ^ e).IsDistinguishedAt I
  | 0 => ⟨⟨fun {i} hi ↦ by simp only [pow_zero, natDegree_one] at hi; omega⟩, by simp⟩
  | (e + 1) => by rw [pow_succ]; exact (pow hF e).mul hF

end Polynomial.IsDistinguishedAt

namespace IwasawaAlgebra

variable {p : ℕ} [Fact p.Prime]

/-- If `F` is distinguished then `Λ ⧸ (F ^ e)` is a free `ℤ_p`-module of rank `e * deg F`. -/
theorem span_pow_coe_eq {F : Polynomial ℤ_[p]} (e : ℕ) :
    (Ideal.span {(F : ℤ_[p]⟦X⟧) ^ e} : Ideal ℤ_[p]⟦X⟧) =
      Ideal.span {((F ^ e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧)} := by
  rw [Polynomial.coe_pow]

theorem finite_quotient_span_pow {F : Polynomial ℤ_[p]}
    (hF : F.IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p])) (e : ℕ) :
    Module.Finite ℤ_[p] (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {(F : ℤ_[p]⟦X⟧) ^ e} : Ideal ℤ_[p]⟦X⟧)) := by
  rw [span_pow_coe_eq]
  exact (hF.pow e).finite_quotient_powerSeries

theorem finrank_quotient_span_pow {F : Polynomial ℤ_[p]}
    (hF : F.IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p])) (e : ℕ) :
    Module.finrank ℤ_[p] (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {(F : ℤ_[p]⟦X⟧) ^ e} : Ideal ℤ_[p]⟦X⟧)) =
      e * F.natDegree := by
  have e1 : (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {(F : ℤ_[p]⟦X⟧) ^ e} : Ideal ℤ_[p]⟦X⟧)) ≃ₗ[ℤ_[p]⟦X⟧]
      (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {((F ^ e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧)} :
        Ideal ℤ_[p]⟦X⟧)) :=
    Submodule.quotEquivOfEq _ _ (congrArg
      (fun I : Ideal ℤ_[p]⟦X⟧ ↦ (I : Submodule ℤ_[p]⟦X⟧ ℤ_[p]⟦X⟧)) (span_pow_coe_eq e))
  rw [(e1.restrictScalars ℤ_[p]).finrank_eq, (hF.pow e).finrank_quotient_powerSeries,
    hF.monic.natDegree_pow]

section Vanishing

variable {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module ℤ_[p]⟦X⟧ M]
  [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M]

/-- A `ℤ_p`-module annihilated by a nonzero element of `ℤ_p` has rank zero. -/
theorem finrank_eq_zero_of_smul_eq_zero {a : ℤ_[p]} (ha : a ≠ 0) (h : ∀ x : M, a • x = 0) :
    Module.finrank ℤ_[p] M = 0 :=
  Module.IsTorsion.finrank_eq_zero fun x ↦ ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, h x⟩

set_option maxHeartbeats 1000000 in
/-- The `ℤ_p`-rank of `M ⧸ gM` is at most that of `M`. -/
theorem finrank_quotSMulTop_le (g : ℤ_[p]⟦X⟧) [Module.Finite ℤ_[p] M] :
    Module.finrank ℤ_[p] (QuotSMulTop g M) ≤ Module.finrank ℤ_[p] M := by
  refine Module.finrank_le_of_surjective (A := ℤ_[p]) (M := M) (N := QuotSMulTop g M)
    (f := (Submodule.mkQ (g • ⊤ : Submodule ℤ_[p]⟦X⟧ M)).restrictScalars ℤ_[p]) ?_
  exact Submodule.mkQ_surjective _

/-- The `ℤ_p`-rank of `M[g]` is at most that of `M`. -/
theorem finrank_torsionBy_le (g : ℤ_[p]⟦X⟧) [Module.Finite ℤ_[p] M] :
    Module.finrank ℤ_[p] (Submodule.torsionBy ℤ_[p]⟦X⟧ M g) ≤ Module.finrank ℤ_[p] M :=
  Module.finrank_le_of_injective
    (f := (Submodule.torsionBy ℤ_[p]⟦X⟧ M g).subtype.restrictScalars ℤ_[p])
    (Submodule.subtype_injective _)

theorem smul_eq_zero_quotSMulTop {a : ℤ_[p]} (h : ∀ x : M, a • x = 0) (g : ℤ_[p]⟦X⟧) :
    ∀ x : QuotSMulTop g M, a • x = 0 := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H y => rw [← Submodule.Quotient.mk_smul, h y, Submodule.Quotient.mk_zero]

theorem smul_eq_zero_torsionBy {a : ℤ_[p]} (h : ∀ x : M, a • x = 0) (g : ℤ_[p]⟦X⟧) :
    ∀ x : Submodule.torsionBy ℤ_[p]⟦X⟧ M g, a • x = 0 := by
  intro x
  exact Subtype.ext (h x.1)

end Vanishing

/-- The `ℤ_p`-module `Λ ⧸ (p ^ e)` is annihilated by `p ^ e`. -/
theorem pow_p_smul_quotient_eq_zero (e : ℕ) :
    ∀ x : (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {(p : ℤ_[p]⟦X⟧) ^ e} : Ideal ℤ_[p]⟦X⟧)),
      ((p : ℤ_[p]) ^ e) • x = 0 := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine Ideal.mem_span_singleton'.2 ⟨y, ?_⟩
    rw [Algebra.smul_def, map_pow, map_natCast]
    ring

/-- Each summand of the structure theorem contributes a bounded `ℤ_p`-rank, uniformly in the
distinguished polynomial `G`. -/
theorem exists_bound_factor (g : ℤ_[p]⟦X⟧) (e : ℕ)
    (hg : g = (p : ℤ_[p]⟦X⟧) ∨ ∃ F : Polynomial ℤ_[p],
      F.IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p]) ∧ 0 < F.natDegree ∧
        g = (F : ℤ_[p]⟦X⟧)) :
    ∃ b : ℕ, ∀ G : ℤ_[p]⟦X⟧,
      Module.finrank ℤ_[p] (QuotSMulTop G (ℤ_[p]⟦X⟧ ⧸
          (Ideal.span {g ^ e} : Ideal ℤ_[p]⟦X⟧))) ≤ b ∧
        Module.finrank ℤ_[p] (Submodule.torsionBy ℤ_[p]⟦X⟧ (ℤ_[p]⟦X⟧ ⧸
          (Ideal.span {g ^ e} : Ideal ℤ_[p]⟦X⟧)) G) ≤ b := by
  rcases hg with rfl | ⟨F, hF, -, rfl⟩
  · refine ⟨0, fun G ↦ ⟨?_, ?_⟩⟩
    · exact le_of_eq (finrank_eq_zero_of_smul_eq_zero
        (pow_ne_zero e (PadicInt.prime_p (p := p)).ne_zero)
        (smul_eq_zero_quotSMulTop (pow_p_smul_quotient_eq_zero e) G))
    · exact le_of_eq (finrank_eq_zero_of_smul_eq_zero
        (pow_ne_zero e (PadicInt.prime_p (p := p)).ne_zero)
        (smul_eq_zero_torsionBy (pow_p_smul_quotient_eq_zero e) G))
  · haveI := finite_quotient_span_pow hF e
    refine ⟨e * F.natDegree, fun G ↦ ⟨?_, ?_⟩⟩
    · rw [← finrank_quotient_span_pow hF e]
      exact finrank_quotSMulTop_le G
    · rw [← finrank_quotient_span_pow hF e]
      exact finrank_torsionBy_le G

set_option maxHeartbeats 1000000 in
/-- **Blueprint node `torsion-rank-bounded`**: for a finitely generated torsion `Λ`-module `M`
there is a constant `c`, depending only on `M`, bounding the `ℤ_p`-ranks of `M ⧸ FM` and of
`M[F]` for *every* distinguished polynomial `F`. -/
theorem exists_bound_of_isTorsion (M : Type*) [AddCommGroup M] [Module ℤ_[p] M]
    [Module ℤ_[p]⟦X⟧ M] [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]
    (hM : Module.IsTorsion ℤ_[p]⟦X⟧ M) :
    ∃ c : ℕ, ∀ F : Polynomial ℤ_[p], F.IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p]) →
      Module.finrank ℤ_[p] (QuotSMulTop (F : ℤ_[p]⟦X⟧) M) ≤ c ∧
      Module.finrank ℤ_[p] (Submodule.torsionBy ℤ_[p]⟦X⟧ M (F : ℤ_[p]⟦X⟧)) ≤ c := by
  classical
  obtain ⟨ι, hι, g, e, -, -, hgcases, hpis⟩ := exists_isPseudoIsomorphic_pi hM
  obtain ⟨φ, hφ⟩ := hpis.exists_isPseudoIsomorphism
  haveI := hφ.isPseudoNull_ker
  haveI := hφ.isPseudoNull_coker
  haveI : Finite (LinearMap.ker φ) := finite_of_isPseudoNull (p := p) (↥(LinearMap.ker φ))
  haveI : Finite (((i : ι) → ℤ_[p]⟦X⟧ ⧸ Ideal.span {g i ^ e i}) ⧸ LinearMap.range φ) :=
    finite_of_isPseudoNull (p := p) (((i : ι) → ℤ_[p]⟦X⟧ ⧸ Ideal.span {g i ^ e i}) ⧸ LinearMap.range φ)
  choose b hb using fun i ↦ exists_bound_factor (g i) (e i) (hgcases i)
  refine ⟨∑ i, b i, fun F hF ↦ ?_⟩
  haveI := hF.finite_quotient_powerSeries
  haveI : ∀ i : ι, Module.Finite ℤ_[p]
      (QuotSMulTop (F : ℤ_[p]⟦X⟧) (ℤ_[p]⟦X⟧ ⧸ Ideal.span {g i ^ e i})) := fun i ↦
    Module.Finite.quotSMulTop ℤ_[p] ℤ_[p]⟦X⟧ (F : ℤ_[p]⟦X⟧) _
  haveI : ∀ i : ι, Module.Finite ℤ_[p]
      (Submodule.torsionBy ℤ_[p]⟦X⟧ (ℤ_[p]⟦X⟧ ⧸ Ideal.span {g i ^ e i}) (F : ℤ_[p]⟦X⟧)) :=
    fun i ↦ Module.Finite.torsionBy ℤ_[p] ℤ_[p]⟦X⟧ (F : ℤ_[p]⟦X⟧) _
  constructor
  · rw [Module.finrank_quotSMulTop_eq_of_finite_ker_of_finite_coker ℤ_[p] (F : ℤ_[p]⟦X⟧) φ,
      (Module.quotSMulTopPiEquiv (F : ℤ_[p]⟦X⟧)
        (fun i ↦ ℤ_[p]⟦X⟧ ⧸ Ideal.span {g i ^ e i})).restrictScalars ℤ_[p] |>.finrank_eq,
      Module.finrank_pi_of_fintype ℤ_[p]]
    exact Finset.sum_le_sum fun i _ ↦ (hb i (F : ℤ_[p]⟦X⟧)).1
  · rw [Module.finrank_torsionBy_eq_of_finite_ker_of_finite_coker ℤ_[p] (F : ℤ_[p]⟦X⟧) φ,
      (Module.torsionByPiEquiv (F : ℤ_[p]⟦X⟧)
        (fun i ↦ ℤ_[p]⟦X⟧ ⧸ Ideal.span {g i ^ e i})).restrictScalars ℤ_[p] |>.finrank_eq,
      Module.finrank_pi_of_fintype ℤ_[p]]
    exact Finset.sum_le_sum fun i _ ↦ (hb i (F : ℤ_[p]⟦X⟧)).2

section Free

variable {L : Type*} [AddCommGroup L] [Module ℤ_[p] L] [Module ℤ_[p]⟦X⟧ L]
  [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ L] [Module.Free ℤ_[p]⟦X⟧ L] [Module.Finite ℤ_[p]⟦X⟧ L]

/-- A free `Λ`-module has no `F`-torsion for `F ≠ 0`. -/
theorem subsingleton_torsionBy_of_free {a : ℤ_[p]⟦X⟧} (ha : a ≠ 0) :
    Subsingleton (Submodule.torsionBy ℤ_[p]⟦X⟧ L a) := by
  classical
  refine ⟨fun x y ↦ Subtype.ext ?_⟩
  have key : ∀ z : L, a • z = 0 → z = 0 := by
    intro z hz
    set b := Module.Free.chooseBasis ℤ_[p]⟦X⟧ L with hb
    refine b.repr.injective (Finsupp.ext fun i ↦ ?_)
    have := congrArg (fun w ↦ b.repr w i) hz
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at this
    rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact (mul_eq_zero.1 this).resolve_left ha
  rw [key x.1 ((Submodule.mem_torsionBy_iff a x.1).1 x.2),
    key y.1 ((Submodule.mem_torsionBy_iff a y.1).1 y.2)]

theorem finrank_torsionBy_of_free {a : ℤ_[p]⟦X⟧} (ha : a ≠ 0) :
    Module.finrank ℤ_[p] (Submodule.torsionBy ℤ_[p]⟦X⟧ L a) = 0 :=
  haveI := subsingleton_torsionBy_of_free (L := L) ha
  Module.finrank_zero_of_subsingleton

set_option maxHeartbeats 1000000 in
/-- For a free `Λ`-module `L` of rank `r` and a distinguished polynomial `F` of degree `d`,
the `ℤ_p`-rank of `L ⧸ FL` is `r * d`. -/
theorem finrank_quotSMulTop_of_free {F : Polynomial ℤ_[p]}
    (hF : F.IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p])) :
    Module.finrank ℤ_[p] (QuotSMulTop (F : ℤ_[p]⟦X⟧) L) =
      Module.finrank ℤ_[p]⟦X⟧ L * F.natDegree := by
  classical
  haveI := hF.finite_quotient_powerSeries
  set b := Module.Free.chooseBasis ℤ_[p]⟦X⟧ L with hb
  have e : QuotSMulTop (F : ℤ_[p]⟦X⟧) L ≃ₗ[ℤ_[p]⟦X⟧]
      (Module.Free.ChooseBasisIndex ℤ_[p]⟦X⟧ L → ℤ_[p]⟦X⟧ ⧸ Ideal.span {(F : ℤ_[p]⟦X⟧)}) :=
    (Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul (F : ℤ_[p]⟦X⟧)
      (⊤ : Submodule ℤ_[p]⟦X⟧ L)).symm).trans (b.quotientSmulTopEquivPi _)
  rw [(e.restrictScalars ℤ_[p]).finrank_eq, Module.finrank_pi_of_fintype ℤ_[p],
    Finset.sum_const, Finset.card_univ, smul_eq_mul,
    hF.finrank_quotient_powerSeries, Module.finrank_eq_card_chooseBasisIndex]

end Free

set_option maxHeartbeats 1000000 in
/-- **Blueprint node `p:rank-growth`**, in the sharp form valid for every distinguished
polynomial: for a finitely generated `Λ`-module `M` of `Λ`-rank `r` there is a constant `c`
with `|rank_{ℤ_p}(M ⧸ FM) - r * deg F| ≤ c` for every distinguished `F`. Applied to
`F = ω_n = (1 + X) ^ (p ^ n) - 1`, whose degree is `p ^ n`, this is
`rank_{ℤ_p}(M ⧸ ω_n M) = r p^n + O(1)`. -/
theorem exists_bound_finrank_quotSMulTop (M : Type*) [AddCommGroup M] [Module ℤ_[p] M]
    [Module ℤ_[p]⟦X⟧ M] [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M] :
    ∃ c : ℕ, ∀ F : Polynomial ℤ_[p], F.IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p]) →
      ((Module.finrank ℤ_[p] (QuotSMulTop (F : ℤ_[p]⟦X⟧) M) : ℤ) -
        (Module.finrank ℤ_[p]⟦X⟧ M : ℤ) * F.natDegree).natAbs ≤ c := by
  classical
  obtain ⟨L, hLfree, hLfin, hLrank, hQtor⟩ :=
    Module.exists_free_submodule_isTorsion_quotient ℤ_[p]⟦X⟧ M
  haveI := hLfree
  haveI := hLfin
  obtain ⟨c, hc⟩ := exists_bound_of_isTorsion (M ⧸ L) hQtor
  refine ⟨c, fun F hF ↦ ?_⟩
  haveI := hF.finite_quotient_powerSeries
  haveI : Module.Finite ℤ_[p]⟦X⟧ (M ⧸ L) := Module.Finite.quotient _ _
  haveI := Module.Finite.torsionBy ℤ_[p] ℤ_[p]⟦X⟧ (F : ℤ_[p]⟦X⟧) M
  haveI := Module.Finite.quotSMulTop ℤ_[p] ℤ_[p]⟦X⟧ (F : ℤ_[p]⟦X⟧) M
  haveI := Module.Finite.torsionBy ℤ_[p] ℤ_[p]⟦X⟧ (F : ℤ_[p]⟦X⟧) ↥L
  haveI := Module.Finite.quotSMulTop ℤ_[p] ℤ_[p]⟦X⟧ (F : ℤ_[p]⟦X⟧) ↥L
  haveI := Module.Finite.torsionBy ℤ_[p] ℤ_[p]⟦X⟧ (F : ℤ_[p]⟦X⟧) (M ⧸ L)
  haveI := Module.Finite.quotSMulTop ℤ_[p] ℤ_[p]⟦X⟧ (F : ℤ_[p]⟦X⟧) (M ⧸ L)
  obtain ⟨r₂, r₃, r₄, h2, h3, h4, h5⟩ := Module.finrank_snake (A := ℤ_[p])
    (g := (F : ℤ_[p]⟦X⟧)) L.subtype L.mkQ (LinearMap.exact_subtype_mkQ L)
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
  have hFne : ((F : ℤ_[p]⟦X⟧)) ≠ 0 := fun h ↦ hF.monic.ne_zero
    (Polynomial.coe_injective (R := ℤ_[p]) (h.trans Polynomial.coe_zero.symm))
  rw [finrank_torsionBy_of_free (L := ↥L) hFne] at h2
  rw [finrank_quotSMulTop_of_free (L := ↥L) hF, hLrank] at h4
  obtain ⟨h6, h7⟩ := hc F hF
  omega

set_option maxHeartbeats 1000000 in
/-- **Blueprint node `finite-quotient-implies-torsion`**, in the form in which it is used: if
`M ⧸ F_n M` is finite for a family of distinguished polynomials `F_n` of unbounded degree, then
`M` is a torsion `Λ`-module. -/
theorem isTorsion_of_finite_quotSMulTop (M : Type*) [AddCommGroup M] [Module ℤ_[p] M]
    [Module ℤ_[p]⟦X⟧ M] [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]
    {ι : Type*} (F : ι → Polynomial ℤ_[p])
    (hF : ∀ i, (F i).IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p]))
    (hdeg : ∀ c : ℕ, ∃ i, c < (F i).natDegree)
    (hfin : ∀ i, Finite (QuotSMulTop ((F i : ℤ_[p]⟦X⟧)) M)) :
    Module.IsTorsion ℤ_[p]⟦X⟧ M := by
  obtain ⟨c, hc⟩ := exists_bound_finrank_quotSMulTop (p := p) M
  have hrank : Module.finrank ℤ_[p]⟦X⟧ M = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ := hdeg c
    haveI := hfin i
    have h0 : Module.finrank ℤ_[p] (QuotSMulTop ((F i : ℤ_[p]⟦X⟧)) M) = 0 :=
      Module.finrank_eq_zero_of_finite ℤ_[p] _
    have h1 := hc (F i) (hF i)
    rw [h0, Nat.cast_zero, zero_sub, Int.natAbs_neg, ← Nat.cast_mul,
      Int.natAbs_natCast] at h1
    have h4 : (F i).natDegree ≤ Module.finrank ℤ_[p]⟦X⟧ M * (F i).natDegree :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
    omega
  obtain ⟨L, hLfree, hLfin, hLrank, hQtor⟩ :=
    Module.exists_free_submodule_isTorsion_quotient ℤ_[p]⟦X⟧ M
  haveI := hLfree
  haveI := hLfin
  haveI : Subsingleton ↥L := Module.finrank_zero_iff.1 (by rw [hLrank, hrank])
  have hLbot : L = ⊥ := by
    refine (Submodule.eq_bot_iff L).2 fun x hx ↦ ?_
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : L) 0)
  subst hLbot
  exact (Submodule.quotEquivOfEqBot (⊥ : Submodule ℤ_[p]⟦X⟧ M) rfl).isTorsion.1 hQtor

/-- `ω_n = (1 + X) ^ (p ^ n) - 1` is distinguished at the maximal ideal of `ℤ_p`. -/
theorem isDistinguishedAt_omega (n : ℕ) :
    (Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n)).IsDistinguishedAt
      (IsLocalRing.maximalIdeal ℤ_[p]) := by
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact Polynomial.isDistinguishedAt_oneAddXPowSubOne ℤ_[p] p n

/-- **Blueprint node `p:rank-growth`**: `rank_{ℤ_p}(M ⧸ ω_n M) = r p^n + O(1)`, where
`r = rank_Λ M` and `ω_n = (1 + X) ^ (p ^ n) - 1`. -/
theorem exists_bound_finrank_quotSMulTop_omega (M : Type*) [AddCommGroup M] [Module ℤ_[p] M]
    [Module ℤ_[p]⟦X⟧ M] [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M] :
    ∃ c : ℕ, ∀ n : ℕ,
      ((Module.finrank ℤ_[p] (QuotSMulTop
          ((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) M) : ℤ) -
        (Module.finrank ℤ_[p]⟦X⟧ M : ℤ) * (p : ℤ) ^ n).natAbs ≤ c := by
  obtain ⟨c, hc⟩ := exists_bound_finrank_quotSMulTop (p := p) M
  refine ⟨c, fun n ↦ ?_⟩
  have h := hc _ (isDistinguishedAt_omega (p := p) n)
  rwa [Polynomial.natDegree_oneAddXPowSubOne, Nat.cast_pow] at h

/-- **Blueprint node `finite-quotient-implies-torsion`** for the sequence `ω_n`: if
`M ⧸ ω_n M` is finite for all sufficiently large `n`, then `M` is a torsion `Λ`-module. -/
theorem isTorsion_of_finite_quotSMulTop_omega (M : Type*) [AddCommGroup M] [Module ℤ_[p] M]
    [Module ℤ_[p]⟦X⟧ M] [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M] (N : ℕ)
    (hfin : ∀ n, N ≤ n → Finite (QuotSMulTop
      ((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) M)) :
    Module.IsTorsion ℤ_[p]⟦X⟧ M := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  refine isTorsion_of_finite_quotSMulTop M (ι := {n : ℕ // N ≤ n})
    (fun i ↦ Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ (i : ℕ)))
    (fun i ↦ isDistinguishedAt_omega (i : ℕ)) (fun c ↦ ?_) (fun i ↦ hfin i i.2)
  refine ⟨⟨max N (c + 1), le_max_left _ _⟩, ?_⟩
  rw [Polynomial.natDegree_oneAddXPowSubOne]
  calc c < max N (c + 1) := lt_of_lt_of_le (Nat.lt_succ_self c) (le_max_right _ _)
    _ < p ^ max N (c + 1) := Nat.lt_pow_self hp1

end IwasawaAlgebra
