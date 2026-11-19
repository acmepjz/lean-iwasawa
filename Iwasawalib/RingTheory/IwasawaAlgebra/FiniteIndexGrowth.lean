/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.CoinvariantGrowth
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# Blueprint node `finite-index-submodule-growth`
-/

open Function Module PowerSeries
open scoped Pointwise

section SubmoduleCard

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem Submodule.smul_le_self' (a : R) (Y : Submodule R M) : a • Y ≤ Y := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists x a Y).1 hx
  rw [← hyx]
  exact Y.smul_mem a hy

theorem Submodule.smul_mono_right' (a : R) {Y Z : Submodule R M} (h : Y ≤ Z) : a • Y ≤ a • Z := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists x a Y).1 hx
  exact (Submodule.mem_smul_pointwise_iff_exists x a Z).2 ⟨y, h hy, hyx⟩

theorem Module.finite_quotient_of_le {S T : Submodule R M} (h : S ≤ T) [Finite (M ⧸ S)] :
    Finite (M ⧸ T) := by
  refine _root_.Finite.of_surjective (Submodule.mapQ S T LinearMap.id h) fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective T x
  exact ⟨Submodule.Quotient.mk y, rfl⟩

theorem Submodule.comap_subtype_smul (a : R) (Y : Submodule R M) :
    (a • Y).comap Y.subtype = a • (⊤ : Submodule R Y) := by
  ext x
  simp only [Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists (x : M) a Y).1 hx
    exact (Submodule.mem_smul_pointwise_iff_exists x a ⊤).2 ⟨⟨y, hy⟩, trivial, Subtype.ext hyx⟩
  · intro hx
    obtain ⟨y, -, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists x a ⊤).1 hx
    exact (Submodule.mem_smul_pointwise_iff_exists (x : M) a Y).2
      ⟨(y : M), y.2, congrArg Subtype.val hyx⟩

theorem Submodule.card_map_mkQ (S T : Submodule R M) :
    Nat.card (T.map S.mkQ) = Nat.card (T ⧸ S.comap T.subtype) := by
  have hmem : ∀ x : T, S.mkQ (x : M) ∈ T.map S.mkQ := fun x ↦ Submodule.mem_map_of_mem x.2
  set f : T →ₗ[R] ↥(T.map S.mkQ) :=
    (S.mkQ.comp T.subtype).codRestrict (T.map S.mkQ) hmem with hf
  have hsurj : Function.Surjective f := by
    rintro ⟨z, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker : LinearMap.ker f = S.comap T.subtype := by
    ext x
    simp only [hf, LinearMap.mem_ker, LinearMap.codRestrict_apply, Subtype.ext_iff,
      ZeroMemClass.coe_zero, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rw [← hker]
  exact (Nat.card_congr (f.quotKerEquivOfSurjective hsurj).toEquiv).symm

/-- `#(M ⧸ aY) = #(M ⧸ Y) * #(Y ⧸ aY)`. -/
theorem Submodule.card_quotient_smul (a : R) (Y : Submodule R M) :
    Nat.card (M ⧸ (a • Y)) = Nat.card (M ⧸ Y) * Nat.card (QuotSMulTop a Y) := by
  rw [Module.card_eq_card_quotient_mul_card (Y.map (a • Y).mkQ),
    Nat.card_congr (Submodule.quotientQuotientEquivQuotient (a • Y) Y
      (Submodule.smul_le_self' a Y)).toEquiv,
    Submodule.card_map_mkQ, Submodule.comap_subtype_smul]

end SubmoduleCard

namespace IwasawaAlgebra

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Blueprint node `pseudo-null-char-ideal` (ii)** applied to a finite-index submodule: a
finite-index `Λ`-submodule has the same `μ` and `λ` as the ambient module. -/
theorem muMod_and_lambdaMod_submodule_eq {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M]
    [Module.Finite ℤ_[p]⟦X⟧ M] (hM : Module.IsTorsion ℤ_[p]⟦X⟧ M)
    (Y : Submodule ℤ_[p]⟦X⟧ M) [Finite (M ⧸ Y)] :
    muMod p Y = muMod p M ∧ lambdaMod p Y = lambdaMod p M := by
  haveI : Subsingleton (LinearMap.ker Y.subtype) := by
    rw [LinearMap.ker_eq_bot.2 (Submodule.subtype_injective Y)]
    infer_instance
  haveI : Module.IsPseudoNull ℤ_[p]⟦X⟧ (M ⧸ LinearMap.range Y.subtype) := by
    rw [Submodule.range_subtype Y]
    exact (isPseudoNull_iff_finite p (M ⧸ Y)).2 inferInstance
  have hpi : (Y.subtype).IsPseudoIsomorphism := ⟨inferInstance, inferInstance⟩
  obtain ⟨a, ha0, ha⟩ := exists_charIdeal_eq_span hM
  exact ⟨(muMod_eq ha0 (hpi.charIdeal_eq.trans ha)).trans (muMod_eq ha0 ha).symm,
    (lambdaMod_eq ha0 (hpi.charIdeal_eq.trans ha)).trans (lambdaMod_eq ha0 ha).symm⟩

/-- **Blueprint node `finite-index-submodule-growth`**: let `X` be a finitely generated
`Λ`-module, `Y ⊆ X` a submodule of finite index, and `e ≥ 0`. If `X ⧸ ν_{n,e} Y` is finite for
all sufficiently large `n`, then `X` and `Y` are finitely generated torsion `Λ`-modules with
`μ(Y) = μ(X)` and `λ(Y) = λ(X)`, and
`ord_p #(X ⧸ ν_{n,e} Y) = μ(X) p ^ n + λ(X) n + ν` for all sufficiently large `n`. -/
theorem exists_factorization_card_quotient_smul_submodule
    {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module ℤ_[p]⟦X⟧ M]
    [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]
    (Y : Submodule ℤ_[p]⟦X⟧ M) [Finite (M ⧸ Y)] (e n₀ : ℕ) (he : e ≤ n₀)
    (hfin : ∀ n, n₀ ≤ n → Finite (M ⧸
      (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y))) :
    Module.IsTorsion ℤ_[p]⟦X⟧ M ∧ Module.IsTorsion ℤ_[p]⟦X⟧ Y ∧
      muMod p Y = muMod p M ∧ lambdaMod p Y = lambdaMod p M ∧
      ∃ (ν : ℤ) (N : ℕ), ∀ n, N ≤ n →
        (((Nat.card (M ⧸ (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) :
            ℤ_[p]⟦X⟧) • Y))).factorization p : ℕ) : ℤ) =
          (muMod p M : ℤ) * (p : ℤ) ^ n + (lambdaMod p M : ℤ) * n + ν := by
  have hcard : ∀ n : ℕ,
      Nat.card (M ⧸ (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y)) =
        Nat.card (M ⧸ Y) *
          Nat.card (QuotSMulTop ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) Y) :=
    fun n ↦ Submodule.card_quotient_smul _ Y
  have hfinY : ∀ n, n₀ ≤ n →
      Finite (QuotSMulTop ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) Y) := by
    intro n hn
    haveI := hfin n hn
    have h1 : Nat.card (M ⧸ (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y))
        ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
    rw [hcard n] at h1
    exact (Nat.card_ne_zero.1 (right_ne_zero_of_mul h1)).2
  have hfinM : ∀ n, n₀ ≤ n →
      Finite (QuotSMulTop ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) M) := by
    intro n hn
    haveI := hfin n hn
    exact Module.finite_quotient_of_le
      (Submodule.smul_mono_right' ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧)
        (le_top : Y ≤ ⊤))
  obtain ⟨htorM, -⟩ := exists_factorization_card_quotSMulTop_nu (M := M) e n₀ he hfinM
  obtain ⟨htorY, ν₀, N₀, hν₀⟩ := exists_factorization_card_quotSMulTop_nu (M := Y) e n₀ he hfinY
  obtain ⟨hmu, hlam⟩ := muMod_and_lambdaMod_submodule_eq htorM Y
  refine ⟨htorM, htorY, hmu, hlam, ⟨ν₀ + ((Nat.card (M ⧸ Y)).factorization p : ℤ), max n₀ N₀,
    fun n hn ↦ ?_⟩⟩
  have hn0 : n₀ ≤ n := le_of_max_le_left hn
  have hYne : Nat.card (M ⧸ Y) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  have hQne : Nat.card (QuotSMulTop
      ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) Y) ≠ 0 := by
    haveI := hfinY n hn0
    exact Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  rw [hcard n, Nat.factorization_mul hYne hQne]
  simp only [Finsupp.add_apply, Nat.cast_add]
  rw [hν₀ n (le_of_max_le_right hn), hmu, hlam]
  ring


/-- `finite-index-submodule-growth` in the `multiplicity` form used downstream: this is the
shape in which Iwasawa's class number formula consumes the `Λ`-module input, once
`X_n ≅ X_∞ ⧸ ν_{n,e} Y` is available. -/
theorem exists_multiplicity_card_quotient_smul_submodule
    {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module ℤ_[p]⟦X⟧ M]
    [IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]
    (Y : Submodule ℤ_[p]⟦X⟧ M) [Finite (M ⧸ Y)] (e n₀ : ℕ) (he : e ≤ n₀)
    (hfin : ∀ n, n₀ ≤ n → Finite (M ⧸
      (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y))) :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n, N < n →
      (multiplicity p (Nat.card (M ⧸
        (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y))) : ℤ)
        = (mu : ℤ) * (p : ℤ) ^ n + (lambda : ℤ) * n + nu := by
  obtain ⟨-, -, -, -, ν, N, hN⟩ :=
    exists_factorization_card_quotient_smul_submodule Y e n₀ he hfin
  refine ⟨muMod p M, lambdaMod p M, ν, max n₀ N, fun n hn ↦ ?_⟩
  haveI := hfin n (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn))
  rw [Nat.multiplicity_eq_factorization hp.out]
  exact hN n (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn))


/-- **Blueprint node `finite-index-submodule-growth`** for a module already known to be
`Λ`-torsion — the form in which Step 3 of the proof of Iwasawa's class number theorem uses it
(Step 2 there, i.e. blueprint node `Xn-isom-qout`, already supplies the torsion statement).
Unlike `IwasawaAlgebra.exists_factorization_card_quotient_smul_submodule` this needs no
`ℤ_p`-module structure on `M`. -/
theorem exists_factorization_card_quotient_smul_submodule_of_isTorsion
    {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]
    (hM : Module.IsTorsion ℤ_[p]⟦X⟧ M)
    (Y : Submodule ℤ_[p]⟦X⟧ M) [Finite (M ⧸ Y)] (e n₀ : ℕ) (he : e ≤ n₀)
    (hfin : ∀ n, n₀ ≤ n → Finite (M ⧸
      (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y))) :
    muMod p Y = muMod p M ∧ lambdaMod p Y = lambdaMod p M ∧
      ∃ (ν : ℤ) (N : ℕ), ∀ n, N ≤ n →
        (((Nat.card (M ⧸ (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) :
            ℤ_[p]⟦X⟧) • Y))).factorization p : ℕ) : ℤ) =
          (muMod p M : ℤ) * (p : ℤ) ^ n + (lambdaMod p M : ℤ) * n + ν := by
  have hcard : ∀ n : ℕ,
      Nat.card (M ⧸ (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y)) =
        Nat.card (M ⧸ Y) *
          Nat.card (QuotSMulTop ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) Y) :=
    fun n ↦ Submodule.card_quotient_smul _ Y
  have hfinY : ∀ n, n₀ ≤ n →
      Finite (QuotSMulTop ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) Y) := by
    intro n hn
    haveI := hfin n hn
    have h1 : Nat.card (M ⧸ (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y))
        ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
    rw [hcard n] at h1
    exact (Nat.card_ne_zero.1 (right_ne_zero_of_mul h1)).2
  have htorY : Module.IsTorsion ℤ_[p]⟦X⟧ Y := by
    intro x
    obtain ⟨a, ha⟩ := @hM (x : M)
    exact ⟨a, Subtype.ext ha⟩
  obtain ⟨ν₀, N₀, hν₀⟩ :=
    exists_factorization_card_quotSMulTop_nu_of_isTorsion htorY e n₀ he hfinY
  obtain ⟨hmu, hlam⟩ := muMod_and_lambdaMod_submodule_eq hM Y
  refine ⟨hmu, hlam, ⟨ν₀ + ((Nat.card (M ⧸ Y)).factorization p : ℤ), max n₀ N₀, fun n hn ↦ ?_⟩⟩
  have hn0 : n₀ ≤ n := le_of_max_le_left hn
  have hYne : Nat.card (M ⧸ Y) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  have hQne : Nat.card (QuotSMulTop
      ((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) Y) ≠ 0 := by
    haveI := hfinY n hn0
    exact Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  rw [hcard n, Nat.factorization_mul hYne hQne]
  simp only [Finsupp.add_apply, Nat.cast_add]
  rw [hν₀ n (le_of_max_le_right hn), hmu, hlam]
  ring


/-- The downstream interface of `finite-index-submodule-growth`: for a finitely generated
torsion `Λ`-module `X` with a finite-index submodule `Y` such that `X ⧸ ν_{n,e} Y` is finite,
there are `μ, λ ∈ ℕ` and `ν ∈ ℤ` with
`ord_p #(X ⧸ ν_{n,e} Y) = μ p ^ n + λ n + ν` for all `n > N`. -/
theorem exists_multiplicity_card_quotient_smul_submodule_of_isTorsion
    {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]
    (hM : Module.IsTorsion ℤ_[p]⟦X⟧ M)
    (Y : Submodule ℤ_[p]⟦X⟧ M) [Finite (M ⧸ Y)] (e n₀ : ℕ) (he : e ≤ n₀)
    (hfin : ∀ n, n₀ ≤ n → Finite (M ⧸
      (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y))) :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n, N < n →
      (multiplicity p (Nat.card (M ⧸
        (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y))) : ℤ)
        = (mu : ℤ) * (p : ℤ) ^ n + (lambda : ℤ) * n + nu := by
  obtain ⟨-, -, ν, N, hN⟩ :=
    exists_factorization_card_quotient_smul_submodule_of_isTorsion hM Y e n₀ he hfin
  refine ⟨muMod p M, lambdaMod p M, ν, max n₀ N, fun n hn ↦ ?_⟩
  haveI := hfin n (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn))
  rw [Nat.multiplicity_eq_factorization hp.out]
  exact hN n (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn))

end IwasawaAlgebra
