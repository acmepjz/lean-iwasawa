/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.NumberTheory.AbsoluteValue.DecompositionSubgroup
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

/-!

# Lifting of residue automorphisms

Let `L` be a field with a nonarchimedean absolute value `w`, and let `L / K / F` be a tower of
fields with `L / F` and `K / F` normal. The main result of this file,
`AbsoluteValue.exists_algHom_residue`, states that an `F`-embedding `K → L` which preserves `w`
and is trivial modulo the maximal ideal extends to an `F`-algebra homomorphism of `L` with the
same two properties. Equivalently, the map `D_w(L/K) → Gal(k_w / k_v)` of decomposition groups
to residue field automorphisms hits every automorphism induced by an element of `D_w(L/F)`.

The proof follows the classical route: the finite Galois case
(`AbsoluteValue.exists_algEquiv_residue_of_isGalois`) is deduced from
`Ideal.Quotient.stabilizerHom_surjective` applied to the ring of `Gal(N/E)`-integral elements,
the finite normal case (`AbsoluteValue.exists_algEquiv_residue_of_normal`) follows from it by
passing to the separable closure and taking `q`-th power roots, and the general case follows
by Zorn's lemma.

-/



open scoped Pointwise
open Polynomial

namespace AbsoluteValue

noncomputable abbrev valSubring {L : Type*} [Field L] {w : AbsoluteValue L ℝ}
    (hw : IsNonarchimedean w) : ValuationSubring L := (w.toValuation hw).valuationSubring

theorem mem_valSubring_iff {L : Type*} [Field L] {w : AbsoluteValue L ℝ}
    (hw : IsNonarchimedean w) (x : L) : x ∈ valSubring hw ↔ w x ≤ 1 := by
  show (w.toValuation hw) x ≤ 1 ↔ _
  rw [← NNReal.coe_le_coe, NNReal.coe_one]
  exact Iff.rfl

/-- Two `F`-algebra homomorphisms from a normal extension `K` into any field have the same range. -/
theorem _root_.AlgHom.fieldRange_eq_of_normal {F K M : Type*} [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Normal F K] (f g : K →ₐ[F] M) :
    g.fieldRange = f.fieldRange := by
  have e : K ≃ₐ[F] f.fieldRange := AlgEquiv.ofInjectiveField f
  haveI : Normal F f.fieldRange := Normal.of_algEquiv e
  have h := AlgHom.fieldRange_of_normal (g.comp e.symm.toAlgHom)
  rw [← h]
  ext x
  simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨e y, by simpa using hy⟩, fun ⟨y, hy⟩ ↦ ⟨e.symm y, hy⟩⟩

/-- In a nonarchimedean world, if `w (a - b) < w b` then `w a = w b`. -/
theorem apply_eq_of_apply_sub_lt {L : Type*} [Field L] {w : AbsoluteValue L ℝ}
    (hw : IsNonarchimedean w) {a b : L} (h : w (a - b) < w b) : w a = w b := by
  have h1 : w a ≤ max (w (a - b)) (w b) := by
    have := hw (a - b) b
    simpa using this
  have h2 : w b ≤ max (w (b - a)) (w a) := by
    have := hw (b - a) a
    simpa using this
  rw [w.map_sub] at h2
  have h3 : w a ≤ w b := h1.trans (max_le h.le le_rfl)
  refine le_antisymm h3 ?_
  rcases max_cases (w (a - b)) (w a) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at h2
  · linarith
  · exact h2

theorem residue_eq_zero_iff {L : Type*} [Field L] {w : AbsoluteValue L ℝ}
    (hw : IsNonarchimedean w) (x : valSubring hw) :
    IsLocalRing.residue _ x = 0 ↔ w (x : L) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff,
    ← NNReal.coe_lt_coe, NNReal.coe_one]
  exact Iff.rfl

theorem residue_eq_iff {L : Type*} [Field L] {w : AbsoluteValue L ℝ}
    (hw : IsNonarchimedean w) (a b : valSubring hw) :
    IsLocalRing.residue _ a = IsLocalRing.residue _ b ↔ w ((a : L) - (b : L)) < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact Iff.rfl

section Localization

variable {E N : Type*} [Field E] [Field N] [Algebra E N] [FiniteDimensional E N]
  {W : AbsoluteValue N ℝ}

/-- Every element of the valuation ring of `W` is a quotient `(s * x) / s` where both `s` and
`s * x` have all their `Gal(N/E)`-conjugates in the valuation ring, and `W s = 1`. -/
theorem exists_apply_eq_one_and_forall_apply_le_one (hW : IsNonarchimedean W)
    (hnt : (W.comp (algebraMap E N).injective).IsNontrivial)
    (x : N) (hx : W x ≤ 1) :
    ∃ s : N, W s = 1 ∧ (∀ ρ : N ≃ₐ[E] N, W (ρ s) ≤ 1) ∧
      (∀ ρ : N ≃ₐ[E] N, W (ρ (s * x)) ≤ 1) := by
  classical
  have hWnt : W.IsNontrivial := (isNontrivial_iff_of_liesOver
    (W.comp (algebraMap E N).injective) W).1 hnt
  set S : Set (AbsoluteValue N ℝ) := Set.range (fun ρ : N ≃ₐ[E] N ↦ ρ • W) with hS
  have hSfin : S.Finite := Set.finite_range _
  have : Finite ↥S := hSfin.to_subtype
  have hcomp : ∀ p : ↥S, (p : AbsoluteValue N ℝ).comp (algebraMap E N).injective =
      W.comp (algebraMap E N).injective := by
    rintro ⟨p, ⟨ρ, rfl⟩⟩
    exact smul_comp_algebraMap W ρ
  have hnt' : ∀ p : ↥S, (p : AbsoluteValue N ℝ).IsNontrivial := by
    rintro ⟨p, ⟨ρ, rfl⟩⟩
    exact isNontrivial_smul ρ hWnt
  have hpw : Pairwise fun p q : ↥S ↦ ¬ (p : AbsoluteValue N ℝ).IsEquiv (q : AbsoluteValue N ℝ) := by
    intro p q hpq he
    exact hpq (Subtype.ext (eq_of_isEquiv_of_comp_eq (by rw [hcomp p]; exact hnt)
      (by rw [hcomp p, hcomp q]) he))
  have hWS : W ∈ S := ⟨1, by simp⟩
  -- a uniform bound for `p x`
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ↥S, (p : AbsoluteValue N ℝ) x ≤ M := by
    obtain ⟨M, hM⟩ := Set.Finite.bddAbove (Set.finite_range fun p : ↥S ↦ (p : AbsoluteValue N ℝ) x)
    exact ⟨max M 0, le_max_right _ _, fun p ↦ (hM ⟨p, rfl⟩).trans (le_max_left _ _)⟩
  set ε : ℝ := 1 / (1 + M) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by linarith)]
    linarith
  obtain ⟨s, hs⟩ := exists_sub_lt_of_not_isEquiv hnt' hpw
    (fun p : ↥S ↦ if (p : AbsoluteValue N ℝ) = W then 1 else 0) hε0
  have hsW : W (s - 1) < ε := by
    have := hs ⟨W, hWS⟩
    rwa [if_pos rfl] at this
  have hs1 : W s = 1 := by
    have h1 : W (s - 1) < 1 := hsW.trans_le hε1
    have h2 : W s ≤ 1 := by
      have := hW (s - 1) 1
      simp only [sub_add_cancel, map_one] at this
      exact this.trans (max_le h1.le le_rfl)
    have h3 : (1 : ℝ) ≤ W s := by
      have := hW (1 - s) s
      simp only [sub_add_cancel, map_one] at this
      rw [W.map_sub] at this
      rcases max_cases (W (s - 1)) (W s) with ⟨h4, -⟩ | ⟨h4, -⟩
      · rw [h4] at this; linarith
      · rw [h4] at this; exact this
    linarith
  have hother : ∀ p : ↥S, (p : AbsoluteValue N ℝ) ≠ W → (p : AbsoluteValue N ℝ) s < ε := by
    intro p hp
    have := hs p
    rwa [if_neg hp, sub_zero] at this
  have key : ∀ p : ↥S, (p : AbsoluteValue N ℝ) s ≤ 1 ∧ (p : AbsoluteValue N ℝ) (s * x) ≤ 1 := by
    intro p
    by_cases hp : (p : AbsoluteValue N ℝ) = W
    · refine ⟨by rw [hp, hs1], ?_⟩
      rw [hp, map_mul, hs1, one_mul]
      exact hx
    · have h1 := (hother p hp).le.trans hε1
      refine ⟨h1, ?_⟩
      rw [map_mul]
      have h2 : (p : AbsoluteValue N ℝ) s * (p : AbsoluteValue N ℝ) x ≤ ε * M :=
        mul_le_mul (hother p hp).le (hM p) ((p : AbsoluteValue N ℝ).nonneg _) hε0.le
      refine h2.trans ?_
      rw [hε, div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
      linarith
  have hsymm : ∀ ρ : N ≃ₐ[E] N, (ρ⁻¹ : N ≃ₐ[E] N).symm = ρ := by
    intro ρ
    rfl
  refine ⟨s, hs1, fun ρ ↦ ?_, fun ρ ↦ ?_⟩
  · have h := (key ⟨ρ⁻¹ • W, ⟨ρ⁻¹, rfl⟩⟩).1
    rw [show ((⟨ρ⁻¹ • W, ⟨ρ⁻¹, rfl⟩⟩ : ↥S) : AbsoluteValue N ℝ) = ρ⁻¹ • W from rfl,
      algEquiv_smul_apply, hsymm ρ] at h
    exact h
  · have h := (key ⟨ρ⁻¹ • W, ⟨ρ⁻¹, rfl⟩⟩).2
    rw [show ((⟨ρ⁻¹ • W, ⟨ρ⁻¹, rfl⟩⟩ : ↥S) : AbsoluteValue N ℝ) = ρ⁻¹ • W from rfl,
      algEquiv_smul_apply, hsymm ρ] at h
    exact h

end Localization

section FiniteGalois

variable {E N : Type*} [Field E] [Field N] [Algebra E N] [FiniteDimensional E N] [IsGalois E N]
  {W : AbsoluteValue N ℝ}

attribute [local instance] Ideal.Quotient.field

/-- The subring of elements of `N` all of whose `Gal(N/E)`-conjugates lie in the valuation ring
of `W`. -/
def galIntegers (hW : IsNonarchimedean W) : Subring N where
  carrier := {y | ∀ ρ : N ≃ₐ[E] N, W (ρ y) ≤ 1}
  mul_mem' {a} {b} ha hb ρ := by
    rw [map_mul, map_mul]
    exact mul_le_one₀ (ha ρ) (W.nonneg _) (hb ρ)
  one_mem' ρ := by simp
  add_mem' {a} {b} ha hb ρ := by
    rw [map_add]
    exact (hW _ _).trans (max_le (ha ρ) (hb ρ))
  zero_mem' ρ := by simp
  neg_mem' {a} ha ρ := by
    rw [map_neg, W.map_neg]
    exact ha ρ

omit [FiniteDimensional E N] [IsGalois E N] in
theorem mem_galIntegers_iff (hW : IsNonarchimedean W) (y : N) :
    y ∈ galIntegers (E := E) hW ↔ ∀ ρ : N ≃ₐ[E] N, W (ρ y) ≤ 1 := Iff.rfl

theorem exists_algEquiv_residue_of_isGalois {L : Type*} [Field L] [Algebra N L]
    {w : AbsoluteValue L ℝ} (hw : IsNonarchimedean w) (j : N →+* L)
    (hval : ∀ x : N, w (j x) = w (algebraMap N L x))
    (hE : ∀ c : E, w (algebraMap N L (algebraMap E N c)) ≤ 1 →
      w (j (algebraMap E N c) - algebraMap N L (algebraMap E N c)) < 1)
    (hWnt : ((w.comp (algebraMap N L).injective).comp (algebraMap E N).injective).IsNontrivial) :
    ∃ ρ : N ≃ₐ[E] N, (∀ x : N, w (algebraMap N L (ρ x)) = w (algebraMap N L x)) ∧
      ∀ x : N, w (algebraMap N L x) ≤ 1 → w (j (ρ x) - algebraMap N L x) < 1 := by
  have hW : IsNonarchimedean (w.comp (algebraMap N L).injective) :=
    (w.isNonarchimedean_comp_iff (algebraMap N L)).2 hw
  have hWE : IsNonarchimedean ((w.comp (algebraMap N L).injective).comp
    (algebraMap E N).injective) :=
    ((w.comp (algebraMap N L).injective).isNonarchimedean_comp_iff (algebraMap E N)).2 hW
  set W : AbsoluteValue N ℝ := w.comp (algebraMap N L).injective with hWdef
  have hWapp : ∀ x : N, W x = w (algebraMap N L x) := fun _ ↦ rfl
  set A : ValuationSubring E := valSubring hWE with hA
  set B : Subring N := galIntegers (E := E) hW with hB
  have hAB : ∀ a : A, (algebraMap E N a) ∈ B := by
    intro a ρ
    rw [AlgEquiv.commutes]
    exact (mem_valSubring_iff hWE _).1 a.2
  letI : Algebra A B := (((algebraMap E N).comp (algebraMap A E)).codRestrict B.toSubsemiring
    (fun a ↦ hAB a)).toAlgebra
  letI : MulSemiringAction (N ≃ₐ[E] N) B := {
    smul ρ b := ⟨ρ b, fun τ ↦ by
      have := b.2 (τ * ρ)
      simpa using this⟩
    one_smul b := Subtype.ext (AlgEquiv.one_apply _)
    mul_smul ρ τ b := Subtype.ext rfl
    smul_zero ρ := Subtype.ext (map_zero ρ)
    smul_add ρ a b := Subtype.ext (map_add ρ _ _)
    smul_one ρ := Subtype.ext (map_one ρ)
    smul_mul ρ a b := Subtype.ext (map_mul ρ _ _) }
  haveI : SMulCommClass (N ≃ₐ[E] N) A B := ⟨by
    intro ρ a b
    ext
    show ρ ((algebraMap E N a) * (b : N)) = (algebraMap E N a) * (ρ (b : N))
    rw [map_mul, AlgEquiv.commutes]⟩
  haveI : Algebra.IsInvariant A B (N ≃ₐ[E] N) := by
    refine ⟨fun b hb ↦ ?_⟩
    have hfix : (b : N) ∈ IntermediateField.fixedField (⊤ : Subgroup (N ≃ₐ[E] N)) := by
      rintro ⟨g, -⟩
      exact congrArg Subtype.val (hb g)
    have hg : IntermediateField.fixedField (⊤ : Subgroup (N ≃ₐ[E] N)) = ⊥ :=
      ((IsGalois.tfae (F := E) (E := N)).out 1 2).mp ‹IsGalois E N›
    rw [hg, IntermediateField.mem_bot] at hfix
    obtain ⟨c, hc⟩ := hfix
    have hcA : c ∈ A := by
      rw [mem_valSubring_iff]
      show W (algebraMap E N c) ≤ 1
      rw [hc]
      simpa using b.2 1
    exact ⟨⟨c, hcA⟩, by ext; exact hc⟩
  haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B (N ≃ₐ[E] N)
  -- the maximal ideal of `A` and the prime of `B` cut out by `W`
  set P : Ideal A := IsLocalRing.maximalIdeal A with hP
  have hmemP : ∀ a : A, a ∈ P ↔ W (algebraMap E N (a : E)) < 1 := by
    intro a
    show a ∈ IsLocalRing.maximalIdeal (valSubring hWE) ↔ _
    rw [Valuation.mem_maximalIdeal_iff, ← NNReal.coe_lt_coe, NNReal.coe_one]
    exact Iff.rfl
  set Q : Ideal B := {
    carrier := {b : B | W (b : N) < 1}
    add_mem' := fun {a} {b} ha hb ↦ lt_of_le_of_lt (hW _ _) (max_lt ha hb)
    zero_mem' := by simp
    smul_mem' := fun c {b} hb ↦ by
      show W ((c : N) * (b : N)) < 1
      rw [map_mul]
      have hc : W (c : N) ≤ 1 := by simpa using c.2 1
      calc W (c : N) * W (b : N) ≤ 1 * W (b : N) :=
            mul_le_mul_of_nonneg_right hc (W.nonneg _)
        _ < 1 := by rw [one_mul]; exact hb } with hQ
  have hmemQ : ∀ b : B, b ∈ Q ↔ W (b : N) < 1 := fun b ↦ Iff.rfl
  haveI : Q.IsPrime := by
    constructor
    · intro h
      have : (1 : B) ∈ Q := h ▸ Submodule.mem_top
      rw [hmemQ] at this
      simp at this
    · intro a b hab
      rw [hmemQ] at hab ⊢
      rw [hmemQ]
      by_contra! h
      obtain ⟨h1, h2⟩ := h
      have ha : W (a : N) ≤ 1 := by simpa using a.2 1
      have hb : W (b : N) ≤ 1 := by simpa using b.2 1
      have : W ((a : N) * (b : N)) = 1 := by
        rw [map_mul]
        nlinarith [W.nonneg (a : N), W.nonneg (b : N)]
      change W (((a * b : B) : N)) < 1 at hab
      push_cast at hab
      rw [this] at hab
      exact lt_irrefl _ hab
  haveI : Q.LiesOver P := by
    constructor
    ext a
    rw [hmemP, Ideal.mem_under, hmemQ]
    exact Iff.rfl
  haveI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q P
  -- the residue field of `L`
  set O : ValuationSubring L := valSubring hw with hO
  have hiB : ∀ b : B, algebraMap N L (b : N) ∈ O := fun b ↦
    (mem_valSubring_iff hw _).2 (by rw [← hWapp]; simpa using b.2 1)
  have hjB : ∀ b : B, j (b : N) ∈ O := fun b ↦
    (mem_valSubring_iff hw _).2 (by rw [hval, ← hWapp]; simpa using b.2 1)
  set iB : B →+* O :=
    RingHom.codRestrict ((algebraMap N L : N →+* L).comp B.subtype) O.toSubring.toSubsemiring hiB
    with hiBdef
  set jB : B →+* O := RingHom.codRestrict (j.comp B.subtype) O.toSubring.toSubsemiring hjB
    with hjBdef
  set ii : B →+* IsLocalRing.ResidueField O := (IsLocalRing.residue O).comp iB with hii
  set jj : B →+* IsLocalRing.ResidueField O := (IsLocalRing.residue O).comp jB with hjj
  have hiiker : ∀ b : B, b ∈ Q → ii b = 0 := by
    intro b hb
    exact (residue_eq_zero_iff hw (iB b)).2 (by rw [hmemQ] at hb; exact hb)
  have hjjker : ∀ b : B, b ∈ Q → jj b = 0 := by
    intro b hb
    refine (residue_eq_zero_iff hw (jB b)).2 ?_
    show w (j (b : N)) < 1
    rw [hval]
    rw [hmemQ] at hb
    exact hb
  -- the two induced embeddings of `B ⧸ Q` into the residue field of `L`
  set iQ : (B ⧸ Q) →+* IsLocalRing.ResidueField O := Ideal.Quotient.lift Q ii hiiker with hiQ
  set jQ : (B ⧸ Q) →+* IsLocalRing.ResidueField O := Ideal.Quotient.lift Q jj hjjker with hjQ
  letI : Algebra (A ⧸ P) (IsLocalRing.ResidueField O) :=
    (Ideal.Quotient.lift P (ii.comp (algebraMap A B)) (by
      intro a ha
      refine hiiker _ ?_
      rw [hmemQ]
      rw [hmemP] at ha
      exact ha)).toAlgebra
  have halgk : ∀ a : A, algebraMap (A ⧸ P) (IsLocalRing.ResidueField O) (Ideal.Quotient.mk P a) =
      ii (algebraMap A B a) := fun a ↦ rfl
  set iA : (B ⧸ Q) →ₐ[A ⧸ P] IsLocalRing.ResidueField O :=
    { __ := iQ
      commutes' := by
        intro x
        induction x using Quotient.inductionOn with
        | h a => rfl } with hiA
  set jA : (B ⧸ Q) →ₐ[A ⧸ P] IsLocalRing.ResidueField O :=
    { __ := jQ
      commutes' := by
        intro x
        induction x using Quotient.inductionOn with
        | h a =>
          show jj (algebraMap A B a) = ii (algebraMap A B a)
          refine (residue_eq_iff hw _ _).2 ?_
          exact hE a ((mem_valSubring_iff hw _).1 (hiB (algebraMap A B a))) } with hjA
  -- the residue extension is normal, so the two embeddings have the same image
  haveI : Normal (A ⧸ P) (B ⧸ Q) := Ideal.Quotient.normal (N ≃ₐ[E] N) P Q
  have hrange : jA.fieldRange = iA.fieldRange := AlgHom.fieldRange_eq_of_normal iA jA
  set eA : (B ⧸ Q) ≃ₐ[A ⧸ P] iA.fieldRange := AlgEquiv.ofInjectiveField iA with heA
  set sig : (B ⧸ Q) →ₐ[A ⧸ P] (B ⧸ Q) :=
    eA.symm.toAlgHom.comp (jA.codRestrict iA.fieldRange.toSubalgebra
      (fun x ↦ hrange ▸ AlgHom.mem_fieldRange.2 ⟨x, rfl⟩)) with hsig
  have hsigapp : ∀ x : B ⧸ Q, iA (sig x) = jA x := by
    intro x
    have : eA (sig x) = ⟨jA x, hrange ▸ AlgHom.mem_fieldRange.2 ⟨x, rfl⟩⟩ := by
      rw [hsig]
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
      exact eA.apply_symm_apply _
    exact congrArg Subtype.val this
  have hbij : Function.Bijective sig := Algebra.IsAlgebraic.algHom_bijective sig
  set sig' : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q) := AlgEquiv.ofBijective sig hbij with hsig'
  obtain ⟨rho0, hrho0⟩ := Ideal.Quotient.stabilizerHom_surjective (N ≃ₐ[E] N) P Q sig'
  -- the residue of `rho0 • b` agrees with the residue of `j b`
  have hBres : ∀ b : B, w (algebraMap N L ((rho0 : N ≃ₐ[E] N) (b : N)) - j (b : N)) < 1 := by
    intro b
    have h1 : sig' (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q ((rho0 : N ≃ₐ[E] N) • b) := by
      rw [← hrho0]
      exact Ideal.Quotient.stabilizerHom_apply Q P (N ≃ₐ[E] N) rho0 b
    have h2 : iA (Ideal.Quotient.mk Q ((rho0 : N ≃ₐ[E] N) • b)) = jA (Ideal.Quotient.mk Q b) := by
      rw [← h1]
      exact hsigapp _
    have h3 : IsLocalRing.residue O (iB ((rho0 : N ≃ₐ[E] N) • b)) =
        IsLocalRing.residue O (jB b) := h2
    exact (residue_eq_iff hw _ _).1 h3
  set rho : N ≃ₐ[E] N := ((rho0 : N ≃ₐ[E] N))⁻¹ with hrhodef
  have hBres' : ∀ x : N, (∀ σ : N ≃ₐ[E] N, W (σ x) ≤ 1) →
      w (j (rho x) - algebraMap N L x) < 1 := by
    intro x hx
    have hxB : x ∈ B := hx
    have h1 := hBres ((rho : N ≃ₐ[E] N) • (⟨x, hxB⟩ : B))
    have h3 : ((((rho : N ≃ₐ[E] N) • (⟨x, hxB⟩ : B)) : B) : N) = rho x := rfl
    rw [h3] at h1
    have h2 : (rho0 : N ≃ₐ[E] N) (rho x) = x := by
      rw [hrhodef]
      simp
    rw [h2] at h1
    rwa [w.map_sub] at h1
  -- extend from `B` to the whole valuation ring of `W`
  have hres : ∀ x : N, W x ≤ 1 → w (j (rho x) - algebraMap N L x) < 1 := by
    intro x hx
    obtain ⟨s, hs1, hsB, hsxB⟩ := exists_apply_eq_one_and_forall_apply_le_one hW hWnt x hx
    have h1 := hBres' s hsB
    have h2 := hBres' (s * x) hsxB
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hs1
      simp at hs1
    set C1 : L := j (rho s) with hC1def
    set C2 : L := algebraMap N L s with hC2def
    set A1 : L := j (rho (s * x)) with hA1def
    set A2 : L := algebraMap N L (s * x) with hA2def
    have hC2 : w C2 = 1 := by rw [hC2def, ← hWapp]; exact hs1
    have hC1w : w C1 = 1 := by
      rw [← hC2]
      exact apply_eq_of_apply_sub_lt hw (by rw [hC2]; exact h1)
    have hC10 : C1 ≠ 0 := by
      intro h
      rw [h] at hC1w
      simp at hC1w
    have hC20 : C2 ≠ 0 := by
      rw [hC2def]
      simpa using hs0
    have hA2 : w A2 ≤ 1 := by
      rw [hA2def, ← hWapp]
      simpa using hsxB 1
    have hjrho : j (rho x) = A1 / C1 := by
      rw [eq_div_iff hC10, hA1def, hC1def, map_mul, map_mul]
      ring
    have hax : algebraMap N L x = A2 / C2 := by
      rw [eq_div_iff hC20, hA2def, hC2def, map_mul]
      ring
    have hdiv : j (rho x) - algebraMap N L x =
        ((A1 - A2) * C2 + A2 * (C2 - C1)) / (C1 * C2) := by
      rw [hjrho, hax]
      field_simp
      ring
    rw [hdiv, map_div₀, map_mul, hC1w, hC2, one_mul, div_one]
    refine lt_of_le_of_lt (hw _ _) (max_lt ?_ ?_)
    · rw [map_mul, hC2, mul_one]
      exact h2
    · rw [map_mul]
      have h5 : w (C2 - C1) < 1 := by rw [w.map_sub]; exact h1
      calc w A2 * w (C2 - C1) ≤ 1 * w (C2 - C1) :=
            mul_le_mul_of_nonneg_right hA2 (w.nonneg _)
        _ < 1 := by rw [one_mul]; exact h5
  -- `rho` preserves the valuation ring, hence the absolute value
  have hball : ∀ x : N, W x ≤ 1 → W (rho x) ≤ 1 := by
    intro x hx
    have h1 := hres x hx
    have h2 : w (j (rho x)) ≤ max (w (j (rho x) - algebraMap N L x)) (w (algebraMap N L x)) := by
      have := hw (j (rho x) - algebraMap N L x) (algebraMap N L x)
      simpa using this
    rw [hval] at h2
    rw [hWapp]
    exact h2.trans (max_le h1.le hx)
  have hpow : ∀ (n : ℕ) (x : N), W x ≤ 1 → W ((rho ^ n) x) ≤ 1 := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ m ih =>
      intro x hx
      have : ((rho ^ (m + 1)) x) = rho ((rho ^ m) x) := by
        rw [pow_succ']
        rfl
      rw [this]
      exact hball _ (ih x hx)
  have hinvball : ∀ x : N, W x ≤ 1 → W (rho⁻¹ x) ≤ 1 := by
    intro x hx
    have hord : 0 < orderOf rho := orderOf_pos rho
    have hinv : rho⁻¹ = rho ^ (orderOf rho - 1) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_succ, Nat.sub_add_cancel hord, pow_orderOf_eq_one]
    rw [hinv]
    exact hpow _ x hx
  have himg : (rho : N → N) '' {x | W x ≤ 1} = {x | W x ≤ 1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hball x hx
    · intro hy
      exact ⟨rho⁻¹ y, hinvball y hy, by simp⟩
  have hdecomp : rho ∈ W.decompositionSubgroup E :=
    (W.mem_decompositionSubgroup_iff_image_setOf_eq rho).2 himg
  exact ⟨rho, fun x ↦ by
    rw [← hWapp, ← hWapp]
    exact W.apply_eq_of_mem_decompositionSubgroup hdecomp x, fun x hx ↦ hres x hx⟩

end FiniteGalois


section NormalCase

variable {E N L : Type*} [Field E] [Field N] [Field L] [Algebra E N] [Algebra N L]
  [FiniteDimensional E N] [Normal E N]

/-- The finite normal case of the residue lifting theorem. -/
theorem exists_algEquiv_residue_of_normal
    {w : AbsoluteValue L ℝ} (hw : IsNonarchimedean w) (j : N →+* L)
    (hval : ∀ x : N, w (j x) = w (algebraMap N L x))
    (hE : ∀ c : E, w (algebraMap N L (algebraMap E N c)) ≤ 1 →
      w (j (algebraMap E N c) - algebraMap N L (algebraMap E N c)) < 1)
    (hWnt : ((w.comp (algebraMap N L).injective).comp (algebraMap E N).injective).IsNontrivial) :
    ∃ ρ : N ≃ₐ[E] N, (∀ x : N, w (algebraMap N L (ρ x)) = w (algebraMap N L x)) ∧
      ∀ x : N, w (algebraMap N L x) ≤ 1 → w (j (ρ x) - algebraMap N L x) < 1 := by
  set Ns := separableClosure E N with hNs
  obtain ⟨q, hq⟩ := ExpChar.exists E
  haveI : ExpChar N q := expChar_of_injective_algebraMap (algebraMap E N).injective q
  haveI : ExpChar L q := expChar_of_injective_algebraMap (algebraMap N L).injective q
  have hq1 : 0 < q := expChar_pos E q
  have hqn : ∀ n : ℕ, q ^ n ≠ 0 := fun n ↦ pow_ne_zero n hq1.ne'
  have htower : ∀ x : Ns, algebraMap Ns L x = algebraMap N L (algebraMap Ns N x) :=
    fun x ↦ IsScalarTower.algebraMap_apply Ns N L x
  obtain ⟨rs, hrs1, hrs2⟩ := exists_algEquiv_residue_of_isGalois (E := E) (N := Ns) (L := L) hw
    (j.comp (algebraMap Ns N)) (fun x ↦ by
      simp only [RingHom.comp_apply]
      rw [hval, htower])
    (fun c hc ↦ by
      simp only [RingHom.comp_apply]
      rw [htower] at hc ⊢
      have h1 : algebraMap Ns N (algebraMap E Ns c) = algebraMap E N c :=
        (IsScalarTower.algebraMap_apply E Ns N c).symm
      rw [h1] at hc ⊢
      exact hE c hc)
    (by
      convert hWnt using 2
      ext c
      show w (algebraMap Ns L (algebraMap E Ns c)) = w (algebraMap N L (algebraMap E N c))
      rw [htower, (IsScalarTower.algebraMap_apply E Ns N c).symm])
  refine ⟨rs.liftNormal N, ?_, ?_⟩
  · intro x
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem (F := Ns) (E := N) q x
    have key1 : (algebraMap N L ((rs.liftNormal N) x)) ^ q ^ n = algebraMap Ns L (rs y) := by
      calc (algebraMap N L ((rs.liftNormal N) x)) ^ q ^ n
          = algebraMap N L ((rs.liftNormal N) (x ^ q ^ n)) := by rw [map_pow, map_pow]
        _ = algebraMap N L ((rs.liftNormal N) (algebraMap Ns N y)) := by rw [hy]
        _ = algebraMap N L (algebraMap Ns N (rs y)) := by rw [rs.liftNormal_commutes]
        _ = algebraMap Ns L (rs y) := (htower _).symm
    have key2 : (algebraMap N L x) ^ q ^ n = algebraMap Ns L y := by
      calc (algebraMap N L x) ^ q ^ n = algebraMap N L (x ^ q ^ n) := (map_pow _ _ _).symm
        _ = algebraMap N L (algebraMap Ns N y) := by rw [hy]
        _ = algebraMap Ns L y := (htower _).symm
    have h1 : (w (algebraMap N L ((rs.liftNormal N) x))) ^ q ^ n =
        (w (algebraMap N L x)) ^ q ^ n :=
      calc (w (algebraMap N L ((rs.liftNormal N) x))) ^ q ^ n
          = w ((algebraMap N L ((rs.liftNormal N) x)) ^ q ^ n) := (map_pow w _ _).symm
        _ = w (algebraMap Ns L (rs y)) := by rw [key1]
        _ = w (algebraMap Ns L y) := hrs1 y
        _ = w ((algebraMap N L x) ^ q ^ n) := by rw [key2]
        _ = (w (algebraMap N L x)) ^ q ^ n := map_pow w _ _
    exact (pow_left_inj₀ (w.nonneg _) (w.nonneg _) (hqn n)).1 h1
  · intro x hx
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem (F := Ns) (E := N) q x
    have key2 : (algebraMap N L x) ^ q ^ n = algebraMap Ns L y := by
      calc (algebraMap N L x) ^ q ^ n = algebraMap N L (x ^ q ^ n) := (map_pow _ _ _).symm
        _ = algebraMap N L (algebraMap Ns N y) := by rw [hy]
        _ = algebraMap Ns L y := (htower _).symm
    have hy1 : w (algebraMap Ns L y) ≤ 1 := by
      rw [← key2, map_pow]
      exact pow_le_one₀ (w.nonneg _) hx
    have key3 : (j ((rs.liftNormal N) x) - algebraMap N L x) ^ q ^ n =
        (j.comp (algebraMap Ns N)) (rs y) - algebraMap Ns L y :=
      calc (j ((rs.liftNormal N) x) - algebraMap N L x) ^ q ^ n
          = (j ((rs.liftNormal N) x)) ^ q ^ n - (algebraMap N L x) ^ q ^ n :=
            sub_pow_expChar_pow ..
        _ = j ((rs.liftNormal N) (x ^ q ^ n)) - (algebraMap N L x) ^ q ^ n := by
              rw [map_pow, map_pow]
        _ = j ((rs.liftNormal N) (algebraMap Ns N y)) - algebraMap Ns L y := by rw [hy, key2]
        _ = j (algebraMap Ns N (rs y)) - algebraMap Ns L y := by rw [rs.liftNormal_commutes]
    have h2 := hrs2 y hy1
    rw [← key3, map_pow] at h2
    by_contra! h3
    exact absurd h2 (not_lt.2 (one_le_pow₀ h3))

end NormalCase


open IntermediateField

section Zorn

variable {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [Algebra K L]
  [IsScalarTower F K L] [Normal F K] [Normal F L]

/-- **Lifting of residue automorphisms**: if `L / K / F` is a tower with `L / F` and `K / F`
normal, `w` a nonarchimedean place of `L`, and `φ₀ : K →ₐ[F] L` preserves `w` and is trivial
modulo the maximal ideal, then `φ₀` extends to an `F`-algebra homomorphism of `L` with the
same properties. -/
theorem exists_algHom_residue {w : AbsoluteValue L ℝ} (hw : IsNonarchimedean w)
    (hnt : (w.comp (algebraMap K L).injective).IsNontrivial)
    (phi0 : K →ₐ[F] L)
    (hval0 : ∀ x : K, w (phi0 x) = w (algebraMap K L x))
    (hres0 : ∀ x : K, w (algebraMap K L x) ≤ 1 → w (phi0 x - algebraMap K L x) < 1) :
    ∃ psi : L →ₐ[F] L, (∀ x : L, w (psi x) = w x) ∧ (∀ x : L, w x ≤ 1 → w (psi x - x) < 1) ∧
      (∀ x : K, psi (algebraMap K L x) = phi0 x) := by
  classical
  set iK : K →ₐ[F] L := IsScalarTower.toAlgHom F K L with hiK
  set eK : K ≃ₐ[F] iK.fieldRange := AlgEquiv.ofInjectiveField iK with heK
  set base : Lifts F L L := ⟨iK.fieldRange, phi0.comp eK.symm.toAlgHom⟩ with hbasedef
  have hbaseK : ∀ x : K, base.emb ⟨algebraMap K L x, ⟨x, rfl⟩⟩ = phi0 x := by
    intro x
    show phi0 (eK.symm ⟨algebraMap K L x, ⟨x, rfl⟩⟩) = phi0 x
    congr 1
    exact eK.injective (by rw [AlgEquiv.apply_symm_apply]; exact Subtype.ext rfl)
  set P : Set (Lifts F L L) := {ϕ | base ≤ ϕ ∧ Normal F ϕ.carrier ∧
      (∀ x : ϕ.carrier, w (ϕ.emb x) = w (x : L)) ∧
      (∀ x : ϕ.carrier, w (x : L) ≤ 1 → w (ϕ.emb x - (x : L)) < 1)} with hP
  have hbase : base ∈ P := by
    refine ⟨le_rfl, ?_, ?_, ?_⟩
    · show Normal F iK.fieldRange
      exact Normal.of_algEquiv eK
    · rintro ⟨x, ⟨y, rfl⟩⟩
      show w (phi0 (eK.symm ⟨iK y, ⟨y, rfl⟩⟩)) = w (iK y)
      rw [show eK.symm ⟨iK y, ⟨y, rfl⟩⟩ = y from eK.injective (by rw [AlgEquiv.apply_symm_apply]; exact Subtype.ext rfl)]
      exact hval0 y
    · rintro ⟨x, ⟨y, rfl⟩⟩ hx
      show w (phi0 (eK.symm ⟨iK y, ⟨y, rfl⟩⟩) - iK y) < 1
      rw [show eK.symm ⟨iK y, ⟨y, rfl⟩⟩ = y from eK.injective (by rw [AlgEquiv.apply_symm_apply]; exact Subtype.ext rfl)]
      exact hres0 y hx
  have key : ∀ c ⊆ P, IsChain (· ≤ ·) c → ∃ ub ∈ P, ∀ z ∈ c, z ≤ ub := by
    intro c hcP hc
    rcases Set.eq_empty_or_nonempty c with rfl | ⟨ϕ₀, hϕ₀⟩
    · exact ⟨base, hbase, by simp⟩
    have hne : Nonempty c := ⟨⟨ϕ₀, hϕ₀⟩⟩
    have hsplit : ∀ x : (Lifts.union c hc).carrier, ∃ (i : c) (hi : (x : L) ∈
        (i : Lifts F L L).carrier), (Lifts.union c hc).emb x = (i : Lifts F L L).emb ⟨(x : L), hi⟩ := by
      intro x
      have hdir : Directed (· ≤ ·) (fun i : c ↦ (i : Lifts F L L).carrier) :=
        (hc.directedOn.directed_val).mono_comp _ (fun _ _ hxy ↦ hxy.1)
      have hx : (x : L) ∈ ⨆ i : c, (i : Lifts F L L).carrier :=
        le_of_eq (Lifts.carrier_union c hc) x.2
      rw [← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed hdir, Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      refine ⟨i, hi, ?_⟩
      have h2 := (Lifts.le_union c hc i.2).2 ⟨(x : L), hi⟩
      rw [← h2]
      rfl
    refine ⟨Lifts.union c hc, ⟨?_, ?_, ?_, ?_⟩, fun z hz ↦ Lifts.le_union c hc hz⟩
    · exact le_trans (hcP hϕ₀).1 (Lifts.le_union c hc hϕ₀)
    · rw [Lifts.carrier_union]
      have : ∀ i : c, Normal F (i : Lifts F L L).carrier := fun i ↦ (hcP i.2).2.1
      exact IntermediateField.normal_iSup F L _
    · intro x
      obtain ⟨i, hi, h3⟩ := hsplit x
      rw [h3]
      exact (hcP i.2).2.2.1 ⟨(x : L), hi⟩
    · intro x hx
      obtain ⟨i, hi, h3⟩ := hsplit x
      rw [h3]
      exact (hcP i.2).2.2.2 ⟨(x : L), hi⟩ hx
  obtain ⟨ϕ, hϕ⟩ := zorn_le₀ P key
  have hcar : ϕ.carrier = ⊤ := by
    by_contra hne
    obtain ⟨α, -, hα⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hne)
    haveI hEnormal : Normal F ϕ.carrier := hϕ.1.2.1
    set E := ϕ.carrier with hE
    set tau0 : L →ₐ[F] L := ϕ.emb.liftNormal L with htau0
    have htau0E : ∀ x : E, tau0 (x : L) = ϕ.emb x := by
      intro x
      have h1 := ϕ.emb.liftNormal_commutes (E := L) x
      simpa using h1
    set p := minpoly F α with hp
    have hαint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
    have hp0 : p ≠ 0 := minpoly.ne_zero hαint
    have hsplits : (p.map (algebraMap F L)).Splits := Normal.splits ‹Normal F L› α
    have hrs : (p.map (algebraMap F E)).rootSet L = p.rootSet L := by
      simp [Polynomial.rootSet, Polynomial.aroots, Polynomial.map_map,
        ← IsScalarTower.algebraMap_eq]
    set N : IntermediateField E L := adjoin E (p.rootSet L) with hN
    have hsp : ((p.map (algebraMap F E)).map (algebraMap E L)).Splits := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]; exact hsplits
    haveI hNsf : IsSplittingField E N (p.map (algebraMap F E)) := by
      have h6 := adjoin_rootSet_isSplittingField (K := E) (L := L) hsp
      rwa [hrs] at h6
    haveI hNnormal : Normal E N := Normal.of_isSplittingField (p.map (algebraMap F E))
    haveI hNfin : FiniteDimensional E N := by
      refine finiteDimensional_adjoin ?_
      intro y _
      exact (Algebra.IsIntegral.isIntegral (R := F) y).tower_top
    -- normalize the values by the finite conjugacy theorem
    set a : AbsoluteValue N ℝ := w.comp (f := ((tau0 : L →+* L).comp (algebraMap N L)))
      (((tau0 : L →+* L).comp (algebraMap N L)).injective) with ha
    set b : AbsoluteValue N ℝ := w.comp (algebraMap N L).injective with hb
    have hab : a.comp (algebraMap E N).injective = b.comp (algebraMap E N).injective := by
      ext y
      show w (tau0 ((algebraMap E N y : N) : L)) = w ((algebraMap E N y : N) : L)
      show w (tau0 (y : L)) = w (y : L)
      rw [htau0E y]
      exact hϕ.1.2.2.1 y
    obtain ⟨rho, hrho⟩ := exists_smul_eq_of_comp_eq_of_finiteDimensional (F := E) (K := N) hab
    have hrho' : ∀ x : N, w (tau0 ((rho.symm x : N) : L)) = w ((x : N) : L) := fun x ↦ congr($hrho x)
    -- apply the finite normal residue lifting theorem
    set jN : N →+* L := (tau0 : L →+* L).comp ((algebraMap N L).comp (rho.symm : N →+* N))
      with hjN
    have hvalN : ∀ x : N, w (jN x) = w (algebraMap N L x) := fun x ↦ hrho' x
    have hEN : ∀ c : E, w (algebraMap N L (algebraMap E N c)) ≤ 1 →
        w (jN (algebraMap E N c) - algebraMap N L (algebraMap E N c)) < 1 := by
      intro c hc
      have h1 : jN (algebraMap E N c) = ϕ.emb c := by
        show tau0 (algebraMap N L (rho.symm (algebraMap E N c))) = ϕ.emb c
        rw [AlgEquiv.commutes]
        show tau0 ((c : L)) = ϕ.emb c
        exact htau0E c
      have h2 : algebraMap N L (algebraMap E N c) = (c : L) := rfl
      rw [h1, h2]
      rw [h2] at hc
      exact hϕ.1.2.2.2 c hc
    have hWntN : ((w.comp (algebraMap N L).injective).comp (algebraMap E N).injective).IsNontrivial := by
      obtain ⟨x, hx0, hx1⟩ := hnt
      have hmem : algebraMap K L x ∈ E := hϕ.1.1.1 ⟨x, rfl⟩
      refine ⟨(⟨algebraMap K L x, hmem⟩ : E), ?_, ?_⟩
      · intro h
        apply hx0
        have h2 : algebraMap K L x = 0 := congrArg Subtype.val h
        simpa using h2
      · show w ((algebraMap K L x : L)) ≠ 1
        exact hx1
    obtain ⟨rho2, hrho2a, hrho2b⟩ := exists_algEquiv_residue_of_normal hw jN hvalN hEN hWntN
    -- build the bigger lift
    set psi : Lifts F L L := ⟨N.restrictScalars F,
      (tau0.comp ((IntermediateField.val N).restrictScalars F)).comp
        ((rho2.trans rho.symm).restrictScalars F).toAlgHom⟩ with hpsi
    have hcarle : E ≤ N.restrictScalars F := by
      rw [hN, IntermediateField.restrictScalars_adjoin_eq_sup]
      exact le_sup_left
    have hpsiemb : ∀ x : N, psi.emb x = jN (rho2 x) := fun x ↦ rfl
    have hle : ϕ ≤ psi := by
      refine ⟨hcarle, fun y ↦ ?_⟩
      have h7 : (inclusion hcarle y) = algebraMap E N y := rfl
      rw [h7, hpsiemb (algebraMap E N y)]
      show tau0 (algebraMap N L (rho.symm (rho2 (algebraMap E N y)))) = ϕ.emb y
      rw [AlgEquiv.commutes, AlgEquiv.commutes]
      exact htau0E y
    have hpsiP : psi ∈ P := by
      refine ⟨le_trans hϕ.1.1 hle, ?_, ?_, ?_⟩
      · show Normal F (N.restrictScalars F)
        rw [hN, IntermediateField.restrictScalars_adjoin_eq_sup]
        haveI : Normal F (adjoin F (p.rootSet L)) :=
          Normal.of_isSplittingField (E := adjoin F (p.rootSet L)) p
            (hFEp := adjoin_rootSet_isSplittingField hsplits)
        exact IntermediateField.normal_sup F L _ _
      · intro x
        rw [hpsiemb x, hvalN]
        exact hrho2a x
      · intro x hx
        rw [hpsiemb x]
        exact hrho2b x hx
    have hmem : α ∈ psi.carrier := by
      show α ∈ N.restrictScalars F
      show α ∈ N
      rw [hN]
      exact subset_adjoin _ _ (Polynomial.mem_rootSet.2 ⟨hp0, minpoly.aeval F α⟩)
    exact hα ((hϕ.2 hpsiP hle).1 hmem)
  refine ⟨ϕ.emb.comp (((IntermediateField.equivOfEq hcar).trans
    IntermediateField.topEquiv).symm : L →ₐ[F] ϕ.carrier), ?_, ?_, ?_⟩
  · intro x
    have h1 := hϕ.1.2.2.1 (((IntermediateField.equivOfEq hcar).trans
      IntermediateField.topEquiv).symm x)
    simpa using h1
  · intro x hx
    have h1 := hϕ.1.2.2.2 (((IntermediateField.equivOfEq hcar).trans
      IntermediateField.topEquiv).symm x) (by simpa using hx)
    simpa using h1
  · intro x
    have h2 := hϕ.1.1.2 ⟨algebraMap K L x, ⟨x, rfl⟩⟩
    rw [hbaseK x] at h2
    rw [← h2]
    exact congrArg ϕ.emb (Subtype.ext rfl)

end Zorn

end AbsoluteValue
