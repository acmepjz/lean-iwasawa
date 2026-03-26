/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Iwasawalib.NumberTheory.Padics.EquivMvZp
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Iwasawalib.Topology.Algebra.Group.Basic

@[expose] public section

/-!

# `ℤₚ`-extension of fields

In this file, when `Kinf / K` is a Galois extension of fields, we define `MvZpExtension p ι K Kinf`,
which is an isomorphism of `Gal(Kinf / K)` and `Multiplicative (ι → ℤ_[p])` as topological groups.

To state that `Gal(Kinf / K)` is isomorphic to `Multiplicative (ι → ℤ_[p])` as topological groups,
use `Nonempty (MvZpExtension p ι K Kinf)`. As a special case, to state that `Kinf / K` is
a `ℤₚᵈ`-extension, use `Nonempty (MvZpExtension p (Fin d) K Kinf)`.

-/

/-! ### Maybe these should be in mathlib -/

theorem AlgEquiv.continuous_autCongr
    {R A₁ A₂ : Type*} [Field R] [Field A₁] [Field A₂] [Algebra R A₁] [Algebra R A₂]
    (ϕ : A₁ ≃ₐ[R] A₂) : Continuous ϕ.autCongr := by
  refine ϕ.autCongr.toMonoidHom.continuous_iff.2 fun s h1 hs ↦ ?_
  obtain ⟨L, _, hle⟩ := (krullTopology_mem_nhds_one_iff _ _ s).1 (isOpen_iff_mem_nhds.1 hs _ h1)
  refine ⟨L.fixingSubgroup.comap ϕ.autCongr.toMonoidHom, one_mem _, ?_, by simpa⟩
  have := (L.equivMap ϕ.symm.toAlgHom).toLinearEquiv.finiteDimensional
  convert (L.map ϕ.symm.toAlgHom).fixingSubgroup_isOpen
  ext f
  simp only [MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_comap, MonoidHom.coe_coe, autCongr_apply,
    IntermediateField.mem_fixingSubgroup_iff, trans_apply, toAlgHom_eq_coe]
  change _ ↔ ∀ x ∈ (L.map _).toSubalgebra, _
  simp only [IntermediateField.toSubalgebra_map, Subalgebra.mem_map, and_imp, forall_exists_index,
    IntermediateField.mem_toSubalgebra, AlgHom.coe_coe, forall_apply_eq_imp_iff₂]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · apply_fun _ using ϕ.injective
    simp [h x hx]
  · simp [h x hx]

/-- Continuous version of `AlgEquiv.autCongr`. -/
@[simps! apply toMulEquiv]
def AlgEquiv.continuousAutCongr
    {R A₁ A₂ : Type*} [Field R] [Field A₁] [Field A₂] [Algebra R A₁] [Algebra R A₂]
    (ϕ : A₁ ≃ₐ[R] A₂) : (A₁ ≃ₐ[R] A₁) ≃ₜ* A₂ ≃ₐ[R] A₂ where
  toMulEquiv := ϕ.autCongr
  continuous_toFun := ϕ.continuous_autCongr
  continuous_invFun := ϕ.symm.continuous_autCongr

/-! ### `ℤₚᵈ`-extension -/

variable (p : ℕ) [Fact p.Prime] (ι K Kinf : Type*)
variable [Field K] [Field Kinf] [Algebra K Kinf]

/-- `MvZpExtension` is an isomorphism of the Galois group of a Galois extension `K∞ / K`
to `ℤₚᵈ` as topological groups. -/
abbrev MvZpExtension [IsGalois K Kinf] := EquivMvZp Gal(Kinf/K) p ι

variable {p ι K Kinf} in
/-- Transfer `MvZpExtension` along field isomorphisms. -/
noncomputable def MvZpExtension.congr [IsGalois K Kinf] (H : MvZpExtension p ι K Kinf)
    {ι' : Type*} (e : ι ≃ ι')
    {Kinf' : Type*} [Field Kinf'] [Algebra K Kinf'] (f : Kinf ≃ₐ[K] Kinf') [IsGalois K Kinf'] :
    MvZpExtension p ι' K Kinf' :=
  EquivMvZp.congr H f.continuousAutCongr e

namespace MvZpExtension

section Finite

variable {p ι K Kinf} [Finite ι] [IsGalois K Kinf] (H : MvZpExtension p ι K Kinf)
include H

/-- Version of `MvZpExtension.congr` for finite case. -/
noncomputable def congrFinOfCardEq {d : ℕ} (h : Nat.card ι = d)
    {Kinf' : Type*} [Field Kinf'] [Algebra K Kinf'] (f : Kinf ≃ₐ[K] Kinf') [IsGalois K Kinf'] :
    MvZpExtension p (Fin d) K Kinf' :=
  H.congr (Finite.equivFinOfCardEq h) f

omit [Finite ι] in
/-- `K∞ / K` is abelian. -/
theorem isAbelianGalois_Kinf : IsAbelianGalois K Kinf where
  is_comm := by
    refine ⟨fun x y ↦ ?_⟩
    apply_fun H.continuousMulEquiv using H.continuousMulEquiv.injective
    simp only [map_mul, mul_comm]

/-- Any subgroup in `Γ` is a normal subgroup. -/
instance normal (G : Subgroup H.Γ) : G.Normal := inferInstance

/-- The intermediate field `Kₙ` of `K∞ / K` fixed by `Γ ^ (p ^ n)`. -/
noncomputable def Kn (n : ℕ) : IntermediateField K Kinf :=
  IntermediateField.fixedField (H.Γpow n)

/-- `K₀ = K`. -/
@[simp]
theorem Kn_zero : H.Kn 0 = ⊥ := by
  simp [Kn, InfiniteGalois.fixedField_bot]

omit [Finite ι] in
/-- Any intermediate field of `K∞ / K` is Galois. -/
theorem isGalois (K' : IntermediateField K Kinf) : IsGalois K K' := by
  let G : Subgroup H.Γ := K'.fixingSubgroup
  have : IntermediateField.fixedField G = K' := InfiniteGalois.fixedField_fixingSubgroup _
  convert ← IsGalois.of_fixedField_normal_subgroup G

omit [Finite ι] in
/-- Any intermediate field of `K∞ / K` is abelian. -/
theorem isAbelianGalois (K' : IntermediateField K Kinf) : IsAbelianGalois K K' := by
  have := H.isAbelianGalois_Kinf
  exact .tower_bot K K' Kinf

/-- `Kₙ / K` is Galois. -/
instance isGalois_Kn (n : ℕ) : IsGalois K (H.Kn n) := H.isGalois _

/-- `Kₙ / K` is abelian. -/
instance isAbelianGalois_Kn (n : ℕ) : IsAbelianGalois K (H.Kn n) := H.isAbelianGalois _

/-- The fixing subgroup of `Kₙ` is `Γ ^ (p ^ n)`. -/
@[simp]
theorem fixingSubgroup_Kn (n : ℕ) : (H.Kn n).fixingSubgroup = H.Γpow n :=
  let G : ClosedSubgroup H.Γ := {
    toSubgroup := (H.Γpow n).toSubgroup
    isClosed' := (H.Γpow n).isClosed
  }
  InfiniteGalois.fixingSubgroup_fixedField G

/-- `Kₙ / K` is a finite extension. -/
instance finiteDimensional_Kn (n : ℕ) : FiniteDimensional K (H.Kn n) := by
  rw [← InfiniteGalois.isOpen_iff_finite, fixingSubgroup_Kn]
  exact (H.Γpow n).isOpen

/-- `Kₙ / K` is of degree `p ^ (n * #ι)`. -/
@[simp]
theorem finrank_Kn (n : ℕ) : Module.finrank K (H.Kn n) = p ^ (n * Nat.card ι) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, H.fixingSubgroup_Kn, H.index_Γpow]

/-- If `m ≤ n` then `Kₘ ≤ Kₙ`. -/
theorem monotone_Kn : Monotone H.Kn := monotone_nat_of_le_succ fun n ↦ by
  nth_rw 2 [Kn]
  rw [IntermediateField.le_iff_le, fixingSubgroup_Kn]
  exact H.antitone_Γpow (by simp)

/-- If `m < n` then `Kₘ < Kₙ`. -/
theorem strictMono_Kn [Nonempty ι] : StrictMono H.Kn :=
  H.monotone_Kn.strictMono_of_injective fun n n' h ↦ by
    replace h := congr(Module.finrank K ($h))
    rw [finrank_Kn, finrank_Kn] at h
    have hd := Nat.card_ne_zero.2 ⟨‹Nonempty ι›, ‹Finite ι›⟩
    simpa [hd] using Nat.pow_right_injective (Fact.out : p.Prime).two_le h

/-- If `K'` is a finite extension of `K` contained in `K∞`,
then it's contained in `Kₙ` for some `n`. -/
theorem le_Kn_of_finiteDimensional (K' : IntermediateField K Kinf) [FiniteDimensional K K'] :
    ∃ n, K' ≤ H.Kn n := by
  obtain ⟨n, _⟩ := H.Γpow_le_of_isOpen _ K'.fixingSubgroup_isOpen
  exact ⟨n, by rwa [Kn, IntermediateField.le_iff_le]⟩

/-- If `K'` is a finite extension of `K` contained in `K∞`,
then `[K' : K] = p ^ n` for some `n`. -/
theorem finrank_eq_pow_of_finiteDimensional (K' : IntermediateField K Kinf)
    [FiniteDimensional K K'] : ∃ n, Module.finrank K K' = p ^ n := by
  obtain ⟨m, h⟩ := H.le_Kn_of_finiteDimensional K'
  have h1 : Module.finrank K K' ∣ p ^ (m * Nat.card ι) := by
    let L := IntermediateField.extendScalars h
    have := Module.Free.of_divisionRing K' L
    have := Module.finrank_mul_finrank K K' L
    rw [show Module.finrank K L = _ from H.finrank_Kn m] at this
    exact dvd_of_mul_right_eq _ this
  obtain ⟨n, -, h2⟩ := (Nat.dvd_prime_pow Fact.out).1 h1
  exact ⟨n, h2⟩

theorem finiteDimensional_iff_isEmpty : FiniteDimensional K Kinf ↔ IsEmpty ι := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · rcases isEmpty_or_nonempty ι with _ | _
    · assumption
    obtain ⟨n, h⟩ := H.le_Kn_of_finiteDimensional ⊤
    simpa using h.trans_lt (H.strictMono_Kn (Nat.lt_add_one n))
  · have : Finite Gal(Kinf/K) := by
      rw [← Cardinal.lt_aleph0_iff_finite]
      convert Cardinal.one_lt_aleph0
      simpa using H.1.toEquiv.lift_cardinal_eq
    exact IsGalois.finiteDimensional_of_finite K Kinf

theorem finiteDimensional_iff_card_eq_zero : FiniteDimensional K Kinf ↔ Nat.card ι = 0 := by
  rw [H.finiteDimensional_iff_isEmpty, Finite.card_eq_zero_iff]

theorem infinite_dimensional [Nonempty ι] : ¬FiniteDimensional K Kinf := by
  rwa [H.finiteDimensional_iff_isEmpty, not_isEmpty_iff]

end Finite

section Unique

variable {p ι K Kinf} [Unique ι] [IsGalois K Kinf]

/-! ### `ℤₚ`-extension -/

/-- An isomorphism from `Γ` to `ℤₚ` gives an `MvZpExtension` when `ι` consists of
exactly one element. -/
noncomputable def ofContinuousMulEquiv₁ (e : Gal(Kinf/K) ≃ₜ* Multiplicative ℤ_[p]) :
    MvZpExtension p ι K Kinf :=
  EquivMvZp.ofContinuousMulEquiv₁ e

theorem nonempty_iff_of_unique :
    Nonempty (MvZpExtension p ι K Kinf) ↔ Nonempty (Gal(Kinf/K) ≃ₜ* Multiplicative ℤ_[p]) :=
  ⟨fun ⟨f⟩ ↦ ⟨f.continuousMulEquiv₁⟩, fun ⟨f⟩ ↦ ⟨.ofContinuousMulEquiv₁ f⟩⟩

variable (H : MvZpExtension p ι K Kinf)
include H

/-- `Kₙ / K` is of degree `p ^ n`. -/
theorem finrank_Kn₁ (n : ℕ) : Module.finrank K (H.Kn n) = p ^ n := by
  simp

/-- If `K'` is a finite extension of `K` contained in `K∞`,
then it's equal to `Kₙ` for some `n`. -/
theorem eq_Kn_of_finiteDimensional (K' : IntermediateField K Kinf) [FiniteDimensional K K'] :
    ∃ n, K' = H.Kn n := by
  obtain ⟨n, h⟩ := H.eq_Γpow_of_isOpen _ K'.fixingSubgroup_isOpen
  replace h := congr(IntermediateField.fixedField $h)
  exact ⟨n, by rwa [InfiniteGalois.fixedField_fixingSubgroup] at h⟩

/-- If `K'` is an extension of `K` contained in `K∞`,
then it's equal to `K∞` or `Kₙ` for some `n`. -/
theorem eq_top_or_Kn (K' : IntermediateField K Kinf) :
    K' = ⊤ ∨ ∃ n, K' = H.Kn n := by
  obtain h | ⟨n, h⟩ := H.eq_bot_or_Γpow_of_isClosed _ (InfiniteGalois.fixingSubgroup_isClosed K')
  · refine .inl (eq_top_iff.2 ?_)
    rw [← InfiniteGalois.fixedField_fixingSubgroup K', IntermediateField.le_iff_le]
    simp [h]
  · replace h := congr(IntermediateField.fixedField $h)
    exact .inr ⟨n, by rwa [InfiniteGalois.fixedField_fixingSubgroup] at h⟩

/-- If `K'` is an infinite extension of `K` contained in `K∞`,
then it's equal to `K∞`. -/
theorem eq_top_of_infinite_dimensional (K' : IntermediateField K Kinf)
    (h : ¬FiniteDimensional K K') : K' = ⊤ := by
  obtain h | ⟨n, rfl⟩ := H.eq_top_or_Kn K'
  · exact h
  · exact False.elim (h inferInstance)

/-- If `K'` is an extension of `K` of degree `p ^ n` contained in `K∞`,
then it's equal to `Kₙ`. -/
theorem eq_Kn_of_finrank_eq (K' : IntermediateField K Kinf)
    {n : ℕ} (h : Module.finrank K K' = p ^ n) : K' = H.Kn n := by
  have : FiniteDimensional K K' := .of_finrank_pos <| by
    have := (Fact.out : p.Prime).pos
    rw [h]
    positivity
  obtain ⟨m, hm⟩ := H.eq_Kn_of_finiteDimensional K'
  convert hm
  replace hm := congr(Module.finrank K $hm)
  rw [h, H.finrank_Kn₁] at hm
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hm

end Unique

end MvZpExtension
