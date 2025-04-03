import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!

# `ℤₚ`-extension of fields

-/

universe u v

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) (Kinf : Type v) [Field K] [Field Kinf] [Algebra K Kinf]

/-- A Galois extension `K∞ / K` ia called a `ℤₚ`-extension, if its Galois group is
isomorphic to `ℤₚ` as a topological group. -/
@[mk_iff]
structure IsZpExtension [IsGalois K Kinf] : Prop where
  nonempty_continuousMulEquiv : Nonempty ((Kinf ≃ₐ[K] Kinf) ≃ₜ* Multiplicative ℤ_[p])

variable [IsGalois K Kinf]

namespace IsZpExtension

variable {p K Kinf}

set_option linter.unusedVariables false in
/-- The Galois group `Γ := Gal(K∞ / K)` of a `ℤₚ`-extension `K∞ / K`. -/
abbrev Γ (H : IsZpExtension p K Kinf) := Kinf ≃ₐ[K] Kinf

variable (H : IsZpExtension p K Kinf)

/-- A random isomorphism from `Γ` to `ℤₚ`. -/
noncomputable def continuousMulEquiv : H.Γ ≃ₜ* Multiplicative ℤ_[p] :=
  Classical.choice H.nonempty_continuousMulEquiv

/-- A random topological generator `γ` of `Γ`. -/
noncomputable def γ : H.Γ := H.continuousMulEquiv.symm (Multiplicative.ofAdd 1)

/-- The `Γ` is commutative. -/
instance commGroup : CommGroup H.Γ := {
  inferInstanceAs (Group H.Γ) with
  mul_comm a b := by
    apply H.continuousMulEquiv.injective
    simp_rw [map_mul, mul_comm]
}

/-- The `γ` is a topological generator of `Γ`. -/
@[simp]
theorem closure_γ_eq_top : closure (Subgroup.closure {H.γ} : Set H.Γ) = ⊤ := by
  sorry

/-- The open subgroup `Γ ^ (p ^ n)` of `Γ`. -/
noncomputable def Γpow (n : ℕ) : OpenSubgroup H.Γ where
  toSubgroup := (p ^ n : Ideal ℤ_[p]).toAddSubgroup.toSubgroup.comap H.continuousMulEquiv
  isOpen' := by
    refine IsOpen.preimage H.continuousMulEquiv.continuous ?_
    change IsOpen ((p ^ n : Ideal ℤ_[p]) : Set ℤ_[p])
    sorry

theorem mem_Γpow_iff (n : ℕ) (σ : H.Γ) : σ ∈ H.Γpow n ↔ ∃ τ, σ = τ ^ p ^ n := by
  sorry

instance normal_Γpow (n : ℕ) : (H.Γpow n).Normal := inferInstance

@[simp]
theorem index_Γpow (n : ℕ) : (H.Γpow n).index = p ^ n := by
  sorry

/-- The `γ ^ (p ^ n)` is a topological generator of `Γ ^ (p ^ n)`. -/
@[simp]
theorem closure_γ_pow_eq (n : ℕ) :
    closure (Subgroup.closure {H.γ ^ p ^ n} : Set H.Γ) = H.Γpow n := by
  sorry

/-- The intermediate field `Kₙ` of `K∞ / K` fixed by `Γ ^ (p ^ n)`. -/
noncomputable def intermediateField (n : ℕ) : IntermediateField K Kinf :=
  IntermediateField.fixedField (H.Γpow n)

/-- `Kₙ / K` is Galois. -/
instance isGalois_intermediateField (n : ℕ) : IsGalois K (H.intermediateField n) :=
  IsGalois.of_fixedField_normal_subgroup (H.Γpow n).toSubgroup

/-- The fixing subgroup of `Kₙ` is `Γ ^ (p ^ n)`. -/
@[simp]
theorem fixingSubgroup_intermediateField (n : ℕ) :
    (H.intermediateField n).fixingSubgroup = H.Γpow n :=
  let G : ClosedSubgroup H.Γ := {
    toSubgroup := (H.Γpow n).toSubgroup
    isClosed' := (H.Γpow n).isClosed
  }
  InfiniteGalois.fixingSubgroup_fixedField G

/-- `Kₙ / K` is a finite extension. -/
instance finiteDimensional_intermediateField (n : ℕ) :
    FiniteDimensional K (H.intermediateField n) := by
  rw [← InfiniteGalois.isOpen_iff_finite, fixingSubgroup_intermediateField]
  exact (H.Γpow n).isOpen

/-- `Kₙ / K` is of degree `p ^ n`. -/
@[simp]
theorem finrank_intermediateField (n : ℕ) :
    Module.finrank K (H.intermediateField n) = p ^ n := by
  sorry

end IsZpExtension
