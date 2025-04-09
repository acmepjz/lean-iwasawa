import Mathlib.FieldTheory.Galois.Infinite
-- import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Ring.Compact

/-!

# `ℤₚ`-extension of fields

## Main definitions

- `IsMvZpExtension`: a `Prop` which asserts that a Galois extension is with Galois group
  isomorphic to `ℤₚᵈ` as a topological group.

- `IsZpExtension`: a `Prop` which asserts that a Galois extension is with Galois group
  isomorphic to `ℤₚ` as a topological group. It is defined as `IsMvZpExtension` with `d = 1`,
  hence it inherits fields of `IsMvZpExtension`.

-/

universe u v

variable (p : ℕ) [Fact p.Prime] (d : ℕ) (K : Type u) (Kinf : Type v)
variable [Field K] [Field Kinf] [Algebra K Kinf]

/-- A Galois extension `K∞ / K` ia called a `ℤₚᵈ`-extension, if its Galois group is
isomorphic to `ℤₚᵈ` as a topological group. -/
@[mk_iff]
structure IsMvZpExtension [IsGalois K Kinf] : Prop where
  nonempty_continuousMulEquiv :
    Nonempty ((Kinf ≃ₐ[K] Kinf) ≃ₜ* Multiplicative (Fin d → ℤ_[p]))

namespace IsMvZpExtension

variable [IsGalois K Kinf]

variable {p d K Kinf}

set_option linter.unusedVariables false in
/-- The Galois group `Γ := Gal(K∞ / K)` of a `ℤₚᵈ`-extension `K∞ / K`. -/
abbrev Γ (H : IsMvZpExtension p d K Kinf) := Kinf ≃ₐ[K] Kinf

variable (H : IsMvZpExtension p d K Kinf)

/-- A random isomorphism from `Γ` to `ℤₚᵈ`. -/
noncomputable def continuousMulEquiv : H.Γ ≃ₜ* Multiplicative (Fin d → ℤ_[p]) :=
  Classical.choice H.nonempty_continuousMulEquiv

/-- The `Γ` is commutative. -/
instance commGroup : CommGroup H.Γ := {
  inferInstanceAs (Group H.Γ) with
  mul_comm a b := by
    apply H.continuousMulEquiv.injective
    simp_rw [map_mul, mul_comm]
}

/-- The open subgroup `Γ ^ (p ^ n)` of `Γ`. -/
noncomputable def Γpow (n : ℕ) : OpenSubgroup H.Γ where
  toSubgroup := (Ideal.pi fun _ ↦ Ideal.span {(p ^ n : ℤ_[p])} : Ideal (Fin d → ℤ_[p]))
    |>.toAddSubgroup.toSubgroup.comap H.continuousMulEquiv
  isOpen' := by
    have h1 : IsOpen (Ideal.span {(p ^ n : ℤ_[p])} : Set ℤ_[p]) := by
      rw [IsDiscreteValuationRing.isOpen_iff]
      simp [show p ≠ 0 from NeZero.out]
    refine IsOpen.preimage H.continuousMulEquiv.continuous ?_
    change IsOpen ((Ideal.pi fun _ ↦ Ideal.span {(p ^ n : ℤ_[p])} :
      Ideal (Fin d → ℤ_[p])) : Set (Fin d → ℤ_[p]))
    convert isOpen_set_pi Set.finite_univ (fun (_ : Fin d) _ ↦ h1)
    ext
    simp [Ideal.mem_pi]

/-- An element is in `Γ ^ (p ^ n)` if and only if it is `p ^ n`-th power of some element. -/
theorem mem_Γpow_iff (n : ℕ) (σ : H.Γ) : σ ∈ H.Γpow n ↔ ∃ τ, σ = τ ^ p ^ n := by
  change σ ∈ ((Ideal.pi fun _ ↦ Ideal.span {(p ^ n : ℤ_[p])} : Ideal (Fin d → ℤ_[p]))
    |>.toAddSubgroup.toSubgroup.comap H.continuousMulEquiv) ↔ _
  rw [Subgroup.mem_comap, MonoidHom.coe_coe]
  change _ ∈ Multiplicative.toAdd ⁻¹' _ ↔ _
  rw [Set.mem_preimage]
  change _ ∈ (_ : Ideal (Fin d → ℤ_[p])) ↔ _
  simp_rw [Ideal.mem_pi, Ideal.mem_span_singleton']
  refine ⟨fun h ↦ ?_, fun ⟨a, ha⟩ ↦ fun i ↦
    ⟨Multiplicative.toAdd (H.continuousMulEquiv a) i, ?_⟩⟩
  · choose a ha using h
    use H.continuousMulEquiv.symm (Multiplicative.ofAdd a)
    apply_fun _ using H.continuousMulEquiv.injective
    apply_fun _ using Multiplicative.toAdd.injective
    ext
    simp [ha, mul_comm (p ^ n : ℤ_[p])]
  · simp [ha, mul_comm (p ^ n : ℤ_[p])]

/-- `Γ ^ (p ^ 0) = Γ`. -/
@[simp]
theorem Γpow_zero : H.Γpow 0 = ⊤ := by
  ext
  simp [H.mem_Γpow_iff]

/-- `Γ ^ (p ^ n)` is a normal subgroup. -/
instance normal_Γpow (n : ℕ) : (H.Γpow n).Normal := inferInstance

-- TODO: move to suitable file
theorem _root_.PadicInt.surjective_toZModPow {p : ℕ} [Fact p.Prime] (n : ℕ) :
    Function.Surjective (PadicInt.toZModPow (p := p) n) := fun x ↦ ⟨x.val, by simp⟩

/-- `Γ ^ (p ^ n)` is of index `p ^ (n * d)`. -/
@[simp]
theorem index_Γpow (n : ℕ) : (H.Γpow n).index = p ^ (n * d) := by
  dsimp only [Γpow]
  rw [Subgroup.index_comap_of_surjective _ H.continuousMulEquiv.surjective,
    AddSubgroup.index_toSubgroup]
  have h1 : (Ideal.span {(p ^ n : ℤ_[p])}).toAddSubgroup.index = p ^ n := by
    rw [AddSubgroup.index_eq_card]
    change Nat.card (ℤ_[p] ⧸ Ideal.span {(p ^ n : ℤ_[p])}) = _
    have := Nat.card_congr
      (RingHom.quotientKerEquivOfSurjective (PadicInt.surjective_toZModPow (p := p) n)).toEquiv
    nth_rw 2 [Nat.card_eq_fintype_card] at this
    rwa [ZMod.card, PadicInt.ker_toZModPow] at this
  have h2 : (AddSubgroup.pi (Set.univ : Set (Fin d))
      fun _ ↦ (Ideal.span {(p ^ n : ℤ_[p])}).toAddSubgroup).index = p ^ (n * d) := by
    simp [h1, pow_mul]
  convert h2
  ext
  simp [Ideal.mem_pi, AddSubgroup.mem_pi]

/-- If `m ≤ n` then `Γ ^ (p ^ n) ≤ Γ ^ (p ^ m)`. -/
theorem antitone_Γpow : Antitone H.Γpow := antitone_nat_of_succ_le fun n x hx ↦ by
  rw [mem_Γpow_iff] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y ^ p, by rw [pow_succ', pow_mul]⟩

/-- If `m < n` then `Γ ^ (p ^ n) < Γ ^ (p ^ m)`. -/
theorem strictAnti_Γpow (hd : d ≠ 0) : StrictAnti H.Γpow :=
  H.antitone_Γpow.strictAnti_of_injective fun _ _ h ↦ by
    replace h := congr(($h).index)
    rw [index_Γpow, index_Γpow] at h
    simpa [hd] using Nat.pow_right_injective (Fact.out : p.Prime).two_le h

/-- The intermediate field `Kₙ` of `K∞ / K` fixed by `Γ ^ (p ^ n)`. -/
noncomputable def Kn (n : ℕ) : IntermediateField K Kinf :=
  IntermediateField.fixedField (H.Γpow n)

/-- `K₀ = K`. -/
@[simp]
theorem Kn_zero : H.Kn 0 = ⊥ := by
  simp [Kn, InfiniteGalois.fixedField_bot]

/-- `Kₙ / K` is Galois. -/
instance isGalois_Kn (n : ℕ) : IsGalois K (H.Kn n) :=
  IsGalois.of_fixedField_normal_subgroup (H.Γpow n).toSubgroup

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

/-- `Kₙ / K` is of degree `p ^ (n * d)`. -/
@[simp]
theorem finrank_Kn (n : ℕ) : Module.finrank K (H.Kn n) = p ^ (n * d) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, H.fixingSubgroup_Kn, H.index_Γpow]

/-- If `m ≤ n` then `Kₘ ≤ Kₙ`. -/
theorem monotone_Kn : Monotone H.Kn := monotone_nat_of_le_succ fun n ↦ by
  nth_rw 2 [Kn]
  rw [IntermediateField.le_iff_le, fixingSubgroup_Kn]
  exact H.antitone_Γpow (by simp)

/-- If `m < n` then `Kₘ < Kₙ`. -/
theorem strictMono_Kn (hd : d ≠ 0) : StrictMono H.Kn :=
  H.monotone_Kn.strictMono_of_injective fun _ _ h ↦ by
    replace h := congr(Module.finrank K ($h))
    rw [finrank_Kn, finrank_Kn] at h
    simpa [hd] using Nat.pow_right_injective (Fact.out : p.Prime).two_le h

/-- If the set `s` topologically generates `Γ`, then the set `s ^ (p ^ n)`
topologically generates `Γ ^ (p ^ n)`. -/
theorem closure_eq_Γpow_of_closure_eq
    {s : Set H.Γ} (h : closure (Subgroup.closure s : Set H.Γ) = ⊤) (n : ℕ) :
    closure (Subgroup.closure ((· ^ p ^ n) '' s) : Set H.Γ) = H.Γpow n := by
  let f : H.Γ →* H.Γ := {
    toFun := (· ^ p ^ n)
    map_one' := by simp
    map_mul' := fun _ _ ↦ by rw [mul_pow]
  }
  have h1 := closure_image_closure (s := (Subgroup.closure s : Set H.Γ))
    (show Continuous f from continuous_pow _)
  rw [h, Set.top_eq_univ, Set.image_univ] at h1
  have : Set.range f = H.Γpow n := by
    ext
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, Set.mem_range, SetLike.mem_coe, H.mem_Γpow_iff, f]
    tauto
  rw [this, (H.Γpow n).isClosed.closure_eq] at h1
  change closure (Subgroup.closure (f '' s) : Set H.Γ) = _
  rw [← MonoidHom.map_closure]
  exact h1.symm

/-- If `γ` is a topological generator of `Γ`, then `γ ^ (p ^ n)`
is a topological generator of `Γ ^ (p ^ n)`. -/
theorem closure_singleton_eq_Γpow_of_closure_singleton_eq
    {γ : H.Γ} (h : closure (Subgroup.closure {γ} : Set H.Γ) = ⊤) (n : ℕ) :
    closure (Subgroup.closure {γ ^ p ^ n} : Set H.Γ) = H.Γpow n := by
  simpa using H.closure_eq_Γpow_of_closure_eq h n

end IsMvZpExtension

/-- A Galois extension `K∞ / K` ia called a `ℤₚ`-extension, if its Galois group is
isomorphic to `ℤₚ` as a topological group. -/
def IsZpExtension [IsGalois K Kinf] := IsMvZpExtension p 1 K Kinf

theorem isZpExtension_iff [IsGalois K Kinf] :
    IsZpExtension p K Kinf ↔ Nonempty ((Kinf ≃ₐ[K] Kinf) ≃ₜ* Multiplicative ℤ_[p]) := by
  rw [IsZpExtension, isMvZpExtension_iff]
  let i1 : Multiplicative (Fin 1 → ℤ_[p]) ≃* Multiplicative ℤ_[p] :=
    (AddEquiv.piUnique fun _ ↦ ℤ_[p]).toMultiplicative
  let i2 : Multiplicative (Fin 1 → ℤ_[p]) ≃ₜ Multiplicative ℤ_[p] :=
    Homeomorph.piUnique fun _ ↦ ℤ_[p]
  let i : Multiplicative (Fin 1 → ℤ_[p]) ≃ₜ* Multiplicative ℤ_[p] :=
    { i1, i2 with }
  exact ⟨fun ⟨f⟩ ↦ ⟨f.trans i⟩, fun ⟨f⟩ ↦ ⟨f.trans i.symm⟩⟩

namespace IsZpExtension

variable [IsGalois K Kinf]

variable {p K Kinf}

variable (H : IsZpExtension p K Kinf)

theorem nonempty_continuousMulEquiv : Nonempty (H.Γ ≃ₜ* Multiplicative ℤ_[p]) := by
  rwa [isZpExtension_iff] at H

/-- A random isomorphism from `Γ` to `ℤₚ`. -/
noncomputable def continuousMulEquiv : H.Γ ≃ₜ* Multiplicative ℤ_[p] :=
  Classical.choice H.nonempty_continuousMulEquiv

/-- A random topological generator `γ` of `Γ`. -/
noncomputable def topologicalGenerator : H.Γ :=
  H.continuousMulEquiv.symm (Multiplicative.ofAdd 1)

/-- The `γ` is a topological generator of `Γ`. -/
theorem topologicalGenerator_spec :
    closure (Subgroup.closure {H.topologicalGenerator} : Set H.Γ) = ⊤ := by
  rw [topologicalGenerator, ← Set.image_singleton]
  have := MonoidHom.map_closure (G := Multiplicative ℤ_[p]) (N := H.Γ)
    H.continuousMulEquiv.symm {Multiplicative.ofAdd 1}
  rw [MonoidHom.coe_coe] at this
  rw [← this]
  change closure (H.continuousMulEquiv.symm.toHomeomorph '' _) = _
  rw [← Homeomorph.image_closure]
  convert Set.image_univ_of_surjective H.continuousMulEquiv.symm.surjective
  have := AddSubgroup.toSubgroup_closure {(1 : ℤ_[p])}
  rw [Set.preimage_equiv_eq_image_symm, Multiplicative.toAdd_symm_eq,
    Set.image_singleton] at this
  rw [← this]
  change closure (AddSubgroup.closure {(1 : ℤ_[p])} : Set ℤ_[p]) = _
  convert (PadicInt.denseRange_intCast (p := p)).closure_range
  ext
  simp [AddSubgroup.mem_closure_singleton]

/-- The `γ ^ (p ^ n)` is a topological generator of `Γ ^ (p ^ n)`. -/
theorem closure_topologicalGenerator_pow_eq (n : ℕ) :
    closure (Subgroup.closure {H.topologicalGenerator ^ p ^ n} : Set H.Γ) = H.Γpow n :=
  H.closure_singleton_eq_Γpow_of_closure_singleton_eq H.topologicalGenerator_spec n

/-- `Γ ^ (p ^ n)` is of index `p ^ n`. -/
theorem index_Γpow (n : ℕ) : (H.Γpow n).index = p ^ n := by
  simp

/-- `Kₙ / K` is of degree `p ^ n`. -/
theorem finrank_Kn (n : ℕ) : Module.finrank K (H.Kn n) = p ^ n := by
  simp

end IsZpExtension
