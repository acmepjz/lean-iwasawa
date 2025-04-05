import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.Padics.ProperSpace

/-!

# `ℤₚ`-extension of fields

-/

universe u v

variable (p : ℕ) [Fact p.Prime]
variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

/-- A Galois extension `K / k` ia called a `ℤₚ`-extension, if its Galois group is
isomorphic to `ℤₚ` as a topological group. -/
@[mk_iff]
structure IsZpExtension [IsGalois k K] : Prop where
  nonempty_continuousMulEquiv : Nonempty ((K ≃ₐ[k] K) ≃ₜ* Multiplicative ℤ_[p])

variable [IsGalois k K]

namespace IsZpExtension

variable {p k K}

set_option linter.unusedVariables false in
/-- The Galois group `Γ := Gal(K / k)` of a `ℤₚ`-extension `K / k`. -/
abbrev Γ (H : IsZpExtension p k K) := K ≃ₐ[k] K

variable (H : IsZpExtension p k K)

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

#check PadicInt.denseRange_intCast

-- TODO: move to suitable file
theorem _root_.PadicInt.ideal_isOpen_of_ne_bot {p : ℕ} [Fact p.Prime]
    {s : Ideal ℤ_[p]} (hs : s ≠ ⊥) : IsOpen (s : Set ℤ_[p]) := by
  obtain ⟨n, rfl⟩ := PadicInt.ideal_eq_span_pow_p hs
  have : (p ^ (-n : ℤ) : ℝ) ≠ 0 := by simp [show p ≠ 0 from NeZero.out]
  convert IsUltrametricDist.isOpen_closedBall (0 : ℤ_[p]) this
  ext
  rw [SetLike.mem_coe, Metric.mem_closedBall, dist_zero_right,
    PadicInt.norm_le_pow_iff_mem_span_pow]

-- TODO: move to suitable file
theorem _root_.PadicInt.ideal_isOpen_iff {p : ℕ} [Fact p.Prime]
    {s : Ideal ℤ_[p]} : IsOpen (s : Set ℤ_[p]) ↔ s ≠ ⊥ := by
  refine ⟨?_, PadicInt.ideal_isOpen_of_ne_bot⟩
  rintro h rfl
  rw [Submodule.bot_coe, ← discreteTopology_iff_isOpen_singleton_zero] at h
  have : Finite ℤ_[p] := finite_of_compact_of_discrete
  have : Infinite ℤ_[p] := .of_injective _ CharZero.cast_injective
  exact not_finite ℤ_[p]

/-- The open subgroup `Γ ^ (p ^ n)` of `Γ`. -/
noncomputable def Γpow (n : ℕ) : OpenSubgroup H.Γ where
  toSubgroup := (Ideal.span {(p ^ n : ℤ_[p])}).toAddSubgroup.toSubgroup.comap
    H.continuousMulEquiv
  isOpen' := by
    refine IsOpen.preimage H.continuousMulEquiv.continuous ?_
    change IsOpen (Ideal.span {(p ^ n : ℤ_[p])} : Set ℤ_[p])
    apply PadicInt.ideal_isOpen_of_ne_bot
    simp [show p ≠ 0 from NeZero.out]

/-- An element is in `Γ ^ (p ^ n)` if and only if it is `p ^ n`-th power of some element. -/
theorem mem_Γpow_iff (n : ℕ) (σ : H.Γ) : σ ∈ H.Γpow n ↔ ∃ τ, σ = τ ^ p ^ n := by
  change σ ∈ (Ideal.span {(p ^ n : ℤ_[p])}).toAddSubgroup.toSubgroup.comap
    H.continuousMulEquiv ↔ _
  rw [Subgroup.mem_comap, MonoidHom.coe_coe]
  change _ ∈ Multiplicative.toAdd ⁻¹' _ ↔ _
  rw [Set.mem_preimage]
  change _ ∈ (_ : Ideal ℤ_[p]) ↔ _
  rw [Ideal.mem_span_singleton']
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨H.continuousMulEquiv.symm (Multiplicative.ofAdd a), ?_⟩,
    fun ⟨a, ha⟩ ↦ ⟨Multiplicative.toAdd (H.continuousMulEquiv a), ?_⟩⟩
  · apply_fun _ using H.continuousMulEquiv.injective
    apply_fun _ using Multiplicative.toAdd.injective
    simp [mul_comm _ a, ha]
  · simp [ha, mul_comm (Multiplicative.toAdd _)]

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

/-- `Γ ^ (p ^ n)` is of index `p ^ n`. -/
@[simp]
theorem index_Γpow (n : ℕ) : (H.Γpow n).index = p ^ n := by
  dsimp only [Γpow]
  rw [Subgroup.index_comap_of_surjective _ H.continuousMulEquiv.surjective,
    AddSubgroup.index_toSubgroup, AddSubgroup.index_eq_card]
  change Nat.card (ℤ_[p] ⧸ Ideal.span {(p ^ n : ℤ_[p])}) = _
  have := Nat.card_congr
    (RingHom.quotientKerEquivOfSurjective (PadicInt.surjective_toZModPow (p := p) n)).toEquiv
  nth_rw 2 [Nat.card_eq_fintype_card] at this
  rwa [ZMod.card, PadicInt.ker_toZModPow] at this

/-- If `m < n` then `Γ ^ (p ^ n) < Γ ^ (p ^ m)`. -/
theorem strictAnti_Γpow : StrictAnti H.Γpow := strictAnti_nat_of_succ_lt fun n ↦ by
  refine lt_of_le_of_ne (fun x hx ↦ ?_) fun h ↦ ?_
  · rw [mem_Γpow_iff] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y ^ p, by rw [pow_succ', pow_mul]⟩
  · replace h := congr(($h).index)
    rw [index_Γpow, index_Γpow] at h
    simpa using Nat.pow_right_injective (Fact.out : p.Prime).two_le h

/-- The `γ ^ (p ^ n)` is a topological generator of `Γ ^ (p ^ n)`. -/
@[simp]
theorem closure_γ_pow_eq (n : ℕ) :
    closure (Subgroup.closure {H.γ ^ p ^ n} : Set H.Γ) = H.Γpow n := by
  sorry

/-- The intermediate field `kₙ` of `K / k` fixed by `Γ ^ (p ^ n)`. -/
noncomputable def kn (n : ℕ) : IntermediateField k K :=
  IntermediateField.fixedField (H.Γpow n)

/-- `k₀ = k`. -/
@[simp]
theorem kn_zero : H.kn 0 = ⊥ := by
  simp [kn, InfiniteGalois.fixedField_bot]

/-- `kₙ / k` is Galois. -/
instance isGalois_kn (n : ℕ) : IsGalois k (H.kn n) :=
  IsGalois.of_fixedField_normal_subgroup (H.Γpow n).toSubgroup

/-- The fixing subgroup of `kₙ` is `Γ ^ (p ^ n)`. -/
@[simp]
theorem fixingSubgroup_kn (n : ℕ) : (H.kn n).fixingSubgroup = H.Γpow n :=
  let G : ClosedSubgroup H.Γ := {
    toSubgroup := (H.Γpow n).toSubgroup
    isClosed' := (H.Γpow n).isClosed
  }
  InfiniteGalois.fixingSubgroup_fixedField G

/-- `kₙ / k` is a finite extension. -/
instance finiteDimensional_kn (n : ℕ) : FiniteDimensional k (H.kn n) := by
  rw [← InfiniteGalois.isOpen_iff_finite, fixingSubgroup_kn]
  exact (H.Γpow n).isOpen

-- TODO: move to suitable file
theorem _root_.IntermediateField.map_fixingSubgroup
    {k E : Type*} (K : Type*)
    [Field k] [Field E] [Field K] [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K]
    [Normal k E] (L : IntermediateField k E) :
    (L.map (IsScalarTower.toAlgHom k E K)).fixingSubgroup =
      L.fixingSubgroup.comap (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E) := by
  ext f
  simp only [Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro h x hx
    change f.restrictNormal E x = x
    apply_fun _ using (algebraMap E K).injective
    rw [AlgEquiv.restrictNormal_commutes]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    replace h := congr(algebraMap E K $(show f.restrictNormal E x = x from h x hx))
    rwa [AlgEquiv.restrictNormal_commutes] at h

-- TODO: move to suitable file
theorem _root_.IntermediateField.map_fixingSubgroup_index
    {k E : Type*} (K : Type*)
    [Field k] [Field E] [Field K] [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K]
    [Normal k E] [Normal k K] (L : IntermediateField k E) :
    (L.map (IsScalarTower.toAlgHom k E K)).fixingSubgroup.index = L.fixingSubgroup.index := by
  rw [L.map_fixingSubgroup K, L.fixingSubgroup.index_comap_of_surjective
    (AlgEquiv.restrictNormalHom_surjective _)]

-- TODO: move to suitable file
theorem _root_.IntermediateField.finrank_eq_fixingSubgroup_index
    {k K : Type*} [Field k] [Field K] [Algebra k K] (L : IntermediateField k K) [IsGalois k K] :
    Module.finrank k L = L.fixingSubgroup.index := by
  wlog hnfd : FiniteDimensional k L generalizing L
  · rw [Module.finrank_of_infinite_dimensional hnfd]
    by_contra! h
    replace h : L.fixingSubgroup.FiniteIndex := ⟨h.symm⟩
    obtain ⟨L', hfd, hL'⟩ :=
      IntermediateField.exists_lt_finrank_of_infinite_dimensional hnfd L.fixingSubgroup.index
    let i := (IntermediateField.liftAlgEquiv L').toLinearEquiv
    replace hfd := i.finiteDimensional
    rw [i.finrank_eq, this _ hfd] at hL'
    exact (Subgroup.index_antitone <| IntermediateField.fixingSubgroup.antimono <|
      IntermediateField.lift_le L').not_lt hL'
  let E := IntermediateField.normalClosure k L K
  have hle : L ≤ E := by
    simpa only [IntermediateField.fieldRange_val] using L.val.fieldRange_le_normalClosure
  let L' := IntermediateField.restrict hle
  have h := Module.finrank_mul_finrank k ↥L' ↥E
  classical
  rw [← IsGalois.card_fixingSubgroup_eq_finrank L', ← IsGalois.card_aut_eq_finrank k E] at h
  nth_rw 2 [Fintype.card_eq_nat_card] at h
  rw [← L'.fixingSubgroup.index_mul_card, Nat.card_eq_fintype_card,
    Nat.mul_left_inj Fintype.card_ne_zero] at h
  rw [(IntermediateField.restrict_algEquiv hle).toLinearEquiv.finrank_eq, h,
    ← L'.map_fixingSubgroup_index K]
  congr 2
  exact IntermediateField.lift_restrict hle

/-- `kₙ / k` is of degree `p ^ n`. -/
@[simp]
theorem finrank_kn (n : ℕ) : Module.finrank k (H.kn n) = p ^ n := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, H.fixingSubgroup_kn, H.index_Γpow]

/-- If `m < n` then `kₘ < kₙ`. -/
theorem strictMono_kn : StrictMono H.kn := strictMono_nat_of_lt_succ fun n ↦ by
  refine lt_of_le_of_ne ?_ fun h ↦ ?_
  · nth_rw 2 [kn]
    rw [IntermediateField.le_iff_le, fixingSubgroup_kn]
    exact H.strictAnti_Γpow.antitone (by simp)
  · replace h := congr(Module.finrank k ($h))
    rw [finrank_kn, finrank_kn] at h
    simpa using Nat.pow_right_injective (Fact.out : p.Prime).two_le h

end IsZpExtension
