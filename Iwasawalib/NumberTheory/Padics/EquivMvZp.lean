/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Iwasawalib.NumberTheory.Padics.HasBasis
import Iwasawalib.Topology.Algebra.OpenSubgroup

/-!

# Assertion that a (multiplicative) topological group is isomorphic to `ℤₚᵈ`

-/

theorem Equiv.arrowCongr_eq_piCongrLeft {M N P : Type*} (f : M ≃ N) :
    f.arrowCongr (.refl P) = f.piCongrLeft fun _ ↦ P := by
  ext g n
  simp [Equiv.piCongrLeft_apply_eq_cast]

variable (G : Type*) [Group G] [TopologicalSpace G] (p : ℕ) [Fact p.Prime] (d : ℕ) (ι : Type*)

/-- An `EquivMvZp G p ι` is just an isomorphism of `G` and `Multiplicative (ι → ℤ_[p])`
as topological groups. -/
structure EquivMvZp where
  continuousMulEquiv' : G ≃ₜ* Multiplicative (ι → ℤ_[p])

namespace EquivMvZp

variable {G p d ι}

/-- Transfer `EquivMvZp` along isomorphisms. -/
def congr (H : EquivMvZp G p ι) {G' : Type*} [Group G'] [TopologicalSpace G'] (f : G ≃ₜ* G')
    {ι' : Type*} (e : ι ≃ ι') : EquivMvZp G' p ι' :=
  letI i1 := (AddEquiv.arrowCongr e (AddEquiv.refl ℤ_[p])).toMultiplicative
  letI i : Multiplicative (ι → ℤ_[p]) ≃ₜ* Multiplicative (ι' → ℤ_[p]) := {
    i1 with
    continuous_toFun := by
      dsimp [i1, AddEquiv.toMultiplicative]
      refine Continuous.comp continuous_ofAdd (Continuous.comp ?_ continuous_toAdd)
      change Continuous (e.arrowCongr (.refl _))
      rw [Equiv.arrowCongr_eq_piCongrLeft]
      exact (Homeomorph.piCongrLeft (Y := fun _ ↦ ℤ_[p]) e).continuous
    continuous_invFun := by
      dsimp [i1, AddEquiv.toMultiplicative]
      refine Continuous.comp continuous_ofAdd (Continuous.comp ?_ continuous_toAdd)
      change Continuous (e.symm.arrowCongr (.refl _))
      rw [Equiv.arrowCongr_eq_piCongrLeft]
      exact (Homeomorph.piCongrLeft (Y := fun _ ↦ ℤ_[p]) e.symm).continuous
  }
  ⟨f.symm.trans (H.continuousMulEquiv'.trans i)⟩

set_option linter.unusedVariables false in
/-- The `EquivMvZp.Γ` is just the group `G` itself. -/
abbrev Γ (H : EquivMvZp G p ι) := G

variable (H : EquivMvZp G p ι)
include H

section General

/-- The isomorphism from `Γ` to `ℤₚᵈ`. -/
def continuousMulEquiv : H.Γ ≃ₜ* Multiplicative (ι → ℤ_[p]) := H.continuousMulEquiv'

/-- The `Γ` is commutative. -/
instance isMulCommutative : IsMulCommutative H.Γ :=
  ⟨⟨fun a b ↦ by apply H.continuousMulEquiv.injective; simp_rw [map_mul, mul_comm]⟩⟩

/-- The (normal) subgroup `Γ ^ (p ^ n)` of `Γ`.

This is only used internally, as later we only considered the case that `ι` is finite,
in which case `Γ ^ (p ^ n)` is an open normal subgroup. -/
noncomputable def Γpow' (n : ℕ) : Subgroup H.Γ :=
  (Ideal.pi fun _ ↦ Ideal.span {(p ^ n : ℤ_[p])} : Ideal (ι → ℤ_[p]))
    |>.toAddSubgroup.toSubgroup.comap H.continuousMulEquiv

/-- An element is in `Γ ^ (p ^ n)` if and only if it is `p ^ n`-th power of some element. -/
theorem mem_Γpow'_iff (n : ℕ) (σ : H.Γ) : σ ∈ H.Γpow' n ↔ ∃ τ, σ = τ ^ p ^ n := by
  rw [Γpow', Subgroup.mem_comap, MonoidHom.coe_coe]
  change _ ∈ Multiplicative.toAdd ⁻¹' _ ↔ _
  rw [Set.mem_preimage]
  change _ ∈ (_ : Ideal (ι → ℤ_[p])) ↔ _
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
theorem Γpow'_zero : H.Γpow' 0 = ⊤ := by
  ext
  simp [H.mem_Γpow'_iff]

/-- If `m ≤ n` then `Γ ^ (p ^ n) ≤ Γ ^ (p ^ m)`. -/
theorem antitone_Γpow' : Antitone H.Γpow' := antitone_nat_of_succ_le fun n x hx ↦ by
  rw [mem_Γpow'_iff] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y ^ p, by rw [pow_succ', pow_mul]⟩

/-- If `m < n` then `Γ ^ (p ^ n) < Γ ^ (p ^ m)`. -/
theorem strictAnti_Γpow' [Nonempty ι] : StrictAnti H.Γpow' := by
  refine H.antitone_Γpow'.strictAnti_of_injective fun n n' h ↦ ?_
  by_contra! h'
  wlog h'' : n < n' generalizing n n'
  · exact this n' n h.symm h'.symm (h'.lt_or_gt.resolve_left h'')
  simp_rw [Γpow'] at h
  replace h := congr(AddSubgroup.toSubgroup.symm <|
    ($h).map (MonoidHomClass.toMonoidHom H.continuousMulEquiv))
  repeat rw [Subgroup.map_comap_eq_self_of_surjective H.continuousMulEquiv.surjective] at h
  simp only [OrderIso.symm_apply_apply, Submodule.toAddSubgroup_inj] at h
  obtain ⟨i⟩ := ‹Nonempty ι›
  suffices True = False by simp_rw [← this]
  classical
  convert congr(Pi.single i (p ^ n : ℤ_[p]) ∈ $h) using 1
  · simp only [Ideal.mem_pi, true_iff, Pi.single_apply]
    intro j
    split_ifs
    exacts [Ideal.mem_span_singleton_self _, Ideal.zero_mem _]
  · simp only [Ideal.mem_pi, false_iff, not_forall]
    use i
    simp only [Pi.single_eq_same, Ideal.mem_span_singleton]
    rw [pow_dvd_pow_iff PadicInt.irreducible_p.ne_zero PadicInt.irreducible_p.not_isUnit]
    exact h''.not_ge

end General

section Finite

variable [Finite ι]

/-- The `Γ ^ (p ^ n)` is open. -/
theorem isOpen_Γpow' (n : ℕ) : IsOpen (H.Γpow' n : Set H.Γ) :=
  (PadicInt.isOpen_pi_span_p_pow ι p n).preimage H.continuousMulEquiv.continuous

/-- The open normal subgroup `Γ ^ (p ^ n)` of `Γ`. -/
noncomputable def Γpow (n : ℕ) : OpenNormalSubgroup H.Γ where
  toSubgroup := H.Γpow' n
  isOpen' := H.isOpen_Γpow' n

theorem toSubgroup_Γpow (n : ℕ) : (H.Γpow n : Subgroup H.Γ) = H.Γpow' n := rfl

/-- An element is in `Γ ^ (p ^ n)` if and only if it is `p ^ n`-th power of some element. -/
theorem mem_Γpow_iff (n : ℕ) (σ : H.Γ) : σ ∈ H.Γpow n ↔ ∃ τ, σ = τ ^ p ^ n :=
  H.mem_Γpow'_iff n σ

/-- `Γ ^ (p ^ 0) = Γ`. -/
@[simp]
theorem Γpow_zero : H.Γpow 0 = ⊤ := by
  ext
  simp [H.mem_Γpow_iff]

/-- `Γ ^ (p ^ n)` is of index `p ^ (n * #ι)`. -/
@[simp]
theorem index_Γpow (n : ℕ) : (H.Γpow n).index = p ^ (n * Nat.card ι) := by
  rw [toSubgroup_Γpow, Γpow', Subgroup.index_comap_of_surjective _ H.continuousMulEquiv.surjective,
    AddSubgroup.index_toSubgroup, PadicInt.index_pi_span_p_pow]

/-- If `m ≤ n` then `Γ ^ (p ^ n) ≤ Γ ^ (p ^ m)`. -/
theorem antitone_Γpow : Antitone H.Γpow := fun _ _ h ↦ H.antitone_Γpow' h

/-- If `m < n` then `Γ ^ (p ^ n) < Γ ^ (p ^ m)`. -/
theorem strictAnti_Γpow [Nonempty ι] : StrictAnti H.Γpow := fun _ _ h ↦ H.strictAnti_Γpow' h

/-- If the set `s` topologically generates `Γ`, then the set `s ^ (p ^ n)`
topologically generates `Γ ^ (p ^ n)`. -/
theorem closure_eq_Γpow_of_closure_eq
    {s : Set H.Γ} (h : closure (Subgroup.closure s : Set H.Γ) = Set.univ) (n : ℕ) :
    closure (Subgroup.closure ((· ^ p ^ n) '' s) : Set H.Γ) = H.Γpow n := by
  let f : H.Γ →* H.Γ := {
    toFun := (· ^ p ^ n)
    map_one' := by simp
    map_mul' := fun _ _ ↦ by rw [mul_pow]
  }
  have := H.continuousMulEquiv.isHomeomorph.isInducing.continuousMul H.continuousMulEquiv
  have h1 := closure_image_closure (s := (Subgroup.closure s : Set H.Γ))
    (show Continuous f from continuous_pow _)
  rw [h, Set.image_univ] at h1
  have h2 : Set.range f = H.Γpow n := by
    ext
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, Set.mem_range, SetLike.mem_coe, H.mem_Γpow_iff, f]
    tauto
  have h3 := (H.Γpow n).coe_toOpenSubgroup ▸ (H.Γpow n).isClosed.closure_eq
  rw [h2, h3] at h1
  change closure (Subgroup.closure (f '' s) : Set H.Γ) = _
  rw [← MonoidHom.map_closure]
  exact h1.symm

/-- If `γ` is a topological generator of `Γ`, then `γ ^ (p ^ n)`
is a topological generator of `Γ ^ (p ^ n)`. -/
theorem closure_singleton_eq_Γpow_of_closure_singleton_eq
    {γ : H.Γ} (h : closure (Subgroup.closure {γ} : Set H.Γ) = Set.univ) (n : ℕ) :
    closure (Subgroup.closure {γ ^ p ^ n} : Set H.Γ) = H.Γpow n := by
  simpa using H.closure_eq_Γpow_of_closure_eq h n

/-- `Γ ^ (p ^ n)` form a neighborhood basis of `1` in `Γ`. -/
theorem nhds_one_hasAntitoneBasis : (nhds (1 : H.Γ)).HasAntitoneBasis (fun n ↦ H.Γpow n) := by
  have h1 := PadicInt.nhds_zero_hasAntitoneBasis_pi_span_p_pow ι p
  change (nhds (1 : Multiplicative (ι → ℤ_[p]))).HasAntitoneBasis
    fun n ↦ ((Ideal.pi fun _ ↦ Ideal.span {(p ^ n : ℤ_[p])} : Ideal (ι → ℤ_[p])))
      |>.toAddSubgroup.toSubgroup at h1
  replace h1 := h1.comap H.continuousMulEquiv
  have h2 : _ = Filter.comap H.continuousMulEquiv (nhds (H.continuousMulEquiv 1)) :=
    H.continuousMulEquiv.nhds_eq_comap 1
  rw [map_one] at h2
  rwa [← h2] at h1

/-- If `O` is an open subgroup of `Γ`, then it contains `Γ ^ (p ^ n)` for some `n`. -/
theorem Γpow_le_of_isOpen (O : Subgroup H.Γ) (h : IsOpen (O : Set H.Γ)) :
    ∃ n, H.Γpow n ≤ O :=
  H.nhds_one_hasAntitoneBasis.mem_iff.1 <| h.mem_nhds_iff.2 (one_mem _)

end Finite

section Unique

variable [Unique ι]

/-- An isomorphism from `Γ` to `ℤₚ` gives an `EquivMvZp G p ι` when `ι` consists of
exactly one element. -/
def ofContinuousMulEquiv₁ (e : G ≃ₜ* Multiplicative ℤ_[p]) : EquivMvZp G p ι :=
  letI i1 : Multiplicative (ι → ℤ_[p]) ≃* Multiplicative ℤ_[p] :=
    (AddEquiv.piUnique fun _ ↦ ℤ_[p]).toMultiplicative
  letI i2 : Multiplicative (ι → ℤ_[p]) ≃ₜ Multiplicative ℤ_[p] :=
    Homeomorph.piUnique fun _ ↦ ℤ_[p]
  letI i : Multiplicative (ι → ℤ_[p]) ≃ₜ* Multiplicative ℤ_[p] :=
    { i1, i2 with }
  ⟨e.trans i.symm⟩

/-- The isomorphism from `Γ` to `ℤₚ`. -/
def continuousMulEquiv₁ : H.Γ ≃ₜ* Multiplicative ℤ_[p] :=
  letI i1 : Multiplicative (ι → ℤ_[p]) ≃* Multiplicative ℤ_[p] :=
    (AddEquiv.piUnique fun _ ↦ ℤ_[p]).toMultiplicative
  letI i2 : Multiplicative (ι → ℤ_[p]) ≃ₜ Multiplicative ℤ_[p] :=
    Homeomorph.piUnique fun _ ↦ ℤ_[p]
  H.continuousMulEquiv.trans { i1, i2 with }

/-- A random topological generator `γ` of `Γ`. -/
noncomputable def topologicalGenerator : H.Γ :=
  H.continuousMulEquiv₁.symm (Multiplicative.ofAdd 1)

/-- The `γ` is a topological generator of `Γ`. -/
theorem topologicalGenerator_spec :
    closure (Subgroup.closure {H.topologicalGenerator} : Set H.Γ) = ⊤ := by
  rw [topologicalGenerator, ← Set.image_singleton]
  have := MonoidHom.map_closure (G := Multiplicative ℤ_[p]) (N := H.Γ)
    H.continuousMulEquiv₁.symm {Multiplicative.ofAdd 1}
  rw [MonoidHom.coe_coe] at this
  rw [← this]
  change closure (H.continuousMulEquiv₁.symm.toHomeomorph '' _) = _
  rw [← Homeomorph.image_closure]
  convert Set.image_univ_of_surjective H.continuousMulEquiv₁.symm.surjective
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
theorem index_Γpow₁ (n : ℕ) : (H.Γpow n).index = p ^ n := by
  simp

/-- If `O` is an open subgroup of `Γ`, then it is equal to `Γ ^ (p ^ n)` for some `n`. -/
theorem eq_Γpow_of_isOpen (O : Subgroup H.Γ) (h : IsOpen (O : Set H.Γ)) :
    ∃ n, O = H.Γpow n := by
  let O' : AddSubgroup ℤ_[p] := (O.comap H.continuousMulEquiv₁.symm).toAddSubgroup'
  obtain ⟨n, hn⟩ := PadicInt.exists_eq_span_p_pow_of_isOpen p O'
    (h.preimage H.continuousMulEquiv₁.symm.continuous)
  have hO : O = (Ideal.span {(p ^ n : ℤ_[p])}).toAddSubgroup.toSubgroup.comap
      H.continuousMulEquiv₁ := by
    simp_rw [← hn, O', OrderIso.apply_symm_apply, Subgroup.comap_comap]
    convert O.comap_id.symm
    ext; simp
  have hmem (σ : H.Γ) : σ ∈ O ↔ ∃ τ, σ = τ ^ p ^ n := by
    rw [hO, Subgroup.mem_comap, MonoidHom.coe_coe]
    change _ ∈ Multiplicative.toAdd ⁻¹' _ ↔ _
    rw [Set.mem_preimage]
    change _ ∈ Ideal.span {(p ^ n : ℤ_[p])} ↔ _
    rw [Ideal.mem_span_singleton']
    refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ⟨Multiplicative.toAdd (H.continuousMulEquiv₁ a), ?_⟩⟩
    · use H.continuousMulEquiv₁.symm (Multiplicative.ofAdd a)
      apply_fun _ using H.continuousMulEquiv₁.injective
      apply_fun _ using Multiplicative.toAdd.injective
      simp [ha, mul_comm (p ^ n : ℤ_[p])]
    · simp [ha, mul_comm (p ^ n : ℤ_[p])]
  use n
  ext
  simp [hmem, H.mem_Γpow_iff]

/-- If `O` is a closed subgroup of `Γ`, then it is equal to `0` or `Γ ^ (p ^ n)` for some `n`. -/
theorem eq_bot_or_Γpow_of_isClosed (O : Subgroup H.Γ) (h : IsClosed (O : Set H.Γ)) :
    O = ⊥ ∨ ∃ n, O = H.Γpow n := by
  refine (eq_or_ne O ⊥).imp (fun hbot ↦ by simp [hbot]) fun hbot ↦ ?_
  let O' : AddSubgroup ℤ_[p] := (O.comap H.continuousMulEquiv₁.symm).toAddSubgroup'
  obtain ⟨I, hI⟩ := PadicInt.exists_eq_ideal_of_addSubgroup_of_isClosed p O'
    (h.preimage H.continuousMulEquiv₁.symm.continuous)
  have hO : O = I.toAddSubgroup.toSubgroup.comap H.continuousMulEquiv₁ := by
    simp_rw [← hI, O', OrderIso.apply_symm_apply, Subgroup.comap_comap]
    convert O.comap_id.symm
    ext; simp
  rcases eq_or_ne I ⊥ with rfl | hbot'
  · simp only [Submodule.bot_toAddSubgroup, map_eq_bot_iff, O'] at hI
    replace hI : (O.map H.continuousMulEquiv₁ : Subgroup (Multiplicative ℤ_[p])) = ⊥ := by
      convert hI using 1
      exact O.map_equiv_eq_comap_symm H.continuousMulEquiv₁.toMulEquiv
    rw [O.map_eq_bot_iff_of_injective H.continuousMulEquiv₁.injective] at hI
    contradiction
  refine H.eq_Γpow_of_isOpen O ?_
  rw [hO]
  exact (IsDiscreteValuationRing.isOpen_iff.2 hbot').preimage H.continuousMulEquiv₁.continuous

end Unique

end EquivMvZp

/-- `IsEquivMvZp G p d` means there exists an isomorphism of `G` and `ℤₚᵈ`. -/
def IsEquivMvZp : Prop := Nonempty (EquivMvZp G p (Fin d))

variable {G p ι} in
theorem EquivMvZp.isEquivMvZp (H : EquivMvZp G p ι) [Finite ι] : IsEquivMvZp G p (Nat.card ι) :=
  ⟨H.congr (ContinuousMulEquiv.refl G) (Finite.equivFin ι)⟩

namespace IsEquivMvZp

variable {G p d ι}

section General

variable (H : IsEquivMvZp G p d)
include H

/-- Transfer `IsEquivMvZp` along isomorphisms. -/
theorem congr {G' : Type*} [Group G'] [TopologicalSpace G'] (f : G ≃ₜ* G') :
    IsEquivMvZp G' p d :=
  ⟨H.some.congr f (Equiv.refl _)⟩

/-- The `IsEquivMvZp.Γ` is just the group `G` itself. -/
abbrev Γ := H.some.Γ

/-- A random isomorphism from `Γ` to `ℤₚᵈ`. -/
noncomputable def continuousMulEquiv : H.Γ ≃ₜ* Multiplicative (Fin d → ℤ_[p]) :=
  H.some.continuousMulEquiv'

/-- The `Γ` is commutative. -/
instance isMulCommutative : IsMulCommutative H.Γ := inferInstance

/-- The open normal subgroup `Γ ^ (p ^ n)` of `Γ`. -/
noncomputable def Γpow (n : ℕ) : OpenNormalSubgroup H.Γ := H.some.Γpow n

/-- An element is in `Γ ^ (p ^ n)` if and only if it is `p ^ n`-th power of some element. -/
theorem mem_Γpow_iff (n : ℕ) (σ : H.Γ) : σ ∈ H.Γpow n ↔ ∃ τ, σ = τ ^ p ^ n :=
  H.some.mem_Γpow_iff n σ

/-- `Γ ^ (p ^ 0) = Γ`. -/
@[simp]
theorem Γpow_zero : H.Γpow 0 = ⊤ := H.some.Γpow_zero

/-- `Γ ^ (p ^ n)` is of index `p ^ (n * d)`. -/
@[simp]
theorem index_Γpow (n : ℕ) : (H.Γpow n).index = p ^ (n * d) := by
  convert H.some.index_Γpow n
  simp

/-- If `m ≤ n` then `Γ ^ (p ^ n) ≤ Γ ^ (p ^ m)`. -/
theorem antitone_Γpow : Antitone H.Γpow := H.some.antitone_Γpow

/-- If `m < n` then `Γ ^ (p ^ n) < Γ ^ (p ^ m)`. -/
theorem strictAnti_Γpow [NeZero d] : StrictAnti H.Γpow := H.some.strictAnti_Γpow

/-- If the set `s` topologically generates `Γ`, then the set `s ^ (p ^ n)`
topologically generates `Γ ^ (p ^ n)`. -/
theorem closure_eq_Γpow_of_closure_eq
    {s : Set H.Γ} (h : closure (Subgroup.closure s : Set H.Γ) = Set.univ) (n : ℕ) :
    closure (Subgroup.closure ((· ^ p ^ n) '' s) : Set H.Γ) = H.Γpow n :=
  H.some.closure_eq_Γpow_of_closure_eq h n

/-- If `γ` is a topological generator of `Γ`, then `γ ^ (p ^ n)`
is a topological generator of `Γ ^ (p ^ n)`. -/
theorem closure_singleton_eq_Γpow_of_closure_singleton_eq
    {γ : H.Γ} (h : closure (Subgroup.closure {γ} : Set H.Γ) = Set.univ) (n : ℕ) :
    closure (Subgroup.closure {γ ^ p ^ n} : Set H.Γ) = H.Γpow n :=
  H.some.closure_singleton_eq_Γpow_of_closure_singleton_eq h n

/-- `Γ ^ (p ^ n)` form a neighborhood basis of `1` in `Γ`. -/
theorem nhds_one_hasAntitoneBasis : (nhds (1 : H.Γ)).HasAntitoneBasis (fun n ↦ H.Γpow n) :=
  H.some.nhds_one_hasAntitoneBasis

/-- If `O` is an open subgroup of `Γ`, then it contains `Γ ^ (p ^ n)` for some `n`. -/
theorem Γpow_le_of_isOpen (O : Subgroup H.Γ) (h : IsOpen (O : Set H.Γ)) :
    ∃ n, H.Γpow n ≤ O :=
  H.some.Γpow_le_of_isOpen O h

end General

section Unique

theorem _root_.isEquivMvZp₁_iff : IsEquivMvZp G p 1 ↔ Nonempty (G ≃ₜ* Multiplicative ℤ_[p]) :=
  ⟨fun ⟨f⟩ ↦ ⟨f.continuousMulEquiv₁⟩, fun ⟨f⟩ ↦ ⟨.ofContinuousMulEquiv₁ f⟩⟩

variable (H : IsEquivMvZp G p 1)
include H

/-- A random isomorphism from `Γ` to `ℤₚ`. -/
noncomputable def continuousMulEquiv₁ : H.Γ ≃ₜ* Multiplicative ℤ_[p] :=
  H.some.continuousMulEquiv₁

/-- A random topological generator `γ` of `Γ`. -/
noncomputable def topologicalGenerator : H.Γ :=
  H.some.topologicalGenerator

/-- The `γ` is a topological generator of `Γ`. -/
theorem topologicalGenerator_spec :
    closure (Subgroup.closure {H.topologicalGenerator} : Set H.Γ) = ⊤ :=
  H.some.topologicalGenerator_spec

/-- The `γ ^ (p ^ n)` is a topological generator of `Γ ^ (p ^ n)`. -/
theorem closure_topologicalGenerator_pow_eq (n : ℕ) :
    closure (Subgroup.closure {H.topologicalGenerator ^ p ^ n} : Set H.Γ) = H.Γpow n :=
  H.some.closure_topologicalGenerator_pow_eq n

/-- `Γ ^ (p ^ n)` is of index `p ^ n`. -/
theorem index_Γpow₁ (n : ℕ) : (H.Γpow n).index = p ^ n := H.some.index_Γpow₁ n

/-- If `O` is an open subgroup of `Γ`, then it is equal to `Γ ^ (p ^ n)` for some `n`. -/
theorem eq_Γpow_of_isOpen (O : Subgroup H.Γ) (h : IsOpen (O : Set H.Γ)) :
    ∃ n, O = H.Γpow n :=
  H.some.eq_Γpow_of_isOpen O h

/-- If `O` is a closed subgroup of `Γ`, then it is equal to `0` or `Γ ^ (p ^ n)` for some `n`. -/
theorem eq_bot_or_Γpow_of_isClosed (O : Subgroup H.Γ) (h : IsClosed (O : Set H.Γ)) :
    O = ⊥ ∨ ∃ n, O = H.Γpow n :=
  H.some.eq_bot_or_Γpow_of_isClosed O h

end Unique

end IsEquivMvZp
