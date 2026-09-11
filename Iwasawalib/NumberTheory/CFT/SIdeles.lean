/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.AdeleFixedPoints
public import Iwasawalib.NumberTheory.CFT.SUnits

@[expose] public section

/-!
# The `S`-ideles of a number field

For a set `T` of finite places of a number field `L`, the group of `T`-ideles is
`𝕀_{L,T} = ∏_{w ∈ T} L_wˣ × ∏_{w ∉ T} O_wˣ`, viewed inside the idele group `𝕀_L`.
Equivalently, it is the set of ideles whose `w`-adic valuation is `1` at every finite place
`w ∉ T`; the archimedean components are unconstrained, which corresponds to the convention
that the archimedean places always belong to `S`.

## Main definitions

* `NumberField.FiniteAdeleRing.sIdeleSubgroup L T` : the `T`-ideles inside the finite ideles.
* `NumberField.IdeleGroup.sIdeleSubgroup L T` : the `T`-ideles inside `𝕀_L`.

## Main results

* `NumberField.FiniteAdeleRing.exists_mem_sIdeleSubgroup` : every finite idele is a `T`-idele
  for some *finite* `T`; this is the statement `𝕀_L = ⋃_T 𝕀_{L,T}`.
* `NumberField.IdeleGroup.iSup_sIdeleSubgroup` : `𝕀_L = ⋃_T 𝕀_{L,T}` as a supremum of
  subgroups.
* `NumberField.IdeleGroup.principalEmbedding_mem_sIdeleSubgroup_iff` and
  `NumberField.IdeleGroup.principalSubgroup_inf_sIdeleSubgroup` :
  **`L^× ∩ 𝕀_{L,S} = O_{L,S}^×`**, the identification of the principal `S`-ideles with the
  group of `S`-units.
* `NumberField.FiniteAdeleRing.smul_mem_sIdeleSubgroup` : `𝕀_{L,S}` is a `Gal(L/K)`-submodule
  of `𝕀_L` when `S` is a set of places of the base field `K`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter

namespace NumberField

/-! ## An auxiliary fact about linearly ordered groups with zero -/

theorem eq_one_of_mul_eq_one_of_le_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (hab : a * b = 1) (ha : a ≤ 1) (hb : b ≤ 1) : a = 1 := by
  refine le_antisymm ha ?_
  have h := mul_le_mul_left hb a
  rwa [one_mul, mul_comm b a, hab] at h

namespace FiniteAdeleRing

variable (L : Type*) [Field L] [NumberField L]

@[simp]
theorem one_apply' (w : HeightOneSpectrum (𝓞 L)) : (1 : FiniteAdeleRing (𝓞 L) L) w = 1 := rfl

@[simp]
theorem mul_apply' (x y : FiniteAdeleRing (𝓞 L) L) (w : HeightOneSpectrum (𝓞 L)) :
    (x * y) w = x w * y w := rfl

variable {L}

/-! ## The `T`-ideles inside the finite ideles -/

variable (L)

/-- The group of `T`-ideles inside the group of finite ideles of `L`: the finite ideles whose
component at `w` is a unit of the ring of integers of `L_w` for every `w ∉ T`. -/
def sIdeleSubgroup (T : Set (HeightOneSpectrum (𝓞 L))) :
    Subgroup (FiniteAdeleRing (𝓞 L) L)ˣ where
  carrier := {u | ∀ w ∉ T, Valued.v ((u : FiniteAdeleRing (𝓞 L) L) w) = 1}
  one_mem' w _ := by
    rw [Units.val_one, one_apply' L w]
    exact map_one _
  mul_mem' {u} {v} hu hv w hw := by
    rw [Units.val_mul, mul_apply', map_mul, hu w hw, hv w hw, one_mul]
  inv_mem' {u} hu w hw := by
    have h : ((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) *
        (u : FiniteAdeleRing (𝓞 L) L) = 1 := u.inv_mul
    have h' := congrArg (fun x : FiniteAdeleRing (𝓞 L) L ↦ Valued.v (x w)) h
    simp only [mul_apply', map_mul, hu w hw, mul_one, one_apply' L w, map_one] at h'
    exact h'

variable {L}

theorem mem_sIdeleSubgroup {T : Set (HeightOneSpectrum (𝓞 L))}
    {u : (FiniteAdeleRing (𝓞 L) L)ˣ} :
    u ∈ sIdeleSubgroup L T ↔
      ∀ w : HeightOneSpectrum (𝓞 L), w ∉ T → Valued.v ((u : FiniteAdeleRing (𝓞 L) L) w) = 1 :=
  Iff.rfl

theorem sIdeleSubgroup_mono {T T' : Set (HeightOneSpectrum (𝓞 L))} (h : T ⊆ T') :
    sIdeleSubgroup L T ≤ sIdeleSubgroup L T' :=
  fun _ hu w hw ↦ hu w fun hwT ↦ hw (h hwT)

@[simp]
theorem sIdeleSubgroup_univ : sIdeleSubgroup L Set.univ = ⊤ := by
  ext u
  exact ⟨fun _ ↦ trivial, fun _ w hw ↦ absurd (Set.mem_univ w) hw⟩

/-- The component of a finite idele at `w` is integral for all but finitely many `w`, and so is
the component of its inverse; where both are integral the valuation is exactly `1`. -/
theorem valued_eq_one_of_mem_integers {u : (FiniteAdeleRing (𝓞 L) L)ˣ}
    {w : HeightOneSpectrum (𝓞 L)}
    (h₁ : (u : FiniteAdeleRing (𝓞 L) L) w ∈ w.adicCompletionIntegers L)
    (h₂ : ((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w
      ∈ w.adicCompletionIntegers L) :
    Valued.v ((u : FiniteAdeleRing (𝓞 L) L) w) = 1 := by
  have h : (u : FiniteAdeleRing (𝓞 L) L) *
      ((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) = 1 := u.mul_inv
  have h' := congrArg (fun x : FiniteAdeleRing (𝓞 L) L ↦ Valued.v (x w)) h
  simp only [mul_apply', map_mul, one_apply' L w, map_one] at h'
  exact eq_one_of_mul_eq_one_of_le_one h' h₁ h₂

/-- **`𝕀_L = ⋃_T 𝕀_{L,T}`.**  Every finite idele is a `T`-idele for some finite set `T` of
finite places. -/
theorem exists_mem_sIdeleSubgroup (u : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    ∃ T : Set (HeightOneSpectrum (𝓞 L)), T.Finite ∧ u ∈ sIdeleSubgroup L T := by
  have h₁ : {w : HeightOneSpectrum (𝓞 L) |
      ¬ ((u : FiniteAdeleRing (𝓞 L) L) w ∈ w.adicCompletionIntegers L)}.Finite :=
    (u : FiniteAdeleRing (𝓞 L) L).2
  have h₂ : {w : HeightOneSpectrum (𝓞 L) |
      ¬ (((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w
        ∈ w.adicCompletionIntegers L)}.Finite :=
    ((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L).2
  refine ⟨_, h₁.union h₂, fun w hw ↦ ?_⟩
  rw [Set.mem_union, not_or, Set.notMem_ofPred_iff, not_not, Set.notMem_ofPred_iff, not_not] at hw
  exact valued_eq_one_of_mem_integers hw.1 hw.2

/-! ## Principal `T`-ideles and `T`-units -/

/-- **`L^× ∩ 𝕀_{L,T} = O_{L,T}^×`** at the level of finite ideles: a principal finite idele is a
`T`-idele exactly when the element is a `T`-unit. -/
theorem unitEmbedding_mem_sIdeleSubgroup_iff {T : Set (HeightOneSpectrum (𝓞 L))} (x : Lˣ) :
    FiniteAdeleRing.unitEmbedding (𝓞 L) L x ∈ sIdeleSubgroup L T ↔ x ∈ T.unit L := by
  constructor
  · intro hx w hw
    have := hx w hw
    rwa [show ((FiniteAdeleRing.unitEmbedding (𝓞 L) L x : (FiniteAdeleRing (𝓞 L) L)ˣ) :
        FiniteAdeleRing (𝓞 L) L) w = ((x : L) : w.adicCompletion L) from
      FiniteAdeleRing.algebraMap_apply (𝓞 L) L (x : L) w, valuedAdicCompletion_eq_valuation'] at this
  · intro hx w hw
    rw [show ((FiniteAdeleRing.unitEmbedding (𝓞 L) L x : (FiniteAdeleRing (𝓞 L) L)ˣ) :
        FiniteAdeleRing (𝓞 L) L) w = ((x : L) : w.adicCompletion L) from
      FiniteAdeleRing.algebraMap_apply (𝓞 L) L (x : L) w, valuedAdicCompletion_eq_valuation']
    exact hx w hw

/-! ## The Galois action on `T`-ideles -/

section Galois

variable {K : Type*} [Field K] [NumberField K] [Algebra K L]

omit [NumberField K] in
/-- The valuation of the `w`-component of `σ • a` is the valuation of the `σ⁻¹ • w`-component
of `a`. -/
theorem valued_smul_apply (σ : L ≃ₐ[K] L) (a : FiniteAdeleRing (𝓞 L) L)
    (w : HeightOneSpectrum (𝓞 L)) :
    Valued.v ((σ • a) w) = Valued.v (a (σ⁻¹ • w)) := by
  conv_lhs => rw [← smul_inv_smul σ w]
  rw [finiteAdele_smul_apply_smul σ a (σ⁻¹ • w)]
  exact valued_adicCompletionCongr (σ : L ≃+* L) _ _
    (valuation_smul_heightOneSpectrum σ (σ⁻¹ • w)) _

omit [NumberField K] in
/-- **`𝕀_{L,S}` is a `Gal(L/K)`-submodule of `𝕀_L`.**  For `S` a set of finite places of the
base field `K`, the group of `S`-ideles of `L` is stable under `Gal(L/K)`. -/
theorem smul_mem_sIdeleSubgroup (S : Set (HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L)
    {u : (FiniteAdeleRing (𝓞 L) L)ˣ} (hu : u ∈ sIdeleSubgroup L (placesOverSet K L S)) :
    σ • u ∈ sIdeleSubgroup L (placesOverSet K L S) := by
  intro w hw
  rw [finiteIdele_smul_coe, valued_smul_apply]
  exact hu _ fun h ↦ hw ((smul_mem_placesOverSet σ⁻¹).1 h)

omit [NumberField K] in
@[simp]
theorem smul_mem_sIdeleSubgroup_iff (S : Set (HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L)
    {u : (FiniteAdeleRing (𝓞 L) L)ˣ} :
    σ • u ∈ sIdeleSubgroup L (placesOverSet K L S) ↔
      u ∈ sIdeleSubgroup L (placesOverSet K L S) := by
  refine ⟨fun h ↦ ?_, smul_mem_sIdeleSubgroup S σ⟩
  have := smul_mem_sIdeleSubgroup S σ⁻¹ h
  rwa [inv_smul_smul] at this

end Galois

end FiniteAdeleRing

/-! ## The `S`-ideles inside the full idele group -/

namespace IdeleGroup

variable (L : Type*) [Field L] [NumberField L]

/-- The projection from the ideles of `L` to the finite ideles of `L`. -/
def finiteUnits : IdeleGroup (𝓞 L) L →* (FiniteAdeleRing (𝓞 L) L)ˣ :=
  Units.map ((RingHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).comp
    (AdeleRing.prodEquiv (𝓞 L) L).toRingHom).toMonoidHom

@[simp]
theorem coe_finiteUnits (u : IdeleGroup (𝓞 L) L) :
    ((finiteUnits L u : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L)
      = (u : AdeleRing (𝓞 L) L).2 := rfl

@[simp]
theorem finiteUnits_principalEmbedding (x : Lˣ) :
    finiteUnits L (IdeleGroup.principalEmbedding (𝓞 L) L x)
      = FiniteAdeleRing.unitEmbedding (𝓞 L) L x := rfl

/-- The group `𝕀_{L,T}` of `T`-ideles inside the idele group `𝕀_L`: the archimedean components
are unconstrained, and the component at a finite place `w ∉ T` is required to be a unit of the
ring of integers of `L_w`. -/
def sIdeleSubgroup (T : Set (HeightOneSpectrum (𝓞 L))) : Subgroup (IdeleGroup (𝓞 L) L) :=
  (FiniteAdeleRing.sIdeleSubgroup L T).comap (finiteUnits L)

variable {L}

theorem mem_sIdeleSubgroup {T : Set (HeightOneSpectrum (𝓞 L))} {u : IdeleGroup (𝓞 L) L} :
    u ∈ sIdeleSubgroup L T ↔
      ∀ w : HeightOneSpectrum (𝓞 L), w ∉ T → Valued.v ((u : AdeleRing (𝓞 L) L).2 w) = 1 :=
  Iff.rfl

theorem sIdeleSubgroup_mono {T T' : Set (HeightOneSpectrum (𝓞 L))} (h : T ⊆ T') :
    sIdeleSubgroup L T ≤ sIdeleSubgroup L T' :=
  Subgroup.comap_mono (FiniteAdeleRing.sIdeleSubgroup_mono h)

@[simp]
theorem sIdeleSubgroup_univ : sIdeleSubgroup L Set.univ = ⊤ := by
  rw [sIdeleSubgroup, FiniteAdeleRing.sIdeleSubgroup_univ, Subgroup.comap_top]

/-- **`𝕀_L = ⋃_T 𝕀_{L,T}`.**  Every idele is a `T`-idele for some finite set `T` of finite
places. -/
theorem exists_mem_sIdeleSubgroup (u : IdeleGroup (𝓞 L) L) :
    ∃ T : Set (HeightOneSpectrum (𝓞 L)), T.Finite ∧ u ∈ sIdeleSubgroup L T := by
  obtain ⟨T, hT, hu⟩ := FiniteAdeleRing.exists_mem_sIdeleSubgroup (finiteUnits L u)
  exact ⟨T, hT, hu⟩

/-- **`𝕀_L = ⋃_T 𝕀_{L,T}`**, as a supremum of subgroups over the finite sets `T`. -/
theorem iSup_sIdeleSubgroup :
    ⨆ T : {T : Set (HeightOneSpectrum (𝓞 L)) // T.Finite}, sIdeleSubgroup L (T : Set _) = ⊤ := by
  refine eq_top_iff.2 fun u _ ↦ ?_
  obtain ⟨T, hT, hu⟩ := exists_mem_sIdeleSubgroup u
  exact le_iSup (fun T : {T : Set (HeightOneSpectrum (𝓞 L)) // T.Finite} ↦
    sIdeleSubgroup L (T : Set _)) ⟨T, hT⟩ hu

/-! ## Principal `T`-ideles are `T`-units -/

/-- **`L^× ∩ 𝕀_{L,T} = O_{L,T}^×`.**  A principal idele is a `T`-idele exactly when the
element of `Lˣ` defining it is a `T`-unit. -/
@[simp]
theorem principalEmbedding_mem_sIdeleSubgroup_iff {T : Set (HeightOneSpectrum (𝓞 L))} (x : Lˣ) :
    IdeleGroup.principalEmbedding (𝓞 L) L x ∈ sIdeleSubgroup L T ↔ x ∈ T.unit L := by
  rw [sIdeleSubgroup, Subgroup.mem_comap, finiteUnits_principalEmbedding]
  exact FiniteAdeleRing.unitEmbedding_mem_sIdeleSubgroup_iff x

/-- **`L^× ∩ 𝕀_{L,T} = O_{L,T}^×`**, as an equality of subgroups of `𝕀_L`. -/
theorem principalSubgroup_inf_sIdeleSubgroup (T : Set (HeightOneSpectrum (𝓞 L))) :
    IdeleGroup.principalSubgroup (𝓞 L) L ⊓ sIdeleSubgroup L T
      = (T.unit L).map (IdeleGroup.principalEmbedding (𝓞 L) L) := by
  ext u
  constructor
  · rintro ⟨⟨x, rfl⟩, hu⟩
    exact ⟨x, (principalEmbedding_mem_sIdeleSubgroup_iff x).1 hu, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, (principalEmbedding_mem_sIdeleSubgroup_iff x).2 hx⟩

/-! ## The Galois action on the `S`-ideles of `𝕀_L` -/

section Galois

variable {K : Type*} [Field K] [NumberField K] [Algebra K L]

omit [NumberField K] in
@[simp]
theorem finiteUnits_galIdeleAut (σ : L ≃ₐ[K] L) (u : IdeleGroup (𝓞 L) L) :
    finiteUnits L (galIdeleAut K L σ u) = σ • finiteUnits L u := rfl

omit [NumberField K] in
/-- **`𝕀_{L,S}` is a `Gal(L/K)`-subgroup of `𝕀_L`.** -/
theorem galIdeleAut_mem_sIdeleSubgroup (S : Set (HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L)
    {u : IdeleGroup (𝓞 L) L} (hu : u ∈ sIdeleSubgroup L (placesOverSet K L S)) :
    galIdeleAut K L σ u ∈ sIdeleSubgroup L (placesOverSet K L S) := by
  rw [sIdeleSubgroup, Subgroup.mem_comap, finiteUnits_galIdeleAut]
  exact FiniteAdeleRing.smul_mem_sIdeleSubgroup S σ hu

omit [NumberField K] in
@[simp]
theorem galIdeleAut_mem_sIdeleSubgroup_iff (S : Set (HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L)
    {u : IdeleGroup (𝓞 L) L} :
    galIdeleAut K L σ u ∈ sIdeleSubgroup L (placesOverSet K L S) ↔
      u ∈ sIdeleSubgroup L (placesOverSet K L S) := by
  refine ⟨fun h ↦ ?_, galIdeleAut_mem_sIdeleSubgroup S σ⟩
  have h2 := galIdeleAut_mem_sIdeleSubgroup S σ⁻¹ h
  have hinv : galIdeleAut K L σ⁻¹ (galIdeleAut K L σ u) = u := by
    have : galIdeleAut K L σ⁻¹ (galIdeleAut K L σ u) = galIdeleAut K L (σ⁻¹ * σ) u := by
      rw [map_mul]; rfl
    rw [this, inv_mul_cancel, map_one]; rfl
  rwa [hinv] at h2

variable (K L)

/-- The `S`-ideles of `L` form a `Gal(L/K)`-module. -/
instance sIdeleMulDistribMulAction (S : Set (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L) (sIdeleSubgroup L (placesOverSet K L S)) where
  smul σ u := ⟨galIdeleAut K L σ (u : IdeleGroup (𝓞 L) L),
    galIdeleAut_mem_sIdeleSubgroup S σ u.2⟩
  one_smul u := by
    refine Subtype.ext ?_
    show galIdeleAut K L 1 (u : IdeleGroup (𝓞 L) L) = (u : IdeleGroup (𝓞 L) L)
    rw [map_one]
    rfl
  mul_smul σ τ u := by
    refine Subtype.ext ?_
    show galIdeleAut K L (σ * τ) (u : IdeleGroup (𝓞 L) L)
      = galIdeleAut K L σ (galIdeleAut K L τ (u : IdeleGroup (𝓞 L) L))
    rw [map_mul]
    rfl
  smul_mul σ u v := by
    refine Subtype.ext ?_
    show galIdeleAut K L σ ((u : IdeleGroup (𝓞 L) L) * (v : IdeleGroup (𝓞 L) L))
      = galIdeleAut K L σ (u : IdeleGroup (𝓞 L) L) * galIdeleAut K L σ (v : IdeleGroup (𝓞 L) L)
    exact map_mul _ _ _
  smul_one σ := by
    refine Subtype.ext ?_
    show galIdeleAut K L σ (1 : IdeleGroup (𝓞 L) L) = 1
    exact map_one _

end Galois

end IdeleGroup

end NumberField
