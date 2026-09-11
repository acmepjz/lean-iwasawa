/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.FieldTheory.ZpExtension.Basic
public import Iwasawalib.FieldTheory.IntermediateField.FixingSubgroup
public import Iwasawalib.FieldTheory.IntermediateField.RestrictScalars

@[expose] public section

/-!
# The shifted `ℤₚᵈ`-extension `K∞ / Kₑ`

If `K∞ / K` is a `ℤₚᵈ`-extension with layers `Kₙ`, then `K∞ / Kₑ` is again a `ℤₚᵈ`-extension,
with Galois group `Γ^{p^e}`.  This file builds that structure, `MvZpExtension.shift`, and
identifies its layers: `(H.shift e).Kₙ = K_{n+e}`.

The construction is purely topological-group-theoretic once two bridges are in place.

* `EquivMvZp.powContinuousMulEquivΓpow`: the `p^e`-th power map is an isomorphism of
  topological groups `Γ ≃ₜ* Γ^{p^e}`.  It is injective because `ℤₚᵈ` is torsion free, onto by
  the definition of `Γ^{p^e}`, and a homeomorphism because `Γ` is compact and `Γ^{p^e}` is
  Hausdorff.
* `IntermediateField.fixingSubgroupContinuousMulEquiv`: mathlib's
  `IntermediateField.fixingSubgroupEquiv` is an isomorphism of *abstract* groups
  `Gal(L/K)_E ≃* Gal(L/E)`; here it is upgraded to the Krull topologies, again by
  compact-to-Hausdorff, the continuity in the direction `Gal(L/K)_E → Gal(L/E)` being the
  usual "adjoin a primitive element of a finite subextension to `K`, not to `E`" argument.

Note that `EquivMvZp.Γpow` depends only on the underlying group, by
`EquivMvZp.mem_Γpow_iff`; this is what makes `MvZpExtension.map_Γpow_shift` possible.

## Main definitions

* `MvZpExtension.shift`: `K∞ / Kₑ` as a `ℤₚᵈ`-extension of `Kₑ`.
* `MvZpExtension.restrictScalarsGalHom`: `Gal(K∞/Kₑ) →* Gal(K∞/K)`, an injection with image
  the fixing subgroup of `Kₑ`.

## Main results

* `MvZpExtension.map_Γpow_shift`: `Γ_e^{p^n} = Γ^{p^{n+e}}`.
* `MvZpExtension.restrictScalars_Kn_shift`: `(H.shift e).Kₙ = K_{n+e}`.
-/

open IntermediateField

set_option synthInstance.maxHeartbeats 400000

/-! ### The `p^e`-th power map on `ℤₚᵈ` -/

namespace EquivMvZp

variable {G : Type*} [Group G] [TopologicalSpace G] {p : ℕ} [Fact p.Prime] {ι : Type*}
  (H : EquivMvZp G p ι)
include H

/-- `Γ ≅ ℤₚᵈ` is compact. -/
theorem compactSpace : CompactSpace G := H.continuousMulEquiv.toHomeomorph.symm.compactSpace

/-- `Γ ≅ ℤₚᵈ` is Hausdorff. -/
theorem t2Space : T2Space G :=
  letI : T2Space (Multiplicative (ι → ℤ_[p])) := inferInstanceAs (T2Space (ι → ℤ_[p]))
  H.continuousMulEquiv.toHomeomorph.symm.t2Space

/-- `Γ ≅ ℤₚᵈ` is a topological group. -/
theorem continuousMul : ContinuousMul G :=
  H.continuousMulEquiv.isHomeomorph.isInducing.continuousMul H.continuousMulEquiv

/-- `(a * b) ^ n = a ^ n * b ^ n` in `Γ`.  This is proved through
`EquivMvZp.continuousMulEquiv` rather than through the scoped `IsMulCommutative` lemmas,
whose instance search for `CommMagma Γ` does not terminate. -/
theorem mul_pow' (a b : G) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  apply H.continuousMulEquiv.injective
  simp [map_pow, map_mul, mul_pow]

/-- The `p ^ e`-th power map on `Γ` is injective: `ℤₚᵈ` is torsion free. -/
theorem pow_injective (e : ℕ) : Function.Injective fun σ : G ↦ σ ^ p ^ e := by
  intro a b hab
  apply H.continuousMulEquiv.injective
  apply Multiplicative.toAdd.injective
  refine IsAddTorsionFree.nsmul_right_injective (M := ι → ℤ_[p]) (pow_ne_zero e
    (Fact.out : p.Prime).ne_zero) ?_
  have := congrArg (fun x ↦ Multiplicative.toAdd (H.continuousMulEquiv x)) hab
  simpa [map_pow] using this

variable [Finite ι]

/-- **`Γ ≃ Γ^{p^e}` as topological groups**, via the `p ^ e`-th power map. -/
noncomputable def powContinuousMulEquivΓpow (e : ℕ) : G ≃ₜ* ↥(H.Γpow e : Subgroup G) :=
  letI := H.compactSpace
  letI := H.t2Space
  letI := H.continuousMul
  letI f : G →* ↥(H.Γpow e : Subgroup G) := {
    toFun σ := ⟨σ ^ p ^ e, (H.mem_Γpow_iff e _).2 ⟨σ, rfl⟩⟩
    map_one' := by simp
    map_mul' a b := Subtype.ext (H.mul_pow' a b _) }
  letI ebij : Function.Bijective f := by
    refine ⟨fun a b hab ↦ H.pow_injective e (congrArg Subtype.val hab), ?_⟩
    rintro ⟨σ, hσ⟩
    obtain ⟨τ, rfl⟩ := (H.mem_Γpow_iff e σ).1 hσ
    exact ⟨τ, rfl⟩
  letI e' : G ≃ ↥(H.Γpow e : Subgroup G) := Equiv.ofBijective f ebij
  letI hc : Continuous e' := (continuous_pow _).subtype_mk _
  letI h : G ≃ₜ ↥(H.Γpow e : Subgroup G) := hc.homeoOfEquivCompactToT2 (f := e')
  { toEquiv := e'
    map_mul' := map_mul f
    continuous_toFun := h.continuous_toFun
    continuous_invFun := h.continuous_invFun }

/-- Equal subgroups are isomorphic as topological groups. -/
def _root_.Subgroup.continuousMulEquivCongr {A B : Subgroup G} (h : A = B) : ↥A ≃ₜ* ↥B :=
  h ▸ ContinuousMulEquiv.refl ↥A

/-- **`Γ^{p^e}` is again isomorphic to `ℤₚᵈ`.** -/
noncomputable def shift (e : ℕ) : EquivMvZp ↥(H.Γpow e : Subgroup G) p ι :=
  H.congr (H.powContinuousMulEquivΓpow e) (Equiv.refl ι)

end EquivMvZp

/-! ### `Gal(L/E)` and the fixing subgroup of `E`, topologically -/

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (E : IntermediateField K L)

/-- The fixing subgroup of `E` is compact: it is closed in the compact group `Gal(L/K)`. -/
theorem compactSpace_fixingSubgroup : CompactSpace ↥E.fixingSubgroup :=
  isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed E).isCompact

/-- `IntermediateField.fixingSubgroupEquiv` is continuous.  An element of `Gal(L/E)` close to
`1` is one fixing a primitive element `α` of a finite subextension of `L / E`; the elements of
`Gal(L/K)` fixing `α` form an open subgroup because `K⟮α⟯ / K` is finite. -/
theorem continuous_fixingSubgroupEquiv :
    Continuous (IntermediateField.fixingSubgroupEquiv E) := by
  refine continuous_of_continuousAt_one _ (continuousAt_def.2 fun N hN ↦ ?_)
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨F, hFfin, hFN⟩ := hN
  obtain ⟨α, hα⟩ := IntermediateField.exists_adjoin_simple_eq (↥E) L F
  haveI : FiniteDimensional K K⟮α⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K) α)
  have hopen : IsOpen ((Subtype.val ⁻¹' (K⟮α⟯.fixingSubgroup : Set Gal(L/K))) :
      Set ↥E.fixingSubgroup) :=
    (IntermediateField.fixingSubgroup_isOpen K⟮α⟯).preimage continuous_subtype_val
  refine Filter.mem_of_superset (hopen.mem_nhds (by simp)) fun σ hσ ↦ ?_
  refine hFN ?_
  rw [← hα]
  refine IntermediateField.mem_fixingSubgroup_adjoin_simple ?_
  have hσ' : (σ : Gal(L/K)) ∈ K⟮α⟯.fixingSubgroup := hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ'
  exact hσ' α (IntermediateField.mem_adjoin_simple_self K α)

/-- **`Gal(L/K)_E ≃ Gal(L/E)` as topological groups.** -/
noncomputable def fixingSubgroupContinuousMulEquiv : ↥E.fixingSubgroup ≃ₜ* Gal(L/↥E) :=
  letI := compactSpace_fixingSubgroup E
  letI h : ↥E.fixingSubgroup ≃ₜ Gal(L/↥E) :=
    (continuous_fixingSubgroupEquiv E).homeoOfEquivCompactToT2
      (f := (IntermediateField.fixingSubgroupEquiv E).toEquiv)
  { (IntermediateField.fixingSubgroupEquiv E) with
    continuous_toFun := h.continuous_toFun
    continuous_invFun := h.continuous_invFun }

/-- The inclusion `Gal(L/E) →* Gal(L/K)`, restriction of scalars. -/
def restrictScalarsGalHom : Gal(L/↥E) →* Gal(L/K) where
  toFun ϕ := ϕ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

omit [IsGalois K L] in
@[simp]
theorem restrictScalarsGalHom_apply (ϕ : Gal(L/↥E)) (x : L) :
    restrictScalarsGalHom E ϕ x = ϕ x := rfl

omit [IsGalois K L] in
theorem restrictScalarsGalHom_injective :
    Function.Injective (restrictScalarsGalHom E) := fun _ _ h ↦
  AlgEquiv.ext fun x ↦ congr($h x)

omit [IsGalois K L] in
theorem range_restrictScalarsGalHom :
    (restrictScalarsGalHom E).range = E.fixingSubgroup := by
  ext σ
  simp only [MonoidHom.mem_range, IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨?_, fun h ↦ ⟨(IntermediateField.fixingSubgroupEquiv E) ⟨σ, fun x ↦ h x x.2⟩, rfl⟩⟩
  rintro ⟨ϕ, rfl⟩ x hx
  exact ϕ.commutes ⟨x, hx⟩

end IntermediateField

/-! ### Intermediate fields over different base fields with the same carrier -/

namespace IntermediateField

variable {A B L : Type*} [Field A] [Field B] [Field L] [Algebra A L] [Algebra B L]
  (E : IntermediateField A L) (F : IntermediateField B L)

/-- If every element of `E` lies in `F`, then the identity of `L` restricts to a ring
homomorphism `↥E →+* ↥F`, even though `E` and `F` are intermediate fields over *different*
base fields.

This is stated for abstract intermediate fields on purpose: at a concrete intermediate field
the `rfl`s below force the kernel to unfold that field's definition, which does not
terminate. -/
def ringHomOfMemImp (h : ∀ x : L, x ∈ E → x ∈ F) : ↥E →+* ↥F where
  toFun x := ⟨x.1, h x.1 x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_ringHomOfMemImp (h : ∀ x : L, x ∈ E → x ∈ F) (x : ↥E) :
    (ringHomOfMemImp E F h x : L) = (x : L) := rfl

/-- Equal intermediate fields have the same Galois group, as a topological group.

Stated for abstract intermediate fields: at concrete ones the transport forces the kernel to
unfold their definitions. -/
def galContinuousMulEquivCongr {E E' : IntermediateField A L} (h : E = E') :
    Gal(↥E/A) ≃ₜ* Gal(↥E'/A) :=
  h ▸ ContinuousMulEquiv.refl Gal(↥E/A)

/-- `IntermediateField.ringHomOfMemImp` is compatible with the structure maps into any further
extension `Ω / L`. -/
theorem algebraMap_ringHomOfMemImp (h : ∀ x : L, x ∈ E → x ∈ F)
    (Ω : Type*) [Field Ω] [Algebra L Ω] (x : ↥E) :
    algebraMap ↥E Ω x = algebraMap ↥F Ω (ringHomOfMemImp E F h x) := by
  rw [IsScalarTower.algebraMap_apply ↥E L Ω, IsScalarTower.algebraMap_apply ↥F L Ω]
  rfl

end IntermediateField

/-! ### The shifted extension -/

namespace MvZpExtension

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]
variable (H : MvZpExtension p ι K Kinf) (e : ℕ)

/-- **`K∞ / Kₑ` is again a `ℤₚᵈ`-extension.** -/
noncomputable def shift : MvZpExtension p ι ↥(H.Kn e) Kinf :=
  ((EquivMvZp.shift H e).congr (Subgroup.continuousMulEquivCongr (H.fixingSubgroup_Kn e).symm)
    (Equiv.refl ι)).congr (IntermediateField.fixingSubgroupContinuousMulEquiv (H.Kn e))
      (Equiv.refl ι)

/-- The inclusion `Gal(K∞/Kₑ) →* Gal(K∞/K) = Γ`. -/
noncomputable abbrev restrictScalarsGalHom : Gal(Kinf/↥(H.Kn e)) →* H.Γ :=
  IntermediateField.restrictScalarsGalHom (H.Kn e)

/-- Membership in the layer `Kₙ`, unfolded. -/
theorem mem_Kn_iff (n : ℕ) (x : Kinf) :
    x ∈ H.Kn n ↔ ∀ σ ∈ (H.Γpow n : Subgroup H.Γ), σ x = x :=
  IntermediateField.mem_fixedField_iff _ x

theorem range_restrictScalarsGalHom : (H.restrictScalarsGalHom e).range = H.Γpow e :=
  (IntermediateField.range_restrictScalarsGalHom (H.Kn e)).trans (H.fixingSubgroup_Kn e)

variable {H e}

/-- **`Γ_e^{p^n} = Γ^{p^{n+e}}`**, elementwise. -/
theorem mem_Γpow_shift_iff (n : ℕ) (σ : Gal(Kinf/↥(H.Kn e))) :
    H.restrictScalarsGalHom e σ ∈ H.Γpow (n + e) ↔ σ ∈ (H.shift e).Γpow n := by
  have key (ρ : H.Γ) : ρ ^ p ^ (n + e) = (ρ ^ p ^ e) ^ p ^ n := by
    rw [← pow_mul, ← pow_add, Nat.add_comm e n]
  rw [EquivMvZp.mem_Γpow_iff, EquivMvZp.mem_Γpow_iff]
  constructor
  · rintro ⟨ρ, hρ⟩
    have hmem : ρ ^ p ^ e ∈ (H.restrictScalarsGalHom e).range := by
      rw [H.range_restrictScalarsGalHom e]
      exact (H.mem_Γpow_iff e _).2 ⟨ρ, rfl⟩
    obtain ⟨τ, hτ⟩ := hmem
    refine ⟨τ, IntermediateField.restrictScalarsGalHom_injective (H.Kn e) ?_⟩
    rw [hρ, key, ← hτ, ← map_pow]
  · rintro ⟨τ, rfl⟩
    have hmem : H.restrictScalarsGalHom e τ ∈ (H.restrictScalarsGalHom e).range := ⟨τ, rfl⟩
    rw [H.range_restrictScalarsGalHom e] at hmem
    obtain ⟨ρ, hρ⟩ := (H.mem_Γpow_iff e _).1 hmem
    exact ⟨ρ, by rw [map_pow, hρ, key]⟩

/-- **`Γ_e^{p^n} = Γ^{p^{n+e}}`**, as subgroups of `Γ`. -/
theorem map_Γpow_shift (n : ℕ) :
    ((H.shift e).Γpow n : Subgroup Gal(Kinf/↥(H.Kn e))).map (H.restrictScalarsGalHom e) =
      (H.Γpow (n + e) : Subgroup H.Γ) := by
  ext ρ
  rw [Subgroup.mem_map]
  refine ⟨?_, fun hρ ↦ ?_⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact (mem_Γpow_shift_iff n σ).2 hσ
  · have hmem : ρ ∈ (H.restrictScalarsGalHom e).range := by
      rw [H.range_restrictScalarsGalHom e]
      exact H.antitone_Γpow (Nat.le_add_left e n) hρ
    obtain ⟨σ, rfl⟩ := hmem
    exact ⟨σ, (mem_Γpow_shift_iff n σ).1 hρ, rfl⟩

/-- **The layers of the shifted extension are the later layers of the original one**:
`(H.shift e).Kₙ = K_{n+e}`. -/
theorem restrictScalars_Kn_shift (n : ℕ) :
    ((H.shift e).Kn n).restrictScalars K = H.Kn (n + e) := by
  ext x
  rw [IntermediateField.mem_restrictScalars, mem_Kn_iff, mem_Kn_iff]
  constructor
  · intro hx ρ hρ
    rw [← map_Γpow_shift (H := H) (e := e) n, Subgroup.mem_map] at hρ
    obtain ⟨σ, hσ, rfl⟩ := hρ
    exact hx σ hσ
  · intro hx σ hσ
    exact hx (H.restrictScalarsGalHom e σ) (by
      rw [← map_Γpow_shift (H := H) (e := e) n]
      exact ⟨σ, hσ, rfl⟩)

/-- Membership in a layer of the shifted extension. -/
theorem mem_Kn_shift_iff (n : ℕ) (x : Kinf) : x ∈ (H.shift e).Kn n ↔ x ∈ H.Kn (n + e) := by
  rw [← restrictScalars_Kn_shift (H := H) (e := e) n, IntermediateField.mem_restrictScalars]

/-- `(H.shift 0).Kₙ = Kₙ`. -/
theorem restrictScalars_Kn_shift_zero (n : ℕ) :
    ((H.shift 0).Kn n).restrictScalars K = H.Kn n := by
  simpa using restrictScalars_Kn_shift (H := H) (e := 0) n

end MvZpExtension
