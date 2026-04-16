/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.Galois.Profinite
public import Iwasawalib.Topology.Algebra.Group.Basic

@[expose] public section

/-!

# Supplementary results for isomorphisms of Galois groups induced by ring isomorphisms

Maybe these should be in mathlib.

-/

namespace AlgEquiv

theorem continuous_autCongr
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
def continuousAutCongr
    {R A₁ A₂ : Type*} [Field R] [Field A₁] [Field A₂] [Algebra R A₁] [Algebra R A₂]
    (ϕ : A₁ ≃ₐ[R] A₂) : (A₁ ≃ₐ[R] A₁) ≃ₜ* A₂ ≃ₐ[R] A₂ where
  toMulEquiv := ϕ.autCongr
  continuous_toFun := ϕ.continuous_autCongr
  continuous_invFun := ϕ.symm.continuous_autCongr

section autCongrOfSurjective

section Ring

variable {F E : Type*} [CommSemiring F] [Semiring E] [Algebra F E]
  {M N : Type*} [CommSemiring M] [Semiring N] [Algebra M N]
  {f : F →+* M} {g : E ≃+* N}
  (hsurj : Function.Surjective f)
  (hcomp : (algebraMap M N).comp f = RingHom.comp g (algebraMap F E))
include hsurj hcomp

/-- Similar to `AlgEquiv.autCongr`. TODO: go mathlib -/
noncomputable def autCongrOfSurjective : (E ≃ₐ[F] E) ≃* N ≃ₐ[M] N where
  toFun t :=
    letI s := g.symm.trans (t.toRingEquiv.trans g)
    { s with
      commutes' x := by
        obtain ⟨y, rfl⟩ := hsurj x
        replace hcomp := congr($hcomp y)
        simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at hcomp
        simp [s, hcomp]
    }
  invFun t :=
    letI s := g.trans (t.toRingEquiv.trans g.symm)
    { s with
      commutes' x := by
        replace hcomp := congr($hcomp x)
        simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at hcomp
        apply_fun _ using g.injective
        simp [s, ← hcomp]
    }
  left_inv t := by ext; simp
  right_inv t := by ext; simp
  map_mul' s t := by ext; simp

@[simp]
theorem autCongrOfSurjective_apply_apply (t : E ≃ₐ[F] E) (x : N) :
    autCongrOfSurjective hsurj hcomp t x = g (t (g.symm x)) := rfl

@[simp]
theorem autCongrOfSurjective_symm_apply_apply (t : N ≃ₐ[M] N) (x : E) :
    (autCongrOfSurjective hsurj hcomp).symm t x = g.symm (t (g x)) := rfl

end Ring

section Field

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  {M N : Type*} [Field M] [Field N] [Algebra M N]
  {f : F →+* M} {g : E ≃+* N}
  (hsurj : Function.Surjective f)
  (hcomp : (algebraMap M N).comp f = RingHom.comp g (algebraMap F E))
include hsurj hcomp

theorem continuous_autCongrOfSurjective : Continuous (autCongrOfSurjective hsurj hcomp) := by
  set ϕ := autCongrOfSurjective hsurj hcomp
  refine ϕ.toMonoidHom.continuous_iff.2 fun s h1 hs ↦ ?_
  obtain ⟨L, hL, hle⟩ := (krullTopology_mem_nhds_one_iff _ _ s).1 (isOpen_iff_mem_nhds.1 hs _ h1)
  refine ⟨L.fixingSubgroup.comap ϕ.toMonoidHom, one_mem _, ?_, by simpa⟩
  let L' : IntermediateField F E := { L.toSubfield.map g.symm.toRingHom with
    algebraMap_mem' r := ⟨algebraMap M N (f r), L.algebraMap_mem _, by
      simpa using congr(g.symm ($(hcomp) r))⟩
  }
  have : FiniteDimensional F L' := by
    let g' : L ≃+* L' := L.toSubring.equivMapOfInjective g.symm.toRingHom g.symm.injective
    have hg' (x : L') : (g'.symm x).1 = g x.1 := by
      obtain ⟨y, rfl⟩ := g'.surjective x
      change _ = g (g.symm y.1)
      simp
    apply Module.rank_lt_aleph0_iff.1
    have := Algebra.lift_rank_eq_of_equiv_equiv (.ofBijective f ⟨f.injective, hsurj⟩) g'.symm <| by
      ext x
      convert congr($(hcomp) x)
      simp [hg']
    have := this ▸ (Cardinal.lift_lt_aleph0.2 (Module.rank_lt_aleph0_iff.2 hL))
    simpa using this
  convert L'.fixingSubgroup_isOpen
  ext σ
  simp only [MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_comap, MonoidHom.coe_coe,
    IntermediateField.mem_fixingSubgroup_iff, autCongrOfSurjective_apply_apply, ϕ]
  change _ ↔ ∀ x ∈ L.toSubfield.map g.symm.toRingHom, _
  simp only [RingEquiv.toRingHom_eq_coe, Subfield.mem_map, Subfield.mem_mk, Subring.mem_mk,
    Subalgebra.mem_toSubsemiring, IntermediateField.mem_toSubalgebra, RingHom.coe_coe,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · apply_fun _ using g.injective
    simp [h x hx]
  · simp [h x hx]

theorem continuous_autCongrOfSurjective_symm :
    Continuous (autCongrOfSurjective hsurj hcomp).symm := by
  let f' := RingEquiv.ofBijective f ⟨f.injective, hsurj⟩
  have := continuous_autCongrOfSurjective (f := f'.symm.toRingHom) (g := g.symm)
      f'.symm.surjective <| by
    ext x
    obtain ⟨y, rfl⟩ := f'.surjective x
    apply_fun _ using g.injective
    simpa using congr($(hcomp.symm) y)
  convert this

/-- Continuous version of `AlgEquiv.autCongrOfSurjective`. -/
@[simps! toMulEquiv]
noncomputable def continuousAutCongrOfSurjective : (E ≃ₐ[F] E) ≃ₜ* N ≃ₐ[M] N where
  toMulEquiv := autCongrOfSurjective hsurj hcomp
  continuous_toFun := continuous_autCongrOfSurjective hsurj hcomp
  continuous_invFun := continuous_autCongrOfSurjective_symm hsurj hcomp

@[simp]
theorem continuousAutCongrOfSurjective_apply_apply (t : E ≃ₐ[F] E) (x : N) :
    continuousAutCongrOfSurjective hsurj hcomp t x = g (t (g.symm x)) := rfl

@[simp]
theorem continuousAutCongrOfSurjective_symm_apply_apply (t : N ≃ₐ[M] N) (x : E) :
    (continuousAutCongrOfSurjective hsurj hcomp).symm t x = g.symm (t (g x)) := rfl

end Field

end autCongrOfSurjective

end AlgEquiv
