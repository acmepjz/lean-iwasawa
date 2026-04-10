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

end autCongrOfSurjective

end AlgEquiv
