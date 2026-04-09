/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section

/-!

# Supplementary results for isomorphisms of Galois groups induced by ring isomorphisms

-/

namespace AlgEquiv

/-- TODO: go mathlib -/
theorem continuous_autCongr {R A₁ A₂ : Type*} [Field R] [Field A₁] [Field A₂]
    [Algebra R A₁] [Algebra R A₂] (ϕ : A₁ ≃ₐ[R] A₂) : Continuous (autCongr ϕ) := by
  apply MonoidHom.continuous_of_continuousAt_one (autCongr ϕ).toMonoidHom
  rw [Filter.HasBasis.tendsto_iff (galGroupBasis R A₁).nhds_one_hasBasis
      (galGroupBasis R A₂).nhds_one_hasBasis]
  intro ⟨K₂, hK₂⟩ _
  refine ⟨⟨K₂.comap ϕ.toAlgHom, ?_⟩, trivial, ?_⟩
  · exact Module.Finite.of_injective
      ((ϕ.toAlgHom.toLinearMap.restrict
        (p := (K₂.comap ϕ.toAlgHom).toSubalgebra.toSubmodule)).codRestrict
        K₂.toSubalgebra.toSubmodule (by
          intro ⟨x, hx⟩
          simp [IntermediateField.mem_comap] at hx
          exact hx)) (by
        intro ⟨a, ha⟩ ⟨b, hb⟩ h
        simp at h
        exact Subtype.ext (ϕ.injective h))
  · intro σ hσ
    simp only [Set.mem_preimage]
    intro x hx
    simp [autCongr]
    have := hσ (ϕ.symm x) (by simp [IntermediateField.mem_comap]; exact hx)
    simp at this
    exact this

/-- Continuous version of `AlgEquiv.autCongr`. TODO: go mathlib -/
@[simps! apply]
noncomputable def autContinuousCongr {R A₁ A₂ : Type*} [Field R] [Field A₁] [Field A₂]
    [Algebra R A₁] [Algebra R A₂] (ϕ : A₁ ≃ₐ[R] A₂) : Gal(A₁/R) ≃ₜ* Gal(A₂/R) where
  toMulEquiv := autCongr ϕ
  continuous_toFun := continuous_autCongr ϕ
  continuous_invFun := continuous_autCongr ϕ.symm

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
