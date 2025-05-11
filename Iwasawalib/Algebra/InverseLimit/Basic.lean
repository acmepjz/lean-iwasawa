/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!

# Inverse limit of algebras

Let `R` be a commutative semiring, `I` be an index set with `≤` defined,
`A` be a family of `R`-algebras indexed by `I`, `f` be a family of algebra homomorphisms,
consisting of a map from `A j` to `A i` whenever `i ≤ j`
(i.e. map from larger index to smaller index).
One can define the inverse limit `Algebra.InverseLimit` with respect to these maps `f`.

-/

namespace Algebra

variable {R : Type*} [CommSemiring R] {I : Type*}
variable {A : I → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

section LE

variable [LE I] (f : ∀ ⦃i j⦄, i ≤ j → A j →ₐ[R] A i)

namespace InverseLimit

/-- The inverse limit of algebras as a subalgebra of products of `A i`. -/
noncomputable def toSubalgebra : Subalgebra R (∀ i, A i) where
  carrier := {x | ∀ ⦃i j⦄ h, f h (x j) = x i}
  add_mem' := by aesop
  mul_mem' := by aesop
  algebraMap_mem' := by aesop

theorem mem_toSubalgebra {x} : x ∈ toSubalgebra f ↔ ∀ ⦃i j⦄ h, f h (x j) = x i := Iff.rfl

end InverseLimit

/-- The inverse limit of algebras as a `Type`. -/
abbrev InverseLimit : Type _ := InverseLimit.toSubalgebra f

namespace InverseLimit

section mk

variable {f} (x : ∀ i, A i) (hx : ∀ ⦃i j⦄ h, f h (x j) = x i)

/-- Construct an element of the inverse limit of algebras
from a compatible family of elements. -/
noncomputable def mk : InverseLimit f := ⟨x, hx⟩

@[simp]
theorem mk_coe : (mk x hx).1 = x := rfl

end mk

section proj

variable (i : I) (x : InverseLimit f)

/-- The `proj` is the natural map from the inverse limit of `A` to `A i` for `i : I`. -/
noncomputable def proj : InverseLimit f →ₐ[R] A i :=
  (Pi.evalAlgHom R _ i).comp (show InverseLimit f →ₐ[R] _ from Subalgebra.val _)

@[simp]
theorem proj_apply : proj f i x = x.1 i := rfl

@[simp]
theorem algHom_comp_proj {i j : I} (h : i ≤ j) : (f h).comp (proj f j) = proj f i := by
  ext1 x
  exact x.2 h

end proj

section lift

variable {B : Type*} [Semiring B] [Algebra R B]
  (φ : ∀ i, B →ₐ[R] A i) (hφ : ∀ ⦃i j⦄ h, (f h).comp (φ j) = φ i)

/-- If a family of algebra maps `B → A i` for `i : I` satisfy compatibility conditions,
then they lift to a map $B\to\varprojlim_i A_i$. -/
noncomputable def lift : B →ₐ[R] InverseLimit f where
  toFun x := ⟨fun i ↦ φ i x, fun i j h ↦ congr($(hφ h) x)⟩
  map_one' := by aesop
  map_mul' := by aesop
  map_zero' := by aesop
  map_add' := by aesop
  commutes' := by aesop

variable {φ hφ}

@[simp]
theorem lift_apply_coe (x i) : (lift f φ hφ x).1 i = φ i x := rfl

theorem proj_comp_lift (i) : (proj f i).comp (lift f φ hφ) = φ i := rfl

/-- The lift map $B\to\varprojlim_i A_i$ is unique. -/
theorem eq_lift_of_proj_comp_eq (g : B →ₐ[R] InverseLimit f)
    (hg : ∀ i, (proj f i).comp g = φ i) : g = lift f φ hφ := by
  ext x i : 3
  simpa using congr($(hg i) x)

end lift

section lift₂

variable {J : Type*} {B : J → Type*} [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]
variable [LE J] (g : ∀ ⦃i j⦄, i ≤ j → B j →ₐ[R] B i)
variable {j' : I → J} (φ : ∀ i, B (j' i) →ₐ[R] A i)
variable (hφ : ∀ ⦃i j⦄ h, ∃ h', (f h).comp (φ j) = (φ i).comp (g h'))

/-- If for each `i : I`, an element `j' i : J` and
an algebra map `B (j' i) → A i` is given, satisfying compatibility conditions,
then they lift to a map $\varprojlim_j B_j\to\varprojlim_i A_i$. -/
noncomputable def lift₂ : InverseLimit g →ₐ[R] InverseLimit f :=
  lift f (fun i ↦ (φ i).comp (proj _ _)) fun i j h ↦ by
    obtain ⟨h', hcomp⟩ := hφ h
    rw [← AlgHom.comp_assoc, hcomp, AlgHom.comp_assoc, algHom_comp_proj]

variable {φ hφ}

@[simp]
theorem lift₂_apply_coe (x i) : (lift₂ f g φ hφ x).1 i = φ i (x.1 _) := rfl

theorem proj_comp_lift₂ (i) : (proj f i).comp (lift₂ f g φ hφ) = (φ i).comp (proj _ _) := rfl

/-- The lift map $\varprojlim_j B_j\to\varprojlim_i A_i$ is unique. -/
theorem eq_lift₂_of_proj_comp_eq (h : InverseLimit g →ₐ[R] InverseLimit f)
    (hh : ∀ i, (proj f i).comp h = (φ i).comp (proj _ _)) : h = lift₂ f g φ hφ := by
  ext x i : 3
  simpa using congr($(hh i) x)

@[simp]
theorem lift₂_id :
    lift₂ f f (fun i ↦ AlgHom.id R (A i)) (fun _ _ h ↦ ⟨h, rfl⟩) = AlgHom.id R _ := rfl

variable {K : Type*} {C : K → Type*} [∀ i, Semiring (C i)] [∀ i, Algebra R (C i)]
variable [LE K] (h : ∀ ⦃i j⦄, i ≤ j → C j →ₐ[R] C i)
variable {k' : J → K} {ψ : ∀ i, C (k' i) →ₐ[R] B i}
variable {hψ : ∀ ⦃i j⦄ h', ∃ h'', (g h').comp (ψ j) = (ψ i).comp (h h'')}

@[simp]
theorem lift₂_comp_lift₂ : (lift₂ f g φ hφ).comp (lift₂ g h ψ hψ) =
    lift₂ f h (j' := k' ∘ j') (fun i ↦ (φ i).comp (ψ _)) (fun i j h' ↦ by
      obtain ⟨h1, h2⟩ := hφ h'
      obtain ⟨h3, h4⟩ := hψ h1
      use h3
      rw [← AlgHom.comp_assoc, h2, AlgHom.comp_assoc, h4, AlgHom.comp_assoc]) := rfl

end lift₂

section congr

variable {B : I → Type*} [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]
variable (g : ∀ ⦃i j⦄, i ≤ j → B j →ₐ[R] B i)
variable (φ : ∀ i, B i ≃ₐ[R] A i)
variable (hφ : ∀ ⦃i j⦄ h, (f h).comp (φ j : B j →ₐ[R] A j) = (φ i : B i →ₐ[R] A i).comp (g h))

noncomputable def congr : InverseLimit g ≃ₐ[R] InverseLimit f :=
  .ofAlgHom (lift₂ f g (fun i ↦ (φ i : B i →ₐ[R] A i)) fun _ _ h ↦ ⟨h, hφ h⟩)
    (lift₂ g f (fun i ↦ ((φ i).symm : A i →ₐ[R] B i)) fun i j h ↦ ⟨h, by
      replace hφ := congr(((φ i).symm : A i →ₐ[R] B i).comp
        ($(hφ h).comp ((φ j).symm : A j →ₐ[R] B j)))
      rw [AlgHom.comp_assoc, AlgEquiv.comp_symm, AlgHom.comp_id,
        ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, AlgEquiv.symm_comp, AlgHom.id_comp] at hφ
      exact hφ.symm⟩) (by simp) (by simp)

end congr

end InverseLimit

end LE

end Algebra
