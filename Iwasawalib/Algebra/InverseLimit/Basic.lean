/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
-- public import Mathlib.Data.Rel
public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

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
variable {A : I → Type*} [∀ i : I, Semiring (A i)] [∀ i : I, Algebra R (A i)]

section LE

variable [LE I] (f : ∀ ⦃i i' : I⦄, i ≤ i' → A i' →ₐ[R] A i)

namespace InverseLimit

/-- The inverse limit of algebras as a subalgebra of products of `A i`. -/
noncomputable def toSubalgebra : Subalgebra R (∀ i, A i) where
  carrier := {x | ∀ ⦃i i'⦄ h, f h (x i') = x i}
  add_mem' := by aesop
  mul_mem' := by aesop
  algebraMap_mem' := by aesop

theorem mem_toSubalgebra {x} : x ∈ toSubalgebra f ↔ ∀ ⦃i i'⦄ h, f h (x i') = x i := Iff.rfl

end InverseLimit

/-- The inverse limit of algebras as a `Type`. -/
abbrev InverseLimit : Type _ := InverseLimit.toSubalgebra f

namespace InverseLimit

section mk

variable {f} (x : ∀ i : I, A i) (hx : ∀ ⦃i i'⦄ h, f h (x i') = x i)

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
theorem algHom_comp_proj {i i' : I} (h : i ≤ i') : (f h).comp (proj f i') = proj f i := by
  ext1 x
  exact x.2 h

theorem eq_of_proj_comp_eq {B : Type*} [Semiring B] [Algebra R B] {a b : B →ₐ[R] InverseLimit f}
    (hab : ∀ i, (proj f i).comp a = (proj f i).comp b) : a = b := by
  ext x i : 3
  simpa using congr($(hab i) x)

end proj

section lift

variable {B : Type*} [Semiring B] [Algebra R B]
  (φ : ∀ i : I, B →ₐ[R] A i) (hφ : ∀ ⦃i i'⦄ h, (f h).comp (φ i') = φ i)

/-- If a family of algebra maps `B → A i` for `i : I` satisfy compatibility conditions,
then they lift to a map $B\to\varprojlim_i A_i$. -/
noncomputable def lift : B →ₐ[R] InverseLimit f where
  toFun x := ⟨fun i ↦ φ i x, fun i i' h ↦ congr($(hφ h) x)⟩
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

theorem ker_lift_eq_iInf : RingHom.ker (lift f φ hφ) = ⨅ i : I, RingHom.ker (φ i) := by
  ext x
  simp only [RingHom.mem_ker, Ideal.mem_iInf]
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · -- congr() macro does not work in this case
    rw [← lift_apply_coe (hφ := hφ), h, ZeroMemClass.coe_zero, Pi.zero_apply]
  · ext i : 2
    simp [h]

end lift

-- section liftRel

-- variable {J : Type*} {B : J → Type*} [∀ j : J, Semiring (B j)] [∀ j : J, Algebra R (B j)]
-- variable [LE J] (g : ∀ ⦃j j' : J⦄, j ≤ j' → B j' →ₐ[R] B j)
-- variable (r : Rel J I) (φ : ∀ ⦃j : J⦄ ⦃i : I⦄, r j i → B j →ₐ[R] A i)
-- variable (hφ : ∀ ⦃j j' i i' i''⦄ (hji : r j i) (hji' : r j' i') (hi : i'' ≤ i) (hi' : i'' ≤ i'),
--   (f hi).comp ((φ hji).comp (proj g j)) = (f hi').comp ((φ hji').comp (proj g j')))

-- end liftRel

section lift₂'

variable {J : Type*} {B : J → Type*} [∀ j : J, Semiring (B j)] [∀ j : J, Algebra R (B j)]
variable [LE J] (g : ∀ ⦃j j' : J⦄, j ≤ j' → B j' →ₐ[R] B j)
variable {ij : I → J} (φ : ∀ i : I, B (ij i) →ₐ[R] A i)
variable (hφ : ∀ ⦃i i'⦄ h, ∃ h', (f h).comp (φ i') = (φ i).comp (g h'))

-- variable {ij : I → J} (φ : ∀ (i : I) (j : J), ij i = j → B j →ₐ[R] A i)
-- variable (hφ : ∀ (i i' : I) (j j' : J) (hij : ij i = j) (hij' : ij i' = j') (hi : i ≤ i'),
--   ∃ (hj : j ≤ j'), (f hi).comp (φ i' j' hij') = (φ i j hij).comp (g hj))

/-- If a map `ij : I → J`, and for each `i : I`,
an algebra map `B (ij i) → A i` is given, satisfying compatibility conditions,
then they lift to a map $\varprojlim_j B_j\to\varprojlim_i A_i$.

This is the primed version since its definition involves a choice of `i ↦ j' i`.
An unprimed version will be defined later with assumptions on index sets. -/
noncomputable def lift₂' : InverseLimit g →ₐ[R] InverseLimit f :=
  lift f (fun i ↦ (φ i).comp (proj _ _)) fun i i' h ↦ by
    obtain ⟨h', hcomp⟩ := hφ h
    rw [← AlgHom.comp_assoc, hcomp, AlgHom.comp_assoc, algHom_comp_proj]

variable {φ hφ}

@[simp]
theorem lift₂'_apply_coe (x i) : (lift₂' f g φ hφ x).1 i = φ i (x.1 _) := rfl

theorem proj_comp_lift₂' (i) : (proj f i).comp (lift₂' f g φ hφ) = (φ i).comp (proj _ _) := rfl

/-- The lift map $\varprojlim_j B_j\to\varprojlim_i A_i$ is unique. -/
theorem eq_lift₂'_of_proj_comp_eq (h : InverseLimit g →ₐ[R] InverseLimit f)
    (hh : ∀ i, (proj f i).comp h = (φ i).comp (proj _ _)) : h = lift₂' f g φ hφ := by
  ext x i : 3
  simpa using congr($(hh i) x)

@[simp]
theorem lift₂'_id :
    lift₂' f f (fun i ↦ AlgHom.id R (A i)) (fun _ _ h ↦ ⟨h, rfl⟩) = AlgHom.id R _ := rfl

variable {K : Type*} {C : K → Type*} [∀ k, Semiring (C k)] [∀ k, Algebra R (C k)]
variable [LE K] (h : ∀ ⦃k k'⦄, k ≤ k' → C k' →ₐ[R] C k)
variable {jk : J → K} {ψ : ∀ j, C (jk j) →ₐ[R] B j}
variable {hψ : ∀ ⦃j j'⦄ h', ∃ h'', (g h').comp (ψ j') = (ψ j).comp (h h'')}

@[simp]
theorem lift₂'_comp_lift₂' : (lift₂' f g φ hφ).comp (lift₂' g h ψ hψ) =
    lift₂' f h (ij := jk ∘ ij) (fun i ↦ (φ i).comp (ψ _)) (fun i i' h' ↦ by
      obtain ⟨h1, h2⟩ := hφ h'
      obtain ⟨h3, h4⟩ := hψ h1
      use h3
      rw [← AlgHom.comp_assoc, h2, AlgHom.comp_assoc, h4, AlgHom.comp_assoc]) := rfl

end lift₂'

section congr

variable {B : I → Type*} [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]
variable (g : ∀ ⦃i i'⦄, i ≤ i' → B i' →ₐ[R] B i)
variable (φ : ∀ i, B i ≃ₐ[R] A i)
variable (hφ : ∀ ⦃i i'⦄ h, (f h).comp (φ i' : B i' →ₐ[R] A i') = (φ i : B i →ₐ[R] A i).comp (g h))

/-- If `A i` and `B i` defined over the same index set are isomorphic,
then their inverse limits are also isomorphic. -/
noncomputable def congr : InverseLimit g ≃ₐ[R] InverseLimit f :=
  .ofAlgHom (lift₂' f g (fun i ↦ (φ i : B i →ₐ[R] A i)) fun _ _ h ↦ ⟨h, hφ h⟩)
    (lift₂' g f (fun i ↦ ((φ i).symm : A i →ₐ[R] B i)) fun i j h ↦ ⟨h, by
      replace hφ := congr(((φ i).symm : A i →ₐ[R] B i).comp
        ($(hφ h).comp ((φ j).symm : A j →ₐ[R] B j)))
      rw [AlgHom.comp_assoc, AlgEquiv.comp_symm, AlgHom.comp_id,
        ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, AlgEquiv.symm_comp, AlgHom.id_comp] at hφ
      exact hφ.symm⟩) (by simp) (by simp)

end congr

section congr₂

variable {J : Type*} {B : J → Type*} [∀ j, Semiring (B j)] [∀ j, Algebra R (B j)]
variable [Preorder J] (g : ∀ ⦃j j'⦄, j ≤ j' → B j' →ₐ[R] B j)
  (hgcomp : ∀ ⦃j j' j''⦄ (h1 : j ≤ j') (h2 : j' ≤ j''), (g h1).comp (g h2) = g (h1.trans h2))
variable (e : I ≃o J) (φ : ∀ i, B (e i) ≃ₐ[R] A i)
variable (hφ : ∀ ⦃i i'⦄ h, (f h).comp (φ i' : B _ →ₐ[R] A i') =
  (φ i : B _ →ₐ[R] A i).comp (g (e.map_rel_iff.2 h)))

/-- If `A i` and `B j` defined over two isomorphic index sets `I` and `J` are isomorphic,
such that `J` is a `Preorder` (which implies that `I` is also), and such that the algebra maps
on `B` are functorial, then their inverse limits are also isomorphic. -/
noncomputable def congr₂ : InverseLimit g ≃ₐ[R] InverseLimit f :=
  .ofAlgHom (lift₂' f g (fun i ↦ (φ i : B _ →ₐ[R] A _)) fun _ _ h ↦ ⟨e.map_rel_iff.2 h, hφ h⟩)
    (lift₂' g f (ij := e.symm) (fun j ↦ (g (OrderIso.apply_symm_apply e j).ge).comp
      (AlgHomClass.toAlgHom (φ (e.symm j)).symm)) fun i j h ↦ ⟨e.symm.map_rel_iff.2 h, by
        replace hφ := congr((g (OrderIso.apply_symm_apply e i).ge).comp
          (AlgHomClass.toAlgHom (φ (e.symm i)).symm) |>.comp
          ($(hφ (e.symm.map_rel_iff.2 h)).comp (AlgHomClass.toAlgHom (φ (e.symm j)).symm)))
        rw [AlgHom.comp_assoc (f _), AlgEquiv.comp_symm, AlgHom.comp_id] at hφ
        simp_rw [AlgHom.comp_assoc] at hφ
        nth_rw 3 [← AlgHom.comp_assoc] at hφ
        rw [AlgEquiv.symm_comp, AlgHom.id_comp, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
          hgcomp] at hφ
        rw [← AlgHom.comp_assoc, hgcomp, hφ]⟩)
    (by
      rw [lift₂'_comp_lift₂']
      refine (eq_lift₂'_of_proj_comp_eq _ _ _ fun i ↦ ?_).symm
      dsimp
      let _ : Preorder I := {
        toLE := ‹LE I›
        le_refl := fun i ↦ by rw [← e.map_rel_iff]
        le_trans := fun i j k hij hjk ↦ by
          rw [← e.map_rel_iff] at hij hjk ⊢
          exact hij.trans hjk
      }
      rw [← AlgHom.comp_assoc, ← hφ (OrderIso.symm_apply_apply e i).ge, AlgHom.comp_assoc (f _),
        AlgEquiv.comp_symm, AlgHom.comp_id, algHom_comp_proj])
    (by
      rw [lift₂'_comp_lift₂']
      refine (eq_lift₂'_of_proj_comp_eq _ _ _ fun i ↦ ?_).symm
      dsimp
      rw [AlgHom.comp_assoc (g _), AlgEquiv.symm_comp, AlgHom.comp_id, algHom_comp_proj])

end congr₂

end InverseLimit

end LE

end Algebra
