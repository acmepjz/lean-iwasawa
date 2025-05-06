/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup

/-!

# Complete group algebras

In this file we state basic definitions of complete group algebras.

We introduce the scoped notation `R[ˣG]` for the `MonoidAlgebra` and `R⟦ˣG⟧` for the
`CompleteGroupAlgebra`. The `R⟦ˣG⟧` (or `CompleteGroupAlgebra R G`) for a topological group `G`
is defined to be the `Type` corresponding to the subalgebra
(`CompleteGroupAlgebra.toSubalgebra R G`) of the background ring `Π N, R[ˣG/N]`
(`CompleteGroupAlgebra.BackgroundRing R G`) where `N` runs over all open normal subgroups of `G`,
whose elements satisfy certaining compatibility conditions. Mathematically, it is the inverse limit
of `R[ˣG/N]` as `N` runs over all open normal subgroups of `G`. We don't use
category theory packages here as currently it doesn't support `Semiring`.

The natural injection from `R⟦ˣG⟧` to the background ring is
`Subalgebra.val (CompleteGroupAlgebra.toSubalgebra R G)`.
Its injectivity is `Subtype.val_injective`, hopefully Lean will figure out what the
implicit argument is. If `x` is an element of `R⟦ˣG⟧`, its image in the background ring is just
`x.1`, and the proof that it satisfies the compatibility conditions is just `x.2`.

`CompleteGroupAlgebra.proj` is the natural projection map from `R⟦ˣG⟧` to `R[ˣG/N]`.
If `x` is an element of `R⟦ˣG⟧`, then its image under this map is just `x.1 N`
(`CompleteGroupAlgebra.proj_apply`).

Two elements in `R⟦ˣG⟧` are equal, if and only if their images in the background ring are equal,
if and only if their images in `R[ˣG/N]` are equal for all open normal subgroups `N`.
To achieve this, one may use tactic `ext1`, resp. `ext : 2` (if the name of the open normal
subgroup `N` is needed, use `ext N : 2`).

The universal property of `R⟦ˣG⟧` is that, if there is a family of maps `S → R[ˣG/N]` satisfying
compatibility conditions, then they lift to a map `S → R⟦ˣG⟧` (`CompleteGroupAlgebra.lift`),
and such lift is unique (`CompleteGroupAlgebra.eq_lift_of_proj_comp_eq`).

...

Currently we only defined the multiplicative version (i.e. no `CompleteAddGroupAlgebra` yet).

-/

namespace MonoidAlgebra

variable (R G : Type*)

section Semiring

variable [Semiring R]

@[inherit_doc]
scoped notation:9000 R:max "[ˣ" G "]" => MonoidAlgebra R G

variable [Inhabited G] [Subsingleton G]

/-- If `G` has only one element, then `R[ˣG]` is just `R`. -/
noncomputable def linearEquivOfSubsingleton : R[ˣG] ≃ₗ[R] R :=
  letI : Unique G := Unique.mk' G
  Finsupp.LinearEquiv.finsuppUnique R R G

@[simp]
theorem linearEquivOfSubsingleton_apply (x : R[ˣG]) :
    linearEquivOfSubsingleton R G x = x default := rfl

@[simp]
theorem linearEquivOfSubsingleton_symm_apply (x : R) :
    (linearEquivOfSubsingleton R G).symm x = single default x :=
  let _ : Unique G := Unique.mk' G
  Finsupp.LinearEquiv.finsuppUnique_symm_apply x

theorem eq_single_default_of_subsingleton (x : R[ˣG]) : x = single default (x default) := by
  trans (linearEquivOfSubsingleton R G).symm (linearEquivOfSubsingleton R G x)
  · rw [(linearEquivOfSubsingleton R G).eq_symm_apply]
  rw [linearEquivOfSubsingleton_apply, linearEquivOfSubsingleton_symm_apply]

end Semiring

section Monoid

variable [CommSemiring R] [Monoid G] [Subsingleton G]

/-- If `G` has only one element, then `R[ˣG]` is just `R`. -/
noncomputable def algEquivOfSubsingleton : R[ˣG] ≃ₐ[R] R where
  __ :=
    letI : Inhabited G := ⟨1⟩
    linearEquivOfSubsingleton R G
  map_mul' x y := by
    let _ : Inhabited G := ⟨1⟩
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      linearEquivOfSubsingleton_apply]
    nth_rw 1 [eq_single_default_of_subsingleton R G x, eq_single_default_of_subsingleton R G y]
    simp [Subsingleton.elim default (1 : G)]
  commutes' r := by
    let _ : Inhabited G := ⟨1⟩
    simp [Subsingleton.elim (1 : G) default]

@[simp]
theorem algEquivOfUnique_apply (x : R[ˣG]) : algEquivOfSubsingleton R G x = x 1 := by
  let _ : Inhabited G := ⟨1⟩
  rw [Subsingleton.elim (1 : G) default]
  exact linearEquivOfSubsingleton_apply R G x

@[simp]
theorem algEquivOfUnique_symm_apply (x : R) : (algEquivOfSubsingleton R G).symm x = single 1 x := by
  let _ : Inhabited G := ⟨1⟩
  rw [Subsingleton.elim (1 : G) default]
  exact linearEquivOfSubsingleton_symm_apply R G x

end Monoid

end MonoidAlgebra

open scoped MonoidAlgebra

variable (R : Type*) [CommSemiring R]
  (G : Type*) [Group G] [TopologicalSpace G]

instance _root_.OpenNormalSubgroup.instTop : Top (OpenNormalSubgroup G) where
  top := { (⊤ : OpenSubgroup G) with isNormal' := inferInstanceAs (⊤ : Subgroup G).Normal }

namespace CompleteGroupAlgebra

/-- The background ring `Π N, R[ˣG/N]` of `CompleteAddGroupAlgebra`. -/
abbrev BackgroundRing := (N : OpenNormalSubgroup G) → R[ˣG ⧸ N.toSubgroup]

/-- The `CompleteGroupAlgebra` as a subalgebra of `BackgroundRing`. -/
noncomputable def toSubalgebra : Subalgebra R (BackgroundRing R G) where
  carrier := {x | ∀ (N₁ N₂ : OpenNormalSubgroup G) (hle : N₁ ≤ N₂),
    MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N₁.toSubgroup N₂.toSubgroup
      (MonoidHom.id G) hle) (x N₁) = x N₂}
  add_mem' {x} {y} hx hy N₁ N₂ hle := by
    simp_rw [Pi.add_apply, map_add, hx N₁ N₂ hle, hy N₁ N₂ hle]
  mul_mem' {x} {y} hx hy N₁ N₂ hle := by
    simp_rw [Pi.mul_apply, map_mul, hx N₁ N₂ hle, hy N₁ N₂ hle]
  algebraMap_mem' r N₁ N₂ hle := MonoidAlgebra.mapDomain_algebraMap R _ r

theorem mem_toSubalgebra {x : BackgroundRing R G} : x ∈ toSubalgebra R G ↔
    ∀ (N₁ N₂ : OpenNormalSubgroup G) (hle : N₁ ≤ N₂),
      MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N₁.toSubgroup N₂.toSubgroup
        (MonoidHom.id G) hle) (x N₁) = x N₂ := Iff.rfl

end CompleteGroupAlgebra

open scoped CompleteGroupAlgebra

/-- The `CompleteGroupAlgebra` as a `Type`. -/
abbrev CompleteGroupAlgebra : Type _ := CompleteGroupAlgebra.toSubalgebra R G

namespace CompleteGroupAlgebra

@[inherit_doc]
notation:9000 R:max "⟦ˣ" G "⟧" => CompleteGroupAlgebra R G

section proj

variable {G}

/-- The natural map from `R⟦ˣG⟧` to `R[ˣG/N]`. -/
noncomputable def proj (N : OpenNormalSubgroup G) : R⟦ˣG⟧ →ₐ[R] R[ˣG ⧸ N.toSubgroup] :=
  (Pi.evalAlgHom R _ N).comp (show R⟦ˣG⟧ →ₐ[R] _ from Subalgebra.val _)

@[simp]
theorem proj_apply (N : OpenNormalSubgroup G) (x : R⟦ˣG⟧) : proj R N x = x.1 N := rfl

end proj

section augmentation

variable {G}

/-- The natural map from `R⟦ˣG⟧` to `R`. -/
noncomputable def augmentation : R⟦ˣG⟧ →ₐ[R] R := (@MonoidAlgebra.algEquivOfSubsingleton R _ _ _
  QuotientGroup.subsingleton_quotient_top).toAlgHom.comp (proj R (⊤ : OpenNormalSubgroup G))

@[simp]
theorem augmentation_apply (x : R⟦ˣG⟧) : augmentation R x = x.1 ⊤ 1 := rfl

end augmentation

section lift

variable {R G} {S : Type*} [Semiring S] [Algebra R S]
  (f : (N : OpenNormalSubgroup G) → S →ₐ[R] R[ˣG ⧸ N.toSubgroup])
  (hf : ∀ (N₁ N₂ : OpenNormalSubgroup G) (hle : N₁ ≤ N₂),
    (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N₁.toSubgroup N₂.toSubgroup
      (MonoidHom.id G) hle)).comp (f N₁) = f N₂)

/-- If there is a family of maps `S → R[ˣG/N]` satisfying compatibility conditions, then they
lift to a map `S → R⟦ˣG⟧`. -/
noncomputable def lift : S →ₐ[R] R⟦ˣG⟧ where
  toFun x := ⟨fun N ↦ f N x, fun N₁ N₂ hle ↦ congr($(hf N₁ N₂ hle) x)⟩
  map_one' := by ext : 2; simp
  map_mul' _ _ := by ext : 2; simp
  map_zero' := by ext : 2; simp
  map_add' _ _ := by ext : 2; simp
  commutes' _ := by ext : 2; simp

@[simp]
theorem lift_apply_coe (x : S) (N : OpenNormalSubgroup G) : (lift f hf x).1 N = f N x := rfl

variable {f hf}

theorem proj_comp_lift (N : OpenNormalSubgroup G) :
  (proj R N).comp (lift f hf) = f N := rfl

/-- The lift map `S → R⟦ˣG⟧` is unique. -/
theorem eq_lift_of_proj_comp_eq (g : S →ₐ[R] R⟦ˣG⟧)
    (hg : ∀ N : OpenNormalSubgroup G, (proj R N).comp g = f N) : g = lift f hf := by
  ext x N : 3
  simpa using congr($(hg N) x)

end lift

section ofMonoidAlgebra

/-- The natural map from `R[ˣG]` to `R⟦ˣG⟧`. -/
noncomputable def ofMonoidAlgebra : R[ˣG] →ₐ[R] R⟦ˣG⟧ :=
  lift (fun N : OpenNormalSubgroup G ↦ MonoidAlgebra.mapDomainAlgHom R R
    (QuotientGroup.mk' N.toSubgroup)) fun N₁ N₂ hle ↦ by
      rw [← MonoidAlgebra.mapDomainAlgHom_comp]
      rfl

theorem ofMonoidAlgebra_apply_coe (x : R[ˣG]) (N : OpenNormalSubgroup G) :
    (ofMonoidAlgebra R G x).1 N = MonoidAlgebra.mapDomainAlgHom R R
      (QuotientGroup.mk' N.toSubgroup) x := rfl

theorem proj_comp_ofMonoidAlgebra (N : OpenNormalSubgroup G) :
    (proj R N).comp (ofMonoidAlgebra R G) = MonoidAlgebra.mapDomainAlgHom R R
      (QuotientGroup.mk' N.toSubgroup) := rfl

end ofMonoidAlgebra

section single

variable {R G}

/-- The linear map which maps `r` to `r • [g]` in `R⟦ˣG⟧`. -/
noncomputable def single (g : G) : R →ₗ[R] R⟦ˣG⟧ where
  toFun r := ⟨fun N ↦ .single (QuotientGroup.mk g) r, fun _ _ _ ↦ MonoidAlgebra.mapDomain_single⟩
  map_add' _ _ := by ext : 2; simp
  map_smul' _ _ := by ext : 2; simp

@[simp]
theorem single_apply_coe (g : G) (r : R) (N : OpenNormalSubgroup G) :
    (single g r).1 N = .single (QuotientGroup.mk g) r := rfl

theorem one_def : (1 : R⟦ˣG⟧) = single 1 1 := by
  ext : 2
  simp [MonoidAlgebra.one_def]

@[simp]
theorem augmentation_single (g : G) (r : R) : augmentation R (single g r) = r := by
  have : Subsingleton (G ⧸ (⊤ : OpenNormalSubgroup G).toSubgroup) :=
    QuotientGroup.subsingleton_quotient_top
  simp [Subsingleton.elim _ (1 : G ⧸ (⊤ : OpenNormalSubgroup G).toSubgroup)]

@[simp]
theorem ofMonoidAlgebra_single (g : G) (r : R) :
    ofMonoidAlgebra R G (.single g r) = single g r := by
  ext : 2
  simp [ofMonoidAlgebra_apply_coe]

theorem proj_surjective (N : OpenNormalSubgroup G) :
    Function.Surjective (proj R N) := fun f ↦ by
  have := MonoidAlgebra.sum_single f
  sorry

end single

end CompleteGroupAlgebra
