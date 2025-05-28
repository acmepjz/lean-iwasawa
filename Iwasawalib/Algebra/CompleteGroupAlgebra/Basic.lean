/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Iwasawalib.Algebra.InverseLimit.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup

/-!

# Complete group algebras

In this file we state basic definitions of complete group algebras.

We introduce the scoped notation `R[ˣG]` for the `MonoidAlgebra`.

DOCUMENT OUTDATED:

If `R` is a commutative semiring, `G` is a topological group, `s` is a subset of open normal
subgroups, then `R⟦ˣG⟧` is defined to be the `Type` corresponding to the
subalgebra (`CompleteGroupAlgebra.toSubalgebra R G s`) of the background ring `Π N ∈ s, R[ˣG/N]`
(`CompleteGroupAlgebra.BackgroundRing R G s`), consisting of elements satisfy certain
compatibility conditions. Mathematically, it is the inverse limit of `R[ˣG/N]` as `N` runs over
elements in `s`. We don't use category theory packages here as currently `AlgebraCat`
doesn't support `Semiring`.

We introduce the scoped notation`R⟦ˣG⟧` for the `R⟦ˣG⟧et.univ`, namely,
the `N` is allowed to be all open normal subgroups.

The natural injection from `R⟦ˣG⟧` to the background ring is
`Subalgebra.val (CompleteGroupAlgebra.toSubalgebra R G s)`.
Its injectivity is `Subtype.val_injective`, hopefully Lean will figure out what the
implicit argument is. If `x` is an element of `R⟦ˣG⟧`, its image in the
background ring is just `x.1`, and the proof that it satisfies the compatibility conditions
is just `x.2`.

Two elements in `R⟦ˣG⟧` are equal, if and only if their images in the
background ring are equal, if and only if their images in `R[ˣG/N]` are equal for all `N ∈ s`.
To achieve this, one may use tactic `ext1`, resp. `ext N ⟨hN⟩ : 3`.

If `N ∈ s`, `CompleteGroupAlgebra.proj R G s N` is the natural projection map from
`R⟦ˣG⟧` to `R[ˣG/N]`.
If `x` is an element of `R⟦ˣG⟧`, then its image under this map is just `x.1 N`
(`CompleteGroupAlgebra.proj_apply`).

In general, if `M` is a normal subgroup such that there exists some `N ∈ s` such that `N ≤ M`,
then `CompleteGroupAlgebra.projOfExistsLE` is a map from `R⟦ˣG⟧` to `R[ˣG/M]`,
defined by using a *random* `N ∈ s` such that `N ≤ M`.

...

The universal property of `R⟦ˣG⟧` is that, if there is a family of maps `S → R[ˣG/N]` satisfying
compatibility conditions, then they lift to a map `S → R⟦ˣG⟧` (`CompleteGroupAlgebra.lift`),
and such lift is unique (`CompleteGroupAlgebra.eq_lift_of_proj_comp_eq`).

...

Currently we only defined the multiplicative version (i.e. no `CompleteAddGroupAlgebra` yet).

-/

/-! ## Things should go to mathlib -/

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
theorem algEquivOfSubsingleton_apply (x : R[ˣG]) : algEquivOfSubsingleton R G x = x 1 := by
  let _ : Inhabited G := ⟨1⟩
  rw [Subsingleton.elim (1 : G) default]
  exact linearEquivOfSubsingleton_apply R G x

@[simp]
theorem algEquivOfSubsingleton_symm_apply (x : R) :
    (algEquivOfSubsingleton R G).symm x = single 1 x := by
  let _ : Inhabited G := ⟨1⟩
  rw [Subsingleton.elim (1 : G) default]
  exact linearEquivOfSubsingleton_symm_apply R G x

end Monoid

end MonoidAlgebra

open scoped MonoidAlgebra

variable (R : Type*) [CommSemiring R] (G : Type*) [Group G] [TopologicalSpace G]

instance OpenNormalSubgroup.instTop : Top (OpenNormalSubgroup G) where
  top := { (⊤ : OpenSubgroup G) with isNormal' := inferInstanceAs (⊤ : Subgroup G).Normal }

/-! ## Definition of complete group algebra -/

/-- The `CompleteGroupAlgebra R G` (with scpoed notation `R⟦ˣG⟧`) is the inverse limit
(`Algebra.InverseLimit`) of `R[ˣG/N]` as `N` runs over open normal subgroups of `G`. -/
abbrev CompleteGroupAlgebra := Algebra.InverseLimit (I := (OpenNormalSubgroup G)ᵒᵈ)
  fun (N₁ N₂ : OpenNormalSubgroup G) (hle : N₂ ≤ N₁) ↦ MonoidAlgebra.mapDomainAlgHom R R
    (QuotientGroup.map N₂.toSubgroup N₁.toSubgroup (MonoidHom.id G) hle)

namespace CompleteGroupAlgebra

@[inherit_doc]
notation:9000 R:max "⟦ˣ" G "⟧" => CompleteGroupAlgebra R G

/-! ## Projection maps -/

section proj

variable (N N' : OpenNormalSubgroup G) (x : R⟦ˣG⟧)

/-- The `proj` is the natural map from `R⟦ˣG⟧` to `R[ˣG/N]` for an open normal subgroup `N`. -/
noncomputable def proj : R⟦ˣG⟧ →ₐ[R] R[ˣG ⧸ N.toSubgroup] := Algebra.InverseLimit.proj ..

@[simp]
theorem proj_apply : proj R G N x = x.1 N := Algebra.InverseLimit.proj_apply ..

variable {N N'} in
theorem mapDomainAlgHom_comp_proj (hle : N ≤ N') :
    (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N.toSubgroup
      N'.toSubgroup (MonoidHom.id G) hle)).comp (proj R G N) = proj R G N' :=
  Algebra.InverseLimit.algHom_comp_proj ..

variable {N N'} in
theorem mapDomainAlgHom_comp_proj_eq_mapDomainAlgHom_comp_proj
    {N'' : Subgroup G} [N''.Normal] (hle : N.toSubgroup ≤ N'') (hle' : N'.toSubgroup ≤ N'') :
    (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N.toSubgroup
      N'' (MonoidHom.id G) hle)).comp (proj R G N) =
    (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N'.toSubgroup
      N'' (MonoidHom.id G) hle')).comp (proj R G N') := by
  let M := N ⊓ N'
  rw [← mapDomainAlgHom_comp_proj R G (show M ≤ N from inf_le_left),
    ← mapDomainAlgHom_comp_proj R G (show M ≤ N' from inf_le_right), ← AlgHom.comp_assoc,
    ← AlgHom.comp_assoc, ← MonoidAlgebra.mapDomainAlgHom_comp, ← MonoidAlgebra.mapDomainAlgHom_comp]
  congr 2
  ext; simp

end proj

section augmentation

/-- The `augmentation` is the map from `R⟦ˣG⟧` to `R`. -/
noncomputable def augmentation : R⟦ˣG⟧ →ₐ[R] R :=
  @MonoidAlgebra.algEquivOfSubsingleton R _ _ _ QuotientGroup.subsingleton_quotient_top
    |>.toAlgHom.comp (proj R G ⊤)

-- should not be a simp lemma
theorem augmentation_apply (x : R⟦ˣG⟧) : augmentation R G x = x.1 (⊤ : OpenNormalSubgroup G) 1 :=
  rfl

end augmentation

/-! ## Universal property of complete group algebra -/

section lift

variable {S : Type*} [Semiring S] [Algebra R S]
  (f : ∀ N : OpenNormalSubgroup G, S →ₐ[R] R[ˣG ⧸ N.toSubgroup])
  (hf : ∀ ⦃N₁ N₂ : OpenNormalSubgroup G⦄ (hle : N₁ ≤ N₂),
    (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N₁.toSubgroup N₂.toSubgroup
      (MonoidHom.id G) hle)).comp (f N₁) = f N₂)

/-- If a family of maps `S → R[ˣG/N]` satisfy compatibility conditions,
then they lift to a map `S → R⟦ˣG⟧`. -/
noncomputable def lift : S →ₐ[R] R⟦ˣG⟧ := Algebra.InverseLimit.lift _ f fun _ _ hle ↦ hf hle

variable {f hf}

@[simp]
theorem lift_apply_coe (x : S) (N : OpenNormalSubgroup G) : (lift R G f hf x).1 N = f N x :=
  Algebra.InverseLimit.lift_apply_coe ..

theorem proj_comp_lift (N : OpenNormalSubgroup G) : (proj R G N).comp (lift R G f hf) = f N :=
  Algebra.InverseLimit.proj_comp_lift ..

/-- The lift map `S → R⟦ˣG⟧` is unique. -/
theorem eq_lift_of_proj_comp_eq (g : S →ₐ[R] R⟦ˣG⟧)
    (hg : ∀ N : OpenNormalSubgroup G, (proj R G N).comp g = f N) : g = lift R G f hf :=
  Algebra.InverseLimit.eq_lift_of_proj_comp_eq _ g fun N ↦ hg N

end lift

section ofMonoidAlgebra

/-- The natural map from `R[ˣG]` to `R⟦ˣG⟧`. -/
noncomputable def ofMonoidAlgebra : R[ˣG] →ₐ[R] R⟦ˣG⟧ :=
  lift R G (fun N ↦ MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.mk' N.toSubgroup))
    fun N₁ N₂ hle ↦ by
      rw [← MonoidAlgebra.mapDomainAlgHom_comp]
      rfl

@[simp]
theorem ofMonoidAlgebra_apply_coe (x : R[ˣG]) (N : OpenNormalSubgroup G) :
    (ofMonoidAlgebra R G x).1 N = MonoidAlgebra.mapDomainAlgHom R R
      (QuotientGroup.mk' N.toSubgroup) x := rfl

theorem proj_comp_ofMonoidAlgebra (N : OpenNormalSubgroup G) :
    (proj R G N).comp (ofMonoidAlgebra R G) = MonoidAlgebra.mapDomainAlgHom R R
      (QuotientGroup.mk' N.toSubgroup) := rfl

end ofMonoidAlgebra

/-! ## Elements of form `r • [g]` -/

section single

/-- The linear map which maps `r` to `r • [g]` in `R⟦ˣG⟧`. -/
noncomputable def single (g : G) : R →ₗ[R] R⟦ˣG⟧ where
  toFun r := ⟨fun _ ↦ .single (QuotientGroup.mk g) r, fun _ _ _ ↦ MonoidAlgebra.mapDomain_single⟩
  map_add' _ _ := by ext : 2; simp
  map_smul' _ _ := by ext : 2; simp

@[simp]
theorem single_apply_coe (g : G) (r : R) (N : OpenNormalSubgroup G) :
    (single R G g r).1 N = .single (QuotientGroup.mk g) r := rfl

theorem one_def : (1 : R⟦ˣG⟧) = single R G 1 1 := by
  ext : 2
  simp [MonoidAlgebra.one_def]

@[simp]
theorem augmentation_single (g : G) (r : R) : augmentation R G (single R G g r) = r := by
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  simp [augmentation_apply, Subsingleton.elim _ (1 : G ⧸ (⊤ : Subgroup G))]

@[simp]
theorem ofMonoidAlgebra_single (g : G) (r : R) :
    ofMonoidAlgebra R G (.single g r) = single R G g r := by
  ext : 2
  simp

-- theorem proj_surjective (N : OpenNormalSubgroup G) :
--     Function.Surjective (proj R N) := fun f ↦ by
--   have := MonoidAlgebra.sum_single f
--   sorry

end single

end CompleteGroupAlgebra
