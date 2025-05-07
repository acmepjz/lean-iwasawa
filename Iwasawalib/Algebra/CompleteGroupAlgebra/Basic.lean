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

We introduce the scoped notation `R[ˣG]` for the `MonoidAlgebra`.

If `R` is a commutative semiring, `G` is a topological group, `s` is a subset of open normal
subgroups, then `CompleteGroupAlgebra R G s` is defined to be the `Type` corresponding to the
subalgebra (`CompleteGroupAlgebra.toSubalgebra R G s`) of the background ring `Π N ∈ s, R[ˣG/N]`
(`CompleteGroupAlgebra.BackgroundRing R G s`), consisting of elements satisfy certain
compatibility conditions. Mathematically, it is the inverse limit of `R[ˣG/N]` as `N` runs over
elements in `s`. We don't use category theory packages here as currently `AlgebraCat`
doesn't support `Semiring`.

We introduce the scoped notation`R⟦ˣG⟧` for the `CompleteGroupAlgebra R G Set.univ`, namely,
the `N` is allowed to be all open normal subgroups.

The natural injection from `CompleteGroupAlgebra R G s` to the background ring is
`Subalgebra.val (CompleteGroupAlgebra.toSubalgebra R G s)`.
Its injectivity is `Subtype.val_injective`, hopefully Lean will figure out what the
implicit argument is. If `x` is an element of `CompleteGroupAlgebra R G s`, its image in the
background ring is just `x.1`, and the proof that it satisfies the compatibility conditions
is just `x.2`.

Two elements in `CompleteGroupAlgebra R G s` are equal, if and only if their images in the
background ring are equal, if and only if their images in `R[ˣG/N]` are equal for all `N ∈ s`.
To achieve this, one may use tactic `ext1`, resp. `ext N ⟨hN⟩ : 3`.

If `N ∈ s`, `CompleteGroupAlgebra.proj R G s N` is the natural projection map from
`CompleteGroupAlgebra R G s` to `R[ˣG/N]`.
If `x` is an element of `CompleteGroupAlgebra R G s`, then its image under this map is just `x.1 N`
(`CompleteGroupAlgebra.proj_apply`).

In general, if `M` is a normal subgroup such that there exists some `N ∈ s` such that `N ≤ M`,
then `CompleteGroupAlgebra.projOfExistsLE` is a map from `CompleteGroupAlgebra R G s` to `R[ˣG/M]`,
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
  (s : Set (OpenNormalSubgroup G))

instance OpenNormalSubgroup.instTop : Top (OpenNormalSubgroup G) where
  top := { (⊤ : OpenSubgroup G) with isNormal' := inferInstanceAs (⊤ : Subgroup G).Normal }

/-! ## Definition of complete group algebra -/

namespace CompleteGroupAlgebra

/-- The background ring `Π N ∈ s, R[ˣG/N]` of `CompleteAddGroupAlgebra`. -/
abbrev BackgroundRing := ⦃N : OpenNormalSubgroup G⦄ → PLift (N ∈ s) → R[ˣG ⧸ N.toSubgroup]

/-- The complete group algebra as a subalgebra of `BackgroundRing`. -/
noncomputable def toSubalgebra : Subalgebra R (BackgroundRing R G s) where
  carrier := {x | ∀ ⦃N₁ N₂⦄ (hN₁ : N₁ ∈ s) (hN₂ : N₂ ∈ s) (hle : N₁ ≤ N₂),
    MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N₁.toSubgroup N₂.toSubgroup
      (MonoidHom.id G) hle) (x ⟨hN₁⟩) = x ⟨hN₂⟩}
  add_mem' {x} {y} hx hy N₁ N₂ hN₁ hN₂ hle := by
    simp_rw [Pi.add_apply, map_add, hx hN₁ hN₂ hle, hy hN₁ hN₂ hle]
  mul_mem' {x} {y} hx hy N₁ N₂ hN₁ hN₂ hle := by
    simp_rw [Pi.mul_apply, map_mul, hx hN₁ hN₂ hle, hy hN₁ hN₂ hle]
  algebraMap_mem' r N₁ N₂ hN₁ hN₂ hle := MonoidAlgebra.mapDomain_algebraMap R _ r

theorem mem_toSubalgebra {x : BackgroundRing R G s} : x ∈ toSubalgebra R G s ↔
    ∀ ⦃N₁ N₂⦄ (hN₁ : N₁ ∈ s) (hN₂ : N₂ ∈ s) (hle : N₁ ≤ N₂),
      MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N₁.toSubgroup N₂.toSubgroup
        (MonoidHom.id G) hle) (x ⟨hN₁⟩) = x ⟨hN₂⟩ := Iff.rfl

end CompleteGroupAlgebra

open scoped CompleteGroupAlgebra

/-- The `CompleteGroupAlgebra` as a `Type`.
The scoped notation `R⟦ˣG⟧` is `CompleteGroupAlgebra R G Set.univ`. -/
abbrev CompleteGroupAlgebra : Type _ := CompleteGroupAlgebra.toSubalgebra R G s

namespace CompleteGroupAlgebra

@[inherit_doc]
notation:9000 R:max "⟦ˣ" G "⟧" => CompleteGroupAlgebra R G Set.univ

/-! ## Projection maps -/

section proj

variable {N} (hN : N ∈ s) (x : CompleteGroupAlgebra R G s)

/-- The `proj` is the natural map from `CompleteGroupAlgebra R G s` to `R[ˣG/N]` for `N ∈ s`. -/
noncomputable def proj : CompleteGroupAlgebra R G s →ₐ[R] R[ˣG ⧸ N.toSubgroup] :=
  (Pi.evalAlgHom R _ ⟨hN⟩).comp (Pi.evalAlgHom R _ N) |>.comp
    (show CompleteGroupAlgebra R G s →ₐ[R] _ from Subalgebra.val _)

@[simp]
theorem proj_apply : proj R G s hN x = x.1 ⟨hN⟩ := rfl

theorem mapDomainAlgHom_comp_proj {N'} (hN' : N' ∈ s) (hle : N ≤ N') :
    (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N.toSubgroup
      N'.toSubgroup (MonoidHom.id G) hle)).comp (proj R G s hN) = proj R G s hN' := by
  ext1 x
  simp_rw [AlgHom.coe_comp, Function.comp_apply, proj_apply, x.2 hN hN' hle]

theorem mapDomainAlgHom_comp_proj_eq_mapDomainAlgHom_comp_proj
    {N'} (hN' : N' ∈ s) {N'' : Subgroup G} [N''.Normal] (hle : N.toSubgroup ≤ N'')
    (hle' : N'.toSubgroup ≤ N'') (hexists : ∃ M ∈ s, M ≤ N ∧ M ≤ N') :
    (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N.toSubgroup
      N'' (MonoidHom.id G) hle)).comp (proj R G s hN) =
    (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N'.toSubgroup
      N'' (MonoidHom.id G) hle')).comp (proj R G s hN') := by
  obtain ⟨M, hM, hle1, hle2⟩ := hexists
  rw [← mapDomainAlgHom_comp_proj R G s hM hN hle1,
    ← mapDomainAlgHom_comp_proj R G s hM hN' hle2, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
    ← MonoidAlgebra.mapDomainAlgHom_comp, ← MonoidAlgebra.mapDomainAlgHom_comp]
  congr 2
  ext; simp

theorem mapDomainAlgHom_comp_proj_eq_mapDomainAlgHom_comp_proj'
    {N'} (hN' : N' ∈ s) {N'' : Subgroup G} [N''.Normal] (hle : N.toSubgroup ≤ N'')
    (hle' : N'.toSubgroup ≤ N'') (hs : DirectedOn GE.ge s) :
    (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N.toSubgroup
      N'' (MonoidHom.id G) hle)).comp (proj R G s hN) =
    (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N'.toSubgroup
      N'' (MonoidHom.id G) hle')).comp (proj R G s hN') :=
  mapDomainAlgHom_comp_proj_eq_mapDomainAlgHom_comp_proj R G s hN hN' hle hle' (hs _ hN _ hN')

end proj

section projOfExistsLE

variable (M : Subgroup G) [M.Normal] (hM : ∃ N ∈ s, N.toSubgroup ≤ M)

/-- If `M` is a normal subgroup such that there exists some `N ∈ s` such that `N ≤ M`,
then `projOfExistsLE` is a map from `CompleteGroupAlgebra R G s` to `R[ˣG/M]`,
defined by using a *random* `N ∈ s` such that `N ≤ M`. -/
noncomputable def projOfExistsLE : CompleteGroupAlgebra R G s →ₐ[R] R[ˣG ⧸ M] :=
  (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map hM.choose.toSubgroup M
    (MonoidHom.id G) hM.choose_spec.2)).comp (proj R G s hM.choose_spec.1)

/-- If `M ∈ s`, then the `projOfExistsLE` for `M` is equal to the `proj` for `M`. -/
theorem projOfExistsLE_eq_proj {M} (hM : M ∈ s) :
    projOfExistsLE R G s M.toSubgroup ⟨M, hM, le_rfl⟩ = proj R G s hM := by
  rw [projOfExistsLE, mapDomainAlgHom_comp_proj]

/-- The definition of `projOfExistsLE` is independent of the choice of `N ∈ s` such that `N ≤ M`,
provided that `s` is directed, i.e. for any `N₁, N₂ ∈ s` there exists `N₃ ∈ s`
such that `N₃ ≤ N₁` and `N₃ ≤ N₂`. -/
theorem projOfExistsLE_eq_mapDomainAlgHom_comp_proj
    {N} (hN : N ∈ s) (hle : N.toSubgroup ≤ M) (hs : DirectedOn GE.ge s) :
    projOfExistsLE R G s M ⟨N, hN, hle⟩ =
      (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N.toSubgroup M
        (MonoidHom.id G) hle)).comp (proj R G s hN) := by
  have hM : ∃ N ∈ s, N.toSubgroup ≤ M := ⟨N, hN, hle⟩
  rw [projOfExistsLE]
  exact mapDomainAlgHom_comp_proj_eq_mapDomainAlgHom_comp_proj' R G s _ hN _ hle hs

theorem mapDomainAlgHom_comp_projOfExistsLE (M' : Subgroup G) [M'.Normal] (hle : M ≤ M')
    (hs : DirectedOn GE.ge s) :
    (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map M M' (MonoidHom.id G) hle)).comp
      (projOfExistsLE R G s M hM) = projOfExistsLE R G s M'
        ⟨hM.choose, hM.choose_spec.1, hM.choose_spec.2.trans hle⟩ := by
  have hM' : ∃ N ∈ s, N.toSubgroup ≤ M' :=
    ⟨hM.choose, hM.choose_spec.1, hM.choose_spec.2.trans hle⟩
  rw [projOfExistsLE, projOfExistsLE, ← AlgHom.comp_assoc, ← MonoidAlgebra.mapDomainAlgHom_comp]
  convert mapDomainAlgHom_comp_proj_eq_mapDomainAlgHom_comp_proj' R G s
    hM.choose_spec.1 hM'.choose_spec.1 (hM.choose_spec.2.trans hle) hM'.choose_spec.2 hs
  ext; simp

end projOfExistsLE

section augmentation

/-- If `s` is not empty, then `augmentation` is a map from `CompleteGroupAlgebra R G s` to `R`. -/
noncomputable def augmentation (hs : s.Nonempty) : CompleteGroupAlgebra R G s →ₐ[R] R :=
  @MonoidAlgebra.algEquivOfSubsingleton R _ _ _ QuotientGroup.subsingleton_quotient_top
    |>.toAlgHom.comp (projOfExistsLE R G s ⊤ ⟨_, hs.some_mem, le_top⟩)

theorem augmentation_apply_of_top_mem (x : CompleteGroupAlgebra R G s) (h : ⊤ ∈ s) :
    augmentation R G s ⟨_, h⟩ x = x.1 ⟨h⟩ 1 := by
  have : projOfExistsLE R G s ⊤ _ = _  := projOfExistsLE_eq_proj R G s h
  rw [augmentation, this]
  rfl

end augmentation

/-! ## Universal property of complete group algebra -/

section lift

variable {S : Type*} [Semiring S] [Algebra R S]
  (f : ∀ ⦃N⦄, N ∈ s → S →ₐ[R] R[ˣG ⧸ N.toSubgroup])
  (hf : ∀ ⦃N₁ N₂⦄ (hN₁ : N₁ ∈ s) (hN₂ : N₂ ∈ s) (hle : N₁ ≤ N₂),
    (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map N₁.toSubgroup N₂.toSubgroup
      (MonoidHom.id G) hle)).comp (f hN₁) = f hN₂)

/-- If a family of maps `S → R[ˣG/N]` for `N ∈ S` satisfy compatibility conditions,
then they lift to a map `S → CompleteGroupAlgebra R G s`. -/
noncomputable def lift : S →ₐ[R] CompleteGroupAlgebra R G s where
  toFun x := ⟨fun N ⟨hN⟩ ↦ f hN x, fun N₁ N₂ hN₁ hN₂ hle ↦ congr($(hf hN₁ hN₂ hle) x)⟩
  map_one' := by ext : 3; simp
  map_mul' _ _ := by ext : 3; simp
  map_zero' := by ext : 3; simp
  map_add' _ _ := by ext : 3; simp
  commutes' _ := by ext : 3; simp

variable {f hf}

@[simp]
theorem lift_apply_coe (x : S) {N} (hN : N ∈ s) : (lift R G s f hf x).1 ⟨hN⟩ = f hN x := rfl

theorem proj_comp_lift {N} (hN : N ∈ s) : (proj R G s hN).comp (lift R G s f hf) = f hN := rfl

/-- The lift map `S → CompleteGroupAlgebra R G s` is unique. -/
theorem eq_lift_of_proj_comp_eq (g : S →ₐ[R] CompleteGroupAlgebra R G s)
    (hg : ∀ ⦃N⦄, (hN : N ∈ s) → (proj R G s hN).comp g = f hN) : g = lift R G s f hf := by
  ext x N ⟨hN⟩ : 4
  simpa using congr($(hg hN) x)

end lift

section ofMonoidAlgebra

/-- The natural map from `R[ˣG]` to `CompleteGroupAlgebra R G s`. -/
noncomputable def ofMonoidAlgebra : R[ˣG] →ₐ[R] CompleteGroupAlgebra R G s :=
  lift R G s (fun N _ ↦ MonoidAlgebra.mapDomainAlgHom R R
    (QuotientGroup.mk' N.toSubgroup)) fun N₁ N₂ hN₁ hN₂ hle ↦ by
      rw [← MonoidAlgebra.mapDomainAlgHom_comp]
      rfl

@[simp]
theorem ofMonoidAlgebra_apply_coe (x : R[ˣG]) {N} (hN : N ∈ s) :
    (ofMonoidAlgebra R G s x).1 ⟨hN⟩ = MonoidAlgebra.mapDomainAlgHom R R
      (QuotientGroup.mk' N.toSubgroup) x := rfl

theorem proj_comp_ofMonoidAlgebra {N} (hN : N ∈ s) :
    (proj R G s hN).comp (ofMonoidAlgebra R G s) = MonoidAlgebra.mapDomainAlgHom R R
      (QuotientGroup.mk' N.toSubgroup) := rfl

theorem projOfExistsLE_comp_ofMonoidAlgebra
    (M : Subgroup G) [M.Normal] (hM : ∃ N ∈ s, N.toSubgroup ≤ M) :
    (projOfExistsLE R G s M hM).comp (ofMonoidAlgebra R G s) = MonoidAlgebra.mapDomainAlgHom R R
      (QuotientGroup.mk' M) := by
  rw [projOfExistsLE, AlgHom.comp_assoc, proj_comp_ofMonoidAlgebra,
    ← MonoidAlgebra.mapDomainAlgHom_comp]
  rfl

end ofMonoidAlgebra

section algHomOfCoinitial

variable (t u : Set (OpenNormalSubgroup G)) (hs : DirectedOn GE.ge s) (hts : IsCoinitialFor t s)
  (ht : DirectedOn GE.ge t) (hst : IsCoinitialFor s t) (hut : IsCoinitialFor u t)

/-- If `s` is directed and `t` is coinitial for `s`, then there is a natural map from
`CompleteGroupAlgebra R G s` to `CompleteGroupAlgebra R G t`. -/
noncomputable def algHomOfCoinitial : CompleteGroupAlgebra R G s →ₐ[R] CompleteGroupAlgebra R G t :=
  lift R G t (fun N hN ↦ projOfExistsLE R G s N.toSubgroup (hts hN)) fun N₁ N₂ hN₁ _ hle ↦
    mapDomainAlgHom_comp_projOfExistsLE R G s N₁.toSubgroup (hts hN₁) N₂.toSubgroup hle hs

@[simp]
theorem algHomOfCoinitial_self : algHomOfCoinitial R G s s hs .rfl = AlgHom.id R _ := by
  refine (eq_lift_of_proj_comp_eq R G s _ fun N hN ↦ ?_).symm
  rw [AlgHom.comp_id]
  exact (projOfExistsLE_eq_proj R G s hN).symm

@[simp]
theorem algHomOfCoinitial_comp :
    (algHomOfCoinitial R G t u ht hut).comp (algHomOfCoinitial R G s t hs hts) =
      algHomOfCoinitial R G s u hs (hut.trans hts) := by
  refine eq_lift_of_proj_comp_eq R G u _ fun N hN ↦ ?_
  rw [← AlgHom.comp_assoc, algHomOfCoinitial, proj_comp_lift, algHomOfCoinitial, projOfExistsLE,
    AlgHom.comp_assoc, proj_comp_lift]
  exact mapDomainAlgHom_comp_projOfExistsLE R G s _ _ _ _ hs

/-- If `s`, `t` are directed and are coinitial for each other, then there is a natural isomorphism
of `CompleteGroupAlgebra R G s` and `CompleteGroupAlgebra R G t`. -/
noncomputable def algEquivOfCoinitial :
    CompleteGroupAlgebra R G s ≃ₐ[R] CompleteGroupAlgebra R G t :=
  .ofAlgHom (algHomOfCoinitial R G s t hs hts) (algHomOfCoinitial R G t s ht hst)
    (by simp) (by simp)

@[simp]
theorem coe_algEquivOfCoinitial : algEquivOfCoinitial R G s t hs hts ht hst =
    algHomOfCoinitial R G s t hs hts := rfl

@[simp]
theorem algEquivOfCoinitial_symm : (algEquivOfCoinitial R G s t hs hts ht hst).symm =
    algEquivOfCoinitial R G t s ht hst hs hts := rfl

theorem coe_algEquivOfCoinitial_symm : (algEquivOfCoinitial R G s t hs hts ht hst).symm =
    algHomOfCoinitial R G t s ht hst := rfl

@[simp]
theorem algEquivOfCoinitial_apply (x) : algEquivOfCoinitial R G s t hs hts ht hst x =
    algHomOfCoinitial R G s t hs hts x := rfl

theorem algEquivOfCoinitial_symm_apply (x) : (algEquivOfCoinitial R G s t hs hts ht hst).symm x =
    algHomOfCoinitial R G t s ht hst x := rfl

end algHomOfCoinitial

/-! ## Elements of form `r • [g]` -/

section single

/-- The linear map which maps `r` to `r • [g]` in `R⟦ˣG⟧`. -/
noncomputable def single (g : G) : R →ₗ[R] CompleteGroupAlgebra R G s where
  toFun r := ⟨fun _ _ ↦ .single (QuotientGroup.mk g) r,
    fun _ _ _ _ _ ↦ MonoidAlgebra.mapDomain_single⟩
  map_add' _ _ := by ext : 3; simp
  map_smul' _ _ := by ext : 3; simp

@[simp]
theorem single_apply_coe (g : G) (r : R) {N} (hN : N ∈ s) :
    (single R G s g r).1 ⟨hN⟩ = .single (QuotientGroup.mk g) r := rfl

theorem one_def : (1 : CompleteGroupAlgebra R G s) = single R G s 1 1 := by
  ext N ⟨hN⟩ : 3
  simp [MonoidAlgebra.one_def]

@[simp]
theorem projOfExistsLE_single (M : Subgroup G) [M.Normal] (hM : ∃ N ∈ s, N.toSubgroup ≤ M)
    (g : G) (r : R) :
    projOfExistsLE R G s M hM (single R G s g r) = .single (QuotientGroup.mk g) r := by
  simp [projOfExistsLE]

@[simp]
theorem augmentation_single (hs : s.Nonempty) (g : G) (r : R) :
    augmentation R G s hs (single R G s g r) = r := by
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  simp [augmentation, Subsingleton.elim _ (1 : G ⧸ (⊤ : Subgroup G))]

@[simp]
theorem ofMonoidAlgebra_single (g : G) (r : R) :
    ofMonoidAlgebra R G s (.single g r) = single R G s g r := by
  ext N ⟨hN⟩ : 3
  simp

@[simp]
theorem algHomOfCoinitial_single (t : Set (OpenNormalSubgroup G)) (hs : DirectedOn GE.ge s)
    (hts : IsCoinitialFor t s) (g : G) (r : R) :
    algHomOfCoinitial R G s t hs hts (single R G s g r) = single R G t g r := by
  ext N ⟨hN⟩ : 3
  simp [algHomOfCoinitial]

-- theorem proj_surjective (N : OpenNormalSubgroup G) :
--     Function.Surjective (proj R N) := fun f ↦ by
--   have := MonoidAlgebra.sum_single f
--   sorry

end single

end CompleteGroupAlgebra
