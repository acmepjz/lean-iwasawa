/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Iwasawalib.Algebra.InverseLimit.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Iwasawalib.Topology.Algebra.OpenSubgroup

/-!

# Complete group algebras

In this file we state basic definitions of complete group algebras.

We introduce the scoped notation `R[ˣG]` for the `MonoidAlgebra`.

If `R` is a commutative semiring, `G` is a topological group,
then `CompleteGroupAlgebra R G` (with scpoed notation `R⟦ˣG⟧`)
is defined to be the inverse limit of `R[ˣG/N]` (`Algebra.InverseLimit`)
as `N` runs over all open normal subgroups of `G`.

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

end Semiring

section Monoid

variable [CommSemiring R] [Monoid G]

/-- The `augmentation` is the map from `R[ˣG]` to `R`. -/
noncomputable def augmentation : R[ˣG] →ₐ[R] R :=
  liftNCAlgHom (AlgHom.id R R) 1 (fun r g ↦ by simp)

theorem augmentation_toLinearMap : (augmentation R G : R[ˣG] →ₗ[R] R) =
    Finsupp.linearCombination R fun _ ↦ (1 : R) := rfl

theorem augmentation_apply (x : R[ˣG]) : augmentation R G x = Finsupp.sum x fun _ r ↦ r := by
  convert Finsupp.linearCombination_apply R x
  simp

@[simp]
theorem augmentation_single (g : G) (r : R) : augmentation R G (single g r) = r := by
  simp [augmentation_apply]

theorem augmentation_comp_lsingle (g : G) :
    (augmentation R G : R[ˣG] →ₗ[R] R) ∘ₗ lsingle g = .id := by
  ext1; simp

theorem augmentation_surjective : Function.Surjective (augmentation R G) :=
  (show Function.LeftInverse _ _ from augmentation_single R G 1).surjective

@[simp]
theorem augmentation_comp_mapDomainAlgHom (H : Type*) [Monoid H] (f : G →* H) :
    (augmentation R H).comp (mapDomainAlgHom R R f) = augmentation R G := by
  ext g
  simp

end Monoid

end MonoidAlgebra

open scoped MonoidAlgebra

variable (R : Type*) [CommSemiring R] (G : Type*) [Group G] [TopologicalSpace G]

/-! ## Definition of complete group algebra -/

/-- The `CompleteGroupAlgebra R G` (with scpoed notation `R⟦ˣG⟧`) is the inverse limit
(`Algebra.InverseLimit`) of `R[ˣG/N]` as `N` runs over open normal subgroups of `G`. -/
abbrev CompleteGroupAlgebra := Algebra.InverseLimit (I := (OpenNormalSubgroup G)ᵒᵈ)
  fun (N₁ N₂ : OpenNormalSubgroup G) (hle : N₂ ≤ N₁) ↦ MonoidAlgebra.mapDomainAlgHom R R
    (QuotientGroup.map N₂.toSubgroup N₁.toSubgroup (MonoidHom.id G) hle)

namespace CompleteGroupAlgebra

@[inherit_doc]
scoped notation:9000 R:max "⟦ˣ" G "⟧" => CompleteGroupAlgebra R G

@[ext]
theorem ext {x y : R⟦ˣG⟧} (hxy : ∀ N : OpenNormalSubgroup G, x.1 N = y.1 N) : x = y := by
  ext N : 2
  exact hxy N

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

theorem eq_of_proj_comp_eq {S : Type*} [Semiring S] [Algebra R S] {f g : S →ₐ[R] R⟦ˣG⟧}
    (hfg : ∀ N : OpenNormalSubgroup G, (proj R G N).comp f = (proj R G N).comp g) : f = g :=
  Algebra.InverseLimit.eq_of_proj_comp_eq _ hfg

end proj

section augmentation

/-- The `augmentation` is the map from `R⟦ˣG⟧` to `R`. -/
noncomputable def augmentation : R⟦ˣG⟧ →ₐ[R] R :=
  (MonoidAlgebra.augmentation R _).comp (proj R G ⊤)

-- should not be a simp lemma
theorem augmentation_apply (x : R⟦ˣG⟧) : augmentation R G x = x.1 (⊤ : OpenNormalSubgroup G) 1 := by
  rw [augmentation, AlgHom.comp_apply, proj_apply]
  generalize x.1 (⊤ : OpenNormalSubgroup G) = y
  have : Subsingleton (G ⧸ (⊤ : OpenNormalSubgroup G).toSubgroup) :=
    QuotientGroup.subsingleton_quotient_top
  induction y using MonoidAlgebra.induction_on with
  | hM g => simp [Subsingleton.elim g 1]
  | hadd x y hx hy => simp only [map_add, hx, hy, Finsupp.add_apply x y]
  | hsmul r x hx => simp only [map_smul, hx, Finsupp.smul_apply r x]

theorem augmentation_eq_augmentation_comp_proj (N : OpenNormalSubgroup G) :
    augmentation R G = (MonoidAlgebra.augmentation R _).comp (proj R G N) := by
  have hle : N ≤ ⊤ := fun x _ ↦ Set.mem_univ x
  rw [augmentation, ← mapDomainAlgHom_comp_proj R G hle, ← AlgHom.comp_assoc,
    MonoidAlgebra.augmentation_comp_mapDomainAlgHom]

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
  Algebra.InverseLimit.eq_lift_of_proj_comp_eq _ g hg

theorem ker_lift_eq_iInf :
    RingHom.ker (lift R G f hf) = ⨅ N : OpenNormalSubgroup G, RingHom.ker (f N) :=
  Algebra.InverseLimit.ker_lift_eq_iInf ..

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
      (QuotientGroup.mk' N.toSubgroup) x := lift_apply_coe ..

theorem proj_comp_ofMonoidAlgebra (N : OpenNormalSubgroup G) :
    (proj R G N).comp (ofMonoidAlgebra R G) = MonoidAlgebra.mapDomainAlgHom R R
      (QuotientGroup.mk' N.toSubgroup) := proj_comp_lift ..

theorem proj_surjective (N : OpenNormalSubgroup G) :
    Function.Surjective (proj R G N) := by
  suffices Function.Surjective ((proj R G N).comp (ofMonoidAlgebra R G)) from .of_comp this
  rw [proj_comp_ofMonoidAlgebra]
  exact Finsupp.mapDomain_surjective QuotientGroup.mk_surjective

theorem augmentation_surjective : Function.Surjective (augmentation R G) :=
  (MonoidAlgebra.augmentation_surjective R _).comp (proj_surjective R G ⊤)

theorem ker_ofMonoidAlgebra_eq_iInf :
    RingHom.ker (ofMonoidAlgebra R G) = ⨅ N : OpenNormalSubgroup G,
      RingHom.ker (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.mk' N.toSubgroup)) :=
  ker_lift_eq_iInf ..

/-- If `G` is a profinite group (i.e. it is `CompactSpace` and `TotallyDisconnectedSpace`),
then the natural map `R[ˣG] → R⟦ˣG⟧` is injective. -/
theorem ofMonoidAlgebra_injective [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] : Function.Injective (ofMonoidAlgebra R G) := fun x y hxy ↦ by
  let s : Set G := x.support ∪ y.support
  let t := (fun a b ↦ a⁻¹ * b).uncurry '' s ×ˢ s ∩ {x | x ≠ 1}
  have ht := Set.toFinite t
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    ht.isClosed.isOpen_compl (by simp [t])
  have hinj : s.InjOn (QuotientGroup.mk' N.toSubgroup) := fun a ha b hb hab ↦ by
    have h := hN (QuotientGroup.eq.1 hab)
    simp only [Set.image_uncurry_prod, ne_eq, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_image2,
      Set.mem_setOf_eq, not_and, not_not, forall_exists_index, and_imp, t, inv_mul_eq_one] at h
    exact h a ha b hb rfl
  apply_fun proj R G N at hxy
  simp_rw [proj_apply, ofMonoidAlgebra_apply_coe, MonoidAlgebra.mapDomainAlgHom_apply] at hxy
  ext1 g
  by_cases hg : g ∈ s
  · rw [← Finsupp.mapDomain_apply' s x Set.subset_union_left hinj hg,
      ← Finsupp.mapDomain_apply' s y Set.subset_union_right hinj hg, hxy]
  · rw [(Finsupp.support_subset_iff (f := x)).1 Set.subset_union_left g hg,
      (Finsupp.support_subset_iff (f := y)).1 Set.subset_union_right g hg]

end ofMonoidAlgebra

/-! ## Elements of form `r • [g]` -/

section single

variable (g g' : G) (r r' : R) (n : ℕ) (N : OpenNormalSubgroup G)

/-- The linear map which maps `r` to `r • [g]` in `R⟦ˣG⟧`. -/
noncomputable def single : R →ₗ[R] R⟦ˣG⟧ where
  toFun r := ⟨fun _ ↦ .single (QuotientGroup.mk g) r, fun _ _ _ ↦ MonoidAlgebra.mapDomain_single⟩
  map_add' _ _ := by aesop
  map_smul' _ _ := by aesop

@[simp]
theorem single_apply_coe : (single R G g r).1 N = .single (QuotientGroup.mk g) r := rfl

theorem proj_comp_single : (proj R G N : R⟦ˣG⟧ →ₗ[R] R[ˣG ⧸ N.toSubgroup]) ∘ₗ single R G g =
    MonoidAlgebra.lsingle (QuotientGroup.mk g) := by
  ext1; simp

theorem one_def : (1 : R⟦ˣG⟧) = single R G 1 1 := by
  ext1; simp [MonoidAlgebra.one_def]

@[simp]
theorem augmentation_single : augmentation R G (single R G g r) = r := by
  simp [augmentation_eq_augmentation_comp_proj R G default]

theorem augmentation_comp_single : (augmentation R G : R⟦ˣG⟧ →ₗ[R] R) ∘ₗ single R G g = .id := by
  ext1; simp

@[simp]
theorem ofMonoidAlgebra_single : ofMonoidAlgebra R G (.single g r) = single R G g r := by
  ext1; simp

theorem ofMonoidAlgebra_comp_lsingle :
    (ofMonoidAlgebra R G : R[ˣG] →ₗ[R] R⟦ˣG⟧) ∘ₗ MonoidAlgebra.lsingle g = single R G g := by
  ext1; simp

theorem single_injective : Function.Injective (single R G g) :=
  (show Function.LeftInverse _ _ from augmentation_single R G g).injective

@[simp]
theorem single_eq_zero : single R G g r = 0 ↔ r = 0 :=
  ⟨fun h ↦ single_injective R G g (by rw [h, map_zero]), fun h ↦ by rw [h, map_zero]⟩

theorem single_ne_zero : single R G g r ≠ 0 ↔ r ≠ 0 := (single_eq_zero R G g r).ne

@[simp]
theorem single_mul_single :
    single R G g r * single R G g' r' = single R G (g * g') (r * r') := by
  ext1; simp

@[simp]
theorem single_pow : single R G g r ^ n = single R G (g ^ n) (r ^ n) := by
  ext1; simp

end single

/-! ## The map `g ↦ [g]` -/

section of

variable (N : OpenNormalSubgroup G)

/-- The map which maps `g` to `[g]` in `R⟦ˣG⟧`. -/
@[simps! apply]
noncomputable def of : G →* R⟦ˣG⟧ :=
  (ofMonoidAlgebra R G : R[ˣG] →* R⟦ˣG⟧).comp (MonoidAlgebra.of R G)

theorem proj_comp_of : (proj R G N : R⟦ˣG⟧ →* R[ˣG ⧸ N.toSubgroup]).comp (of R G) =
    (MonoidAlgebra.of R _).comp (QuotientGroup.mk' _) := by
  ext1; simp

/-- If `G` is a profinite group (i.e. it is `CompactSpace` and `TotallyDisconnectedSpace`) and
`R` is not trivial, then the map `G → R⟦ˣG⟧`, `g ↦ [g]` is injective. -/
theorem of_injective [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [Nontrivial R] : Function.Injective (of R G) :=
  (ofMonoidAlgebra_injective R G).comp MonoidAlgebra.of_injective

end of

/-! ## The map `R⟦ˣG⟧ → R⟦ˣH⟧` induced by `G → H` -/

section map

variable {G} {H : Type*} [Group H] [TopologicalSpace H] (f : G →* H) (hf : Continuous f)

/-- The map `R⟦ˣG⟧ → R⟦ˣH⟧` induced by a continuous group homomorphism `G → H`. -/
noncomputable def map : R⟦ˣG⟧ →ₐ[R] R⟦ˣH⟧ :=
  lift R H
    (fun N ↦ (MonoidAlgebra.mapDomainAlgHom R R
      (QuotientGroup.map (N.comap f hf).toSubgroup N.toSubgroup f le_rfl)).comp
        (proj R G (N.comap f hf)))
    fun N₁ N₂ hle ↦ by
      dsimp only
      have hle' : N₁.comap f hf ≤ N₂.comap f hf := Subgroup.comap_mono hle
      rw [← mapDomainAlgHom_comp_proj R G hle']
      simp_rw [← AlgHom.comp_assoc, ← MonoidAlgebra.mapDomainAlgHom_comp]
      congr 2
      ext; simp

theorem map_apply_coe (x : R⟦ˣG⟧) (N : OpenNormalSubgroup H) :
    (map R f hf x).1 N = MonoidAlgebra.mapDomainAlgHom R R
      (QuotientGroup.map (N.comap f hf).toSubgroup N.toSubgroup f le_rfl)
        (proj R G (N.comap f hf) x) := lift_apply_coe ..

theorem proj_comp_map (N : OpenNormalSubgroup H) :
    (proj R H N).comp (map R f hf) = (MonoidAlgebra.mapDomainAlgHom R R
      (QuotientGroup.map (N.comap f hf).toSubgroup N.toSubgroup f le_rfl)).comp
        (proj R G (N.comap f hf)) := proj_comp_lift ..

@[simp]
theorem map_single (g : G) (r : R) : map R f hf (single R G g r) = single R H (f g) r := by
  ext1 N
  rw [map_apply_coe, proj_apply]
  simp

theorem map_comp_ofMonoidAlgebra : (map R f hf).comp (ofMonoidAlgebra R G) =
    (ofMonoidAlgebra R H).comp (MonoidAlgebra.mapDomainAlgHom R R f) := by
  ext x : 2
  simp

theorem map_comp_of : (map R f hf : R⟦ˣG⟧ →* R⟦ˣH⟧).comp (of R G) = (of R H).comp f := by
  ext1; simp

@[simp]
theorem augmentation_map (x : R⟦ˣG⟧) : augmentation R H (map R f hf x) = augmentation R G x := by
  have h : OpenNormalSubgroup.comap f hf ⊤ = ⊤ := by
    ext x
    exact propext_iff.1 congr(x ∈ $(Subgroup.comap_top f))
  rw [augmentation, AlgHom.comp_apply, ← (proj R H _).comp_apply, proj_comp_map,
    ← mapDomainAlgHom_comp_proj R _ h.ge, augmentation, ← AlgHom.comp_apply]
  simp_rw [← AlgHom.comp_assoc]
  congr 2
  rw [AlgHom.comp_assoc, ← MonoidAlgebra.mapDomainAlgHom_comp,
    MonoidAlgebra.augmentation_comp_mapDomainAlgHom]

@[simp]
theorem augmentation_comp_map : (augmentation R H).comp (map R f hf) = augmentation R G :=
  AlgHom.ext (augmentation_map R f hf)

variable (G) in
@[simp]
theorem map_id : map R (MonoidHom.id G) continuous_id = AlgHom.id R _ := by
  refine eq_of_proj_comp_eq R _ fun N ↦ ?_
  rw [AlgHom.comp_id, proj_comp_map, mapDomainAlgHom_comp_proj]

variable {K : Type*} [Group K] [TopologicalSpace K] (g : H →* K) (hg : Continuous g)

theorem map_comp_map : (map R g hg).comp (map R f hf) = map R (g.comp f) (hg.comp hf) := by
  refine eq_of_proj_comp_eq R _ fun N ↦ ?_
  rw [proj_comp_map, ← AlgHom.comp_assoc, proj_comp_map, AlgHom.comp_assoc, proj_comp_map,
    ← AlgHom.comp_assoc, ← MonoidAlgebra.mapDomainAlgHom_comp]
  congr 2
  ext; rfl

end map

/-! ## The map `R⟦ˣG⟧ ≃ R⟦ˣH⟧` induced by `G ≃ H` -/

section congr

variable {G} {H : Type*} [Group H] [TopologicalSpace H] (f : G ≃ₜ* H)

/-- The map `R⟦ˣG⟧ ≃ R⟦ˣH⟧` induced by a continuous group isomorphism `G ≃ H`. -/
noncomputable def congr : R⟦ˣG⟧ ≃ₐ[R] R⟦ˣH⟧ where
  __ := map R f f.continuous
  invFun := map R f.symm f.symm.continuous
  left_inv x := by
    convert congr($(map_comp_map R (f : G →* H) f.continuous (f.symm : H →* G) f.symm.continuous) x)
    conv_lhs => rw [← AlgHom.id_apply (R := R) x, ← map_id]
    congr 2
    ext; simp
  right_inv x := by
    convert congr($(map_comp_map R (f.symm : H →* G) f.symm.continuous (f : G →* H) f.continuous) x)
    conv_lhs => rw [← AlgHom.id_apply (R := R) x, ← map_id]
    congr 2
    ext; simp

@[simp]
theorem coe_congr : (congr R f : R⟦ˣG⟧ →ₐ[R] R⟦ˣH⟧) = map R f f.continuous := rfl

@[simp]
theorem congr_symm : (congr R f).symm = congr R f.symm := rfl

theorem coe_congr_symm :
  ((congr R f).symm : R⟦ˣH⟧ →ₐ[R] R⟦ˣG⟧) = map R f.symm f.symm.continuous := rfl

@[simp]
theorem congr_single (g : G) (r : R) : congr R f (single R G g r) = single R H (f g) r :=
  map_single R (f : G →* H) f.continuous g r

variable (G) in
@[simp]
theorem congr_refl : congr R (.refl G) = AlgEquiv.refl := by
  ext1 x
  exact congr($(map_id R G) x)

variable {K : Type*} [Group K] [TopologicalSpace K] (g : H ≃ₜ* K)

theorem congr_trans_congr : (congr R f).trans (congr R g) = congr R (f.trans g) := by
  ext1 x
  exact congr($(map_comp_map R (f : G →* H) f.continuous (g : H →* K) g.continuous) x)

end congr

/-! ## Isomorphism to inverse limit by taking a neighborhood basis -/

section equivInverseLimit

variable {G} {I : Type*} [Preorder I] (N : I → OpenNormalSubgroup G)
  (hN : (nhds (1 : G)).HasAntitoneBasis fun i ↦ N i)

/-- If `{ N_i }` is a family of open normal subgroups forming a neighborhood basis of `1`,
then given any open normal subgroup `M`, there exists `i` such that `N_i ≤ M`. -/
noncomputable def equivInverseLimit.auxIndex (M : OpenNormalSubgroup G) : I :=
  (hN.mem_iff.1 <| M.isOpen.mem_nhds_iff.2 (one_mem _)).choose

theorem equivInverseLimit.auxIndex_spec (M : OpenNormalSubgroup G) : N (auxIndex N hN M) ≤ M :=
  (hN.mem_iff.1 <| M.isOpen.mem_nhds_iff.2 (one_mem _)).choose_spec

open equivInverseLimit

/-- If `{ N_i }` is a family of open normal subgroups forming a neighborhood basis of `1`,
then `CompleteGroupAlgebra.InverseLimit` is the inverse limit of `R[ˣG/N_i]`. -/
abbrev InverseLimit := Algebra.InverseLimit
  fun (i i' : I) (hle : i ≤ i') ↦ MonoidAlgebra.mapDomainAlgHom R R
    (QuotientGroup.map (N i').toSubgroup (N i).toSubgroup (MonoidHom.id G)
      (hN.antitone hle))

/-- If `{ N_i }` is a family of open normal subgroups forming a neighborhood basis of `1`,
then there is a map from `R⟦ˣG⟧` to the inverse limit of `R[ˣG/N_i]`. -/
noncomputable def toInverseLimit : R⟦ˣG⟧ →ₐ[R] InverseLimit R N hN :=
  Algebra.InverseLimit.lift _ (fun i ↦ proj R G (N i)) fun _ _ hle ↦
    mapDomainAlgHom_comp_proj R G (hN.antitone hle)

variable [IsDirected I LE.le]

/-- If `{ N_i }` is a family of open normal subgroups forming a neighborhood basis of `1`,
then there is a map from the inverse limit of `R[ˣG/N_i]` to `R⟦ˣG⟧`. -/
noncomputable def ofInverseLimit : InverseLimit R N hN →ₐ[R] R⟦ˣG⟧ :=
  lift R G (fun M ↦ (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map
    (N (auxIndex N hN M)).toSubgroup M.toSubgroup (MonoidHom.id G) (auxIndex_spec N hN M))).comp
      (Algebra.InverseLimit.proj _ (auxIndex N hN M)))
    fun N₁ N₂ hle ↦ by
      dsimp only
      obtain ⟨i, hi₁, hi₂⟩ := directed_of LE.le (auxIndex N hN N₁) (auxIndex N hN N₂)
      rw [← Algebra.InverseLimit.algHom_comp_proj _ hi₁,
        ← Algebra.InverseLimit.algHom_comp_proj _ hi₂]
      simp_rw [← AlgHom.comp_assoc, ← MonoidAlgebra.mapDomainAlgHom_comp]
      congr 2
      ext; rfl

theorem toInverseLimit_comp_ofInverseLimit :
    (toInverseLimit R N hN).comp (ofInverseLimit R N hN) = AlgHom.id _ _ := by
  unfold toInverseLimit ofInverseLimit
  ext x i : 3
  simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.InverseLimit.lift_apply_coe, proj_apply,
    lift_apply_coe, Algebra.InverseLimit.proj_apply, AlgHom.id_apply]
  obtain ⟨j, h1, h2⟩ := directed_of LE.le (auxIndex N hN (N i)) i
  conv_lhs => rw [← Algebra.InverseLimit.proj_apply,
    ← Algebra.InverseLimit.algHom_comp_proj _ h1]
  conv_rhs => rw [← Algebra.InverseLimit.proj_apply,
    ← Algebra.InverseLimit.algHom_comp_proj _ h2]
  simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.InverseLimit.proj_apply]
  simp_rw [← AlgHom.comp_apply, ← MonoidAlgebra.mapDomainAlgHom_comp]
  congr 2
  ext; rfl

theorem ofInverseLimit_comp_toInverseLimit :
    (ofInverseLimit R N hN).comp (toInverseLimit R N hN) = AlgHom.id _ _ := by
  unfold toInverseLimit ofInverseLimit
  ext x M : 2
  conv_rhs => rw [AlgHom.id_apply, ← proj_apply,
    ← mapDomainAlgHom_comp_proj R G (auxIndex_spec N hN M)]
  simp

/-- If `{ N_i }` is a family of open normal subgroups forming a neighborhood basis of `1`,
then there is an isomorphism from `R⟦ˣG⟧` to the inverse limit of `R[ˣG/N_i]`. -/
noncomputable def equivInverseLimit : R⟦ˣG⟧ ≃ₐ[R] InverseLimit R N hN :=
  AlgEquiv.ofAlgHom (toInverseLimit R N hN) (ofInverseLimit R N hN)
    (toInverseLimit_comp_ofInverseLimit R N hN)
    (ofInverseLimit_comp_toInverseLimit R N hN)

end equivInverseLimit

end CompleteGroupAlgebra
