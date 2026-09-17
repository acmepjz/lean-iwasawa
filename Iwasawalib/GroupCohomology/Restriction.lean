module

public import Iwasawalib.GroupCohomology.CFTLowDegree
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

@[expose] public section

open Rep CategoryTheory ConcreteCategory Limits groupCohomology BigOperators

universe t w w' u v0 v1 v2

variable {R : Type u} {G : Type v0} {H : Type v1} {K : Type v2} [CommRing R]

noncomputable section

namespace Rep

notation3:60 M:60 " ↓ " f:61 => res f M

section monoid

variable [Monoid G] [Monoid H] [Monoid K]

abbrev resComp (f : H →* G) (g : K →* H) :
    resFunctor (f.comp g) ≅ resFunctor (k := R) f ⋙ resFunctor g :=
  NatIso.ofComponents (fun A ↦ mkIso (.mk (LinearEquiv.refl _ _) <| fun _ ↦ by simp))

abbrev resCongr {f1 f2 : H →* G} (h : f1 = f2) :
    resFunctor.{w} (k := R) f1 ≅ resFunctor f2 :=
  NatIso.ofComponents (fun A ↦ mkIso (.mk (LinearEquiv.refl _ _) <| fun _ ↦ by simp [h]))

set_option backward.isDefEq.respectTransparency false in
variable (R) in
def resEquiv (f : H ≃* G) : Rep.{w} R G ≌ Rep.{w} R H where
  functor := resFunctor f.toMonoidHom
  inverse := resFunctor f.symm.toMonoidHom
  unitIso := resCongr f.coe_monoidHom_comp_coe_monoidHom_symm.symm ≪≫ resComp _ _
  counitIso := (resComp _ _).symm ≪≫ resCongr f.coe_monoidHom_symm_comp_coe_monoidHom

@[simp] lemma resEquiv_functor (f : H ≃* G) :
    (resEquiv R f).functor = resFunctor f := rfl

@[simp] lemma resEquiv_inverse (f : H ≃* G) :
    (resEquiv R f).inverse = resFunctor f.symm := rfl

variable (φ : H →* G)

instance : Limits.HasLimits (Rep.{w} R G) :=
  Adjunction.has_limits_of_equivalence toModuleMonoidAlgebra

instance : Limits.HasColimits (Rep.{w} R G) :=
  Adjunction.has_colimits_of_equivalence toModuleMonoidAlgebra

instance : Limits.ReflectsLimitsOfSize.{w, w}
    (forget₂ (Rep.{w} R G) (ModuleCat R)) :=
  Limits.reflectsLimits_of_reflectsIsomorphisms

instance : Limits.PreservesLimits (resFunctor.{w} (k := R) φ) :=
  have : PreservesLimitsOfSize.{w, w}
      (resFunctor φ ⋙ forget₂ (Rep.{w} R H) (ModuleCat R)) :=
    inferInstanceAs (PreservesLimitsOfSize.{w, w} (forget₂ (Rep.{w} R G) (ModuleCat R)))
  preservesLimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} R H) (ModuleCat R))

instance : Limits.ReflectsColimitsOfSize.{w, w}
    (forget₂ (Rep.{w} R H) (ModuleCat R)) :=
  reflectsColimits_of_reflectsIsomorphisms

instance : Limits.PreservesColimits (resFunctor.{w} (k := R) φ) :=
  have : PreservesColimitsOfSize.{w, w}
      (resFunctor (k := R) φ ⋙ forget₂ (Rep.{w} R H) (ModuleCat R)) :=
    inferInstanceAs (PreservesColimitsOfSize.{w, w} (forget₂ (Rep.{w} R G) (ModuleCat R)))
  preservesColimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} R H) (ModuleCat R))

lemma res_map_ShortComplex_Exact (φ : H →* G)
    (S : ShortComplex (Rep.{u} R G)) [Small.{u} R] :
    (S.map (resFunctor φ)).Exact ↔ S.Exact := by
  rw [ShortComplex.exact_map_iff_of_faithful]

end monoid

section

@[simp] lemma norm_hom_res [Group G] [Group H] [Fintype G] [Fintype H]
    (M : Rep.{w} R G) (e : H ≃* G) :
    (res e.toMonoidHom M).norm.hom.toLinearMap = M.norm.hom.toLinearMap := by
  ext
  simp [res_obj_V, norm, Representation.norm, res_obj_ρ, ← e.toEquiv.sum_comp]

end

end Rep

namespace groupCohomology

variable {G S S' : Type u} [Group G] [Group S] (φ : S →* G)
  [Group S'] (ψ : S' →* S) {M : Rep.{u} R G}

set_option backward.defeqAttrib.useBackward true in
def rest (n : ℕ) : functor R G n ⟶ Rep.resFunctor φ ⋙ functor R S n where
  app M := map φ (𝟙 (M ↓ φ)) n
  naturality M₁ M₂ f := by
    simp only [functor_obj, Functor.comp_obj, functor_map, Functor.comp_map]
    rw [← map_comp, ← map_comp]
    congr 1

lemma rest_app (n : ℕ) (M : Rep R G) :
    (rest φ n).app M = map φ (𝟙 (M ↓ φ)) n := rfl

lemma rest_id (n : ℕ) : rest (MonoidHom.id G) (R := R) n = 𝟙 (functor R G n) := by
  ext M : 2
  rw [rest_app]
  apply map_id

set_option backward.isDefEq.respectTransparency false in
lemma rest_comp (n : ℕ) :
    rest (φ.comp ψ) n = rest φ (R := R) n ≫ (𝟙 _ ◫ rest ψ n) := by
  ext M : 2
  simp only [rest_app, Functor.id_hcomp, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← map_comp]
  exact map_congr rfl rfl n

lemma rest_δ_naturality {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    {H : Type u} [Group H] (φ : H →* G) (i j : ℕ) (hij : i + 1 = j) :
    δ hS i j hij ≫ (rest φ j).app S.X₁ =
      (rest φ i).app S.X₃ ≫ δ ((shortExact_res φ).2 hS) i j hij := by
  let C₁ := S.map (cochainsFunctor R G)
  let C₂ := (S.map (resFunctor φ)).map (cochainsFunctor R H)
  have ses₁ : C₁.ShortExact := map_cochainsFunctor_shortExact hS
  have ses₂ : C₂.ShortExact := by
    apply map_cochainsFunctor_shortExact
    rwa [shortExact_res]
  let this : C₁ ⟶ C₂ := {
    τ₁ := cochainsMap φ (𝟙 (res φ S.X₁))
    τ₂ := cochainsMap φ (𝟙 (res φ S.X₂))
    τ₃ := cochainsMap φ (𝟙 (res φ S.X₃))
  }
  exact HomologicalComplex.HomologySequence.δ_naturality this ses₁ ses₂ i j hij

set_option backward.isDefEq.respectTransparency false in
noncomputable def resSubtypeRangeIso (M : Rep.{u} R G) {H : Type u}
    [Group H] (f : H →* G) (n : ℕ) (hf : Function.Injective f) :
    groupCohomology (M ↓ f.range.subtype) n ≅ groupCohomology (M ↓ f) n where
  hom := groupCohomology.map f.rangeRestrict (Rep.ofHom ⟨LinearMap.id, by simp⟩) _
  inv := groupCohomology.map (MonoidHom.ofInjective hf).symm.toMonoidHom
      (Rep.ofHom ⟨LinearMap.id, by simp⟩) _
  hom_inv_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    exact groupCohomology.map_congr (by ext; simp) (by rfl) n
  inv_hom_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    refine groupCohomology.map_congr (MonoidHom.ext fun x ↦ ?_) (by rfl) n
    rw [MonoidHom.comp_apply]
    exact (MonoidHom.ofInjective hf).symm_apply_apply _

end groupCohomology

namespace groupHomology

variable {G S S' : Type u} [Group G] [Group S] (φ : S →* G)
  [Group S'] (ψ : S' →* S) {M : Rep.{u} R G}

set_option backward.isDefEq.respectTransparency false in
noncomputable def resSubtypeRangeIso (M : Rep R G) {H : Type u}
    [Group H] (f : H →* G) (n : ℕ) (hf : Function.Injective f) :
    groupHomology (M ↓ f.range.subtype) n ≅ groupHomology (M ↓ f) n where
  hom := groupHomology.map (MonoidHom.ofInjective hf).symm.toMonoidHom
      (Rep.ofHom ⟨LinearMap.id (M := M.V), by simp⟩) _
  inv := groupHomology.map f.rangeRestrict (Rep.ofHom ⟨.id (M := M.V), by simp⟩) _
  hom_inv_id := by
    rw [← groupHomology.map_comp, ← groupHomology.map_id]
    exact groupHomology.map_congr (by ext; simp) (by simp) n
  inv_hom_id := by
    rw [← groupHomology.map_comp, ← groupHomology.map_id]
    refine groupHomology.map_congr (MonoidHom.ext fun x ↦ ?_) (by simp) n
    rw [MonoidHom.comp_apply]
    exact (MonoidHom.ofInjective hf).symm_apply_apply _

end groupHomology
