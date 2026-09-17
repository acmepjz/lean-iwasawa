module

public import Iwasawalib.GroupCohomology.CFTCompat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ConcreteCategory

set_option backward.isDefEq.respectTransparency false in
lemma CategoryTheory.ShortComplex.cocyclesMk_surjective
    {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type*}
    [(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasForget₂ C Ab] [Preadditive C] [(forget₂ C Ab).Additive]
    [(forget₂ C Ab).PreservesHomology] (S : ShortComplex C) [S.HasHomology]
    (x : ((forget₂ C Ab).obj S.cycles)) :
    ∃ (x₂ : ((forget₂ C Ab).obj S.X₂))
      (hx₂ : (ConcreteCategory.hom ((forget₂ C Ab).map S.g)) x₂ = 0),
      ShortComplex.cyclesMk _ x₂ hx₂ = x := by
  let y := (ShortComplex.abCyclesIso _).hom <| (S.mapCyclesIso (forget₂ C Ab)).inv x
  use y.1, y.2
  simp +zetaDelta [ShortComplex.cyclesMk]

lemma HomologicalComplex.cyclesMk_surjective
    {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type*}
    [(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasForget₂ C Ab] [Abelian C] [(forget₂ C Ab).Additive]
    [(forget₂ C Ab).PreservesHomology] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) {i : ι} (j : ι) (hj : c.next i = j)
    (x : ((forget₂ C Ab).obj (K.cycles i))) :
    ∃ (x₂ : ((forget₂ C Ab).obj (K.X i)))
      (hx₂ : (ConcreteCategory.hom ((forget₂ C Ab).map (K.d i j))) x₂ = 0),
      HomologicalComplex.cyclesMk K x₂ j hj hx₂ = x := by
  subst hj
  exact (K.sc i).cocyclesMk_surjective x

open groupCohomology

lemma groupCohomology.cocyclesMk_surjective.{u}
    {k G : Type u} [CommRing k] [Group G] {A : Rep k G}
    {n : ℕ} (x : cocycles A n) :
    ∃ (f : (Fin n → G) → A.V)
      (h : (ConcreteCategory.hom (inhomogeneousCochains.d A n)) f = 0),
      cocyclesMk f h = x := by
  obtain ⟨f, h, hf⟩ := (inhomogeneousCochains A).cyclesMk_surjective (n + 1) (by simp) x
  simp only [CochainComplex.of_X, ModuleCat.forget₂_obj, CochainComplex.of_d,
    ModuleCat.forget₂_map, AddCommGrpCat.hom_ofHom] at h
  exact ⟨f, h, hf⟩

namespace RepresentationTheory

universe u

variable {k G : Type u} [CommRing k] [Group G]

noncomputable def groupCohomology.zeroι (X : Rep k G) :
    H0 X ⟶ ModuleCat.of k X.V :=
  (H0Iso X).hom ≫ ModuleCat.ofHom (Submodule.subtype X.ρ.invariants)

@[reassoc (attr := simp)]
lemma groupCohomology.zeroι_naturality {X Y : Rep k G} (f : X ⟶ Y) :
    groupCohomology.map (.id _) f 0 ≫ groupCohomology.zeroι Y =
      zeroι X ≫ f.toModuleCatHom := by
  aesop (add simp zeroι)

set_option backward.defeqAttrib.useBackward true in
variable (k G) in
noncomputable def groupCohomology.zeroEmb :
    functor k G 0 ⟶ forget₂ (Rep k G) (ModuleCat k) where
  app X := groupCohomology.zeroι X

end RepresentationTheory

namespace groupCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] {A : Rep R G}

lemma H1_isZero_of_trivial (M : Rep R G) [IsAddTorsionFree M]
    [M.IsTrivial] [Finite G] : IsZero (H1 M) := by
  refine .of_iso ?_ (groupCohomology.H1IsoOfIsTrivial M)
  simp [subsingleton_addMonoidHom_of_isTorsion_isAddTorsionFree,
    is_add_torsion_of_finite]

namespace cocycles₂

@[simp, norm_cast] lemma coe_zero : ⇑(0 : cocycles₂ A) = 0 := rfl

@[simp, norm_cast] lemma coe_add (a b : cocycles₂ A) : ⇑(a + b) = a + b := rfl

@[simp, norm_cast] lemma coe_mk' (f : G × G → A) (hf) :
    ⇑(⟨f, hf⟩ : cocycles₂ A) = f := rfl

end cocycles₂

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma H2π_comp_H2Iso_hom :
    H2π A ≫ (H2Iso A).hom = (shortComplexH2 A).moduleCatLeftHomologyData.π := by
  simp [H2π]

end groupCohomology

open Finsupp

namespace groupHomology

variable {G : Type} [Group G]

@[simps! -isSimp]
def H1TrivialAddEquiv : H1 (.trivial ℤ G ℤ) ≃+ Additive (Abelianization G) :=
  (H1AddEquivOfIsTrivial _).trans (TensorProduct.rid ..).toAddEquiv

@[simp] lemma H1TrivialAddEquiv_single (g : G) (n : ℤ) :
    H1TrivialAddEquiv (H1π _ <| (cycles₁IsoOfIsTrivial _).inv <| single g n) =
      n • Additive.ofMul (Abelianization.of g) := by
  simp [H1TrivialAddEquiv, H1AddEquivOfIsTrivial_single (A := .trivial ℤ G ℤ)]

@[simp] lemma H1TrivialAddEquiv_symm (g : G) :
    H1TrivialAddEquiv.symm (.ofMul <| .of g) =
      H1π _ ((cycles₁IsoOfIsTrivial _).inv <| single g 1) := by
  rw [AddEquiv.symm_apply_eq, H1TrivialAddEquiv_single]
  simp

end groupHomology
