module

public import Iwasawalib.GroupCohomology.IndCoind.Basic
public import Iwasawalib.GroupCohomology.IndCoind.TrivialCohomology
public import Iwasawalib.GroupCohomology.TateCohomology
public import Iwasawalib.GroupCohomology.CFTCompat

@[expose] public noncomputable section

open
  Function
  Rep
  Representation
  CategoryTheory
  NatTrans
  ConcreteCategory
  Limits
  groupCohomology
  HomologicalComplex

universe u

variable {R G : Type u} [CommRing R] [Group G] (M : Rep.{u} R G)

namespace Rep.dimensionShift

@[simps, implicit_reducible]
def up : Rep.{u} R G ⥤ Rep.{u} R G where
  obj M := cokernel (coind₁'_ι.app M)
  map f := by
    apply cokernel.desc _ (coind₁'.map f ≫ cokernel.π _)
    rw [← Category.assoc, ← coind₁'_ι.naturality, Category.assoc, cokernel.condition, comp_zero]
  map_comp f g := by
    simp only [Functor.id_obj, Functor.map_comp, Category.assoc]
    apply coequalizer.hom_ext
    simp

abbrev up.π : coind₁'.obj M ⟶ up.obj M := cokernel.π (coind₁'_ι.app M)

@[simps, implicit_reducible]
def upSES : ShortComplex (Rep R G) where
  X₁ := M
  X₂ := coind₁'.obj M
  X₃ := up.obj M
  f := coind₁'_ι.app M
  g := up.π M
  zero := cokernel.condition (coind₁'_ι.app M)

lemma shortExact_upSES : (upSES M).ShortExact where
  exact := ShortComplex.exact_cokernel (coind₁'_ι.app M)
  mono_f := (inferInstance : Mono (coind₁'_ι.app M))
  epi_g := by dsimp; infer_instance

lemma shortExact_upSES_res {H : Type u} [Group H] (φ : H →* G) :
    ((upSES M).map (resFunctor φ)).ShortExact :=
  .map_of_exact (shortExact_upSES M) _

@[simps]
def upShortComplex : Rep.{u} R G ⥤ ShortComplex (Rep.{u} R G) where
  obj := upSES
  map f := {
    τ₁ := f
    τ₂ := coind₁'.map f
    τ₃ := up.map f
  }
  map_comp f g := by simp only [Functor.map_comp]; rfl

instance δ_up_zero_epi : Epi (δ (shortExact_upSES M) 0 1 rfl) := by
  refine epi_δ_of_isZero (shortExact_upSES M) 0 ?_
  simpa only [upSES_X₂, zero_add] using isZero_of_trivialCohomology

instance δ_up_isIso (n : ℕ) : IsIso (δ (shortExact_upSES M) (n + 1) (n + 2) rfl) := by
  refine isIso_δ_of_isZero (shortExact_upSES M) (n + 1) ?_ ?_ <;>
    simpa only [upSES_X₂] using isZero_of_trivialCohomology

@[simps! hom]
def δUpIso (n : ℕ) : groupCohomology (G := G) (up.obj M) (n + 1) ≅
    groupCohomology M (n + 2) :=
  asIso (δ (shortExact_upSES M) (n + 1) (n + 2) rfl)

def δUpNatIso (n : ℕ) : up ⋙ functor R G (n + 1) ≅ functor R G (n + 2) :=
  NatIso.ofComponents (fun M ↦ δUpIso M n) fun {M N} f ↦ .symm <| HomologySequence.δ_naturality
    ((upShortComplex ⋙ (cochainsFunctor R G).mapShortComplex).map f)
    (map_cochainsFunctor_shortExact (shortExact_upSES M))
    (map_cochainsFunctor_shortExact (shortExact_upSES N)) (n + 1) (n + 2) rfl

lemma epi_δ_up_zero_res {S : Type u} [Group S] {φ : S →* G} (inj : Injective φ) :
    Epi (δ ((shortExact_res φ).2 <| shortExact_upSES M) 0 1 rfl) := by
  refine epi_δ_of_isZero _ 0 ?_
  simpa only [ShortComplex.map_X₂, upSES_X₂, zero_add]
    using isZero_of_injective _ φ _ (by omega) inj

lemma isIso_δ_up_res {S : Type u} [Group S] {φ : S →* G} (inj : Injective φ)
    (n : ℕ) [NeZero n] :
    IsIso (δ ((shortExact_res φ).2 <| shortExact_upSES M) n (n + 1) rfl) := by
  refine isIso_δ_of_isZero _ n ?_ ?_ <;>
    simpa only [ShortComplex.map_X₂, upSES_X₂]
      using isZero_of_injective _ φ _ (NeZero.ne _) inj

def δUpResIso {S : Type u} [Group S] {φ : S →* G} (inj : Function.Injective φ)
    (n : ℕ) [NeZero n] :
    groupCohomology (up.obj M ↓ φ) n ≅ groupCohomology (M ↓ φ) (n + 1) := by
  have := isIso_δ_up_res M inj n
  apply asIso (δ ((shortExact_res φ).2 <| shortExact_upSES M) n (n + 1) rfl)

@[simps, implicit_reducible]
def down : Rep.{u} R G ⥤ Rep.{u} R G where
  obj M := kernel (ind₁'_π.app M)
  map φ := kernel.lift _ (kernel.ι _ ≫ ind₁'.map φ) (by
    rw [Category.assoc, ind₁'_π.naturality, ← Category.assoc, kernel.condition, zero_comp])
  map_comp f g := by
    simp only [Functor.id_obj, Functor.map_comp]
    apply equalizer.hom_ext
    simp

abbrev down.ι : down.obj M ⟶ ind₁'.obj M := kernel.ι (ind₁'_π.app M)

@[simps, implicit_reducible]
def downSES : ShortComplex (Rep R G) where
  X₁ := down.obj M
  X₂ := ind₁'.obj M
  X₃ := M
  f := down.ι M
  g := ind₁'_π.app M
  zero := kernel.condition (ind₁'_π.app M)

lemma shortExact_downSES : (downSES M).ShortExact where
  exact := ShortComplex.exact_kernel (ind₁'_π.app M)
  mono_f := by dsimp; infer_instance
  epi_g := (inferInstance : Epi (ind₁'_π.app M))

lemma shortExact_downSES_res {H : Type*} [Group H] (φ : H →* G) :
    ((downSES M).map (resFunctor φ)).ShortExact :=
  (shortExact_res φ).2 (shortExact_downSES M)

@[simps, implicit_reducible]
def downShortComplex : Rep.{u} R G ⥤ ShortComplex (Rep.{u} R G) where
  obj := downSES
  map f :=
  { τ₁ := down.map f
    τ₂ := ind₁'.map f
    τ₃ := f
    comm₂₃ := by
      ext : 2
      simp only [downSES_X₂, ind₁', downSES_X₃, downSES_g, ind₁'_π, hom_comp, hom_ofHom,
        IntertwiningMap.comp_toLinearMap]
      ext; simp }
  map_comp f g := by simp only [Functor.map_comp]; rfl

variable [Finite G]

instance epi_δ_down_zero : Epi (δ (shortExact_downSES M) 0 1 rfl) := by
  refine epi_δ_of_isZero (shortExact_downSES M) 0 ?_
  simpa only [downSES_X₂, zero_add] using isZero_of_trivialCohomology

lemma epi_δ_down_res_zero {S : Type u} [Group S] {φ : S →* G} (inj : Injective φ) :
    Epi (δ (shortExact_downSES_res M φ) 0 1 rfl) := by
  refine epi_δ_of_isZero (shortExact_downSES_res M φ) 0 ?_
  simpa only [downSES_X₂, ShortComplex.map_X₂, zero_add]
    using isZero_of_injective _ φ _ (by omega) inj

instance isIso_δ_down (n : ℕ) [NeZero n] :
    IsIso (δ (shortExact_downSES M) n (n + 1) rfl) := by
  apply isIso_δ_of_isZero <;> dsimp only [downSES_X₂] <;> exact isZero_of_trivialCohomology

lemma isIso_δ_down_res (n : ℕ) [NeZero n] {H : Type u} [Group H] {φ : H →* G}
    (inj : Injective φ) :
    IsIso (δ (shortExact_downSES_res M φ) n (n + 1) rfl) := by
  have := NeZero.ne n
  refine isIso_δ_of_isZero (shortExact_downSES_res M φ) n ?_ ?_ <;>
    simpa only [downSES_X₂, ShortComplex.map_X₂]
      using isZero_of_injective _ φ _ (by omega) inj

def δDownIso (n : ℕ) [NeZero n] :
    groupCohomology M n ≅ groupCohomology (down.obj M) (n + 1) :=
  asIso (δ (shortExact_downSES M) n (n + 1) rfl)

def δDownResIso {H : Type u} [Group H] {φ : H →* G} (inj : Injective φ)
    (n : ℕ) [NeZero n] :
    groupCohomology (M ↓ φ) n ≅ groupCohomology (down.obj M ↓ φ) (n + 1) :=
  @asIso _ _ _ _ (δ (shortExact_downSES_res M φ) n (n + 1) rfl)
    (isIso_δ_down_res M n inj)

def δDownNatIso (n : ℕ) [NeZero n] : functor R G n ≅ down ⋙ functor R G (n + 1) :=
  NatIso.ofComponents (fun M ↦ δDownIso M n) fun {M N} f ↦ .symm <| HomologySequence.δ_naturality
    ((downShortComplex ⋙ (cochainsFunctor R G).mapShortComplex).map f)
    (map_cochainsFunctor_shortExact (shortExact_downSES M))
    (map_cochainsFunctor_shortExact (shortExact_downSES N)) n (n + 1) rfl

end dimensionShift

end Rep

namespace groupCohomology

variable [Fintype G]
open Rep dimensionShift

private lemma isZero_of_trivialTateCohomology' (M : Rep R G)
    [M.TrivialTateCohomology] (n : ℤ) : IsZero (tateCohomology M n) :=
  TrivialTateCohomology.of_injective (.id G) _ Function.injective_id

instance instIsIso_shortExact_upSES (M : Rep R G) (n : ℤ) :
    IsIso (TateCohomology.δ (shortExact_upSES M) n) := by
  have _ : TrivialTateCohomology (coind₁'.obj M) := inferInstance
  exact ShortComplex.ShortExact.isIso_δ
    (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_upSES M))
    n (n + 1) rfl (by simpa using! isZero_of_trivialTateCohomology' (coind₁'.obj M) n)
    (by simpa using! isZero_of_trivialTateCohomology' (coind₁'.obj M) (n + 1))

instance instIsIso_shortExact_downSES (M : Rep R G) (n : ℤ) :
    IsIso (TateCohomology.δ (shortExact_downSES M) n) := by
  have _ : TrivialTateCohomology (ind₁'.obj M) := inferInstance
  exact ShortComplex.ShortExact.isIso_δ
    (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_downSES M))
    n (n + 1) rfl (by simpa using! isZero_of_trivialTateCohomology' (ind₁'.obj M) n)
    (by simpa using! isZero_of_trivialTateCohomology' (ind₁'.obj M) (n + 1))

@[simps! hom]
def δUpIsoTate (M : Rep R G) (n : ℤ) :
    tateCohomology (up.{u}.obj M) n ≅ tateCohomology M (n + 1) :=
  have := instIsIso_shortExact_upSES M n
  asIso (TateCohomology.δ (shortExact_upSES M) n)

@[simps! hom]
def δDownIsoTate (M : Rep R G) (n : ℤ) :
    tateCohomology M n ≅ tateCohomology (down.obj M) (n + 1) :=
  asIso (TateCohomology.δ (shortExact_downSES M) n)

def δUpResIsoTate {S : Type u} [Group S] [Fintype S] {φ : S →* G}
    (inj : Injective φ) (n : ℤ) :
    tateCohomology (up.obj M ↓ φ) n ≅ tateCohomology (M ↓ φ) (n + 1) := by
  let h := shortExact_upSES_res M φ
  have _ : TrivialTateCohomology (coind₁'.obj M) := inferInstance
  have hn : IsZero (tateCohomology (coind₁'.obj M ↓ φ) n) :=
    TrivialTateCohomology.of_injective φ n inj
  have hn1 : IsZero (tateCohomology (coind₁'.obj M ↓ φ) (n + 1)) :=
    TrivialTateCohomology.of_injective φ (n + 1) inj
  let hi : IsIso (TateCohomology.δ h n) := ShortComplex.ShortExact.isIso_δ
    (TateCohomology.map_tateComplexFunctor_shortExact h) n (n + 1) rfl
    (by
      change IsZero (tateCohomology (coind₁'.obj M ↓ φ) n)
      exact hn)
    (by
      change IsZero (tateCohomology (coind₁'.obj M ↓ φ) (n + 1))
      exact hn1)
  exact @asIso _ _ _ _ (TateCohomology.δ h n) hi

def δDownResIsoTate {H : Type u} [Group H] [Fintype H] {φ : H →* G}
    (inj : Injective φ) (n : ℤ) :
    tateCohomology (M ↓ φ) n ≅ tateCohomology (down.obj M ↓ φ) (n + 1) := by
  let h := shortExact_downSES_res M φ
  have _ : TrivialTateCohomology (ind₁'.obj M) := inferInstance
  have hn : IsZero (tateCohomology (ind₁'.obj M ↓ φ) n) :=
    TrivialTateCohomology.of_injective φ n inj
  have hn1 : IsZero (tateCohomology (ind₁'.obj M ↓ φ) (n + 1)) :=
    TrivialTateCohomology.of_injective φ (n + 1) inj
  let hi : IsIso (TateCohomology.δ h n) := ShortComplex.ShortExact.isIso_δ
    (TateCohomology.map_tateComplexFunctor_shortExact h) n (n + 1) rfl
    (by
      change IsZero (tateCohomology (ind₁'.obj M ↓ φ) n)
      exact hn)
    (by
      change IsZero (tateCohomology (ind₁'.obj M ↓ φ) (n + 1))
      exact hn1)
  exact @asIso _ _ _ _ (TateCohomology.δ h n) hi

def δUpNatIsoTate (n : ℤ) : up ⋙ tateCohomologyFunctor (R := R) (G := G) n ≅
    tateCohomologyFunctor (n + 1) :=
  NatIso.ofComponents (fun M ↦ δUpIsoTate M n) fun {M N} f ↦ .symm <| HomologySequence.δ_naturality
    ((upShortComplex ⋙ (tateComplexFunctor R G).mapShortComplex).map f)
    (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_upSES M))
    (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_upSES N)) n (n + 1) rfl

def δDownNatIsoTate (n : ℤ) : tateCohomologyFunctor (R := R) (G := G) n ≅
    down ⋙ tateCohomologyFunctor (n + 1) :=
  NatIso.ofComponents (fun M ↦ δDownIsoTate M n) fun {M N} f ↦ .symm <|
    HomologySequence.δ_naturality
      ((downShortComplex ⋙ (tateComplexFunctor R G).mapShortComplex).map f)
      (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_downSES M))
      (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_downSES N)) n (n + 1) rfl

end groupCohomology

end
