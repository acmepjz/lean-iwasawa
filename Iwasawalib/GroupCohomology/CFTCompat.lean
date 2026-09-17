module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Card
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Rep.Iso

@[expose] public noncomputable section

universe w u v v'

@[simps]
def Module.IsTorsionBy.coprime_decompose {k m1 m2 : ℕ} {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] (hk : k = m1 * m2)
    (hmm : m1.Coprime m2) (hA : Module.IsTorsionBy R M k) :
    M ≃ₗ[R] Submodule.torsionBy R M m1 × Submodule.torsionBy R M m2 where
  toFun m := ⟨⟨(m2 : R) • m, by simp [← mul_smul, ← Nat.cast_mul, ← hk, hA]⟩,
    ⟨(m1 : R) • m, by simp [← mul_smul, mul_comm, ← Nat.cast_mul, ← hk, hA]⟩⟩
  map_add' := by simp
  map_smul' := by simp [← mul_smul, mul_comm]
  invFun := fun ⟨x1, x2⟩ ↦ (m1.gcdB m2 : R) • x1.1 + (m1.gcdA m2 : R) • x2.1
  left_inv x := by
    simp only [← smul_assoc, smul_eq_mul, ← add_smul]
    convert one_smul R x using 2
    rw [← Nat.cast_one, ← Nat.coprime_iff_gcd_eq_one (m := m1) (n := m2)|>.1 hmm,
      ← AddCommGroupWithOne.intCast_ofNat (m1.gcd m2), Nat.gcd_eq_gcd_ab m1 m2]
    simpa using by grind
  right_inv := fun ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩ ↦ by
    simp only [Submodule.mem_torsionBy_iff] at hx1 hx2
    simp only [smul_add, ← smul_assoc, smul_eq_mul, mul_comm, Prod.mk.injEq, Subtype.mk.injEq]
    simp only [mul_smul, hx2, smul_zero, add_zero, hx1, zero_add]
    constructor
    · rw [← add_zero (_ • _ • x1), ← smul_zero (m1.gcdA m2), ← hx1, ← smul_assoc,
        ← smul_assoc, ← add_smul, smul_eq_mul, zsmul_eq_mul,
        ← AddCommGroupWithOne.intCast_ofNat, ← Int.cast_mul,
        ← AddCommGroupWithOne.intCast_ofNat m1, ← Int.cast_mul, ← Int.cast_add, mul_comm,
        mul_comm _ (m1 : ℤ), add_comm, ← Nat.gcd_eq_gcd_ab m1 m2,
        Nat.coprime_iff_gcd_eq_one.1 hmm]
      simp
    · rw [← add_zero (_ • _ • x2), ← smul_zero (m1.gcdB m2), ← hx2, ← smul_assoc,
        ← smul_assoc, ← add_smul, smul_eq_mul, zsmul_eq_mul,
        ← AddCommGroupWithOne.intCast_ofNat, ← Int.cast_mul,
        ← AddCommGroupWithOne.intCast_ofNat m2, ← Int.cast_mul, ← Int.cast_add, mul_comm,
        mul_comm _ (m2 : ℤ), ← Nat.gcd_eq_gcd_ab m1 m2,
        Nat.coprime_iff_gcd_eq_one.1 hmm]
      simp

open CategoryTheory in
theorem CategoryTheory.comp_commSq (C' : Type*) [Category C'] {A B C D E F : C'}
    (f₁ : A ⟶ B) (f₂ : B ⟶ C) (g₁ : A ⟶ D) (g₂ : C ⟶ F)
    (h₁ : D ⟶ E) (h₂ : E ⟶ F) (f : B ⟶ E)
    (comm1 : f₁ ≫ f = g₁ ≫ h₁) (comm2 : f₂ ≫ g₂ = f ≫ h₂) :
    (f₁ ≫ f₂) ≫ g₂ = g₁ ≫ (h₁ ≫ h₂) := by
  rw [← Category.assoc, ← comm1, Category.assoc, comm2, Category.assoc]

namespace CategoryTheory.ShortComplex

open Abelian
open Limits hiding im

variable {C D : Type*} [Category C] [Category D]

section Abelian

variable [Abelian C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[simps!] def kerIsoIm (F : D ⥤ ShortComplex C) (hF : ∀ d, (F.obj d).Exact) :
    F ⋙ gFunctor ⋙ ker C ≅ F ⋙ fFunctor ⋙ im :=
  NatIso.ofComponents fun X ↦
    have := (hF X).mono_cokernelDesc
    kernelIsoOfEq (by simp) ≪≫
      kernelCompMono _ (cokernel.desc (F.obj X).f (F.obj X).g (F.obj X).zero)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[simps!] def cokerIsoCoim (F : D ⥤ ShortComplex C) (hF : ∀ d, (F.obj d).Exact) :
    F ⋙ fFunctor ⋙ coker C ≅ F ⋙ gFunctor ⋙ coim :=
  NatIso.ofComponents fun X ↦
    have := (hF X).epi_kernelLift
    cokernelIsoOfEq (by simp) ≪≫
      cokernelEpiComp (kernel.lift (F.obj X).g (F.obj X).f (F.obj X).zero) _

end Abelian

variable {R : Type*} [Ring R] (S : ShortComplex (ModuleCat R))

lemma moduleCat_range_le_ker : LinearMap.range S.f.hom ≤ LinearMap.ker S.g.hom :=
  fun _ ⟨_, ht⟩ ↦ LinearMap.mem_ker.mpr (ht ▸ moduleCat_zero_apply _ _)

lemma Exact.moduleCat_of_ker_le_range (h : LinearMap.ker S.g.hom ≤ LinearMap.range S.f.hom) :
    S.Exact := .moduleCat_of_range_eq_ker _ _ (S.moduleCat_range_le_ker.antisymm h)

lemma Exact.moduleCat_finite {R : Type u} [Ring R]
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.Exact)
    [Finite S.X₁] [Finite S.X₃] : Finite S.X₂ := by
  have : Finite S.f.hom.toAddMonoidHom.range := Set.finite_range _
  have : Finite (S.X₂ ⧸ S.f.hom.toAddMonoidHom.range) := by
    rw [show S.f.hom.toAddMonoidHom.range = S.g.hom.toAddMonoidHom.ker from
      congr($(hS.moduleCat_range_eq_ker).toAddSubgroup)]
    exact .of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).toEquiv.symm
  exact .of_addSubgroup_quotient S.f.hom.toAddMonoidHom.range

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]

lemma shortExact_map_iff_of_natIso
    {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (S : ShortComplex C) (hIso : F ≅ G) :
    (S.map F).ShortExact ↔ (S.map G).ShortExact :=
  shortExact_iff_of_iso (S.mapNatIso hIso)

alias ⟨ShortExact.map_of_natIso, _⟩ := shortExact_map_iff_of_natIso

end CategoryTheory.ShortComplex

open CategoryTheory CategoryTheory.Limits ConcreteCategory

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

set_option backward.defeqAttrib.useBackward true in
def CategoryTheory.Limits.compNatIso' {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y} [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    parallelPair f 0 ⋙ F ≅ parallelPair (F.map f) 0 :=
  let app (j : WalkingParallelPair) :
      (parallelPair f 0 ⋙ F).obj j ≅ (parallelPair (F.map f) 0).obj j :=
    match j with
    | .zero => Iso.refl _
    | .one => Iso.refl _
  NatIso.ofComponents app <| by rintro ⟨i⟩ ⟨j⟩ <;> rintro (g | g) <;> simp [app]

attribute [local instance] Functor.PreservesHomology.preservesKernel
  Functor.PreservesHomology.preservesCokernel in
instance CategoryTheory.Functor.PreservesHomology.comp
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology]
    (G : D ⥤ E) [G.PreservesZeroMorphisms] [G.PreservesHomology] :
    PreservesHomology (F ⋙ G) where
  preservesKernels _ _ _ :=
    ⟨fun hc ↦ ⟨(KernelFork.isLimitMapConeEquiv _ _).2
      (KernelFork.mapIsLimit _ (KernelFork.mapIsLimit _ hc F) G)⟩⟩
  preservesCokernels _ _ _ :=
    ⟨fun hc ↦ ⟨(CokernelCofork.isColimitMapCoconeEquiv _ _).2
      (CokernelCofork.mapIsColimit _ (CokernelCofork.mapIsColimit _ hc F) G)⟩⟩

lemma CategoryTheory.ShortComplex.rep_exact_iff
    {S : ShortComplex (Rep.{w} k G)} :
    S.Exact ↔ S.g.hom.ker ≤ S.f.hom.range := by
  rw [← exact_map_iff_of_faithful (F := forget₂ (Rep k G) (ModuleCat k)),
    CategoryTheory.ShortComplex.moduleCat_exact_iff_ker_sub_range]
  rfl

lemma CategoryTheory.ShortComplex.ShortExact.rep_exact_iff_function_exact
    {S : ShortComplex (Rep.{w} k G)} : S.Exact ↔ Function.Exact S.f S.g := by
  rw [← exact_map_iff_of_faithful (F := forget₂ _ (ModuleCat k)),
    moduleCat_exact_iff_function_exact]
  rfl

theorem QuotientGroup.mk_mul' {G : Type} [Group G] {S : Subgroup G} (g x : G) :
    QuotientGroup.mk (s := S) (g * x) = g • QuotientGroup.mk x := rfl

namespace IsCyclic

variable {G : Type*} [Group G] [IsCyclic G]

variable (G) in
noncomputable def gen : G := IsCyclic.exists_generator.choose

lemma gen_generate (x : G) : x ∈ Subgroup.zpowers (gen G) :=
  IsCyclic.exists_generator.choose_spec x

theorem unique_gen_zpow_zmod [Fintype G] (x : G) :
    ∃! n : ZMod (Fintype.card G), x = gen G ^ n.val :=
  IsCyclic.unique_zpow_zmod gen_generate x

theorem unique_gen_pow [Fintype G] (x : G) :
    ∃! n < Fintype.card G, x = gen G ^ n := by
  obtain ⟨k, hk, hk_unique⟩ := unique_gen_zpow_zmod x
  refine ⟨k.val, ⟨⟨ZMod.val_lt _, hk⟩, ?_⟩⟩
  intro y ⟨hy_lt, hy⟩
  rw [← hk_unique y]
  · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hy_lt]
  · simp [hy]

end IsCyclic

variable {M N : Type*} [Monoid M] [Monoid N]

variable (M N) in
@[to_additive]
lemma subsingleton_monoidHom_of_isTorsion_isMulTorsionFree
    (hM : Monoid.IsTorsion M) [IsMulTorsionFree N] : Subsingleton (M →* N) where
  allEq f g := by
    ext m
    obtain ⟨n, hn, hrm⟩ := isOfFinOrder_iff_pow_eq_one.1 <| hM m
    refine pow_left_injective hn.ne' ?_
    simp_all [← map_pow]

namespace Finsupp

variable {α β M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

attribute [simp] coe_lmapDomain

@[simp, norm_cast] alias toLinearMap_mapDomainLinearEquiv :=
  mapDomain.toLinearMap_linearEquiv

@[simp] lemma coe_mapDomainLinearEquiv (e : α ≃ β) :
    ⇑(mapDomain.linearEquiv M R e) = equivMapDomain e := by
  ext
  simp [mapDomain.linearEquiv]

end Finsupp

variable {R M₂ : Type*} [Ring R] [AddCommGroup M] [AddCommGroup M₂]
  [Module R M] [Module R M₂]

omit [Monoid M] in
@[simp] lemma LinearMap.natCard_range_mul_natCard_ker (f : M →ₗ[R] M₂) :
    Nat.card (LinearMap.range f) * Nat.card (LinearMap.ker f) = Nat.card M := by
  rw [← Nat.card_congr f.quotKerEquivRange.toEquiv, mul_comm,
    ← Submodule.card_eq_card_quotient_mul_card]

namespace Nat

@[simp] lemma card_ne_zero' {α : Type*} [Nonempty α] [Finite α] : Nat.card α ≠ 0 :=
  Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩

end Nat

open scoped QuotientAddGroup
open LinearMap QuotientAddGroup

namespace Submodule

variable {𝕜 R M : Type*} [Semifield 𝕜] [CharZero 𝕜]

section Semiring

variable [Semiring R] [AddCommGroup M] [Module R M] {p q : Submodule R M}

@[simp] lemma natCard_submoduleOf (h : p ≤ q) : Nat.card (p.submoduleOf q) = Nat.card p :=
  Nat.card_congr (submoduleOfEquivOfLe h)

end Semiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M] {p : Submodule R M}

@[simp] lemma natCard_quotient [Finite M] : (Nat.card (M ⧸ p) : 𝕜) =
    Nat.card M / Nat.card p := by
  simp [p.card_eq_card_quotient_mul_card]

end Ring

end Submodule

namespace Representation

variable {G : Type*} [Group G] [Fintype G]

variable (G) in
@[simp] lemma norm_trivial_int_eq_card : (trivial ℤ G ℤ).norm = Nat.card G := by
  ext
  simp [Representation.norm]

end Representation

namespace Rep

variable {R : Type u} {G : Type v} {H : Type v'} [Ring R] [Monoid G]
  {A B : Rep.{w} R G}

lemma ρ_apply (g : G) :
    (leftRegular R G).ρ g = MonoidAlgebra.mapDomainLinearMap R R (g * ·) := rfl

lemma leftRegularHomEquiv_symm_comp {R : Type u} [CommRing R] {A B : Rep R G}
    (f : A ⟶ B) (a : A) :
    (leftRegularHomEquiv A).symm a ≫ f = (leftRegularHomEquiv B).symm (f.hom a) := by
  ext g
  simp [leftRegularHomEquiv, homLinearEquiv, homEquiv, hom_comm_apply]

lemma exists_kernelι_eq {R : Type u} [CommRing R]
    {M₁ M₂ : Rep.{max u v} R G} (f : M₁ ⟶ M₂) (m : M₁) (hm : f.hom m = 0) :
    ∃ k : kernel f (C := Rep R G), (kernel.ι f).hom k = m := by
  let g : leftRegular R G ⟶ M₁ := (leftRegularHomEquiv M₁).symm m
  have : g ≫ f = 0 := by
    rw [leftRegularHomEquiv_symm_comp]
    ext1
    rw [hm, map_zero]
  use leftRegularHomEquiv (kernel f) (kernel.lift f g this)
  simp [homEquiv, kernel.lift_ι_apply, g]

end Rep

lemma _root_.Representation.norm_ofIsTrivial (R M G : Type*) [Group G] [Semiring R]
    [AddCommGroup M] [Module R M] [Fintype G] (ρ : Representation R G M)
    [ρ.IsTrivial] : ρ.norm = Nat.card G := by
  ext
  simp [Representation.norm]

theorem _root_.range_eq_span {R : Type*} [CommSemiring R] (n : ℕ) :
    LinearMap.range (n : R →ₗ[R] R) = Ideal.span {(n : R)} := by
  ext x
  simp [Ideal.mem_span_singleton, dvd_iff_exists_eq_mul_right, eq_comm]

open Finsupp

namespace Rep.leftRegular

lemma leftRegularHom_eq_ρReg {R : Type u} {G : Type v} [Ring R] [Monoid G]
    (g : G) (hg : g ∈ Submonoid.center G) :
    ((leftRegular R G).leftRegularHom (.single g 1)).hom.toLinearMap =
      (leftRegular R G).ρ g := by
  ext
  simp [Submonoid.mem_center_iff.1 hg]

variable {R G : Type u} [Ring R] [Monoid G]

noncomputable abbrev ε (R G : Type u) [Ring R] [Monoid G] :
    leftRegular R G ⟶ trivial R G R := leftRegularHom (trivial R G R) (1 : R)

lemma ε_of_one : (ε R G) (.single 1 1) = (1 : R) := by simp

lemma ε_comp_ρ (g : G) :
    (ε R G).hom.toLinearMap ∘ₗ (leftRegular R G).ρ g = (ε R G).hom.toLinearMap := by
  ext
  simp

open Representation.IntertwiningMap in
lemma ε_comp_ρ_apply (g : G) (v : leftRegular R G) :
    (ε R G).hom ((leftRegular R G).ρ g v) = ε R G v := by
  rw [← toLinearMap_apply, ← LinearMap.comp_apply, ε_comp_ρ, toLinearMap_apply]

@[simp] lemma ε_of (g : G) : (ε R G).hom (.single g 1) = (1 : R) := by simp

lemma ε_eq_sum' (v : leftRegular R G) :
    (ε R G).hom v = ∑ x ∈ v.coeff.support, v.coeff x := by
  simp [Finsupp.sum]

lemma ε_eq_sum (v : leftRegular R G) [Fintype G] :
    (ε R G).hom v = ∑ g : G, v.coeff g := by
  refine ε_eq_sum' v|>.trans <| (finsum_eq_sum_of_support_subset v.coeff (by simp)).symm.trans ?_
  simp [finsum_eq_sum_of_fintype]

lemma nontrivial_iff_nontrivial : Nontrivial (leftRegular R G) ↔ Nontrivial R :=
  (MonoidAlgebra.coeffEquiv (R := R) (M := G)).nontrivial_congr.trans <|
    Finsupp.nontrivial_iff.trans <| and_iff_right ⟨1⟩

lemma ε_epi : Epi (ε R G) := epi_of_surjective _ fun r ↦ ⟨r • .single 1 1, by simp⟩

end Rep.leftRegular

theorem CommGroup.exists_mulHom_zmod_surjective_of_finite
    (G : Type*) [CommGroup G] [Finite G] [Nontrivial G] :
    ∃ n > 1, ∃ (f : G →* Multiplicative (ZMod n)), (⇑f).Surjective := by
  obtain ⟨ι, _, n, hn1, ⟨equiv⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  obtain ⟨i⟩ : Nonempty ι := by
    rw [← not_isEmpty_iff]
    intro
    apply not_subsingleton G
    exact equiv.subsingleton
  refine ⟨n i, hn1 i, (Pi.evalMonoidHom (fun i => Multiplicative (ZMod (n i))) i).comp equiv, ?_⟩
  simp [Function.surjective_eval]

theorem exists_isCyclic_quotient_of_finite {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} [H.Normal] (hH : H ≠ ⊤) (comm : IsMulCommutative (G ⧸ H)) :
    ∃ H' ∈ Set.Ico H ⊤, ∃ (_ : H'.Normal), IsCyclic (G ⧸ H') := by
  have := QuotientGroup.nontrivial_iff.2 hH
  obtain ⟨n, hn, f, hf⟩ := @CommGroup.exists_mulHom_zmod_surjective_of_finite (G ⧸ H)
    comm.instCommGroup _ _
  refine ⟨(f.comp (QuotientGroup.mk' H)).ker, ?_, inferInstance, ?_⟩
  · rw [Set.mem_Ico, ← MonoidHom.comap_ker, ← Subgroup.map_le_iff_le_comap,
      QuotientGroup.map_mk'_self, and_iff_right bot_le, lt_top_iff_ne_top,
      ← Subgroup.comap_top (QuotientGroup.mk' H),
      (Subgroup.comap_injective (QuotientGroup.mk'_surjective H)).ne_iff,
      ne_eq, MonoidHom.ker_eq_top_iff]
    rintro rfl
    apply Fact.mk at hn
    have := uniqueOfSurjectiveOne (G ⧸ H) hf
    exact not_subsingleton (ZMod n) Multiplicative.ofAdd.subsingleton
  · exact (QuotientGroup.quotientKerEquivRange _).isCyclic.2 inferInstance

theorem solvable_ind {G : Type*} [Group G] [Group.IsSolvable G] [Finite G]
    {motive : Subgroup G → Prop} (bot : motive ⊥)
    (ind : ∀ (H H' : Subgroup G) (_ : H ≤ H')
      (normal : (H.subgroupOf H').Normal), IsCyclic (H' ⧸ H.subgroupOf H') →
      motive H → motive H') (t : Subgroup G) : motive t := by
  by_cases ht : t = ⊥
  · exact ht ▸ bot
  · have hhh : ⁅t, t⁆ < t := Group.IsSolvable.commutator_lt_of_ne_bot ht
    have sub_eq : (⁅t, t⁆).subgroupOf t = commutator t := by
      apply Subgroup.map_injective t.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hhh.le, map_commutator_eq, Subgroup.range_subtype]
    have normal : ((⁅t, t⁆).subgroupOf t).Normal := by
      rw [sub_eq]
      infer_instance
    have comm : IsMulCommutative (t ⧸ (⁅t, t⁆).subgroupOf t) := by
      revert normal
      rw [sub_eq]
      intro normal
      exact inferInstanceAs (IsMulCommutative (Abelianization t))
    have htt : (⁅t, t⁆).subgroupOf t ≠ ⊤ := by simpa using hhh.not_ge
    obtain ⟨t', ⟨-, ht'⟩, _, cyclic⟩ := exists_isCyclic_quotient_of_finite htt comm
    have h : (Subgroup.map t.subtype t').subgroupOf t = t' := by
      rw [← Subgroup.comap_subtype,
        Subgroup.comap_map_eq_self_of_injective t.subtype_injective]
    have normal : ((Subgroup.map t.subtype t').subgroupOf t).Normal :=
      (congrArg Subgroup.Normal h).mpr inferInstance
    apply ind (t'.map t.subtype) t ((Subgroup.map_mono ht'.le).trans_eq
      ((MonoidHom.range_eq_map t.subtype).symm.trans t.range_subtype)) normal
      ((QuotientGroup.quotientMulEquivOfEq h).isCyclic.2 cyclic)
    have : Subgroup.map t.subtype t' < t := by
      apply ((Subgroup.map_lt_map_iff_of_injective t.subtype_injective).2 ht').trans_eq
      rw [← MonoidHom.range_eq_map t.subtype, t.range_subtype]
    exact solvable_ind bot ind (Subgroup.map t.subtype t')
termination_by wellFounded_lt.wrap t
