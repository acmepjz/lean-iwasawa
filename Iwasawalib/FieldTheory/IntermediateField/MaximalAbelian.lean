/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.FieldTheory.Galois.Abelian
public import Iwasawalib.FieldTheory.IntermediateField.MaximalGaloisSExtension

@[expose] public section

/-!

# Maximal abelian subextension

- `IntermediateField.maximalAbelianExtension F K`, being an `IntermediateField F K`,
  is the maximal abelian subextension of `K / F`, which is defined to be
  the compositum of all abelian subextension of `K / F`.

- `IntermediateField.maximalAbelianSExtension F K S`, being an `IntermediateField F K`,
  is the maximal abelian `S`-subextension of `K / F`, which is defined to be
  the maximal Galois `S`-subextension of the maximal abelian subextension of `K / F`.

"le_lift_XXX_iff" and "lift_XXX_le_iff" are useful results since we often chain these constuctions
with `IntermediateField.lift`.

-/

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

namespace IntermediateField

/-- Unused result. TODO: go mathlib -/
theorem fixingSubgroup_restrictScalars
    (K : Type*) {L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L]
    [Algebra K L'] [Algebra L' L] [IsScalarTower K L' L] [Normal K L] (E : IntermediateField L' L) :
    (E.restrictScalars K).fixingSubgroup =
    E.fixingSubgroup.map (restrictRestrictAlgEquivMapHom K L L' L) := by
  ext f
  simp only [mem_fixingSubgroup_iff, mem_restrictScalars, restrictRestrictAlgEquivMapHom,
    AlgEquiv.restrictNormalHom_id, MonoidHom.CompTriple.comp_eq, Subgroup.mem_map,
    MulSemiringAction.toAlgAut_apply]
  refine ⟨fun h ↦ ?_, fun ⟨g, h1, h2⟩ ↦ by simpa [← h2]⟩
  let g : Gal(L/L') := {
    toRingEquiv := f.toRingEquiv
    commutes' := fun x ↦ h _ (algebraMap_mem E x)
  }
  exact ⟨g, by simpa [g], by ext; simp [g]⟩

/-! ### Maximal abelian subextension -/

/-- The maximal abelian subextension of `K / F` is the compositum of all
abelian subextension of `K / F`. -/
def maximalAbelianExtension : IntermediateField F K := sSup {E | IsAbelianGalois F E}

instance isAbelianGalois_maximalAbelianExtension :
    IsAbelianGalois F (maximalAbelianExtension F K) := by
  rw [maximalAbelianExtension, sSup_eq_iSup']
  have (E : {E : IntermediateField F K | IsAbelianGalois F E}) : IsAbelianGalois F E.1 := E.2
  infer_instance

variable {F K} in
theorem le_maximalAbelianExtension (E : IntermediateField F K) [IsAbelianGalois F E] :
    E ≤ maximalAbelianExtension F K :=
  le_sSup ‹_›

variable {F K} in
theorem le_maximalAbelianExtension_iff (E : IntermediateField F K) :
    E ≤ maximalAbelianExtension F K ↔ IsAbelianGalois F E := by
  refine ⟨fun h ↦ ?_, fun _ ↦ E.le_maximalAbelianExtension⟩
  have : IsAbelianGalois F (extendScalars h) := isAbelianGalois_maximalAbelianExtension F K
  exact .tower_bot F E (extendScalars h)

variable {F K} in
theorem maximalAbelianExtension_le_iff (E : IntermediateField F K) :
    maximalAbelianExtension F K ≤ E ↔
      ∀ E' : IntermediateField F K, IsAbelianGalois F E' → E' ≤ E :=
  ⟨fun h E' _ ↦ E'.le_maximalAbelianExtension.trans h, sSup_le⟩

variable {F K} in
theorem le_lift_maximalAbelianExtension_iff (L E : IntermediateField F K) :
    E ≤ lift (maximalAbelianExtension F L) ↔ E ≤ L ∧ IsAbelianGalois F E := by
  refine ⟨fun h ↦ ⟨h.trans (lift_le _), ?_⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  · have := IsAbelianGalois.of_algEquiv (liftAlgEquiv (maximalAbelianExtension F L))
    exact .of_algEquiv (restrict_algEquiv h).symm
  · have := IsAbelianGalois.of_algEquiv (restrict_algEquiv h1)
    have := le_maximalAbelianExtension (restrict h1)
    intro x h
    have := @this ⟨x, h1 h⟩ ((mem_restrict h1 _).2 h)
    rwa [← mem_lift] at this

variable {F K} in
theorem lift_maximalAbelianExtension_le_iff (L E : IntermediateField F K) :
    lift (maximalAbelianExtension F L) ≤ E ↔
      ∀ E' : IntermediateField F K, E' ≤ L → IsAbelianGalois F E' → E' ≤ E :=
  ⟨fun h _ h2 h3 ↦ ((le_lift_maximalAbelianExtension_iff L _).2 ⟨h2, h3⟩).trans h,
    fun h ↦ h _ (lift_le ..) (.of_algEquiv (liftAlgEquiv _))⟩

theorem maximalAbelianExtension_eq_top [IsAbelianGalois F K] : maximalAbelianExtension F K = ⊤ := by
  simpa only [eq_top_iff] using le_maximalAbelianExtension (⊤ : IntermediateField F K)

variable {F K} in
theorem maximalAbelianExtension_eq_top_iff :
    maximalAbelianExtension F K = ⊤ ↔ IsAbelianGalois F K :=
  ⟨fun h ↦ @IsAbelianGalois.of_algEquiv F _ _ _ K _ _ _
    (h ▸ isAbelianGalois_maximalAbelianExtension F K) topEquiv,
      fun _ ↦ maximalAbelianExtension_eq_top ..⟩

variable {F K} in
theorem sup_le_maximalAbelianExtension {E1 E2 : IntermediateField F K}
    (h1 : E1 ≤ maximalAbelianExtension F K) (h2 : E2 ≤ maximalAbelianExtension F K) :
    E1 ⊔ E2 ≤ maximalAbelianExtension F K := by
  rw [le_maximalAbelianExtension_iff] at h1 h2 ⊢
  infer_instance

variable {F K} in
theorem iSup_le_maximalAbelianExtension {ι : Type*} {E : ι → IntermediateField F K}
    (h : ∀ i, E i ≤ maximalAbelianExtension F K) : ⨆ i, E i ≤ maximalAbelianExtension F K := by
  simp_rw [le_maximalAbelianExtension_iff] at h ⊢
  infer_instance

/-
PROVIDED SOLUTION
Strategy: Show maximalAbelianExtension F K = IntermediateField.fixedField (commutator Gal(K/F)), then use IntermediateField.fixingSubgroup_fixedField (since K/F is finite-dimensional) to conclude.

For the equality, show both directions:
(≤): maximalAbelianExtension is sSup of abelian subextensions. Each abelian subextension E has fixingSubgroup containing the commutator (by Abelianization.commutator_subset_ker applied to the restriction map to Gal(E/F) which is abelian). So E ≤ fixedField(commutator) for each abelian E. Hence sSup ≤ fixedField(commutator).

(≥): fixedField(commutator) is an abelian extension. Its Galois group is Gal(K/F)/commutator ≅ Abelianization, which is abelian. So it's contained in maximalAbelianExtension.

Actually, simpler: just show maximalAbelianExtension = fixedField(commutator) and then apply fixingSubgroup_fixedField.

Or even simpler: show le_antisymm for the fixingSubgroup directly.
(commutator ≤ fixingSubgroup(maximalAbelianExtension)): Every element of commutatorSet fixes every abelian subextension (since abelian subextensions have abelian Galois group, so commutators act trivially on them). Since maximalAbelianExtension is sSup of abelian subextensions, commutators fix it. Use commutator_eq_normalClosure and Subgroup.closure_le.

(fixingSubgroup(maximalAbelianExtension) ≤ commutator): Consider E = fixedField(commutator). This is an abelian extension (Gal(K/F)/commutator is abelian). So E ≤ maximalAbelianExtension. Hence fixingSubgroup(maximalAbelianExtension) ≤ fixingSubgroup(E) = commutator (by fixingSubgroup_fixedField).
-/
theorem fixingSubgroup_maximalAbelianExtension_of_finiteDimensional
    [IsGalois F K] [FiniteDimensional F K] :
    (maximalAbelianExtension F K).fixingSubgroup = commutator Gal(K/F) := by
  have h_max_abelian : (maximalAbelianExtension F K).fixingSubgroup ≤ commutator Gal(K/F) := by
    -- Consider the fixed field of the commutator subgroup.
    set L := IntermediateField.fixedField (commutator Gal(K/F)) with hL_def;
    -- Since $L$ is abelian, it is contained in the maximal abelian extension.
    have hL_abelian : IsAbelianGalois F L := by
      have hL_abelian : IsMulCommutative (Gal(L/F)) := by
        have hL_abelian : Gal(L/F) ≃* (Gal(K/F) ⧸ commutator Gal(K/F)) := by
          exact?;
        have hL_abelian : ∀ x y : Gal(K/F) ⧸ commutator Gal(K/F), x * y = y * x := by
          intro x y; obtain ⟨ x, rfl ⟩ := QuotientGroup.mk_surjective x; obtain ⟨ y, rfl ⟩ := QuotientGroup.mk_surjective y; simp +decide [ commutator_def ] ;
          erw [ QuotientGroup.eq ];
          simp +decide [ Subgroup.commutator_def ];
          exact Subgroup.subset_closure ⟨ y⁻¹, x⁻¹, by group ⟩;
        have hL_abelian : ∀ x y : Gal(L/F), x * y = y * x := by
          exact fun x y => by simpa [ ← ‹Gal(L/F) ≃* Gal(K/F) ⧸ commutator Gal(K/F)›.injective.eq_iff ] using hL_abelian ( ‹Gal(L/F) ≃* Gal(K/F) ⧸ commutator Gal(K/F)› x ) ( ‹Gal(L/F) ≃* Gal(K/F) ⧸ commutator Gal(K/F)› y ) ;
        constructor ; tauto;
      constructor
    have hL_le_max : L ≤ maximalAbelianExtension F K := by
      exact?;
    have hL_fixingSubgroup : (maximalAbelianExtension F K).fixingSubgroup ≤ L.fixingSubgroup := by
      exact?;
    convert hL_fixingSubgroup using 1;
    exact?;
  refine' le_antisymm h_max_abelian _;
  have h_comm_subgroup : ∀ (E : IntermediateField F K), IsAbelianGalois F E → commutator (Gal(K/F)) ≤ E.fixingSubgroup := by
    intro E hE
    have h_comm_subgroup : commutator (Gal(K/F)) ≤ E.fixingSubgroup := by
      have h_comm_subgroup : ∀ g h : Gal(K/F), g * h * g⁻¹ * h⁻¹ ∈ E.fixingSubgroup := by
        intro g h
        have h_comm_subgroup : ∀ x : E, (g * h * g⁻¹ * h⁻¹) (algebraMap E K x) = algebraMap E K x := by
          intro x
          have h_comm_subgroup : (g * h * g⁻¹ * h⁻¹) (algebraMap E K x) = algebraMap E K ((AlgEquiv.restrictNormalHom E g) ((AlgEquiv.restrictNormalHom E h) ((AlgEquiv.restrictNormalHom E g⁻¹) ((AlgEquiv.restrictNormalHom E h⁻¹) x))) ) := by
            simp +decide [ AlgEquiv.restrictNormalHom ];
          have h_comm_subgroup : ∀ g h : Gal(E/F), g * h = h * g := by
            exact?;
          specialize h_comm_subgroup (AlgEquiv.restrictNormalHom E g) (AlgEquiv.restrictNormalHom E h);
          replace h_comm_subgroup := congr_arg ( fun f => f ( ( AlgEquiv.restrictNormalHom E g⁻¹ ) ( ( AlgEquiv.restrictNormalHom E h⁻¹ ) x ) ) ) h_comm_subgroup ; aesop;
        exact?
      rw [ commutator_eq_closure ];
      rw [ Subgroup.closure_le ];
      exact fun x hx => by obtain ⟨ g, h, rfl ⟩ := hx; exact h_comm_subgroup g h;
    exact h_comm_subgroup;
  exact?

/-
PROVIDED SOLUTION
The commutator subgroup of Gal(K/F) fixes maximalAbelianExtension F K. The maximalAbelianExtension is the sSup of all abelian subextensions E. So fixingSubgroup(maximalAbelianExtension) = iInf of fixingSubgroup(E) over all abelian E. It suffices to show commutator Gal(K/F) ≤ fixingSubgroup(E) for each abelian E. This means every commutator element g*h*g⁻¹*h⁻¹ fixes E. Use commutator_eq_normalClosure and Subgroup.closure_le. For each commutator element g*h*g⁻¹*h⁻¹ and x ∈ E, we need (g*h*g⁻¹*h⁻¹)(x) = x. Since E is abelian (IsAbelianGalois F E), use Abelianization.commutator_subset_ker with the restrictNormalHom to Gal(E/F), which gives that the commutator maps to 1 in Gal(E/F), so it fixes E.
-/
private theorem commutator_le_fixingSubgroup_maximalAbelianExtension [IsGalois F K] :
    commutator Gal(K/F) ≤ (maximalAbelianExtension F K).fixingSubgroup := by
  -- Since the maximal abelian extension is the supremum of all abelian subextensions, its fixing subgroup is the intersection of the fixing subgroups of all abelian subextensions.
  have h_fixing_subgroup : (maximalAbelianExtension F K).fixingSubgroup = ⨅ (E : IntermediateField F K) (_ : IsAbelianGalois F E), E.fixingSubgroup := by
    refine' le_antisymm _ _;
    · refine' le_iInf fun E => le_iInf fun hE => _;
      have h_le : E ≤ maximalAbelianExtension F K := by
        exact?;
      exact?;
    · refine' iInf₂_le _ _;
      exact?;
  -- For any abelian subextension E of K/F, the commutator subgroup of Gal(K/F) is contained in the fixing subgroup of E.
  have h_comm_subgroup : ∀ E : IntermediateField F K, IsAbelianGalois F E → commutator Gal(K/F) ≤ E.fixingSubgroup := by
    intro E hE
    have h_comm_subgroup : commutator Gal(K/F) ≤ (AlgEquiv.restrictNormalHom E).ker := by
      rw [ commutator_eq_normalClosure ];
      refine' Subgroup.normalClosure_le_normal _;
      rintro _ ⟨ g, h, rfl ⟩;
      simp +decide [ commutatorElement_def ];
    convert h_comm_subgroup using 1;
    exact?;
  exact h_fixing_subgroup.symm ▸ le_iInf₂ fun E hE => h_comm_subgroup E hE

/-
PROVIDED SOLUTION
Step 1: fixedField(closure(commutator)) is Galois over F. This follows from IsGalois.of_fixedField_normal_subgroup, using that closure(commutator) is a normal subgroup (use instNormalCommutatorClosure or Subgroup.is_normal_topologicalClosure).

Step 2: The Galois group Gal(fixedField(closure(commutator))/F) is abelian. By the Galois correspondence (AlgEquiv.restrictNormalHom), there is a surjective map Gal(K/F) → Gal(fixedField(N)/F) with kernel = fixingSubgroup(fixedField(N)) = N (for closed N, by InfiniteGalois.fixingSubgroup_fixedField). So Gal(fixedField(N)/F) ≃ Gal(K/F)/N. When N = closure(commutator), commutator ≤ N, so Gal(K/F)/N is a quotient of Gal(K/F)/commutator which is abelian.

For commutativity: let x y ∈ Gal(fixedField(N)/F). Lift to x' y' ∈ Gal(K/F). Then x'*y'*x'⁻¹*y'⁻¹ ∈ commutator ≤ N = ker. So the images commute.
-/
private theorem isAbelianGalois_fixedField_topologicalClosure_commutator [IsGalois F K] :
    IsAbelianGalois F (IntermediateField.fixedField (commutator Gal(K/F)).topologicalClosure) := by
  have h_normal : Subgroup.Normal (Subgroup.topologicalClosure (commutator (Gal(K/F))) : Subgroup (Gal(K/F))) := by
    exact?;
  have h_surjective : Function.Surjective (AlgEquiv.restrictNormalHom (fixedField (Subgroup.topologicalClosure (commutator (Gal(K/F))) : Subgroup (Gal(K/F)))) : Gal(K/F) → Gal(↥(fixedField (Subgroup.topologicalClosure (commutator (Gal(K/F))) : Subgroup (Gal(K/F))))/F)) := by
    exact?;
  have h_ker : (AlgEquiv.restrictNormalHom (fixedField (Subgroup.topologicalClosure (commutator (Gal(K/F))) : Subgroup (Gal(K/F))))).ker = Subgroup.topologicalClosure (commutator (Gal(K/F))) := by
    convert InfiniteGalois.fixingSubgroup_fixedField _;
    any_goals exact IsGalois.mk;
    rotate_right;
    exact ⟨ Subgroup.topologicalClosure ( commutator Gal(K/F) ), isClosed_closure ⟩;
    · exact?;
    · rfl;
  have h_abelian : ∀ x y : Gal(K/F), x * y * x⁻¹ * y⁻¹ ∈ Subgroup.topologicalClosure (commutator (Gal(K/F))) := by
    exact fun x y => Subgroup.le_topologicalClosure _ ( Subgroup.commutator_mem_commutator ( Subgroup.mem_top x ) ( Subgroup.mem_top y ) );
  have h_abelian : ∀ x y : Gal(↥(fixedField (Subgroup.topologicalClosure (commutator (Gal(K/F))) : Subgroup (Gal(K/F))))/F), x * y = y * x := by
    intro x y
    obtain ⟨x', hx'⟩ := h_surjective x
    obtain ⟨y', hy'⟩ := h_surjective y
    have h_comm : x' * y' * x'⁻¹ * y'⁻¹ ∈ Subgroup.topologicalClosure (commutator (Gal(K/F))) := h_abelian x' y';
    simp_all +decide [ ← h_ker, MonoidHom.mem_ker ];
    simpa [ mul_inv_eq_iff_eq_mul ] using eq_inv_of_mul_eq_one_left h_comm;
  have h_abelian : IsMulCommutative (Gal(↥(fixedField (Subgroup.topologicalClosure (commutator (Gal(K/F))) : Subgroup (Gal(K/F))))/F)) := by
    constructor ; tauto;
  exact?

theorem fixingSubgroup_maximalAbelianExtension [IsGalois F K] :
    (maximalAbelianExtension F K).fixingSubgroup = (commutator Gal(K/F)).topologicalClosure := by
  refine le_antisymm ?_ ?_
  · -- fixingSubgroup(max_ab) ≤ closure(commutator)
    -- By antitone: suffices to show fixedField(closure(commutator)) ≤ maximalAbelianExtension
    -- fixedField(closure(commutator)) is abelian, so it's ≤ maximalAbelianExtension
    have h1 := isAbelianGalois_fixedField_topologicalClosure_commutator F K
    have h2 := le_maximalAbelianExtension
      (IntermediateField.fixedField (commutator Gal(K/F)).topologicalClosure)
    have h3 : (maximalAbelianExtension F K).fixingSubgroup ≤
        (IntermediateField.fixedField (commutator Gal(K/F)).topologicalClosure).fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone h2
    rw [InfiniteGalois.fixingSubgroup_fixedField
      ⟨(commutator Gal(K/F)).topologicalClosure, isClosed_closure⟩] at h3
    exact h3
  · -- closure(commutator) ≤ fixingSubgroup(max_ab)
    exact closure_minimal (commutator_le_fixingSubgroup_maximalAbelianExtension F K)
      (InfiniteGalois.fixingSubgroup_isClosed _)

/-- Suppose `L / K / F` is a field extension tower, such that `L / F` and `K / F` are Galois.
Let `H / K` be the maximal abelian subextension of `L / K`. Then `H / F` is also Galois. -/
theorem isGalois_maximalAbelianExtension_of_isGalois
    (L : Type*) [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
    [IsGalois F L] [IsGalois F K] : IsGalois F (maximalAbelianExtension K L) := by
  set H := maximalAbelianExtension K L
  suffices Normal F H by
    have := IsGalois.tower_top_of_isGalois F K L
    have := H.isSeparable_tower_bot
    have := Algebra.IsSeparable.trans F K H
    exact ⟨⟩
  change Normal F (restrictScalars F H)
  rw [normal_iff_forall_map_le']
  intro σ
  let σH := ((restrictScalars F H).map (AlgHomClass.toAlgHom σ)).toSubfield.toIntermediateField
      fun (x : K) ↦ by
    simp only [toSubfield_map, AlgHomClass.toRingHom_toAlgHom, restrictScalars_toSubfield,
      Subfield.mem_map, mem_toSubfield, RingHom.coe_coe]
    use algebraMap K L (σ.symm.restrictNormal K x), algebraMap_mem ..
    simp
  suffices σH ≤ H from fun x hx ↦ this hx
  let f := (σ.restrictNormal K).toRingEquiv
  let g : H ≃+* σH := ((restrictScalars F H).equivMap (AlgHomClass.toAlgHom σ)).toRingEquiv
  have hcomp : (algebraMap K σH).comp f = RingHom.comp g (algebraMap K H) := by
    ext x
    simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, SubalgebraClass.coe_algebraMap,
      AlgEquiv.restrictNormal_commutes, f, g]
    rfl
  have : IsAbelianGalois K σH := .of_equiv_equiv hcomp
  exact le_maximalAbelianExtension ..

/-! ### Maximal abelian `S`-subextension -/

variable (S : Set ℕ) (p : ℕ) [Fact p.Prime]

/-- The maximal abelian `S`-subextension of `K / F` is defined to be the maximal Galois
`S`-subextension of the maximal abelian subextension of `K / F`. -/
def maximalAbelianSExtension : IntermediateField F K :=
  lift (maximalGaloisSExtension F (maximalAbelianExtension F K) S)

instance isAbelianGalois_maximalAbelianSExtension :
    IsAbelianGalois F (maximalAbelianSExtension F K S) :=
  .of_algEquiv (liftAlgEquiv _)

instance isSExtension_maximalAbelianSExtension :
    IsSExtension F (maximalAbelianSExtension F K S) S :=
  .of_algEquiv S (liftAlgEquiv _)

/-- The maximal abelian `S`-subextension of `K / F` is equal to
the compositum of all abelian subextensions `E` of `K / F` which are `S`-extensions. -/
theorem maximalAbelianSExtension_eq_sSup : maximalAbelianSExtension F K S =
    sSup {E : IntermediateField F K | IsAbelianGalois F E ∧ IsSExtension F E S} := by
  refine le_antisymm (le_sSup ⟨inferInstance, inferInstance⟩) (sSup_le fun E ⟨_, _⟩ ↦ ?_)
  rw [maximalAbelianSExtension]
  apply le_lift_maximalGaloisSExtension
  apply le_maximalAbelianExtension

/-- The maximal abelian `S`-subextension of `K / F` is equal to
the compositum of all finite abelian subextensions `E` of `K / F` which are `S`-extensions. -/
theorem maximalAbelianSExtension_eq_sSup_finiteDimensional :
    maximalAbelianSExtension F K S = sSup {E : IntermediateField F K |
      FiniteDimensional F E ∧ IsAbelianGalois F E ∧ IsSExtension F E S} := by
  rw [maximalAbelianSExtension_eq_sSup]
  refine le_antisymm (sSup_le fun E ⟨_, _⟩ ↦ ?_) (sSup_le fun E ⟨_, h⟩ ↦ le_sSup h)
  rw [E.eq_sSup_of_isGalois_of_isSExtension S]
  refine sSup_le fun E' ⟨h, h1, h2, h3⟩ ↦ le_sSup ⟨h1, ?_, h3⟩
  have := IsAbelianGalois.tower_bot F (restrict h) E
  exact .of_algEquiv (restrict_algEquiv h).symm

variable {F K} in
theorem le_maximalAbelianSExtension (E : IntermediateField F K) [IsAbelianGalois F E]
    [IsSExtension F E S] : E ≤ maximalAbelianSExtension F K S := by
  rw [maximalAbelianSExtension_eq_sSup]
  exact le_sSup ⟨‹_›, ‹_›⟩

variable {F K p} in
theorem le_maximalAbelianSExtension_singleton (E : IntermediateField F K) [IsAbelianGalois F E]
    (h : ∃ n, Module.finrank F E = p ^ n) : E ≤ maximalAbelianSExtension F K {p} := by
  have := isSExtension_singleton_of_exists_finrank_eq_pow _ _ _ h
  exact le_maximalAbelianSExtension _ E

variable {F K S} in
theorem le_maximalAbelianSExtension_iff (E : IntermediateField F K) :
    E ≤ maximalAbelianSExtension F K S ↔ IsAbelianGalois F E ∧ IsSExtension F E S := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _⟩ ↦ E.le_maximalAbelianSExtension S⟩
  have := IsAbelianGalois.tower_bot F (restrict h) (maximalAbelianSExtension F K S)
  have := IsSExtension.tower_bot F (restrict h) S (maximalAbelianSExtension F K S)
  exact ⟨.of_algEquiv (restrict_algEquiv h).symm, .of_algEquiv S (restrict_algEquiv h).symm⟩

variable {F K S} in
theorem maximalAbelianSExtension_le_iff (E : IntermediateField F K) :
    maximalAbelianSExtension F K S ≤ E ↔
      ∀ E' : IntermediateField F K, IsAbelianGalois F E' → IsSExtension F E' S → E' ≤ E := by
  refine ⟨fun h E' _ _ ↦ (E'.le_maximalAbelianSExtension S).trans h, fun h ↦ ?_⟩
  rw [maximalAbelianSExtension_eq_sSup]
  exact sSup_le fun _ ⟨h1, h2⟩ ↦ h _ h1 h2

variable {F K} in
theorem le_lift_maximalAbelianSExtension {L E : IntermediateField F K} (h : E ≤ L)
    [IsAbelianGalois F E] [IsSExtension F E S] : E ≤ lift (maximalAbelianSExtension F L S) := by
  have := IsAbelianGalois.of_algEquiv (restrict_algEquiv h)
  have := IsSExtension.of_algEquiv S (restrict_algEquiv h)
  have := le_maximalAbelianSExtension S (restrict h)
  intro x h'
  have := @this ⟨x, h h'⟩ ((mem_restrict h _).2 h')
  rwa [← mem_lift] at this

variable {F K S} in
theorem le_lift_maximalAbelianSExtension_iff (L E : IntermediateField F K) :
    E ≤ lift (maximalAbelianSExtension F L S) ↔
      E ≤ L ∧ IsAbelianGalois F E ∧ IsSExtension F E S := by
  refine ⟨fun h ↦ ⟨h.trans (lift_le _), ?_⟩, fun ⟨h, _, _⟩ ↦ le_lift_maximalAbelianSExtension S h⟩
  have := IsSExtension.of_algEquiv S (liftAlgEquiv (maximalAbelianSExtension F L S))
  have := IsSExtension.tower_bot F (restrict h) S (lift (maximalAbelianSExtension F L S))
  have := IsAbelianGalois.of_algEquiv (liftAlgEquiv (maximalAbelianSExtension F L S))
  have := IsAbelianGalois.tower_bot F (restrict h) (lift (maximalAbelianSExtension F L S))
  exact ⟨.of_algEquiv (restrict_algEquiv h).symm, .of_algEquiv S (restrict_algEquiv h).symm⟩

variable {F K S} in
theorem lift_maximalAbelianSExtension_le_iff (L E : IntermediateField F K) :
    lift (maximalAbelianSExtension F L S) ≤ E ↔
      ∀ E' : IntermediateField F K, E' ≤ L → IsAbelianGalois F E' → IsSExtension F E' S → E' ≤ E :=
  ⟨fun h _ h2 _ _ ↦ (le_lift_maximalAbelianSExtension S h2).trans h,
    fun h ↦ h _ (lift_le ..) (.of_algEquiv (liftAlgEquiv _)) (.of_algEquiv S (liftAlgEquiv _))⟩

variable {F K} in
theorem lift_maximalAbelianSExtension_eq_sSup (L : IntermediateField F K) :
    lift (maximalAbelianSExtension F L S) = sSup {E : IntermediateField F K |
      E ≤ L ∧ IsAbelianGalois F E ∧ IsSExtension F E S} := by
  refine le_antisymm ?_ (sSup_le fun E ⟨h, _, _⟩ ↦ le_lift_maximalAbelianSExtension S h)
  rw [lift_maximalAbelianSExtension_le_iff]
  exact fun E' h1 h2 h3 ↦ le_sSup ⟨h1, h2, h3⟩

variable {F K} in
theorem lift_maximalAbelianSExtension_eq_sSup_finiteDimensional (L : IntermediateField F K) :
    lift (maximalAbelianSExtension F L S) = sSup {E : IntermediateField F K |
      E ≤ L ∧ FiniteDimensional F E ∧ IsAbelianGalois F E ∧ IsSExtension F E S} := by
  rw [lift_maximalAbelianSExtension_eq_sSup]
  refine le_antisymm (sSup_le fun E ⟨h, _, _⟩ ↦ ?_) (sSup_le fun E ⟨h, _, h2⟩ ↦ le_sSup ⟨h, h2⟩)
  rw [E.eq_sSup_of_isGalois_of_isSExtension S]
  refine sSup_le fun _ ⟨h1, h2, _, h4⟩ ↦ le_sSup ⟨h1.trans h, h2, ?_, h4⟩
  have := IsAbelianGalois.tower_bot F (restrict h1) E
  exact .of_algEquiv (restrict_algEquiv h1).symm

theorem maximalAbelianSExtension_le_maximalAbelianExtension :
    maximalAbelianSExtension F K S ≤ maximalAbelianExtension F K := lift_le ..

theorem maximalAbelianSExtension_le_maximalGaloisSExtension :
    maximalAbelianSExtension F K S ≤ maximalGaloisSExtension F K S := by
  rw [maximalAbelianSExtension_eq_sSup, maximalGaloisSExtension, sSup_le_iff]
  exact fun E ⟨_, h⟩ ↦ le_sSup ⟨inferInstance, h⟩

theorem maximalAbelianSExtension_eq_maximalGaloisSExtension [IsAbelianGalois F K] :
    maximalAbelianSExtension F K S = maximalGaloisSExtension F K S := by
  have h1 (E : IntermediateField F K) : IsAbelianGalois F E := inferInstance
  have h2 (E : IntermediateField F K) : IsGalois F E := inferInstance
  simp only [maximalAbelianSExtension_eq_sSup, maximalGaloisSExtension, h1, h2]

/-- Suppose `L / K / F` is a field extension tower, such that `L / F` and `K / F` are Galois.
Let `H / K` be the maximal abelian `S`-subextension of `L / K`. Then `H / F` is also Galois. -/
theorem isGalois_maximalAbelianSExtension_of_isGalois
    (L : Type*) [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
    [IsGalois F L] [IsGalois F K] : IsGalois F (maximalAbelianSExtension K L S) := by
  have := isGalois_maximalAbelianExtension_of_isGalois F K L
  have := isGalois_maximalGaloisSExtension_of_isGalois F K S (maximalAbelianExtension K L)
  exact .of_algEquiv ((liftAlgEquiv _).restrictScalars F)

section FiniteDimensional

variable [FiniteDimensional F K]

theorem exists_finrank_maximalAbelianSExtension_singleton_eq_pow :
    ∃ n, Module.finrank F (maximalAbelianSExtension F K {p}) = p ^ n :=
  exists_finrank_eq_pow_of_le_maximalGaloisSExtension_singleton
    (maximalAbelianSExtension_le_maximalGaloisSExtension ..)

end FiniteDimensional

end IntermediateField
