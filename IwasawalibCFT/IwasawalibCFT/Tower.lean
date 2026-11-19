/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IwasawalibCFT.Iwasawa
public import IwasawalibCFT.CyclicTower
public import Iwasawalib.FieldTheory.Galois.InverseLimit

@[expose] public section

/-! # Transport of Iwasawa's formula to a tower in an arbitrary ambient field -/

namespace NumberField

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
variable {L : Type*} [Field L] [Algebra K L]

/-- Restrict each layer to the union of the tower. -/
noncomputable def towerLayer (Kn : ℕ → IntermediateField K L) (n : ℕ) :
    IntermediateField K ↥(⨆ n, Kn n : IntermediateField K L) :=
  IntermediateField.restrict (le_iSup Kn n)

/-- Restriction to the union preserves the original layer as a K-algebra. -/
noncomputable def towerLayerEquiv (Kn : ℕ → IntermediateField K L) (n : ℕ) :
    Kn n ≃ₐ[K] towerLayer Kn n :=
  IntermediateField.restrictAlgEquiv (le_iSup Kn n)

/-- The union of Galois layers is Galois. -/
theorem isGalois_towerUnion (Kn : ℕ → IntermediateField K L)
    [∀ n, IsGalois K (Kn n)] : IsGalois K ↥(⨆ n, Kn n : IntermediateField K L) := by
  exact ⟨⟩

omit [NumberField K] in
/-- Restriction preserves the inclusions in an increasing tower. -/
theorem monotone_towerLayer (Kn : ℕ → IntermediateField K L)
    (hle : ∀ n, Kn n ≤ Kn (n + 1)) : Monotone (towerLayer Kn) := by
  intro m n hmn x hx
  apply (IntermediateField.mem_restrict _ x).2
  exact (monotone_nat_of_le_succ hle hmn) ((IntermediateField.mem_restrict _ x).1 hx)

omit [NumberField K] in
/-- The restricted layers exhaust their union. -/
theorem iSup_towerLayer (Kn : ℕ → IntermediateField K L)
    (hle : ∀ n, Kn n ≤ Kn (n + 1)) : ⨆ n, towerLayer Kn n = ⊤ := by
  apply top_unique
  intro x _
  have hx := x.property
  rw [← SetLike.mem_coe,
    IntermediateField.coe_iSup_of_directed (monotone_nat_of_le_succ hle).directed_le,
    Set.mem_iUnion] at hx
  obtain ⟨n, hn⟩ := hx
  exact (le_iSup (towerLayer Kn) n) ((IntermediateField.mem_restrict _ x).2 hn)

omit [NumberField K] in
/-- Galoisness transports to a layer restricted to the union. -/
theorem isGalois_towerLayer (Kn : ℕ → IntermediateField K L)
    [∀ n, IsGalois K (Kn n)] (n : ℕ) : IsGalois K (towerLayer Kn n) :=
  IsGalois.of_algEquiv (towerLayerEquiv Kn n)

/-- The Galois group of the union is the inverse limit of its restricted layers. -/
noncomputable def towerUnionGalEquivLimit (Kn : ℕ → IntermediateField K L)
    [∀ n, IsGalois K (Kn n)] (hle : ∀ n, Kn n ≤ Kn (n + 1)) :
    letI := isGalois_towerUnion Kn
    Gal(↥(⨆ n, Kn n : IntermediateField K L)/K) ≃ₜ*
      ↥(IntermediateField.galInvLimit (towerLayer Kn) (monotone_towerLayer Kn hle)) := by
  let := isGalois_towerUnion Kn
  let (n : ℕ) := isGalois_towerLayer Kn n
  exact IntermediateField.galContinuousMulEquivInvLimit
    (towerLayer Kn) (monotone_towerLayer Kn hle) (iSup_towerLayer Kn hle)

/-- Cyclic layers of degree p^n make their union a Z_p-extension. -/
theorem nonempty_towerUnion_zpExtension
    (Kn : ℕ → IntermediateField K L) [∀ n, NumberField (Kn n)]
    [∀ n, IsGalois K (Kn n)] [∀ n, IsCyclic Gal(Kn n/K)]
    (hle : ∀ n, Kn n ≤ Kn (n + 1))
    (hfinrank : ∀ n, Module.finrank K (Kn n) = p ^ n) :
    letI := isGalois_towerUnion Kn
    Nonempty (MvZpExtension p (Fin 1) K ↥(⨆ n, Kn n : IntermediateField K L)) := by
  classical
  let F := ↥(⨆ n, Kn n : IntermediateField K L)
  let E := towerLayer Kn
  let := isGalois_towerUnion Kn
  let (n : ℕ) := isGalois_towerLayer Kn n
  have hdim (n : ℕ) : FiniteDimensional K (Kn n) := .of_finrank_pos (by
    rw [hfinrank]; exact pow_pos (Fact.out : p.Prime).pos n)
  let (n : ℕ) : FiniteDimensional K (E n) :=
    (towerLayerEquiv Kn n).toLinearEquiv.finiteDimensional
  let (n : ℕ) : IsCyclic Gal(E n/K) :=
    (towerLayerEquiv Kn n).autCongr.isCyclic.mp inferInstance
  let r (n : ℕ) : Gal(F/K) →* Gal(E n/K) := AlgEquiv.restrictNormalHom (E n)
  have rs (n) : Function.Surjective (r n) :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E n) F
  have hk (n) : (r (n + 1)).ker ≤ (r n).ker := by
    rw [show (r (n + 1)).ker = (E (n + 1)).fixingSubgroup from
      IntermediateField.restrictNormalHom_ker _,
      show (r n).ker = (E n).fixingSubgroup from IntermediateField.restrictNormalHom_ker _]
    exact IntermediateField.fixingSubgroup_le (monotone_towerLayer Kn hle (Nat.le_succ n))
  let t (n) : Gal(E (n + 1)/K) →* Gal(E n/K) :=
    (r (n + 1)).liftOfSurjective (rs (n + 1)) ⟨r n, hk n⟩
  have rt (n) (x) : t n (r (n + 1) x) = r n x := by
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  obtain ⟨e⟩ := CyclicTower.nonempty_equiv_padic p r
    (fun n ↦ InfiniteGalois.restrictNormalHom_continuous (E n)) rs
    (fun x y h ↦ IntermediateField.toGalInvLimit_injective E
      (monotone_towerLayer Kn hle) (iSup_towerLayer Kn hle)
      (Subtype.ext (funext h))) t rt (fun n ↦ by
        rw [IsGalois.card_aut_eq_finrank]
        exact (towerLayerEquiv Kn n).toLinearEquiv.finrank_eq.symm.trans (hfinrank n))
  exact ⟨MvZpExtension.ofContinuousMulEquiv₁ e⟩

omit [NumberField K] in
/-- In a Z_p-extension, degree determines the layer. -/
theorem eq_layer_of_finrank_eq_pow {F : Type*} [Field F] [Algebra K F] [IsGalois K F]
    (H : MvZpExtension p (Fin 1) K F) (E : IntermediateField K F)
    [FiniteDimensional K E] (n : ℕ) (hn : Module.finrank K E = p ^ n) :
    E = H.Kn n := by
  obtain ⟨m, hm⟩ := H.eq_Kn_of_finiteDimensional E
  have hmn : m = n := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    change p ^ m = p ^ n
    rw [← H.finrank_Kn₁ m, ← hm, hn]
  simpa [hmn] using hm

/-- Once the union is identified as a Z_p-extension, its degree-p^n layers
recover the original tower and Iwasawa's formula transports back to it. -/
theorem multiplicity_classNumber_eq_of_union_zpExtension
    (Kn : ℕ → IntermediateField K L) [∀ n, NumberField (Kn n)]
    [IsGalois K ↥(⨆ n, Kn n : IntermediateField K L)]
    (H : MvZpExtension p (Fin 1) K ↥(⨆ n, Kn n : IntermediateField K L))
    (hfinrank : ∀ n, Module.finrank K (Kn n) = p ^ n) :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n > N,
      multiplicity p (NumberField.classNumber (Kn n)) = mu * p ^ n + lambda * n + nu := by
  have hclass (n : ℕ) : classNumber (Kn n) = classNumber (H.Kn n) := by
    let e := towerLayerEquiv Kn n
    have : FiniteDimensional K (Kn n) := .of_finrank_pos (by
      rw [hfinrank]
      exact pow_pos (Fact.out : p.Prime).pos n)
    have : FiniteDimensional K (towerLayer Kn n) := e.toLinearEquiv.finiteDimensional
    have he : towerLayer Kn n = H.Kn n := eq_layer_of_finrank_eq_pow H _ n
      (e.toLinearEquiv.finrank_eq.symm.trans (hfinrank n))
    exact classNumber_eq_of_ringEquiv
      ((e.trans (IntermediateField.equivOfEq he)).toRingEquiv)
  simpa only [hclass] using H.multiplicity_classNumber_Kn_eq₁

end NumberField
