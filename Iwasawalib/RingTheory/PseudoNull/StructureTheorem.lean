/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan, Yiming Fu, Shouxin Zhang
-/
import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.KrullDimension.Zero
import Iwasawalib.RingTheory.PseudoNull.CharacteristicIdeal

/-!

# Structure theorem of finitely generated torsion module up to pseudo-isomorphism

-/

universe u

theorem PrimeSpectrum.localization_comap_range_eq_of_isDomain_of_primeHeight_eq_one
    {R : Type*} (S : Type*) [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]
    (s : Set (PrimeSpectrum R)) (hs : s ⊆ {p : PrimeSpectrum R | p.1.primeHeight = 1})
    (hn : s.Nonempty) (hfin : s.Finite) [IsLocalization (⨅ p ∈ s, p.1.primeCompl) S] :
    Set.range (PrimeSpectrum.comap (algebraMap R S)) = s ∪ {⟨⊥, Ideal.bot_prime⟩} := by
  set M := ⨅ p ∈ s, p.1.primeCompl
  rw [PrimeSpectrum.localization_comap_range S M]
  ext p
  simp_rw [Set.mem_setOf_eq, Set.union_singleton, Set.mem_insert_iff, M, Submonoid.coe_iInf,
    ← le_compl_iff_disjoint_left, Set.compl_iInter, Set.le_eq_subset]
  change _ ⊆ ⋃ p ∈ s, (p.1ᶜᶜ : Set R) ↔ _
  simp_rw [compl_compl]
  rw [← hfin.coe_toFinset, Ideal.subset_union_prime hn.some hn.some fun p _ _ _ ↦ p.2]
  simp_rw [Set.Finite.mem_toFinset, Set.Finite.coe_toFinset]
  refine ⟨fun ⟨q, hq, hle⟩ ↦ ?_, fun h ↦ ?_⟩
  · have : q.1.FiniteHeight := q.1.finiteHeight_iff.2 <| Or.inr <| by
      rw [Ideal.height_eq_primeHeight, hs hq]; nofun
    have hle' := hs hq ▸ Ideal.primeHeight_mono hle
    rcases eq_or_ne p.1.primeHeight 1 with hh | hh
    · have hmem := mem_minimalPrimes_of_primeHeight_eq_height hle
        (by rw [Ideal.height_eq_primeHeight, hs hq, hh])
      rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff,
        ← PrimeSpectrum.ext_iff] at hmem
      right; rwa [← hmem]
    replace hh := ENat.lt_one_iff_eq_zero.1 (hle'.lt_of_ne hh)
    have := Ideal.bot_prime (α := R)
    rw [Ideal.primeHeight_eq_zero_iff, minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self,
      Set.mem_singleton_iff] at hh
    left; ext1; exact hh
  · rcases h with h | h
    · rw [PrimeSpectrum.ext_iff] at h
      exact ⟨hn.some, hn.some_mem, by simp [h]⟩
    · exact ⟨p, h, le_rfl⟩

theorem RingEquiv.isPrincipalIdealRing {α β : Type*} [Semiring α] [Semiring β]
    [IsPrincipalIdealRing β] (e : α ≃+* β) : IsPrincipalIdealRing α where
  principal S := by
    obtain ⟨b, hb⟩ := IsPrincipalIdealRing.principal (S.map e.toRingHom)
    use e.symm.toRingHom b
    apply_fun Ideal.map e.symm.toRingHom at hb
    simp_rw [Ideal.map_map, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, Ideal.map_id] at hb
    simp_rw [hb, Ideal.submodule_span_eq, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    change Ideal.map e.symm _ = _
    rw [Ideal.map_symm]
    ext x
    simp_rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨fun ⟨a, ha⟩ ↦ ⟨e.symm a, ?_⟩, fun ⟨a, ha⟩ ↦ ⟨e a, ?_⟩⟩
    · simpa using congr(e.symm $(ha))
    · simpa using congr(e $(ha))

-- theorem MaximalSpectrum.localization_comap_range_eq_of_primeHeight_eq_one
--     {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
--     (s : Set (PrimeSpectrum R)) (hs : s ⊆ {p : PrimeSpectrum R | p.1.primeHeight = 1})
--     (hfin : s.Finite) [IsLocalization (⨅ p ∈ s, p.1.primeCompl) S] :
--     Set.range (PrimeSpectrum.comap (algebraMap R S) ∘ toPrimeSpectrum) = s := by
--   rcases s.eq_empty_or_nonempty with rfl | hn
--   · simp_all only [Set.empty_subset, Set.finite_empty, Set.mem_empty_iff_false, not_false_eq_true,
--       iInf_neg, iInf_top, Set.range_eq_empty_iff]
--     have := IsLocalization.subsingleton (R := R) (S := S) (M := ⊤) (Submonoid.mem_top 0)
--     exact toPrimeSpectrum.isEmpty
--   set M := ⨅ p ∈ s, p.1.primeCompl
--   have h1 := PrimeSpectrum.localization_comap_range S M
--   sorry

/-!

## Krull domain

-/

/-- An integral domain `A` is a Krull domain if it satisfies the following properties:

- `Aₚ` is a discrete valuation ring for every height one prime `p` of `A`.
- The intersection of all such `Aₚ` is equal to `A`.
- Any nonzero element of `A` is contained in only a finitely many height one primes of `A`.

See <https://en.wikipedia.org/wiki/Krull_ring>. -/
class IsKrullDomain (A : Type*) [CommRing A] [IsDomain A] : Prop where
  isDiscreteValuationRing_localization (p : PrimeSpectrum A) :
    p.1.primeHeight = 1 → IsDiscreteValuationRing (Localization p.1.primeCompl)
  biInf_eq_bot (A) : ⨅ p ∈ {p : PrimeSpectrum A | p.1.primeHeight = 1},
    Localization.subalgebra (FractionRing A) p.1.primeCompl p.1.primeCompl_le_nonZeroDivisors = ⊥
  finite (a : A) :
    a ≠ 0 → {p : PrimeSpectrum A | p.1.primeHeight = 1 ∧ a ∈ p.1}.Finite

instance (priority := 100) IsKrullDomain.isIntegrallyClosed
    (A : Type*) [CommRing A] [IsDomain A] [IsKrullDomain A] : IsIntegrallyClosed A := by
  sorry

instance (priority := 100) IsIntegrallyClosed.isKrullDomain_of_isNoetherianRing
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] :
    IsKrullDomain A := by
  sorry

/-- A Noetherian ring is a Krull domain if and only if it is an integrally closed domain. -/
theorem isKrullDomain_iff_isIntegrallyClosed
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] :
    IsKrullDomain A ↔ IsIntegrallyClosed A :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance (priority := 100) UniqueFactorizationMonoid.isKrullDomain
    (A : Type*) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] : IsKrullDomain A := by
  sorry

/-!

## Height one localization is PID

-/

/-- A typeclass asserting that for any finitely many height one primes `p₁, ..., pₙ` of `A`,
let `S = A \ ⋃ i, pᵢ`, then `S⁻¹A` is a PID. -/
class HeightOneLocalizationIsPID (A : Type*) [CommRing A] : Prop where
  isPrincipalIdealRing_localization (s : Set (PrimeSpectrum A)) :
    s ⊆ {p : PrimeSpectrum A | p.1.primeHeight = 1} → s.Nonempty → s.Finite →
    IsDomain (Localization (⨅ p ∈ s, p.1.primeCompl)) ∧
    IsPrincipalIdealRing (Localization (⨅ p ∈ s, p.1.primeCompl))

namespace IsLocalizedModule

section numerator

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']
variable {R' : Type*} [CommSemiring R'] [Algebra R R'] [Module R' M'] [IsLocalization S R']
variable [Module R M] [Module R M'] [IsScalarTower R R' M']
variable (f : M →ₗ[R] M') [IsLocalizedModule S f]

private noncomputable def getNumerator (x : M') : M :=
  (Classical.choose (IsLocalizedModule.surj S f x)).1

/-- If the image of `getNumerator x` under `f`
is in a submodule `N'` of `M'`, then `x` itself lies in `N'`. -/
private lemma mem_of_getNumerator_image_mem {N' : Submodule R' M'} {x : M'}
    (hx : f (getNumerator S f x) ∈ N') : x ∈ N' := by
  let Num := (getNumerator S f x)
  let Den := (Classical.choose (IsLocalizedModule.surj S f x)).2
  have h : Den • x = f Num := (Classical.choose_spec (IsLocalizedModule.surj S f x))
  rwa [← IsLocalization.smul_mem_iff (s := Den), h]

private noncomputable def finsetNumerator [DecidableEq M] (s : Finset M') : Finset M :=
  Finset.image (getNumerator S f) s

end numerator

end IsLocalizedModule

namespace Module

open IsLocalizedModule

variable {R : Type*} [CommSemiring R] [Finite (MaximalSpectrum R)]
variable (M : Type*) [AddCommMonoid M] [Module R M]

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommSemiring (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]

include f in
theorem finite_of_finite_isLocalized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal], Module.Finite (Rₚ P) (Mₚ P)) :
    Module.Finite R M := by
  classical
  let _ : Fintype ({ P : Ideal R | P.IsMaximal }) := by
    rw [← MaximalSpectrum.range_asIdeal]
    exact Fintype.ofFinite (Set.range MaximalSpectrum.asIdeal)
  constructor
  let _ {P : { P : Ideal R | P.IsMaximal }} : P.1.IsMaximal := P.2
  choose s₁ s₂ using (fun P : { P : Ideal R | P.IsMaximal } ↦ (H P.1).1)
  let sf := fun P : { P : Ideal R | P.IsMaximal } ↦
    finsetNumerator P.1.primeCompl (f P.1) (s₁ P)
  use Finset.biUnion (Finset.univ) sf
  let N : Submodule R M := Submodule.span R (Finset.univ.biUnion sf)
  apply Submodule.eq_top_of_localization_maximal Rₚ Mₚ f
  intro P hP
  rw [← top_le_iff, ← s₂ ⟨P, hP⟩]
  simp only [Submodule.localized'_span, N]
  apply Submodule.span_le.2
  intro x hx
  lift x to s₁ ⟨P, hP⟩ using hx
  rw [SetLike.mem_coe]
  let Num := (getNumerator P.primeCompl (f P) x)
  apply mem_of_getNumerator_image_mem P.primeCompl (f P)
  refine Submodule.mem_span.mpr fun p a => a ?_
  simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_image,
    Set.mem_iUnion, Finset.mem_coe, finsetNumerator, Finset.mem_image, sf]
  exact ⟨Num, ⟨⟨P, hP⟩, ⟨x, ⟨x.2, rfl⟩⟩⟩, rfl⟩

theorem finite_of_finite_localized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal],
      Module.Finite (Localization P.primeCompl) (LocalizedModule P.primeCompl M)) :
    Module.Finite R M :=
  finite_of_finite_isLocalized_maximal M _ _ (fun _ _ ↦ LocalizedModule.mkLinearMap _ _) H

theorem finite_of_finite_localized_maximal'
    (H : ∀ p : MaximalSpectrum R,
      Module.Finite (Localization p.1.primeCompl) (LocalizedModule p.1.primeCompl M)) :
    Module.Finite R M := by
  apply finite_of_finite_localized_maximal
  convert H
  exact ⟨fun h p ↦ h p.1, fun H P hP ↦ H ⟨P, hP⟩⟩

end Module

namespace Submodule

variable {R : Type*} [CommSemiring R] [Finite (MaximalSpectrum R)]
variable {M : Type*} [AddCommMonoid M] [Module R M] (N : Submodule R M)

theorem fg_of_fg_localized_maximal'
    (H : ∀ p : MaximalSpectrum R, (localized (p.1.primeCompl) N).FG) :
    N.FG := by
  simp_rw [← Module.Finite.iff_fg] at ⊢ H
  apply Module.finite_of_finite_localized_maximal'
  convert H
  exact Module.Finite.equiv_iff (Submodule.localizedEquiv _ N).symm

end Submodule

namespace Ring

-- TODO: Generalize this to `ringKrullDim` for `CommSemiring A`.
/-- If a commutative domain `A` satisfies that its localization at all maximal ideals is `Ring.DimensionLEOne`,
then `A` itself is `Ring.DimensionLEOne`. -/
lemma dimensionLEOne_of_dimensionLEOne_localization_maximal {A : Type*} [CommRing A] [IsDomain A]
    (h : ∀ (P : Ideal A) [P.IsMaximal], Ring.DimensionLEOne (Localization P.primeCompl)) :
    Ring.DimensionLEOne A where
  maximalOfPrime := by
    intro p hp hpp
    rcases p.exists_le_maximal (Ideal.IsPrime.ne_top hpp) with ⟨q, hq, hpq⟩
    let f := (IsLocalization.orderIsoOfPrime q.primeCompl (Localization.AtPrime q)).symm
    let P := f ⟨p, hpp, hpq.disjoint_compl_left⟩
    let Q := f ⟨q, hq.isPrime, Set.disjoint_left.mpr fun _ a => a⟩
    have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
      IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors
    have hp1 : P.1 ≠ ⊥ := fun x => hp ((p.map_eq_bot_iff_of_injective hinj).mp x)
    have hq1 : Q.1 ≠ ⊥ :=
      fun x => (ne_bot_of_le_ne_bot hp hpq) ((q.map_eq_bot_iff_of_injective hinj).mp x)
    by_cases hqf : IsField (Localization.AtPrime q)
    · let _ : Field (Localization.AtPrime q) := by exact hqf.toField
      have huq : ∃! P : Ideal (Localization.AtPrime q), P.IsPrime :=
        Ring.KrullDimLE.existsUnique_isPrime (Localization.AtPrime q)
      rw [show p = q from Subtype.val_inj.mpr <| f.injective <|
        Subtype.val_inj.mp (huq.unique P.2 Q.2)]
      exact hq
    · have huq : ∃! P : Ideal (Localization.AtPrime q), P ≠ ⊥ ∧ P.IsPrime := by
        obtain ⟨P, hP⟩ := Ring.not_isField_iff_exists_prime.1 hqf
        refine ⟨P, ⟨hP, fun Q hQ ↦ ?_⟩⟩
        have hpm := Ideal.IsPrime.isMaximal hP.2 hP.1
        have hqm := Ideal.IsPrime.isMaximal hQ.2 hQ.1
        exact (IsLocalRing.maximal_ideal_unique _).unique hqm hpm
      rw [show p = q from Subtype.val_inj.mpr <| f.injective <|
        Subtype.val_inj.mp (huq.unique ⟨hp1, P.2⟩ ⟨hq1, Q.2⟩)]
      exact hq

lemma dimensionLEOne_of_dimensionLEOne_localization_maximal' {A : Type*} [CommRing A] [IsDomain A]
    (h : ∀ p : MaximalSpectrum A, Ring.DimensionLEOne (Localization p.1.primeCompl)) :
    Ring.DimensionLEOne A := by
  apply dimensionLEOne_of_dimensionLEOne_localization_maximal
  convert h
  exact ⟨fun h p ↦ h p.1, fun H P hP ↦ H ⟨P, hP⟩⟩

end Ring

/-- If a semilocal integral domain satisfies that it localized at all
maximal ideals is a PID, then itself is a PID. -/
theorem isPrincipalIdealRing_of_isPrincipalIdealRing_localization
    (A : Type*) [CommRing A] [IsDomain A] [Finite (MaximalSpectrum A)]
    (hpid : ∀ p : MaximalSpectrum A, IsPrincipalIdealRing (Localization p.1.primeCompl)) :
    IsPrincipalIdealRing A := by
  have : IsNoetherianRing A := by
    constructor
    intro N
    refine Submodule.fg_of_fg_localized_maximal' N (fun p ↦ ?_)
    exact IsNoetherian.noetherian (Submodule.localized p.asIdeal.primeCompl N)
  have : IsIntegrallyClosed A := by
    apply IsIntegrallyClosed.of_localization_maximal
    intro P _ hP
    let p : MaximalSpectrum A := ⟨P, hP⟩
    show IsIntegrallyClosed (Localization p.1.primeCompl)
    infer_instance
  have : Ring.DimensionLEOne A := by
    apply Ring.dimensionLEOne_of_dimensionLEOne_localization_maximal'
    infer_instance
  have : IsDedekindDomain A := {maximalOfPrime := Ring.DimensionLEOne.maximalOfPrime}
  have hp_sub : {P : Ideal A | P.IsPrime} ⊆ {P : Ideal A | P.IsMaximal} ∪ {⊥} := by
    simp only [Set.mem_setOf_eq, Set.union_singleton, Set.mem_insert_iff]
    intro P hP
    obtain rfl | hbot := eq_or_ne P ⊥
    · simp
    · simp only [Set.mem_insert_iff, hbot, Set.mem_setOf_eq, false_or]
      exact Ring.DimensionLEOne.maximalOfPrime hbot hP
  have hp_finite : {P : Ideal A | P.IsPrime}.Finite := by
    refine Set.Finite.subset (Set.Finite.union ?_ (Set.finite_singleton ⊥)) hp_sub
    rw [← MaximalSpectrum.range_asIdeal]
    exact Set.finite_range MaximalSpectrum.asIdeal
  exact IsPrincipalIdealRing.of_finite_primes hp_finite

instance (priority := 100) IsKrullDomain.heightOneLocalizationIsPID
    (A : Type*) [CommRing A] [IsDomain A] [IsKrullDomain A] : HeightOneLocalizationIsPID A := by
  refine ⟨fun s hs hn hfin ↦ ?_⟩
  set S := ⨅ p ∈ s, p.1.primeCompl
  have hS : S ≤ nonZeroDivisors A :=
    iInf_le_of_le hn.some <| iInf_le_of_le hn.some_mem hn.some.1.primeCompl_le_nonZeroDivisors
  have : IsDomain (Localization S) := IsLocalization.isDomain_of_le_nonZeroDivisors A hS
  have := Ideal.bot_prime (α := A)
  refine ⟨‹_›, ?_⟩
  have hrange := PrimeSpectrum.localization_comap_range_eq_of_isDomain_of_primeHeight_eq_one
    (Localization S) s hs hn hfin
  have : Finite (MaximalSpectrum (Localization S)) := by
    refine @Finite.of_injective _ _ ?_ _ MaximalSpectrum.toPrimeSpectrum_injective
    refine @Finite.of_injective_finite_range _ _ _
      (PrimeSpectrum.localization_comap_injective (Localization S) S) (Set.Finite.to_subtype ?_)
    simp [hrange, hfin]
  refine isPrincipalIdealRing_of_isPrincipalIdealRing_localization _ fun p ↦ ?_
  have hp := Set.mem_range_self (f := PrimeSpectrum.comap (algebraMap A (Localization S)))
    p.toPrimeSpectrum
  rw [hrange, Set.union_singleton, Set.mem_insert_iff] at hp
  rcases hp with hp | hp
  · have : p.1.primeCompl = nonZeroDivisors (Localization S) := by
      have hp' : PrimeSpectrum.comap (algebraMap A (Localization S)) ⟨⊥, Ideal.bot_prime⟩ =
          ⟨⊥, Ideal.bot_prime⟩ := by
        ext1
        exact Ideal.comap_bot_of_injective (algebraMap A (Localization S))
          (IsLocalization.injective _ hS)
      have := congr($(PrimeSpectrum.localization_comap_injective (Localization S) S (hp' ▸ hp)).1)
      change p.1 = ⊥ at this
      ext
      simp_rw [mem_nonZeroDivisors_iff_ne_zero, this]
      change _ ∈ ((⊥ : Ideal (Localization S)) : Set (Localization S))ᶜ ↔ _
      simp
    rw [this]
    infer_instance
  · replace hp := IsKrullDomain.isDiscreteValuationRing_localization _ (hs hp)
    have : IsLocalization
        (PrimeSpectrum.comap (algebraMap A (Localization S)) p.toPrimeSpectrum).1.primeCompl
        (Localization p.1.primeCompl) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S
        (Localization p.1.primeCompl) p.1
    exact IsLocalization.algEquiv
      (PrimeSpectrum.comap (algebraMap A (Localization S)) p.toPrimeSpectrum).1.primeCompl
      (Localization (PrimeSpectrum.comap (algebraMap A (Localization S))
        p.toPrimeSpectrum).1.primeCompl)
      (Localization p.1.primeCompl) |>.symm.toRingEquiv.isPrincipalIdealRing

/-!

## Structure theorem under the assumption that height one localization is PID

-/

private lemma subsingleton_convert {A : Type*} [CommRing A] [IsNoetherianRing A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] (hMT : Module.IsTorsion A M)
  {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] (hNT : Module.IsTorsion A N)
  (X : Type*) [AddCommGroup X] [Module A X] [Module.Finite A X] :
  let sigma := (Module.support A M ∪ Module.support A N) ∩
    {p : PrimeSpectrum A | p.1.primeHeight = 1}
  let S := ⨅ p ∈ sigma, p.1.primeCompl
  Subsingleton (LocalizedModule S X) ↔ (∀ p ∈ sigma, Subsingleton (LocalizedModule p.1.primeCompl X)) := by
  intro sigma S
  constructor
  . intro hS p hp
    simp only [S] at hS
    rw [LocalizedModule.subsingleton_iff] at hS ⊢
    intro m
    specialize hS m
    obtain ⟨r, ⟨hrmem, hreq⟩⟩ := hS
    use r, by
      apply Set.mem_of_subset_of_mem ?_ hrmem
      simp only [Submonoid.coe_iInf, Set.biInter_subset_of_mem hp]
  . intro h
    simp_rw [LocalizedModule.subsingleton_iff] at h ⊢
    intro k
    obtain ⟨s_a, hmem, hnotmem⟩ : ∃ s_a ∈ Module.annihilator A X, s_a ∉ ⋃ p ∈ sigma, p.1 := by
      simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop, not_exists, not_and]
      have h_not_subset : ¬((Module.annihilator A X : Set A) ⊆ ⋃ p ∈ sigma, ↑p.asIdeal) := by
        intro h_sub
        haveI : Fintype ↑sigma := by
          refine Set.Finite.fintype ?_
          unfold sigma
          rw [Set.union_inter_distrib_right]
          refine Set.Finite.union ?_ ?_
          all_goals exact Module.IsTorsion.finite_primeHeight_one_support ‹_›
        let t : Finset (PrimeSpectrum A) := sigma.toFinset
        have h_not_le : ∀ p ∈ sigma, ¬(Module.annihilator A X ≤ p.asIdeal) := by
          intro p hp
          specialize h p hp
          rwa [← LocalizedModule.subsingleton_iff, ← Module.notMem_support_iff, Module.mem_support_iff_of_finite] at h
        obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b, a ∈ t ∧ b ∈ t ∧ a ≠ b := by
          suffices Nontrivial t by
            rw [nontrivial_iff] at this
            obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := this
            use a, b, ha, hb
            simpa using hab
          convert_to Nontrivial sigma; simp [t]
          simp only [Set.nontrivial_coe_sort]
          obtain ⟨p, hp⟩ : sigma.Nonempty := by
            rw [@Set.nonempty_iff_ne_empty]
            intro h
            replace h_sub : ∀ (x : A), x ∉ ↑(Module.annihilator A X) := by
              simpa [h, Set.eq_empty_iff_forall_notMem] using h_sub
            specialize h_sub 0
            simp at h_sub
          rw [← Set.not_subsingleton_iff]
          intro h
          rw [Set.subsingleton_iff_singleton hp] at h
          simp only [h, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left, SetLike.coe_subset_coe,
            forall_eq] at h_sub h_not_le
          contradiction
        rw [show sigma = t by simp [t]] at h_sub h_not_le
        have hp : ∀ i ∈ t, (i.asIdeal).IsPrime := fun i _ => i.isPrime
        rw [Ideal.subset_union_prime a b (fun i hi _ _ => hp i hi)] at h_sub
        obtain ⟨i, hi, hle⟩ := h_sub
        exact h_not_le i hi hle
      obtain ⟨s_a, hs_a⟩ := Set.not_subset.mp h_not_subset
      simp only [SetLike.mem_coe, Set.mem_iUnion, exists_prop, not_exists, not_and] at hs_a
      exact ⟨s_a, hs_a.1, hs_a.2⟩
    use s_a, by
      simp_rw [S, Submonoid.mem_iInf]
      intro p hp
      simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop, not_exists, not_and] at hnotmem
      simp [Ideal.primeCompl, hnotmem p hp]
    rw [Module.mem_annihilator] at hmem
    simp [hmem k]

private lemma LinearMap.subsingleton_ker_convert
  {A : Type*} [CommRing A]
  {M : Type*} [AddCommGroup M] [Module A M]
  {N : Type*} [AddCommGroup N] [Module A N]
  (f : M →ₗ[A] N) (S : Submonoid A):
  Subsingleton ↥(ker ((LocalizedModule.map S) f)) ↔ Subsingleton (LocalizedModule S (LinearMap.ker f)) := by
  have h_exact : Function.Exact (LocalizedModule.map S (ker f).subtype) (LocalizedModule.map S f) :=
    LocalizedModule.map_exact S _ _ (f.exact_subtype_ker_map)
  rw [LinearMap.exact_iff] at h_exact
  rw [h_exact]
  have : LocalizedModule S ↥(ker f) ≃ₗ[Localization S] range (LocalizedModule.map S (ker f).subtype) := by
    apply LinearEquiv.ofInjective
    exact LocalizedModule.map_injective S _ (Submodule.subtype_injective _)
  rw [Equiv.subsingleton_congr this.toEquiv]

private lemma LinearMap.subsingleton_coker_convert
  {A : Type*} [CommRing A]
  {M : Type*} [AddCommGroup M] [Module A M]
  {N : Type*} [AddCommGroup N] [Module A N]
  (f : M →ₗ[A] N) (S : Submonoid A):
  Subsingleton (LocalizedModule S N ⧸ range ((LocalizedModule.map S) f)) ↔ Subsingleton (LocalizedModule S (N ⧸ LinearMap.range f)) := by
  have h_exact : Function.Exact (LocalizedModule.map S f)
      (LocalizedModule.map S (range f).mkQ) :=
    LocalizedModule.map_exact S _ _ (f.exact_map_mkQ_range)
  rw [LinearMap.exact_iff] at h_exact
  have : LocalizedModule S (N ⧸ range f) ≃ₗ[Localization S]
    (LocalizedModule S N) ⧸ ker (LocalizedModule.map S (range f).mkQ) := by
    refine (((LocalizedModule.map S) (range f).mkQ).quotKerEquivOfSurjective ?_).symm
    refine LocalizedModule.map_surjective S (range f).mkQ ?_
    exact Submodule.mkQ_surjective (range f)
  rw [h_exact] at this
  exact Equiv.subsingleton_congr this.symm.toEquiv

/-- Let `A` be a Noetherian ring and let `M`, `N` be finitely generated torsion `A`-modules.
Let `p₁, ..., pₙ` be all height one primes in `Supp(M) ∪ Supp(N)`, let `S = A \ ⋃ i, pᵢ`.
Then an `A`-linear map `f : M → N` is a pseudo-isomorphism if and only if
`S⁻¹f : S⁻¹M → S⁻¹N` is an isomorphism. -/
theorem LinearMap.isPseudoIsomorphism_iff_bijective_map
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] (hMT : Module.IsTorsion A M)
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] (hNT : Module.IsTorsion A N)
    (f : M →ₗ[A] N) :
    f.IsPseudoIsomorphism ↔ Function.Bijective (LocalizedModule.map
      (⨅ p ∈ (Module.support A M ∪ Module.support A N) ∩
        {p : PrimeSpectrum A | p.1.primeHeight = 1}, p.1.primeCompl) f) := by
  set sigma := (Module.support A M ∪ Module.support A N) ∩
    {p : PrimeSpectrum A | p.1.primeHeight = 1} with hsigma
  set S := ⨅ p ∈ sigma, p.1.primeCompl with hS
  set K := LinearMap.ker f
  simp_rw [isPseudoIsomorphism_iff, Module.isPseudoNull_iff_primeHeight_le_one_imp_subsingleton, Function.Bijective]
  rw [← ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot, subsingleton_ker_convert]
  rw [← range_eq_top, ← Submodule.subsingleton_quotient_iff_eq_top, subsingleton_coker_convert]
  simp_rw [S, sigma, subsingleton_convert hMT hNT, ← hsigma]
  refine and_congr ?_ ?_
  . refine forall_congr' fun p => ?_
    constructor
    . rintro hp₁ hp
      apply hp₁
      rw [Set.mem_inter_iff] at hp
      simp [show p.asIdeal.primeHeight = 1 by simpa using hp.2]
    . rintro hp hp₁
      rw [Decidable.le_iff_eq_or_lt, ENat.lt_one_iff_eq_zero] at hp₁
      rcases hp₁ with hp₁ | hp₁
      . by_cases hpmem : p ∈ sigma
        . exact hp hpmem
        replace hpmem : p ∉ Module.support A M ∧ p ∉ Module.support A N := by simpa [hp₁, sigma] using hpmem
        replace hpmem := hpmem.1
        rw [← Module.notMem_support_iff]
        contrapose! hpmem
        have : Module.support A ↥(ker f) ⊆ Module.support A M :=
          Module.support_subset_of_injective (Submodule.subtype (ker f)) Subtype.val_injective
        exact this hpmem
      . rw [Ideal.primeHeight_eq_zero_iff] at hp₁
        rw [LocalizedModule.subsingleton_iff]
        rintro ⟨m, hm⟩
        simp only [SetLike.mk_smul_mk, Submodule.mk_eq_zero]
        have hK_is_torsion : Module.IsTorsion A K := by
          unfold Module.IsTorsion at hMT ⊢
          rintro ⟨x, hx⟩
          simpa using @hMT x
        obtain ⟨⟨s, hsne⟩, hs⟩ := @hK_is_torsion ⟨m, hm⟩
        use s, ?_, by simpa using hs
        have := Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp₁
        rw [Set.disjoint_right] at this
        apply this
        simpa
  . refine forall_congr' fun p => ?_
    constructor
    . rintro hp₁ hp
      apply hp₁
      rw [Set.mem_inter_iff] at hp
      simp [show p.asIdeal.primeHeight = 1 by simpa using hp.2]
    . rintro hp hp₁
      rw [Decidable.le_iff_eq_or_lt, ENat.lt_one_iff_eq_zero] at hp₁
      rcases hp₁ with hp₁ | hp₁
      . by_cases hpmem : p ∈ sigma
        . exact hp hpmem
        replace hpmem : p ∉ Module.support A M ∧ p ∉ Module.support A N := by simpa [hp₁, sigma] using hpmem
        replace hpmem := hpmem.2
        rw [← Module.notMem_support_iff]
        contrapose! hpmem
        have : Module.support A (N ⧸ range f) ⊆ Module.support A N :=
          Module.support_subset_of_surjective (range f).mkQ (Submodule.mkQ_surjective (range f))
        exact this hpmem
      . rw [Ideal.primeHeight_eq_zero_iff] at hp₁
        rw [LocalizedModule.subsingleton_iff]
        intro m
        have hK_is_torsion : Module.IsTorsion A (N ⧸ range f) := by
          unfold Module.IsTorsion at hNT ⊢
          intro x
          obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (range f) x
          obtain ⟨a, ha⟩ := @hNT y
          use a, by simp [← Submodule.Quotient.mk_smul (range f), ha]
        obtain ⟨⟨s, hsne⟩, hs⟩ := @hK_is_torsion m
        use s, ?_, by simpa using hs
        have := Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp₁
        rw [Set.disjoint_right] at this
        apply this
        simpa

-- #check DirectSum.linearEquivFunOnFintype
-- #check Module.equiv_directSum_of_isTorsion

/-- **Structure theorem of finitely generated torsion modules up to pseudo-isomorphism**:
A finitely generated torsion module over a Noetherian ring `A` satisfying
`HeightOneLocalizationIsPID` is pseudo-isomorphic to a finite product of some `A ⧸ pᵢ ^ eᵢ`
where the `pᵢ ^ eᵢ` are powers of height one primes of `A`. -/
theorem Module.IsTorsion.isPseudoIsomorphic_pi
    {A : Type u} [CommRing A] [IsNoetherianRing A] [HeightOneLocalizationIsPID A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] (hMT : Module.IsTorsion A M) :
    ∃ (ι : Type u) (_ : Fintype ι) (p : ι → PrimeSpectrum A) (_ : ∀ i, (p i).1.primeHeight = 1)
      (e : ι → ℕ) (_ : ∀ i, 0 < e i), M ∼ₚᵢₛ[A] ((i : ι) → A ⧸ (p i).1 ^ (e i)) := by
  sorry

/-- Let `A` be a Noetherian ring satisfying `HeightOneLocalizationIsPID`. Then two finitely
generated torsion `A`-modules `M`, `N` are pseudo-isomorphic if and only if their localizations
at all height one primes are isomorphic. -/
theorem Module.IsTorsion.isPseudoIsomorphic_iff_nonempty_linearEquiv_localizedModule
    {A : Type*} [CommRing A] [IsNoetherianRing A] [HeightOneLocalizationIsPID A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] (hMT : Module.IsTorsion A M)
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] (hNT : Module.IsTorsion A N) :
    M ∼ₚᵢₛ[A] N ↔ ∀ p : PrimeSpectrum A, p.1.primeHeight = 1 →
      Nonempty ((LocalizedModule p.1.primeCompl M) ≃ₗ[Localization p.1.primeCompl]
        (LocalizedModule p.1.primeCompl N)) := by
  sorry

/-- Let `A` be a Noetherian ring satisfying `HeightOneLocalizationIsPID`. Then pseudo-isomorphic
between two finitely generated torsion `A`-modules are symmectric. -/
theorem Module.IsPseudoIsomorphic.symm
    {A : Type*} [CommRing A] [IsNoetherianRing A] [HeightOneLocalizationIsPID A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] (hMT : Module.IsTorsion A M)
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] (hNT : Module.IsTorsion A N)
    (H : M ∼ₚᵢₛ[A] N) : N ∼ₚᵢₛ[A] M := by
  rw [hMT.isPseudoIsomorphic_iff_nonempty_linearEquiv_localizedModule hNT] at H
  rw [hNT.isPseudoIsomorphic_iff_nonempty_linearEquiv_localizedModule hMT]
  convert H using 2
  exact ⟨fun ⟨f⟩ ↦ ⟨f.symm⟩, fun ⟨f⟩ ↦ ⟨f.symm⟩⟩

/-- Let `A` be a Noetherian ring satisfying `HeightOneLocalizationIsPID`. Then pseudo-isomorphic
between two finitely generated torsion `A`-modules are symmectric. -/
theorem Module.isPseudoIsomorphic_comm
    {A : Type*} [CommRing A] [IsNoetherianRing A] [HeightOneLocalizationIsPID A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] (hMT : Module.IsTorsion A M)
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] (hNT : Module.IsTorsion A N) :
    M ∼ₚᵢₛ[A] N ↔ N ∼ₚᵢₛ[A] M :=
  ⟨fun H ↦ H.symm hMT hNT, fun H ↦ H.symm hNT hMT⟩
