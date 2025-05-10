/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.DedekindDomain.PID
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

section Missinglemmas

namespace Submodule

variable {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable {p : Submodule R M}
variable {r : R} {x : M}
variable (p)

lemma smul_mem_iff_of_isUnit (hr : IsUnit r) :
    r • x ∈ p ↔ x ∈ p :=
  let _ : Invertible r := hr.invertible
  smul_mem_iff'' p

end Submodule

namespace IsLocalization

section smul

variable {R : Type*} [CommSemiring R] {S : Submonoid R}
variable {R' : Type*} [CommSemiring R'] [Algebra R R'] [IsLocalization S R']
variable {M': Type*} [AddCommMonoid M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']

/-- If `x` in a `R' = S⁻¹ R`-module `M'`, then for a submodule `N'` of `M'`,
`s • x ∈ N'` if and only if `x ∈ N'` for some `s` in S. -/
lemma smul_mem_iff {N' : Submodule R' M'} {x : M'} {s : S} :
    s • x ∈ N' ↔ x ∈ N' := by
  refine ⟨fun h ↦ ?_, fun h ↦ Submodule.smul_of_tower_mem N' s h⟩
  rwa [← Submodule.smul_mem_iff_of_isUnit (r := algebraMap R R' s) N' (map_units R' s),
    algebraMap_smul]

end smul

end IsLocalization

section numerator

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']
variable {R' : Type*} [CommSemiring R'] [Algebra R R'] [Module R' M'] [IsLocalization S R']
variable [Module R M] [Module R M'] [IsScalarTower R R' M']
variable (f : M →ₗ[R] M') [IsLocalizedModule S f]

noncomputable def getNumerator (x : M') : M :=
  (Classical.choose (IsLocalizedModule.surj S f x)).1

/-- If the image of `getNumerator x` under `f`
is in a submodule `N'` of `M'`, then `x` itself lies in `N'`. -/
lemma mem_of_getNumerator_image_mem {N' : Submodule R' M'} {x : M'}
    (hx : f (getNumerator S f x) ∈ N') : x ∈ N' := by
  let Num := (getNumerator S f x)
  let Den := (Classical.choose (IsLocalizedModule.surj S f x)).2
  have h : Den • x = f Num := (Classical.choose_spec (IsLocalizedModule.surj S f x))
  rwa [← IsLocalization.smul_mem_iff (s := Den), h]

noncomputable def finsetNumerator [DecidableEq M] (s : Finset M') : Finset M :=
  Finset.image (getNumerator S f) s

end numerator

end Missinglemmas

namespace Module

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
    Set.mem_iUnion, Finset.mem_coe, finsetNumerator, Finset.mem_image, getNumerator, sf]
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
  exact ⟨fun h p ↦ h p.1, fun H p hp ↦ H ⟨p, hp⟩⟩

end Module

/-- If a semilocal integral domain which is not a field satisfies that it localized at all
maximal ideals is a PID, then itself is a PID. -/
theorem isPrincipalIdealRing_of_isPrincipalIdealRing_localization
    (A : Type*) [CommRing A] [IsDomain A] [Finite (MaximalSpectrum A)]
    (hpid : ∀ p : MaximalSpectrum A, IsPrincipalIdealRing (Localization p.1.primeCompl)) :
    IsPrincipalIdealRing A := by
  sorry

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
  sorry

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
      (e : ι → ℕ), M ∼ₚᵢₛ[A] ((i : ι) → A ⧸ (p i).1 ^ (e i)) := by
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
