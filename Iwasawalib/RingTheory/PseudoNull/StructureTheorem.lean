/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan, Yiming Fu, Shouxin Zhang
-/
module

public import Mathlib.Algebra.Module.PID
public import Mathlib.RingTheory.LocalProperties.Semilocal
public import Iwasawalib.RingTheory.PseudoNull.CharacteristicIdeal

@[expose] public section

/-!

# Structure theorem of finitely generated torsion module up to pseudo-isomorphism

-/

universe u

theorem PrimeSpectrum.localization_comap_range_eq_of_isDomain_of_primeHeight_eq_one
    {R : Type*} (S : Type*) [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]
    (s : Set (PrimeSpectrum R)) (hs : s ⊆ {p : PrimeSpectrum R | p.1.primeHeight = 1})
    (hn : s.Nonempty) (hfin : s.Finite) [IsLocalization (⨅ p ∈ s, p.1.primeCompl) S] :
    Set.range (PrimeSpectrum.comap (algebraMap R S)) = s ∪ {⟨⊥, Ideal.isPrime_bot⟩} := by
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
    have := Ideal.isPrime_bot (α := R)
    rw [Ideal.primeHeight_eq_zero_iff, minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self,
      Set.mem_singleton_iff] at hh
    left; ext1; exact hh
  · rcases h with h | h
    · rw [PrimeSpectrum.ext_iff] at h
      exact ⟨hn.some, hn.some_mem, by simp [h]⟩
    · exact ⟨p, h, le_rfl⟩

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

instance (priority := 100) IsKrullDomain.heightOneLocalizationIsPID
    (A : Type*) [CommRing A] [IsDomain A] [IsKrullDomain A] : HeightOneLocalizationIsPID A := by
  refine ⟨fun s hs hn hfin ↦ ?_⟩
  set S := ⨅ p ∈ s, p.1.primeCompl
  have hS : S ≤ nonZeroDivisors A :=
    iInf_le_of_le hn.some <| iInf_le_of_le hn.some_mem hn.some.1.primeCompl_le_nonZeroDivisors
  have : IsDomain (Localization S) := IsLocalization.isDomain_localization hS
  have := Ideal.isPrime_bot (α := A)
  refine ⟨‹_›, ?_⟩
  have hrange := PrimeSpectrum.localization_comap_range_eq_of_isDomain_of_primeHeight_eq_one
    (Localization S) s hs hn hfin
  have : Finite (MaximalSpectrum (Localization S)) := by
    refine @Finite.of_injective _ _ ?_ _ MaximalSpectrum.toPrimeSpectrum_injective
    refine @Finite.of_injective_finite_range _ _ _
      (PrimeSpectrum.localization_comap_injective (Localization S) S) (Set.Finite.to_subtype ?_)
    simp [hrange, hfin]
  apply isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal
    fun P _ ↦ Localization.AtPrime P
  suffices h : ∀ p : MaximalSpectrum (Localization S),
    IsPrincipalIdealRing (Localization p.1.primeCompl) from fun P hP ↦ h ⟨P, hP⟩
  intro p
  have hp := Set.mem_range_self (f := PrimeSpectrum.comap (algebraMap A (Localization S)))
    p.toPrimeSpectrum
  rw [hrange, Set.union_singleton, Set.mem_insert_iff] at hp
  rcases hp with hp | hp
  · have : p.1.primeCompl = nonZeroDivisors (Localization S) := by
      have hp' : PrimeSpectrum.comap (algebraMap A (Localization S)) ⟨⊥, Ideal.isPrime_bot⟩ =
          ⟨⊥, Ideal.isPrime_bot⟩ := by
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
    let e := IsLocalization.algEquiv
      (PrimeSpectrum.comap (algebraMap A (Localization S)) p.toPrimeSpectrum).1.primeCompl
      (Localization (PrimeSpectrum.comap (algebraMap A (Localization S))
        p.toPrimeSpectrum).1.primeCompl)
      (Localization p.1.primeCompl)
    exact IsPrincipalIdealRing.of_surjective e e.surjective

/-!

## Structure theorem under the assumption that height one localization is PID

-/

/-- The natural isomorphism `S⁻¹ker(f) ≃ ker(S⁻¹f)`. TODO: already in mathlib? -/
noncomputable def LinearMap.localizedModuleKerEquivKerLocalizedModuleMap
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (S : Submonoid A) :
    LocalizedModule S f.ker ≃ₗ[Localization S] (LocalizedModule.map S f).ker :=
  letI i : LocalizedModule S f.ker ≃ₗ[Localization S] (LocalizedModule.map S f.ker.subtype).range :=
    .ofInjective _ (LocalizedModule.map_injective S _ (Submodule.subtype_injective _))
  haveI h : ((LocalizedModule.map S) f).ker = ((LocalizedModule.map S) f.ker.subtype).range :=
    LinearMap.exact_iff.1 (LocalizedModule.map_exact S _ _ f.exact_subtype_ker_map)
  i ≪≫ₗ LinearEquiv.ofEq _ _ h.symm

/-- The natural isomorphism `S⁻¹coker(f) ≃ coker(S⁻¹f)`. TODO: already in mathlib? -/
noncomputable def LinearMap.localizedModuleCokerEquivCokerLocalizedModuleMap
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (S : Submonoid A) :
    LocalizedModule S (N ⧸ f.range) ≃ₗ[Localization S]
      LocalizedModule S N ⧸ (LocalizedModule.map S f).range :=
  letI i : LocalizedModule S (N ⧸ f.range) ≃ₗ[Localization S]
      (LocalizedModule S N) ⧸ ker (LocalizedModule.map S f.range.mkQ) := by
    refine ((LocalizedModule.map S f.range.mkQ).quotKerEquivOfSurjective ?_).symm
    exact LocalizedModule.map_surjective S f.range.mkQ (Submodule.mkQ_surjective f.range)
  haveI h : (LocalizedModule.map S f.range.mkQ).ker = ((LocalizedModule.map S) f).range :=
    LinearMap.exact_iff.1 (LocalizedModule.map_exact S _ _ f.exact_map_mkQ_range)
  i ≪≫ₗ Submodule.quotEquivOfEq _ _ h

/-- Let `A` be a Noetherian ring and let `M`, `N` be finitely generated torsion `A`-modules.
Let `s` be the set of height one primes in `Supp(M) ∪ Supp(N)`, let `S = A \ ⋃ p ∈ s, p`.
Then an `A`-linear map `f : M → N` is a pseudo-isomorphism if and only if
`S⁻¹f : S⁻¹M → S⁻¹N` is an isomorphism. -/
theorem LinearMap.isPseudoIsomorphism_iff_bijective_localizedModuleMap
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] (hMT : Module.IsTorsion A M)
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] (hNT : Module.IsTorsion A N)
    (f : M →ₗ[A] N) :
    f.IsPseudoIsomorphism ↔ Function.Bijective (LocalizedModule.map
      (⨅ p ∈ (Module.support A M ∪ Module.support A N) ∩
        {p : PrimeSpectrum A | p.1.primeHeight = 1}, p.1.primeCompl) f) := by
  set s := (Module.support A M ∪ Module.support A N) ∩ {p : PrimeSpectrum A | p.1.primeHeight = 1}
  have hs : s.Finite := by simpa only [← Set.union_inter_distrib_right] using
    hMT.finite_primeHeight_one_support.union hNT.finite_primeHeight_one_support
  rw [isPseudoIsomorphism_iff]
  apply and_congr
  · have := Module.isPseudoNull_iff_subsingleton_of_subset_of_isTorsion A f.ker hs
      (Set.inter_subset_inter_left _ (Set.subset_union_of_subset_left
        (Module.support_subset_of_injective _ f.ker.subtype_injective) _))
      Set.inter_subset_right (hMT.injective f.ker.subtype_injective)
    rw [this, ← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
      (f.localizedModuleKerEquivKerLocalizedModuleMap _).subsingleton_congr]
  · have := Module.isPseudoNull_iff_subsingleton_of_subset_of_isTorsion A (N ⧸ f.range) hs
      (Set.inter_subset_inter_left _ (Set.subset_union_of_subset_right
        (Module.support_subset_of_surjective _ f.range.mkQ_surjective) _))
      Set.inter_subset_right (hNT.surjective f.range.mkQ_surjective)
    rw [this, ← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff,
      (f.localizedModuleCokerEquivCokerLocalizedModuleMap _).subsingleton_congr]

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

/-- Let `A` be a Noetherian ring satisfying `HeightOneLocalizationIsPID`, `M` be a finitely
generated `A`-module, `T` be the torsion submodule of `M`. Then `M` is pseudo-isomorphic to
`T × M/T`. -/
theorem Module.isPseudoIsomorphic_torsion_prod_quotient
    {A : Type*} [CommRing A] [IsNoetherianRing A] [HeightOneLocalizationIsPID A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] :
    M ∼ₚᵢₛ[A] (Submodule.torsion A M × M ⧸ Submodule.torsion A M) := by
  sorry
