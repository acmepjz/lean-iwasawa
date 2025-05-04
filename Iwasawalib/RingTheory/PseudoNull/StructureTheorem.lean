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
set_option diagnostics true

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
    (Localization.mapToFractionRing (FractionRing A) p.1.primeCompl (Localization p.1.primeCompl)
      p.1.primeCompl_le_nonZeroDivisors).range = ⊥
  finite (a : A) :
    a ≠ 0 → {p : PrimeSpectrum A | p.1.primeHeight = 1 ∧ a ∈ p.1}.Finite

instance (priority := 100) IsKrullDomain.isIntegrallyClosed
    (A : Type*) [CommRing A] [IsDomain A] [IsKrullDomain A] : IsIntegrallyClosed A := by
  have notField : ∀ (p : PrimeSpectrum A), p.1.primeHeight = 1 → ¬IsField (Localization p.1.primeCompl) := by
    intros p hp
    have : IsDiscreteValuationRing (Localization p.1.primeCompl) := IsKrullDomain.isDiscreteValuationRing_localization _ hp
    apply IsDiscreteValuationRing.not_isField
  have pisDVR : ∀ (p : PrimeSpectrum A), p.1.primeHeight = 1 → IsDiscreteValuationRing (Localization p.1.primeCompl) := by
    intros p hp
    exact IsKrullDomain.isDiscreteValuationRing_localization _ hp
  have pisIntegrallyclosed : ∀ (p : PrimeSpectrum A), p.1.primeHeight = 1 → IsIntegrallyClosed (Localization p.1.primeCompl) := by
    intros p hp
    have : IsDiscreteValuationRing (Localization p.1.primeCompl) := IsKrullDomain.isDiscreteValuationRing_localization _ hp
    have : IsIntegrallyClosed (Localization p.asIdeal.primeCompl) ∧ ∃! (P : Ideal (Localization p.asIdeal.primeCompl)), P ≠ ⊥ ∧ P.IsPrime := by
      apply ((IsDiscreteValuationRing.TFAE _ (notField p hp)).out 0 3).mp
      exact pisDVR p hp
    exact this.1
  unfold IsIntegrallyClosed IsIntegrallyClosedIn
  apply  IsIntegralClosure.mk
  · exact FaithfulSMul.algebraMap_injective A (FractionRing A)
  · intro x
    constructor
    · intro h
      rw [IsIntegral] at h
      obtain ⟨l, hl_monic, hl_eval⟩ := h
      --have :∀ p : PrimeSpectrum A, p.1.primeHeight = 1 → ∀ x ∈ A, x ∈ (Localization p.1.primeCompl) := by
      --have : ∀ p ∈ {p : PrimeSpectrum A | p.1.primeHeight = 1}, l ∈ Polynomial (Localization p.1.primeCompl) := by sorry
      --apply (IsIntegralClosure.mk _ _).isIntegral _ this
      sorry
    · intro h
      rw [IsIntegral] at ⊢
      obtain ⟨p, hp_monic, hp_eval⟩ := h
      exact RingHom.isIntegralElem_map (algebraMap A (FractionRing A))

#check Ideal.minimalPrimes
#check Localization.AtPrime.map_eq_maximalIdeal
#check IsAssociatedPrime
#check primesOver_finite
--#check Ring.KrullDimLE.existsUnique_isPrime


instance (priority := 100) IsIntegrallyClosed.isKrullDomain_of_isNoetherianRing
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] :
    IsKrullDomain A := by
  apply IsKrullDomain.mk
  · intro p hp
    have IsLocalRingAp : IsLocalRing (Localization p.1.primeCompl) := Localization.AtPrime.isLocalRing p.asIdeal
    have IsIntegralClosedAp : IsIntegrallyClosed (Localization p.1.primeCompl) := by
      apply isIntegrallyClosed_of_isLocalization (Localization p.asIdeal.primeCompl) p.1.primeCompl
      exact Ideal.primeCompl_le_nonZeroDivisors p.asIdeal
    have IsNoetherianRingAp : IsNoetherianRing (Localization p.1.primeCompl) := by
      apply  IsLocalization.isNoetherianRing p.asIdeal.primeCompl
      infer_instance
    have notField: ¬IsField (Localization p.1.primeCompl) := by
      refine Ring.not_isField_iff_exists_prime.mpr ?_
      set P := Ideal.map (algebraMap A (Localization p.1.primeCompl)) p.1
      use P
      constructor
      · sorry
      · sorry
    have UniquePrime : ∃! P : Ideal (Localization p.1.primeCompl), P ≠ ⊥ ∧ P.IsPrime := by
      have UniqueMax : ∃! I : Ideal (Localization p.1.primeCompl), I.IsMaximal := by
        exact IsLocalRing.maximal_ideal_unique (Localization p.asIdeal.primeCompl)
      --one way is to show that each prime ideal in Ap is in the form of qAp where q is a prime ideal in A contained in p. And then use "Localization.AtPrime.map_eq_maximalIdeal" to show that it's maximal then unique.
      --another way is to show that Ap is KrullDim 0, then prime is unique
      have PrimeIsMaximal : ∀ P : Ideal (Localization p.1.primeCompl), P ≠ ⊥ ∧ P.IsPrime → P.IsMaximal := by
        intro P hP
        sorry
      unfold ExistsUnique
      set P := Ideal.map (algebraMap A (Localization p.1.primeCompl)) p.1
      use P
      constructor
      · sorry
      · intro y hy
        have yMaximal : y.IsMaximal := by exact PrimeIsMaximal y hy
        have hP : P ≠ ⊥ ∧ P.IsPrime := by
          sorry
        have PMaximal : P.IsMaximal := by exact PrimeIsMaximal P hP
        exact ExistsUnique.unique UniqueMax yMaximal PMaximal
    have TFAE3 : IsIntegrallyClosed (Localization p.1.primeCompl) ∧ ∃! P : Ideal (Localization p.1.primeCompl), P ≠ ⊥ ∧ P.IsPrime := by
      exact ⟨IsIntegralClosedAp, UniquePrime⟩
    have IsDVRAp : IsDiscreteValuationRing (Localization p.1.primeCompl) := by
      apply ((IsDiscreteValuationRing.TFAE _ notField).out 0 3).mpr
      exact TFAE3
    exact IsDVRAp
  · ext a
    constructor
    · intro ha
      sorry
    · intro ha
      have : ∀ p ∈ {p : PrimeSpectrum A  | p.asIdeal.primeHeight = 1}, a ∈ (Localization.mapToFractionRing (FractionRing A) p.1.primeCompl (Localization p.1.primeCompl) p.1.primeCompl_le_nonZeroDivisors).range := by
        intro p hp
        simp only [AlgHom.mem_range, Localization.mapToFractionRing_apply]
        sorry
      simp only [Set.mem_setOf_eq]
      apply Algebra.mem_sInf.mpr
      sorry
  · intro a ha
    --have : IsDedekindDomain A := by sorry
    have : (Ideal.span {a}).IsPrime  := sorry
    have : ∀ p ∈ {p : PrimeSpectrum A | p.asIdeal.primeHeight = 1 ∧ a ∈ p.asIdeal}, IsAssociatedPrime (Ideal.map (algebraMap A (Localization p.1.primeCompl)) p.1) (Localization p.1.primeCompl) := by sorry
    -- show that associated prime ideals of A are finite
    sorry
--#check primesOver_finite

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
    s ⊆ {p : PrimeSpectrum A | p.1.primeHeight = 1} → s.Finite →
    IsDomain (Localization (⨅ p ∈ s, p.1.primeCompl)) ∧
    IsPrincipalIdealRing (Localization (⨅ p ∈ s, p.1.primeCompl))

/-- If a semilocal integral domain which is not a field satisfies that it localized at all
maximal ideals is a PID, then itself is a PID. -/
theorem isPrincipalIdealRing_of_isPrincipalIdealRing_localization
    (A : Type*) [CommRing A] [IsDomain A] [Finite (MaximalSpectrum A)] (hnf : ¬IsField A)
    (hpid : ∀ p : MaximalSpectrum A, IsPrincipalIdealRing (Localization p.1.primeCompl)) :
    IsPrincipalIdealRing A := by
  sorry

instance (priority := 100) IsKrullDomain.heightOneLocalizationIsPID
    (A : Type*) [CommRing A] [IsDomain A] [IsKrullDomain A] : HeightOneLocalizationIsPID A := by
  sorry

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
