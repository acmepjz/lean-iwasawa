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
    s ⊆ {p : PrimeSpectrum A | p.1.primeHeight = 1} → s.Finite →
    IsDomain (Localization (⨅ p ∈ s, p.1.primeCompl)) ∧
    IsPrincipalIdealRing (Localization (⨅ p ∈ s, p.1.primeCompl))

/-- The image of the n-th power of the maximal ideal of the localization at `p` in the fraction field,
intersected with `A`, equals the image of the n-th power of `p` in the fraction field. -/
theorem map_pow_maximal_ideal_eq_map_localization_pow_inf_map_top
    (A : Type*) [CommRing A] [IsDomain A] :
    ∀ p : MaximalSpectrum A , ∀ n : ℕ, n ≥ 1 →
    ((IsLocalRing.maximalIdeal (Localization p.1.primeCompl)) ^ n).map
    (algebraMap (Localization p.1.primeCompl) (FractionRing A))
    ⊓ (⊤ : Ideal A).map (algebraMap A (FractionRing A))
    = (p.1 ^ n).map (algebraMap A (FractionRing A)) := by
    sorry

/-- The image of the n-th power of the maximal ideal of the localization at `p` in the fraction field,
intersected with `A`, equals the image of the n-th power of `p` in the fraction field. -/
theorem map_pow_maximal_ideal_eq_map_localization_pow_inf_map_top'
    (A : Type*) [CommRing A] [IsDomain A] :
    ∀ p : MaximalSpectrum A , ∀ n : ℕ, n ≥ 1 →
    ((IsLocalRing.maximalIdeal (Localization p.1.primeCompl)) ^ n).map
    (Localization.mapToFractionRing (FractionRing A) p.1.primeCompl (Localization p.1.primeCompl)
    (Ideal.primeCompl_le_nonZeroDivisors p.1) )
    ⊓ (⊤ : Ideal A).map (algebraMap A (FractionRing A))
    = (p.1 ^ n).map (algebraMap A (FractionRing A)) := by
    sorry

namespace Module

variable {R : Type*} [CommSemiring R] [Finite (MaximalSpectrum R)]
variable (M : Type*) [AddCommMonoid M] [Module R M]

variable (Mₚ : ∀ _ : MaximalSpectrum R, Type*)
  [∀ P : MaximalSpectrum R, AddCommMonoid (Mₚ P)]
  [∀ P : MaximalSpectrum R, Module R (Mₚ P)]
  (f : ∀ P : MaximalSpectrum R, M →ₗ[R] Mₚ P)
  [∀ P : MaximalSpectrum R, IsLocalizedModule P.1.primeCompl (f P)]

include f in
theorem finite_of_isLocalized_maximal (H : ∀ P : MaximalSpectrum R, Module.Finite R (Mₚ P)) :
    Module.Finite R M := by sorry

variable (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]

include f in
theorem finite_of_isLocalized_maximal' (H : ∀ (P : Ideal R) [P.IsMaximal], Module.Finite R (Mₚ P)) :
    Module.Finite R M := by sorry

end Module

theorem isDedekindDomain_of_isDedekindDomain_localization
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] (hnf : ¬IsField A)
    (hddk : ∀ p : MaximalSpectrum A, IsDedekindDomain (Localization p.1.primeCompl)) :
    IsDedekindDomain A := by
  sorry

theorem IsDedekindDomain.isDedekindDomain_localization_at_maximal
    (A : Type*) [CommRing A] [IsDedekindDomain A] (hnf : ¬IsField A) :
    ∀ p : MaximalSpectrum A, IsDedekindDomain (Localization p.1.primeCompl) ∧
    IsNoetherianRing A := by
  sorry

theorem isPrincipalIdealRing_of_DedekindDomain_semilocal
    (A : Type*) [CommRing A] [IsDedekindDomain A] [Finite (MaximalSpectrum A)] :
    IsPrincipalIdealRing A := by
  sorry

/-- If a semilocal integral domain which is not a field satisfies that it localized at all
maximal ideals is a PID, then itself is a PID. -/
theorem isPrincipalIdealRing_of_isPrincipalIdealRing_localization
    (A : Type*) [CommRing A] [IsDomain A] [Finite (MaximalSpectrum A)] (hnf : ¬IsField A)
    (hpid : ∀ p : MaximalSpectrum A, IsPrincipalIdealRing (Localization p.1.primeCompl)) :
    IsPrincipalIdealRing A := by
  have h1 : IsNoetherianRing A := by
    sorry
  have h2 : IsDedekindDomain A := by
    sorry
  apply isPrincipalIdealRing_of_DedekindDomain_semilocal A

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
