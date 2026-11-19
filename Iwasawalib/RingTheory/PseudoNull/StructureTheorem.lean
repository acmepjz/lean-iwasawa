/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan, Yiming Fu, Shouxin Zhang
-/
module

public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

public import Mathlib.RingTheory.DiscreteValuationRing.Basic

public import Mathlib.Algebra.Module.PID
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.LocalProperties.Semilocal
public import Mathlib.RingTheory.Ideal.UFD
public import Iwasawalib.RingTheory.PseudoNull.CharacteristicIdeal

@[expose] public section

/-!

# Structure theorem of finitely generated torsion module up to pseudo-isomorphism

-/

universe u

theorem PrimeSpectrum.localization_comap_range_eq_of_isDomain_of_height_eq_one
    {R : Type*} (S : Type*) [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]
    (s : Set (PrimeSpectrum R)) (hs : s ⊆ {p : PrimeSpectrum R | p.1.height = 1})
    (hn : s.Nonempty) (hfin : s.Finite) [IsLocalization (⨅ p ∈ s, p.1.primeCompl) S] :
    Set.range (PrimeSpectrum.comap (algebraMap R S)) = s ∪ {⟨⊥, Ideal.isPrime_bot⟩} := by
  set M := ⨅ p ∈ s, p.1.primeCompl
  rw [PrimeSpectrum.localization_comap_range S M]
  ext p
  simp_rw [Set.mem_ofPred_eq, Set.union_singleton, Set.mem_insert_iff, M, Submonoid.coe_iInf,
    ← le_compl_iff_disjoint_left, Set.compl_iInter]
  change _ ⊆ ⋃ p ∈ s, (p.1ᶜᶜ : Set R) ↔ _
  simp_rw [compl_compl]
  rw [← hfin.coe_toFinset, Ideal.subset_union_prime hn.some hn.some fun p _ _ _ ↦ p.2]
  simp_rw [Set.Finite.mem_toFinset, Set.Finite.coe_toFinset]
  refine ⟨fun ⟨q, hq, hle⟩ ↦ ?_, fun h ↦ ?_⟩
  · have : q.1.FiniteHeight := q.1.finiteHeight_iff.2 <| Or.inr <| by
      rw [hs hq]; nofun
    have hle' := hs hq ▸ Ideal.height_mono hle
    rcases eq_or_ne p.1.height 1 with hh | hh
    · have hmem := Ideal.mem_minimalPrimes_of_height_eq hle <| by
        rw [hs hq, hh]
      rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff,
        ← PrimeSpectrum.ext_iff] at hmem
      right; rwa [← hmem]
    replace hh := Order.lt_one_iff.1 (hle'.lt_of_ne hh)
    rw [Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff] at hh
    left; ext1; exact hh
  · rcases h with h | h
    · rw [PrimeSpectrum.ext_iff] at h
      exact ⟨hn.some, hn.some_mem, by simp [h]⟩
    · exact ⟨p, h, le_rfl⟩

-- theorem MaximalSpectrum.localization_comap_range_eq_of_height_eq_one
--     {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
--     (s : Set (PrimeSpectrum R)) (hs : s ⊆ {p : PrimeSpectrum R | p.1.height = 1})
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
    p.1.height = 1 → IsDiscreteValuationRing (Localization p.1.primeCompl)
  biInf_eq_bot (A) : ⨅ p ∈ {p : PrimeSpectrum A | p.1.height = 1},
    Localization.subalgebra (FractionRing A) p.1.primeCompl p.1.primeCompl_le_nonZeroDivisors = ⊥
  finite (a : A) :
    a ≠ 0 → {p : PrimeSpectrum A | p.1.height = 1 ∧ a ∈ p.1}.Finite

instance (priority := 100) IsKrullDomain.isIntegrallyClosed
    (A : Type*) [CommRing A] [IsDomain A] [IsKrullDomain A] : IsIntegrallyClosed A := by
  refine IsIntegrallyClosed.of_localization
    {p : PrimeSpectrum A | p.1.height = 1} (fun p hp ↦ ?_) (IsKrullDomain.biInf_eq_bot A)
  have := IsKrullDomain.isDiscreteValuationRing_localization p hp
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

section NoethKrull

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

/-- In a Noetherian integrally closed domain, the localization at a height one prime is a
discrete valuation ring. -/
private theorem IsIntegrallyClosed.isDiscreteValuationRing_of_height_eq_one
    (p : PrimeSpectrum A) (hp : p.1.height = 1) :
    IsDiscreteValuationRing (Localization p.1.primeCompl) := by
  have hpne : p.asIdeal ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hp
  have hdom : IsDomain (Localization p.asIdeal.primeCompl) :=
    IsLocalization.isDomain_localization p.asIdeal.primeCompl_le_nonZeroDivisors
  have hic : IsIntegrallyClosed (Localization p.asIdeal.primeCompl) :=
    isIntegrallyClosed_of_isLocalization _ p.asIdeal.primeCompl
      p.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨a, hamem, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
  have hmaxne : IsLocalRing.maximalIdeal (Localization p.asIdeal.primeCompl) ≠ ⊥ := by
    intro h
    refine ha0 (IsLocalization.injective (M := p.asIdeal.primeCompl)
      (Localization p.asIdeal.primeCompl) p.asIdeal.primeCompl_le_nonZeroDivisors ?_)
    have : algebraMap A (Localization p.asIdeal.primeCompl) a ∈
        IsLocalRing.maximalIdeal (Localization p.asIdeal.primeCompl) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p.asIdeal a).2 hamem
    rw [h, Ideal.mem_bot] at this
    rw [this, map_zero]
  have hnf : ¬ IsField (Localization p.asIdeal.primeCompl) := fun h ↦
    hmaxne (IsLocalRing.isField_iff_maximalIdeal_eq.1 h)
  suffices h : ∃! P : Ideal (Localization p.asIdeal.primeCompl), P ≠ ⊥ ∧ P.IsPrime by
    have htfae := (IsDiscreteValuationRing.TFAE (Localization p.asIdeal.primeCompl) hnf).out 4 1
    exact htfae.1 ⟨hic, h⟩
  refine ⟨IsLocalRing.maximalIdeal (Localization p.asIdeal.primeCompl),
    ⟨hmaxne, inferInstance⟩, ?_⟩
  rintro Q ⟨hQ0, hQp⟩
  have hd := (IsLocalization.isPrime_iff_isPrime_disjoint p.asIdeal.primeCompl
    (Localization p.asIdeal.primeCompl) Q).1 hQp
  have hqp : (Q.under A).IsPrime := hd.1
  have hqle : Q.under A ≤ p.asIdeal := fun x hx ↦ by
    by_contra hxp
    exact Set.disjoint_left.1 hd.2 hxp hx
  have hqne : Q.under A ≠ ⊥ := by
    intro h
    refine hQ0 ?_
    rw [← IsLocalization.map_under p.asIdeal.primeCompl (Localization p.asIdeal.primeCompl) Q, h,
      Ideal.map_bot]
  have hfh : p.asIdeal.FiniteHeight := p.asIdeal.finiteHeight_iff.2 <| Or.inr <| by
    rw [hp]; nofun
  have hqeq : Q.under A = p.asIdeal := by
    by_contra hne
    have hlt : Q.under A < p.asIdeal := lt_of_le_of_ne hqle hne
    have hh := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    rw [hp] at hh
    exact hqne (Ideal.height_eq_zero_iff_eq_bot.1 (Order.lt_one_iff.1 hh))
  rw [← IsLocalization.map_under p.asIdeal.primeCompl (Localization p.asIdeal.primeCompl) Q,
    hqeq, Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]

omit [IsIntegrallyClosed A] in
/-- In a Noetherian domain, only finitely many height one primes contain a given nonzero
element. -/
private theorem IsIntegrallyClosed.finite_heightOne_mem {a : A} (ha : a ≠ 0) :
    {p : PrimeSpectrum A | p.1.height = 1 ∧ a ∈ p.1}.Finite := by
  refine Set.Finite.of_finite_image ?_ (fun _ _ _ _ h ↦ PrimeSpectrum.ext h)
  refine Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})) ?_
  rintro _ ⟨p, ⟨h1, hmem⟩, rfl⟩
  have hfh : p.asIdeal.FiniteHeight := p.asIdeal.finiteHeight_iff.2 <| Or.inr <| by
    rw [h1]; nofun
  refine Ideal.mem_minimalPrimes_of_height_eq ((Ideal.span_singleton_le_iff_mem _).2 hmem) ?_
  rw [h1]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero ha)

/-- In a Noetherian integrally closed domain, the intersection of the localizations at all
height one primes is the ring. -/
private theorem IsIntegrallyClosed.biInf_subalgebra_eq_bot :
    ⨅ p ∈ {p : PrimeSpectrum A | p.1.height = 1},
      Localization.subalgebra (FractionRing A) p.1.primeCompl
        p.1.primeCompl_le_nonZeroDivisors = ⊥ := by
  classical
  refine bot_unique fun x hx ↦ ?_
  have hx' : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 →
      x ∈ Localization.subalgebra (FractionRing A) p.asIdeal.primeCompl
        p.asIdeal.primeCompl_le_nonZeroDivisors :=
    fun p hp ↦ Algebra.mem_iInf.1 (Algebra.mem_iInf.1 hx p) hp
  set I : Ideal A :=
    { carrier := {c : A | ∃ y : A, algebraMap A (FractionRing A) c * x =
        algebraMap A (FractionRing A) y}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro a b ⟨u, hu⟩ ⟨v, hv⟩
        exact ⟨u + v, by rw [map_add, add_mul, hu, hv, map_add]⟩
      smul_mem' := by
        rintro c a ⟨u, hu⟩
        exact ⟨c * u, by rw [smul_eq_mul, map_mul, mul_assoc, hu, map_mul]⟩ } with hIdef
  have hmemI : ∀ c : A, c ∈ I ↔ ∃ y : A, algebraMap A (FractionRing A) c * x =
      algebraMap A (FractionRing A) y := fun c ↦ Iff.rfl
  suffices h1 : (1 : A) ∈ I by
    obtain ⟨y, hy⟩ := (hmemI 1).1 h1
    rw [map_one, one_mul] at hy
    exact Algebra.mem_bot.2 ⟨y, hy.symm⟩
  by_contra h1
  have hItop : I ≠ ⊤ := fun h ↦ h1 (h ▸ Submodule.mem_top)
  -- `I` is nonzero
  obtain ⟨a₀, b₀, hb₀, hab₀⟩ :=
    IsFractionRing.div_surjective (A := A) (K := FractionRing A) x
  have hb₀0 : b₀ ≠ 0 := nonZeroDivisors.ne_zero hb₀
  have hb₀K : algebraMap A (FractionRing A) b₀ ≠ 0 := by
    simpa using (IsFractionRing.injective A (FractionRing A)).ne hb₀0
  have hb₀I : b₀ ∈ I := ⟨a₀, by rw [← hab₀, mul_div_cancel₀ _ hb₀K]⟩
  -- pick an associated prime of `A ⧸ I`
  have hnt : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hItop
  obtain ⟨P, hPass⟩ := associatedPrimes.nonempty A (A ⧸ I)
  obtain ⟨hPp, z, hPz⟩ := isAssociatedPrime_iff.1 hPass
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hPmem : ∀ c : A, c ∈ P ↔ c * y ∈ I := by
    intro c
    have hsmul : c • (Ideal.Quotient.mk I) y = (Ideal.Quotient.mk I) (c * y) := rfl
    rw [hPz, Submodule.mem_colon_singleton, hsmul, Submodule.mem_bot,
      Ideal.Quotient.eq_zero_iff_mem]
  have hIP : I ≤ P := fun c hc ↦ (hPmem c).2 (I.mul_mem_right y hc)
  have hyI : y ∉ I := by
    intro hy
    exact hPp.ne_top (Ideal.eq_top_iff_one P |>.2 ((hPmem 1).2 (by rwa [one_mul])))
  have hPbot : P ≠ ⊥ := fun h ↦ hb₀0 (by
    have := hIP hb₀I
    rwa [h, Ideal.mem_bot] at this)
  set u : FractionRing A := algebraMap A (FractionRing A) y * x with hudef
  have hu : ∀ c ∈ P, ∃ w : A, algebraMap A (FractionRing A) w =
      algebraMap A (FractionRing A) c * u := by
    intro c hc
    obtain ⟨w, hw⟩ := (hmemI _).1 ((hPmem c).1 hc)
    exact ⟨w, by rw [← hw, hudef, map_mul]; ring⟩
  by_cases hcase : ∀ c ∈ P, ∀ w : A,
      algebraMap A (FractionRing A) w = algebraMap A (FractionRing A) c * u → w ∈ P
  · -- `u` stabilizes the finitely generated faithful module `P`, hence is integral
    set N : Submodule A (FractionRing A) :=
      Submodule.map (Algebra.linearMap A (FractionRing A)) P with hNdef
    have hN : N ≠ ⊥ := by
      obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPbot
      rw [Submodule.ne_bot_iff]
      refine ⟨algebraMap A (FractionRing A) c, ⟨c, hc, rfl⟩, ?_⟩
      simpa using (IsFractionRing.injective A (FractionRing A)).ne hc0
    have hN' : N.FG := Submodule.FG.map _ (IsNoetherian.noetherian P)
    have hstab : ∀ n ∈ N, u • n ∈ N := by
      rintro _ ⟨c, hc, rfl⟩
      obtain ⟨w, hw⟩ := hu c hc
      refine ⟨w, hcase c hc w hw, ?_⟩
      simp only [Algebra.linearMap_apply]
      rw [hw, smul_eq_mul, mul_comm]
    have hint : IsIntegral A u := isIntegral_of_smul_mem_submodule N hN hN' u hstab
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    exact hyI ⟨v, by rw [hv, hudef]⟩
  · push Not at hcase
    obtain ⟨c₀, hc₀P, e, hce, heP⟩ := hcase
    have hc₀0 : c₀ ≠ 0 := by
      rintro rfl
      refine heP ?_
      have : algebraMap A (FractionRing A) e = 0 := by rw [hce, map_zero, zero_mul]
      rw [show (0 : FractionRing A) = algebraMap A (FractionRing A) 0 from (map_zero _).symm] at this
      rw [IsFractionRing.injective A (FractionRing A) this]
      exact P.zero_mem
    have hmin : P ∈ (Ideal.span {c₀}).minimalPrimes := by
      refine ⟨⟨hPp, (Ideal.span_singleton_le_iff_mem _).2 hc₀P⟩, ?_⟩
      rintro q ⟨hq, hqle⟩ hqP
      intro t ht
      obtain ⟨w, hw⟩ := hu t ht
      have hkey : e * t = c₀ * w := by
        refine IsFractionRing.injective A (FractionRing A) ?_
        rw [map_mul, map_mul, hce, hw]
        ring
      have : e * t ∈ q := hkey ▸ hqle (Ideal.mem_span_singleton.2 ⟨w, rfl⟩)
      exact (hq.mem_or_mem this).resolve_left (fun h ↦ heP (hqP h))
    have hheight : P.height = 1 := by
      refine le_antisymm
        (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {c₀}) P hmin) ?_
      rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      exact hPbot
    obtain ⟨d, t, ht, hxe⟩ := hx' ⟨P, hPp⟩ hheight
    have ht0 : algebraMap A (FractionRing A) t ≠ 0 := by
      simpa using (IsFractionRing.injective A (FractionRing A)).ne
        (nonZeroDivisors.ne_zero (P.primeCompl_le_nonZeroDivisors ht))
    rw [IsFractionRing.mk'_eq_div] at hxe
    exact ht (hIP ⟨d, by rw [hxe, mul_div_cancel₀ _ ht0]⟩)

end NoethKrull

instance (priority := 100) IsIntegrallyClosed.isKrullDomain_of_isNoetherianRing
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] :
    IsKrullDomain A := by
  refine ⟨fun p hp ↦ ?_, ?_, fun a ha ↦ ?_⟩
  · exact IsIntegrallyClosed.isDiscreteValuationRing_of_height_eq_one p hp
  · exact IsIntegrallyClosed.biInf_subalgebra_eq_bot
  · exact IsIntegrallyClosed.finite_heightOne_mem ha

/-- A Noetherian ring is a Krull domain if and only if it is an integrally closed domain. -/
theorem isKrullDomain_iff_isIntegrallyClosed
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] :
    IsKrullDomain A ↔ IsIntegrallyClosed A :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩


section UFDKrull

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

/-- In a UFD, the ideal generated by a prime element has height one. -/
private theorem Ideal.height_span_singleton_eq_one_of_prime' {q : A} (hq : Prime q) :
    (Ideal.span {q}).height = 1 := by
  have hp : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).2 hq
  refine le_antisymm ?_ (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hq.ne_zero))
  have hkey : ∀ y : PrimeSpectrum A, y < (⟨Ideal.span {q}, hp⟩ : PrimeSpectrum A) →
      y.asIdeal = ⊥ := by
    intro y hy
    have hle : y.asIdeal ≤ Ideal.span {q} := hy.le
    have hqny : q ∉ y.asIdeal := fun hmem ↦ hy.ne <| PrimeSpectrum.ext <|
      le_antisymm hle ((Ideal.span_singleton_le_iff_mem _).2 hmem)
    have main : ∀ (n : ℕ) (a : A), a ∈ y.asIdeal → q ^ n ∣ a := by
      intro n
      induction n with
      | zero => intro a _; simp
      | succ n ih =>
        intro a ha
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 (hle ha)
        have hb : b ∈ y.asIdeal := (y.isPrime.mem_or_mem ha).resolve_left hqny
        obtain ⟨c, rfl⟩ := ih b hb
        exact ⟨c, by ring⟩
    refine (Submodule.eq_bot_iff _).2 fun a ha ↦ ?_
    by_contra ha0
    exact (FiniteMultiplicity.not_iff_forall.2 fun n ↦ main n a ha)
      (FiniteMultiplicity.of_prime_left hq ha0)
  have := PrimeSpectrum.height_eq_orderHeight (⟨Ideal.span {q}, hp⟩ : PrimeSpectrum A)
  simp only at this
  rw [this, show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Order.height_le_coe_iff]
  intro y hy
  have hyb : y = ⊥ := PrimeSpectrum.ext (hkey y hy)
  simp [hyb]

/-- In a UFD, only finitely many height one primes contain a given nonzero element. -/
private theorem UniqueFactorizationMonoid.finite_heightOne_mem {a : A} (ha : a ≠ 0) :
    {p : PrimeSpectrum A | p.1.height = 1 ∧ a ∈ p.1}.Finite := by
  refine Set.Finite.of_finite_image ?_ (fun _ _ _ _ h ↦ PrimeSpectrum.ext h)
  refine Set.Finite.subset (Set.Finite.image (fun q : A ↦ Ideal.span {q})
    (UniqueFactorizationMonoid.factors a).finite_toSet) ?_
  rintro _ ⟨p, ⟨h1, hmem⟩, rfl⟩
  obtain ⟨x, hxmem, hxp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot p.isPrime
    (Ideal.ne_bot_of_height_eq_one h1)
  have hpe : p.asIdeal = Ideal.span {x} :=
    Ideal.eq_span_singleton_of_height_eq_one h1 hxmem hxp
  have hdvd : x ∣ a := Ideal.mem_span_singleton.1 (hpe ▸ hmem)
  obtain ⟨q, hq, hassoc⟩ :=
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd ha hxp.irreducible hdvd
  exact ⟨q, hq, by rw [hpe, Ideal.span_singleton_eq_span_singleton.2 hassoc]⟩

/-- In a UFD, the localization at a height one prime is a discrete valuation ring. -/
private theorem UniqueFactorizationMonoid.isDiscreteValuationRing_of_height_eq_one
    (p : PrimeSpectrum A) (hp : p.1.height = 1) :
    IsDiscreteValuationRing (Localization p.1.primeCompl) := by
  obtain ⟨x, hxmem, hxp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot p.isPrime
    (Ideal.ne_bot_of_height_eq_one hp)
  have hpe : p.asIdeal = Ideal.span {x} :=
    Ideal.eq_span_singleton_of_height_eq_one hp hxmem hxp
  have hdom : IsDomain (Localization p.asIdeal.primeCompl) :=
    IsLocalization.isDomain_localization p.asIdeal.primeCompl_le_nonZeroDivisors
  set ϖ : Localization p.asIdeal.primeCompl :=
    algebraMap A (Localization p.asIdeal.primeCompl) x with hϖdef
  have hmapspan : Ideal.map (algebraMap A (Localization p.asIdeal.primeCompl)) p.asIdeal
      = Ideal.span {ϖ} := by
    have hc := congrArg (Ideal.map (algebraMap A (Localization p.asIdeal.primeCompl))) hpe
    rw [hc, Ideal.map_span]
    simp [hϖdef]
  have hmax : IsLocalRing.maximalIdeal (Localization p.asIdeal.primeCompl) = Ideal.span {ϖ} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal), hmapspan]
  have hϖ0 : ϖ ≠ 0 := by
    rw [hϖdef, Ne, ← (algebraMap A (Localization p.asIdeal.primeCompl)).map_zero]
    exact fun h ↦ hxp.ne_zero
      (IsLocalization.injective _ p.asIdeal.primeCompl_le_nonZeroDivisors h)
  have hirr : Irreducible ϖ :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ hϖ0 hmax
  have key : ∀ u : Localization p.asIdeal.primeCompl, Irreducible u → Associated ϖ u := by
    intro u hu
    have hmemu : u ∈ IsLocalRing.maximalIdeal (Localization p.asIdeal.primeCompl) :=
      (IsLocalRing.mem_maximalIdeal u).2 hu.not_isUnit
    rw [hmax, Ideal.mem_span_singleton] at hmemu
    obtain ⟨c, hc⟩ := hmemu
    have hcu : IsUnit c := (hu.isUnit_or_isUnit hc).resolve_left hirr.not_isUnit
    exact ⟨hcu.unit, by rw [hc, hcu.unit_spec]⟩
  exact IsDiscreteValuationRing.of_ufd_of_unique_irreducible ⟨ϖ, hirr⟩
    fun _ _ hs ht ↦ (key _ hs).symm.trans (key _ ht)

/-- In a UFD, the intersection of the localizations at all height one primes is the ring. -/
private theorem UniqueFactorizationMonoid.biInf_subalgebra_eq_bot :
    ⨅ p ∈ {p : PrimeSpectrum A | p.1.height = 1},
      Localization.subalgebra (FractionRing A) p.1.primeCompl
        p.1.primeCompl_le_nonZeroDivisors = ⊥ := by
  classical
  have main : ∀ b : A, b ≠ 0 → ∀ a : A,
      (∀ p : PrimeSpectrum A, p.asIdeal.height = 1 →
        algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b ∈
          Localization.subalgebra (FractionRing A) p.asIdeal.primeCompl
            p.asIdeal.primeCompl_le_nonZeroDivisors) →
      ∃ y : A, algebraMap A (FractionRing A) y =
        algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b := by
    intro b
    induction b using WfDvdMonoid.induction_on_irreducible with
    | zero => intro h; exact absurd rfl h
    | unit u hu =>
      intro _ a _
      obtain ⟨v, rfl⟩ := hu
      have hv0 : algebraMap A (FractionRing A) (v : A) ≠ 0 := by
        simp
      refine ⟨a * ↑v⁻¹, ?_⟩
      rw [eq_div_iff hv0, ← map_mul]
      congr 1
      simp
    | mul c i hc hi ih =>
      intro hb a hmem
      have hip : Prime i := UniqueFactorizationMonoid.irreducible_iff_prime.1 hi
      have hprime : (Ideal.span {i}).IsPrime := (Ideal.span_singleton_prime hip.ne_zero).2 hip
      have hheight : (Ideal.span ({i} : Set A)).height = 1 :=
        Ideal.height_span_singleton_eq_one_of_prime' hip
      obtain ⟨d, t, ht, hxe⟩ := hmem ⟨Ideal.span {i}, hprime⟩ hheight
      have hti : ¬ i ∣ t := fun h ↦ ht (Ideal.mem_span_singleton.2 h)
      have ht0 : t ≠ 0 := by rintro rfl; exact hti (dvd_zero i)
      have hi0 : algebraMap A (FractionRing A) i ≠ 0 := by
        simpa using (IsFractionRing.injective A (FractionRing A)).ne hip.ne_zero
      have ht0' : algebraMap A (FractionRing A) t ≠ 0 := by
        simpa using (IsFractionRing.injective A (FractionRing A)).ne ht0
      have hb0' : algebraMap A (FractionRing A) (i * c) ≠ 0 := by
        simpa using (IsFractionRing.injective A (FractionRing A)).ne hb
      rw [IsFractionRing.mk'_eq_div, div_eq_div_iff hb0' ht0', ← map_mul, ← map_mul] at hxe
      have hxe' : a * t = d * (i * c) := IsFractionRing.injective A (FractionRing A) hxe
      have hia : i ∣ a := by
        rcases hip.2.2 a t ⟨d * c, by rw [hxe']; ring⟩ with h | h
        · exact h
        · exact absurd h hti
      obtain ⟨a', rfl⟩ := hia
      have heq : algebraMap A (FractionRing A) a' / algebraMap A (FractionRing A) c =
          algebraMap A (FractionRing A) (i * a') / algebraMap A (FractionRing A) (i * c) := by
        rw [map_mul, map_mul, mul_div_mul_left _ _ hi0]
      obtain ⟨y, hy⟩ := ih hc a' (fun p hp ↦ heq ▸ hmem p hp)
      exact ⟨y, hy.trans heq⟩
  refine bot_unique fun x hx ↦ ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) (K := FractionRing A) x
  have hx' : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 →
      algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b ∈
        Localization.subalgebra (FractionRing A) p.asIdeal.primeCompl
          p.asIdeal.primeCompl_le_nonZeroDivisors :=
    fun p hp ↦ Algebra.mem_iInf.1 (Algebra.mem_iInf.1 hx p) hp
  obtain ⟨y, hy⟩ := main b (nonZeroDivisors.ne_zero hb) a hx'
  exact Algebra.mem_bot.2 ⟨y, hy⟩

end UFDKrull

instance (priority := 100) UniqueFactorizationMonoid.isKrullDomain
    (A : Type*) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] : IsKrullDomain A := by
  refine ⟨fun p hp ↦ ?_, ?_, fun a ha ↦ ?_⟩
  · exact UniqueFactorizationMonoid.isDiscreteValuationRing_of_height_eq_one p hp
  · exact UniqueFactorizationMonoid.biInf_subalgebra_eq_bot
  · exact UniqueFactorizationMonoid.finite_heightOne_mem ha

/-!

## Height one localization is PID

-/

/-- A typeclass asserting that for any finitely many height one primes `p₁, ..., pₙ` of `A`,
let `S = A \ ⋃ i, pᵢ`, then `S⁻¹A` is a PID. -/
class HeightOneLocalizationIsPID (A : Type*) [CommRing A] : Prop where
  isPrincipalIdealRing_localization (s : Set (PrimeSpectrum A)) :
    s ⊆ {p : PrimeSpectrum A | p.1.height = 1} → s.Nonempty → s.Finite →
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
  have hrange := PrimeSpectrum.localization_comap_range_eq_of_isDomain_of_height_eq_one
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
        {p : PrimeSpectrum A | p.1.height = 1}, p.1.primeCompl) f) := by
  set s := (Module.support A M ∪ Module.support A N) ∩ {p : PrimeSpectrum A | p.1.height = 1}
  have hs : s.Finite := by simpa only [← Set.union_inter_distrib_right] using
    hMT.finite_height_one_support.union hNT.finite_height_one_support
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

/-- If `X` is a module of finite length over a local ring `R`, then some power of the maximal
ideal of `R` annihilates `X`. -/
private theorem exists_pow_maximalIdeal_smul_eq_bot {R X : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup X] [Module R X] (h : IsFiniteLength R X) :
    ∃ n : ℕ, (IsLocalRing.maximalIdeal R ^ n) • (⊤ : Submodule R X) = ⊥ := by
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  set m := IsLocalRing.maximalIdeal R with hm
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := R) (M := X)
    ⟨fun n => OrderDual.toDual (m ^ n • (⊤ : Submodule R X)),
      fun a b hab => Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)⟩
  refine ⟨n, ?_⟩
  have h1 : m ^ n • (⊤ : Submodule R X) = m • (m ^ n • (⊤ : Submodule R X)) := by
    have := hn (n + 1) (by omega)
    change m ^ n • (⊤ : Submodule R X) = m ^ (n + 1) • (⊤ : Submodule R X) at this
    conv_lhs => rw [this]
    rw [pow_succ', mul_smul]
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m _ (IsNoetherian.noetherian _) h1.le
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])

/-- Let `A` be a Noetherian ring, `M` a finitely generated torsion `A`-module and `q` a prime
ideal of height `≤ 1`. Then some power of `q` annihilates `M_q`. -/
private theorem exists_pow_smul_localizedModule_eq_zero {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] (hMT : Module.IsTorsion A M)
    (q : PrimeSpectrum A) (hq : q.1.height ≤ 1) :
    ∃ n : ℕ, ∀ c ∈ q.1 ^ n, ∀ x : LocalizedModule q.1.primeCompl M, c • x = 0 := by
  obtain ⟨n, hn⟩ := exists_pow_maximalIdeal_smul_eq_bot
    (hMT.isFiniteLength_localizedModule_of_height_le_one q hq)
  refine ⟨n, fun c hc x ↦ ?_⟩
  have h1 : (algebraMap A (Localization q.1.primeCompl)) c ∈
      IsLocalRing.maximalIdeal (Localization q.1.primeCompl) ^ n := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hc
  have : (algebraMap A (Localization q.1.primeCompl)) c • x = 0 := by
    have hmem : (algebraMap A (Localization q.1.primeCompl)) c • x ∈
        (IsLocalRing.maximalIdeal (Localization q.1.primeCompl) ^ n) •
          (⊤ : Submodule (Localization q.1.primeCompl) (LocalizedModule q.1.primeCompl M)) :=
      Submodule.smul_mem_smul h1 Submodule.mem_top
    rw [hn] at hmem
    simpa using hmem
  rwa [algebraMap_smul] at this

/-- Any `A`-linear map `S⁻¹M → S⁻¹N` is, up to multiplication by an element of `S`, the
localization of an `A`-linear map `M → N`, provided that `M` is finitely generated over the
Noetherian ring `A`. -/
private theorem exists_lift_localizedModule_map {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {N : Type*} [AddCommGroup N] [Module A N] (S : Submonoid A)
    (g : LocalizedModule S M →ₗ[A] LocalizedModule S N) :
    ∃ (h : M →ₗ[A] N) (s : S), ∀ x, LocalizedModule.map S h x = (s : A) • g x := by
  have := Module.finitePresentation_of_finite A M
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S
    (LocalizedModule.mkLinearMap S N) (g ∘ₗ LocalizedModule.mkLinearMap S M)
  refine ⟨h, s, fun x ↦ ?_⟩
  have key : ((LocalizedModule.map S h).restrictScalars A) = (s : A) • g := by
    refine IsLocalizedModule.ext S (LocalizedModule.mkLinearMap S M)
      (fun x ↦ IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S N) x) ?_
    ext m
    have := LinearMap.congr_fun hs m
    simpa [Submonoid.smul_def] using this
  exact LinearMap.congr_fun key x

/-- If `M_q ≅ N_q` for a prime ideal `q`, then there is an `A`-linear map `M → N` whose
localization at `q` is bijective. -/
private theorem exists_bijective_localizedModule_map_of_linearEquiv
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {N : Type*} [AddCommGroup N] [Module A N]
    (q : PrimeSpectrum A)
    (e : (LocalizedModule q.1.primeCompl M) ≃ₗ[Localization q.1.primeCompl]
        (LocalizedModule q.1.primeCompl N)) :
    ∃ h : M →ₗ[A] N, Function.Bijective (LocalizedModule.map q.1.primeCompl h) := by
  obtain ⟨h, u, hu⟩ := exists_lift_localizedModule_map q.1.primeCompl
    (e.toLinearMap.restrictScalars A)
  refine ⟨h, ?_⟩
  have h1 : (LocalizedModule.map q.1.primeCompl h : LocalizedModule q.1.primeCompl M → _) =
      (fun x ↦ (u : A) • x) ∘ e := by
    funext x; exact hu x
  rw [h1]
  refine Function.Bijective.comp ?_ e.bijective
  have := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap q.1.primeCompl N) u
  rw [Module.End.isUnit_iff] at this
  exact this

/-- Let `A` be a Noetherian ring, `M` and `N` be finitely generated torsion `A`-modules such
that `M_p ≅ N_p` for all height one primes `p` of `A`. Then there exists a pseudo-isomorphism
`M → N`. -/
private theorem exists_isPseudoIsomorphism_of_forall_nonempty_linearEquiv
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] (hMT : Module.IsTorsion A M)
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] (hNT : Module.IsTorsion A N)
    (H : ∀ p : PrimeSpectrum A, p.1.height = 1 →
      Nonempty ((LocalizedModule p.1.primeCompl M) ≃ₗ[Localization p.1.primeCompl]
        (LocalizedModule p.1.primeCompl N))) :
    ∃ f : M →ₗ[A] N, f.IsPseudoIsomorphism := by
  classical
  have hfin : ((Module.support A M ∪ Module.support A N) ∩
      {p : PrimeSpectrum A | p.1.height = 1}).Finite := by
    simpa only [← Set.union_inter_distrib_right] using
      hMT.finite_height_one_support.union hNT.finite_height_one_support
  set s : Finset (PrimeSpectrum A) := hfin.toFinset with hsdef
  have hsmem : ∀ q : PrimeSpectrum A, q ∈ s →
      (q ∈ Module.support A M ∪ Module.support A N) ∧ q.1.height = 1 := by
    intro q hq
    simpa [hsdef] using hq
  have hA : ∀ q : PrimeSpectrum A, ∃ h : M →ₗ[A] N,
      q ∈ s → Function.Bijective (LocalizedModule.map q.1.primeCompl h) := by
    intro q
    by_cases hq : q ∈ s
    · obtain ⟨h, hb⟩ :=
        exists_bijective_localizedModule_map_of_linearEquiv q (H q (hsmem q hq).2).some
      exact ⟨h, fun _ ↦ hb⟩
    · exact ⟨0, fun h ↦ absurd h hq⟩
  choose hh hhb using hA
  have hB : ∀ q : PrimeSpectrum A, ∃ n : ℕ, q ∈ s →
      ∀ c ∈ q.1 ^ n, ∀ x : LocalizedModule q.1.primeCompl N, c • x = 0 := by
    intro q
    by_cases hq : q ∈ s
    · obtain ⟨n, hn⟩ := exists_pow_smul_localizedModule_eq_zero hNT q (le_of_eq (hsmem q hq).2)
      exact ⟨n, fun _ ↦ hn⟩
    · exact ⟨0, fun h ↦ absurd h hq⟩
  choose nn hnn using hB
  have hC : ∀ q : PrimeSpectrum A, ∃ c : A, q ∈ s →
      (c ∈ ∏ q' ∈ s.erase q, q'.1 ^ (nn q' + 1) ∧ c ∉ q.1) := by
    intro q
    by_cases hq : q ∈ s
    · have hnle : ¬ ((∏ q' ∈ s.erase q, q'.1 ^ (nn q' + 1)) ≤ q.1) := by
        intro hle
        obtain ⟨q', hq', hle'⟩ := (Ideal.IsPrime.prod_le q.2).1 hle
        rw [Ideal.IsPrime.pow_le_iff (Nat.succ_ne_zero _)] at hle'
        refine (Finset.mem_erase.1 hq').1 ?_
        have h1 : q'.1.height = 1 := (hsmem q' (Finset.mem_of_mem_erase hq')).2
        have h2 : q.1.height = 1 := (hsmem q hq).2
        have : q.1.FiniteHeight := q.1.finiteHeight_iff.2 (Or.inr (by rw [h2]; nofun))
        rcases eq_or_lt_of_le hle' with h | h
        · exact PrimeSpectrum.ext h
        · exact absurd (Ideal.height_strict_mono_of_isPrime_of_isPrime h) (by rw [h1, h2]; simp)
      obtain ⟨c, hc1, hc2⟩ := SetLike.not_le_iff_exists.1 hnle
      exact ⟨c, fun _ ↦ ⟨hc1, hc2⟩⟩
    · exact ⟨0, fun h ↦ absurd h hq⟩
  choose cc hcc using hC
  refine ⟨∑ q ∈ s, cc q • hh q, ?_⟩
  rw [LinearMap.isPseudoIsomorphism_iff_height_le_one_imp_bijective]
  intro p hp
  by_cases hps : p ∈ s
  · have heval : ∀ x : LocalizedModule p.1.primeCompl M,
        LocalizedModule.map p.1.primeCompl (∑ q ∈ s, cc q • hh q) x =
          cc p • LocalizedModule.map p.1.primeCompl (hh p) x := by
      intro x
      rw [map_sum]
      simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Finset.sum_eq_single p (fun q hq hqp ↦ ?_) (fun h ↦ absurd hps h)
      refine (hnn p hps) (cc q) ?_ _
      have : (∏ q' ∈ (s.erase q), q'.1 ^ (nn q' + 1)) ≤ p.1 ^ (nn p + 1) :=
        le_trans Ideal.prod_le_inf (Finset.inf_le (Finset.mem_erase.2 ⟨Ne.symm hqp, hps⟩))
      exact Ideal.pow_le_pow_right (Nat.le_succ _) (this (hcc q hq).1)
    have hbij : Function.Bijective (fun x : LocalizedModule p.1.primeCompl M ↦
        cc p • LocalizedModule.map p.1.primeCompl (hh p) x) := by
      refine Function.Bijective.comp ?_ (hhb p hps)
      have := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap p.1.primeCompl N)
        (⟨cc p, (hcc p hps).2⟩ : p.1.primeCompl)
      rw [Module.End.isUnit_iff] at this
      exact this
    have heq : (LocalizedModule.map p.1.primeCompl (∑ q ∈ s, cc q • hh q) :
        LocalizedModule p.1.primeCompl M → LocalizedModule p.1.primeCompl N) =
        fun x ↦ cc p • LocalizedModule.map p.1.primeCompl (hh p) x := funext heval
    rw [heq]
    exact hbij
  · have hpM : p ∉ Module.support A M := fun h ↦ hps (by
      simp [hsdef, Set.mem_inter_iff, hp.antisymm (hMT.one_le_height_of_mem_support p h), h])
    have hpN : p ∉ Module.support A N := fun h ↦ hps (by
      simp [hsdef, Set.mem_inter_iff, hp.antisymm (hNT.one_le_height_of_mem_support p h), h])
    rw [Module.notMem_support_iff] at hpM hpN
    exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- Two finitely generated torsion modules over a Noetherian ring are pseudo-isomorphic if and
only if their localizations at all height one primes are isomorphic. -/
private theorem isPseudoIsomorphic_iff_aux {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] (hMT : Module.IsTorsion A M)
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] (hNT : Module.IsTorsion A N) :
    M ∼ₚᵢₛ[A] N ↔ ∀ p : PrimeSpectrum A, p.1.height = 1 →
      Nonempty ((LocalizedModule p.1.primeCompl M) ≃ₗ[Localization p.1.primeCompl]
        (LocalizedModule p.1.primeCompl N)) := by
  refine ⟨fun ⟨f, hf⟩ p hp ↦ ⟨LinearEquiv.ofBijective _
    (hf.bijective_of_height_le_one hp.le)⟩, fun H ↦ ⟨?_⟩⟩
  exact exists_isPseudoIsomorphism_of_forall_nonempty_linearEquiv hMT hNT H

/-- The localization of `A` at the complement of a height one prime is a PID domain. -/
private theorem heightOne_localization_isPID {A : Type*} [CommRing A]
    [HeightOneLocalizationIsPID A] (q : PrimeSpectrum A) (hq : q.1.height = 1) :
    IsDomain (Localization q.1.primeCompl) ∧
      IsPrincipalIdealRing (Localization q.1.primeCompl) := by
  have h := HeightOneLocalizationIsPID.isPrincipalIdealRing_localization (A := A) {q}
    (by simpa using hq) ⟨q, rfl⟩ (Set.finite_singleton q)
  have heq : (⨅ p ∈ ({q} : Set (PrimeSpectrum A)), p.1.primeCompl) = q.1.primeCompl := by simp
  rw [heq] at h
  exact h

/-- A height one prime is not contained in the kernel of the localization map at itself. -/
private theorem exists_mem_map_ne_zero {A : Type*} [CommRing A] (q : PrimeSpectrum A)
    (hq : q.1.height = 1) : ∃ t ∈ q.1, algebraMap A (Localization q.1.primeCompl) t ≠ 0 := by
  by_contra! h
  have hmin : q.1 ∈ minimalPrimes A := by
    refine ⟨⟨q.2, bot_le⟩, ?_⟩
    rintro p ⟨hp, -⟩ hle
    intro t ht
    have := h t ht
    rw [IsLocalization.map_eq_zero_iff q.1.primeCompl] at this
    obtain ⟨v, hv⟩ := this
    have hvp : (v : A) ∉ p := fun hc ↦ v.2 (hle hc)
    exact (hp.mem_or_mem (by simpa using hv ▸ p.zero_mem : (v : A) * t ∈ p)).resolve_left hvp
  rw [← Ideal.height_eq_zero_iff] at hmin
  rw [hmin] at hq
  exact absurd hq (by simp)

/-- The localization of a finitely generated torsion module at a height one prime is a torsion
module over the localized ring. -/
private theorem isTorsion_localizedModule {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hMT : Module.IsTorsion A M) (q : PrimeSpectrum A) (hq : q.1.height = 1)
    [IsDomain (Localization q.1.primeCompl)] :
    Module.IsTorsion (Localization q.1.primeCompl) (LocalizedModule q.1.primeCompl M) := by
  obtain ⟨t, htq, ht0⟩ := exists_mem_map_ne_zero q hq
  obtain ⟨n, hn⟩ := exists_pow_smul_localizedModule_eq_zero hMT q hq.le
  intro x
  refine ⟨⟨(algebraMap A (Localization q.1.primeCompl) t) ^ n, ?_⟩, ?_⟩
  · rw [mem_nonZeroDivisors_iff_ne_zero]
    exact pow_ne_zero _ ht0
  · have : ((t ^ n : A)) • x = 0 := hn _ (Ideal.pow_mem_pow htq n) x
    rw [← algebraMap_smul (Localization q.1.primeCompl)] at this
    simpa using this

/-- `S⁻¹A ⧸ S⁻¹I ≅ S⁻¹(A ⧸ I)`. -/
private noncomputable def localizedQuotEquiv {A : Type*} [CommRing A] (S : Submonoid A)
    (I : Ideal A) :
    ((Localization S) ⧸ (Ideal.map (algebraMap A (Localization S)) I)) ≃ₗ[Localization S]
      LocalizedModule S (A ⧸ I) := by
  have heq : (I : Submodule A A).localized' (Localization S) S
      (Algebra.linearMap A (Localization S)) =
      Ideal.map (algebraMap A (Localization S)) I := by
    rw [Submodule.localized'_eq_span]; rfl
  have e1 : ((Localization S) ⧸ ((I : Submodule A A).localized' (Localization S) S
      (Algebra.linearMap A (Localization S)))) ≃ₗ[A] LocalizedModule S (A ⧸ I) :=
    IsLocalizedModule.linearEquiv S
      ((I : Submodule A A).toLocalizedQuotient' (Localization S) S
        (Algebra.linearMap A (Localization S)))
      (LocalizedModule.mkLinearMap S (A ⧸ I))
  rw [heq] at e1
  exact e1.extendScalarsOfIsLocalization S (Localization S)

open Classical in
/-- Trivial factors may be dropped from a product of modules. -/
private noncomputable def piSubtypeEquivOfSubsingleton {R : Type*} [CommRing R] {ι : Type*}
    (X : ι → Type*) [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)] (P : ι → Prop)
    (h : ∀ i, ¬ P i → Subsingleton (X i)) :
    ((i : ι) → X i) ≃ₗ[R] ((i : {i // P i}) → X i.1) :=
  LinearEquiv.ofBijective (LinearMap.pi fun i : {i // P i} ↦ LinearMap.proj i.1)
    ⟨fun x y hxy ↦ by
      funext i
      by_cases hi : P i
      · exact congrFun hxy ⟨i, hi⟩
      · exact @Subsingleton.elim _ (h i hi) _ _,
     fun z ↦ ⟨fun i ↦ if hi : P i then z ⟨i, hi⟩ else 0, by
       funext i
       simp [dif_pos i.2]⟩⟩

/-- **Local structure theorem**: the localization of a finitely generated torsion module at a
height one prime `q` is a finite product of modules of the form `(A ⧸ q ^ e)_q` with `e > 0`. -/
private theorem local_structure {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HeightOneLocalizationIsPID A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hMT : Module.IsTorsion A M) (q : PrimeSpectrum A) (hq : q.1.height = 1) :
    ∃ (ι : Type u) (_ : Fintype ι) (e : ι → ℕ) (_ : ∀ i, 0 < e i),
      Nonempty (LocalizedModule q.1.primeCompl M ≃ₗ[Localization q.1.primeCompl]
        ((i : ι) → LocalizedModule q.1.primeCompl (A ⧸ q.1 ^ e i))) := by
  obtain ⟨hdom, hpid⟩ := heightOne_localization_isPID q hq
  have htor := isTorsion_localizedModule hMT q hq
  obtain ⟨ι, hfin, π, hirr, e, ⟨eq1⟩⟩ := Module.equiv_directSum_of_isTorsion htor
  refine ⟨{i : ι // e i ≠ 0}, inferInstance, fun i ↦ e i.1, fun i ↦ Nat.pos_of_ne_zero i.2, ⟨?_⟩⟩
  refine eq1 ≪≫ₗ (DirectSum.linearEquivFunOnFintype _ ι _) ≪≫ₗ
    (piSubtypeEquivOfSubsingleton _ (fun i ↦ e i ≠ 0) ?_) ≪≫ₗ
    (LinearEquiv.piCongrRight fun i ↦ ?_)
  · intro i hi
    rw [not_not] at hi
    rw [hi, pow_zero]
    refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun x _ ↦ ?_)
    exact Submodule.mem_span_singleton.2 ⟨x, by simp⟩
  · have hmap : (Localization q.1.primeCompl ∙ (π i.1) ^ (e i.1)) =
        Ideal.map (algebraMap A (Localization q.1.primeCompl)) (q.1 ^ (e i.1)) := by
      rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]
      have h1 : (Ideal.span {π i.1} : Ideal (Localization q.1.primeCompl)) =
          IsLocalRing.maximalIdeal (Localization q.1.primeCompl) :=
        IsLocalRing.eq_maximalIdeal (PrincipalIdealRing.isMaximal_of_irreducible (hirr i.1))
      rw [← h1]
      exact (Ideal.span_singleton_pow _ _).symm
    rw [hmap]
    exact localizedQuotEquiv _ _

open scoped Classical in
/-- Localization commutes with finite products of modules. -/
private theorem isLocalizedModule_pi {A : Type*} [CommRing A] (S : Submonoid A)
    {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module A (X i)]
    {Y : ι → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module A (Y i)]
    (f : ∀ i, X i →ₗ[A] Y i) [inst : ∀ i, IsLocalizedModule S (f i)] :
    IsLocalizedModule S (LinearMap.pi (fun i ↦ (f i) ∘ₗ (LinearMap.proj i)) :
      (∀ i, X i) →ₗ[A] (∀ i, Y i)) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      funext i
      have hi := (Module.End.isUnit_iff _).1 (IsLocalizedModule.map_units (f i) s)
      exact hi.1 (congrFun hxy i)
    · intro y
      have : ∀ i, ∃ z : Y i, (s : A) • z = y i := by
        intro i
        exact ((Module.End.isUnit_iff _).1 (IsLocalizedModule.map_units (f i) s)).2 (y i)
      choose z hz using this
      exact ⟨z, funext hz⟩
  surj y := by
    have : ∀ i, ∃ x : X i × S, (x.2 : A) • y i = f i x.1 :=
      fun i ↦ IsLocalizedModule.surj S (f i) (y i)
    choose x hx using this
    refine ⟨⟨fun i ↦ (∏ j ∈ Finset.univ.erase i, ((x j).2 : A)) • (x i).1, ∏ j, (x j).2⟩, ?_⟩
    funext i
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply,
      map_smul, ← hx i, Submonoid.coe_finsetProd, Submonoid.smul_def]
    rw [← mul_smul, ← smul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    simp [mul_comm, mul_smul]
  exists_of_eq {x₁ x₂} h := by
    have : ∀ i, ∃ c : S, (c : A) • x₁ i = (c : A) • x₂ i := by
      intro i
      obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f i) (congrFun h i)
      exact ⟨c, hc⟩
    choose c hc using this
    refine ⟨∏ i, c i, ?_⟩
    funext i
    have hsplit : ((∏ j, c j : S) : A) = (∏ j ∈ Finset.univ.erase i, (c j : A)) * (c i : A) := by
      rw [Submonoid.coe_finsetProd, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    show ((∏ j, c j : S) : A) • x₁ i = ((∏ j, c j : S) : A) • x₂ i
    rw [hsplit, mul_smul, mul_smul, hc i]

open Classical in
/-- If all but one factor of a product of modules is trivial, the product is isomorphic to that
factor. -/
private noncomputable def dropPiEquiv {R : Type*} [CommRing R] {ι : Type*}
    (Z : ι → Type*) [∀ i, AddCommGroup (Z i)] [∀ i, Module R (Z i)] (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → Subsingleton (Z i)) :
    ((i : ι) → Z i) ≃ₗ[R] Z i₀ :=
  LinearEquiv.ofBijective (LinearMap.proj i₀)
    ⟨fun x y hxy ↦ by
      funext i
      by_cases hi : i = i₀
      · subst hi; exact hxy
      · exact @Subsingleton.elim _ (h i hi) _ _,
     fun z ↦ ⟨Function.update (0 : (i : ι) → Z i) i₀ z, by simp⟩⟩

/-- Any two trivial modules are isomorphic. -/
private def linearEquivOfSubsingleton {R : Type*} [CommRing R] {X Y : Type*} [AddCommGroup X]
    [AddCommGroup Y] [Module R X] [Module R Y] [Subsingleton X] [Subsingleton Y] :
    X ≃ₗ[R] Y where
  toFun _ := 0
  invFun _ := 0
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- A finitely generated torsion module is annihilated by a non-zero-divisor. -/
private theorem exists_nzd_smul_eq_zero {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] [Module.Finite A M] (hMT : Module.IsTorsion A M) :
    ∃ d ∈ nonZeroDivisors A, ∀ m : M, d • m = 0 := by
  classical
  obtain ⟨t, ht⟩ := ‹Module.Finite A M›
  have h1 : ∀ m : M, ∃ a : nonZeroDivisors A, (a : A) • m = 0 := fun m ↦ by
    obtain ⟨a, ha⟩ := hMT (x := m)
    exact ⟨a, ha⟩
  choose d hd using h1
  refine ⟨∏ m ∈ t, (d m : A), ?_, fun m ↦ ?_⟩
  · exact prod_mem fun m _ ↦ (d m).2
  · have hker : (⊤ : Submodule A M) ≤ LinearMap.ker
        (DistribSMul.toLinearMap A M (∏ m ∈ t, (d m : A))) := by
      rw [← ht, Submodule.span_le]
      intro x hx
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      show (∏ m ∈ t, (d m : A)) • x = 0
      rw [← Finset.prod_erase_mul _ _ hx, mul_smul]
      rw [hd x, smul_zero]
    have := hker (Submodule.mem_top (x := m))
    simpa using this

/-- **Structure theorem of finitely generated torsion modules up to pseudo-isomorphism**:
A finitely generated torsion module over a Noetherian ring `A` satisfying
`HeightOneLocalizationIsPID` is pseudo-isomorphic to a finite product of some `A ⧸ pᵢ ^ eᵢ`
where the `pᵢ ^ eᵢ` are powers of height one primes of `A`. -/
theorem Module.IsTorsion.isPseudoIsomorphic_pi
    {A : Type u} [CommRing A] [IsNoetherianRing A] [HeightOneLocalizationIsPID A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] (hMT : Module.IsTorsion A M) :
    ∃ (ι : Type u) (_ : Fintype ι) (p : ι → PrimeSpectrum A) (_ : ∀ i, (p i).1.height = 1)
      (e : ι → ℕ) (_ : ∀ i, 0 < e i), M ∼ₚᵢₛ[A] ((i : ι) → A ⧸ (p i).1 ^ (e i)) := by
  classical
  have hfin := hMT.finite_height_one_support
  set s : Finset (PrimeSpectrum A) := hfin.toFinset with hsdef
  have hsmem : ∀ q : PrimeSpectrum A, q ∈ s → (q ∈ Module.support A M ∧ q.1.height = 1) := by
    intro q hq; simpa [hsdef] using hq
  have hL : ∀ q : {q : PrimeSpectrum A // q ∈ s}, ∃ (ι : Type u) (_ : Fintype ι) (e : ι → ℕ)
      (_ : ∀ i, 0 < e i),
      Nonempty (LocalizedModule (q.1).1.primeCompl M ≃ₗ[Localization (q.1).1.primeCompl]
        ((i : ι) → LocalizedModule (q.1).1.primeCompl (A ⧸ (q.1).1 ^ e i))) :=
    fun q ↦ local_structure hMT q.1 (hsmem q.1 q.2).2
  choose ιq ftq eqq epos equivq using hL
  haveI : ∀ q : {q : PrimeSpectrum A // q ∈ s}, Fintype (ιq q) := ftq
  refine ⟨(q : {q : PrimeSpectrum A // q ∈ s}) × ιq q, inferInstance, fun j ↦ (j.1).1,
    fun j ↦ (hsmem (j.1).1 (j.1).2).2, fun j ↦ eqq j.1 j.2, fun j ↦ epos j.1 j.2, ?_⟩
  -- notation
  set ι := (q : {q : PrimeSpectrum A // q ∈ s}) × ιq q with hι
  set X : ι → Type u := fun j ↦ A ⧸ ((j.1).1).1 ^ (eqq j.1 j.2) with hX
  -- N is finite
  haveI : Module.Finite A ((j : ι) → X j) := Module.Finite.pi
  -- N is torsion
  obtain ⟨d, hd, hdM⟩ := exists_nzd_smul_eq_zero hMT
  have hdmem : ∀ j : ι, d ∈ ((j.1).1).1 := by
    intro j
    have h1 : Module.annihilator A M ≤ ((j.1).1).1 :=
      Module.annihilator_le_of_mem_support (hsmem (j.1).1 (j.1).2).1
    exact h1 (Module.mem_annihilator.2 hdM)
  have hNT : Module.IsTorsion A ((j : ι) → X j) := by
    intro x
    set K := Finset.univ.sup (fun j : ι ↦ eqq j.1 j.2) with hK
    refine ⟨⟨d ^ K, pow_mem hd K⟩, ?_⟩
    funext j
    show (d ^ K) • (x j) = 0
    have hmem : d ^ K ∈ ((j.1).1).1 ^ (eqq j.1 j.2) := by
      have hle : eqq j.1 j.2 ≤ K := Finset.le_sup (f := fun j : ι ↦ eqq j.1 j.2) (Finset.mem_univ j)
      have hsplit : d ^ K = d ^ (eqq j.1 j.2) * d ^ (K - eqq j.1 j.2) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hdmem j) _)
    induction (x j) using Submodule.Quotient.induction_on with
    | H a =>
      rw [← Submodule.Quotient.mk_smul]
      exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mul_mem_right _ _ hmem)
  rw [isPseudoIsomorphic_iff_aux hMT hNT]
  intro p hp
  have hfactor : ∀ (q : {q : PrimeSpectrum A // q ∈ s}) (i : ιq q), q.1 ≠ p →
      Subsingleton (LocalizedModule p.1.primeCompl (A ⧸ ((q.1).1) ^ (eqq q i))) := by
    intro q i hne
    rw [← Module.notMem_support_iff, Ring.support_quotient]
    intro hmem
    simp only [PrimeSpectrum.mem_zeroLocus] at hmem
    have hle : ((q.1).1) ^ (eqq q i) ≤ p.1 := hmem
    rw [Ideal.IsPrime.pow_le_iff (epos q i).ne'] at hle
    have h1 : (q.1).1.height = 1 := (hsmem q.1 q.2).2
    have : p.1.FiniteHeight := p.1.finiteHeight_iff.2 (Or.inr (by rw [hp]; nofun))
    rcases eq_or_lt_of_le hle with h | h
    · exact hne (PrimeSpectrum.ext h)
    · exact absurd (Ideal.height_strict_mono_of_isPrime_of_isPrime h) (by rw [h1, hp]; simp)
  haveI : ∀ j : ι, IsLocalizedModule p.1.primeCompl
      (LocalizedModule.mkLinearMap p.1.primeCompl (X j)) := fun j ↦ inferInstance
  haveI := isLocalizedModule_pi (A := A) p.1.primeCompl
    (fun j : ι ↦ LocalizedModule.mkLinearMap p.1.primeCompl (X j))
  have e1A : LocalizedModule p.1.primeCompl ((j : ι) → X j) ≃ₗ[A]
      ((j : ι) → LocalizedModule p.1.primeCompl (X j)) :=
    IsLocalizedModule.linearEquiv p.1.primeCompl
      (LocalizedModule.mkLinearMap p.1.primeCompl ((j : ι) → X j))
      (LinearMap.pi fun j : ι ↦
        (LocalizedModule.mkLinearMap p.1.primeCompl (X j)) ∘ₗ (LinearMap.proj j))
  have e1 : LocalizedModule p.1.primeCompl ((j : ι) → X j) ≃ₗ[Localization p.1.primeCompl]
      ((j : ι) → LocalizedModule p.1.primeCompl (X j)) :=
    e1A.extendScalarsOfIsLocalization p.1.primeCompl (Localization p.1.primeCompl)
  have e2 := LinearEquiv.piCurry (Localization p.1.primeCompl)
    (fun (q : {q : PrimeSpectrum A // q ∈ s}) (i : ιq q) ↦
      LocalizedModule p.1.primeCompl (A ⧸ ((q.1).1) ^ (eqq q i)))
  by_cases hps : p ∈ s
  · set q₀ : {q : PrimeSpectrum A // q ∈ s} := ⟨p, hps⟩ with hq₀
    have e3 : ((q : {q : PrimeSpectrum A // q ∈ s}) → (i : ιq q) →
        LocalizedModule p.1.primeCompl (A ⧸ ((q.1).1) ^ (eqq q i)))
        ≃ₗ[Localization p.1.primeCompl]
        ((i : ιq q₀) → LocalizedModule p.1.primeCompl (A ⧸ ((q₀.1).1) ^ (eqq q₀ i))) := by
      refine dropPiEquiv _ q₀ (fun q hq ↦ ?_)
      have hne : q.1 ≠ p := fun h ↦ hq (Subtype.ext h)
      haveI := fun i ↦ hfactor q i hne
      infer_instance
    exact ⟨(equivq q₀).some ≪≫ₗ e3.symm ≪≫ₗ e2.symm ≪≫ₗ e1.symm⟩
  · have hpM : p ∉ Module.support A M := fun h ↦ hps (by simp [hsdef, h, hp])
    rw [Module.notMem_support_iff] at hpM
    have hsub : Subsingleton ((j : ι) → LocalizedModule p.1.primeCompl (X j)) := by
      have : ∀ j : ι, Subsingleton (LocalizedModule p.1.primeCompl (X j)) := by
        intro j
        exact hfactor j.1 j.2 (fun h ↦ hps (h ▸ (j.1).2))
      infer_instance
    haveI : Subsingleton (LocalizedModule p.1.primeCompl ((j : ι) → X j)) :=
      e1.toEquiv.subsingleton
    exact ⟨linearEquivOfSubsingleton⟩

/-- Let `A` be a Noetherian ring satisfying `HeightOneLocalizationIsPID`. Then two finitely
generated torsion `A`-modules `M`, `N` are pseudo-isomorphic if and only if their localizations
at all height one primes are isomorphic. -/
theorem Module.IsTorsion.isPseudoIsomorphic_iff_nonempty_linearEquiv_localizedModule
    {A : Type*} [CommRing A] [IsNoetherianRing A] [HeightOneLocalizationIsPID A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] (hMT : Module.IsTorsion A M)
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] (hNT : Module.IsTorsion A N) :
    M ∼ₚᵢₛ[A] N ↔ ∀ p : PrimeSpectrum A, p.1.height = 1 →
      Nonempty ((LocalizedModule p.1.primeCompl M) ≃ₗ[Localization p.1.primeCompl]
        (LocalizedModule p.1.primeCompl N)) := by
  exact isPseudoIsomorphic_iff_aux hMT hNT

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

/-- If `q` is a prime containing a non-zero-divisor `d` and `A_q` is a PID domain, then
`(M ⧸ torsion M)_q` is a torsion free `A_q`-module. -/
private theorem isTorsionFree_loc {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (q : PrimeSpectrum A) (d : A) (hd : d ∈ nonZeroDivisors A) (hdq : d ∈ q.1)
    [IsDomain (Localization q.1.primeCompl)]
    [IsPrincipalIdealRing (Localization q.1.primeCompl)] :
    Module.IsTorsionFree (Localization q.1.primeCompl)
      (LocalizedModule q.1.primeCompl (M ⧸ Submodule.torsion A M)) := by
  set R := Localization q.1.primeCompl
  set X := M ⧸ Submodule.torsion A M
  -- key claim
  have key : ∀ (z : LocalizedModule q.1.primeCompl X) (r : R), r ≠ 0 → r • z = 0 → z = 0 := by
    intro z r hr hrz
    by_contra hz
    -- the annihilator of z
    set J : Ideal R := (LinearMap.toSpanSingleton R (LocalizedModule q.1.primeCompl X) z).ker
      with hJ
    have hrJ : r ∈ J := by simpa [hJ, LinearMap.toSpanSingleton] using hrz
    obtain ⟨r₀, hr₀⟩ := (IsPrincipalIdealRing.principal J).principal
    have hr₀0 : r₀ ≠ 0 := by
      intro h
      rw [h] at hr₀
      simp only [Submodule.span_zero_singleton] at hr₀
      rw [hr₀] at hrJ
      exact hr (by simpa using hrJ)
    have hr₀u : ¬ IsUnit r₀ := by
      intro hu
      have : (1 : R) ∈ J := by
        rw [hr₀]
        exact (Submodule.mem_span_singleton).2 ⟨(hu.unit⁻¹ : Rˣ), by simp⟩
      have : z = 0 := by simpa [hJ, LinearMap.toSpanSingleton] using this
      exact hz this
    obtain ⟨π, hπ, c, hc⟩ := WfDvdMonoid.exists_irreducible_factor hr₀u hr₀0
    have hz' : c • z ≠ 0 := by
      intro h
      have hcJ : c ∈ J := by simpa [hJ, LinearMap.toSpanSingleton] using h
      rw [hr₀, Submodule.mem_span_singleton] at hcJ
      obtain ⟨t, ht⟩ := hcJ
      have hcne : c ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hc
        exact hr₀0 hc
      have hct : c = t * (π * c) := by
        rw [← hc]
        simpa [smul_eq_mul] using ht.symm
      have hzero : c * (1 - t * π) = 0 := by linear_combination hct
      rcases mul_eq_zero.1 hzero with h1 | h1
      · exact hcne h1
      · have hu : π * t = 1 := by linear_combination -h1
        exact hπ.not_isUnit (IsUnit.of_mul_eq_one t hu)
    have hπz : π • (c • z) = 0 := by
      rw [smul_smul, ← hc]
      simpa [hJ, LinearMap.toSpanSingleton] using (hr₀ ▸ Submodule.mem_span_singleton_self r₀ :
        r₀ ∈ J)
    -- `π` generates the maximal ideal, hence `d` kills `c • z`
    have hmax : (Ideal.span {π} : Ideal R) = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (PrincipalIdealRing.isMaximal_of_irreducible hπ)
    have hdm : algebraMap A R d ∈ (Ideal.span {π} : Ideal R) := by
      rw [hmax, ← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hdq
    obtain ⟨t', ht'⟩ := Ideal.mem_span_singleton'.1 hdm
    have hdz : (algebraMap A R d) • (c • z) = 0 := by
      rw [← ht', mul_smul, hπz, smul_zero]
    obtain ⟨x, u, hxu⟩ : ∃ (x : X) (u : q.1.primeCompl), c • z = LocalizedModule.mk x u :=
      LocalizedModule.induction_on (β := fun w ↦ ∃ x u, w = LocalizedModule.mk x u)
        (fun m s ↦ ⟨m, s, rfl⟩) (c • z)
    rw [hxu, algebraMap_smul, LocalizedModule.smul'_mk] at hdz
    rw [show (0 : LocalizedModule q.1.primeCompl X) = LocalizedModule.mk 0 1 from OreLocalization.zero_def,
      LocalizedModule.mk_eq] at hdz
    obtain ⟨w, hw⟩ := hdz
    have hwx : (w : A) • x = 0 := by
      have h2 : d • ((w : A) • x) = 0 := by
        rw [smul_smul, mul_comm, ← smul_smul]
        simpa [Submonoid.smul_def] using hw
      have : (w : A) • x ∈ Submodule.torsion A X :=
        (Submodule.mem_torsion_iff _).2 ⟨⟨d, hd⟩, h2⟩
      rw [Submodule.QuotientTorsion.torsion_eq_bot] at this
      simpa using this
    refine hz' ?_
    rw [hxu, show (0 : LocalizedModule q.1.primeCompl X) = LocalizedModule.mk 0 1 from OreLocalization.zero_def,
      LocalizedModule.mk_eq]
    exact ⟨w, by simpa [Submonoid.smul_def] using hwx⟩
  refine ⟨fun r hr x y hxy ↦ ?_⟩
  have h0 : r • (x - y) = 0 := by
    rw [smul_sub]
    exact sub_eq_zero_of_eq hxy
  exact sub_eq_zero.1 (key (x - y) r (isRegular_iff_ne_zero.1 hr) h0)

/-- At a height one prime `q` in the support of the torsion submodule `T` of `M`, the exact
sequence `0 → T → M → M ⧸ T → 0` splits after localizing at `q`; a retraction can be chosen to
be the localization of an `A`-linear map `M → T`. -/
private theorem exists_retraction {A : Type*} [CommRing A] [IsNoetherianRing A]
    [HeightOneLocalizationIsPID A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (q : PrimeSpectrum A) (hq : q.1.height = 1)
    (d : A) (hd : d ∈ nonZeroDivisors A) (hdq : d ∈ q.1) :
    ∃ g : M →ₗ[A] Submodule.torsion A M,
      Function.Bijective ((LocalizedModule.map q.1.primeCompl g) ∘ₗ
        (LocalizedModule.map q.1.primeCompl (Submodule.torsion A M).subtype)) := by
  set T := Submodule.torsion A M with hT
  set S := q.1.primeCompl with hS
  obtain ⟨hdom, hpid⟩ := heightOne_localization_isPID q hq
  haveI := isTorsionFree_loc (M := M) q d hd hdq
  haveI : Module.Free (Localization S) (LocalizedModule S (M ⧸ T)) :=
    Module.free_of_finite_type_torsion_free'
  set iq := LocalizedModule.map S T.subtype with hiq
  set πq := LocalizedModule.map S T.mkQ with hπq
  have hπsurj : Function.Surjective πq := LocalizedModule.map_surjective S _ T.mkQ_surjective
  have hiinj : Function.Injective iq := LocalizedModule.map_injective S _ T.injective_subtype
  have hexact : Function.Exact iq πq :=
    LocalizedModule.map_exact S _ _ (LinearMap.exact_subtype_mkQ T)
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property πq LinearMap.id hπsurj
  set w : LocalizedModule S M →ₗ[Localization S] LocalizedModule S M :=
    LinearMap.id - σ ∘ₗ πq with hw
  have hwmem : ∀ y, w y ∈ LinearMap.range iq := by
    intro y
    rw [← LinearMap.exact_iff.1 hexact]
    have : πq (w y) = 0 := by
      simp only [hw, LinearMap.sub_apply, LinearMap.id_apply, map_sub, LinearMap.comp_apply]
      have := LinearMap.congr_fun hσ (πq y)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [this, sub_self]
    exact this
  set r : LocalizedModule S M →ₗ[Localization S] LocalizedModule S T :=
    (LinearEquiv.ofInjective iq hiinj).symm.toLinearMap ∘ₗ (w.codRestrict _ hwmem) with hr
  have hri : ∀ t, r (iq t) = t := by
    intro t
    apply hiinj
    have h1 : iq (r (iq t)) = w (iq t) := by
      simp only [hr, LinearMap.coe_comp, Function.comp_apply]
      exact congrArg Subtype.val ((LinearEquiv.ofInjective iq hiinj).apply_symm_apply _)
    rw [h1]
    have h2 : πq (iq t) = 0 := hexact.apply_apply_eq_zero t
    simp only [hw, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h2, map_zero,
      sub_zero]
  obtain ⟨g, s, hgs⟩ := exists_lift_localizedModule_map S (r.restrictScalars A)
  refine ⟨g, ?_⟩
  have hcomp : ∀ t, ((LocalizedModule.map S g) ∘ₗ iq) t = (s : A) • t := by
    intro t
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hgs (iq t)]
    simp only [LinearMap.coe_restrictScalars, hri t]
  have : ((LocalizedModule.map S g) ∘ₗ iq : LocalizedModule S T → LocalizedModule S T) =
      fun t ↦ (s : A) • t := funext hcomp
  rw [this]
  have := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S T) s
  rw [Module.End.isUnit_iff] at this
  exact this

/-- If `0 → T → M → X` is exact with `M → X` surjective and `ρ : M → T` restricts to a
bijection on `T`, then `(ρ, π) : M → T × X` is bijective. -/
private theorem bijective_prod_of_exact {R : Type*} [CommRing R] {T' M' X' : Type*}
    [AddCommGroup T'] [Module R T'] [AddCommGroup M'] [Module R M'] [AddCommGroup X'] [Module R X']
    (i : T' →ₗ[R] M') (π : M' →ₗ[R] X') (ρ : M' →ₗ[R] T')
    (hπ : Function.Surjective π) (hexact : Function.Exact i π)
    (hρ : Function.Bijective (ρ ∘ₗ i)) : Function.Bijective (LinearMap.prod ρ π) := by
  constructor
  · intro x y hxy
    rw [Prod.ext_iff] at hxy
    obtain ⟨h1, h2⟩ := hxy
    simp only [LinearMap.prod_apply, Function.prod_apply] at h1 h2
    have hsub : π (x - y) = 0 := by rw [map_sub, h2, sub_self]
    obtain ⟨t, ht⟩ := (hexact (x - y)).1 hsub
    have : (ρ ∘ₗ i) t = 0 := by
      simp only [LinearMap.coe_comp, Function.comp_apply, ht, map_sub, h1, sub_self]
    have ht0 : t = 0 := hρ.1 (by simpa using this)
    rw [ht0, map_zero] at ht
    exact sub_eq_zero.1 ht.symm
  · rintro ⟨t, x⟩
    obtain ⟨m₀, hm₀⟩ := hπ x
    obtain ⟨t', ht'⟩ := hρ.2 (t - ρ m₀)
    refine ⟨m₀ + i t', ?_⟩
    have h1 : π (i t') = 0 := hexact.apply_apply_eq_zero t'
    simp only [LinearMap.prod_apply, Function.prod_apply, map_add, h1, hm₀]
    simp only [LinearMap.coe_comp, Function.comp_apply] at ht'
    rw [ht']
    simp

/-- Localization commutes with binary products of modules. -/
private theorem isLocalizedModule_prodMap {A : Type*} [CommRing A] (S : Submonoid A)
    {X X' Y Y' : Type*} [AddCommGroup X] [Module A X] [AddCommGroup X'] [Module A X']
    [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y']
    (f : X →ₗ[A] X') (g : Y →ₗ[A] Y') [IsLocalizedModule S f] [IsLocalizedModule S g] :
    IsLocalizedModule S (f.prodMap g) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have hf := (Module.End.isUnit_iff _).1 (IsLocalizedModule.map_units f s)
    have hg := (Module.End.isUnit_iff _).1 (IsLocalizedModule.map_units g s)
    constructor
    · rintro ⟨x1, y1⟩ ⟨x2, y2⟩ h
      rw [Prod.ext_iff] at h ⊢
      exact ⟨hf.1 h.1, hg.1 h.2⟩
    · rintro ⟨x, y⟩
      obtain ⟨x', hx'⟩ := hf.2 x
      obtain ⟨y', hy'⟩ := hg.2 y
      exact ⟨⟨x', y'⟩, Prod.ext hx' hy'⟩
  surj y := by
    obtain ⟨⟨x1, s1⟩, h1⟩ := IsLocalizedModule.surj S f y.1
    obtain ⟨⟨x2, s2⟩, h2⟩ := IsLocalizedModule.surj S g y.2
    refine ⟨⟨((s2 : A) • x1, (s1 : A) • x2), s1 * s2⟩, ?_⟩
    have e1 : ((s1 * s2 : S) : A) • y.1 = f ((s2 : A) • x1) := by
      rw [map_smul, ← h1]
      simp only [Submonoid.coe_mul, Submonoid.smul_def]
      rw [mul_comm, mul_smul]
    have e2 : ((s1 * s2 : S) : A) • y.2 = g ((s1 : A) • x2) := by
      rw [map_smul, ← h2]
      simp only [Submonoid.coe_mul, Submonoid.smul_def]
      rw [mul_smul]
    exact Prod.ext e1 e2
  exists_of_eq {x₁ x₂} h := by
    rw [Prod.ext_iff] at h
    obtain ⟨c1, hc1⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) h.1
    obtain ⟨c2, hc2⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := g) h.2
    refine ⟨c1 * c2, Prod.ext ?_ ?_⟩
    · show ((c1 * c2 : S) : A) • x₁.1 = ((c1 * c2 : S) : A) • x₂.1
      simp only [Submonoid.coe_mul]
      rw [mul_comm, mul_smul, mul_smul]
      simpa [Submonoid.smul_def] using congrArg (fun z ↦ (c2 : A) • z) hc1
    · show ((c1 * c2 : S) : A) • x₁.2 = ((c1 * c2 : S) : A) • x₂.2
      simp only [Submonoid.coe_mul]
      rw [mul_smul, mul_smul]
      simpa [Submonoid.smul_def] using congrArg (fun z ↦ (c1 : A) • z) hc2

/-- Let `A` be a Noetherian ring satisfying `HeightOneLocalizationIsPID`, `M` be a finitely
generated `A`-module, `T` be the torsion submodule of `M`. Then `M` is pseudo-isomorphic to
`T × M/T`. -/
theorem Module.isPseudoIsomorphic_torsion_prod_quotient
    {A : Type*} [CommRing A] [IsNoetherianRing A] [HeightOneLocalizationIsPID A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] :
    M ∼ₚᵢₛ[A] (Submodule.torsion A M × M ⧸ Submodule.torsion A M) := by
  classical
  set T := Submodule.torsion A M with hT
  have hTT : Module.IsTorsion A T := Submodule.torsion'_isTorsion' _
  obtain ⟨d, hd, hdT⟩ := exists_nzd_smul_eq_zero hTT
  have hfin := hTT.finite_height_one_support
  set s : Finset (PrimeSpectrum A) := hfin.toFinset with hsdef
  have hsmem : ∀ q : PrimeSpectrum A, q ∈ s → (q ∈ Module.support A T ∧ q.1.height = 1) := by
    intro q hq; simpa [hsdef] using hq
  have hdq : ∀ q : PrimeSpectrum A, q ∈ s → d ∈ q.1 := fun q hq ↦
    Module.annihilator_le_of_mem_support (hsmem q hq).1 (Module.mem_annihilator.2 hdT)
  have hA : ∀ q : PrimeSpectrum A, ∃ g : M →ₗ[A] T, q ∈ s →
      Function.Bijective ((LocalizedModule.map q.1.primeCompl g) ∘ₗ
        (LocalizedModule.map q.1.primeCompl T.subtype)) := by
    intro q
    by_cases hq : q ∈ s
    · obtain ⟨g, hg⟩ := exists_retraction (M := M) q (hsmem q hq).2 d hd (hdq q hq)
      exact ⟨g, fun _ ↦ hg⟩
    · exact ⟨0, fun h ↦ absurd h hq⟩
  choose gg ggb using hA
  have hB : ∀ q : PrimeSpectrum A, ∃ n : ℕ, q ∈ s →
      ∀ c ∈ q.1 ^ n, ∀ x : LocalizedModule q.1.primeCompl T, c • x = 0 := by
    intro q
    by_cases hq : q ∈ s
    · obtain ⟨n, hn⟩ := exists_pow_smul_localizedModule_eq_zero hTT q (le_of_eq (hsmem q hq).2)
      exact ⟨n, fun _ ↦ hn⟩
    · exact ⟨0, fun h ↦ absurd h hq⟩
  choose nn hnn using hB
  have hC : ∀ q : PrimeSpectrum A, ∃ c : A, q ∈ s →
      (c ∈ ∏ q' ∈ s.erase q, q'.1 ^ (nn q' + 1) ∧ c ∉ q.1) := by
    intro q
    by_cases hq : q ∈ s
    · have hnle : ¬ ((∏ q' ∈ s.erase q, q'.1 ^ (nn q' + 1)) ≤ q.1) := by
        intro hle
        obtain ⟨q', hq', hle'⟩ := (Ideal.IsPrime.prod_le q.2).1 hle
        rw [Ideal.IsPrime.pow_le_iff (Nat.succ_ne_zero _)] at hle'
        refine (Finset.mem_erase.1 hq').1 ?_
        have h1 : q'.1.height = 1 := (hsmem q' (Finset.mem_of_mem_erase hq')).2
        have h2 : q.1.height = 1 := (hsmem q hq).2
        have : q.1.FiniteHeight := q.1.finiteHeight_iff.2 (Or.inr (by rw [h2]; nofun))
        rcases eq_or_lt_of_le hle' with h | h
        · exact PrimeSpectrum.ext h
        · exact absurd (Ideal.height_strict_mono_of_isPrime_of_isPrime h) (by rw [h1, h2]; simp)
      obtain ⟨c, hc1, hc2⟩ := SetLike.not_le_iff_exists.1 hnle
      exact ⟨c, fun _ ↦ ⟨hc1, hc2⟩⟩
    · exact ⟨0, fun h ↦ absurd h hq⟩
  choose cc hcc using hC
  set g : M →ₗ[A] T := ∑ q ∈ s, cc q • gg q with hg
  have hkey : ∀ p : PrimeSpectrum A, p.1.height ≤ 1 →
      Function.Bijective ((LocalizedModule.map p.1.primeCompl g) ∘ₗ
        (LocalizedModule.map p.1.primeCompl T.subtype)) := by
    intro p hp
    by_cases hps : p ∈ s
    · have heval : ∀ x : LocalizedModule p.1.primeCompl T,
          ((LocalizedModule.map p.1.primeCompl g) ∘ₗ
            (LocalizedModule.map p.1.primeCompl T.subtype)) x =
          cc p • ((LocalizedModule.map p.1.primeCompl (gg p)) ∘ₗ
            (LocalizedModule.map p.1.primeCompl T.subtype)) x := by
        intro x
        simp only [LinearMap.coe_comp, Function.comp_apply, hg, map_sum, map_smul,
          LinearMap.sum_apply, LinearMap.smul_apply]
        refine Finset.sum_eq_single p (fun q hq hqp ↦ ?_) (fun h ↦ absurd hps h)
        refine (hnn p hps) (cc q) ?_ _
        have hsub : (∏ q' ∈ (s.erase q), q'.1 ^ (nn q' + 1)) ≤ p.1 ^ (nn p + 1) :=
          le_trans Ideal.prod_le_inf (Finset.inf_le (Finset.mem_erase.2 ⟨Ne.symm hqp, hps⟩))
        exact Ideal.pow_le_pow_right (Nat.le_succ _) (hsub (hcc q hq).1)
      have hbij : Function.Bijective (fun x : LocalizedModule p.1.primeCompl T ↦
          cc p • ((LocalizedModule.map p.1.primeCompl (gg p)) ∘ₗ
            (LocalizedModule.map p.1.primeCompl T.subtype)) x) := by
        refine Function.Bijective.comp ?_ (ggb p hps)
        have := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap p.1.primeCompl T)
          (⟨cc p, (hcc p hps).2⟩ : p.1.primeCompl)
        rw [Module.End.isUnit_iff] at this
        exact this
      have heq : ((LocalizedModule.map p.1.primeCompl g) ∘ₗ
          (LocalizedModule.map p.1.primeCompl T.subtype) :
          LocalizedModule p.1.primeCompl T → LocalizedModule p.1.primeCompl T) =
          fun x ↦ cc p • ((LocalizedModule.map p.1.primeCompl (gg p)) ∘ₗ
            (LocalizedModule.map p.1.primeCompl T.subtype)) x := funext heval
      rw [heq]
      exact hbij
    · have hpT : p ∉ Module.support A T := fun h ↦ hps (by
        simp [hsdef, Set.mem_inter_iff, hp.antisymm (hTT.one_le_height_of_mem_support p h), h])
      rw [Module.notMem_support_iff] at hpT
      exact Function.bijective_of_subsingleton _
  refine ⟨⟨LinearMap.prod g T.mkQ, ?_⟩⟩
  rw [LinearMap.isPseudoIsomorphism_iff_height_le_one_imp_bijective]
  intro p hp
  set S := p.1.primeCompl with hS
  haveI := isLocalizedModule_prodMap S (LocalizedModule.mkLinearMap S T)
    (LocalizedModule.mkLinearMap S (M ⧸ T))
  set e := IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (T × M ⧸ T))
    ((LocalizedModule.mkLinearMap S T).prodMap (LocalizedModule.mkLinearMap S (M ⧸ T))) with he
  set P : LocalizedModule S M →ₗ[A] (LocalizedModule S T × LocalizedModule S (M ⧸ T)) :=
    LinearMap.prod ((LocalizedModule.map S g).restrictScalars A)
      ((LocalizedModule.map S T.mkQ).restrictScalars A) with hP
  have hEq : (e : LocalizedModule S (T × M ⧸ T) →ₗ[A] _) ∘ₗ
      (LocalizedModule.map S (LinearMap.prod g T.mkQ)).restrictScalars A = P := by
    refine IsLocalizedModule.ext S (LocalizedModule.mkLinearMap S M)
      (fun x ↦ IsLocalizedModule.map_units
        ((LocalizedModule.mkLinearMap S T).prodMap (LocalizedModule.mkLinearMap S (M ⧸ T))) x) ?_
    refine LinearMap.ext fun m ↦ ?_
    have hkey2 : e (LocalizedModule.mkLinearMap S (T × M ⧸ T) (g m, Submodule.Quotient.mk m)) =
        ((LocalizedModule.mkLinearMap S T).prodMap
          (LocalizedModule.mkLinearMap S (M ⧸ T))) (g m, Submodule.Quotient.mk m) := by
      rw [he]
      exact IsLocalizedModule.linearEquiv_apply S _ _ _
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LocalizedModule.mkLinearMap_apply, hP, LinearMap.prod_apply, Function.prod_apply]
    rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.map_mk]
    simpa using hkey2
  have hbij : Function.Bijective P := by
    rw [hP]
    refine bijective_prod_of_exact ((LocalizedModule.map S T.subtype).restrictScalars A)
      ((LocalizedModule.map S T.mkQ).restrictScalars A)
      ((LocalizedModule.map S g).restrictScalars A)
      (LocalizedModule.map_surjective S _ T.mkQ_surjective)
      (LocalizedModule.map_exact S _ _ (LinearMap.exact_subtype_mkQ T))
      (hkey p hp)
  have : ⇑(LocalizedModule.map S (LinearMap.prod g T.mkQ)) = ⇑e.symm ∘ ⇑P := by
    rw [← hEq]
    ext x
    simp
  rw [this]
  exact e.symm.bijective.comp hbij
