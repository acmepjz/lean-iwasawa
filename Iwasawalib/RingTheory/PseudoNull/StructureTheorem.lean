/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan, Yiming Fu, Shouxin Zhang
-/
module

public import Mathlib.Algebra.Module.PID
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
    have htfae := (IsDiscreteValuationRing.TFAE (Localization p.asIdeal.primeCompl) hnf).out 3 0
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

/-- **Structure theorem of finitely generated torsion modules up to pseudo-isomorphism**:
A finitely generated torsion module over a Noetherian ring `A` satisfying
`HeightOneLocalizationIsPID` is pseudo-isomorphic to a finite product of some `A ⧸ pᵢ ^ eᵢ`
where the `pᵢ ^ eᵢ` are powers of height one primes of `A`. -/
theorem Module.IsTorsion.isPseudoIsomorphic_pi
    {A : Type u} [CommRing A] [IsNoetherianRing A] [HeightOneLocalizationIsPID A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] (hMT : Module.IsTorsion A M) :
    ∃ (ι : Type u) (_ : Fintype ι) (p : ι → PrimeSpectrum A) (_ : ∀ i, (p i).1.height = 1)
      (e : ι → ℕ) (_ : ∀ i, 0 < e i), M ∼ₚᵢₛ[A] ((i : ι) → A ⧸ (p i).1 ^ (e i)) := by
  sorry

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
