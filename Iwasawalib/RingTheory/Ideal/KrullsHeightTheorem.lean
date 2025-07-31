import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!

# Consequences of Krull's Height Theorem

-/

/-- Every height one prime ideal in a UFD is principal. -/
theorem UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (p : Ideal R) [p.IsPrime]
    (h : p.height = 1) : p.IsPrincipal := by
  rcases eq_or_ne p ⊥ with rfl | hpne
  · exact ⟨0, by rw [Submodule.span_zero_singleton]⟩
  have := p.finiteHeight_iff.2 (Or.inr (by simp [h]))
  obtain ⟨a, h1, h2⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
  replace h1 : (factors a).prod ∈ p := by
    obtain ⟨u, h⟩ := (factors_prod h2).symm
    rw [← h]
    exact Ideal.mul_mem_right _ _ h1
  rw [Ideal.IsPrime.multiset_prod_mem_iff_exists_mem ‹_›] at h1
  obtain ⟨q, hq, h1⟩ := h1
  rcases eq_or_ne q 0 with rfl | hqne
  · have := factors_prod h2
    rw [Multiset.prod_eq_zero hq, Associated.comm, associated_zero_iff_eq_zero] at this
    contradiction
  use q
  rw [Ideal.submodule_span_eq]
  have : (Ideal.span {q}).IsPrime := by
    rw [Ideal.span_singleton_prime hqne]
    exact prime_of_factor q hq
  rw [← Ideal.span_singleton_le_iff_mem] at h1
  have := mem_minimalPrimes_of_primeHeight_eq_height h1 <| by
    rw [← Ideal.height_eq_primeHeight, h]
    apply le_antisymm
    · contrapose! hqne
      simpa [ENat.lt_one_iff_eq_zero, Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff,
        IsDomain.minimalPrimes_eq_singleton_bot] using hqne
    simpa [h] using Ideal.height_mono h1
  simpa [Ideal.minimalPrimes_eq_subsingleton_self] using this

/-- A Noetherian domain whose height one prime ideals are principal is a UFD. -/
theorem UniqueFactorizationMonoid.of_primeHeight_eq_one_imp_isPrincipal
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h : ∀ p : PrimeSpectrum R, p.1.primeHeight = 1 → p.1.IsPrincipal) :
    UniqueFactorizationMonoid R where
  irreducible_iff_prime {a} := by
    refine ⟨fun ha ↦ ?_, Prime.irreducible⟩
    have hne := ha.not_isUnit
    rw [← Ideal.span_singleton_eq_top] at hne
    obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
    have := Ideal.minimalPrimes_isPrime hp
    obtain ⟨b, hb⟩ : p.IsPrincipal := by
      have : p.height ≤ 1 := by
        refine (Ideal.height_le_spanRank_toENat_of_mem_minimal_primes _ _ hp).trans ?_
        rw [← Ideal.submodule_span_eq]
        grw [Submodule.spanRank_span_le_card]
        simp
      rw [Ideal.height_eq_primeHeight] at this
      rcases this.eq_or_lt with h1 | h1
      · exact h ⟨p, ‹_›⟩ h1
      use 0
      simpa only [Submodule.span_zero_singleton, ENat.lt_one_iff_eq_zero,
        Ideal.primeHeight_eq_zero_iff,
        IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] using h1
    rw [Ideal.submodule_span_eq] at hb
    rcases ha.dvd_iff.1 (Ideal.span_singleton_le_span_singleton.1 (hb ▸ hp.1.2)) with h1 | h1
    · rw [← Ideal.span_singleton_eq_top, ← hb] at h1
      exact False.elim (this.ne_top h1)
    rwa [← Ideal.span_singleton_prime ha.ne_zero, Ideal.span_singleton_eq_span_singleton.2 h1, ← hb]

/-- A Noetherian domain is a UFD if and only if every height one prime ideal is principal. -/
theorem IsNoetherianRing.uniqueFactorizationMonoid_iff
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] :
    UniqueFactorizationMonoid R ↔
    ∀ p : PrimeSpectrum R, p.1.primeHeight = 1 → p.1.IsPrincipal :=
  ⟨fun _ p hp ↦ UniqueFactorizationMonoid.isPrincipal_of_height_eq_one p.1
    (by simpa only [Ideal.height_eq_primeHeight]),
      UniqueFactorizationMonoid.of_primeHeight_eq_one_imp_isPrincipal R⟩
