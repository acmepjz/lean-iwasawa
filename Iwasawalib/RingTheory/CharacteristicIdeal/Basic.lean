/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Iwasawalib.Algebra.Module.Torsion
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Support

/-!

# Characteristic ideal of a finitely generated module over a Noetherian ring

-/

theorem Ring.support_quotient {A : Type*} [CommRing A] (I : Ideal A) :
    Module.support A (A ⧸ I) = PrimeSpectrum.zeroLocus I := by
  simp [Module.support_of_algebra, show algebraMap A (A ⧸ I) = Ideal.Quotient.mk I from rfl]

/-- There are only finitely many height one primes contained in the support of a
finitely generated torsion module over a Noetherian ring. -/
theorem Module.IsTorsion.finite_primeHeight_one_support
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (H : Module.IsTorsion A M) :
    (Module.support A M ∩ {p : PrimeSpectrum A | p.1.primeHeight = 1}).Finite := by
  induction ‹Module.Finite A M› using
    IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A with
  | subsingleton N => simp [Module.support_eq_empty]
  | quotient N p f =>
    rw [f.isTorsion] at H
    have hp : 1 ≤ p.1.primeHeight := H.one_le_primeHeight_of_mem_support p <| by
      simp [Ring.support_quotient]
    rw [f.support_eq, Ring.support_quotient]
    refine (Set.finite_singleton p).subset fun q ⟨h1, h2⟩ ↦ ?_
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
      PrimeSpectrum.asIdeal_le_asIdeal] at h1
    rw [Set.mem_setOf_eq] at h2
    rw [Set.mem_singleton_iff]
    ext1
    have : q.1.FiniteHeight := ⟨.inr (by simp [q.1.height_eq_primeHeight, h2])⟩
    have := p.1.height_eq_primeHeight ▸ (h2 ▸ hp).antisymm (Ideal.primeHeight_mono h1)
    have := mem_minimalPrimes_of_primeHeight_eq_height h1 this
    simpa [Ideal.minimalPrimes_eq_subsingleton_self] using this
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    specialize h₁ (H.injective hf)
    specialize h₃ (H.surjective hg)
    rw [Module.support_of_exact hfg hf hg, Set.union_inter_distrib_right]
    exact h₁.union h₃

open scoped Classical in
theorem Module.length_localizedModule_primeCompl_quotient_prime_eq_of_primeHeight_le
    {A : Type*} [CommRing A] {p q : PrimeSpectrum A}
    (hp : p.1.primeHeight ≠ ⊤) (hq : p.1.primeHeight ≤ q.1.primeHeight) :
    Module.length (Localization p.1.primeCompl) (LocalizedModule p.1.primeCompl (A ⧸ q.1)) =
      if p = q then 1 else 0 := by
  have : p.1.FiniteHeight := ⟨.inr (by simpa only [p.1.height_eq_primeHeight])⟩
  by_cases hpq : p ≠ q
  · rw [if_neg hpq, Module.length_eq_zero_iff]
    rw [← Module.notMem_support_iff, Ring.support_quotient,
      PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, PrimeSpectrum.asIdeal_le_asIdeal]
    intro h
    simpa using lt_of_le_of_lt hq (Ideal.primeHeight_strict_mono (h.lt_of_ne hpq.symm))
  rw [ne_eq, not_not] at hpq
  rw [if_pos hpq, Module.length_eq_one_iff, ← hpq, ← LinearMap.isSimpleModule_iff_of_bijective _
    (localizedQuotientEquiv p.1.primeCompl p.1).bijective, isSimpleModule_iff_quot_maximal]
  refine ⟨_, IsLocalRing.maximalIdeal.isMaximal (Localization p.1.primeCompl),
    ⟨Submodule.Quotient.equiv _ _ (LocalizedModule.equivTensorProduct p.1.primeCompl A ≪≫ₗ
      TensorProduct.AlgebraTensorModule.rid _ _ _) ?_⟩⟩
  change Submodule.map (LinearEquiv.toLinearMap _) _ = _
  rw [LinearEquiv.map_eq_comap]
  ext x
  induction x with | H x =>
  nth_rw 2 [Localization.mk_eq_mk']
  rw [IsLocalization.AtPrime.mk'_mem_maximal_iff _ p.1, Submodule.mem_comap, LinearEquiv.coe_coe]
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.rid_symm_apply,
    LocalizedModule.equivTensorProduct_symm_apply_tmul, Submodule.mem_localized']
  simp_rw [← IsLocalizedModule.mk_eq_mk', LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨fun ⟨a, ha, ⟨b, hb⟩, u, hu⟩ ↦ ?_, fun h ↦ ⟨x.1, h, x.2, 1, by simp⟩⟩
  change u.1 * (x.2.1 * a) = u.1 * (b * (x.1 * 1)) at hu
  rw [← mul_assoc, mul_one, ← mul_assoc] at hu
  replace ha := p.1.mul_mem_left (u.1 * x.2.1) ha
  rw [hu] at ha
  exact (p.2.mem_or_mem ha).resolve_left (p.1.primeCompl.mul_mem u.2 hb)

theorem Module.isFiniteLength_localizedModule_primeCompl_quotient_prime_of_primeHeight_le
    {A : Type*} [CommRing A] {p q : PrimeSpectrum A}
    (hp : p.1.primeHeight ≠ ⊤) (hq : p.1.primeHeight ≤ q.1.primeHeight) :
    IsFiniteLength (Localization p.1.primeCompl) (LocalizedModule p.1.primeCompl (A ⧸ q.1)) := by
  rw [← Module.length_ne_top_iff,
    Module.length_localizedModule_primeCompl_quotient_prime_eq_of_primeHeight_le hp hq]
  split_ifs <;> simp

/-- Let `M` be a finitely generated torsion module over a Noetherian ring `A`. For any prime ideal
`p` of `A` of height `≤ 1`, the `Mₚ` is of finite length over `Aₚ`. -/
theorem Module.IsTorsion.isFiniteLength_localizedModule_of_primeHeight_le_one
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (H : Module.IsTorsion A M)
    (p : PrimeSpectrum A) (hp : p.1.primeHeight ≤ 1) :
    IsFiniteLength (Localization p.1.primeCompl) (LocalizedModule p.1.primeCompl M) := by
  by_cases hmem : p ∉ Module.support A M
  · rw [Module.notMem_support_iff] at hmem
    exact IsFiniteLength.of_subsingleton
  rw [not_not] at hmem
  replace hp := hp.antisymm (H.one_le_primeHeight_of_mem_support p hmem)
  clear hmem
  induction ‹Module.Finite A M› using
    IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A with
  | subsingleton N => exact IsFiniteLength.of_subsingleton
  | quotient N q f =>
    rw [f.isTorsion] at H
    have hq : 1 ≤ q.1.primeHeight := H.one_le_primeHeight_of_mem_support q <| by
      simp [Ring.support_quotient]
    refine (LinearEquiv.ofBijective (LocalizedModule.map p.1.primeCompl f.toLinearMap)
      ⟨LocalizedModule.map_injective _ _ f.injective,
        LocalizedModule.map_surjective _ _ f.surjective⟩).symm.isFiniteLength ?_
    exact Module.isFiniteLength_localizedModule_primeCompl_quotient_prime_of_primeHeight_le
      (by simp [hp]) (hp ▸ hq)
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    specialize h₁ (H.injective hf)
    specialize h₃ (H.surjective hg)
    rw [← Module.length_ne_top_iff, ← lt_top_iff_ne_top] at h₁ h₃ ⊢
    rw [Module.length_eq_add_of_exact (LocalizedModule.map p.1.primeCompl f)
      (LocalizedModule.map p.1.primeCompl g) (LocalizedModule.map_injective _ f hf)
      (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g hfg)]
    exact ENat.add_lt_top.2 ⟨h₁, h₃⟩

/-- The characteristic ideal `char(M)` of a module `M` over a ring `A`. It is
mathematically correct if the module is finitely generated torsion over a Noetherian ring. -/
noncomputable def Module.charIdeal
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M] : Ideal A :=
  ∏ᶠ (p : PrimeSpectrum A), if p.1.primeHeight = 1 then
    p.1 ^ (Module.length (Localization p.1.primeCompl) (LocalizedModule p.1.primeCompl M)).toNat
  else
    1

theorem Module.charIdeal_eq_prod_of_support_subset
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
    (s : Finset (PrimeSpectrum A)) (hh : ∀ p ∈ s, p.1.primeHeight = 1)
    (hs : Module.support A M ∩ {p : PrimeSpectrum A | p.1.primeHeight = 1} ⊆ s) :
    Module.charIdeal A M = ∏ p ∈ s, p.1 ^ (Module.length (Localization p.1.primeCompl)
      (LocalizedModule p.1.primeCompl M)).toNat := by
  rw [charIdeal, finprod_eq_prod_of_mulSupport_subset _ (s := s) ?_]
  · congr! 2 with p hp
    simp [hh p hp]
  intro p hp
  simp_rw [Function.mem_mulSupport] at hp
  split_ifs at hp with h
  · replace hp : (Module.length (Localization p.1.primeCompl)
        (LocalizedModule p.1.primeCompl M)).toNat ≠ 0 := by
      contrapose! hp
      simp [hp]
    rw [ne_eq, ENat.toNat_eq_zero, not_or, Module.length_eq_zero_iff,
      not_subsingleton_iff_nontrivial, ← Module.mem_support_iff] at hp
    exact hs ⟨hp.1, h⟩
  · contradiction

/-- If `0 → M → N → P → 0` is a short exact sequence of fintely generated torsion modules
over a Noetherian ring, then `char(N) = char(M) * char(P)`. -/
theorem Module.IsTorsion.charIdeal_eq_mul_of_exact
    {A M N P : Type*} [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    [Module.Finite A N] (H : Module.IsTorsion A N) (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Module.charIdeal A N = Module.charIdeal A M * Module.charIdeal A P := by
  have hMt := H.injective hf
  have hPt := H.surjective hg
  have := isNoetherian_of_injective f hf
  have := Module.Finite.of_surjective g hg
  let s := H.finite_primeHeight_one_support.toFinset
  have hh : ∀ p ∈ s, p.1.primeHeight = 1 := fun p hp ↦ by
    simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq, s] at hp
    exact hp.2
  have hNs : Module.support A N ∩ {p : PrimeSpectrum A | p.1.primeHeight = 1} ⊆ s := by
    simp [s]
  have hMs : Module.support A M ∩ {p : PrimeSpectrum A | p.1.primeHeight = 1} ⊆ s := by
    refine subset_trans ?_ hNs
    gcongr
    exact Module.support_subset_of_injective f hf
  have hPs : Module.support A P ∩ {p : PrimeSpectrum A | p.1.primeHeight = 1} ⊆ s := by
    refine subset_trans ?_ hNs
    gcongr
    exact Module.support_subset_of_surjective g hg
  rw [Module.charIdeal_eq_prod_of_support_subset A N s hh hNs,
    Module.charIdeal_eq_prod_of_support_subset A M s hh hMs,
    Module.charIdeal_eq_prod_of_support_subset A P s hh hPs, ← Finset.prod_mul_distrib]
  congr! 2 with p hp
  rw [← pow_add]
  congr 1
  rw [Module.length_eq_add_of_exact (LocalizedModule.map p.1.primeCompl f)
    (LocalizedModule.map p.1.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g hfg)]
  simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq, s] at hp
  have hMl := hMt.isFiniteLength_localizedModule_of_primeHeight_le_one p (by simp [hp.2])
  have hPl := hPt.isFiniteLength_localizedModule_of_primeHeight_le_one p (by simp [hp.2])
  rw [← Module.length_ne_top_iff] at hMl hPl
  exact ENat.toNat_add hMl hPl

theorem Module.IsTorsion.charIdeal_dvd_of_injective
    {A M N : Type*} [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] (H : Module.IsTorsion A N) (f : M →ₗ[A] N)
    (hf : Function.Injective f) :
    Module.charIdeal A M ∣ Module.charIdeal A N := by
  rw [H.charIdeal_eq_mul_of_exact f (LinearMap.range f).mkQ hf
    (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range f)]
  exact dvd_mul_right _ _

theorem Module.IsTorsion.charIdeal_dvd_of_surjective
    {A N P : Type*} [CommRing A] [IsNoetherianRing A] [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] [Module.Finite A N] (H : Module.IsTorsion A N) (g : N →ₗ[A] P)
    (hg : Function.Surjective g) :
    Module.charIdeal A P ∣ Module.charIdeal A N := by
  rw [H.charIdeal_eq_mul_of_exact (LinearMap.ker g).subtype g (Submodule.subtype_injective _) hg
    (LinearMap.exact_subtype_ker_map g)]
  exact dvd_mul_left _ _

theorem Module.IsTorsion.charIdeal_prod
    {A M P : Type*} [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] [Module.Finite A M] [Module.Finite A P]
    (HM : Module.IsTorsion A M) (HP : Module.IsTorsion A P) :
    Module.charIdeal A (M × P) = Module.charIdeal A M * Module.charIdeal A P :=
  (HM.prod HP).charIdeal_eq_mul_of_exact _ _
    LinearMap.inl_injective LinearMap.snd_surjective .inl_snd

theorem Module.charIdeal_eq_one_of_subsingleton
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M] [Subsingleton M] :
    Module.charIdeal A M = 1 := by
  simp [Module.charIdeal_eq_prod_of_support_subset A M ∅
    (by simp) (by simp [Module.support_eq_empty])]

theorem LinearEquiv.charIdeal_eq
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {M' : Type*} [AddCommGroup M'] [Module A M']
    (f : M ≃ₗ[A] M') : Module.charIdeal A M = Module.charIdeal A M' := by
  simp_rw [Module.charIdeal]
  congr! 4 with p _
  rw [(LinearEquiv.ofBijective (LocalizedModule.map p.1.primeCompl f.toLinearMap)
    ⟨LocalizedModule.map_injective _ _ f.injective,
      LocalizedModule.map_surjective _ _ f.surjective⟩).length_eq]

theorem Module.charIdeal_quotient_prime_eq_of_one_le_primeHeight
    {A : Type*} [CommRing A] (p : PrimeSpectrum A) (hp : 1 ≤ p.1.primeHeight) :
    Module.charIdeal A (A ⧸ p.1) = if p.1.primeHeight = 1 then p.1 else 1 := by
  have hf : ({p} ∩ {p : PrimeSpectrum A | p.1.primeHeight = 1}).Finite :=
    Set.Finite.inter_of_left (by simp) _
  have heq := Module.charIdeal_eq_prod_of_support_subset A (A ⧸ p.1) hf.toFinset
    (fun q h ↦ by
      simp only [Set.toFinite_toFinset, Set.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq] at h
      exact h.2)
    (fun q ↦ by
      simp only [Ring.support_quotient p.1, Set.mem_inter_iff, PrimeSpectrum.mem_zeroLocus,
        SetLike.coe_subset_coe, PrimeSpectrum.asIdeal_le_asIdeal, Set.mem_setOf_eq,
        Set.toFinite_toFinset, Set.coe_toFinset, Set.mem_singleton_iff, and_imp]
      intro hpq hq
      refine ⟨by_contra fun H ↦ ?_, hq⟩
      have : q.1.FiniteHeight := ⟨.inr (by simp [q.1.height_eq_primeHeight, hq])⟩
      replace hpq := Ideal.primeHeight_strict_mono (hpq.lt_of_ne' H)
      exact hp.not_lt (hq ▸ hpq))
  have hf' : hf.toFinset = if p.1.primeHeight = 1 then {p} else ∅ := by
    ext
    split_ifs <;> (simp only [Set.toFinite_toFinset, Set.mem_toFinset, Set.mem_inter_iff,
      Set.mem_singleton_iff, Set.mem_setOf_eq, Finset.mem_singleton, and_iff_left_iff_imp,
      Finset.notMem_empty, iff_false, not_and]; intro h; rwa [h])
  rw [heq, hf']
  split_ifs with hp'
  · simp [Module.length_localizedModule_primeCompl_quotient_prime_eq_of_primeHeight_le
      (p := p) (q := p) (by simp [hp']) (by rfl)]
  · simp
