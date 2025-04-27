/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Iwasawalib.Algebra.Exact.Basic
import Iwasawalib.Algebra.Exact.KerCokerComp
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Support

/-!

# Pseudo-null modules, pseudo-isomorphisms, and pseudo-isomorphic modules

-/

universe u v w x

variable (A : Type u) [CommRing A]
variable (M : Type v) [AddCommGroup M] [Module A M]
variable (N : Type w) [AddCommGroup N] [Module A N]
variable (P : Type x) [AddCommGroup P] [Module A P]

/-! ## Pseudo-null modules -/

namespace Module

/-- A finitely generated module `M` over a Noetherian ring `A` is called pseudo-null,
if every prime ideals in the support of `M` are of height `≥ 2`.
Equivalently, if `M` localized at `p` equals zero for all prime ideals `p` of height `≤ 1`. -/
@[mk_iff]
class IsPseudoNull : Prop where
  two_le_primeHeight : ∀ p ∈ support A M, 2 ≤ p.1.primeHeight

theorem isPseudoNull_iff_primeHeight_le_one_imp_subsingleton :
    IsPseudoNull A M ↔ ∀ p : PrimeSpectrum A, p.1.primeHeight ≤ 1 →
      Subsingleton (LocalizedModule p.1.primeCompl M) := by
  rw [isPseudoNull_iff]
  congr! 1 with p
  nth_rw 2 [← not_imp_not]
  rw [not_subsingleton_iff_nontrivial, ← Module.mem_support_iff, not_le,
    ← ENat.add_one_le_iff (by simp)]
  rfl

theorem IsPseudoNull.subsingleton_of_primeHeight_le_one [IsPseudoNull A M]
    {p : PrimeSpectrum A} (hp : p.1.primeHeight ≤ 1) :
    Subsingleton (LocalizedModule p.1.primeCompl M) :=
  (isPseudoNull_iff_primeHeight_le_one_imp_subsingleton A M).1 ‹_› p hp

variable {A M N} in
theorem _root_.LinearEquiv.isPseudoNull_iff (f : M ≃ₗ[A] N) :
    IsPseudoNull A M ↔ IsPseudoNull A N := by
  simp_rw [Module.isPseudoNull_iff, f.support_eq]

variable {A M N} in
theorem _root_.LinearEquiv.isPseudoNull (f : M ≃ₗ[A] N) [IsPseudoNull A M] : IsPseudoNull A N :=
  f.isPseudoNull_iff.1 ‹_›

instance isPseudoNull_of_subsingleton [Subsingleton M] : IsPseudoNull A M := by
  simp [isPseudoNull_iff, support_eq_empty]

/-- A module over a ring with Krull dimension `≤ 1` is pseudo-null if and only it is zero. -/
theorem isPseudoNull_iff_subsingleton_of_krullDimLE_one [Ring.KrullDimLE 1 A] :
    IsPseudoNull A M ↔ Subsingleton M := by
  refine ⟨fun H ↦ ?_, fun _ ↦ inferInstance⟩
  rw [← support_eq_empty_iff (R := A)]
  ext p
  rw [Set.mem_empty_iff_false, iff_false]
  intro hp
  have h2 := LE.le.trans p.1.primeHeight_le_ringKrullDim
    (show ringKrullDim A ≤ 1 from Order.KrullDimLE.krullDim_le)
  rw [WithBot.coe_le_one] at h2
  simpa only [Nat.not_ofNat_le_one] using (H.two_le_primeHeight p hp).trans h2

theorem _root_.IsNoetherianRing.exists_nilradical_pow_eq_bot [IsNoetherianRing A] :
    ∃ n, (nilradical A) ^ n = ⊥ := by
  obtain ⟨s, hs⟩ := (isNoetherianRing_iff_ideal_fg A).1 ‹_› (nilradical A)
  rw [← hs]
  classical
  refine Finset.induction_on' (motive := fun t : Finset A ↦ ∃ n, Ideal.span (t : Set A) ^ n = ⊥)
    s ⟨1, by simp⟩ ?_
  rintro a t ha ht - ⟨m, hm⟩
  obtain ⟨n, hn⟩ : ∃ n, Ideal.span {a} ^ n = ⊥ := by
    simp_rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot]
    suffices a ∈ nilradical A from mem_nilradical.1 this
    rw [← hs]
    exact Ideal.span_mono (by simp [ha]) (Ideal.mem_span_singleton_self a)
  use n + m
  rw [Finset.coe_insert, Ideal.span_insert, eq_bot_iff]
  exact Ideal.sup_pow_add_le_pow_sup_pow.trans (by simp [hm, hn])

theorem _root_.IsNoetherianRing.exists_pow_le_of_zeroLocus_eq_singleton [IsNoetherianRing A]
    {I : Ideal A} {p : PrimeSpectrum A} (h : PrimeSpectrum.zeroLocus I = {p}) :
    ∃ n, p.1 ^ n ≤ I := by
  have hrange := PrimeSpectrum.range_comap_of_surjective _ (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker, h] at hrange
  obtain ⟨q, hq⟩ := hrange ▸ Set.mem_singleton p
  have hnil : nilradical (A ⧸ I) = q.1 := by
    rw [PrimeSpectrum.nilradical_eq_iInf]
    refine le_antisymm (iInf_le _ _) (le_iInf fun r ↦ ?_)
    have := Set.mem_singleton_iff.1 (hrange ▸ Set.mem_range_self r)
    rw [← this] at hq
    rw [PrimeSpectrum.comap_injective_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective hq]
  obtain ⟨n, hn⟩ := IsNoetherianRing.exists_nilradical_pow_eq_bot (A ⧸ I)
  use n
  rw [hnil] at hn
  apply_fun Ideal.comap (Ideal.Quotient.mk I) at hn
  rw [← hq, PrimeSpectrum.comap_asIdeal]
  refine (Ideal.le_comap_pow _ _).trans ?_
  rw [hn, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

theorem support_subset_maximalIdeal_iff_exists_pow_le_annihilator
    [IsNoetherianRing A] [IsLocalRing A] [Module.Finite A M] :
    Module.support A M ⊆ {⟨IsLocalRing.maximalIdeal A, inferInstance⟩} ↔
      ∃ n, (IsLocalRing.maximalIdeal A) ^ n ≤ Module.annihilator A M := by
  refine ⟨fun h ↦ ?_, fun ⟨n, hn⟩ p hp ↦ ?_⟩
  · by_cases hM : Subsingleton M
    · simp [Module.annihilator_eq_top_iff.2 inferInstance]
    rw [← support_eq_empty_iff (R := A), ← Ne, ← Set.nonempty_iff_ne_empty] at hM
    rw [hM.subset_singleton_iff, support_eq_zeroLocus] at h
    exact IsNoetherianRing.exists_pow_le_of_zeroLocus_eq_singleton _ h
  have := Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance) <|
    Ideal.IsPrime.le_of_pow_le <| hn.trans (mem_support_iff_of_finite.1 hp)
  simp [this]

theorem isPseudoNull_iff_support_subset_maximalIdeal_of_ringKrullDim_eq_two
    (hd : ringKrullDim A = 2) [IsLocalRing A] :
    IsPseudoNull A M ↔ Module.support A M ⊆ {⟨IsLocalRing.maximalIdeal A, inferInstance⟩} := by
  rw [isPseudoNull_iff, Set.subset_singleton_iff]
  congr! 2 with p _
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : FiniteRingKrullDim A := finiteRingKrullDim_iff_ne_bot_and_top.2
      (by rw [hd]; exact ⟨nofun, nofun⟩)
    have := (Ideal.primeHeight_le_ringKrullDim (I := p.1)).antisymm
      (by simpa [hd] using WithBot.coe_le_coe.2 h)
    ext1
    rwa [Ideal.primeHeight_eq_ringKrullDim_iff] at this
  · simp [h, Option.some.inj (hd ▸ IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim)]

/-- Let `A` be a Noetherian local ring of Krull dimension 2 with finite residue field,
`M` be a finitely generated `A`-module. Then `M` is pseudo-null if and only if the cardinality
of `M` is finite. -/
theorem isPseudoNull_iff_finite_of_ringKrullDim_eq_two (hd : ringKrullDim A = 2)
    [IsNoetherianRing A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)]
    [Module.Finite A M] : IsPseudoNull A M ↔ Finite M := by
  rw [isPseudoNull_iff_support_subset_maximalIdeal_of_ringKrullDim_eq_two _ _ hd,
    support_subset_maximalIdeal_iff_exists_pow_le_annihilator]
  refine ⟨?_, fun _ ↦ ?_⟩
  · let _ := Module.quotientAnnihilator (R := A) (M := M)
    have := Module.Finite.of_restrictScalars_finite A (A ⧸ annihilator A M) M
    rw [← IsLocalRing.finite_quotient_iff]
    intro _
    exact Module.finite_of_finite (A ⧸ annihilator A M)
  obtain ⟨n, h⟩ := IsArtinian.monotone_stabilizes {
    toFun := fun n ↦ ((IsLocalRing.maximalIdeal A) ^ n • ⊤ : Submodule A M)
    monotone' := fun m n h ↦ Submodule.smul_mono_left (Ideal.pow_le_pow_right h) }
  replace h := h (n + 1) (by simp)
  dsimp at h
  rw [pow_succ', mul_smul] at h
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (IsLocalRing.maximalIdeal A) ((IsLocalRing.maximalIdeal A) ^ n • ⊤ : Submodule A M)
    (IsNoetherian.noetherian _) (by apply Eq.le; convert h)
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ (by simp)])
  refine ⟨n, fun x hx ↦ Module.mem_annihilator.2 fun m ↦ ?_⟩
  simpa [hbot] using Submodule.smul_mem_smul hx (Submodule.mem_top : m ∈ _)

variable {A M N} in
/-- Pseudo-null modules are preserved by taking submodules. -/
theorem isPseudoNull_of_injective (f : M →ₗ[A] N) (h : Function.Injective f) [IsPseudoNull A N] :
    IsPseudoNull A M :=
  ⟨fun _ hp ↦ IsPseudoNull.two_le_primeHeight _ (support_subset_of_injective f h hp)⟩

variable {A M N} in
/-- Pseudo-null modules are preserved by taking quotient modules. -/
theorem isPseudoNull_of_surjective (f : M →ₗ[A] N) (h : Function.Surjective f) [IsPseudoNull A M] :
    IsPseudoNull A N :=
  ⟨fun _ hp ↦ IsPseudoNull.two_le_primeHeight _ (support_subset_of_surjective f h hp)⟩

variable {A M N P} in
private theorem isPseudoNull_of_exact' (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g)
    [IsPseudoNull A M] [IsPseudoNull A P] : IsPseudoNull A N := by
  refine ⟨fun _ hp ↦ ?_⟩
  rw [support_of_exact h hf hg, Set.mem_union] at hp
  rcases hp with hp | hp <;> exact IsPseudoNull.two_le_primeHeight _ hp

variable {A M N P} in
/-- If `M`, `P` are pseudo-null, `M → N → P` is exact at `N`, then `N` is also pseudo-null. -/
theorem isPseudoNull_of_exact (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (h : Function.Exact f g) [IsPseudoNull A M] [IsPseudoNull A P] : IsPseudoNull A N :=
  let M' := LinearMap.range f
  let P' := LinearMap.range g
  have : IsPseudoNull A M' := isPseudoNull_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  have : IsPseudoNull A P' := isPseudoNull_of_injective P'.subtype P'.injective_subtype
  isPseudoNull_of_exact' M'.subtype g.rangeRestrict h.linearMap_rangeRestrict
    M'.injective_subtype g.surjective_rangeRestrict

end Module

/-! ## Pseudo-isomorphisms -/

namespace LinearMap

variable {A M N P}
variable (f : M →ₗ[A] N) (g : N →ₗ[A] P)

/-- A linear map between two finitely generated modules over a Noetherian ring is called a
pseudo-isomorphism if its kernel and cokernel are pseudo-null. -/
@[mk_iff]
structure IsPseudoIsomorphism : Prop where
  isPseudoNull_ker : Module.IsPseudoNull A (ker f)
  isPseudoNull_coker : Module.IsPseudoNull A (N ⧸ range f)

theorem isPseudoIsomorphism_iff_primeHeight_le_one_imp_bijective :
    f.IsPseudoIsomorphism ↔ ∀ p : PrimeSpectrum A, p.1.primeHeight ≤ 1 →
      Function.Bijective (LocalizedModule.map p.1.primeCompl f) := by
  simp_rw [isPseudoIsomorphism_iff, Module.isPseudoNull_iff_primeHeight_le_one_imp_subsingleton,
    ← forall_and, Function.Bijective]
  congr! 3 with p hp
  · have H : Function.Exact (LocalizedModule.map p.1.primeCompl (ker f).subtype)
        (LocalizedModule.map p.1.primeCompl f) :=
      LocalizedModule.map_exact p.1.primeCompl _ _ (f.exact_subtype_ker_map)
    rw [← (LocalizedModule.map p.1.primeCompl f).exact_zero_iff_injective
      (LocalizedModule p.asIdeal.primeCompl ↥(ker f))]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · convert H
      exact Subsingleton.elim _ _
    · refine ⟨fun x y ↦ LocalizedModule.map_injective p.1.primeCompl _ (ker f).injective_subtype ?_⟩
      rw [LinearMap.exact_iff] at H h
      rw [H] at h
      have hx := LinearMap.mem_range_self
        ((LocalizedModule.map p.asIdeal.primeCompl) (ker f).subtype)
      simp only [h, range_zero, Submodule.mem_bot] at hx
      simp only [hx]
  · have H : Function.Exact (LocalizedModule.map p.1.primeCompl f)
        (LocalizedModule.map p.1.primeCompl (range f).mkQ) :=
      LocalizedModule.map_exact p.1.primeCompl _ _ (f.exact_map_mkQ_range)
    rw [← (LocalizedModule.map p.1.primeCompl f).exact_zero_iff_surjective
      (LocalizedModule p.asIdeal.primeCompl (N ⧸ range f))]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · convert H
    · refine ⟨fun x y ↦ ?_⟩
      have hs := LocalizedModule.map_surjective p.1.primeCompl _ (range f).mkQ_surjective
      obtain ⟨x, rfl⟩ := hs x
      obtain ⟨y, rfl⟩ := hs y
      rw [LinearMap.exact_iff] at H h
      rw [← h, LinearMap.ker_zero, LinearMap.ker_eq_top] at H
      simp [H]

variable {f} in
theorem IsPseudoIsomorphism.bijective_of_primeHeight_le_one (H : f.IsPseudoIsomorphism)
    {p : PrimeSpectrum A} (hp : p.1.primeHeight ≤ 1) :
    Function.Bijective (LocalizedModule.map p.1.primeCompl f) :=
  f.isPseudoIsomorphism_iff_primeHeight_le_one_imp_bijective.1 H p hp

theorem isPseudoIsomorphism_iff_of_injective (h : Function.Injective f) :
    f.IsPseudoIsomorphism ↔ Module.IsPseudoNull A (N ⧸ range f) := by
  rw [isPseudoIsomorphism_iff, and_iff_right_iff_imp]
  rintro -
  rw [ker_eq_bot_of_injective h]
  infer_instance

theorem isPseudoIsomorphism_iff_of_surjective (h : Function.Surjective f) :
    f.IsPseudoIsomorphism ↔ Module.IsPseudoNull A (ker f) := by
  rw [isPseudoIsomorphism_iff, and_iff_left_iff_imp]
  rintro -
  suffices Subsingleton (N ⧸ range f) by infer_instance
  rw [Submodule.subsingleton_quotient_iff_eq_top]
  exact range_eq_top_of_surjective f h

theorem isPseudoIsomorphism_of_bijective (h : Function.Bijective f) : f.IsPseudoIsomorphism := by
  rw [f.isPseudoIsomorphism_iff_of_surjective h.surjective, ker_eq_bot_of_injective h.injective]
  infer_instance

theorem _root_.LinearEquiv.isPseudoIsomorphism (f : M ≃ₗ[A] N) :
    f.toLinearMap.IsPseudoIsomorphism :=
  isPseudoIsomorphism_of_bijective f.toLinearMap f.bijective

theorem isPseudoIsomorphism_id : (id : M →ₗ[A] M).IsPseudoIsomorphism :=
  isPseudoIsomorphism_of_bijective _ Function.bijective_id

theorem isPseudoIsomorphism_zero_iff :
    (0 : M →ₗ[A] N).IsPseudoIsomorphism ↔ Module.IsPseudoNull A M ∧ Module.IsPseudoNull A N := by
  rw [isPseudoIsomorphism_iff]
  congr! 1
  · rw [ker_zero]
    exact Submodule.topEquiv.isPseudoNull_iff
  · refine (Submodule.quotEquivOfEqBot _ ?_).isPseudoNull_iff
    exact range_zero

theorem isPseudoIsomorphism_of_isPseudoNull [Module.IsPseudoNull A M] [Module.IsPseudoNull A N] :
    f.IsPseudoIsomorphism :=
  ⟨Module.isPseudoNull_of_injective _ (ker f).injective_subtype,
    Module.isPseudoNull_of_surjective _ (range f).mkQ_surjective⟩

/-- If `M` is pseudo-null, then `M → N` is a pseudo-isomorphism if and only if
`N` is pseudo-null. -/
theorem isPseudoIsomorphism_iff_of_isPseudoNull_left [Module.IsPseudoNull A M] :
    f.IsPseudoIsomorphism ↔ Module.IsPseudoNull A N :=
  ⟨fun ⟨_, _⟩ ↦ Module.isPseudoNull_of_exact _ _ f.exact_map_mkQ_range,
    fun _ ↦ f.isPseudoIsomorphism_of_isPseudoNull⟩

/-- If `N` is pseudo-null, then `M → N` is a pseudo-isomorphism if and only if
`M` is pseudo-null. -/
theorem isPseudoIsomorphism_iff_of_isPseudoNull_right [Module.IsPseudoNull A N] :
    f.IsPseudoIsomorphism ↔ Module.IsPseudoNull A M :=
  ⟨fun ⟨_, _⟩ ↦ Module.isPseudoNull_of_exact _ _ f.exact_subtype_ker_map,
    fun _ ↦ f.isPseudoIsomorphism_of_isPseudoNull⟩

variable {f g} in
/-- Composition of two pseudo-isomorphisms is a pseudo-isomorphism. -/
theorem IsPseudoIsomorphism.comp (hg : g.IsPseudoIsomorphism) (hf : f.IsPseudoIsomorphism) :
    (g ∘ₗ f).IsPseudoIsomorphism :=
  have := hf.isPseudoNull_ker
  have := hf.isPseudoNull_coker
  have := hg.isPseudoNull_ker
  have := hg.isPseudoNull_coker
  ⟨Module.isPseudoNull_of_exact _ _ (Module.KerCokerComp.exact_f₁_f₂ f g),
    Module.isPseudoNull_of_exact _ _ (Module.KerCokerComp.exact_f₄_f₅ f g)⟩

end LinearMap

/-! ## Pseudo-isomorphic modules -/

namespace Module

/-- Two finitely generated modules `M, N` over a Noetherian ring `A` is called pseudo-isomorphic,
if there exists a linear map `f : M →ₗ[A] N` which is a pseudo-isomorphism.

WARNING: pseudo-isomorphic is not symmetric in general. -/
@[mk_iff]
structure IsPseudoIsomorphic : Prop where
  exists_isPseudoIsomorphism : ∃ f : M →ₗ[A] N, f.IsPseudoIsomorphism

@[inherit_doc]
notation:50 M " ∼ₚᵢₛ[" A "] " N:50 => IsPseudoIsomorphic A M N

/-- Pseudo-isomorphic is reflexive. -/
theorem IsPseudoIsomorphic.refl : M ∼ₚᵢₛ[A] M :=
  ⟨⟨_, LinearMap.isPseudoIsomorphism_id⟩⟩

theorem isPseudoIsomorphic_iff_of_isPseudoNull_left [IsPseudoNull A M] :
    M ∼ₚᵢₛ[A] N ↔ IsPseudoNull A N := by
  simp [isPseudoIsomorphic_iff, LinearMap.isPseudoIsomorphism_iff_of_isPseudoNull_left]

theorem isPseudoIsomorphic_iff_of_isPseudoNull_right [IsPseudoNull A N] :
    M ∼ₚᵢₛ[A] N ↔ IsPseudoNull A M := by
  simp [isPseudoIsomorphic_iff, LinearMap.isPseudoIsomorphism_iff_of_isPseudoNull_right]

variable {A M N P} in
/-- Pseudo-isomorphic is transitive. -/
@[trans]
theorem IsPseudoIsomorphic.trans (h1 : M ∼ₚᵢₛ[A] N) (h2 : N ∼ₚᵢₛ[A] P) : M ∼ₚᵢₛ[A] P := by
  obtain ⟨_, h1⟩ := h1
  obtain ⟨_, h2⟩ := h2
  exact ⟨_, h2.comp h1⟩

end Module
