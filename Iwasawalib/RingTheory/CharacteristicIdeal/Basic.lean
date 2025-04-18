import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Ideal.AssociatedPrime
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Support

/-!

# Characteristic ideal of a finitely generated module over a Noetherian ring

-/

universe u v

/-! ### Results should be PR into mathlib -/

section IsNoetherianRing

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M] {n : ℕ} {N : Submodule A M}

section

omit [Module.Finite A M]

/-- A `Prop` asserting that two submodules `N₁, N₂` satisfy `N₁ ≤ N₂` and
`N₂ / N₁` is isomorphic to `A / p` for some prime ideal `p` of `A`. -/
def Submodule.IsQuotientEquivQuotientPrime (N₁ N₂ : Submodule A M) :=
  ∃ (h : N₁ ≤ N₂) (p : PrimeSpectrum A),
    Nonempty ((↥N₂ ⧸ LinearMap.range (Submodule.inclusion h)) ≃ₗ[A] A ⧸ p.1)

private theorem aux (h : N ≠ ⊤) :
    ∃ (p : PrimeSpectrum A) (f : A ⧸ p.1 →ₗ[A] M ⧸ N), Function.Injective f := by
  have := Submodule.Quotient.nontrivial_of_lt_top _ h.lt_top
  have H := associatedPrimes.nonempty A (M ⧸ N)
  have hprime := (AssociatePrimes.mem_iff.1 H.some_mem).1
  obtain ⟨a, ha⟩ := (AssociatePrimes.mem_iff.1 H.some_mem).2
  exact ⟨⟨_, hprime⟩, Submodule.liftQ _ _ ha.le,
    LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot' _ _ ha)⟩

private noncomputable def auxP (h : N ≠ ⊤) : PrimeSpectrum A := (aux h).choose

private noncomputable def auxLinearMap (h : N ≠ ⊤) :
    A ⧸ (auxP h).1 →ₗ[A] M ⧸ N := (aux h).choose_spec.choose

private theorem auxLinearMap_injective (h : N ≠ ⊤) : Function.Injective (auxLinearMap h) :=
  (aux h).choose_spec.choose_spec

private noncomputable def auxSeq
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] : ℕ → Submodule A M
  | 0 => ⊥
  | n + 1 =>
    open scoped Classical in
    if h : auxSeq A M n = ⊤ then
      ⊤
    else
      (LinearMap.range (auxLinearMap h)).comap (auxSeq A M n).mkQ

variable (A M) in
private theorem auxSeq_zero : auxSeq A M 0 = ⊥ := rfl

private theorem auxSeq_succ_of_eq_top (h : auxSeq A M n = ⊤) : auxSeq A M (n + 1) = ⊤ := by
  simp only [auxSeq, dif_pos h]

private theorem auxSeq_succ_of_ne_top (h : auxSeq A M n ≠ ⊤) :
    auxSeq A M (n + 1) = (LinearMap.range (auxLinearMap h)).comap (auxSeq A M n).mkQ := by
  simp only [auxSeq, dif_neg h]

private theorem lt_auxSeq_succ_of_ne_top (h : auxSeq A M n ≠ ⊤) :
    auxSeq A M n < auxSeq A M (n + 1) := by
  rw [auxSeq_succ_of_ne_top h]
  nth_rw 1 [← (auxSeq A M n).ker_mkQ]
  rw [LinearMap.ker, Submodule.comap_lt_comap_iff_of_surjective (auxSeq A M n).mkQ_surjective,
    bot_lt_iff_ne_bot]
  by_contra! H
  rw [LinearMap.range_eq_bot] at H
  have : Subsingleton (A ⧸ (auxP h).1) := subsingleton_iff.2 fun x y ↦
    auxLinearMap_injective h (by simp [H])
  exact false_of_nontrivial_of_subsingleton (A ⧸ (auxP h).1)

variable (A M) in
private theorem monotone_auxSeq : Monotone (auxSeq A M) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  by_cases h : auxSeq A M n = ⊤
  · simp [auxSeq_succ_of_eq_top h]
  exact (lt_auxSeq_succ_of_ne_top h).le

private theorem auxSeq_eq_auxSeq_succ_iff : auxSeq A M n = auxSeq A M (n + 1) ↔ auxSeq A M n = ⊤ :=
  ⟨not_imp_not.1 fun h ↦ (lt_auxSeq_succ_of_ne_top h).ne,
    fun h ↦ h.trans (auxSeq_succ_of_eq_top h).symm⟩

namespace Submodule

variable {R M M₁ : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid M₁]
  [Module R M] [Module R M₁] (q : Submodule R M₁) (f : M →ₗ[R] M₁)

-- TODO:
def comapRestrict : ↥(q.comap f) →ₗ[R] ↥q :=
  f.restrict fun x hx ↦ by simpa only [mem_comap] using hx

@[simp]
theorem comapRestrict_coe_apply (x : q.comap f) : (q.comapRestrict f) x = f x := by
  simp [comapRestrict]

theorem comapRestrict_surjective_of_surjective (hf : Function.Surjective f) :
    Function.Surjective (q.comapRestrict f) := fun y ↦ by
  obtain ⟨x, hx⟩ := hf y
  use ⟨x, by rw [mem_comap, hx]; exact y.2⟩
  apply_fun _ using Subtype.val_injective
  simp [hx]

end Submodule

private theorem isQuotientEquivQuotientPrime_auxSeq_of_ne_top (h : auxSeq A M n ≠ ⊤) :
    (auxSeq A M n).IsQuotientEquivQuotientPrime (auxSeq A M (n + 1)) := by
  rw [auxSeq_succ_of_ne_top h]
  have hle : auxSeq A M n ≤ (LinearMap.range (auxLinearMap h)).comap (auxSeq A M n).mkQ := by
    nth_rw 1 [← (auxSeq A M n).ker_mkQ]
    exact LinearMap.ker_le_comap _
  refine ⟨hle, auxP h, ⟨?_ ≪≫ₗ (LinearEquiv.ofInjective _ (auxLinearMap_injective h)).symm⟩⟩
  refine (Submodule.quotEquivOfEq _ _ ?_) ≪≫ₗ
    ((LinearMap.range (auxLinearMap h)).comapRestrict (auxSeq A M n).mkQ
      |>.quotKerEquivOfSurjective ((LinearMap.range (auxLinearMap h))
        |>.comapRestrict_surjective_of_surjective _ (auxSeq A M n).mkQ_surjective))
  rw [Submodule.comapRestrict, LinearMap.ker_restrict, Submodule.ker_mkQ]
  ext ⟨x, _⟩
  simp only [LinearMap.mem_range, Subtype.exists, Submodule.mem_comap, Submodule.subtype_apply]
  refine ⟨fun ⟨a, h1, h2⟩ ↦ ?_, fun h2 ↦ ⟨x, h2, rfl⟩⟩
  rwa [← show a = x from congr($(h2).1)]

end

variable (A M)

/-- If `A` is a Noetherian ring and `M` is a finitely generated `A`-module, then there exists
a chain of submodules `0 = M₀ ≤ M₁ ≤ M₂ ≤ ... ≤ Mₙ = M` of `M`, such that for each `0 ≤ i < n`,
`Mᵢ₊1 / Mᵢ` is isomorphic to `A / pᵢ` for some prime ideal `pᵢ` of `A`. -/
@[stacks 00L0]
theorem IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime :
    ∃ s : RelSeries (Submodule.IsQuotientEquivQuotientPrime (A := A) (M := M)),
      s.head = ⊥ ∧ s.last = ⊤ := by
  have H : ∃ n : ℕ, auxSeq A M n = ⊤ := by
    obtain ⟨n, h⟩ := monotone_stabilizes_iff_noetherian.2 (inferInstanceAs (IsNoetherian A M))
      ⟨_, monotone_auxSeq A M⟩
    exact ⟨n, auxSeq_eq_auxSeq_succ_iff.1 (h (n + 1) n.lt_add_one.le)⟩
  classical exact ⟨⟨Nat.find H, fun ⟨n, _⟩ ↦ auxSeq A M n,
    fun ⟨n, h⟩ ↦ isQuotientEquivQuotientPrime_auxSeq_of_ne_top (Nat.find_min H h)⟩,
      auxSeq_zero A M, Nat.find_spec H⟩

/-- If a property on finitely generated modules over a Noetherian ring satisfies that:

- it holds for zero module (it's formalized as it holds for any module which is subsingleton),
- it holds for `A ⧸ p` for every prime ideal `p` of `A` (to avoid universe problem,
  it's formalized as it holds for any module isomorphic to `A ⧸ p`),
- it is stable by short exact sequences,

then the property holds for every finitely generated modules.

NOTE: This should be the induction principle for `M`, but due to the bug
https://github.com/leanprover/lean4/issues/4246
currently it is induction for `Module.Finite A M`. -/
@[elab_as_elim]
theorem IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
    ⦃M : Type v⦄ [AddCommGroup M] [Module A M] (_ : Module.Finite A M)
    {motive : (N : Type v) → [AddCommGroup N] → [Module A N] → [Module.Finite A N] → Prop}
    (subsingleton : (N : Type v) → [AddCommGroup N] → [Module A N] → [Module.Finite A N] →
      [Subsingleton N] → motive N)
    (quotient : (N : Type v) → [AddCommGroup N] → [Module A N] → [Module.Finite A N] →
      (p : PrimeSpectrum A) → (N ≃ₗ[A] A ⧸ p.1) → motive N)
    (exact : (N₁ : Type v) → [AddCommGroup N₁] → [Module A N₁] → [Module.Finite A N₁] →
      (N₂ : Type v) → [AddCommGroup N₂] → [Module A N₂] → [Module.Finite A N₂] →
      (N₃ : Type v) → [AddCommGroup N₃] → [Module A N₃] → [Module.Finite A N₃] →
      (f : N₁ →ₗ[A] N₂) → (g : N₂ →ₗ[A] N₃) →
      Function.Injective f → Function.Surjective g → Function.Exact f g →
      motive N₁ → motive N₃ → motive N₂) : motive M := by
  have equiv (N₁ : Type v) [AddCommGroup N₁] [Module A N₁] [Module.Finite A N₁]
      (N₂ : Type v) [AddCommGroup N₂] [Module A N₂] [Module.Finite A N₂]
      (f : N₁ ≃ₗ[A] N₂) (h : motive N₁) : motive N₂ :=
    exact N₁ N₂ PUnit.{v + 1} f 0 f.injective (Function.surjective_to_subsingleton _)
      ((f.exact_zero_iff_surjective _).2 f.surjective) h (subsingleton _)
  obtain ⟨s, hs1, hs2⟩ := IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime A M
  suffices H : ∀ n, (h : n < s.length + 1) → motive (s ⟨n, h⟩) by
    replace H : motive s.last := H s.length s.length.lt_add_one
    rw [hs2] at H
    exact equiv _ _ Submodule.topEquiv H
  intro n h
  induction n with
  | zero =>
    change motive s.head
    rw [hs1]
    exact subsingleton _
  | succ n ih =>
    specialize ih (n.lt_add_one.trans h)
    obtain ⟨hle, p, ⟨f⟩⟩ := s.step ⟨n, (add_lt_add_iff_right _).1 h⟩
    replace ih := equiv _ _ (LinearEquiv.ofInjective (Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)) ih
    exact exact _ _ _ (LinearMap.range (Submodule.inclusion hle)).subtype
      (LinearMap.range (Submodule.inclusion hle)).mkQ
      (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ (LinearMap.range (Submodule.inclusion hle))) ih (quotient _ p f)

/-- If `0 → M → M' → M''` is an exact sequence, then the set of associated primes of `M'` is
contained in the union of those of `M` and `M''`. -/
@[stacks 02M3 "second part"]
theorem associatedPrimes.subset_union_of_exact
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {M' : Type*} [AddCommGroup M'] [Module R M'] {M'' : Type*} [AddCommGroup M''] [Module R M'']
    (f : M →ₗ[R] M') (g : M' →ₗ[R] M'') (hf : Function.Injective f) (hfg : Function.Exact f g) :
    associatedPrimes R M' ⊆ associatedPrimes R M ∪ associatedPrimes R M'' := by
  rintro p ⟨_, x, hx⟩
  by_cases h : ∃ a ∈ p.primeCompl, ∃ y : M, f y = a • x
  · obtain ⟨a, ha, y, h⟩ := h
    refine Or.inl ⟨‹_›, y, le_antisymm (fun b hb ↦ ?_) (fun b hb ↦ ?_)⟩
    · rw [hx] at hb
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hb ⊢
      apply_fun _ using hf
      rw [map_smul, map_zero, h, smul_comm, hb, smul_zero]
    · rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hb
      apply_fun f at hb
      rw [map_smul, map_zero, h, ← mul_smul, ← LinearMap.toSpanSingleton_apply,
        ← LinearMap.mem_ker, ← hx] at hb
      contrapose! hb
      exact p.primeCompl.mul_mem hb ha
  · push_neg at h
    refine Or.inr ⟨‹_›, g x, le_antisymm (fun b hb ↦ ?_) (fun b hb ↦ ?_)⟩
    · rw [hx] at hb
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hb ⊢
      rw [← map_smul, hb, map_zero]
    · rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul, ← LinearMap.mem_ker,
        hfg.linearMap_ker_eq] at hb
      obtain ⟨y, hy⟩ := hb
      by_contra! H
      exact h b H y hy

/-- The set of associated primes of the product of two modules is equal to
the union of those of the two modules. -/
@[stacks 02M3 "third part"]
theorem associatedPrimes.prod
    (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (M' : Type*) [AddCommGroup M'] [Module R M'] :
    associatedPrimes R (M × M') = associatedPrimes R M ∪ associatedPrimes R M' :=
  (subset_union_of_exact (.inl R M M') (.snd R M M') LinearMap.inl_injective .inl_snd).antisymm
    (Set.union_subset_iff.2 ⟨subset_of_injective (.inl R M M') LinearMap.inl_injective,
      subset_of_injective (.inr R M M') LinearMap.inr_injective⟩)

/-- There are only finitely many associated primes of a finitely generated module
over a Noetherian ring. -/
@[stacks 00LC]
theorem associatedPrimes.finite : (associatedPrimes A M).Finite := by
  induction ‹Module.Finite A M› using
    IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A with
  | subsingleton N => simp [associatedPrimes.eq_empty_of_subsingleton]
  | quotient N p f =>
    have := associatedPrimes.eq_singleton_of_isPrimary p.2.isPrimary
    simp [LinearEquiv.AssociatedPrimes.eq f, this]
  | exact N₁ N₂ N₃ f g hf _ hfg h₁ h₃ =>
    exact (h₁.union h₃).subset (associatedPrimes.subset_union_of_exact f g hf hfg)

end IsNoetherianRing

theorem Module.IsTorsion.not_disjoint_nonZeroDivisors_of_mem_support
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (H : Module.IsTorsion A M) :
    ∀ p ∈ Module.support A M, ¬Disjoint (p.1 : Set A) (nonZeroDivisors A : Set A) := by
  intro p
  contrapose!
  rw [Module.not_mem_support_iff, LocalizedModule.subsingleton_iff,
    ← Set.subset_compl_iff_disjoint_left]
  intro h x
  obtain ⟨t, ht⟩ := @H x
  exact ⟨t.1, h t.2, ht⟩

theorem Module.IsTorsion.one_le_primeHeight_of_mem_support
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (H : Module.IsTorsion A M) : ∀ p ∈ Module.support A M, 1 ≤ p.1.primeHeight := by
  intro p hp
  replace H := H.not_disjoint_nonZeroDivisors_of_mem_support p hp
  contrapose! H
  rw [ENat.lt_one_iff_eq_zero, Ideal.primeHeight_eq_zero_iff] at H
  exact Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes H

theorem Module.isTorsion_iff_subsingleton_localizedModule_nonZeroDivisors
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] :
    Module.IsTorsion A M ↔ Subsingleton (LocalizedModule (nonZeroDivisors A) M) := by
  simp only [IsTorsion, Subtype.exists, Submonoid.mk_smul, exists_prop,
    LocalizedModule.subsingleton_iff]

alias ⟨Module.IsTorsion.subsingleton_localizedModule_nonZeroDivisors, _⟩ :=
  Module.isTorsion_iff_subsingleton_localizedModule_nonZeroDivisors

theorem Module.IsTorsion.injective
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {M' : Type*} [AddCommGroup M'] [Module A M'] (H : Module.IsTorsion A M')
    {f : M →ₗ[A] M'} (hf : Function.Injective f) : Module.IsTorsion A M := fun x ↦ by
  obtain ⟨a, ha⟩ := @H (f x)
  exact ⟨a, hf (by rwa [map_zero, LinearMap.map_smul_of_tower])⟩

theorem Module.IsTorsion.surjective
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {M' : Type*} [AddCommGroup M'] [Module A M'] (H : Module.IsTorsion A M)
    {f : M →ₗ[A] M'} (hf : Function.Surjective f) : Module.IsTorsion A M' := fun x ↦ by
  obtain ⟨y, rfl⟩ := hf x
  obtain ⟨a, ha⟩ := @H y
  exact ⟨a, by rw [← LinearMap.map_smul_of_tower, ha, map_zero]⟩

theorem LinearEquiv.isTorsion
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {M' : Type*} [AddCommGroup M'] [Module A M']
    (f : M ≃ₗ[A] M') : Module.IsTorsion A M ↔ Module.IsTorsion A M' :=
  ⟨fun H ↦ H.surjective f.surjective, fun H ↦ H.injective f.injective⟩

theorem Function.Exact.subsingleton
    {M N P : Type*} {f : M → N} {g : N → P} [Zero P]
    (H : Function.Exact f g) [Subsingleton M] [Subsingleton P] : Subsingleton N where
  allEq x y := by
    simp_rw [Function.Exact, Subsingleton.elim _ (0 : P), Set.mem_range, true_iff] at H
    obtain ⟨a, ha⟩ := H x
    obtain ⟨b, hb⟩ := H y
    rw [← ha, ← hb, Subsingleton.elim a b]

theorem Module.IsTorsion.exact
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {M' : Type*} [AddCommGroup M'] [Module A M'] {M'' : Type*} [AddCommGroup M''] [Module A M'']
    (h1 : Module.IsTorsion A M) (h2 : Module.IsTorsion A M'')
    (f : M →ₗ[A] M') (g : M' →ₗ[A] M'') (hfg : Function.Exact f g) : Module.IsTorsion A M' := by
  rw [Module.isTorsion_iff_subsingleton_localizedModule_nonZeroDivisors] at h1 h2 ⊢
  exact (LocalizedModule.map_exact (nonZeroDivisors A) f g hfg).subsingleton

theorem Module.IsTorsion.prod
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {M'' : Type*} [AddCommGroup M''] [Module A M'']
    (h1 : Module.IsTorsion A M) (h2 : Module.IsTorsion A M'') : Module.IsTorsion A (M × M'') :=
  h1.exact h2 (.inl A M M'') (.snd A M M'') .inl_snd

/-! ### Actual contents of the file -/

@[simp]
theorem Module.support_self (A : Type u) [CommRing A] : Module.support A A = Set.univ := by
  nontriviality A
  ext p
  simp_rw [Set.mem_univ, iff_true, mem_support_iff]
  by_contra! h
  rw [not_nontrivial_iff_subsingleton, LocalizedModule.subsingleton_iff] at h
  specialize h 1
  simp_rw [smul_eq_mul, mul_one, exists_eq_right] at h
  change 0 ∉ p.1 at h
  exact h (zero_mem p.1)

theorem Ring.support_quotient {A : Type u} [CommRing A] (I : Ideal A) :
    Module.support A (A ⧸ I) = PrimeSpectrum.zeroLocus I := by
  have : I = I • ⊤ := by simp
  have := Module.support_quotient (M := A) I
  rw [Module.support_self, Set.univ_inter] at this
  convert this

/-- There are only finitely many height one primes contained in the support of a
finitely generated torsion module over a Noetherian ring. -/
theorem Module.IsTorsion.finite_primeHeight_one_support
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
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
    {A : Type u} [CommRing A] {p q : PrimeSpectrum A}
    (hp : p.1.primeHeight ≠ ⊤) (hq : p.1.primeHeight ≤ q.1.primeHeight) :
    Module.length (Localization p.1.primeCompl) (LocalizedModule p.1.primeCompl (A ⧸ q.1)) =
      if p = q then 1 else 0 := by
  have : p.1.FiniteHeight := ⟨.inr (by simpa only [p.1.height_eq_primeHeight])⟩
  by_cases hpq : p ≠ q
  · rw [if_neg hpq, Module.length_eq_zero_iff]
    rw [← Module.not_mem_support_iff, Ring.support_quotient,
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
    {A : Type u} [CommRing A] {p q : PrimeSpectrum A}
    (hp : p.1.primeHeight ≠ ⊤) (hq : p.1.primeHeight ≤ q.1.primeHeight) :
    IsFiniteLength (Localization p.1.primeCompl) (LocalizedModule p.1.primeCompl (A ⧸ q.1)) := by
  rw [← Module.length_ne_top_iff,
    Module.length_localizedModule_primeCompl_quotient_prime_eq_of_primeHeight_le hp hq]
  split_ifs <;> simp

/-- Let `M` be a finitely generated torsion module over a Noetherian ring `A`. For any prime ideal
`p` of `A` of height `≤ 1`, the `Mₚ` is of finite length over `Aₚ`. -/
theorem Module.IsTorsion.isFiniteLength_localizedModule_of_primeHeight_le_one
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (H : Module.IsTorsion A M)
    (p : PrimeSpectrum A) (hp : p.1.primeHeight ≤ 1) :
    IsFiniteLength (Localization p.1.primeCompl) (LocalizedModule p.1.primeCompl M) := by
  by_cases hmem : p ∉ Module.support A M
  · rw [Module.not_mem_support_iff] at hmem
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
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M] : Ideal A :=
  ∏ᶠ (p : PrimeSpectrum A), if p.1.primeHeight = 1 then
    p.1 ^ (Module.length (Localization p.1.primeCompl) (LocalizedModule p.1.primeCompl M)).toNat
  else
    1

theorem Module.charIdeal_eq_prod_of_support_subset
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
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
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M] [Subsingleton M] :
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
    {A : Type u} [CommRing A] (p : PrimeSpectrum A) (hp : 1 ≤ p.1.primeHeight) :
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
      Finset.not_mem_empty, iff_false, not_and]; intro h; rwa [h])
  rw [heq, hf']
  split_ifs with hp'
  · simp [Module.length_localizedModule_primeCompl_quotient_prime_eq_of_primeHeight_le
      (p := p) (q := p) (by simp [hp']) (by rfl)]
  · simp
