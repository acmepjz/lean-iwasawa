import Iwasawalib.Algebra.Exact.Basic
import Iwasawalib.Algebra.Exact.KerCokerComp
import Mathlib.RingTheory.Ideal.Height
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

variable {A M N} in
theorem _root_.LinearEquiv.isPseudoNull_iff (f : M ≃ₗ[A] N) :
    IsPseudoNull A M ↔ IsPseudoNull A N := by
  simp_rw [Module.isPseudoNull_iff, f.support_eq]

variable {A M N} in
theorem _root_.LinearEquiv.isPseudoNull (f : M ≃ₗ[A] N) [IsPseudoNull A M] : IsPseudoNull A N :=
  f.isPseudoNull_iff.1 ‹_›

instance isPseudoNull_of_subsingleton [Subsingleton M] : IsPseudoNull A M := by
  simp [isPseudoNull_iff, support_eq_empty]

/-- A module of a ring with Krull dimension `≤ 1` is pseudo-null if and only it is zero. -/
theorem isPseudoNull_iff_of_krullDimLE_one [Ring.KrullDimLE 1 A] :
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
/-- Pseudo-null modules are preserved by short exact sequences.
This is weaker than `isPseudoNull_of_exact`. -/
theorem isPseudoNull_of_exact' (f : M →ₗ[A] N) (g : N →ₗ[A] P)
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
