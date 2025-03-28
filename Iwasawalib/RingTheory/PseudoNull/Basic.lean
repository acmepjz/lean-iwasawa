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
/-- Pseudo-null modules are preserved by short exact sequences. -/
theorem isPseudoNull_of_exact (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g)
    [IsPseudoNull A M] [IsPseudoNull A P] : IsPseudoNull A N := by
  refine ⟨fun _ hp ↦ ?_⟩
  rw [support_of_exact h hf hg, Set.mem_union] at hp
  rcases hp with hp | hp <;> exact IsPseudoNull.two_le_primeHeight _ hp

end Module

/-! ## Pseudo-isomorphisms -/

namespace LinearMap

variable {A M N}
variable (f : M →ₗ[A] N)

/-- A linear map between two finitely generated modules over a Noetherian ring is called a
pseudo-isomorphism if its kernel and cokernel are pseudo-null. -/
@[mk_iff]
class IsPseudoIsomorphism : Prop where
  isPseudoNull_ker : Module.IsPseudoNull A (ker f)
  isPseudoNull_coker : Module.IsPseudoNull A (N ⧸ range f)

theorem isPseudoIsomorphism_of_bijective (h : Function.Bijective f) : f.IsPseudoIsomorphism := by
  constructor
  · rw [ker_eq_bot_of_injective h.injective]
    infer_instance
  · suffices Subsingleton (N ⧸ range f) by infer_instance
    rw [Submodule.subsingleton_quotient_iff_eq_top]
    exact range_eq_top_of_surjective f h.surjective

end LinearMap

/-! ## Pseudo-isomorphic modules -/

namespace Module

/-- Two finitely generated modules `M, N` over a Noetherian ring `A` is called pseudo-isomorphic,
if there exists a linear map `f : M →ₗ[A] N` which is a pseudo-isomorphism.

WARNING: pseudo-isomorphic is not symmetric in general. -/
@[mk_iff]
class IsPseudoIsomorphic : Prop where
  exists_isPseudoIsomorphism : ∃ f : M →ₗ[A] N, f.IsPseudoIsomorphism

@[inherit_doc]
notation:50 M " ∼ₚᵢₛ[" A "] " N:50 => IsPseudoIsomorphic A M N

instance isPseudoIsomorphic_refl : M ∼ₚᵢₛ[A] M :=
  ⟨⟨LinearMap.id, LinearMap.isPseudoIsomorphism_of_bijective _ Function.bijective_id⟩⟩

theorem isPseudoIsomorphic_iff_of_isPseudoNull_left [IsPseudoNull A M] :
    M ∼ₚᵢₛ[A] N ↔ IsPseudoNull A N := by
  sorry

theorem isPseudoIsomorphic_iff_of_isPseudoNull_right [IsPseudoNull A N] :
    M ∼ₚᵢₛ[A] N ↔ IsPseudoNull A M := by
  sorry

end Module
