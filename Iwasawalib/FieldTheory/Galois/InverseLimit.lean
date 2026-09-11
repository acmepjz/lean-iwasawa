/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section

/-!
# `Gal(L/F) ≅ lim Gal(Eₙ/F)` for an increasing exhaustion by normal subextensions

Let `L / F` be Galois and let `E : ℕ → IntermediateField F L` be an increasing sequence of
normal subextensions with `⨆ n, E n = ⊤`.  Then restriction identifies `Gal(L/F)` with the
inverse limit of the `Gal(Eₙ/F)`, as topological groups.

Mathlib has the corresponding statement for the system of *all* finite Galois subextensions
(`InfiniteGalois.continuousMulEquivToLimit`), phrased category-theoretically over
`FiniteGaloisIntermediateField`.  That does not cover an `ℕ`-indexed cofinal system of
possibly infinite normal subextensions, which is the shape in which Iwasawa theory meets it
(`L∞ = ⋃ₙ K∞Lₙ`, blueprint node `X-inf-is-proj-lim`).  The inverse limit is realised here
concretely, as a subgroup of the product `∀ n, Gal(Eₙ/F)` cut out by coherence, so no category
theory is needed.

The `E n` are *not* assumed finite over `F`.

## Main definitions

* `IntermediateField.GalCoherent`, `IntermediateField.galInvLimit`: the inverse limit.
* `IntermediateField.toGalInvLimit`: the restriction homomorphism `Gal(L/F) → lim Gal(Eₙ/F)`.
* `IntermediateField.limAlgEquiv`: its inverse, the automorphism glued from a coherent family.
* `IntermediateField.galContinuousMulEquivInvLimit`: the isomorphism of topological groups.

## Main results

* `IntermediateField.toGalInvLimit_injective`, `IntermediateField.toGalInvLimit_surjective`.
* `IntermediateField.continuous_toGalInvLimit`.
-/

open IntermediateField Topology

namespace IntermediateField

section Limit

variable {F L : Type*} [Field F] [Field L] [Algebra F L] (E : ℕ → IntermediateField F L)

/-- A family of automorphisms of the `E n` is *coherent* if any two of them agree wherever
both are defined. -/
def GalCoherent (s : ∀ n, Gal(↥(E n)/F)) : Prop :=
  ∀ (m n : ℕ) (x : L) (hm : x ∈ E m) (hn : x ∈ E n), (s m ⟨x, hm⟩ : L) = (s n ⟨x, hn⟩ : L)

variable (hE : Monotone E)

include hE

/-- The inverse limit `lim Gal(Eₙ/F)`, as a subgroup of the product. -/
def galInvLimit : Subgroup (∀ n, Gal(↥(E n)/F)) where
  carrier := {s | GalCoherent E s}
  one_mem' := by intro m n x hm hn; rfl
  mul_mem' := by
    rintro s t hs ht m n x hm hn
    have hxt : (t m ⟨x, hm⟩ : L) = (t n ⟨x, hn⟩ : L) := ht m n x hm hn
    have hym : (t m ⟨x, hm⟩ : L) ∈ E m := (t m ⟨x, hm⟩).2
    have hyn : (t m ⟨x, hm⟩ : L) ∈ E n := by rw [hxt]; exact (t n ⟨x, hn⟩).2
    have key : ((s n) ⟨(t m ⟨x, hm⟩ : L), hyn⟩ : L)
        = ((s n) ⟨(t n ⟨x, hn⟩ : L), (t n ⟨x, hn⟩).2⟩ : L) :=
      congrArg _ (congrArg (s n) (Subtype.ext hxt))
    calc ((s * t) m ⟨x, hm⟩ : L) = ((s m) ⟨(t m ⟨x, hm⟩ : L), hym⟩ : L) := rfl
      _ = ((s n) ⟨(t m ⟨x, hm⟩ : L), hyn⟩ : L) := hs m n _ hym hyn
      _ = ((s * t) n ⟨x, hn⟩ : L) := key
  inv_mem' := by
    rintro s hs m n x hm hn
    set a := ((s m)⁻¹ ⟨x, hm⟩ : ↥(E m))
    set b := ((s n)⁻¹ ⟨x, hn⟩ : ↥(E n))
    set k := max m n
    have hak : (a : L) ∈ E k := hE (le_max_left m n) a.2
    have hbk : (b : L) ∈ E k := hE (le_max_right m n) b.2
    have h1 : (s k ⟨(a : L), hak⟩ : L) = x := by
      rw [← hs m k (a : L) a.2 hak]
      show ((s m) ((s m)⁻¹ ⟨x, hm⟩) : L) = x
      simp
    have h2 : (s k ⟨(b : L), hbk⟩ : L) = x := by
      rw [← hs n k (b : L) b.2 hbk]
      show ((s n) ((s n)⁻¹ ⟨x, hn⟩) : L) = x
      simp
    have : (⟨(a : L), hak⟩ : ↥(E k)) = ⟨(b : L), hbk⟩ :=
      (s k).injective (Subtype.ext (h1.trans h2.symm))
    exact congrArg Subtype.val this

/-- Membership in the inverse limit is coherence. -/
theorem mem_galInvLimit {s : ∀ n, Gal(↥(E n)/F)} :
    s ∈ galInvLimit E hE ↔ GalCoherent E s := Iff.rfl

end Limit

/-! ### Restriction into the inverse limit -/

section Restriction

variable {F L : Type*} [Field F] [Field L] [Algebra F L] (E : ℕ → IntermediateField F L)
  (hE : Monotone E)
include hE

/-- If the `E n` increase to `L`, every element of `L` lies in one of them. -/
theorem exists_mem_of_iSup_eq_top (htop : ⨆ n, E n = ⊤) (x : L) : ∃ n, x ∈ E n := by
  have : x ∈ (⨆ n, E n : IntermediateField F L) := by rw [htop]; trivial
  rw [← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed hE.directed_le,
    Set.mem_iUnion] at this
  exact this

variable [∀ n, Normal F ↥(E n)]

/-- Restriction of automorphisms, into the inverse limit. -/
noncomputable def toGalInvLimit : Gal(L/F) →* ↥(galInvLimit E hE) where
  toFun σ := ⟨fun n ↦ AlgEquiv.restrictNormalHom (↥(E n)) σ, by
    intro m n x hm hn
    rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]⟩
  map_one' := Subtype.ext (funext fun n ↦ map_one _)
  map_mul' _ _ := Subtype.ext (funext fun n ↦ map_mul _ _ _)

/-- Restriction acts as the automorphism itself. -/
@[simp]
theorem toGalInvLimit_apply_coe (σ : Gal(L/F)) (n : ℕ) (x : ↥(E n)) :
    ((toGalInvLimit E hE σ).1 n x : L) = σ (x : L) :=
  AlgEquiv.restrictNormalHom_apply (E n) σ x

/-- Restriction to the `E n` determines an automorphism of `L`. -/
theorem toGalInvLimit_injective (htop : ⨆ n, E n = ⊤) :
    Function.Injective (toGalInvLimit E hE) := by
  intro σ τ h
  refine AlgEquiv.ext fun x ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_of_iSup_eq_top E hE htop x
  have := congrArg (fun u : ↥(galInvLimit E hE) ↦ ((u.1 n ⟨x, hn⟩ : ↥(E n)) : L)) h
  simpa using this

end Restriction

/-! ### Gluing a coherent family -/

section Glue

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {E : ℕ → IntermediateField F L}
  {hE : Monotone E} (htop : ⨆ n, E n = ⊤) (s : ↥(galInvLimit E hE))

/-- The automorphism of `L` determined by a coherent family. -/
noncomputable def limFun (x : L) : L :=
  (s.1 (exists_mem_of_iSup_eq_top E hE htop x).choose
    ⟨x, (exists_mem_of_iSup_eq_top E hE htop x).choose_spec⟩ : L)

/-- `IntermediateField.limFun` may be computed with any index. -/
theorem limFun_eq {n : ℕ} {x : L} (hx : x ∈ E n) : limFun htop s x = (s.1 n ⟨x, hx⟩ : L) :=
  s.2 _ n x _ hx

/-- `IntermediateField.limFun` is multiplicative. -/
theorem limFun_mul (x y : L) : limFun htop s (x * y) = limFun htop s x * limFun htop s y := by
  obtain ⟨m, hm⟩ := exists_mem_of_iSup_eq_top E hE htop x
  obtain ⟨n, hn⟩ := exists_mem_of_iSup_eq_top E hE htop y
  have hx : x ∈ E (max m n) := hE (le_max_left m n) hm
  have hy : y ∈ E (max m n) := hE (le_max_right m n) hn
  rw [limFun_eq htop s hx, limFun_eq htop s hy,
    limFun_eq htop s ((E (max m n)).mul_mem hx hy)]
  have h : (⟨x * y, (E (max m n)).mul_mem hx hy⟩ : ↥(E (max m n)))
      = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [h, map_mul]
  rfl

/-- `IntermediateField.limFun` is additive. -/
theorem limFun_add (x y : L) : limFun htop s (x + y) = limFun htop s x + limFun htop s y := by
  obtain ⟨m, hm⟩ := exists_mem_of_iSup_eq_top E hE htop x
  obtain ⟨n, hn⟩ := exists_mem_of_iSup_eq_top E hE htop y
  have hx : x ∈ E (max m n) := hE (le_max_left m n) hm
  have hy : y ∈ E (max m n) := hE (le_max_right m n) hn
  rw [limFun_eq htop s hx, limFun_eq htop s hy,
    limFun_eq htop s ((E (max m n)).add_mem hx hy)]
  have h : (⟨x + y, (E (max m n)).add_mem hx hy⟩ : ↥(E (max m n)))
      = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [h, map_add]
  rfl

/-- `IntermediateField.limFun` fixes `F`. -/
theorem limFun_commutes (r : F) :
    limFun htop s (algebraMap F L r) = algebraMap F L r := by
  rw [limFun_eq htop s ((E 0).algebraMap_mem r)]
  have h : (⟨algebraMap F L r, (E 0).algebraMap_mem r⟩ : ↥(E 0)) = algebraMap F ↥(E 0) r := rfl
  rw [h, AlgEquiv.commutes]
  rfl

/-- `IntermediateField.limFun` of the inverse family inverts it. -/
theorem limFun_leftInverse (x : L) : limFun htop s⁻¹ (limFun htop s x) = x := by
  obtain ⟨n, hx⟩ := exists_mem_of_iSup_eq_top E hE htop x
  rw [limFun_eq htop s hx, limFun_eq htop s⁻¹ (s.1 n ⟨x, hx⟩).2]
  have h : (s⁻¹).1 n = (s.1 n)⁻¹ := rfl
  rw [h]
  have h2 : (⟨(s.1 n ⟨x, hx⟩ : L), (s.1 n ⟨x, hx⟩).2⟩ : ↥(E n)) = s.1 n ⟨x, hx⟩ := rfl
  rw [h2]
  show (((s.1 n)⁻¹ ((s.1 n) ⟨x, hx⟩) : ↥(E n)) : L) = x
  simp

/-- The automorphism of `L` determined by a coherent family. -/
noncomputable def limAlgEquiv : Gal(L/F) where
  toFun := limFun htop s
  invFun := limFun htop s⁻¹
  left_inv := limFun_leftInverse htop s
  right_inv x := by
    have := limFun_leftInverse htop s⁻¹ x
    rwa [inv_inv] at this
  map_mul' := limFun_mul htop s
  map_add' := limFun_add htop s
  commutes' := limFun_commutes htop s

variable [∀ n, Normal F ↥(E n)]

/-- `IntermediateField.limAlgEquiv` is a section of `IntermediateField.toGalInvLimit`. -/
theorem toGalInvLimit_limAlgEquiv : toGalInvLimit E hE (limAlgEquiv htop s) = s := by
  refine Subtype.ext (funext fun n ↦ AlgEquiv.ext fun x ↦ Subtype.ext ?_)
  rw [toGalInvLimit_apply_coe]
  exact limFun_eq htop s x.2

/-- Every coherent family glues. -/
theorem toGalInvLimit_surjective (htop : ⨆ n, E n = ⊤) :
    Function.Surjective (toGalInvLimit E hE) :=
  fun s ↦ ⟨limAlgEquiv htop s, toGalInvLimit_limAlgEquiv htop s⟩

end Glue

/-! ### The isomorphism of topological groups -/

section Topology

variable {F L : Type*} [Field F] [Field L] [Algebra F L] (E : ℕ → IntermediateField F L)
  (hE : Monotone E) [∀ n, IsGalois F ↥(E n)]

/-- Restriction into the inverse limit is continuous. -/
theorem continuous_toGalInvLimit : Continuous (toGalInvLimit E hE) := by
  rw [continuous_induced_rng]
  exact continuous_pi fun n ↦ InfiniteGalois.restrictNormalHom_continuous (E n)

variable [IsGalois F L]

/-- **`Gal(L/F) ≅ lim Gal(Eₙ/F)` as topological groups.** -/
noncomputable def galContinuousMulEquivInvLimit (htop : ⨆ n, E n = ⊤) :
    Gal(L/F) ≃ₜ* ↥(galInvLimit E hE) :=
  letI e : Gal(L/F) ≃ ↥(galInvLimit E hE) :=
    Equiv.ofBijective _ ⟨toGalInvLimit_injective E hE htop, toGalInvLimit_surjective (E := E) (hE := hE) htop⟩
  letI h : Gal(L/F) ≃ₜ ↥(galInvLimit E hE) :=
    (continuous_toGalInvLimit E hE).homeoOfEquivCompactToT2 (f := e)
  { toEquiv := e
    map_mul' := map_mul (toGalInvLimit E hE)
    continuous_toFun := h.continuous_toFun
    continuous_invFun := h.continuous_invFun }

end Topology

end IntermediateField
