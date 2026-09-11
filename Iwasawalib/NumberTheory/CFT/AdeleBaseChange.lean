/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.FiniteAdeleBaseChange
public import Iwasawalib.NumberTheory.CFT.InfiniteAdeleBaseChange

@[expose] public section

/-!
# Base change of the adele ring, the idele group and the idele class group

Combining `NumberField.InfiniteAdeleRing.baseChange` with
`IsDedekindDomain.FiniteAdeleRing.baseChange` gives the base change map
`𝔸_K →+* 𝔸_L` for an extension of number fields `L / K`, hence base change maps on ideles
and on idele classes.  The image of each is fixed by `Gal(L/K)`; this is the easy inclusion
`𝔸_K ⊆ (𝔸_L)^{Gal(L/K)}` and its multiplicative analogues.

The reverse inclusion `(𝔸_L)^{Gal(L/K)} ⊆ 𝔸_K` is *not* proved here: at a ramified or inert
place it amounts to `L_w^{D_w} = K_v`, which is Galois theory of complete local fields.

## Main definitions

* `NumberField.AdeleRing.baseChange : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L`.
* `NumberField.AdeleRing.baseChangeAlgebra` : the induced `𝔸_K`-algebra structure on `𝔸_L`.
* `NumberField.IdeleGroup.baseChange : IdeleGroup (𝓞 K) K →* IdeleGroup (𝓞 L) L`.
* `NumberField.IdeleClassGroup.baseChange : IdeleClassGroup (𝓞 K) K →* IdeleClassGroup (𝓞 L) L`.

## Main results

* `NumberField.AdeleRing.baseChange_injective`, `..._continuous`, `..._algebraMap`.
* `NumberField.AdeleRing.adeleMap_baseChange`, `NumberField.AdeleRing.galAdeleAut_baseChange` :
  the adeles coming from `K` are `Gal(L/K)`-invariant.
* `NumberField.IdeleGroup.galIdeleAut_baseChange`,
  `NumberField.IdeleClassGroup.galIdeleClassAut_baseChange` : the same for ideles and idele
  classes.
* `NumberField.AdeleRing.baseChange_trans`, `NumberField.IdeleGroup.baseChange_trans`,
  `NumberField.IdeleClassGroup.baseChange_trans` : functoriality in a tower `K ⊆ L ⊆ M`.
-/

noncomputable section

open IsDedekindDomain

namespace NumberField.AdeleRing

variable (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]

/-- The base change map `𝔸_K →+* 𝔸_L` on adele rings. -/
def baseChange : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  (AdeleRing.prodEquiv (𝓞 L) L).symm.toRingHom.comp
    (((InfiniteAdeleRing.baseChange (K := K) (L := L)).prodMap
      (finiteAdeleBaseChange K L)).comp (AdeleRing.prodEquiv (𝓞 K) K).toRingHom)

variable {K L}

@[simp]
theorem baseChange_fst (x : AdeleRing (𝓞 K) K) :
    (AdeleRing.prodEquiv (𝓞 L) L (baseChange K L x)).1 =
      InfiniteAdeleRing.baseChange (AdeleRing.prodEquiv (𝓞 K) K x).1 := rfl

@[simp]
theorem baseChange_snd (x : AdeleRing (𝓞 K) K) :
    (AdeleRing.prodEquiv (𝓞 L) L (baseChange K L x)).2 =
      finiteAdeleBaseChange K L (AdeleRing.prodEquiv (𝓞 K) K x).2 := rfl

theorem baseChange_ext {x y : AdeleRing (𝓞 K) K}
    (h₁ : (AdeleRing.prodEquiv (𝓞 K) K x).1 = (AdeleRing.prodEquiv (𝓞 K) K y).1)
    (h₂ : (AdeleRing.prodEquiv (𝓞 K) K x).2 = (AdeleRing.prodEquiv (𝓞 K) K y).2) : x = y :=
  Prod.ext h₁ h₂

variable (K L)

@[simp]
theorem baseChange_algebraMap (k : K) :
    baseChange K L (algebraMap K (AdeleRing (𝓞 K) K) k) =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L k) := by
  refine Prod.ext ?_ ?_
  · exact InfiniteAdeleRing.baseChange_algebraMap k
  · exact IsDedekindDomain.FiniteAdeleRing.baseChange_algebraMap K L k

theorem baseChange_injective : Function.Injective (baseChange K L) := by
  intro x y hxy
  refine Prod.ext ?_ ?_
  · exact (InfiniteAdeleRing.baseChange_injective (K := K) (L := L))
      (congrArg (fun z : AdeleRing (𝓞 L) L ↦ (AdeleRing.prodEquiv (𝓞 L) L z).1) hxy)
  · exact (finiteAdeleBaseChange_injective K L)
      (congrArg (fun z : AdeleRing (𝓞 L) L ↦ (AdeleRing.prodEquiv (𝓞 L) L z).2) hxy)

theorem continuous_baseChange : Continuous (baseChange K L) :=
  ((InfiniteAdeleRing.continuous_baseChange (K := K) (L := L)).prodMap
    (continuous_finiteAdeleBaseChange K L)).comp continuous_id

/-- The `𝔸_K`-algebra structure on `𝔸_L` given by base change. -/
@[instance_reducible]
def baseChangeAlgebra : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
  (baseChange K L).toAlgebra

variable {K L}

/-- **The easy inclusion `𝔸_K ⊆ (𝔸_L)^{Gal(L/K)}`.** -/
theorem adeleMap_baseChange (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 K) K) :
    adeleMap (σ : L ≃+* L) (baseChange K L x) = baseChange K L x := by
  refine Prod.ext ?_ ?_
  · exact InfiniteAdeleRing.infiniteAdeleMap_baseChange σ _
  · exact finiteAdeleMap_baseChange σ _

@[simp]
theorem galAdeleAut_baseChange (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 K) K) :
    galAdeleAut K L σ (baseChange K L x) = baseChange K L x :=
  adeleMap_baseChange σ x

@[simp]
theorem smul_baseChange (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 K) K) :
    (σ : L ≃+* L) • baseChange K L x = baseChange K L x :=
  adeleMap_baseChange σ x

end NumberField.AdeleRing

/-! ## Base change of ideles -/

namespace NumberField.IdeleGroup

variable (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]

/-- The base change map `𝕀_K →* 𝕀_L` on idele groups. -/
def baseChange : IdeleGroup (𝓞 K) K →* IdeleGroup (𝓞 L) L :=
  Units.map (AdeleRing.baseChange K L).toMonoidHom

variable {K L}

@[simp]
theorem coe_baseChange (u : IdeleGroup (𝓞 K) K) :
    ((baseChange K L u : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L) =
      AdeleRing.baseChange K L (u : AdeleRing (𝓞 K) K) := rfl

theorem baseChange_injective : Function.Injective (baseChange K L) :=
  Units.map_injective (AdeleRing.baseChange_injective K L)

@[simp]
theorem baseChange_principalEmbedding (x : Kˣ) :
    baseChange K L (principalEmbedding (𝓞 K) K x) =
      principalEmbedding (𝓞 L) L (Units.map (algebraMap K L) x) := by
  refine Units.ext ?_
  simp

set_option maxHeartbeats 1000000 in
/-- The principal ideles of `K` land in the principal ideles of `L`. -/
theorem baseChange_le_comap_principalSubgroup :
    principalSubgroup (𝓞 K) K ≤ (principalSubgroup (𝓞 L) L).comap (baseChange K L) := by
  rintro u ⟨x, rfl⟩
  rw [Subgroup.mem_comap, baseChange_principalEmbedding]
  exact ⟨Units.map (algebraMap K L) x, rfl⟩

/-- **The easy inclusion `𝕀_K ⊆ (𝕀_L)^{Gal(L/K)}`.** -/
@[simp]
theorem galIdeleAut_baseChange (σ : L ≃ₐ[K] L) (u : IdeleGroup (𝓞 K) K) :
    galIdeleAut K L σ (baseChange K L u) = baseChange K L u :=
  Units.ext (AdeleRing.adeleMap_baseChange σ _)

end NumberField.IdeleGroup

/-! ## Base change of idele classes -/

namespace NumberField.IdeleClassGroup

variable (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]

/-- The base change map `C_K →* C_L` on idele class groups. -/
def baseChange : IdeleClassGroup (𝓞 K) K →* IdeleClassGroup (𝓞 L) L :=
  QuotientGroup.map _ _ (IdeleGroup.baseChange K L)
    IdeleGroup.baseChange_le_comap_principalSubgroup

variable {K L}

@[simp]
theorem baseChange_mk (u : IdeleGroup (𝓞 K) K) :
    baseChange K L (IdeleClassGroup.mk (𝓞 K) K u) =
      IdeleClassGroup.mk (𝓞 L) L (IdeleGroup.baseChange K L u) :=
  QuotientGroup.map_mk' _ _ _ _ u

/-- **The easy inclusion `C_K ⊆ (C_L)^{Gal(L/K)}`.** -/
@[simp]
theorem galIdeleClassAut_baseChange (σ : L ≃ₐ[K] L) (c : IdeleClassGroup (𝓞 K) K) :
    galIdeleClassAut K L σ (baseChange K L c) = baseChange K L c := by
  obtain ⟨u, rfl⟩ := IdeleClassGroup.mk_surjective (𝓞 K) K c
  rw [baseChange_mk, galIdeleClassAut_mk, galIdeleAut_apply]
  congr 1
  exact IdeleGroup.galIdeleAut_baseChange σ u

end NumberField.IdeleClassGroup

/-! ## Functoriality in a tower of number fields -/

namespace NumberField

variable (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  (M : Type*) [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M]

/-- Base change of adeles is functorial in a tower of number fields `K ⊆ L ⊆ M`. -/
theorem AdeleRing.baseChange_trans (x : AdeleRing (𝓞 K) K) :
    AdeleRing.baseChange L M (AdeleRing.baseChange K L x) = AdeleRing.baseChange K M x :=
  Prod.ext (InfiniteAdeleRing.baseChange_trans _) (finiteAdeleBaseChange_trans K L M _)

/-- Base change of ideles is functorial in a tower of number fields `K ⊆ L ⊆ M`. -/
theorem IdeleGroup.baseChange_trans (u : IdeleGroup (𝓞 K) K) :
    IdeleGroup.baseChange L M (IdeleGroup.baseChange K L u) = IdeleGroup.baseChange K M u :=
  Units.ext (AdeleRing.baseChange_trans K L M _)

/-- Base change of idele classes is functorial in a tower of number fields `K ⊆ L ⊆ M`. -/
theorem IdeleClassGroup.baseChange_trans (c : IdeleClassGroup (𝓞 K) K) :
    IdeleClassGroup.baseChange L M (IdeleClassGroup.baseChange K L c) =
      IdeleClassGroup.baseChange K M c := by
  obtain ⟨u, rfl⟩ := IdeleClassGroup.mk_surjective (𝓞 K) K c
  rw [IdeleClassGroup.baseChange_mk, IdeleClassGroup.baseChange_mk,
    IdeleClassGroup.baseChange_mk]
  congr 1
  exact IdeleGroup.baseChange_trans K L M u

end NumberField
