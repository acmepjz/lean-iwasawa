/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.AdeleBaseChange
public import Iwasawalib.NumberTheory.CFT.AdeleCongr

@[expose] public section

/-!
# Galois equivariance of adelic base change over an intermediate field

`Iwasawalib/NumberTheory/CFT/AdeleBaseChange.lean` proves the *trivial-action* case of
Galois equivariance: an automorphism of `L` over `K` fixes every adele coming from `K`
(`NumberField.AdeleRing.adeleMap_baseChange`).  That is the statement for the bottom field of
the extension.  For an *intermediate* field `E`, an automorphism `τ` of `L` over `K` need not
fix `𝔸_E` pointwise: it acts on `E` through its restriction `ρ`, and base change intertwines
the two actions rather than killing one of them.

This file proves that naturality, at every level of the adelic stack:

`AdeleRing.baseChange E L (adeleMap ρ y) = adeleMap τ (AdeleRing.baseChange E L y)`

whenever `τ (algebraMap E L x) = algebraMap E L (ρ x)` for all `x : E`.  Taking `ρ = id`
recovers the trivial-action statement, so the lemma is a strict generalisation of
`adeleMap_baseChange`.

The proof is componentwise, and the local input is in both cases a density argument: the
image of the global field is dense in each completion, and the two composites agree on it by
the hypothesis relating `τ` and `ρ`.  The bookkeeping that is genuinely new compared with the
trivial-action case is that the *place* moves: the source place of the base change on the
left is `(w ∘ τ) ∘ ι` and on the right `(w ∘ ι) ∘ ρ`, and these agree only because `τ ∘ ι`
and `ι ∘ ρ` are the same ring homomorphism.  Finitely this is
`IsDedekindDomain.FiniteAdeleRing.under_equivOfRingEquiv_symm_comm`, which says that the
permutation of the height one spectrum of `B` induced by `τ` covers the permutation of the
spectrum of `A` induced by `ρ`; archimedeanly it is the equation `hidx` inside
`NumberField.InfiniteAdeleRing.baseChange_infiniteAdeleMap_comm`.

## Main definitions

* `IntermediateField.restrictStable` : the restriction `E ≃ₐ[K] E` of an automorphism
  `τ : L ≃ₐ[K] L` to an intermediate field `E` that `τ` stabilises.

## Main statements

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr_adicCompletionComap_comm` : the
  local naturality, `K_v →+* L_w` intertwining `ρ` and `τ`.
* `IsDedekindDomain.FiniteAdeleRing.ringEquiv_comp_algebraMap_comm`,
  `IsDedekindDomain.FiniteAdeleRing.under_equivOfRingEquiv_symm_comm` : the induced
  automorphism of `B` restricts to the induced automorphism of `A`, and the induced
  permutations of the height one spectra are compatible with `w ↦ w.under A`.
* `IsDedekindDomain.FiniteAdeleRing.baseChange_congrRingHom_comm`,
  `NumberField.InfiniteAdeleRing.baseChange_infiniteAdeleMap_comm` : the two halves.
* `NumberField.AdeleRing.baseChange_adeleMap_comm`,
  `NumberField.IdeleGroup.baseChange_ideleAut_comm`,
  `NumberField.IdeleClassGroup.baseChange_ideleClassAut_comm` : the naturality on `𝔸`, on
  `𝕀` and on `C`.
* `NumberField.AdeleRing.baseChange_adeleMap_restrictStable`,
  `NumberField.IdeleGroup.baseChange_ideleAut_restrictStable`,
  `NumberField.IdeleClassGroup.baseChange_ideleClassAut_restrictStable` : the same three
  statements for an intermediate field `E` stabilised by `τ : L ≃ₐ[K] L`, with `ρ` taken to
  be `IntermediateField.restrictStable`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

section LocalNaturality

variable {A B : Type*} (K L : Type*)
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]

/-- **Local naturality of base change.** -/
theorem adicCompletionCongr_adicCompletionComap_comm
    (ρ : K ≃+* K) (τ : L ≃+* L)
    (hcompat : ∀ x : K, τ (algebraMap K L x) = algebraMap K L (ρ x))
    (v v' : HeightOneSpectrum A) (w w' : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v'.asIdeal]
    (hτ : ∀ y : L, w'.valuation L (τ y) = w.valuation L y)
    (hρ : ∀ x : K, v'.valuation K (ρ x) = v.valuation K x)
    (z : v.adicCompletion K) :
    adicCompletionCongr τ w w' hτ (adicCompletionComap K L v w z) =
      adicCompletionComap K L v' w' (adicCompletionCongr ρ v v' hρ z) := by
  have hcont₁ : Continuous fun z : v.adicCompletion K ↦
      adicCompletionCongr τ w w' hτ (adicCompletionComap K L v w z) :=
    (continuous_adicCompletionCongr τ w w' hτ).comp (continuous_adicCompletionComap K L v w)
  have hcont₂ : Continuous fun z : v.adicCompletion K ↦
      adicCompletionComap K L v' w' (adicCompletionCongr ρ v v' hρ z) :=
    (continuous_adicCompletionComap K L v' w').comp (continuous_adicCompletionCongr ρ v v' hρ)
  have := Continuous.ext_on (denseRange_algebraMap (R := A) (K := K) (v := v))
    hcont₁ hcont₂ ?_
  · exact congrFun this z
  · rintro _ ⟨k, rfl⟩
    show adicCompletionCongr τ w w' hτ
          (adicCompletionComap K L v w ((k : K) : v.adicCompletion K))
        = adicCompletionComap K L v' w'
          (adicCompletionCongr ρ v v' hρ ((k : K) : v.adicCompletion K))
    rw [adicCompletionComap_coe, adicCompletionCongr_coe, adicCompletionCongr_coe,
      adicCompletionComap_coe, hcompat]

end LocalNaturality

end IsDedekindDomain.HeightOneSpectrum

/-! ## Naturality on the finite adele ring -/

namespace IsDedekindDomain.FiniteAdeleRing

section Naturality

variable {A B : Type*} (K L : Type*)
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable {eA : A ≃+* A} {eB : B ≃+* B} {ρ : K ≃+* K} {τ : L ≃+* L}
variable (hA : ∀ a : A, ρ (algebraMap A K a) = algebraMap A K (eA a))
variable (hB : ∀ b : B, τ (algebraMap B L b) = algebraMap B L (eB b))
variable (hcompat : ∀ x : K, τ (algebraMap K L x) = algebraMap K L (ρ x))

include hA hB hcompat

omit [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [Algebra.IsIntegral A B] [IsFractionRing A K] in
/-- If `τ` restricts to `ρ` on `K`, then the induced automorphism `eB` of `B` restricts to the
induced automorphism `eA` of `A`. -/
theorem ringEquiv_comp_algebraMap_comm :
    ((eB : B →+* B).comp (algebraMap A B)) = (algebraMap A B).comp (eA : A →+* A) := by
  refine RingHom.ext fun a ↦ ?_
  refine IsFractionRing.injective B L ?_
  show algebraMap B L (eB (algebraMap A B a)) = algebraMap B L (algebraMap A B (eA a))
  calc algebraMap B L (eB (algebraMap A B a))
      = τ (algebraMap B L (algebraMap A B a)) := (hB _).symm
    _ = τ (algebraMap K L (algebraMap A K a)) := by
        rw [← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L]
    _ = algebraMap K L (ρ (algebraMap A K a)) := hcompat _
    _ = algebraMap K L (algebraMap A K (eA a)) := by rw [hA]
    _ = algebraMap B L (algebraMap A B (eA a)) := by
        rw [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L]

omit [Module.IsTorsionFree A B] [IsFractionRing A K] in
/-- The permutation of the height one spectrum of `B` induced by `eB` is compatible with the
one induced by `eA`, under `w ↦ w.under A`. -/
theorem under_equivOfRingEquiv_symm_comm (w : HeightOneSpectrum B) :
    ((equivOfRingEquiv eB).symm w).under A =
      (equivOfRingEquiv eA).symm (w.under A) := by
  refine HeightOneSpectrum.ext ?_
  show (w.asIdeal.comap ((eB : B ≃+* B) : B →+* B)).comap (algebraMap A B) =
    (w.asIdeal.comap (algebraMap A B)).comap ((eA : A ≃+* A) : A →+* A)
  rw [Ideal.comap_comap, Ideal.comap_comap,
    ringEquiv_comp_algebraMap_comm K L hA hB hcompat]

/-- **Naturality of base change on finite adele rings.** -/
theorem baseChange_congrRingHom_comm (x : FiniteAdeleRing A K) :
    baseChange K L (congrRingHom eA ρ hA x) = congrRingHom eB τ hB (baseChange K L x) := by
  refine FiniteAdeleRing.ext L fun w ↦ ?_
  set u : HeightOneSpectrum B := (equivOfRingEquiv eB).symm w with hu
  have hunder : u.under A = (equivOfRingEquiv eA).symm (w.under A) :=
    under_equivOfRingEquiv_symm_comm K L hA hB hcompat w
  have hτv : ∀ y : L, w.valuation L (τ y) = u.valuation L y :=
    valuation_symm_equivOfRingEquiv eB τ hB w
  have hρv : ∀ z : K, (w.under A).valuation K (ρ z) = (u.under A).valuation K z := by
    rw [hunder]
    exact valuation_symm_equivOfRingEquiv eA ρ hA (w.under A)
  rw [baseChange_apply, congrRingHom_apply, congrRingHom_apply, baseChange_apply,
    adicCompletionCongr_adicCompletionComap_comm K L ρ τ hcompat (u.under A) (w.under A) u w
      hτv hρv]
  exact congrArg (adicCompletionComap K L (w.under A) w)
    (adicCompletionCongr_index_congr hunder (w.under A) ρ hρv
      (valuation_symm_equivOfRingEquiv eA ρ hA (w.under A)) (fun t ↦ x t)).symm

end Naturality

end IsDedekindDomain.FiniteAdeleRing

/-! ## Naturality on the infinite adele ring -/

namespace NumberField.InfiniteAdeleRing

open InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Naturality of base change on infinite adele rings.** -/
theorem baseChange_infiniteAdeleMap_comm (ρ : K ≃+* K) (τ : L ≃+* L)
    (hcompat : ∀ x : K, τ (algebraMap K L x) = algebraMap K L (ρ x)) (y : InfiniteAdeleRing K) :
    baseChange (K := K) (L := L) (infiniteAdeleMap ρ y) =
      infiniteAdeleMap τ (baseChange (K := K) (L := L) y) := by
  funext w
  have hcomp : ((τ : L ≃+* L) : L →+* L).comp (algebraMap K L) =
      (algebraMap K L).comp ((ρ : K ≃+* K) : K →+* K) := RingHom.ext hcompat
  set v : InfinitePlace K := w.comap (algebraMap K L) with hv
  have hidx : (w.comap ((τ : L ≃+* L) : L →+* L)).comap (algebraMap K L) =
      v.comap ((ρ : K ≃+* K) : K →+* K) := by
    rw [hv, ← InfinitePlace.comap_comp, ← InfinitePlace.comap_comp, hcomp]
  have h2 : ∀ k : K, (w.comap ((τ : L ≃+* L) : L →+* L)) (algebraMap K L k) =
      (v.comap ((ρ : K ≃+* K) : K →+* K)) k := by
    intro k
    simp only [InfinitePlace.comap_apply, hv]
    exact congrArg w (hcompat k)
  have h3 : ∀ k : K, w ((((τ : L ≃+* L) : L →+* L)).comp (algebraMap K L) k) =
      (v.comap ((ρ : K ≃+* K) : K →+* K)) k := h2
  have h4 : ∀ k : K, w ((algebraMap K L).comp ((ρ : K ≃+* K) : K →+* K) k) =
      (v.comap ((ρ : K ≃+* K) : K →+* K)) k := fun _ ↦ rfl
  calc baseChange (K := K) (L := L) (infiniteAdeleMap ρ y) w
      = Completion.map (algebraMap K L) v w (fun _ ↦ rfl)
          (Completion.map ((ρ : K ≃+* K) : K →+* K) (v.comap ((ρ : K ≃+* K) : K →+* K)) v
            (fun _ ↦ rfl) (y (v.comap ((ρ : K ≃+* K) : K →+* K)))) := rfl
    _ = Completion.map ((algebraMap K L).comp ((ρ : K ≃+* K) : K →+* K))
          (v.comap ((ρ : K ≃+* K) : K →+* K)) w h4
          (y (v.comap ((ρ : K ≃+* K) : K →+* K))) :=
        Completion.map_trans _ _ _ _ _ _ _ _ _
    _ = Completion.map (((τ : L ≃+* L) : L →+* L).comp (algebraMap K L))
          (v.comap ((ρ : K ≃+* K) : K →+* K)) w h3
          (y (v.comap ((ρ : K ≃+* K) : K →+* K))) :=
        Completion.map_hom_congr hcomp.symm _ _ _ _ _
    _ = Completion.map ((τ : L ≃+* L) : L →+* L) (w.comap ((τ : L ≃+* L) : L →+* L)) w
          (fun _ ↦ rfl)
          (Completion.map (algebraMap K L) (v.comap ((ρ : K ≃+* K) : K →+* K))
            (w.comap ((τ : L ≃+* L) : L →+* L)) h2
            (y (v.comap ((ρ : K ≃+* K) : K →+* K)))) :=
        (Completion.map_trans _ _ _ _ _ _ _ _ _).symm
    _ = Completion.map ((τ : L ≃+* L) : L →+* L) (w.comap ((τ : L ≃+* L) : L →+* L)) w
          (fun _ ↦ rfl)
          (Completion.map (algebraMap K L)
            ((w.comap ((τ : L ≃+* L) : L →+* L)).comap (algebraMap K L))
            (w.comap ((τ : L ≃+* L) : L →+* L)) (fun _ ↦ rfl)
            (y ((w.comap ((τ : L ≃+* L) : L →+* L)).comap (algebraMap K L)))) := by
        rw [Completion.map_index_congr hidx (algebraMap K L)
          (w.comap ((τ : L ≃+* L) : L →+* L)) (fun _ ↦ rfl) h2 y]
    _ = infiniteAdeleMap τ (baseChange (K := K) (L := L) y) w := rfl

end NumberField.InfiniteAdeleRing

/-! ## Naturality on the full adele ring, on ideles and on idele classes -/

namespace NumberField

open IsDedekindDomain

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Naturality of adelic base change.**  If the automorphism `τ` of `L` restricts to the
automorphism `ρ` of the subfield `K`, then base change `𝔸_K →+* 𝔸_L` intertwines the two
actions.  For `ρ = id` this is `NumberField.AdeleRing.adeleMap_baseChange`. -/
theorem AdeleRing.baseChange_adeleMap_comm (ρ : K ≃+* K) (τ : L ≃+* L)
    (hcompat : ∀ x : K, τ (algebraMap K L x) = algebraMap K L (ρ x)) (y : AdeleRing (𝓞 K) K) :
    AdeleRing.baseChange K L (adeleMap ρ y) = adeleMap τ (AdeleRing.baseChange K L y) := by
  refine Prod.ext ?_ ?_
  · exact InfiniteAdeleRing.baseChange_infiniteAdeleMap_comm ρ τ hcompat _
  · exact IsDedekindDomain.FiniteAdeleRing.baseChange_congrRingHom_comm K L
      (mapRingEquiv_compat ρ) (mapRingEquiv_compat τ) hcompat _

/-- **Naturality of adelic base change on ideles.** -/
theorem IdeleGroup.baseChange_ideleAut_comm (ρ : RingAut K) (τ : RingAut L)
    (hcompat : ∀ x : K, τ (algebraMap K L x) = algebraMap K L (ρ x))
    (u : IdeleGroup (𝓞 K) K) :
    IdeleGroup.baseChange K L (ideleAut ρ u) = ideleAut τ (IdeleGroup.baseChange K L u) :=
  Units.ext (AdeleRing.baseChange_adeleMap_comm ρ τ hcompat _)

/-- **Naturality of adelic base change on idele classes.** -/
theorem IdeleClassGroup.baseChange_ideleClassAut_comm (ρ : RingAut K) (τ : RingAut L)
    (hcompat : ∀ x : K, τ (algebraMap K L x) = algebraMap K L (ρ x))
    (c : IdeleClassGroup (𝓞 K) K) :
    IdeleClassGroup.baseChange K L (ideleClassAut ρ c) =
      ideleClassAut τ (IdeleClassGroup.baseChange K L c) := by
  obtain ⟨u, rfl⟩ := IdeleClassGroup.mk_surjective (𝓞 K) K c
  rw [ideleClassAut_mk, IdeleClassGroup.baseChange_mk, IdeleClassGroup.baseChange_mk,
    ideleClassAut_mk]
  exact congrArg (IdeleClassGroup.mk (𝓞 L) L)
    (IdeleGroup.baseChange_ideleAut_comm ρ τ hcompat u)

end NumberField

/-! ## The intermediate field form -/

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The restriction to a stable intermediate field `E` of an automorphism `τ` of `L`. -/
def restrictStable (E : IntermediateField K L) (τ : L ≃ₐ[K] L)
    (hE : E.map (τ : L →ₐ[K] L) = E) : E ≃ₐ[K] E :=
  (IntermediateField.intermediateFieldMap τ E).trans (IntermediateField.equivOfEq hE)

@[simp]
theorem coe_restrictStable (E : IntermediateField K L) (τ : L ≃ₐ[K] L)
    (hE : E.map (τ : L →ₐ[K] L) = E) (x : E) :
    ((restrictStable E τ hE x : E) : L) = τ (x : L) := rfl

theorem algebraMap_restrictStable (E : IntermediateField K L) (τ : L ≃ₐ[K] L)
    (hE : E.map (τ : L →ₐ[K] L) = E) (x : E) :
    τ (algebraMap E L x) = algebraMap E L (restrictStable E τ hE x) :=
  (coe_restrictStable E τ hE x).symm

end IntermediateField

namespace NumberField

open IsDedekindDomain

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The missing naturality, in the form the tower needs.**  For a Galois automorphism `τ`
of `L` over `K` stabilising the intermediate field `E`, base change `𝔸_E →+* 𝔸_L` carries the
action of the restriction of `τ` to `E` to the action of `τ`. -/
theorem AdeleRing.baseChange_adeleMap_restrictStable (E : IntermediateField K L)
    (τ : L ≃ₐ[K] L) (hE : E.map (τ : L →ₐ[K] L) = E) (y : AdeleRing (𝓞 E) E) :
    AdeleRing.baseChange E L
        (adeleMap ((E.restrictStable τ hE : E ≃ₐ[K] E) : E ≃+* E) y) =
      adeleMap ((τ : L ≃ₐ[K] L) : L ≃+* L) (AdeleRing.baseChange E L y) :=
  AdeleRing.baseChange_adeleMap_comm _ _ (E.algebraMap_restrictStable τ hE) y

/-- **The missing naturality for ideles.** -/
theorem IdeleGroup.baseChange_ideleAut_restrictStable (E : IntermediateField K L)
    (τ : L ≃ₐ[K] L) (hE : E.map (τ : L →ₐ[K] L) = E) (u : IdeleGroup (𝓞 E) E) :
    IdeleGroup.baseChange E L
        (galIdeleAut K E (E.restrictStable τ hE) u) =
      galIdeleAut K L τ (IdeleGroup.baseChange E L u) :=
  IdeleGroup.baseChange_ideleAut_comm _ _ (E.algebraMap_restrictStable τ hE) u

/-- **The missing naturality for idele classes.** -/
theorem IdeleClassGroup.baseChange_ideleClassAut_restrictStable (E : IntermediateField K L)
    (τ : L ≃ₐ[K] L) (hE : E.map (τ : L →ₐ[K] L) = E) (c : IdeleClassGroup (𝓞 E) E) :
    IdeleClassGroup.baseChange E L
        (galIdeleClassAut K E (E.restrictStable τ hE) c) =
      galIdeleClassAut K L τ (IdeleClassGroup.baseChange E L c) :=
  IdeleClassGroup.baseChange_ideleClassAut_comm _ _ (E.algebraMap_restrictStable τ hE) c

end NumberField
