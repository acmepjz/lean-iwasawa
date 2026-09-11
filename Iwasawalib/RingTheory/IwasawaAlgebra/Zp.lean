/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.Algebra.CompleteGroupAlgebra.Basic
public import Iwasawalib.NumberTheory.Padics.EquivMvZp
public import Iwasawalib.RingTheory.IwasawaAlgebra.Basic

@[expose] public section

/-!
# The Iwasawa algebra of a group isomorphic to `ℤ_p`

If `Γ` is a topological group isomorphic to `ℤ_p`, then the completed group algebra
`ℤ_p⟦Γ⟧` is isomorphic to `ℤ_p⟦X⟧` as a `ℤ_p`-algebra. This is blueprint node
`Iwasawa-alg-isom`.
-/

open PowerSeries CompleteGroupAlgebra

namespace EquivMvZp

variable {G : Type*} [Group G] [TopologicalSpace G] {p : ℕ} [Fact p.Prime]
  {ι : Type*} [Unique ι] (H : EquivMvZp G p ι)

/-- The surjection from `Γ` onto `Multiplicative (ZMod (p ^ n))`. -/
noncomputable def toZMod (n : ℕ) : H.Γ →* Multiplicative (ZMod (p ^ n)) :=
  (AddMonoidHom.toMultiplicative (PadicInt.toZModPow n).toAddMonoidHom).comp
    (H.continuousMulEquiv₁ : H.Γ →* Multiplicative ℤ_[p])

theorem toZMod_apply (n : ℕ) (σ : H.Γ) : Multiplicative.toAdd (H.toZMod n σ) =
    PadicInt.toZModPow n (Multiplicative.toAdd (H.continuousMulEquiv₁ σ)) := rfl

theorem toZMod_surjective (n : ℕ) : Function.Surjective (H.toZMod n) := by
  intro a
  obtain ⟨b, hb⟩ : ∃ b : ℤ_[p], PadicInt.toZModPow n b = Multiplicative.toAdd a :=
    ⟨((Multiplicative.toAdd a).val : ℤ_[p]), by
      rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]⟩
  exact ⟨H.continuousMulEquiv₁.symm (Multiplicative.ofAdd b), by
    apply Multiplicative.toAdd.injective
    rw [toZMod_apply]
    simpa using hb⟩

theorem ker_toZMod (n : ℕ) : (H.Γpow n).toSubgroup = MonoidHom.ker (H.toZMod n) := by
  ext σ
  have h1 : H.toZMod n σ = 1 ↔ Multiplicative.toAdd (H.continuousMulEquiv₁ σ) ∈
      Ideal.span {(p : ℤ_[p]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, ← toZMod_apply]
    exact ⟨fun h ↦ by rw [h]; rfl, fun h ↦ Multiplicative.toAdd.injective h⟩
  rw [MonoidHom.mem_ker, h1, EquivMvZp.toSubgroup_Γpow, H.mem_Γpow'_iff,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨τ, rfl⟩
    refine ⟨Multiplicative.toAdd (H.continuousMulEquiv₁ τ), ?_⟩
    rw [map_pow, toAdd_pow, nsmul_eq_mul]
    push_cast
    ring
  · rintro ⟨b, hb⟩
    refine ⟨H.continuousMulEquiv₁.symm (Multiplicative.ofAdd b), ?_⟩
    apply H.continuousMulEquiv₁.injective
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow]
    simp [hb, nsmul_eq_mul]

/-- `Γ ⧸ Γ ^ (p ^ n) ≃* Multiplicative (ZMod (p ^ n))`. -/
noncomputable def quotEquiv (n : ℕ) :
    H.Γ ⧸ (H.Γpow n).toSubgroup ≃* Multiplicative (ZMod (p ^ n)) :=
  (QuotientGroup.quotientMulEquivOfEq (H.ker_toZMod n)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (H.toZMod_surjective n))

@[simp]
theorem quotEquiv_mk (n : ℕ) (σ : H.Γ) :
    H.quotEquiv n (QuotientGroup.mk σ) = H.toZMod n σ := rfl

theorem castHom_toZMod {n m : ℕ} (h : n ≤ m) (σ : H.Γ) :
    ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n))
      (Multiplicative.toAdd (H.toZMod m σ)) = Multiplicative.toAdd (H.toZMod n σ) := by
  rw [toZMod_apply, toZMod_apply, ← RingHom.comp_apply,
    PadicInt.zmod_cast_comp_toZModPow n m h]

theorem zmodTransHom_comp_quotEquiv {n m : ℕ} (h : n ≤ m) :
    (IwasawaAlgebra.zmodTransHom p h).comp (H.quotEquiv m : _ →* _) =
      (H.quotEquiv n : _ →* _).comp (QuotientGroup.map (H.Γpow m).toSubgroup
        (H.Γpow n).toSubgroup (MonoidHom.id H.Γ) (H.antitone_Γpow h)) := by
  refine MonoidHom.ext fun x ↦ ?_
  induction x using QuotientGroup.induction_on with
  | H σ =>
    simp only [MonoidHom.comp_apply, QuotientGroup.map_mk, MonoidHom.id_apply]
    exact Multiplicative.toAdd.injective (H.castHom_toZMod h σ)

/-- The level isomorphism `ℤ_p[Γ ⧸ Γ ^ (p ^ n)] ≃ₐ[ℤ_p] ℤ_p[ZMod (p ^ n)]`. -/
noncomputable def groupAlgebraLevelEquiv (n : ℕ) :
    MonoidAlgebra ℤ_[p] (H.Γ ⧸ (H.Γpow n).toSubgroup) ≃ₐ[ℤ_[p]]
      MonoidAlgebra ℤ_[p] (Multiplicative (ZMod (p ^ n))) :=
  MonoidAlgebra.domCongr ℤ_[p] ℤ_[p] (H.quotEquiv n)

theorem groupAlgebraLevelEquiv_comp ⦃n m : ℕ⦄ (h : n ≤ m) :
    (IwasawaAlgebra.groupTrans ℤ_[p] p h).comp
        (H.groupAlgebraLevelEquiv m : _ →ₐ[ℤ_[p]] _) =
      (H.groupAlgebraLevelEquiv n : _ →ₐ[ℤ_[p]] _).comp
        (MonoidAlgebra.mapDomainAlgHom ℤ_[p] ℤ_[p] (QuotientGroup.map (H.Γpow m).toSubgroup
          (H.Γpow n).toSubgroup (MonoidHom.id H.Γ) (H.antitone_Γpow h))) := by
  simp only [IwasawaAlgebra.groupTrans, groupAlgebraLevelEquiv,
    MonoidAlgebra.domCongr_toAlgHom]
  rw [← MonoidAlgebra.mapDomainAlgHom_comp, ← MonoidAlgebra.mapDomainAlgHom_comp,
    H.zmodTransHom_comp_quotEquiv h]

/-- **The Iwasawa algebra isomorphism** (blueprint node `Iwasawa-alg-isom`):
if `Γ` is a topological group isomorphic to `ℤ_p`, then the completed group algebra
`Λ = ℤ_p⟦Γ⟧` is isomorphic to the power series ring `ℤ_p⟦X⟧` as a `ℤ_p`-algebra. -/
noncomputable def completeGroupAlgebraEquivPowerSeries :
    CompleteGroupAlgebra ℤ_[p] H.Γ ≃ₐ[ℤ_[p]] ℤ_[p]⟦X⟧ :=
  (CompleteGroupAlgebra.equivInverseLimit ℤ_[p] H.Γpow H.nhds_one_hasAntitoneBasis).trans
    ((Algebra.InverseLimit.congr (IwasawaAlgebra.groupTrans ℤ_[p] p) _
      H.groupAlgebraLevelEquiv H.groupAlgebraLevelEquiv_comp).trans
      (IwasawaAlgebra.padicInverseLimitEquiv p))

/-- The topological generator of `Γ` corresponding to `1 ∈ ℤ_p`. -/
noncomputable def gen : H.Γ := H.continuousMulEquiv₁.symm (Multiplicative.ofAdd 1)

@[simp]
theorem toZMod_gen (n : ℕ) : H.toZMod n H.gen = Multiplicative.ofAdd (1 : ZMod (p ^ n)) := by
  apply Multiplicative.toAdd.injective
  rw [toZMod_apply, gen]
  simp

/-- Under the isomorphism `ℤ_p⟦Γ⟧ ≃ ℤ_p⟦X⟧`, the topological generator `γ` of `Γ`
corresponds to `1 + X`. -/
theorem completeGroupAlgebraEquivPowerSeries_of_gen :
    H.completeGroupAlgebraEquivPowerSeries (CompleteGroupAlgebra.of ℤ_[p] H.Γ H.gen) =
      1 + X := by
  rw [completeGroupAlgebraEquivPowerSeries, IwasawaAlgebra.padicInverseLimitEquiv,
    IwasawaAlgebra.inverseLimitEquiv]
  simp only [AlgEquiv.trans_apply]
  rw [AlgEquiv.symm_apply_eq]
  refine Subtype.ext (funext fun n ↦ ?_)
  rw [PowerSeries.equivInverseLimitOmega_apply_coe]
  show IwasawaAlgebra.levelEquiv ℤ_[p] p n (H.groupAlgebraLevelEquiv n
    (CompleteGroupAlgebra.proj ℤ_[p] H.Γ (H.Γpow n) (CompleteGroupAlgebra.of ℤ_[p] H.Γ H.gen)))
    = Ideal.Quotient.mk _ (1 + PowerSeries.X)
  have h1 : CompleteGroupAlgebra.proj ℤ_[p] H.Γ (H.Γpow n)
      (CompleteGroupAlgebra.of ℤ_[p] H.Γ H.gen) =
      MonoidAlgebra.single (QuotientGroup.mk H.gen) 1 := by
    simp
  rw [h1, groupAlgebraLevelEquiv, MonoidAlgebra.domCongr_single, quotEquiv_mk, toZMod_gen,
    IwasawaAlgebra.levelEquiv_single]
  rw [map_pow]
  conv_rhs => rw [← pow_one (Ideal.Quotient.mk (PowerSeries.omegaIdeal ℤ_[p] p n)
    (1 + PowerSeries.X))]
  refine pow_eq_pow_of_modEq ?_ (IwasawaAlgebra.one_add_X_pow_eq_one ℤ_[p] p n)
  simp [ZMod.val_one_eq_one_mod, Nat.ModEq]

end EquivMvZp
