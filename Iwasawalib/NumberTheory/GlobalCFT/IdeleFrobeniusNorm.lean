/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.GlobalCFT.IdeleOrd
public import Iwasawalib.NumberTheory.LocalCFT.PlaceDedekind
public import Iwasawalib.NumberTheory.GlobalCFT.ReciprocityCyclic

@[expose] public section

/-!
# The reciprocity map on ideles kills the norms

Let `L / K` be an abelian extension of number fields, unramified at every place, and let

`ρ : 𝕀_K → Gal(L/K)`, `ρ(a) = ∏_p Frob_p ^ ord_p(a_p)`

be the reciprocity map of `Iwasawalib/NumberTheory/GlobalCFT/IdeleFrobenius.lean`.  Granted
`NumberField.IsArtinReciprocal K L` it descends to `C_K` (`NumberField.artinIdeleClassMap`).
This file proves, with **no further hypothesis**, that the descended map kills the group of
norms `N_{L/K} C_L`, so that it factors through `C_K / N_{L/K} C_L = Ĥ⁰(Gal(L/K), C_L)`.  That
is the input `NumberField.KillsNorms` required by
`Iwasawalib/NumberTheory/GlobalCFT/ReciprocityCyclic.lean`, and it is the half of the
reciprocity law which is local.

## The argument

Let `c ∈ C_K` become a norm in `C_L`.  Lift `c` to an idele `a ∈ 𝕀_K` and the norm to
`∏_{g ∈ Gal(L/K)} g · b` for an idele `b ∈ 𝕀_L`.  The two differ inside `𝕀_L` by a principal
idele of some `z ∈ Lˣ`; both are fixed by `Gal(L/K)` (`NumberField.smul_prod_smul` and
`NumberField.IdeleGroup.galIdeleAut_baseChange`), so `z` is fixed too, hence `z ∈ Kˣ`.

Now fix a place `v` of `K` and a place `w` of `L` above it.  The extension is unramified, so
base change preserves orders (`NumberField.IdeleGroup.ord_baseChange_of_ramificationIdx_eq_one`,
using the place/Dedekind bridge
`NumberField.ramificationIdx'_under_eq_one_of_isUnramifiedEverywhere`), and

`ord_v(a) - ord_v(z) = ord_w(∏_g g · b) = ∑_{g ∈ Gal(L/K)} ord_{g⁻¹ w}(b)`.

Because `Gal(L/K)` is **abelian**, the summand does not change when `g` is multiplied on the
right by an element of the decomposition group `D_w = Stab(w)`; hence `#D_w` divides the sum
(`Subgroup.card_dvd_sum_of_mul_mem`).  Since `Frob_v` lies in `D_w`
(`NumberField.frobAt_mem_stabilizer`), `Frob_v ^ #D_w = 1`, so `Frob_v ^ ord_v(a)` equals
`Frob_v ^ ord_v(z)` at every `v` and therefore `ρ(a) = ρ(z) = 1` by Artin reciprocity.

Note where each hypothesis is used: *unramified* to identify orders under base change and to
have a Frobenius at all, *abelian* twice (the Frobenius at `v` is the arithmetic Frobenius at
every `w` above `v`, and the right-invariance above), and *Artin reciprocity* only at the very
last step.

## Main statements

* `Subgroup.card_dvd_sum_of_mul_mem` : the counting lemma.
* `NumberField.frobAt_mem_stabilizer`, `NumberField.frobAt_pow_card_stabilizer`.
* `NumberField.frobIdeleHom_eq_one_of_baseChange_eq` : the local–global computation.
* `NumberField.killsNorms_artinIdeleClassMap` : the conclusion.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MulAction
open scoped IsMulCommutative nonZeroDivisors Pointwise

/-! ## A sum over a group of a function constant on the cosets of a subgroup -/

namespace Subgroup

variable {G : Type*} [Group G] [Fintype G] (H : Subgroup G)

/-- The fibre of `G → G ⧸ H` over a class is in bijection with `H`. -/
def fiberEquiv (q : G ⧸ H) : {g : G // (g : G ⧸ H) = q} ≃ H where
  toFun g := ⟨(Quotient.out q)⁻¹ * g, by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', g.2]⟩
  invFun h := ⟨Quotient.out q * h, by
    rw [← QuotientGroup.out_eq' q]
    exact (QuotientGroup.eq.2 (by simp)).symm⟩
  left_inv g := Subtype.ext (by simp)
  right_inv h := Subtype.ext (by simp)

/-- **The order of `H` divides any sum over `G` of a function constant on the cosets of `H`.**

This is the counting that makes the reciprocity map kill the norms: the norm of an idele is a
product over the whole Galois group, and its order at a place `w` is a sum which is constant on
the cosets of the decomposition group of `w`. -/
theorem card_dvd_sum_of_mul_mem (φ : G → ℤ)
    (hφ : ∀ (g h : G), h ∈ H → φ (g * h) = φ g) :
    (Nat.card H : ℤ) ∣ ∑ g : G, φ g := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (G ⧸ H)))
    (g := fun g : G ↦ (g : G ⧸ H)) (fun g _ ↦ Finset.mem_univ _) φ]
  refine Finset.dvd_sum fun q _ ↦ ?_
  have hconst : ∀ g ∈ Finset.univ.filter (fun g : G ↦ (g : G ⧸ H) = q),
      φ g = φ (Quotient.out q) := by
    intro g hg
    rw [Finset.mem_filter] at hg
    have : (Quotient.out q)⁻¹ * g ∈ H := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', hg.2]
    rw [← hφ (Quotient.out q) _ this, mul_inv_cancel_left]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const]
  have hcard : (Finset.univ.filter (fun g : G ↦ (g : G ⧸ H) = q)).card = Nat.card H := by
    rw [← Fintype.card_subtype, Nat.card_eq_fintype_card,
      Fintype.card_congr (fiberEquiv H q)]
  rw [hcard]
  exact Dvd.intro _ (by rw [nsmul_eq_mul])

end Subgroup

/-! ## The Frobenius lies in the decomposition group -/

attribute [local instance] NumberField.galIdeleMulDistribMulAction

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L] [IsAbelianGalois K L] [IsUnramifiedEverywhere K L]

/-- **The Frobenius at `v` stabilises every place `w` of `L` above `v`.**  In an abelian
extension the Frobenius at `v` is the arithmetic Frobenius at *every* prime above `v`, and an
arithmetic Frobenius at a prime stabilises that prime
(`IsArithFrobAt.mem_stabilizer`). -/
theorem frobAt_mem_stabilizer (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.under (𝓞 K) = v.asIdeal) :
    frobAt (F := K) (K := L) v ∈ stabilizer (L ≃ₐ[K] L) w := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  have hmem := (isArithFrobAt_globalFrobAt K L v w hw).mem_stabilizer
  rw [MulAction.mem_stabilizer_iff] at hmem ⊢
  rw [frobAt_eq_globalFrobAt]
  exact HeightOneSpectrum.ext (by rw [HeightOneSpectrum.smul_asIdeal, hmem])

/-- **`Frob_v` has order dividing the order of the decomposition group of any place above
`v`.** -/
theorem frobAt_pow_card_stabilizer (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.under (𝓞 K) = v.asIdeal) :
    frobAt (F := K) (K := L) v ^ Nat.card (stabilizer (L ≃ₐ[K] L) w) = 1 := by
  have := pow_card_eq_one' (G := stabilizer (L ≃ₐ[K] L) w)
    (x := ⟨_, frobAt_mem_stabilizer v w hw⟩)
  exact congrArg Subtype.val this

end NumberField

/-! ## The reciprocity map kills the norms -/

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L] [IsAbelianGalois K L] [IsUnramifiedEverywhere K L]

/-- **The local–global computation behind the norm-killing property.**

If the base change of an idele `a ∈ 𝕀_K` is the norm `∏_{g ∈ Gal(L/K)} g · b` of an idele of
`L` times the base change of a principal idele of `K`, then `∏_p Frob_p ^ ord_p(a) = 1`.

At a place `v`, pick `w` above it.  The extension is unramified, so `ord_w` of a base change is
`ord_v`, and the equation reads

`ord_v(a) - ord_v(y) = ord_w(∏_g g · b) = ∑_{g} ord_{g⁻¹ w}(b)`.

The summand is unchanged when `g` is multiplied on the right by an element of the decomposition
group `D_w = Stab(w)` — this uses that `Gal(L/K)` is **abelian** — so `#D_w` divides the sum
(`Subgroup.card_dvd_sum_of_mul_mem`).  And `Frob_v ^ #D_w = 1`
(`NumberField.frobAt_pow_card_stabilizer`).  Hence `Frob_v ^ ord_v(a) = Frob_v ^ ord_v(y)` at
every `v`, and the two Frobenius products agree; the second is `1` by Artin reciprocity. -/
theorem frobIdeleHom_eq_one_of_baseChange_eq (hrec : IsArtinReciprocal K L)
    (a : IdeleGroup (𝓞 K) K) (b : IdeleGroup (𝓞 L) L) (y : Kˣ)
    (hab : IdeleGroup.baseChange K L a
      = (∏ g : L ≃ₐ[K] L, g • b)
        * IdeleGroup.baseChange K L (IdeleGroup.principalEmbedding (𝓞 K) K y)) :
    frobIdeleHom K L a = 1 := by
  set P := IdeleGroup.principalEmbedding (𝓞 K) K y with hP
  have key : ∀ v : HeightOneSpectrum (𝓞 K),
      frobAt (F := K) (K := L) v ^ (IdeleGroup.ord a v - IdeleGroup.ord P v) = 1 := by
    intro v
    obtain ⟨w, hw⟩ := exists_heightOneSpectrum_under_eq' K L v
    have hunder : HeightOneSpectrum.under (𝓞 K) w = v := HeightOneSpectrum.ext hw
    have he : (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal = 1 :=
      ramificationIdx'_under_eq_one_of_isUnramifiedEverywhere w
    have h1 : IdeleGroup.ord (IdeleGroup.baseChange K L a) w = IdeleGroup.ord a v := by
      rw [IdeleGroup.ord_baseChange_of_ramificationIdx_eq_one a w he, hunder]
    have h2 : IdeleGroup.ord (IdeleGroup.baseChange K L P) w = IdeleGroup.ord P v := by
      rw [IdeleGroup.ord_baseChange_of_ramificationIdx_eq_one P w he, hunder]
    have h3 : IdeleGroup.ord a v - IdeleGroup.ord P v
        = ∑ g : L ≃ₐ[K] L, IdeleGroup.ord b (g⁻¹ • w) := by
      have hc := congrArg (fun u : IdeleGroup (𝓞 L) L ↦ IdeleGroup.ord u w) hab
      simp only [IdeleGroup.ord_mul] at hc
      rw [h1, h2] at hc
      rw [hc, add_sub_cancel_right, IdeleGroup.ord_prod]
      exact Finset.sum_congr rfl fun g _ ↦ IdeleGroup.ord_smul' g b w
    have hdvd : (Nat.card (stabilizer (L ≃ₐ[K] L) w) : ℤ)
        ∣ (IdeleGroup.ord a v - IdeleGroup.ord P v) := by
      rw [h3]
      refine Subgroup.card_dvd_sum_of_mul_mem _ _ fun g d hd ↦ ?_
      congr 1
      rw [mul_inv_rev, mul_comm' d⁻¹, mul_smul,
        show d⁻¹ • w = w from (stabilizer (L ≃ₐ[K] L) w).inv_mem hd]
    obtain ⟨m, hm⟩ := hdvd
    rw [hm, zpow_mul, zpow_natCast, frobAt_pow_card_stabilizer v w hw, one_zpow]
  have hPa : frobIdeleHom K L a = frobIdeleHom K L P := by
    rw [frobIdeleHom_apply, frobIdeleHom_apply]
    refine finprod_congr fun v ↦ ?_
    have h := key v
    rw [zpow_sub] at h
    exact mul_inv_eq_one.1 h
  rw [hPa, hP]
  exact (isArtinReciprocal_iff_frobIdeleHom K L).1 hrec y

end NumberField

/-! ## The reduction of a norm class to the local–global computation -/

namespace NumberField

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.galIdeleClassMulDistribMulAction
  CyclicTate.Additive.distribMulActionOfMulDistrib

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L]
  [Algebra K L] [IsAbelianGalois K L] [IsUnramifiedEverywhere K L]

omit [NumberField K] [IsAbelianGalois K L] [IsUnramifiedEverywhere K L] in
/-- The class map commutes with the Galois action. -/
theorem mk_smul_idele (σ : L ≃ₐ[K] L) (u : IdeleGroup (𝓞 L) L) :
    IdeleClassGroup.mk (𝓞 L) L (σ • u) = σ • IdeleClassGroup.mk (𝓞 L) L u :=
  (galIdeleClassAut_mk σ u).symm

omit [IsAbelianGalois K L] [IsUnramifiedEverywhere K L] in
/-- **The norm idele `∏_{g} g · b` is `Gal(L/K)`-invariant.** -/
theorem smul_prod_smul (σ : L ≃ₐ[K] L) (b : IdeleGroup (𝓞 L) L) :
    σ • (∏ g : L ≃ₐ[K] L, g • b) = ∏ g : L ≃ₐ[K] L, g • b := by
  show galIdeleAut K L σ (∏ g : L ≃ₐ[K] L, g • b) = _
  rw [map_prod]
  exact Fintype.prod_equiv (Equiv.mulLeft σ) _ _ fun g ↦ (mul_smul σ g b).symm

/-- **Artin reciprocity implies that the reciprocity map on the idele class group kills the
norms from `C_L`.**

This is the local half of the reciprocity law, obtained here without any further hypothesis:
if `c ∈ C_K` becomes a norm in `C_L`, lift it to an idele `a`, lift the norm to `∏_g g · b`,
and observe that the discrepancy `z ∈ Lˣ` between `a_L` and `∏_g g · b` is fixed by the whole
Galois group, hence lies in `Kˣ`.  The computation
`NumberField.frobIdeleHom_eq_one_of_baseChange_eq` then applies. -/
theorem killsNorms_artinIdeleClassMap (hrec : IsArtinReciprocal K L) :
    KillsNorms (artinIdeleClassMap K L hrec) (L := L) := by
  intro c hc
  obtain ⟨d, hd⟩ := (IdeleClassGroup.mem_normSubgroup_iff_prod c).1 hc
  obtain ⟨a, ha⟩ := IdeleClassGroup.mk_surjective (𝓞 K) K (Additive.toMul c)
  obtain ⟨b, hb⟩ := IdeleClassGroup.mk_surjective (𝓞 L) L d
  have hmk : IdeleClassGroup.mk (𝓞 L) L (∏ g : L ≃ₐ[K] L, g • b)
      = IdeleClassGroup.mk (𝓞 L) L (IdeleGroup.baseChange K L a) := by
    rw [map_prod]
    calc ∏ g : L ≃ₐ[K] L, IdeleClassGroup.mk (𝓞 L) L (g • b)
        = ∏ g : L ≃ₐ[K] L, g • d := by
          exact Finset.prod_congr rfl fun g _ ↦ by rw [mk_smul_idele, hb]
      _ = IdeleClassGroup.baseChange K L (Additive.toMul c) := hd
      _ = IdeleClassGroup.mk (𝓞 L) L (IdeleGroup.baseChange K L a) := by
          rw [← ha, IdeleClassGroup.baseChange_mk]
  obtain ⟨z, hz⟩ := (IdeleClassGroup.mk_eq_mk_iff (𝓞 L) L).1 hmk
  -- `z` is fixed by the Galois group, hence comes from `K`
  have hfix : ∀ σ : L ≃ₐ[K] L, σ (z : L) = (z : L) := by
    intro σ
    have h1 : σ • (IdeleGroup.principalEmbedding (𝓞 L) L z)
        = IdeleGroup.principalEmbedding (𝓞 L) L z := by
      have h2 : IdeleGroup.principalEmbedding (𝓞 L) L z
          = IdeleGroup.baseChange K L a * (∏ g : L ≃ₐ[K] L, g • b)⁻¹ := by
        rw [← hz]; group
      rw [h2]
      show galIdeleAut K L σ _ = _
      rw [map_mul, map_inv, IdeleGroup.galIdeleAut_baseChange]
      congr 1
      exact congrArg (·⁻¹) (smul_prod_smul σ b)
    have h3 : IdeleGroup.principalEmbedding (𝓞 L) L
          (Units.mapEquiv (galToRingAut K L σ).toMulEquiv z)
        = IdeleGroup.principalEmbedding (𝓞 L) L z := by
      rw [← ideleAut_principalEmbedding (galToRingAut K L σ) z]
      exact h1
    exact congrArg (Units.val) (IdeleGroup.principalEmbedding_injective (𝓞 L) L h3)
  obtain ⟨y₀, hy₀⟩ := IntermediateField.mem_bot.1
    ((IsGalois.mem_bot_iff_fixed (F := K) (z : L)).2 hfix)
  have hy₀0 : y₀ ≠ 0 := by
    rintro rfl
    exact z.ne_zero (by rw [← hy₀, map_zero])
  have hzy : Units.map (algebraMap K L : K →* L) (Units.mk0 y₀ hy₀0) = z :=
    Units.ext (by simpa using hy₀)
  rw [← ha, artinIdeleClassMap_mk]
  refine frobIdeleHom_eq_one_of_baseChange_eq hrec a b (Units.mk0 y₀ hy₀0) ?_
  rw [IdeleGroup.baseChange_principalEmbedding, hzy, ← hz, mul_comm]

end NumberField
