/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.TameInjective
public import Iwasawalib.NumberTheory.LocalCFT.ResidueFrobenius
public import Iwasawalib.NumberTheory.LocalCFT.Inertia

@[expose] public section

/-!
# Tame inertia of an abelian extension of number fields is killed by `N(v) - 1`

Let `L / K` be a Galois extension of number fields, `w` a prime of `𝓞 L` lying over the prime
`v` of `𝓞 K`, and `O_w = w.adicCompletionIntegers L` the valuation ring of the completion
`L_w`.  `Iwasawalib/NumberTheory/LocalCFT/TameInjective.lean` proves, for an abstract discrete
valuation ring `B`, that an automorphism `σ` of `B` which acts trivially on the residue field,
has finite order invertible in `B` (tameness), and commutes with an automorphism inducing
`x ↦ x ^ q` on the residue field, satisfies `orderOf σ ∣ q - 1` (`LocalCFT.orderOf_dvd_sub_one`).
This file feeds that theorem with `B = O_w` and the action of the decomposition group `D_w`
(`NumberField.decompositionIntegersMulSemiringAction`):

* the action `D_w → RingAut O_w` is injective (`NumberField.decompositionIntegersRingAut_injective`),
  so a conclusion about the image of `σ` in `RingAut O_w` is a conclusion about `σ` itself;
* an element of Mathlib's global inertia group `w.asIdeal.inertia Gal(L/K)` acts trivially on
  the residue field of `O_w` (`NumberField.decompositionIntegersRingAut_mem_inertiaAut`);
* Mathlib's arithmetic Frobenius `NumberField.arithFrobDecomposition` induces `x ↦ x ^ N(v)` on
  the residue field of `O_w`, where `N(v) = Nat.card (𝓞 K ⧸ v.asIdeal)`
  (`NumberField.residue_decompositionIntegersRingAut_arithFrobDecomposition`);
* a natural number outside `w` is a unit of `O_w` (`NumberField.isUnit_natCast_integers_of_notMem`).

When `Gal(L/K)` is abelian the Frobenius commutes with everything, and the main theorem
`NumberField.pow_card_quotient_sub_one_eq_one_of_mem_inertia` follows: an element `σ` of the
inertia group of `w` with `σ ^ N = 1` for some `N ∉ w` satisfies `σ ^ (N(v) - 1) = 1`.  The
hypothesis `(N : 𝓞 L) ∉ w.asIdeal` is exactly tameness; no assumption on the ramification
index of `w` over `v` is made.

The consumer is `Iwasawalib/NumberTheory/ZpExtension/TameLocalExponent.lean`, where `L = Kₙ` is a
layer of a `ℤₚ`-extension, `N = p ^ (n · #ι)` and `p ∉ w`.

## Main statements

* `NumberField.decompositionIntegersRingAut`: the action of `D_w` on `O_w` as a homomorphism
  `D_w →* RingAut O_w`.
* `NumberField.decompositionIntegersRingAut_injective`: it is injective.
* `NumberField.decompositionIntegersRingAut_mem_inertiaAut`: the global inertia group lands in
  `LocalCFT.inertiaAut O_w`.
* `NumberField.residue_decompositionIntegersRingAut_arithFrobDecomposition`: the arithmetic
  Frobenius is a `N(v)`-Frobenius on the residue field of `O_w`.
* `NumberField.isUnit_natCast_integers_of_notMem`: `N ∉ w` is a unit of `O_w`.
* `NumberField.one_lt_card_quotient`: `1 < N(v)`.
* `NumberField.pow_card_quotient_sub_one_eq_one_of_mem_inertia`: **`σ ^ (N(v) - 1) = 1`** for
  tame inertia elements of an abelian extension.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField IsLocalRing

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] decompositionIntegersMulSemiringAction
  IsLocalRing.residueMulSemiringAction

/-- The action of the decomposition group `D_w` on the valuation ring `O_w` of `L_w`
(`NumberField.decompositionIntegersMulSemiringAction`), as a group homomorphism
`D_w →* RingAut O_w`. -/
abbrev decompositionIntegersRingAut :
    decompositionGroup K L w →* RingAut (LocalCFT.integers (F := w.adicCompletion L)) :=
  MulSemiringAction.toRingEquiv (decompositionGroup K L w)
    (LocalCFT.integers (F := w.adicCompletion L))

/-- The `𝓞 L`-algebra structure of `O_w`, in the `LocalCFT.integers` form. -/
@[instance_reducible] local instance algebraIntegers :
    Algebra (𝓞 L) (LocalCFT.integers (F := w.adicCompletion L)) :=
  inferInstanceAs (Algebra (𝓞 L) (w.adicCompletionIntegers L))

omit [NumberField K] [IsGalois K L] in
/-- The action of `D_w` on `O_w` restricts, on the image of `𝓞 L`, to the action of the
underlying element of `Gal(L/K)` on `𝓞 L`. -/
theorem decomposition_smul_algebraMap_integers (d : decompositionGroup K L w) (a : 𝓞 L) :
    d • algebraMap (𝓞 L) (LocalCFT.integers (F := w.adicCompletion L)) a
      = algebraMap (𝓞 L) (LocalCFT.integers (F := w.adicCompletion L))
        ((d : L ≃ₐ[K] L) • a) := by
  refine Subtype.ext ?_
  show d • ((algebraMap (𝓞 L) L a : L) : w.adicCompletion L)
    = ((algebraMap (𝓞 L) L ((d : L ≃ₐ[K] L) • a) : L) : w.adicCompletion L)
  rw [decomposition_smul_coe]
  exact congrArg (fun x : L ↦ ((x : w.adicCompletion L)))
    (coe_smul_ringOfIntegers (d : L ≃ₐ[K] L) a).symm

omit [NumberField K] [IsGalois K L] in
/-- If `b : O_w` and `a : 𝓞 L` have the same residue, then so do `d • b` and `d • a`. -/
theorem residue_decomposition_smul_of_residue_eq (d : decompositionGroup K L w)
    (b : LocalCFT.integers (F := w.adicCompletion L)) (a : 𝓞 L)
    (h : residue (LocalCFT.integers (F := w.adicCompletion L)) b
      = residue _ (algebraMap (𝓞 L) (LocalCFT.integers (F := w.adicCompletion L)) a)) :
    residue (LocalCFT.integers (F := w.adicCompletion L)) (d • b)
      = residue _ (algebraMap (𝓞 L) (LocalCFT.integers (F := w.adicCompletion L))
        ((d : L ≃ₐ[K] L) • a)) := by
  rw [← decomposition_smul_algebraMap_integers]
  show d • residue (LocalCFT.integers (F := w.adicCompletion L)) b
    = d • residue _ (algebraMap (𝓞 L) (LocalCFT.integers (F := w.adicCompletion L)) a)
  rw [h]

/-- **The local action is faithful.**  `D_w → RingAut O_w` is injective: an element of the
decomposition group fixing `O_w` pointwise fixes `𝓞 L`, hence `L`, pointwise. -/
theorem decompositionIntegersRingAut_injective :
    Function.Injective (decompositionIntegersRingAut (K := K) w) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  have hfix : ∀ a : 𝓞 L, (d : L ≃ₐ[K] L) (algebraMap (𝓞 L) L a) = algebraMap (𝓞 L) L a := by
    intro a
    have h1 : d • algebraMap (𝓞 L) (LocalCFT.integers (F := w.adicCompletion L)) a
        = algebraMap (𝓞 L) (LocalCFT.integers (F := w.adicCompletion L)) a :=
      congrArg (fun f : RingAut (LocalCFT.integers (F := w.adicCompletion L)) ↦
        f (algebraMap (𝓞 L) (LocalCFT.integers (F := w.adicCompletion L)) a)) hd
    rw [decomposition_smul_algebraMap_integers] at h1
    have h2 := congrArg (fun x : LocalCFT.integers (F := w.adicCompletion L) ↦
      (x : w.adicCompletion L)) h1
    have h3 : algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L ((d : L ≃ₐ[K] L) • a))
        = algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L a) := h2
    have h4 := (algebraMap L (w.adicCompletion L)).injective h3
    exact (coe_smul_ringOfIntegers (d : L ≃ₐ[K] L) a).symm.trans h4
  refine Subtype.ext ?_
  refine AlgEquiv.ext fun x ↦ ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  show (d : L ≃ₐ[K] L) (algebraMap (𝓞 L) L a / algebraMap (𝓞 L) L b)
    = algebraMap (𝓞 L) L a / algebraMap (𝓞 L) L b
  rw [map_div₀, hfix, hfix]

/-- **Global inertia acts trivially on the local residue field.**  An element of `D_w` whose
underlying automorphism lies in Mathlib's inertia group `w.asIdeal.inertia Gal(L/K)` acts as
the identity on the residue field of `O_w`, i.e. lies in `LocalCFT.inertiaAut O_w`. -/
theorem decompositionIntegersRingAut_mem_inertiaAut (d : decompositionGroup K L w)
    (hd : (d : L ≃ₐ[K] L) ∈ w.asIdeal.inertia (L ≃ₐ[K] L)) :
    decompositionIntegersRingAut (K := K) w d ∈
      LocalCFT.inertiaAut (LocalCFT.integers (F := w.adicCompletion L)) := by
  rw [LocalCFT.mem_inertiaAut]
  intro b
  obtain ⟨a, ha⟩ := residueFieldHom_surjective L w
    (residue (LocalCFT.integers (F := w.adicCompletion L)) b)
  have key := residue_decomposition_smul_of_residue_eq (K := K) w d b a ha.symm
  refine key.trans (Eq.trans ?_ ha)
  show residueFieldHom L w ((d : L ≃ₐ[K] L) • a) = residueFieldHom L w a
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ker_residueFieldHom]
  exact hd a

/-- **The arithmetic Frobenius is a `N(v)`-Frobenius on the local residue field.**  The action
of `NumberField.arithFrobDecomposition` on `O_w` induces `x ↦ x ^ N(v)` on the residue field of
`O_w`, where `N(v) = Nat.card (𝓞 K ⧸ v.asIdeal)`. -/
theorem residue_decompositionIntegersRingAut_arithFrobDecomposition
    (b : LocalCFT.integers (F := w.adicCompletion L)) :
    residue _ (decompositionIntegersRingAut (K := K) w (arithFrobDecomposition (K := K) w) b)
      = residue _ b ^ Nat.card (𝓞 K ⧸ v.asIdeal) := by
  obtain ⟨a, ha⟩ := residueFieldHom_surjective L w
    (residue (LocalCFT.integers (F := w.adicCompletion L)) b)
  have key := residue_decomposition_smul_of_residue_eq (K := K) w
    (arithFrobDecomposition (K := K) w) b a ha.symm
  refine key.trans ?_
  rw [← ha]
  have hfrob := (IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal).mk_apply a
  rw [Nat.card_congr
    (Ideal.quotEquivOfEq (Ideal.over_def w.asIdeal v.asIdeal).symm).toEquiv] at hfrob
  have h2 := congrArg (w.quotientEquivResidueField L) hfrob
  rw [map_pow] at h2
  exact h2

/-- A natural number `N` with `(N : 𝓞 L) ∉ w` is a unit of `O_w`.  This is the tameness input
of `LocalCFT.orderOf_dvd_sub_one`. -/
theorem isUnit_natCast_integers_of_notMem {N : ℕ} (hN : (N : 𝓞 L) ∉ w.asIdeal) :
    IsUnit ((N : ℕ) : LocalCFT.integers (F := w.adicCompletion L)) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  intro h0
  apply hN
  rw [← ker_residueFieldHom L w, RingHom.mem_ker, map_natCast]
  rw [map_natCast] at h0
  exact h0

/-- The residue field `𝓞 K ⧸ v` has more than one element, so `N(v) - 1 ≠ 0`. -/
theorem one_lt_card_quotient : 1 < Nat.card (𝓞 K ⧸ v.asIdeal) := by
  exact Finite.one_lt_card_iff_nontrivial.2 inferInstance

/-- **Tame inertia of an abelian extension is killed by `N(v) - 1`.**  Let `L / K` be an abelian
extension of number fields, `w | v` a prime of `𝓞 L`, and `σ ∈ w.asIdeal.inertia Gal(L/K)` with
`σ ^ N = 1` for a natural number `N` outside `w` (tameness).  Then `σ ^ (N(v) - 1) = 1`, where
`N(v) = Nat.card (𝓞 K ⧸ v.asIdeal)`.  This is `LocalCFT.orderOf_dvd_sub_one` applied to the
image of `σ` in `RingAut O_w`, with the arithmetic Frobenius as the commuting `N(v)`-Frobenius,
transported back along `NumberField.decompositionIntegersRingAut_injective`. -/
theorem pow_card_quotient_sub_one_eq_one_of_mem_inertia [IsMulCommutative (L ≃ₐ[K] L)]
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ w.asIdeal.inertia (L ≃ₐ[K] L))
    {N : ℕ} (hσN : σ ^ N = 1) (hN : (N : 𝓞 L) ∉ w.asIdeal) :
    σ ^ (Nat.card (𝓞 K ⧸ v.asIdeal) - 1) = 1 := by
  have hmem : σ ∈ decompositionGroup K L w := by
    rw [decompositionGroup_eq_stabilizer (K := K) w]
    exact Ideal.inertia_le_stabilizer w.asIdeal hσ
  set d : decompositionGroup K L w := ⟨σ, hmem⟩ with hd
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (LocalCFT.integers (F := w.adicCompletion L))
  have hdN : d ^ N = 1 := Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hσN)
  have hcomm : arithFrobDecomposition (K := K) w * d = d * arithFrobDecomposition (K := K) w :=
    Subtype.ext (IsMulCommutative.is_comm.comm _ _)
  have hdvd := LocalCFT.orderOf_dvd_sub_one hπ
    (σ := decompositionIntegersRingAut (K := K) w d)
    (τ := decompositionIntegersRingAut (K := K) w (arithFrobDecomposition (K := K) w))
    (decompositionIntegersRingAut_mem_inertiaAut w d hσ)
    (n := N) (by rw [← map_pow, hdN, map_one])
    (isUnit_natCast_integers_of_notMem w hN)
    (q := Nat.card (𝓞 K ⧸ v.asIdeal)) (one_lt_card_quotient v).le
    (residue_decompositionIntegersRingAut_arithFrobDecomposition v w)
    (by rw [← map_mul, ← map_mul, hcomm])
  have hpow := orderOf_dvd_iff_pow_eq_one.1 hdvd
  rw [← map_pow] at hpow
  have hd1 := (injective_iff_map_eq_one _).1
    (decompositionIntegersRingAut_injective (K := K) w) _ hpow
  have := congrArg (fun x : decompositionGroup K L w ↦ (x : L ≃ₐ[K] L)) hd1
  simpa [SubmonoidClass.coe_pow] using this

end NumberField
