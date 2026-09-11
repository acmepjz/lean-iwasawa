/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.ArchimedeanPowerIndex
public import Iwasawalib.NumberTheory.CFT.LocalPowerIndexProduct

@[expose] public section

/-!
# The index of a componentwise subgroup of a finite product

The semilocal splitting of the `S`-ideles (`NumberField.finiteSIdeleSemilocalEquiv`) turns
`𝕀_{K,S}` into a finite product of local factors, but the *index* bookkeeping that the local
factor of Chevalley's count needs — the index of a componentwise subgroup of a finite product
is the product of the local indices — was missing.  This file supplies it, in the form used
by `PowerIndex.powIndex`.

Mathlib's `Subgroup.index_pi` is stated only for a *constant* family of groups
`H : ι → Subgroup G`; the local factors `K_v^×` are a genuinely dependent family, so the
dependent version `Subgroup.index_pi'` is proved here (with Mathlib's proof, which never uses
constancy).

The archimedean values come from `Iwasawalib/NumberTheory/CFT/ArchimedeanPowerIndex.lean` and
the finite ones from `Iwasawalib/NumberTheory/CFT/LocalPowerIndexProduct.lean`, so the last
theorem below assembles the complete local factor for an odd exponent.

## Main statements

* `Subgroup.index_pi'`, `AddSubgroup.index_pi'` : the dependent form of `Subgroup.index_pi`.
* `PowerIndex.nsmul_range_pi`, `PowerIndex.nsmul_range_prod` : the subgroup of `n`-th
  multiples of a product is the product of the subgroups of `n`-th multiples.
* `PowerIndex.powIndex_pi`, `PowerIndex.powIndex_pi_mul`, `PowerIndex.powIndex_prod`,
  `PowerIndex.powIndex_prod_mul` : `[∏ A i : n ∏ A i] = ∏ [A i : n A i]`, additively and
  multiplicatively, for a finite product and for a binary product.
* `NumberField.powIndex_pi_adicCompletion_units` : the index of the componentwise `n`-th
  powers in `∏_{v ∈ S} K_v^×` is `∏_{v ∈ S} [K_v^× : (K_v^×)^n]`.
* `NumberField.powIndex_pi_completion_units_of_odd`,
  `NumberField.powIndex_pi_completion_units_of_even` : the archimedean factor is `1` for odd
  `n`, and `2 ^ r₁` for even `n ≠ 0`.
* `NumberField.powIndex_local_units_of_isPrimitiveRoot_of_odd` : the complete local factor
  `n ^ (2 #S) · n ^ [K : ℚ]` for odd `n` with `μ_n ⊆ K`.
-/

noncomputable section

open PowerIndex

/-! ## The index of a componentwise subgroup -/

namespace Subgroup

/-- **The index of a componentwise subgroup of a finite product is the product of the
indices.**  Mathlib's `Subgroup.index_pi` states this only for a constant family of groups;
this is the dependent version, with the same proof. -/
@[to_additive]
theorem index_pi' {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

end Subgroup

/-! ## `powIndex` of a finite product -/

namespace PowerIndex

variable {ι : Type*} (n : ℕ)

/-- The subgroup of `n`-th multiples of a product is the product of the subgroups of `n`-th
multiples: this needs no choice, since a preimage can be chosen coordinatewise. -/
theorem nsmul_range_pi (A : ι → Type*) [∀ i, AddCommGroup (A i)] :
    (nsmulAddMonoidHom (α := ∀ i, A i) n).range =
      AddSubgroup.pi Set.univ (fun i ↦ (nsmulAddMonoidHom (α := A i) n).range) := by
  ext x
  simp only [mem_nsmul_range, AddSubgroup.mem_pi, Set.mem_univ, forall_const]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext hy⟩

variable [Fintype ι]

/-- **`[∏ A i : n ∏ A i] = ∏ [A i : n A i]`.** -/
theorem powIndex_pi (A : ι → Type*) [∀ i, AddCommGroup (A i)] :
    powIndex n (∀ i, A i) = ∏ i, powIndex n (A i) := by
  rw [powIndex, nsmul_range_pi n A, AddSubgroup.index_pi']
  rfl

/-- The multiplicative form of `PowerIndex.powIndex_pi`:
`[∏ G i : (∏ G i)ⁿ] = ∏ [G i : (G i)ⁿ]`. -/
theorem powIndex_pi_mul (G : ι → Type*) [∀ i, CommGroup (G i)] :
    powIndex n (Additive (∀ i, G i)) = ∏ i, powIndex n (Additive (G i)) := by
  rw [powIndex_congr n (AddEquiv.mk (Equiv.refl (Additive (∀ i, G i))) (fun _ _ ↦ rfl) :
    Additive (∀ i, G i) ≃+ (∀ i, Additive (G i)))]
  exact powIndex_pi n fun i ↦ Additive (G i)

/-- The subgroup of `n`-th multiples of a binary product. -/
theorem nsmul_range_prod (A B : Type*) [AddCommGroup A] [AddCommGroup B] :
    (nsmulAddMonoidHom (α := A × B) n).range =
      (nsmulAddMonoidHom (α := A) n).range.prod (nsmulAddMonoidHom (α := B) n).range := by
  ext x
  simp only [mem_nsmul_range, AddSubgroup.mem_prod]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.1, rfl⟩, ⟨y.2, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(a, b), Prod.ext ha hb⟩

/-- **`[A × B : n(A × B)] = [A : nA] · [B : nB]`.** -/
theorem powIndex_prod (A B : Type*) [AddCommGroup A] [AddCommGroup B] :
    powIndex n (A × B) = powIndex n A * powIndex n B := by
  rw [powIndex, nsmul_range_prod n A B, AddSubgroup.index_prod]
  rfl

/-- The multiplicative form of `PowerIndex.powIndex_prod`. -/
theorem powIndex_prod_mul (G H : Type*) [CommGroup G] [CommGroup H] :
    powIndex n (Additive (G × H)) = powIndex n (Additive G) * powIndex n (Additive H) := by
  rw [powIndex_congr n (AddEquiv.mk (Equiv.refl (Additive (G × H))) (fun _ _ ↦ rfl) :
    Additive (G × H) ≃+ (Additive G × Additive H))]
  exact powIndex_prod n (Additive G) (Additive H)

end PowerIndex

/-! ## The local factors of a number field -/

namespace NumberField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum PowerIndex

variable (K : Type*) [Field K] [NumberField K] {n : ℕ}

/-- **The index of the componentwise `n`-th powers in `∏_{v ∈ S} K_v^×`.**  This is the
bookkeeping that turns the semilocal splitting of the `S`-ideles into the local product
`∏_{v ∈ S} [K_v^× : (K_v^×)^n]` computed in
`Iwasawalib/NumberTheory/CFT/LocalPowerIndexProduct.lean`. -/
theorem powIndex_pi_adicCompletion_units (S : Finset (HeightOneSpectrum (𝓞 K))) :
    powIndex n (Additive (∀ v : S, ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ))
      = ∏ v ∈ S, powIndex n (Additive (v.adicCompletion K)ˣ) := by
  rw [powIndex_pi_mul n fun v : S ↦ ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ]
  exact Finset.prod_coe_sort S fun v ↦ powIndex n (Additive (v.adicCompletion K)ˣ)

/-- **The archimedean local factor for an odd exponent is trivial.** -/
theorem powIndex_pi_completion_units_of_odd (hn : Odd n) :
    powIndex n (Additive (∀ v : InfinitePlace K, v.Completionˣ)) = 1 := by
  rw [powIndex_pi_mul n fun v : InfinitePlace K ↦ v.Completionˣ]
  refine Finset.prod_eq_one fun v _ ↦ ?_
  rcases v.isReal_or_isComplex with hv | hv
  · exact InfinitePlace.powIndex_completion_units_of_isReal_of_odd hv hn
  · exact InfinitePlace.powIndex_completion_units_of_isComplex hv
      (by rintro rfl; simp at hn)

open scoped Classical in
/-- **The archimedean local factor for an even exponent is `2` to the number of real
places.** -/
theorem powIndex_pi_completion_units_of_even (hn : Even n) (hn0 : n ≠ 0) :
    powIndex n (Additive (∀ v : InfinitePlace K, v.Completionˣ))
      = 2 ^ InfinitePlace.nrRealPlaces K := by
  rw [powIndex_pi_mul n fun v : InfinitePlace K ↦ v.Completionˣ,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun v : InfinitePlace K ↦ v.IsReal)]
  have h₁ : ∀ v ∈ Finset.univ.filter (fun v : InfinitePlace K ↦ v.IsReal),
      powIndex n (Additive v.Completionˣ) = 2 := by
    intro v hv
    exact InfinitePlace.powIndex_completion_units_of_isReal_of_even
      (Finset.mem_filter.1 hv).2 hn hn0
  have h₂ : ∀ v ∈ Finset.univ.filter (fun v : InfinitePlace K ↦ ¬ v.IsReal),
      powIndex n (Additive v.Completionˣ) = 1 := by
    intro v hv
    exact InfinitePlace.powIndex_completion_units_of_isComplex
      (InfinitePlace.not_isReal_iff_isComplex.1 (Finset.mem_filter.1 hv).2) hn0
  rw [Finset.prod_congr rfl h₁, Finset.prod_congr rfl h₂, Finset.prod_const,
    Finset.prod_const_one, mul_one, InfinitePlace.nrRealPlaces, Fintype.card_subtype]

end NumberField

namespace NumberField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum PowerIndex

variable (K : Type*) [Field K] [NumberField K] {n : ℕ}

/-- **The full local factor of Chevalley's count, for an odd exponent.**

If `K` contains a primitive `n`-th root of unity with `n` odd, and `S` contains every finite
place dividing `n`, then the index of the componentwise `n`-th powers in the local product
`(∏_{v ∈ S} K_v^×) × (∏_{v ∣ ∞} K_v^×)` is `n ^ (2 #S) · n ^ [K : ℚ]`: the archimedean places
contribute nothing. -/
theorem powIndex_local_units_of_isPrimitiveRoot_of_odd [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (hodd : Odd n) {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : ∀ w : HeightOneSpectrum (𝓞 K), w.ord K ((n : K)) ≠ 0 → w ∈ S) :
    powIndex n (Additive ((∀ v : S, ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ) ×
        (∀ v : InfinitePlace K, v.Completionˣ)))
      = n ^ (2 * S.card) * n ^ (Module.finrank ℚ K) := by
  rw [powIndex_prod_mul, powIndex_pi_adicCompletion_units,
    powIndex_pi_completion_units_of_odd K hodd, mul_one,
    prod_powIndex_adicCompletion_units_of_isPrimitiveRoot hζ hS]

end NumberField
