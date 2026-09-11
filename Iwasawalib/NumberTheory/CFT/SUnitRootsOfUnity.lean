/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.SUnitPowerIndex
public import Iwasawalib.NumberTheory.LocalCFT.LocalPowerIndex
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-!
# The torsion factor of the `S`-unit index is `#μ_n(L)`

`Iwasawalib/NumberTheory/CFT/SUnitPowerIndex.lean` proves
`[O_{L,S}^× : (O_{L,S}^×)^n] = n ^ (#S - 1) · #{x ∈ O_{L,S}^× | x ^ n = 1}` and states the
second factor exactly as it is proved — the `n`-th roots of unity **among the `S`-units** —
noting that the identification with `#μ_n(L)` "is not proved here and is not used".  Chevalley's
count does use it: the factor has to be `ℓ` when `μ_ℓ ⊆ K`, and what one knows is that `K`
contains a primitive `ℓ`-th root of unity, not that the `S`-units do.

This file supplies the identification.  It is elementary: a root of unity `x` has
`v(x) ^ n = v(x ^ n) = 1` in `ℤᵐ⁰`, and the value group `ℤ` is torsion free, so `v(x) = 1` at
*every* finite place — in particular `x` is an `S`-unit for every `S`, including `S = ∅`.

## Main statements

* `PowerIndex.powKer_subgroup_eq` : a subgroup containing all the `n`-torsion of `G` has the
  same `n`-torsion as `G`.
* `NumberField.mem_sUnit_of_pow_eq_one` : every root of unity of `L` is an `S`-unit.
* `NumberField.powKer_sUnit` : `#{x ∈ O_{L,S}^× | x ^ n = 1} = #μ_n(L)`.
* `NumberField.powIndex_sUnit_eq_card_rootsOfUnity` :
  `[O_{L,S}^× : (O_{L,S}^×)^n] = n ^ (#S - 1) · #μ_n(L)`.
* `NumberField.powIndex_sUnit_of_isPrimitiveRoot` : **`[O_{L,S}^× : (O_{L,S}^×)^n] = n ^ #S`**
  when `L` contains a primitive `n`-th root of unity.  This is the factor `ℓ ^ #S` of
  Chevalley's count.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace PowerIndex

/-- **A subgroup containing all the `n`-torsion has the same `n`-torsion as the whole group.** -/
theorem powKer_subgroup_eq {G : Type*} [CommGroup G] (H : Subgroup G) (n : ℕ)
    (h : ∀ x : G, x ^ n = 1 → x ∈ H) :
    powKer n (Additive H) = powKer n (Additive G) := by
  set f : Additive H →+ Additive G := (H.subtype).toAdditive with hf
  have hfinj : Function.Injective f := fun a b hab ↦
    Additive.ofMul.injective (Subtype.ext (congrArg Additive.toMul hab))
  have hmem : ∀ z : Additive H, n • z = 0 ↔ ((Additive.toMul z : H) : G) ^ n = 1 := by
    intro z
    constructor
    · intro hz
      have hz2 := congrArg (fun w : Additive H ↦ ((Additive.toMul w : H) : G)) hz
      simpa [toMul_nsmul] using hz2
    · intro hz
      refine Additive.toMul.injective ?_
      rw [toMul_nsmul, toMul_zero]
      exact Subtype.ext (by simpa using hz)
  have hmapeq : (nsmulAddMonoidHom (α := Additive H) n).ker.map f
      = (nsmulAddMonoidHom (α := Additive G) n).ker := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : n • z = 0 := hz
      rw [mem_nsmul_ker, ← map_nsmul, hz', map_zero]
    · intro hy
      rw [mem_nsmul_ker] at hy
      have hy' : (Additive.toMul y : G) ^ n = 1 := by
        have h2 := congrArg Additive.toMul hy
        rwa [toMul_nsmul, toMul_zero] at h2
      exact ⟨Additive.ofMul (⟨Additive.toMul y, h _ hy'⟩ : H),
        (hmem _).2 hy', rfl⟩
  rw [powKer, powKer, ← hmapeq]
  exact Nat.card_congr (AddSubgroup.equivMapOfInjective _ f hfinj).toEquiv

end PowerIndex

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- **Every root of unity is an `S`-unit**, for every set `S` of finite places (including the
empty set): a root of unity has valuation `1` at every place. -/
theorem mem_sUnit_of_pow_eq_one (T : Set (HeightOneSpectrum (𝓞 L))) {n : ℕ} (hn : n ≠ 0)
    {x : Lˣ} (hx : x ^ n = 1) : x ∈ T.unit L := by
  intro v _
  have hxL : ((x : L)) ^ n = 1 := by
    have := congrArg (fun u : Lˣ ↦ (u : L)) hx
    simpa using this
  have hx0 : ((x : L)) ≠ 0 := x.ne_zero
  have hval : (v.valuation L ((x : L))) ^ n = 1 := by rw [← map_pow, hxL, map_one]
  have hne : v.valuation L ((x : L)) ≠ 0 := valuation_ne_zero hx0
  set a : ℤ := WithZero.log (v.valuation L ((x : L))) with ha
  have hexp : v.valuation L ((x : L)) = exp a := (exp_log hne).symm
  rw [hexp, ← WithZero.exp_nsmul, show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm,
    exp_inj] at hval
  have : a = 0 := by
    simp only [nsmul_eq_mul] at hval
    rcases mul_eq_zero.1 hval with h | h
    · exact absurd (by exact_mod_cast h) hn
    · exact h
  rw [hexp, this, exp_zero]

variable {T : Set (HeightOneSpectrum (𝓞 L))}

/-- **The `n`-torsion of the `S`-units is `μ_n(L)`.** -/
theorem powKer_sUnit {n : ℕ} (hn : n ≠ 0) :
    PowerIndex.powKer n (Additive (T.unit L)) = Nat.card (rootsOfUnity n L) := by
  rw [PowerIndex.powKer_subgroup_eq (T.unit L) n fun x hx ↦ mem_sUnit_of_pow_eq_one T hn hx,
    PowerIndex.powKer_additive_units_eq_card_rootsOfUnity L n]

variable [Fintype T]

/-- **`[O_{L,S}^× : (O_{L,S}^×)^n] = n ^ (#S - 1) · #μ_n(L)`.**

This is `NumberField.powIndex_sUnit` with its second factor identified: the `n`-th roots of
unity *among the `S`-units* are all of the `n`-th roots of unity of `L`. -/
theorem powIndex_sUnit_eq_card_rootsOfUnity {n : ℕ} (hn : n ≠ 0) :
    PowerIndex.powIndex n (Additive (T.unit L))
      = n ^ sRank L T * Nat.card (rootsOfUnity n L) := by
  rw [powIndex_sUnit hn, powKer_sUnit hn]

/-- **`[O_{L,S}^× : (O_{L,S}^×)^n] = n ^ #S`** when `μ_n ⊆ L`.

This is the factor `ℓ ^ #S` of Chevalley's count, for `n = ℓ` and `μ_ℓ ⊆ K`. -/
theorem powIndex_sUnit_of_isPrimitiveRoot {n : ℕ} [NeZero n] {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) :
    PowerIndex.powIndex n (Additive (T.unit L)) = n ^ (sRank L T + 1) := by
  rw [powIndex_sUnit_eq_card_rootsOfUnity (NeZero.ne n), hζ.card_rootsOfUnity, pow_succ]

end NumberField

end
