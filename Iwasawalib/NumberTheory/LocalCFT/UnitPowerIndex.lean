/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.UnitFiltrationGraded
public import Iwasawalib.NumberTheory.LocalCFT.LocalPowerIndex
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

/-!
# The index of `n`-th powers in the units of a complete discretely valued field

`Iwasawalib/NumberTheory/LocalCFT/LocalPowerIndex.lean` reduces the local power index to
`[𝒪^× : (𝒪^×)^n]`, and records that the missing factor is `#μ_n(F) / |n|_F`.  This file supplies
it, unconditionally, in mixed characteristic `(0, p)`.

Write `n = p^a · s` with `p ∤ s`.  The `n`-th power map carries the group of principal units
`U^(m)` of level `m = e + 1` **bijectively** onto `U^(m + a e)`
(`Iwasawalib/NumberTheory/LocalCFT/UnitFiltrationPow.lean`), so

* `U^(m)` has no `n`-torsion, and
* `[U^(m) : (U^(m))^n] = [U^(m) : U^(m + a e)] = q^{a e} = |n|_F^{-1}`,

where `q` is the residue cardinality.  Since `U^(m)` has finite index in `𝒪^×`, the counting
identity `PowerIndex.powIndex_mul_powKer_of_injective` gives

`[𝒪^× : (𝒪^×)^n] = #μ_n(F) · q^{a e}`,  and hence  `[F^× : (F^×)^n] = n · #μ_n(F) · q^{a e}`.

No `p`-adic logarithm is used anywhere.

## Main statements

* `LocalCFT.image_pow_unitFiltration`: `(· ^ n) '' U^(m) = U^(m + a e)`.
* `LocalCFT.powIndex_unitFiltration`: `[U^(m) : (U^(m))^n] = q^{a e}`.
* `LocalCFT.powIndex_integers_units`: **`[𝒪^× : (𝒪^×)^n] = #μ_n(F) · q^{a e}`.**
* `LocalCFT.powIndex_units_eq_card_rootsOfUnity_mul`: **`[F^× : (F^×)^n] = n · #μ_n(F) · q^{a e}`.**
* `LocalCFT.valued_natCast_eq_of_factorization`: `v n = exp (-a e)`, which is the statement
  that `q^{a e} = |n|_F^{-1}`.
* `NumberField.powIndex_adicCompletionIntegers_units`,
  `NumberField.powIndex_adicCompletion_units`: the same at a finite place of a number field.
-/

noncomputable section

open WithZero IsLocalRing PowerIndex

/-! ## Two dictionary lemmas for `PowerIndex` -/

namespace PowerIndex

variable {G : Type*} [CommGroup G] (n : ℕ)

/-- If the subgroup of `n`-th powers of `G` is `H`, then `[G : nG] = [G : H]`. -/
theorem powIndex_additive_eq_index (H : Subgroup G)
    (hH : ∀ x : G, (∃ y : G, y ^ n = x) ↔ x ∈ H) :
    powIndex n (Additive G) = H.index := by
  rw [powIndex, ← Subgroup.index_toAddSubgroup]
  congr 1
  ext x
  rw [Additive.mem_toAddSubgroup]
  exact (mem_nsmul_range_additive G n (x := Additive.toMul x)).trans (hH _)

/-- If `G` has no `n`-torsion then `#(Additive G)[n] = 1`. -/
theorem powKer_additive_eq_one (h : ∀ x : G, x ^ n = 1 → x = 1) :
    powKer n (Additive G) = 1 := by
  rw [powKer, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y ↦ Subtype.ext ?_⟩, ⟨0⟩⟩
  have hx1 : Additive.toMul (x : Additive G) = 1 := h _ ((mem_nsmul_ker_additive G n).1 x.2)
  have hy1 : Additive.toMul (y : Additive G) = 1 := h _ ((mem_nsmul_ker_additive G n).1 y.2)
  exact Additive.toMul.injective (hx1.trans hy1.symm)

end PowerIndex

namespace LocalCFT

variable {F : Type*} [Field F] [hv : Valued F ℤᵐ⁰]

/-! ## Iterated torsion-freeness -/

/-- **No `n^a`-torsion.** -/
theorem IsPowData.eq_one_of_pow_pow_eq_one {n m δ : ℕ} (hd : IsPowData F n m δ)
    {u : (integers (F := F))ˣ} (hu : u ∈ unitFiltration m) (a : ℕ) (h : u ^ (n ^ a) = 1) :
    u = 1 := by
  induction a with
  | zero => simpa using h
  | succ a ih =>
    refine ih ?_
    refine hd.eq_one_of_pow_eq_one (Subgroup.pow_mem _ hu _) ?_
    rw [← pow_mul, ← pow_succ]
    exact h

/-! ## The `n`-th power map on the principal units -/

section Main

variable [CompleteSpace F] {p e m a s : ℕ}

/-- **The `n`-th power map is a bijection `U^(m) → U^(m + a e)`** for `n = p^a · s` with
`p ∤ s`, at any level `m` with `m (p-1) > e`. -/
theorem image_pow_unitFiltration (hp : p.Prime) (hm : 1 ≤ m) (he : 1 ≤ e)
    (hpv : (Valued.v ((p : F)) : ℤᵐ⁰) = exp (-(e : ℤ))) (hme : e < m * (p - 1))
    (hs : Nat.Coprime s p) :
    (fun u : (integers (F := F))ˣ ↦ u ^ (p ^ a * s)) '' (unitFiltration (F := F) m : Set _)
      = (unitFiltration (F := F) (m + a * e) : Set _) := by
  have hd := isPowData_prime (F := F) hp hm hpv hme
  have hds := isPowData_of_valued_eq_one (F := F) (n := s) hm
    (valued_natCast_eq_one_of_coprime he hpv hs)
  have hcomp : (fun u : (integers (F := F))ˣ ↦ u ^ (p ^ a * s))
      = (fun t : (integers (F := F))ˣ ↦ t ^ s) ∘ (fun u : (integers (F := F))ˣ ↦ u ^ (p ^ a)) :=
    funext fun u ↦ by rw [Function.comp_apply, ← pow_mul]
  rw [hcomp, Set.image_comp, hd.image_pow_pow (le_refl m) a,
    hds.image_pow (k := m + a * e) (by omega), Nat.add_zero]

/-- **The principal units `U^(m)` have no `n`-torsion.** -/
theorem eq_one_of_pow_eq_one_unitFiltration (hp : p.Prime) (hm : 1 ≤ m) (he : 1 ≤ e)
    (hpv : (Valued.v ((p : F)) : ℤᵐ⁰) = exp (-(e : ℤ))) (hme : e < m * (p - 1))
    (hs : Nat.Coprime s p) {u : (integers (F := F))ˣ} (hu : u ∈ unitFiltration m)
    (h : u ^ (p ^ a * s) = 1) : u = 1 := by
  have hd := isPowData_prime (F := F) hp hm hpv hme
  have hds := isPowData_of_valued_eq_one (F := F) (n := s) hm
    (valued_natCast_eq_one_of_coprime he hpv hs)
  have h1 : (u ^ (p ^ a)) ^ s = 1 := by rw [← pow_mul]; exact h
  exact hd.eq_one_of_pow_pow_eq_one hu a
    (hds.eq_one_of_pow_eq_one (Subgroup.pow_mem _ hu _) h1)

variable {π : F}

/-- **`[U^(m) : (U^(m))^n] = q^{a e}`.** -/
theorem powIndex_unitFiltration (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (hp : p.Prime)
    (hm : 1 ≤ m) (he : 1 ≤ e) (hpv : (Valued.v ((p : F)) : ℤᵐ⁰) = exp (-(e : ℤ)))
    (hme : e < m * (p - 1)) (hs : Nat.Coprime s p) :
    powIndex (p ^ a * s) (Additive (unitFiltration (F := F) m))
      = Nat.card (ResidueField (integers (F := F))) ^ (a * e) := by
  have himage := image_pow_unitFiltration (F := F) (a := a) hp hm he hpv hme hs
  rw [powIndex_additive_eq_index _
    ((unitFiltration (F := F) (m + a * e)).subgroupOf (unitFiltration (F := F) m)) ?_]
  · rw [← Subgroup.relIndex, relIndex_unitFiltration hπ hm (a * e)]
  · intro x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, rfl⟩
      have hy : ((y : (integers (F := F))ˣ)) ^ (p ^ a * s)
          ∈ (unitFiltration (F := F) (m + a * e) : Set _) := by
        rw [← himage]
        exact ⟨(y : (integers (F := F))ˣ), y.2, rfl⟩
      simpa using hy
    · intro hx
      have hx' : ((x : (integers (F := F))ˣ))
          ∈ (unitFiltration (F := F) (m + a * e) : Set _) := hx
      rw [← himage] at hx'
      obtain ⟨u, hu, huv⟩ := hx'
      refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
      simpa using huv

/-- **The headline isomorphism, at the residue characteristic**: `1 + 𝔪^k ≅ 1 + 𝔪^(k+e)` for
every `k ≥ m` with `m (p-1) > e`.  This is the algebraic substitute for the `p`-adic logarithm
isomorphism `1 + 𝔪^m ≅ 𝔪^m`, and it is what the index computation below actually consumes. -/
def unitFiltrationPowEquiv (hp : p.Prime) (hm : 1 ≤ m)
    (hpv : (Valued.v ((p : F)) : ℤᵐ⁰) = exp (-(e : ℤ))) (hme : e < m * (p - 1)) {k : ℕ}
    (hk : m ≤ k) :
    unitFiltration (F := F) k ≃* unitFiltration (F := F) (k + e) :=
  (isPowData_prime (F := F) hp hm hpv hme).powEquiv hk

@[simp] theorem coe_unitFiltrationPowEquiv (hp : p.Prime) (hm : 1 ≤ m)
    (hpv : (Valued.v ((p : F)) : ℤᵐ⁰) = exp (-(e : ℤ))) (hme : e < m * (p - 1)) {k : ℕ}
    (hk : m ≤ k) (u : unitFiltration (F := F) k) :
    ((unitFiltrationPowEquiv hp hm hpv hme hk u : unitFiltration (F := F) (k + e))
      : (integers (F := F))ˣ) = (u : (integers (F := F))ˣ) ^ p := rfl

/-! ## The inclusion of the principal units -/

variable (F) in
/-- The inclusion `U^(m) → 𝒪^×`, additively. -/
def unitFiltrationIncl (m : ℕ) :
    Additive (unitFiltration (F := F) m) →+ Additive (integers (F := F))ˣ where
  toFun x := Additive.ofMul ((x.toMul : unitFiltration (F := F) m) : (integers (F := F))ˣ)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem unitFiltrationIncl_injective (m : ℕ) :
    Function.Injective (unitFiltrationIncl F m) := by
  intro x y h
  exact Additive.toMul.injective (Subtype.ext (congrArg Additive.toMul h))

theorem finite_quotient_range_unitFiltrationIncl
    [Finite ((integers (F := F))ˣ ⧸ unitFiltration (F := F) m)] :
    Finite (Additive (integers (F := F))ˣ ⧸ (unitFiltrationIncl F m).range) := by
  classical
  refine Finite.of_surjective
    (fun q : (integers (F := F))ˣ ⧸ unitFiltration (F := F) m ↦
      Quotient.liftOn' q
        (fun x : (integers (F := F))ˣ ↦
          (QuotientAddGroup.mk (Additive.ofMul x) :
            Additive (integers (F := F))ˣ ⧸ (unitFiltrationIncl F m).range))
        (fun x y hxy ↦ ?_)) ?_
  · exact QuotientAddGroup.eq.2
      ⟨Additive.ofMul (⟨x⁻¹ * y, (QuotientGroup.leftRel_apply).1 hxy⟩ :
        unitFiltration (F := F) m), rfl⟩
  · intro z
    obtain ⟨A, rfl⟩ := QuotientAddGroup.mk_surjective (s := (unitFiltrationIncl F m).range) z
    exact ⟨QuotientGroup.mk (A.toMul), rfl⟩

/-! ## Anti-vacuity: the image is a proper subgroup -/

/-- **The `n`-th power map on `U^(m)` is not onto** as soon as `a e ≥ 1` and the residue field
has more than one element: its image `U^(m + a e)` has index `q^{a e} > 1` in `U^(m)`.  So
`LocalCFT.image_pow_unitFiltration` is not the vacuous statement that every unit is an `n`-th
power, and the shift by `a e` in it is real. -/
theorem not_le_unitFiltration_of_pos (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (hm : 1 ≤ m)
    (hq : 1 < Nat.card (ResidueField (integers (F := F)))) {j : ℕ} (hj : 1 ≤ j) :
    ¬ (unitFiltration (F := F) m ≤ unitFiltration (F := F) (m + j)) := by
  intro hle
  have hone : (unitFiltration (F := F) (m + j)).relIndex (unitFiltration (F := F) m) = 1 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_one]
    exact Subgroup.subgroupOf_eq_top.2 hle
  rw [relIndex_unitFiltration hπ hm j] at hone
  have : 1 < Nat.card (ResidueField (integers (F := F))) ^ j :=
    Nat.one_lt_pow (by omega) hq
  omega

/-! ## The index of `n`-th powers in `𝒪^×` -/

/-- **`[𝒪^× : (𝒪^×)^n] = #(𝒪^×)[n] · q^{a e}`** for `n = p^a · s` with `p ∤ s`, at a complete
discretely valued field of mixed characteristic `(0, p)` with absolute ramification index `e`
and finite residue field.  The second factor is `|n|_F^{-1}`
(`LocalCFT.valued_natCast_eq_of_factorization`).

This is the factor that `Iwasawalib/NumberTheory/LocalCFT/LocalPowerIndex.lean` was missing. -/
theorem powIndex_integers_units [Finite (ResidueField (integers (F := F)))]
    (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (hp : p.Prime) (he : 1 ≤ e)
    (hpv : (Valued.v ((p : F)) : ℤᵐ⁰) = exp (-(e : ℤ))) (hs : Nat.Coprime s p) (hs0 : s ≠ 0) :
    powIndex (p ^ a * s) (Additive (integers (F := F))ˣ)
      = powKer (p ^ a * s) (Additive (integers (F := F))ˣ)
        * Nat.card (ResidueField (integers (F := F))) ^ (a * e) := by
  set m : ℕ := e + 1 with hmdef
  have hm : 1 ≤ m := by omega
  have hme : e < m * (p - 1) := by
    have h2 : 2 ≤ p := hp.two_le
    have : 1 ≤ p - 1 := by omega
    calc e < m := by omega
      _ = m * 1 := (mul_one m).symm
      _ ≤ m * (p - 1) := Nat.mul_le_mul_left m this
  have hn0 : p ^ a * s ≠ 0 := Nat.mul_ne_zero (pow_ne_zero a hp.pos.ne') hs0
  haveI : Finite ((integers (F := F))ˣ ⧸ unitFiltration (F := F) m) :=
    finite_quotient_unitFiltration hπ m
  haveI := finite_quotient_range_unitFiltrationIncl (F := F) (m := m)
  have hker : powKer (p ^ a * s) (Additive (unitFiltration (F := F) m)) = 1 :=
    powKer_additive_eq_one _ fun x hx ↦ Subtype.ext
      (eq_one_of_pow_eq_one_unitFiltration hp hm he hpv hme hs x.2
        (by simpa using congrArg (fun t : unitFiltration (F := F) m ↦
          (t : (integers (F := F))ˣ)) hx))
  have hmain := powIndex_mul_powKer_of_injective (n := p ^ a * s) hn0
    (unitFiltrationIncl F m) (unitFiltrationIncl_injective m)
  rw [hker, mul_one] at hmain
  rw [← hmain, powIndex_unitFiltration hπ hp hm he hpv hme hs, mul_comm]

/-- **`v n = exp (-(a e))`** for `n = p^a · s` with `p ∤ s`: the factor `q^{a e}` of
`LocalCFT.powIndex_integers_units` is exactly `|n|_F^{-1}`. -/
theorem valued_natCast_eq_of_factorization (hp : p.Prime) (he : 1 ≤ e)
    (hpv : (Valued.v ((p : F)) : ℤᵐ⁰) = exp (-(e : ℤ))) (hs : Nat.Coprime s p) :
    (Valued.v (((p ^ a * s : ℕ) : F)) : ℤᵐ⁰) = exp (-((a * e : ℕ) : ℤ)) := by
  push_cast
  rw [map_mul, map_pow, hpv, valued_natCast_eq_one_of_coprime he hpv hs, mul_one, ← exp_nsmul]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring

/-- **`[F^× : (F^×)^n] = n · #μ_n(F) · q^{a e}`.**  The complete local power index in mixed
characteristic `(0, p)`: the valuation factor `n` of
`LocalCFT.powIndex_units_eq_mul`, the roots of unity, and `|n|_F^{-1} = q^{a e}`. -/
theorem powIndex_units_eq_card_rootsOfUnity_mul [Finite (ResidueField (integers (F := F)))]
    (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (hp : p.Prime) (he : 1 ≤ e)
    (hpv : (Valued.v ((p : F)) : ℤᵐ⁰) = exp (-(e : ℤ))) (hs : Nat.Coprime s p) (hs0 : s ≠ 0) :
    powIndex (p ^ a * s) (Additive Fˣ)
      = (p ^ a * s) * (Nat.card (rootsOfUnity (p ^ a * s) (integers (F := F)))
        * Nat.card (ResidueField (integers (F := F))) ^ (a * e)) := by
  have hn0 : p ^ a * s ≠ 0 := Nat.mul_ne_zero (pow_ne_zero a hp.pos.ne') hs0
  rw [powIndex_units_eq_mul F _ hn0 ⟨π, hπ⟩,
    powIndex_integers_units hπ hp he hpv hs hs0,
    powKer_additive_units_eq_card_rootsOfUnity (integers (F := F)) (p ^ a * s)]

/-! ## The same for an arbitrary `n ≠ 0` -/

section General

variable {n : ℕ}

/-- **`[𝒪^× : (𝒪^×)^n] = #(𝒪^×)[n] · q^{v_p(n) · e}`** for an arbitrary `n ≠ 0`, with the
`p`-adic factorisation of `n` performed internally. -/
theorem powIndex_integers_units_of_ne_zero [Finite (ResidueField (integers (F := F)))]
    (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (hp : p.Prime) (he : 1 ≤ e)
    (hpv : (Valued.v ((p : F)) : ℤᵐ⁰) = exp (-(e : ℤ))) (hn : n ≠ 0) :
    powIndex n (Additive (integers (F := F))ˣ)
      = powKer n (Additive (integers (F := F))ˣ)
        * Nat.card (ResidueField (integers (F := F))) ^ (n.factorization p * e) := by
  have hcop : Nat.Coprime (n / p ^ n.factorization p) p :=
    (Nat.coprime_ordCompl hp hn).symm
  have hs0 : n / p ^ n.factorization p ≠ 0 := (Nat.ordCompl_pos p hn).ne'
  set b : ℕ := n.factorization p with hbdef
  set c : ℕ := n / p ^ b with hcdef
  have hsplit : p ^ b * c = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have h := powIndex_integers_units (a := b) (s := c) hπ hp he hpv hcop hs0
  rwa [hsplit] at h

/-- **`[F^× : (F^×)^n] = n · #μ_n(F) · q^{v_p(n) · e}`** for an arbitrary `n ≠ 0`. -/
theorem powIndex_units_of_ne_zero [Finite (ResidueField (integers (F := F)))]
    (hπ : (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) (hp : p.Prime) (he : 1 ≤ e)
    (hpv : (Valued.v ((p : F)) : ℤᵐ⁰) = exp (-(e : ℤ))) (hn : n ≠ 0) :
    powIndex n (Additive Fˣ)
      = n * (Nat.card (rootsOfUnity n (integers (F := F)))
        * Nat.card (ResidueField (integers (F := F))) ^ (n.factorization p * e)) := by
  rw [powIndex_units_eq_mul F n hn ⟨π, hπ⟩,
    powIndex_integers_units_of_ne_zero hπ hp he hpv hn,
    powKer_additive_units_eq_card_rootsOfUnity (integers (F := F)) n]

end General

end Main

end LocalCFT

/-! ## At a finite place of a number field -/

namespace NumberField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum LocalCFT

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- **The absolute ramification index exists.**  If the residue characteristic `p` lies in `v`
then `v p = exp (-e)` for a unique `e ≥ 1`, the absolute ramification index of `K_v`. -/
theorem exists_valued_natCast_eq_exp {p : ℕ} (hp : (p : 𝓞 K) ∈ v.asIdeal) (hp0 : p ≠ 0) :
    ∃ e : ℕ, 1 ≤ e ∧ (Valued.v ((p : v.adicCompletion K)) : ℤᵐ⁰) = exp (-(e : ℤ)) := by
  have hcast : ((p : v.adicCompletion K)) = algebraMap K (v.adicCompletion K) ((p : K)) :=
    (map_natCast (algebraMap K (v.adicCompletion K)) p).symm
  have hval : (Valued.v ((p : v.adicCompletion K)) : ℤᵐ⁰) = v.valuation K ((p : K)) := by
    rw [hcast]
    exact valuedAdicCompletion_eq_valuation' (v := v) ((p : K))
  have hcoe : (((p : 𝓞 K) : K)) = ((p : K)) := by push_cast; ring
  have hlt : (Valued.v ((p : v.adicCompletion K)) : ℤᵐ⁰) < 1 := by
    rw [hval, ← hcoe]
    exact (v.valuation_lt_one_iff_mem (K := K) ((p : 𝓞 K))).2 hp
  have hK0 : ((p : K)) ≠ 0 := Nat.cast_ne_zero.2 hp0
  have hne : (Valued.v ((p : v.adicCompletion K)) : ℤᵐ⁰) ≠ 0 := by
    rw [hval]
    exact (Valuation.ne_zero_iff _).2 hK0
  obtain ⟨j, hj⟩ : ∃ j : ℤ, (Valued.v ((p : v.adicCompletion K)) : ℤᵐ⁰) = exp j :=
    ⟨log _, (exp_log hne).symm⟩
  rw [hj, show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm, exp_lt_exp] at hlt
  refine ⟨(-j).toNat, by omega, ?_⟩
  rw [hj]
  congr 1
  omega

/-- **`[O_v^× : (O_v^×)^n] = #μ_n(K_v) · q^{a e}`** at a finite place of a number field, for
`n = p^a · s` with `p` the residue characteristic and `p ∤ s`.

This is the factor that `NumberField.powIndex_adicCompletion_units_eq_mul` was missing. -/
theorem powIndex_adicCompletionIntegers_units {p a s e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hpv : (Valued.v ((p : v.adicCompletion K)) : ℤᵐ⁰) = exp (-(e : ℤ)))
    (hs : Nat.Coprime s p) (hs0 : s ≠ 0) :
    PowerIndex.powIndex (p ^ a * s)
        (Additive (LocalCFT.integers (F := v.adicCompletion K))ˣ)
      = Nat.card (rootsOfUnity (p ^ a * s) (LocalCFT.integers (F := v.adicCompletion K)))
        * Nat.card (ResidueField (LocalCFT.integers (F := v.adicCompletion K))) ^ (a * e) := by
  haveI : Finite (ResidueField (LocalCFT.integers (F := v.adicCompletion K))) :=
    HeightOneSpectrum.finite_residueField (F := K) v
  obtain ⟨π, hπ⟩ := valuedAdicCompletion_surjective (K := K) v (exp (-1 : ℤ))
  rw [LocalCFT.powIndex_integers_units (π := π) hπ hp he hpv hs hs0,
    PowerIndex.powKer_additive_units_eq_card_rootsOfUnity
      (LocalCFT.integers (F := v.adicCompletion K)) (p ^ a * s)]

/-- **`[K_v^× : (K_v^×)^n] = n · #μ_n(K_v) · q^{a e}`**, the complete local power index at a
finite place of a number field.  The last factor is `|n|_v^{-1}`. -/
theorem powIndex_adicCompletion_units {p a s e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hpv : (Valued.v ((p : v.adicCompletion K)) : ℤᵐ⁰) = exp (-(e : ℤ)))
    (hs : Nat.Coprime s p) (hs0 : s ≠ 0) :
    PowerIndex.powIndex (p ^ a * s) (Additive (v.adicCompletion K)ˣ)
      = (p ^ a * s)
        * (Nat.card (rootsOfUnity (p ^ a * s) (LocalCFT.integers (F := v.adicCompletion K)))
          * Nat.card (ResidueField (LocalCFT.integers (F := v.adicCompletion K))) ^ (a * e)) := by
  have hn0 : p ^ a * s ≠ 0 := Nat.mul_ne_zero (pow_ne_zero a hp.pos.ne') hs0
  rw [powIndex_adicCompletion_units_eq_mul v (p ^ a * s) hn0,
    powIndex_adicCompletionIntegers_units v hp he hpv hs hs0]

/-- **`[O_v^× : (O_v^×)^n] = #μ_n(K_v) · q^{v_p(n) · e}`** for an arbitrary `n ≠ 0`. -/
theorem powIndex_adicCompletionIntegers_units_of_ne_zero {p e n : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hpv : (Valued.v ((p : v.adicCompletion K)) : ℤᵐ⁰) = exp (-(e : ℤ))) (hn : n ≠ 0) :
    PowerIndex.powIndex n (Additive (LocalCFT.integers (F := v.adicCompletion K))ˣ)
      = Nat.card (rootsOfUnity n (LocalCFT.integers (F := v.adicCompletion K)))
        * Nat.card (ResidueField (LocalCFT.integers (F := v.adicCompletion K)))
            ^ (n.factorization p * e) := by
  haveI : Finite (ResidueField (LocalCFT.integers (F := v.adicCompletion K))) :=
    HeightOneSpectrum.finite_residueField (F := K) v
  obtain ⟨π, hπ⟩ := valuedAdicCompletion_surjective (K := K) v (exp (-1 : ℤ))
  rw [LocalCFT.powIndex_integers_units_of_ne_zero (π := π) hπ hp he hpv hn,
    PowerIndex.powKer_additive_units_eq_card_rootsOfUnity
      (LocalCFT.integers (F := v.adicCompletion K)) n]

/-- **`[K_v^× : (K_v^×)^n] = n · #μ_n(K_v) · q^{v_p(n) · e}`** for an arbitrary `n ≠ 0`.  This
is the complete local power index at a finite place of a number field. -/
theorem powIndex_adicCompletion_units_of_ne_zero {p e n : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hpv : (Valued.v ((p : v.adicCompletion K)) : ℤᵐ⁰) = exp (-(e : ℤ))) (hn : n ≠ 0) :
    PowerIndex.powIndex n (Additive (v.adicCompletion K)ˣ)
      = n * (Nat.card (rootsOfUnity n (LocalCFT.integers (F := v.adicCompletion K)))
        * Nat.card (ResidueField (LocalCFT.integers (F := v.adicCompletion K)))
            ^ (n.factorization p * e)) := by
  rw [powIndex_adicCompletion_units_eq_mul v n hn,
    powIndex_adicCompletionIntegers_units_of_ne_zero v hp he hpv hn]

end NumberField
