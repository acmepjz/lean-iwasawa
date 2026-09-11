/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.UnitCohomology
public import Mathlib.Data.Nat.Choose.Dvd

@[expose] public section

/-!
# Powers in the unit filtration of a complete discretely valued field

Let `F` be a complete field with a valuation `v : F → ℤᵐ⁰`, `𝒪` its valuation ring, and
`U^(k) = 1 + 𝔪^k` the unit filtration of
`Iwasawalib/NumberTheory/LocalCFT/UnitFiltration.lean`.  This file proves that raising to the
`n`-th power is a **bijection** `U^(k) → U^(k+δ)` whenever `v n = exp (-δ)` and the error term
of the binomial expansion is one step smaller than the linear term `n x`.

The two instances are:

* `n = p` the residue characteristic, `δ = e` the absolute ramification index, valid for
  `k(p-1) > e` — in particular for every `k ≥ m` once `m(p-1) > e`;
* `n` prime to `p`, `δ = 0`, valid for every `k ≥ 1`.

Together they give, for `n = p^a · s` with `p ∤ s`, that the `n`-th power map carries `U^(m)`
onto `U^(m + a e)` bijectively.  **This is the algebraic substitute for the `p`-adic logarithm
isomorphism `1 + 𝔪^m ≅ 𝔪^m`**: it is exactly the input that the index computation
`[𝒪^× : (𝒪^×)^n] = #μ_n(F) · |n|_F^{-1}` needs, and it requires no convergence theory, only
the completeness of the filtration (`LocalCFT.unitFiltration_complete`).

## Main statements

* `LocalCFT.valued_one_add_pow_sub_le_of_prime`: the binomial estimate
  `v ((1+x)^p - 1 - p x) ≤ max (v p · v x², v x ^ p)` for `p` prime.
* `LocalCFT.IsPowData`: the package of hypotheses under which `(·)^n : U^(k) → U^(k+δ)` is
  bijective for all `k ≥ m`.
* `LocalCFT.IsPowData.pow_injective`, `LocalCFT.IsPowData.exists_pow_eq`,
  `LocalCFT.IsPowData.image_pow`: injectivity, surjectivity and the image identity
  `(· ^ n) '' U^(k) = U^(k+δ)`.
* `LocalCFT.isPowData_prime`: the instance at the residue characteristic.
* `LocalCFT.isPowData_coprime`: the instance at an exponent prime to the residue
  characteristic.
-/

noncomputable section

open Finset WithZero

namespace LocalCFT

variable {F : Type*} [Field F] [hv : Valued F ℤᵐ⁰]

/-! ## Arithmetic in `ℤᵐ⁰` -/

theorem pow_le_pow_of_le_one' {c : ℤᵐ⁰} (hc : c ≤ 1) {k l : ℕ} (h : k ≤ l) : c ^ l ≤ c ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  exact mul_le_of_le_one_right' (pow_le_one' hc j)

/-- In `ℤᵐ⁰` the value group is discrete: being `< exp (-k)` is being `≤ exp (-k-1)`. -/
theorem lt_exp_iff_le_exp_sub_one {c : ℤᵐ⁰} {k : ℤ} : c < exp k ↔ c ≤ exp (k - 1) := by
  rw [← lt_mul_exp_iff_le (y := exp (k - 1)) exp_ne_zero, ← exp_add]
  norm_num

/-! ## The valuation of a natural number -/

/-- A natural number has valuation at most one. -/
theorem valued_natCast_le_one (m : ℕ) : (Valued.v ((m : F)) : ℤᵐ⁰) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast
    exact le_trans (Valuation.map_add _ _ _) (max_le ih (by simp))

/-- An integer has valuation at most one. -/
theorem valued_intCast_le_one (m : ℤ) : (Valued.v ((m : F)) : ℤᵐ⁰) ≤ 1 := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · exact_mod_cast valued_natCast_le_one (F := F) k
  · rw [Int.cast_neg, Valuation.map_neg]
    exact_mod_cast valued_natCast_le_one (F := F) k

/-! ## The binomial estimate at a prime -/

/-- **`(1 + x)^p = 1 + p x + O(max (v p · v x², v x^p))`.**  For `p` prime the middle binomial
coefficients `C(p, k)`, `0 < k < p`, are divisible by `p`, so every term of the expansion other
than `1` and `p x` is bounded either by `v p · v x ^ 2` (for `2 ≤ k < p`) or by `v x ^ p` (for
`k = p`). -/
theorem valued_one_add_pow_sub_le_of_prime {p : ℕ} (hp : p.Prime) (x : F) {c d B : ℤᵐ⁰}
    (hc1 : c ≤ 1) (hx : Valued.v x ≤ c) (hpv : Valued.v ((p : F)) ≤ d)
    (hmid : d * (c * c) ≤ B) (htop : c ^ p ≤ B) :
    (Valued.v ((1 + x) ^ p - 1 - (p : F) * x) : ℤᵐ⁰) ≤ B := by
  have hp2 : 2 ≤ p := hp.two_le
  have hexp : (1 + x) ^ p = ∑ k ∈ range (p + 1), x ^ k * ((p.choose k : ℕ) : F) := by
    rw [add_comm, add_pow]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [one_pow, mul_one]
  have hsplit : (1 + x) ^ p - 1 - (p : F) * x
      = ∑ k ∈ Finset.Ico 2 (p + 1), x ^ k * ((p.choose k : ℕ) : F) := by
    have h2 : ∑ k ∈ Finset.Ico 0 2, x ^ k * ((p.choose k : ℕ) : F) = 1 + (p : F) * x := by
      rw [show Finset.Ico 0 2 = ({0, 1} : Finset ℕ) by decide,
        Finset.sum_insert (by decide), Finset.sum_singleton]
      simp [Nat.choose_one_right]
      ring
    rw [hexp, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le 2) (by omega : 2 ≤ p + 1), h2]
    ring
  rw [hsplit]
  refine Valuation.map_sum_le _ ?_
  intro k hk
  rw [Finset.mem_Ico] at hk
  rw [map_mul, map_pow]
  rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hk.2) with hkp | hkp
  · -- the top term `x ^ p`
    subst hkp
    rw [Nat.choose_self, Nat.cast_one, map_one, mul_one]
    exact le_trans (pow_le_pow_left' hx k) htop
  · -- a middle term, divisible by `p`
    obtain ⟨t, ht⟩ := Nat.Prime.dvd_choose_self hp (by omega) hkp
    rw [ht]
    push_cast
    rw [map_mul]
    have h1 : (Valued.v x : ℤᵐ⁰) ^ k ≤ c * c := by
      refine le_trans (pow_le_pow_left' hx k) ?_
      rw [← pow_two]
      exact pow_le_pow_of_le_one' hc1 hk.1
    calc (Valued.v x : ℤᵐ⁰) ^ k * (Valued.v ((p : F)) * Valued.v ((t : F)))
        ≤ (c * c) * (d * 1) := mul_le_mul' h1 (mul_le_mul' hpv (valued_natCast_le_one t))
      _ = d * (c * c) := by rw [mul_one, mul_comm]
      _ ≤ B := hmid

/-! ## Units of the form `1 + x` -/

/-- An element `1 + x` with `v x < 1` is a unit of the valuation ring. -/
def oneAddUnit {x : F} (hx : (Valued.v x : ℤᵐ⁰) < 1) : (integers (F := F))ˣ :=
  unitOfValuedEqOne (x := 1 + x) <| by
    have h : (Valued.v ((1 + x) - 1) : ℤᵐ⁰) < Valued.v (1 : F) := by
      rw [map_one]; simpa using hx
    rw [Valuation.map_eq_of_sub_lt _ h, map_one]

@[simp] theorem coe_oneAddUnit {x : F} (hx : (Valued.v x : ℤᵐ⁰) < 1) :
    ((oneAddUnit hx : integers (F := F)) : F) = 1 + x := rfl

theorem oneAddUnit_mem {x : F} (hx : (Valued.v x : ℤᵐ⁰) < 1) {k : ℕ}
    (hk : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) : oneAddUnit hx ∈ unitFiltration k := by
  rw [mem_unitFiltration, coe_oneAddUnit]
  simpa using hk

/-- The coercion of a power of a unit. -/
theorem coe_units_pow (u : (integers (F := F))ˣ) (n : ℕ) :
    (((u ^ n : (integers (F := F))ˣ) : integers (F := F)) : F)
      = ((u : integers (F := F)) : F) ^ n := by
  push_cast; rfl

/-! ## The approximation package -/

section PowData

variable (F) in
/-- **The hypotheses under which `u ↦ u ^ n` is a bijection `U^(k) → U^(k+δ)` for `k ≥ m`.**

`valued_natCast` says that `v n = exp (-δ)`, so that the linear term `n x` of the binomial
expansion of `(1 + x)^n` moves an element of `U^(k)` exactly `δ` steps down the filtration;
`error` says that all the remaining terms move it *strictly more* than `δ` steps.  Under those
two conditions the `n`-th power map is level-exact and successive approximation converges. -/
structure IsPowData (n m δ : ℕ) : Prop where
  /-- the filtration is started at a positive level -/
  one_le : 1 ≤ m
  /-- `v n = exp (-δ)` -/
  valued_natCast : (Valued.v ((n : F)) : ℤᵐ⁰) = exp (-(δ : ℤ))
  /-- the binomial error term is one step better than the linear term -/
  error : ∀ (k : ℕ), m ≤ k → ∀ z : F, (Valued.v z : ℤᵐ⁰) ≤ exp (-(k : ℤ)) →
    (Valued.v ((1 + z) ^ n - 1 - (n : F) * z) : ℤᵐ⁰) ≤ exp (-((k : ℤ) + δ + 1))

variable {n m δ : ℕ}

theorem IsPowData.natCast_ne_zero (hd : IsPowData F n m δ) : ((n : F)) ≠ 0 := by
  intro h
  have := hd.valued_natCast
  rw [h, map_zero] at this
  exact exp_ne_zero this.symm

/-- **The `n`-th power map carries `U^(k)` into `U^(k+δ)`.** -/
theorem IsPowData.pow_mem (hd : IsPowData F n m δ) {k : ℕ} (hk : m ≤ k)
    {u : (integers (F := F))ˣ} (hu : u ∈ unitFiltration k) :
    u ^ n ∈ unitFiltration (F := F) (k + δ) := by
  set x : F := ((u : integers (F := F)) : F) - 1 with hxdef
  have hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ)) := hu
  have hone : ((u : integers (F := F)) : F) = 1 + x := by rw [hxdef]; ring
  rw [mem_unitFiltration, coe_units_pow, hone,
    show (1 + x) ^ n - 1 = ((1 + x) ^ n - 1 - (n : F) * x) + (n : F) * x by ring]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
  · refine le_trans (hd.error k hk x hx) ?_
    rw [exp_le_exp]
    push_cast
    omega
  · rw [map_mul, hd.valued_natCast]
    refine le_trans (mul_le_mul' le_rfl hx) ?_
    rw [← exp_add, exp_le_exp]
    push_cast
    omega

/-- **The `n`-th power map is exact on levels.**  If `u - 1` has valuation exactly `exp (-k)`
then `u ^ n - 1` has valuation exactly `exp (-(k + δ))`. -/
theorem IsPowData.valued_pow_sub_one (hd : IsPowData F n m δ) {k : ℕ} (hk : m ≤ k)
    {u : (integers (F := F))ˣ}
    (hx : (Valued.v (((u : integers (F := F)) : F) - 1) : ℤᵐ⁰) = exp (-(k : ℤ))) :
    (Valued.v ((((u ^ n : (integers (F := F))ˣ) : integers (F := F)) : F) - 1) : ℤᵐ⁰)
      = exp (-((k : ℤ) + δ)) := by
  set x : F := ((u : integers (F := F)) : F) - 1 with hxdef
  have hone : ((u : integers (F := F)) : F) = 1 + x := by rw [hxdef]; ring
  have hR : (Valued.v ((1 + x) ^ n - 1 - (n : F) * x) : ℤᵐ⁰) ≤ exp (-((k : ℤ) + δ + 1)) :=
    hd.error k hk x (le_of_eq hx)
  have hlin : (Valued.v ((n : F) * x) : ℤᵐ⁰) = exp (-((k : ℤ) + δ)) := by
    rw [map_mul, hd.valued_natCast, hx, ← exp_add]
    congr 1
    ring
  have hlt : (Valued.v (((1 + x) ^ n - 1) - ((n : F) * x)) : ℤᵐ⁰)
      < Valued.v ((n : F) * x) := by
    rw [show ((1 + x) ^ n - 1) - ((n : F) * x) = (1 + x) ^ n - 1 - (n : F) * x by ring, hlin]
    refine lt_of_le_of_lt hR ?_
    rw [exp_lt_exp]
    omega
  rw [coe_units_pow, hone, Valuation.map_eq_of_sub_lt _ hlt, hlin]

/-- **`U^(m)` has no `n`-torsion.** -/
theorem IsPowData.eq_one_of_pow_eq_one (hd : IsPowData F n m δ)
    {u : (integers (F := F))ˣ} (hu : u ∈ unitFiltration m) (h : u ^ n = 1) : u = 1 := by
  by_contra hne
  have hx0 : ((u : integers (F := F)) : F) - 1 ≠ 0 := by
    intro h0
    exact hne (Units.ext (Subtype.ext (by
      have : ((u : integers (F := F)) : F) = 1 := by linear_combination h0
      exact this)))
  have hne0 : (Valued.v (((u : integers (F := F)) : F) - 1) : ℤᵐ⁰) ≠ 0 := by
    simpa using hx0
  obtain ⟨j, hj⟩ : ∃ j : ℤ, (Valued.v (((u : integers (F := F)) : F) - 1) : ℤᵐ⁰) = exp j :=
    ⟨log _, (exp_log hne0).symm⟩
  have hle : (Valued.v (((u : integers (F := F)) : F) - 1) : ℤᵐ⁰) ≤ exp (-(m : ℤ)) := hu
  rw [hj, exp_le_exp] at hle
  set k : ℕ := (-j).toNat with hkdef
  have hkj : ((k : ℤ)) = -j := Int.toNat_of_nonneg (by omega)
  have hmk : m ≤ k := by omega
  have hx : (Valued.v (((u : integers (F := F)) : F) - 1) : ℤᵐ⁰) = exp (-(k : ℤ)) := by
    rw [hj, hkj, neg_neg]
  have := hd.valued_pow_sub_one hmk hx
  rw [h] at this
  simp only [Units.val_one, OneMemClass.coe_one, sub_self, map_zero] at this
  exact exp_ne_zero this.symm

/-- **The `n`-th power map is injective on `U^(m)`.** -/
theorem IsPowData.pow_injective (hd : IsPowData F n m δ)
    {u u' : (integers (F := F))ˣ} (hu : u ∈ unitFiltration m) (hu' : u' ∈ unitFiltration m)
    (h : u ^ n = u' ^ n) : u = u' := by
  have hdiv : (u / u') ^ n = 1 := by rw [div_pow, h, div_self']
  have := hd.eq_one_of_pow_eq_one (Subgroup.div_mem _ hu hu') hdiv
  rwa [div_eq_one] at this

/-- **One step of the successive approximation.**  Every `t ∈ U^(k+δ)` is an `n`-th power up to
`U^(k+δ+1)`, by an `n`-th root taken from `U^(k)`. -/
theorem IsPowData.exists_div_pow_mem (hd : IsPowData F n m δ) {k : ℕ} (hk : m ≤ k)
    {t : (integers (F := F))ˣ} (ht : t ∈ unitFiltration (F := F) (k + δ)) :
    ∃ s ∈ unitFiltration (F := F) k, t / s ^ n ∈ unitFiltration (F := F) (k + δ + 1) := by
  have hn0 : ((n : F)) ≠ 0 := hd.natCast_ne_zero
  have hk1 : 1 ≤ k := le_trans hd.one_le hk
  set y : F := ((t : integers (F := F)) : F) - 1 with hydef
  have hy : (Valued.v y : ℤᵐ⁰) ≤ exp (-((k + δ : ℕ) : ℤ)) := ht
  set z : F := y / (n : F) with hzdef
  have hvz : (Valued.v z : ℤᵐ⁰) ≤ exp (-(k : ℤ)) := by
    rw [hzdef, map_div₀, hd.valued_natCast, div_le_iff₀ exp_pos, ← exp_add]
    refine le_trans hy ?_
    rw [exp_le_exp]
    push_cast
    omega
  have hz1 : (Valued.v z : ℤᵐ⁰) < 1 := by
    refine lt_of_le_of_lt hvz ?_
    rw [show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm, exp_lt_exp]
    omega
  set s : (integers (F := F))ˣ := oneAddUnit hz1 with hsdef
  refine ⟨s, oneAddUnit_mem hz1 hvz, ?_⟩
  set R : F := (1 + z) ^ n - 1 - (n : F) * z with hRdef
  have hR : (Valued.v R : ℤᵐ⁰) ≤ exp (-((k : ℤ) + δ + 1)) := hd.error k hk z hvz
  have hnz : (n : F) * z = y := by
    rw [hzdef]
    field_simp
  have hsn : (((s ^ n : (integers (F := F))ˣ) : integers (F := F)) : F)
      = ((t : integers (F := F)) : F) + R := by
    rw [coe_units_pow, hsdef, coe_oneAddUnit, hRdef, hnz, hydef]
    ring
  have hval : (Valued.v ((((s ^ n : (integers (F := F))ˣ)) : integers (F := F)) : F) : ℤᵐ⁰) = 1 :=
    valued_coe_units _
  have hsn0 : ((t : integers (F := F)) : F) + R ≠ 0 := by
    rw [← hsn]
    intro h0
    rw [h0, map_zero] at hval
    exact zero_ne_one hval
  rw [mem_unitFiltration, coe_units_div]
  have hsub : ((t : integers (F := F)) : F)
      / ((((s ^ n : (integers (F := F))ˣ)) : integers (F := F)) : F) - 1
      = (-R) / (((t : integers (F := F)) : F) + R) := by
    rw [hsn]
    field_simp
    ring
  rw [hsub, map_div₀, ← hsn, hval, div_one, Valuation.map_neg]
  refine le_trans hR ?_
  rw [exp_le_exp]
  push_cast
  omega

/-- **The `n`-th power map carries `U^(k)` onto `U^(k+δ)`**, by successive approximation along
the filtration.  This is the algebraic replacement for the `p`-adic logarithm: no series is
summed, only the completeness of the unit filtration is used. -/
theorem IsPowData.exists_pow_eq [CompleteSpace F] (hd : IsPowData F n m δ) {k : ℕ} (hk : m ≤ k)
    {w : (integers (F := F))ˣ} (hw : w ∈ unitFiltration (F := F) (k + δ)) :
    ∃ u ∈ unitFiltration (F := F) k, u ^ n = w := by
  classical
  have step : ∀ (j : ℕ) (u : (integers (F := F))ˣ), ∃ s : (integers (F := F))ˣ,
      (w / u ^ n ∈ unitFiltration (F := F) (k + j + δ) →
        s ∈ unitFiltration (F := F) (k + j) ∧
          w / (u * s) ^ n ∈ unitFiltration (F := F) (k + (j + 1) + δ)) := by
    intro j u
    by_cases hc : w / u ^ n ∈ unitFiltration (F := F) (k + j + δ)
    · obtain ⟨s, hs1, hs2⟩ := hd.exists_div_pow_mem (k := k + j) (by omega) hc
      refine ⟨s, fun _ ↦ ⟨hs1, ?_⟩⟩
      rw [show k + (j + 1) + δ = k + j + δ + 1 by omega]
      rwa [mul_pow, ← div_div]
    · exact ⟨1, fun h ↦ absurd h hc⟩
  choose s hs using step
  set u : ℕ → (integers (F := F))ˣ :=
    fun j ↦ Nat.rec (motive := fun _ ↦ (integers (F := F))ˣ) 1 (fun i ui ↦ ui * s i ui) j
    with hudef
  have hu0 : u 0 = 1 := rfl
  have husucc : ∀ j, u (j + 1) = u j * s j (u j) := fun _ ↦ rfl
  have hinv : ∀ j, u j ∈ unitFiltration (F := F) k ∧
      w / (u j) ^ n ∈ unitFiltration (F := F) (k + j + δ) := by
    intro j
    induction j with
    | zero =>
      refine ⟨by rw [hu0]; exact one_mem _, ?_⟩
      rw [hu0, one_pow, div_one, Nat.add_zero]
      exact hw
    | succ j ih =>
      obtain ⟨h1, h2⟩ := hs j (u j) ih.2
      exact ⟨by rw [husucc]; exact mul_mem ih.1 (unitFiltration_mem_of_le (by omega) h1),
        by rw [husucc]; exact h2⟩
  have hstep : ∀ j, u j / u (j + 1) ∈ unitFiltration (F := F) j := by
    intro j
    have h1 := (hs j (u j) (hinv j).2).1
    rw [husucc, show u j / (u j * s j (u j)) = (s j (u j))⁻¹ by
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]]
    exact unitFiltration_mem_of_le (by omega) (Subgroup.inv_mem _ h1)
  obtain ⟨y, hy⟩ := unitFiltration_complete u hstep
  have hyk : y ∈ unitFiltration (F := F) k := by
    have := (unitFiltration (F := F) k).mul_mem (hy k) (hinv k).1
    simpa using this
  refine ⟨y, hyk, ?_⟩
  have hsep : ∀ j : ℕ, w / y ^ n ∈ unitFiltration (F := F) j := by
    intro j
    have h1 : w / (u j) ^ n ∈ unitFiltration (F := F) j :=
      unitFiltration_mem_of_le (by omega) (hinv j).2
    have h2 : (u j / y) ^ n ∈ unitFiltration (F := F) j := by
      refine Subgroup.pow_mem _ ?_ n
      have := Subgroup.inv_mem _ (hy j)
      rwa [inv_div] at this
    have h3 : w / y ^ n = (w / (u j) ^ n) * (u j / y) ^ n := by
      rw [div_pow]
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
    rw [h3]
    exact mul_mem h1 h2
  have := unitFiltration_separated hsep
  rw [div_eq_one] at this
  exact this.symm

/-- **The `n`-th power map is a bijection `U^(k) → U^(k+δ)`.** -/
theorem IsPowData.image_pow [CompleteSpace F] (hd : IsPowData F n m δ) {k : ℕ} (hk : m ≤ k) :
    (fun u : (integers (F := F))ˣ ↦ u ^ n) '' (unitFiltration (F := F) k : Set _)
      = (unitFiltration (F := F) (k + δ) : Set _) := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hd.pow_mem hk hu
  · intro ht
    obtain ⟨u, hu, rfl⟩ := hd.exists_pow_eq hk ht
    exact ⟨u, hu, rfl⟩

/-- The `n`-th power map as a homomorphism `U^(k) → U^(k+δ)`. -/
def IsPowData.powHom (hd : IsPowData F n m δ) {k : ℕ} (hk : m ≤ k) :
    unitFiltration (F := F) k →* unitFiltration (F := F) (k + δ) where
  toFun u := ⟨(u : (integers (F := F))ˣ) ^ n, hd.pow_mem hk u.2⟩
  map_one' := Subtype.ext (one_pow n)
  map_mul' u v := Subtype.ext (mul_pow _ _ n)

@[simp] theorem IsPowData.coe_powHom (hd : IsPowData F n m δ) {k : ℕ} (hk : m ≤ k)
    (u : unitFiltration (F := F) k) :
    ((hd.powHom hk u : unitFiltration (F := F) (k + δ)) : (integers (F := F))ˣ)
      = (u : (integers (F := F))ˣ) ^ n := rfl

/-- **`u ↦ u ^ n` is an isomorphism `U^(k) ≃ U^(k+δ)`.**  For `n = p` and `δ = e` this is the
algebraic form of `1 + 𝔪^k ≅ 1 + 𝔪^(k+e)` that replaces the `p`-adic logarithm. -/
def IsPowData.powEquiv [CompleteSpace F] (hd : IsPowData F n m δ) {k : ℕ} (hk : m ≤ k) :
    unitFiltration (F := F) k ≃* unitFiltration (F := F) (k + δ) :=
  MulEquiv.ofBijective (hd.powHom hk) <| by
    constructor
    · intro u v huv
      refine Subtype.ext (hd.pow_injective (unitFiltration_mem_of_le hk u.2)
        (unitFiltration_mem_of_le hk v.2) ?_)
      simpa using congrArg (fun t : unitFiltration (F := F) (k + δ) ↦
        (t : (integers (F := F))ˣ)) huv
    · intro t
      obtain ⟨u, hu, hut⟩ := hd.exists_pow_eq hk t.2
      exact ⟨⟨u, hu⟩, Subtype.ext hut⟩

@[simp] theorem IsPowData.coe_powEquiv [CompleteSpace F] (hd : IsPowData F n m δ) {k : ℕ}
    (hk : m ≤ k) (u : unitFiltration (F := F) k) :
    ((hd.powEquiv hk u : unitFiltration (F := F) (k + δ)) : (integers (F := F))ˣ)
      = (u : (integers (F := F))ˣ) ^ n := rfl

/-- **Iterated powers.**  The `n^a`-th power map carries `U^(k)` onto `U^(k + a δ)`. -/
theorem IsPowData.image_pow_pow [CompleteSpace F] (hd : IsPowData F n m δ) {k : ℕ} (hk : m ≤ k)
    (a : ℕ) :
    (fun u : (integers (F := F))ˣ ↦ u ^ (n ^ a)) '' (unitFiltration (F := F) k : Set _)
      = (unitFiltration (F := F) (k + a * δ) : Set _) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hcomp : (fun u : (integers (F := F))ˣ ↦ u ^ (n ^ (a + 1)))
        = (fun t : (integers (F := F))ˣ ↦ t ^ n) ∘ (fun u : (integers (F := F))ˣ ↦ u ^ (n ^ a)) :=
      funext fun u ↦ by rw [Function.comp_apply, ← pow_mul, ← pow_succ]
    rw [hcomp, Set.image_comp, ih, hd.image_pow (k := k + a * δ) (by omega),
      show k + a * δ + δ = k + (a + 1) * δ by ring]

end PowData

/-! ## The instance at the residue characteristic -/

section Instances

/-- **The `p`-power map is a bijection `U^(k) → U^(k+e)` for `k(p-1) > e`.**  Here `p` is the
residue characteristic and `e = v(p)` is the absolute ramification index; the hypothesis
`e < m (p-1)` is the classical bound `m > e/(p-1)`. -/
theorem isPowData_prime {p m e : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hpv : (Valued.v ((p : F)) : ℤᵐ⁰) = exp (-(e : ℤ))) (hme : e < m * (p - 1)) :
    IsPowData F p m e where
  one_le := hm
  valued_natCast := hpv
  error := by
    intro k hk z hz
    refine valued_one_add_pow_sub_le_of_prime hp z (exp_neg_natCast_le_one k) hz
      (le_of_eq hpv) ?_ ?_
    · rw [← exp_add, ← exp_add, exp_le_exp]
      have hk1 : 1 ≤ k := le_trans hm hk
      push_cast
      omega
    · rw [← exp_nsmul, exp_le_exp, nsmul_eq_mul]
      have hkq : e + 1 ≤ k * (p - 1) := le_trans hme (Nat.mul_le_mul_right _ hk)
      have hprod : k * (p - 1) + k = k * p := by
        cases p with
        | zero => omega
        | succ q => simp [Nat.succ_sub_one, Nat.mul_succ]
      have h1 : ((e : ℤ) + 1) + (k : ℤ) ≤ ((k : ℤ) * (p : ℤ)) := by
        have h2 : e + 1 + k ≤ k * p := by omega
        exact_mod_cast h2
      push_cast
      nlinarith [h1]

/-- **An exponent of valuation one acts bijectively on every step of the unit filtration.**
This is the case `δ = 0` of `LocalCFT.IsPowData`, and applies to every `n` prime to the residue
characteristic. -/
theorem isPowData_of_valued_eq_one {n m : ℕ} (hm : 1 ≤ m)
    (hn : (Valued.v ((n : F)) : ℤᵐ⁰) = 1) :
    IsPowData F n m 0 where
  one_le := hm
  valued_natCast := by rw [hn]; simp
  error := by
    intro k hk z hz
    have hk1 : 1 ≤ k := le_trans hm hk
    have hexp := prod_one_add_sub_le (F := F) (Finset.range n) (fun _ ↦ z)
      (exp_neg_natCast_le_one k) (fun _ _ ↦ hz)
    rw [Finset.prod_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hexp
    refine le_trans hexp ?_
    rw [← exp_add, exp_le_exp]
    push_cast
    omega

/-- **A natural number prime to the residue characteristic is a unit.**  If `v p = exp (-e)`
with `e ≥ 1` — i.e. `p` is in the maximal ideal — then any `s` coprime to `p` has `v s = 1`. -/
theorem valued_natCast_eq_one_of_coprime {p s e : ℕ} (he : 1 ≤ e)
    (hpv : (Valued.v ((p : F)) : ℤᵐ⁰) = exp (-(e : ℤ))) (hs : Nat.Coprime s p) :
    (Valued.v ((s : F)) : ℤᵐ⁰) = 1 := by
  have hb : (1 : ℤ) = (s : ℤ) * Nat.gcdA s p + (p : ℤ) * Nat.gcdB s p := by
    have h := Nat.gcd_eq_gcd_ab s p
    rw [show Nat.gcd s p = 1 from hs] at h
    exact_mod_cast h
  have hbF : (1 : F) = (s : F) * ((Nat.gcdA s p : ℤ) : F) + (p : F) * ((Nat.gcdB s p : ℤ) : F) := by
    exact_mod_cast congrArg (fun z : ℤ ↦ (z : F)) hb
  have hle : (1 : ℤᵐ⁰) ≤ max (Valued.v ((s : F)) * Valued.v (((Nat.gcdA s p : ℤ) : F)))
      (Valued.v ((p : F)) * Valued.v (((Nat.gcdB s p : ℤ) : F))) := by
    calc (1 : ℤᵐ⁰) = Valued.v (1 : F) := (map_one _).symm
      _ = Valued.v ((s : F) * ((Nat.gcdA s p : ℤ) : F)
            + (p : F) * ((Nat.gcdB s p : ℤ) : F)) := by rw [← hbF]
      _ ≤ max (Valued.v ((s : F) * ((Nat.gcdA s p : ℤ) : F)))
            (Valued.v ((p : F) * ((Nat.gcdB s p : ℤ) : F))) := Valuation.map_add _ _ _
      _ = _ := by rw [map_mul, map_mul]
  by_contra hne
  have hs1 : (Valued.v ((s : F)) : ℤᵐ⁰) ≤ exp (-1 : ℤ) :=
    le_exp_neg_one_iff_lt_one.2 (lt_of_le_of_ne (valued_natCast_le_one s) hne)
  have hp1 : (Valued.v ((p : F)) : ℤᵐ⁰) ≤ exp (-1 : ℤ) := by
    rw [hpv, exp_le_exp]
    omega
  have hbound : max (Valued.v ((s : F)) * Valued.v (((Nat.gcdA s p : ℤ) : F)))
      (Valued.v ((p : F)) * Valued.v (((Nat.gcdB s p : ℤ) : F))) ≤ exp (-1 : ℤ) :=
    max_le
      (le_trans (mul_le_mul' hs1 (valued_intCast_le_one _)) (by rw [mul_one]))
      (le_trans (mul_le_mul' hp1 (valued_intCast_le_one _)) (by rw [mul_one]))
  have : (1 : ℤᵐ⁰) ≤ exp (-1 : ℤ) := le_trans hle hbound
  rw [show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm, exp_le_exp] at this
  omega

end Instances

end LocalCFT
