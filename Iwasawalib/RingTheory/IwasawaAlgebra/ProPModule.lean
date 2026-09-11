/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.Topology.Algebra.ProP
public import Iwasawalib.RingTheory.IwasawaAlgebra.ProfiniteLambdaModule
public import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section

/-!
# A profinite abelian pro-`p` group is a profinite `ℤ_p`-module

Let `A` be a profinite abelian group (compact, Hausdorff, totally disconnected, with a uniform
additive group structure) which is pro-`p` in the sense of `IsAddProP`.  Then `A` carries a
unique continuous `ℤ_p`-module structure extending its `ℤ`-module structure, namely

`a • x = lim_n (a.appr n) • x`,

written here as the telescoping series `∑' i, (a.appr (i+1) - a.appr i) • x`.  The series
converges because `p ^ i` divides `a.appr (i+1) - a.appr i` and, `A` being pro-`p` and compact,
`p ^ i` moves all of `A` into any prescribed open subgroup once `i` is large.  That last
estimate is *uniform in `x`*, which is what makes `mul_smul` and joint continuity work; see
`ProP.exists_forall_sub_appr_smul_mem`.

Mathlib as of 2026-09 has no pro-`p` predicate and no construction of a `ℤ_p`-module from a
pro-`p` group: greps over `Mathlib/Topology/Algebra/Category/ProfiniteGrp/*`,
`Mathlib/NumberTheory/Padics/*` and `Module ℤ_[p]` turn up only
`Mathlib/NumberTheory/Padics/MahlerBasis.lean`, which is about `C(ℤ_p, E)`.  `PadicInt.lift` is
the universal property for maps *into* `ℤ_p` and does not help here.

This is the coefficient half of blueprint node `X-has-Gamma-action`: `X∞ = Gal(L∞/K∞)` is a
multiplicative profinite abelian pro-`p` group, while `IwasawaAlgebra.gammaLambdaModule` needs
an additive profinite `ℤ_p`-module.  See
`Iwasawalib.NumberTheory.ZpExtension.XinfModule`.

## Main definitions and results

* `ProP.padicSMul`: the scalar multiplication.
* `ProP.tendsto_appr_smul`, `ProP.tendsto_smul_of_approx`: what it is, and that any sequence of
  integers approximating `a` computes it.
* `ProP.padicModule`: the `Module ℤ_[p] A` structure; `ProP.continuousSMul_padicModule`: it is
  continuous.
* `ProP.eq_padicSMul`: uniqueness among actions continuous in the scalar and extending `ℤ`.
* `ProP.map_padicSMul`: every continuous additive endomorphism is `ℤ_p`-linear.
* `ProP.additivePadicModule`: the same statement for a multiplicatively written group `G`, on
  `Additive G`.
-/

open Topology Filter

namespace ProP

variable {p : ℕ} [Fact p.Prime]

section Additive

variable {A : Type*} [AddCommGroup A] [UniformSpace A] [IsUniformAddGroup A]
  [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]

/-! ### Separation and open subgroups -/

/-- Two elements of a Hausdorff profinite abelian group which are congruent modulo every open
subgroup are equal. -/
theorem eq_of_forall_sub_mem {u v : A} (h : ∀ U : OpenAddSubgroup A, u - v ∈ U) : u = v := by
  rw [← sub_eq_zero]
  by_contra hne
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean (G := A) {u - v}ᶜ
    ((isClosed_singleton (x := u - v)).isOpen_compl.mem_nhds (by simpa [eq_comm] using hne))
  exact hU (h U) rfl

/-- If `p ^ n` divides `k` with `n` large, then `k • x` lies in a prescribed open subgroup,
uniformly in `x`. -/
theorem exists_forall_zsmul_mem (hA : IsAddProP p A) (U : OpenAddSubgroup A) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ k : ℤ, ((p : ℤ) ^ n ∣ k) → ∀ x : A, k • x ∈ U := by
  obtain ⟨N, hN⟩ := hA.exists_forall_le (U.isOpen.mem_nhds U.zero_mem)
  refine ⟨N, fun n hn k hk x ↦ ?_⟩
  obtain ⟨m, rfl⟩ := hk
  have h1 : ((p : ℤ) ^ n * m) • x = m • (((p : ℤ) ^ n) • x) := by
    rw [mul_comm, mul_zsmul]
  have h2 : ((p : ℤ) ^ n) • x = (p ^ n : ℕ) • x := by
    rw [← Nat.cast_pow, natCast_zsmul]
  rw [h1, h2]
  exact U.toAddSubgroup.zsmul_mem (hN n hn x) m

/-! ### `p`-adic approximation by integers -/

/-- `p ^ n` divides an integer as soon as it does in `ℤ_p`. -/
theorem int_dvd_of_padicInt_dvd {n : ℕ} {k : ℤ} (h : ((p : ℤ_[p])) ^ n ∣ (k : ℤ_[p])) :
    ((p : ℤ)) ^ n ∣ k := by
  have hmem : (k : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := Ideal.mem_span_singleton.2 h
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_intCast,
    ZMod.intCast_zmod_eq_zero_iff_dvd] at hmem
  exact_mod_cast hmem

/-- `PadicInt.appr` values are congruent modulo `p ^ n`, as integers. -/
theorem dvd_appr_sub_appr (a : ℤ_[p]) {m n : ℕ} (h : n ≤ m) :
    ((p : ℤ)) ^ n ∣ (a.appr m : ℤ) - (a.appr n : ℤ) := by
  have hle : a.appr n ≤ a.appr m := PadicInt.appr_mono a h
  have hd := PadicInt.dvd_appr_sub_appr a n m h
  rw [← Nat.cast_sub hle]
  exact_mod_cast Int.natCast_dvd_natCast.2 (by exact_mod_cast hd)

/-- Consecutive `PadicInt.appr` values differ by a multiple of `p ^ i`. -/
theorem dvd_appr_sub_appr_succ (a : ℤ_[p]) (i : ℕ) :
    ((p : ℤ)) ^ i ∣ (a.appr (i + 1) : ℤ) - (a.appr i : ℤ) :=
  dvd_appr_sub_appr a (Nat.le_succ i)

theorem appr_zero (a : ℤ_[p]) : a.appr 0 = 0 :=
  Nat.lt_one_iff.1 (by simpa using PadicInt.appr_lt a 0)

/-- `a - a.appr n` is divisible by `p ^ n` in `ℤ_p`. -/
theorem padicInt_dvd_sub_appr (a : ℤ_[p]) (n : ℕ) :
    ((p : ℤ_[p])) ^ n ∣ a - (a.appr n : ℤ_[p]) :=
  Ideal.mem_span_singleton.1 (PadicInt.appr_spec n a)

/-! ### The `ℤ_p`-action -/

/-- The `ℤ_p`-scalar multiplication on a profinite abelian pro-`p` group: `a • x` is the limit
of `(a.appr n) • x`, written as a telescoping series. -/
noncomputable def padicSMul (a : ℤ_[p]) (x : A) : A :=
  ∑' i : ℕ, ((a.appr (i + 1) : ℤ) - (a.appr i : ℤ)) • x

theorem summable_padicSMul (hA : IsAddProP p A) (a : ℤ_[p]) (x : A) :
    Summable (fun i : ℕ ↦ ((a.appr (i + 1) : ℤ) - (a.appr i : ℤ)) • x) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop, tendsto_atTop']
  intro U hU
  obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean (G := A) U hU
  obtain ⟨N, hN⟩ := exists_forall_zsmul_mem hA V
  exact ⟨N, fun i hi ↦ hVU (hN i hi _ (dvd_appr_sub_appr_succ a i) x)⟩

theorem hasSum_padicSMul (hA : IsAddProP p A) (a : ℤ_[p]) (x : A) :
    HasSum (fun i : ℕ ↦ ((a.appr (i + 1) : ℤ) - (a.appr i : ℤ)) • x) (padicSMul a x) :=
  (summable_padicSMul hA a x).hasSum

/-- The defining property: `a • x` is the limit of the integer multiples `(a.appr n) • x`. -/
theorem tendsto_appr_smul (hA : IsAddProP p A) (a : ℤ_[p]) (x : A) :
    Tendsto (fun n : ℕ ↦ ((a.appr n : ℤ)) • x) atTop (𝓝 (padicSMul a x)) := by
  have h := (hasSum_padicSMul hA a x).tendsto_sum_nat
  refine h.congr fun n ↦ ?_
  rw [← Finset.sum_smul, Finset.sum_range_sub (fun i ↦ (a.appr i : ℤ)) n, appr_zero]
  simp

/-! ### Approximation by integers -/

/-- The uniform key estimate: an integer divisible by a large power of `p` moves every element
of `A` into a prescribed open subgroup. -/
theorem tendsto_zsmul_zero_of_dvd (hA : IsAddProP p A) {f : ℕ → ℤ}
    (hf : ∀ n, ((p : ℤ)) ^ n ∣ f n) (x : A) :
    Tendsto (fun n ↦ f n • x) atTop (𝓝 0) := by
  rw [tendsto_atTop']
  intro U hU
  obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean (G := A) U hU
  obtain ⟨N, hN⟩ := exists_forall_zsmul_mem hA V
  exact ⟨N, fun n hn ↦ hVU (hN n hn _ (hf n) x)⟩

/-- **The characterisation of the action.**  If a sequence of integers `f n` approximates
`a : ℤ_[p]` to precision `p ^ n`, then `f n • x` converges to `a • x`. -/
theorem tendsto_smul_of_approx (hA : IsAddProP p A) {a : ℤ_[p]} {f : ℕ → ℤ}
    (hf : ∀ n, ((p : ℤ_[p])) ^ n ∣ (a - (f n : ℤ_[p]))) (x : A) :
    Tendsto (fun n ↦ f n • x) atTop (𝓝 (padicSMul a x)) := by
  have hdvd : ∀ n, ((p : ℤ)) ^ n ∣ (f n - (a.appr n : ℤ)) := by
    intro n
    refine int_dvd_of_padicInt_dvd ?_
    have h := (padicInt_dvd_sub_appr a n).sub (hf n)
    push_cast
    convert h using 1
    ring
  have h0 := tendsto_zsmul_zero_of_dvd hA hdvd x
  have := (tendsto_appr_smul hA a x).add h0
  rw [add_zero] at this
  refine this.congr fun n ↦ ?_
  rw [sub_smul]
  abel

/-- **The uniform approximation estimate**, with `N` depending only on the open subgroup `U`
and not on `a` or `x`. -/
theorem exists_forall_sub_appr_smul_mem (hA : IsAddProP p A) (U : OpenAddSubgroup A) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ (a : ℤ_[p]) (x : A),
      padicSMul a x - ((a.appr n : ℤ)) • x ∈ U := by
  obtain ⟨N, hN⟩ := exists_forall_zsmul_mem hA U
  refine ⟨N, fun n hn a x ↦ ?_⟩
  have hcl : IsClosed (U : Set A) :=
    AddSubgroup.isClosed_of_isOpen U.toAddSubgroup U.isOpen
  refine hcl.mem_of_tendsto
    ((tendsto_appr_smul hA a x).sub tendsto_const_nhds)
    ((eventually_ge_atTop n).mono fun m h ↦ ?_)
  rw [← sub_smul]
  exact hN n hn _ (dvd_appr_sub_appr a h) x

/-! ### The module axioms -/

variable (hA : IsAddProP p A)
include hA

/-- Integers act as they always did. -/
theorem padicSMul_intCast (k : ℤ) (x : A) : padicSMul ((k : ℤ_[p])) x = k • x :=
  tendsto_nhds_unique
    (tendsto_smul_of_approx hA (f := fun _ ↦ k) (fun n ↦ by simp) x) tendsto_const_nhds

@[simp]
theorem padicSMul_zero_left (x : A) : padicSMul (0 : ℤ_[p]) x = 0 := by
  simpa using padicSMul_intCast hA 0 x

@[simp]
theorem padicSMul_one_left (x : A) : padicSMul (1 : ℤ_[p]) x = x := by
  simpa using padicSMul_intCast hA 1 x

@[simp]
theorem padicSMul_zero_right (a : ℤ_[p]) : padicSMul a (0 : A) = 0 := by
  simp [padicSMul]

theorem padicSMul_add_left (a b : ℤ_[p]) (x : A) :
    padicSMul (a + b) x = padicSMul a x + padicSMul b x := by
  refine tendsto_nhds_unique
    (tendsto_smul_of_approx hA (f := fun n ↦ (a.appr n : ℤ) + (b.appr n : ℤ)) (fun n ↦ ?_) x)
    (by simpa [add_smul] using (tendsto_appr_smul hA a x).add (tendsto_appr_smul hA b x))
  have h := (padicInt_dvd_sub_appr a n).add (padicInt_dvd_sub_appr b n)
  push_cast
  convert h using 1
  ring

theorem padicSMul_add_right (a : ℤ_[p]) (x y : A) :
    padicSMul a (x + y) = padicSMul a x + padicSMul a y :=
  tendsto_nhds_unique (tendsto_appr_smul hA a (x + y))
    (by simpa [smul_add] using (tendsto_appr_smul hA a x).add (tendsto_appr_smul hA a y))

theorem padicSMul_mul_left (a b : ℤ_[p]) (x : A) :
    padicSMul (a * b) x = padicSMul a (padicSMul b x) := by
  refine (eq_of_forall_sub_mem fun U ↦ ?_).symm
  have hcl : IsClosed (U : Set A) := AddSubgroup.isClosed_of_isOpen U.toAddSubgroup U.isOpen
  have hab : ∀ n : ℕ, ((p : ℤ_[p])) ^ n ∣
      (a * b - (((a.appr n : ℤ) * (b.appr n : ℤ) : ℤ) : ℤ_[p])) := by
    intro n
    have h1 := (padicInt_dvd_sub_appr a n).mul_left (b.appr n : ℤ_[p])
    have h2 := (padicInt_dvd_sub_appr b n).mul_left a
    have h := h2.add h1
    push_cast
    convert h using 1
    ring
  obtain ⟨N, hN⟩ := exists_forall_sub_appr_smul_mem hA U
  refine hcl.mem_of_tendsto
    (tendsto_const_nhds.sub (tendsto_smul_of_approx hA hab x))
    ((eventually_ge_atTop N).mono fun n hn ↦ ?_)
  have h1 := hN n hn a (padicSMul b x)
  have h2 : ((a.appr n : ℤ)) • (padicSMul b x - ((b.appr n : ℤ)) • x) ∈ U :=
    U.toAddSubgroup.zsmul_mem (hN n hn b x) _
  have h3 : padicSMul a (padicSMul b x) - ((a.appr n : ℤ) * (b.appr n : ℤ)) • x
      = (padicSMul a (padicSMul b x) - ((a.appr n : ℤ)) • padicSMul b x)
        + ((a.appr n : ℤ)) • (padicSMul b x - ((b.appr n : ℤ)) • x) := by
    rw [smul_sub, mul_smul]
    abel
  rw [h3]
  exact U.toAddSubgroup.add_mem h1 h2

/-- **The `ℤ_p`-module bridge.**  A profinite abelian pro-`p` group is a `ℤ_p`-module, with
`a • x` the limit of the integer multiples `(a.appr n) • x`.  Mathlib as of 2026-09 has no
pro-`p` predicate and no such construction. -/
@[instance_reducible] noncomputable def padicModule : Module ℤ_[p] A where
  smul := padicSMul
  one_smul := padicSMul_one_left hA
  mul_smul := padicSMul_mul_left hA
  smul_zero := padicSMul_zero_right hA
  smul_add := padicSMul_add_right hA
  add_smul := padicSMul_add_left hA
  zero_smul := padicSMul_zero_left hA

theorem padicModule_smul (a : ℤ_[p]) (x : A) :
    letI := padicModule hA
    a • x = padicSMul a x := rfl

/-! ### Continuity -/

theorem padicSMul_neg_left (a : ℤ_[p]) (x : A) : padicSMul (-a) x = -padicSMul a x := by
  have h := padicSMul_add_left hA a (-a) x
  rw [add_neg_cancel, padicSMul_zero_left hA] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem padicSMul_sub_right (a : ℤ_[p]) (x y : A) :
    padicSMul a (x - y) = padicSMul a x - padicSMul a y := by
  have h := padicSMul_add_right hA a (x - y) y
  rw [sub_add_cancel] at h
  rw [h]
  abel

theorem padicSMul_sub_left (a b : ℤ_[p]) (x : A) :
    padicSMul (a - b) x = padicSMul a x - padicSMul b x := by
  rw [sub_eq_add_neg, padicSMul_add_left hA, padicSMul_neg_left hA, sub_eq_add_neg]

/-- **Uniform continuity in the scalar.**  Scalars congruent modulo a large power of `p` act
the same modulo a prescribed open subgroup, uniformly in the group element. -/
theorem exists_forall_sub_padicSMul_mem (U : OpenAddSubgroup A) :
    ∃ N : ℕ, ∀ a b : ℤ_[p], ((p : ℤ_[p])) ^ N ∣ (a - b) → ∀ x : A,
      padicSMul a x - padicSMul b x ∈ U := by
  obtain ⟨N, hN⟩ := hA.exists_forall_le (U.isOpen.mem_nhds U.zero_mem)
  refine ⟨N, fun a b ⟨c, hc⟩ x ↦ ?_⟩
  rw [← padicSMul_sub_left hA, hc, padicSMul_mul_left hA]
  have hcast : padicSMul ((p : ℤ_[p]) ^ N) (padicSMul c x) = (p ^ N : ℕ) • padicSMul c x := by
    have h := padicSMul_intCast hA ((p : ℤ) ^ N) (padicSMul c x)
    push_cast at h
    rw [h, ← Nat.cast_pow, natCast_zsmul]
  rw [hcast]
  exact hN N le_rfl _

/-- For each scalar, multiplication by it is continuous. -/
theorem continuous_padicSMul (a : ℤ_[p]) : Continuous (padicSMul a : A → A) := by
  let f : A →+ A :=
    { toFun := padicSMul a
      map_zero' := padicSMul_zero_right hA a
      map_add' := padicSMul_add_right hA a }
  refine continuous_of_continuousAt_zero f ?_
  simp only [ContinuousAt, map_zero, f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  intro W hW
  rw [Filter.mem_map]
  obtain ⟨U, hUW⟩ := NonarchimedeanAddGroup.is_nonarchimedean (G := A) W hW
  obtain ⟨N, hN⟩ := exists_forall_sub_appr_smul_mem hA U
  have hpre : IsOpen ((fun x : A ↦ ((a.appr N : ℤ)) • x) ⁻¹' (U : Set A)) :=
    U.isOpen.preimage (continuous_zsmul _)
  have h0 : (0 : A) ∈ (fun x : A ↦ ((a.appr N : ℤ)) • x) ⁻¹' (U : Set A) := by
    simp [U.zero_mem]
  refine Filter.mem_of_superset (hpre.mem_nhds h0) fun x hx ↦ hUW ?_
  have h1 := hN N le_rfl a x
  simpa using U.toAddSubgroup.add_mem h1 hx

/-- **The `ℤ_p`-action is jointly continuous.** -/
theorem continuous_padicSMul_uncurry :
    Continuous (fun q : ℤ_[p] × A ↦ padicSMul q.1 q.2) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  refine continuous_iff_continuousAt.2 ?_
  rintro ⟨a₀, x₀⟩
  intro W hW
  rw [nhds_prod_eq, Filter.mem_map]
  have hW0 : (fun z : A ↦ z + padicSMul a₀ x₀) ⁻¹' W ∈ 𝓝 (0 : A) := by
    have hc : Continuous (fun z : A ↦ z + padicSMul a₀ x₀) := continuous_add_const _
    refine hc.continuousAt (x := (0 : A)) ?_
    simpa using hW
  obtain ⟨U, hUW⟩ := NonarchimedeanAddGroup.is_nonarchimedean (G := A) _ hW0
  obtain ⟨N, hN⟩ := exists_forall_sub_padicSMul_mem hA U
  have hS : {a : ℤ_[p] | ((p : ℤ_[p])) ^ N ∣ (a - a₀)} ∈ 𝓝 a₀ := by
    refine Filter.mem_of_superset
      (Metric.ball_mem_nhds a₀ (zpow_pos hp0 (-N : ℤ))) fun a ha ↦ ?_
    refine Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ N).1 ?_)
    rw [← dist_eq_norm]
    exact le_of_lt ha
  have hT : {x : A | padicSMul a₀ (x - x₀) ∈ U} ∈ 𝓝 x₀ := by
    have hc : Continuous (fun x : A ↦ padicSMul a₀ (x - x₀)) :=
      (continuous_padicSMul hA a₀).comp (continuous_sub_right x₀)
    refine (U.isOpen.preimage hc).mem_nhds ?_
    simp [padicSMul_zero_right hA, U.zero_mem]
  filter_upwards [Filter.prod_mem_prod hS hT] with q hq
  have h1 : padicSMul q.1 q.2 - padicSMul a₀ q.2 ∈ U := hN q.1 a₀ hq.1 q.2
  have h2 : padicSMul a₀ q.2 - padicSMul a₀ x₀ ∈ U := by
    have h := hq.2
    rw [Set.mem_setOf_eq, padicSMul_sub_right hA] at h
    exact h
  have h3 : padicSMul q.1 q.2 - padicSMul a₀ x₀ ∈ U := by
    have := U.toAddSubgroup.add_mem h1 h2
    simpa using this
  simpa using hUW h3

/-- **The `ℤ_p`-module structure is continuous.** -/
theorem continuousSMul_padicModule :
    letI := padicModule hA
    ContinuousSMul ℤ_[p] A :=
  letI := padicModule hA
  ⟨continuous_padicSMul_uncurry hA⟩

/-- **Every continuous additive endomorphism is automatically `ℤ_p`-linear.**  This is what
makes a continuous action by group automorphisms — for instance the `Γ`-action on `X∞` — an
action by `ℤ_p`-linear maps, i.e. supplies the `SMulCommClass` hypothesis of
`IwasawaAlgebra.gammaLambdaModule`. -/
theorem map_padicSMul {f : A →+ A} (hf : Continuous f) (a : ℤ_[p]) (x : A) :
    f (padicSMul a x) = padicSMul a (f x) := by
  refine tendsto_nhds_unique ?_ (tendsto_appr_smul hA a (f x))
  have h := (hf.continuousAt (x := padicSMul a x)).tendsto.comp (tendsto_appr_smul hA a x)
  refine h.congr fun n ↦ ?_
  simp

/-! ### Uniqueness -/

omit hA in
/-- `a.appr n` converges to `a` in `ℤ_p`. -/
theorem tendsto_appr (a : ℤ_[p]) :
    Tendsto (fun n : ℕ ↦ (((a.appr n : ℤ)) : ℤ_[p])) atTop (𝓝 a) := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨k, fun n hn ↦ lt_of_le_of_lt ?_ hk⟩
  have h1 : ‖a - ((a.appr n : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
    refine (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 ?_
    simpa using PadicInt.appr_spec n a
  have h2 : (p : ℝ) ^ (-(n : ℤ)) ≤ (p : ℝ) ^ (-(k : ℤ)) := by
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
    exact zpow_le_zpow_right₀ hp1 (by exact_mod_cast neg_le_neg (by exact_mod_cast hn))
  rw [dist_eq_norm, ← norm_neg]
  simpa using h1.trans h2

/-- **Uniqueness of the `ℤ_p`-action.**  Any action which is continuous in the scalar and
restricts to the canonical `ℤ`-action is `ProP.padicSMul`. -/
theorem eq_padicSMul {σ : ℤ_[p] → A → A}
    (hint : ∀ (k : ℤ) (x : A), σ ((k : ℤ_[p])) x = k • x)
    (hcont : ∀ x : A, Continuous fun a ↦ σ a x) (a : ℤ_[p]) (x : A) :
    σ a x = padicSMul a x := by
  refine tendsto_nhds_unique (f := fun n : ℕ ↦ ((a.appr n : ℤ)) • x) ?_
    (tendsto_appr_smul hA a x)
  have h := ((hcont x).continuousAt (x := a)).tendsto.comp (tendsto_appr (p := p) a)
  refine h.congr fun n ↦ ?_
  exact hint _ x

end Additive

/-! ### Multiplicative notation -/

section Multiplicative

variable {G : Type*} [CommGroup G] [UniformSpace G] [IsUniformGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

instance instIsUniformAddGroupAdditive : IsUniformAddGroup (Additive G) :=
  ⟨IsUniformGroup.uniformContinuous_div (α := G)⟩

instance instCompactSpaceAdditive : CompactSpace (Additive G) := inferInstanceAs (CompactSpace G)

instance instT2SpaceAdditive : T2Space (Additive G) := inferInstanceAs (T2Space G)

instance instTotallyDisconnectedSpaceAdditive : TotallyDisconnectedSpace (Additive G) :=
  inferInstanceAs (TotallyDisconnectedSpace G)

/-- **The `ℤ_p`-module bridge, multiplicative form.**  A profinite abelian pro-`p` group `G`
makes `Additive G` a `ℤ_p`-module. -/
@[instance_reducible] noncomputable def additivePadicModule (hG : IsProP p G) :
    Module ℤ_[p] (Additive G) :=
  padicModule (A := Additive G) hG

theorem additivePadicModule_smul (hG : IsProP p G) (a : ℤ_[p]) (x : Additive G) :
    letI := additivePadicModule hG
    a • x = padicSMul a x := rfl

/-- **What the scalar multiplication is**: `a • g` is the limit of the integer powers
`g ^ (a.appr n)`. -/
theorem tendsto_zpow_appr (hG : IsProP p G) (a : ℤ_[p]) (g : G) :
    Tendsto (fun n : ℕ ↦ Additive.ofMul (g ^ ((a.appr n : ℤ)))) atTop
      (𝓝 (padicSMul a (Additive.ofMul g))) :=
  tendsto_appr_smul (A := Additive G) hG a (Additive.ofMul g)

/-- The module structure of `ProP.additivePadicModule` is continuous. -/
theorem continuousSMul_additivePadicModule (hG : IsProP p G) :
    letI := additivePadicModule hG
    ContinuousSMul ℤ_[p] (Additive G) :=
  continuousSMul_padicModule (A := Additive G) hG

end Multiplicative

end ProP
