/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.LocalNormalBasis
public import Iwasawalib.NumberTheory.LocalCFT.AdditiveFiltration
public import Iwasawalib.NumberTheory.LocalCFT.AdicResidueField

@[expose] public section

/-!
# The integral normal basis lattice, and `h(D_w, O_w⁺) = 1`

`Iwasawalib/NumberTheory/LocalCFT/LocalNormalBasis.lean` gives a `K_v`-basis of `L_w` which is a
single `D_w`-orbit.  Scaling it into the valuation ring produces a `D_w`-stable `O_v`-lattice

`M = ⊕_{d ∈ D_w} O_v · (d • x) ⊆ O_w`

which is **free of rank one over `O_v[D_w]`**, hence cohomologically trivial.  It is *not* `O_w`
— Noether's theorem says `O_w` itself is `O_v[D_w]`-free only in the tamely ramified case — but
it has finite index in `O_w`, and the Herbrand quotient only sees the commensurability class.
Hence, at **every** finite place, ramified or not:

`NumberField.herbrand_adicCompletionIntegers_eq_one : h(D_w, O_w⁺) = 1`.

This is the "local normal basis theorem for lattices" which
`Iwasawalib/NumberTheory/LocalCFT/LocalNormIndex.lean` records as missing.

## The finite index

The two inclusions are proved by different means.

* `M ⊆ O_w` is arranged by scaling: all the basis vectors `d • x` have the *same* valuation
  (`NumberField.valued_decomposition_smul`), so a single scalar `s ∈ K_v` makes the whole orbit
  integral.
* `O_w ⊆ M` fails, but `𝔪^k ⊆ M` holds for some `k`, and that is enough.  The coordinate
  functionals of a basis of a finite-dimensional topological vector space over a complete field
  are continuous (`Module.Basis.continuous_coe_repr`), so the set where they are all integral is
  a neighbourhood of `0`, hence contains a ball of the valuation
  (`NumberField.exists_valBall_coord_integral`).  Finiteness of `O_w / 𝔪^k` is
  `LocalCFT.finite_quotient_of_valBall_le`.

## Main statements

* `NumberField.exists_integral_normalBasis`: a normal basis contained in `O_w`.
* `NumberField.exists_valBall_coord_integral`: the coordinates are integral on a ball.
* `NumberField.herbrand_adicCompletionIntegers_eq_one`: `h(D_w, O_w⁺) = 1`, unconditional.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero LocalCFT
open scoped WithZero

namespace NumberField

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] adicCompletionComapAlgebra decompositionIntegersMulSemiringAction

/-- `L_w` is a topological `K_v`-module (a copy of the local instance of
`Iwasawalib/NumberTheory/CFT/LocalGalois.lean`, which is not exported). -/
local instance continuousSMul_adicCompletion_of_comap :
    ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) := by
  constructor
  have h : (fun p : v.adicCompletion K × w.adicCompletion L ↦ p.1 • p.2) =
      fun p ↦ adicCompletionComap K L v w p.1 * p.2 := by
    funext p; exact Algebra.smul_def _ _
  rw [h]
  exact ((continuous_adicCompletionComap K L v w).comp continuous_fst).mul continuous_snd

omit [IsGalois K L] in
/-- The valuation in `L_w` of a scalar from `K_v`. -/
theorem valued_algebraMap_adicCompletion (c : v.adicCompletion K) :
    (Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) c) : ℤᵐ⁰)
      = (Valued.v c : ℤᵐ⁰) ^ (v.asIdeal.ramificationIdx' w.asIdeal) :=
  valued_adicCompletionComap K L v w c

omit [IsGalois K L] in
/-- A scalar of valuation at most one acts on `L_w` with valuation at most one. -/
theorem valued_algebraMap_le_one {c : v.adicCompletion K} (hc : (Valued.v c : ℤᵐ⁰) ≤ 1) :
    (Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) c) : ℤᵐ⁰) ≤ 1 := by
  rw [valued_algebraMap_adicCompletion]
  exact pow_le_one₀ zero_le hc

omit [IsGalois K L] in
theorem valued_smul_adicCompletion (c : v.adicCompletion K) (y : w.adicCompletion L) :
    (Valued.v (c • y) : ℤᵐ⁰)
      = (Valued.v c : ℤᵐ⁰) ^ (v.asIdeal.ramificationIdx' w.asIdeal) * Valued.v y := by
  rw [Algebra.smul_def, map_mul, valued_algebraMap_adicCompletion]

/-! ## A normal basis inside the valuation ring -/

/-- **A normal basis of `L_w / K_v` consisting of integral elements.**  Scaling the orbit basis
of `NumberField.decompositionNormalBasis` by a large power of a uniformizer of `K_v` makes every
member integral — all the members have the same valuation, because the decomposition group
preserves the valuation — while keeping it a single `D_w`-orbit. -/
theorem exists_integral_normalBasis :
    ∃ b : Module.Basis (decompositionGroup K L w) (v.adicCompletion K) (w.adicCompletion L),
      (∀ g d : decompositionGroup K L w, b (g * d) = g • b d) ∧
        ∀ d, (Valued.v (b d) : ℤᵐ⁰) ≤ 1 := by
  classical
  obtain ⟨t, ht⟩ := valuedAdicCompletion_surjective (K := K) v (exp (-1 : ℤ))
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht
    exact exp_ne_zero ht.symm
  set b₀ := decompositionNormalBasis v w with hb₀
  have hmul : ∀ g d : decompositionGroup K L w, b₀ (g * d) = g • b₀ d :=
    decompositionNormalBasis_mul v w
  have happ : ∀ d : decompositionGroup K L w, b₀ d = d • b₀ 1 :=
    decompositionNormalBasis_apply v w
  have hx0 : b₀ 1 ≠ 0 := b₀.ne_zero 1
  have hvx0 : (Valued.v (b₀ 1) : ℤᵐ⁰) ≠ 0 := by
    simpa using (Valuation.ne_zero_iff (Valued.v (R := w.adicCompletion L))).2 hx0
  set a : ℤ := log (Valued.v (b₀ 1) : ℤᵐ⁰) with ha
  have hax : (Valued.v (b₀ 1) : ℤᵐ⁰) = exp a := (exp_log hvx0).symm
  set s : v.adicCompletion K := t ^ a.toNat with hs
  have hs0 : s ≠ 0 := pow_ne_zero _ ht0
  have hvs : (Valued.v s : ℤᵐ⁰) = exp (-(a.toNat : ℤ)) := by
    rw [hs, map_pow, ht, ← exp_nsmul]
    congr 1
    rw [nsmul_eq_mul]
    ring
  refine ⟨b₀.isUnitSMul (w := fun _ ↦ s) (fun _ ↦ isUnit_iff_ne_zero.2 hs0), fun g d ↦ ?_,
    fun d ↦ ?_⟩
  · rw [Module.Basis.isUnitSMul_apply, Module.Basis.isUnitSMul_apply, hmul,
      smul_adicCompletion_smul]
  · rw [Module.Basis.isUnitSMul_apply, valued_smul_adicCompletion, happ,
      valued_decomposition_smul w, hvs, hax, ← exp_nsmul,
      ← exp_add, show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm, exp_le_exp, nsmul_eq_mul]
    have he : 1 ≤ v.asIdeal.ramificationIdx' w.asIdeal :=
      Nat.one_le_iff_ne_zero.2 (ramificationIdx_ne_zero' v w)
    have h1 : a ≤ (a.toNat : ℤ) := Int.self_le_toNat a
    have h2 : (a.toNat : ℤ) ≤ (v.asIdeal.ramificationIdx' w.asIdeal : ℤ) * (a.toNat : ℤ) := by
      nlinarith [Int.natCast_nonneg a.toNat, (by exact_mod_cast he : (1 : ℤ) ≤
        (v.asIdeal.ramificationIdx' w.asIdeal : ℤ))]
    linarith

/-! ## The coordinates are integral on a ball -/

omit [IsGalois K L] in
/-- **The coordinate functionals of a basis of `L_w` are integral on a small ball.**  They are
continuous (`Module.Basis.continuous_coe_repr`, which needs only that `L_w` is a
finite-dimensional topological vector space over the complete field `K_v`), so the set where
all of them are integral is a neighbourhood of zero, hence contains `{y : v y ≤ exp (-k)}` for
some `k`. -/
theorem exists_valBall_coord_integral
    (b : Module.Basis (decompositionGroup K L w) (v.adicCompletion K) (w.adicCompletion L))
    [Fintype (decompositionGroup K L w)] :
    ∃ k : ℕ, ∀ y : w.adicCompletion L, (Valued.v y : ℤᵐ⁰) ≤ exp (-(k : ℤ)) →
      ∀ d, (Valued.v (b.repr y d) : ℤᵐ⁰) ≤ 1 := by
  classical
  have hcoord : ∀ d : decompositionGroup K L w,
      Continuous fun y : w.adicCompletion L ↦ b.repr y d :=
    fun d ↦ (continuous_apply d).comp b.continuous_coe_repr
  have hS : {y : w.adicCompletion L | ∀ d, (Valued.v (b.repr y d) : ℤᵐ⁰) ≤ 1}
      ∈ nhds (0 : w.adicCompletion L) := by
    have h1 : ∀ d : decompositionGroup K L w,
        {y : w.adicCompletion L | (Valued.v (b.repr y d) : ℤᵐ⁰) ≤ 1}
          ∈ nhds (0 : w.adicCompletion L) := by
      intro d
      have h0 : {c : v.adicCompletion K | (Valued.v c : ℤᵐ⁰) ≤ 1}
          ∈ nhds (0 : v.adicCompletion K) :=
        Valued.mem_nhds_zero.2 ⟨1, fun x hx ↦
          le_of_lt ((Valuation.restrict_lt_one_iff _).1 (by simpa using hx))⟩
      have hc := (hcoord d).continuousAt (x := (0 : w.adicCompletion L))
      rw [ContinuousAt, show b.repr (0 : w.adicCompletion L) d = 0 by simp] at hc
      exact hc h0
    have hiInter : {y : w.adicCompletion L | ∀ d, (Valued.v (b.repr y d) : ℤᵐ⁰) ≤ 1}
        = ⋂ d, {y : w.adicCompletion L | (Valued.v (b.repr y d) : ℤᵐ⁰) ≤ 1} := by
      ext y; simp
    rw [hiInter]
    exact Filter.iInter_mem.2 h1
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hS
  set c : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding γ.val with hc
  have hc0 : c ≠ 0 := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  refine ⟨(1 - log c).toNat, fun y hy d ↦ ?_⟩
  have hlt : (Valued.v y : ℤᵐ⁰) < c := by
    refine lt_of_le_of_lt hy ?_
    conv_rhs => rw [← exp_log hc0]
    rw [exp_lt_exp]
    omega
  exact hγ ((Valuation.restrict_lt_iff_lt_embedding _).2 hlt) d

/-! ## The Herbrand quotient of the local integers -/

section Herbrand

variable [Fintype (decompositionGroup K L w)] {σ : decompositionGroup K L w}

omit [IsGalois K L] [Fintype (decompositionGroup K L w)] in
/-- A generator of the decomposition group generates it by natural powers. -/
theorem exists_pow_eq_of_mem_zpowers'
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ)
    (d : decompositionGroup K L w) : ∃ k : ℕ, σ ^ k = d := by
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff d σ).1 (mem_powers_iff_mem_zpowers.2 (hσ d))
  exact ⟨k, hk⟩

include v

/-- **`h(D_w, O_w⁺) = 1` at every finite place**, ramified or not.

The `O_v`-lattice spanned by an integral normal basis (`NumberField.exists_integral_normalBasis`)
is free of rank one over `O_v[D_w]`, so its Tate cohomology vanishes
(`CyclicTate.herbrand_eq_one_of_regularLattice`), and it has finite index in `O_w` because it
contains a ball of the valuation (`NumberField.exists_valBall_coord_integral`,
`LocalCFT.finite_quotient_of_valBall_le`).  The Herbrand quotient is a commensurability
invariant, so `h(O_w⁺) = 1`.

This is the additive half of the classical `h(D_w, O_w^×) = 1`; the remaining half is the
comparison of the unit filtration with the additive one, for which see
`Iwasawalib/NumberTheory/LocalCFT/LocalNormIndex.lean`. -/
theorem exists_latticeMap :
    ∃ f : (decompositionGroup K L w → LocalCFT.integers (F := v.adicCompletion K)) →+
        LocalCFT.integers (F := w.adicCompletion L),
      (∀ (g : decompositionGroup K L w)
          (F : decompositionGroup K L w → LocalCFT.integers (F := v.adicCompletion K)),
        f (fun x ↦ F (g⁻¹ * x)) = g • f F) ∧ Function.Injective f ∧
          Finite (LocalCFT.integers (F := w.adicCompletion L) ⧸ f.range) := by
  classical
  haveI : Finite (IsLocalRing.ResidueField
      (LocalCFT.integers (F := w.adicCompletion L))) :=
    HeightOneSpectrum.finite_residueField (F := L) w
  obtain ⟨b, hbmul, hbint⟩ := exists_integral_normalBasis v w
  obtain ⟨k, hk⟩ := exists_valBall_coord_integral v w b
  -- the lattice map, sending a tuple of integral coefficients to the corresponding combination
  have hmem : ∀ c : decompositionGroup K L w → LocalCFT.integers (F := v.adicCompletion K),
      (∑ d : decompositionGroup K L w, ((c d : v.adicCompletion K)) • b d)
        ∈ LocalCFT.integers (F := w.adicCompletion L) := by
    intro c
    refine sum_mem fun d _ ↦ ?_
    rw [LocalCFT.mem_integer, valued_smul_adicCompletion]
    exact mul_le_one' (pow_le_one₀ zero_le (c d).2) (hbint d)
  set f : (decompositionGroup K L w → LocalCFT.integers (F := v.adicCompletion K)) →+
      LocalCFT.integers (F := w.adicCompletion L) :=
    { toFun := fun c ↦ ⟨∑ d : decompositionGroup K L w, ((c d : v.adicCompletion K)) • b d,
        hmem c⟩
      map_zero' := by
        refine Subtype.ext ?_
        show (∑ d : decompositionGroup K L w, ((0 : v.adicCompletion K)) • b d) = 0
        simp
      map_add' := fun c c' ↦ by
        refine Subtype.ext ?_
        show (∑ d : decompositionGroup K L w,
            (((c d : v.adicCompletion K) + (c' d : v.adicCompletion K))) • b d) = _
        rw [show ∀ x y : LocalCFT.integers (F := w.adicCompletion L),
          ((x + y : LocalCFT.integers (F := w.adicCompletion L)) : w.adicCompletion L)
            = (x : w.adicCompletion L) + y from fun _ _ ↦ rfl]
        simp only [add_smul]
        exact Finset.sum_add_distrib } with hf
  have hcoe : ∀ c, ((f c : LocalCFT.integers (F := w.adicCompletion L)) : w.adicCompletion L)
      = ∑ d : decompositionGroup K L w, ((c d : v.adicCompletion K)) • b d := fun _ ↦ rfl
  refine ⟨f, fun g F ↦ ?_, fun c c' h ↦ ?_, ?_⟩
  · -- equivariance
    refine Subtype.ext ?_
    rw [hcoe, coe_decomposition_smul_integers, hcoe, Finset.smul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun d ↦ ?_).symm
    rw [smul_adicCompletion_smul, ← hbmul]
    show ((F d : v.adicCompletion K)) • b (g * d)
      = ((F (g⁻¹ * (g * d)) : v.adicCompletion K)) • b (g * d)
    rw [inv_mul_cancel_left]
  · -- injectivity
    have h' : (∑ d : decompositionGroup K L w, ((c d : v.adicCompletion K)) • b d)
        = ∑ d : decompositionGroup K L w, ((c' d : v.adicCompletion K)) • b d := by
      rw [← hcoe, ← hcoe, h]
    have h'' : (fun d ↦ (c d : v.adicCompletion K)) = fun d ↦ (c' d : v.adicCompletion K) :=
      b.equivFun.symm.injective (by
        rw [b.equivFun_symm_apply, b.equivFun_symm_apply]
        exact h')
    funext d
    exact Subtype.ext (congrFun h'' d)
  · -- finite index
    obtain ⟨π, hπ⟩ := valuedAdicCompletion_surjective (K := L) w (exp (-1 : ℤ))
    refine LocalCFT.finite_quotient_of_valBall_le (π := π) hπ (k := k) fun y hy ↦ ?_
    rw [LocalCFT.mem_valBall] at hy
    have hcoord : ∀ d, (Valued.v (b.repr (y : w.adicCompletion L) d) : ℤᵐ⁰) ≤ 1 :=
      hk (y : w.adicCompletion L) hy
    refine ⟨fun d ↦ ⟨b.repr (y : w.adicCompletion L) d, hcoord d⟩, Subtype.ext ?_⟩
    rw [hcoe]
    show (∑ d : decompositionGroup K L w, b.repr (y : w.adicCompletion L) d • b d)
      = (y : w.adicCompletion L)
    have hEq : ⇑(b.repr (y : w.adicCompletion L))
        = b.equivFun (y : w.adicCompletion L) := by
      funext d
      simp [Module.Basis.equivFun_apply]
    rw [← b.equivFun_symm_apply, hEq, b.equivFun.symm_apply_apply]

/-- **`h(D_w, O_w⁺) = 1` at every finite place**, ramified or not.

The `O_v`-lattice spanned by an integral normal basis (`NumberField.exists_integral_normalBasis`)
is free of rank one over `O_v[D_w]`, so its Tate cohomology vanishes
(`CyclicTate.herbrand_eq_one_of_regularLattice`), and it has finite index in `O_w` because it
contains a ball of the valuation (`NumberField.exists_valBall_coord_integral`,
`LocalCFT.finite_quotient_of_valBall_le`).  The Herbrand quotient is a commensurability
invariant, so `h(O_w⁺) = 1`.

This is the additive half of the classical `h(D_w, O_w^×) = 1`; the remaining half is the
comparison of the unit filtration with the additive one, for which see
`Iwasawalib/NumberTheory/LocalCFT/WildNormIndex.lean`. -/
theorem herbrand_adicCompletionIntegers_eq_one
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) :
    CyclicTate.herbrand (decompositionGroup K L w)
      (LocalCFT.integers (F := w.adicCompletion L)) σ = 1 := by
  obtain ⟨f, hf, hinj, hcoker⟩ := exists_latticeMap v w
  exact CyclicTate.herbrand_eq_one_of_regularLattice
    (exists_pow_eq_of_mem_zpowers' w hσ) f hf hinj hcoker

/-- `Ĥ⁰(D_w, O_w⁺)` is finite. -/
theorem finite_tateH0_adicCompletionIntegers
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) :
    Finite (CyclicTate.TateH0 (decompositionGroup K L w)
      (LocalCFT.integers (F := w.adicCompletion L)) σ) := by
  obtain ⟨f, hf, hinj, hcoker⟩ := exists_latticeMap v w
  exact CyclicTate.finite_tateH0_of_regularLattice
    (exists_pow_eq_of_mem_zpowers' w hσ) f hf hinj hcoker

/-- `Ĥ¹(D_w, O_w⁺)` is finite. -/
theorem finite_tateH1_adicCompletionIntegers
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) :
    Finite (CyclicTate.TateH1 (decompositionGroup K L w)
      (LocalCFT.integers (F := w.adicCompletion L)) σ) := by
  obtain ⟨f, hf, hinj, hcoker⟩ := exists_latticeMap v w
  exact CyclicTate.finite_tateH1_of_regularLattice
    (exists_pow_eq_of_mem_zpowers' w hσ) f hf hinj hcoker

end Herbrand

end NumberField
