/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.FgTorsion
public import Iwasawalib.RingTheory.IwasawaAlgebra.LambdaNakayama
public import Iwasawalib.RingTheory.IwasawaAlgebra.ProfiniteLambdaModule
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Polynomial.Coeff

@[expose] public section

/-!
# A profinite `Γ`-module is a `Λ`-module

**Blueprint node `profinite-Gamma-module-is-Lambda-module`.**  Let `Z` be a profinite
`ℤ_p`-module and let a compact group `Γ` act on `Z` continuously and `ℤ_p`-linearly.  Let
`γ : Γ` be an element with `γ ^ (p ^ n) → 1` (for `Γ ≅ ℤ_p` with `γ` a topological generator
this holds, as `p ^ n → 0` in `ℤ_p`).  Then `Z` is a continuous `Λ = ℤ_p⟦X⟧`-module in which
`X = T` acts as `γ - 1`, and this structure is unique.

The proof is in two steps.

*Step 1* (`IwasawaAlgebra.exists_pow_smul_sub_mem`): for every open submodule `V` there is `n`
with `γ ^ (p ^ n) z - z ∈ V` for all `z`.  This is the tube lemma applied to the open set
`{(σ, z) | σ • z - z ∈ V}`, which contains the compact slice `{1} × Z`.

*Step 2* (`IwasawaAlgebra.isUnifTopNilpotent_sub_one`): `d = γ - 1` is uniformly
topologically nilpotent.  Here one uses the polynomial identity

`(T - 1) ^ (p ^ n * M) = (T ^ (p ^ n) - 1) * A + p ^ M * B`  in `ℤ[T]`,

which holds because `(T - 1) ^ (p ^ n) ≡ T ^ (p ^ n) - 1 (mod p)` (Frobenius in `𝔽_p[T]`).
Evaluating at `γ` in `Module.End ℤ_[p] Z` and applying to `z`, the first summand lies in `V`
by Step 1 and the second lies in `V` because `p ^ M` moves all of the compact module `Z` into
`V` (`IwasawaAlgebra.exists_pow_smul_mem`, again the tube lemma).

`IwasawaAlgebra.lambdaModule` of `Iwasawalib.RingTheory.IwasawaAlgebra.ProfiniteLambdaModule`
then supplies the module structure.
-/

open Topology Filter PowerSeries Polynomial
open scoped PowerSeries.WithPiTopology

namespace IwasawaAlgebra

/-! ### A binomial identity -/

/-- In a commutative ring, `(a + c) ^ M = a * A + c ^ M * B` for some `A`, `B`. -/
theorem exists_add_pow_eq {R : Type*} [CommRing R] (a c : R) (M : ℕ) :
    ∃ A B : R, (a + c) ^ M = a * A + c ^ M * B := by
  induction M with
  | zero => exact ⟨0, 1, by simp⟩
  | succ M ih =>
    obtain ⟨A, B, hAB⟩ := ih
    refine ⟨A * (a + c) + c ^ M * B, B, ?_⟩
    rw [pow_succ, hAB, add_mul, pow_succ]
    ring

/-! ### The polynomial identity -/

variable (p : ℕ) [Fact p.Prime]

/-- `(T - 1) ^ (p ^ n) ≡ T ^ (p ^ n) - 1` modulo `p` in `ℤ[T]`. -/
theorem C_p_dvd_sub_pow_sub (n : ℕ) :
    (Polynomial.C (p : ℤ)) ∣
      ((Polynomial.X - 1) ^ (p ^ n) - ((Polynomial.X : Polynomial ℤ) ^ (p ^ n) - 1)) := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  set q : Polynomial ℤ :=
    (Polynomial.X - 1) ^ (p ^ n) - ((Polynomial.X : Polynomial ℤ) ^ (p ^ n) - 1) with hq
  have hmap : q.map (Int.castRingHom (ZMod p)) = 0 := by
    rw [hq]
    push_cast [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X]
    rw [sub_pow_char_pow (R := Polynomial (ZMod p)), one_pow, sub_self]
  have h0 : ((q.coeff i : ℤ) : ZMod p) = 0 := by
    have := congrArg (fun r : Polynomial (ZMod p) ↦ r.coeff i) hmap
    simpa [Polynomial.coeff_map] using this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0

/-- **The polynomial identity behind topological nilpotence of `γ - 1`.** -/
theorem exists_X_sub_one_pow_eq (n M : ℕ) :
    ∃ A B : Polynomial ℤ, ((Polynomial.X : Polynomial ℤ) - 1) ^ (p ^ n * M)
      = ((Polynomial.X : Polynomial ℤ) ^ (p ^ n) - 1) * A + Polynomial.C ((p : ℤ) ^ M) * B := by
  obtain ⟨h, hh⟩ := C_p_dvd_sub_pow_sub p n
  have hsplit : ((Polynomial.X : Polynomial ℤ) - 1) ^ (p ^ n)
      = ((Polynomial.X : Polynomial ℤ) ^ (p ^ n) - 1) + Polynomial.C (p : ℤ) * h := by
    rw [← hh]; ring
  obtain ⟨A, B, hAB⟩ := exists_add_pow_eq
    ((Polynomial.X : Polynomial ℤ) ^ (p ^ n) - 1) (Polynomial.C (p : ℤ) * h) M
  refine ⟨A, h ^ M * B, ?_⟩
  rw [pow_mul, hsplit, hAB, mul_pow, ← Polynomial.C_pow]
  ring

/-! ### Uniform topological nilpotence -/

variable {p}

variable {Z : Type*} [AddCommGroup Z] [Module ℤ_[p] Z]
  [UniformSpace Z] [IsUniformAddGroup Z] [CompactSpace Z] [T2Space Z]
  [TotallyDisconnectedSpace Z] [ContinuousSMul ℤ_[p] Z]

/-- **Step 2.**  If `γ` is a `ℤ_p`-linear operator on a profinite `ℤ_p`-module such that every
open submodule `V` contains `γ ^ (p ^ n) z - z` for all `z` and some `n`, then `γ - 1` is
uniformly topologically nilpotent. -/
theorem isUnifTopNilpotent_sub_one (γ : Module.End ℤ_[p] Z)
    (hγ : ∀ V : Submodule ℤ_[p] Z, IsOpen (V : Set Z) →
      ∃ n : ℕ, ∀ z : Z, (γ ^ (p ^ n)) z - z ∈ V) :
    IsUnifTopNilpotent (γ - 1) := by
  intro U hU
  obtain ⟨V, hVopen, -, hVU⟩ := exists_isOpen_isClosed_submodule_subset (p := p) hU
  obtain ⟨n, hn⟩ := hγ V hVopen
  obtain ⟨M, hM⟩ := exists_pow_smul_mem V hVopen
  obtain ⟨A, B, hAB⟩ := exists_X_sub_one_pow_eq p n M
  set φ : Polynomial ℤ →+* Module.End ℤ_[p] Z :=
    Polynomial.eval₂RingHom' (Int.castRingHom (Module.End ℤ_[p] Z)) γ
      (fun a ↦ Int.cast_commute a γ) with hφ
  have hφX : φ Polynomial.X = γ := by
    simp [hφ]
  have hkey : ((γ - 1) ^ (p ^ n * M))
      = (γ ^ (p ^ n) - 1) * φ A + ((((p : ℤ) ^ M : ℤ) : Module.End ℤ_[p] Z)) * φ B := by
    have h := congrArg φ hAB
    simp only [map_add, map_mul, map_sub, map_pow, map_one, hφX] at h
    rw [h]
    congr 2
    simp [hφ]
  refine ⟨p ^ n * M, fun z ↦ hVU ?_⟩
  rw [hkey]
  refine V.add_mem ?_ ?_
  · have : ((γ ^ (p ^ n) - 1) * φ A) z = (γ ^ (p ^ n)) (φ A z) - (φ A z) := by
      simp [Module.End.mul_apply]
    rw [this]
    exact hn _
  · have : ((((p : ℤ) ^ M : ℤ) : Module.End ℤ_[p] Z) * φ B) z
        = ((p : ℤ) ^ M : ℤ) • (φ B z) := by
      rw [Module.End.mul_apply, Module.End.intCast_apply]
    rw [this]
    have hcast : (((p : ℤ) ^ M : ℤ)) • (φ B z) = ((p : ℤ_[p]) ^ M) • (φ B z) := by
      rw [← Int.cast_smul_eq_zsmul ℤ_[p]]
      push_cast
      rfl
    rw [hcast]
    exact hM _ (Ideal.mem_span_singleton_self _) _

/-! ### Finite generation from finite coinvariants -/

section Finiteness

variable {d : Module.End ℤ_[p] Z}

/-- `X • Z = d (Z)`: the submodule `(X) · Z` of the `Λ`-module structure is the image of
`d`. -/

theorem coe_span_X_smul_top (hd : IsUnifTopNilpotent d) (hdc : Continuous d) :
    letI := lambdaModule hd hdc
    ((((Ideal.span {(X : ℤ_[p]⟦X⟧)}) • (⊤ : Submodule ℤ_[p]⟦X⟧ Z)) :
      Submodule ℤ_[p]⟦X⟧ Z) : Set Z) = (LinearMap.range d : Set Z) := by
  letI := lambdaModule hd hdc
  ext w
  simp only [SetLike.mem_coe]
  constructor
  · intro hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · rintro r hr z -
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      refine ⟨lsmul d g z, ?_⟩
      rw [lambdaModule_smul hd hdc, apply_lsmul hd hdc]
      simpa using (lsmul_mul_X_pow hd g 1 z).symm
    · exact fun a b ha hb ↦ (LinearMap.range d).add_mem ha hb
  · rintro ⟨z, rfl⟩
    have : d z = (X : ℤ_[p]⟦X⟧) • z := (lsmul_X hd z).symm
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

/-- **Nakayama for `Λ`, in the form used for `X_n`.**  A profinite `ℤ_p`-module with a
continuous uniformly topologically nilpotent operator `d` and *finite* `Z / d Z` is a finitely
generated `Λ`-module. -/
theorem moduleFinite_of_finite_quotient_range (hd : IsUnifTopNilpotent d) (hdc : Continuous d)
    (hfin : Finite (Z ⧸ LinearMap.range d)) :
    letI := lambdaModule hd hdc
    Module.Finite ℤ_[p]⟦X⟧ Z := by
  letI := lambdaModule hd hdc
  haveI := continuousSMul_lambdaModule hd hdc
  have hcar := coe_span_X_smul_top hd hdc
  haveI : Finite (Z ⧸ ((Ideal.span {(X : ℤ_[p]⟦X⟧)}) • (⊤ : Submodule ℤ_[p]⟦X⟧ Z))) := by
    refine Finite.of_equiv (Z ⧸ LinearMap.range d) ?_
    refine Quotient.congr (Equiv.refl Z) fun a b ↦ ?_
    simp only [Equiv.refl_apply, Submodule.quotientRel_def]
    exact ⟨fun h ↦ (Set.ext_iff.1 hcar (a - b)).2 h, fun h ↦ (Set.ext_iff.1 hcar (a - b)).1 h⟩
  exact lambdaModuleFinite_of_finite_quotient_X_smul this

/-- **Blueprint node `Xn-isom-qout-of-totally-ramified`, Step 3, first half.**  A profinite
`ℤ_p`-module with a continuous uniformly topologically nilpotent operator `d` whose
coinvariants `Z / d Z` form a *finitely generated* `ℤ_p`-module is a finitely generated
`Λ`-module.  This is the form Step 3 needs: `Y / TX` has positive `ℤ_p`-rank in general, so
`IwasawaAlgebra.moduleFinite_of_finite_quotient_range` does not apply. -/
theorem moduleFinite_of_moduleFinite_quotient_range (hd : IsUnifTopNilpotent d)
    (hdc : Continuous d) (hfg : Module.Finite ℤ_[p] (Z ⧸ LinearMap.range d)) :
    letI := lambdaModule hd hdc
    Module.Finite ℤ_[p]⟦X⟧ Z := by
  letI := lambdaModule hd hdc
  haveI := continuousSMul_lambdaModule hd hdc
  haveI := isScalarTower_lambdaModule hd hdc
  exact lambdaModuleFinite_of_moduleFinite_quotient (LinearMap.range d)
    (coe_span_X_smul_top hd hdc).symm hfg

end Finiteness

/-! ### The action of a compact group -/

section Gamma

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [DistribMulAction Γ Z]
  [ContinuousSMul Γ Z] [SMulCommClass Γ ℤ_[p] Z]

/-- The `ℤ_p`-linear endomorphism of `Z` given by the action of `γ : Γ`. -/
def gammaEnd (γ : Γ) : Module.End ℤ_[p] Z where
  toFun z := γ • z
  map_add' := smul_add γ
  map_smul' a z := smul_comm γ a z

@[simp]
theorem gammaEnd_apply (γ : Γ) (z : Z) : gammaEnd (p := p) γ z = γ • z := rfl

theorem gammaEnd_pow (γ : Γ) (k : ℕ) :
    (gammaEnd (p := p) (Z := Z) γ) ^ k = gammaEnd (γ ^ k) := by
  induction k with
  | zero => ext z; simp
  | succ k ih => ext z; simp [pow_succ, Module.End.mul_apply, ih, mul_smul]

theorem continuous_gammaEnd (γ : Γ) : Continuous (gammaEnd (p := p) (Z := Z) γ) :=
  continuous_smul.comp (continuous_const.prodMk continuous_id)

/-- **Step 1.**  Tube lemma: for a continuous action of a group on a compact module, every
open submodule `V` absorbs `σ • z - z` for `σ` near `1`, uniformly in `z`.  Hence if
`γ ^ (p ^ n) → 1` then some `γ ^ (p ^ n)` is trivial modulo `V`. -/
theorem exists_pow_smul_sub_mem (γ : Γ)
    (hγ : Tendsto (fun n : ℕ ↦ γ ^ (p ^ n)) atTop (𝓝 1))
    (V : Submodule ℤ_[p] Z) (hV : IsOpen (V : Set Z)) :
    ∃ n : ℕ, ∀ z : Z, γ ^ (p ^ n) • z - z ∈ V := by
  have hpre : IsOpen {q : Γ × Z | q.1 • q.2 - q.2 ∈ V} :=
    hV.preimage ((continuous_smul (M := Γ) (X := Z)).sub continuous_snd)
  have hsub : ({1} : Set Γ) ×ˢ (Set.univ : Set Z) ⊆ {q : Γ × Z | q.1 • q.2 - q.2 ∈ V} := by
    rintro ⟨σ, z⟩ ⟨hσ, -⟩
    simp only [Set.mem_singleton_iff] at hσ
    simp [hσ, V.zero_mem]
  obtain ⟨u, v, huo, -, hsu, hvu, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_univ (X := Z)) hpre hsub
  have hev : ∀ᶠ y in 𝓝 (1 : Γ), y ∈ u := huo.mem_nhds (hsu rfl)
  obtain ⟨n, hn⟩ := Filter.Eventually.exists (hγ.eventually hev)
  exact ⟨n, fun z ↦ huv (show ((γ ^ (p ^ n), z) : Γ × Z) ∈ u ×ˢ v from
    ⟨hn, hvu (Set.mem_univ z)⟩)⟩

/-- **Blueprint node `profinite-Gamma-module-is-Lambda-module`, main step**: `γ - 1` is
uniformly topologically nilpotent on a profinite `ℤ_p`-module with a continuous action of a
group in which `γ ^ (p ^ n) → 1`. -/
theorem isUnifTopNilpotent_gammaEnd_sub_one (γ : Γ)
    (hγ : Tendsto (fun n : ℕ ↦ γ ^ (p ^ n)) atTop (𝓝 1)) :
    IsUnifTopNilpotent (gammaEnd (p := p) (Z := Z) γ - 1) := by
  refine isUnifTopNilpotent_sub_one _ fun V hV ↦ ?_
  obtain ⟨n, hn⟩ := exists_pow_smul_sub_mem γ hγ V hV
  exact ⟨n, fun z ↦ by simpa [gammaEnd_pow] using hn z⟩

/-- **Blueprint node `profinite-Gamma-module-is-Lambda-module`.**  A profinite `ℤ_p`-module
with a continuous, `ℤ_p`-linear action of a group `Γ` and an element `γ` with
`γ ^ (p ^ n) → 1` is a `Λ = ℤ_p⟦X⟧`-module, with `T = X` acting as `γ - 1`. -/
@[instance_reducible] noncomputable def gammaLambdaModule (γ : Γ)
    (hγ : Tendsto (fun n : ℕ ↦ γ ^ (p ^ n)) atTop (𝓝 1)) :
    Module ℤ_[p]⟦X⟧ Z :=
  lambdaModule (isUnifTopNilpotent_gammaEnd_sub_one γ hγ)
    ((continuous_gammaEnd γ).sub continuous_id)

/-- **Blueprint node `profinite-Gamma-module-is-Lambda-module`, uniqueness.**  Any continuous
`Λ`-action `σ` on `Z` which is additive and multiplicative, extends the `ℤ_p`-action and sends
`X = T` to `z ↦ γ • z - z` is `IwasawaAlgebra.gammaLambdaModule`.  Together with
`IwasawaAlgebra.gammaLambdaModule` this is the "uniquely" in the blueprint statement. -/
theorem eq_gammaLambdaModule_smul (γ : Γ)
    (hγ : Tendsto (fun n : ℕ ↦ γ ^ (p ^ n)) atTop (𝓝 1))
    {σ : ℤ_[p]⟦X⟧ → Z → Z}
    (hadd : ∀ f g z, σ (f + g) z = σ f z + σ g z)
    (hmul : ∀ f g z, σ (f * g) z = σ f (σ g z))
    (hone : ∀ z, σ 1 z = z)
    (hzp : ∀ (a : ℤ_[p]) (f : ℤ_[p]⟦X⟧) (z : Z), σ (a • f) z = a • σ f z)
    (hcont : ∀ z, Continuous fun f ↦ σ f z)
    (hX : ∀ z, σ (X : ℤ_[p]⟦X⟧) z = γ • z - z)
    (f : ℤ_[p]⟦X⟧) (z : Z) :
    letI := gammaLambdaModule (Z := Z) γ hγ
    σ f z = f • z := by
  letI := gammaLambdaModule (Z := Z) γ hγ
  have hd := isUnifTopNilpotent_gammaEnd_sub_one (p := p) (Z := Z) γ hγ
  have hdc : Continuous ((gammaEnd (p := p) (Z := Z) γ - 1 : Module.End ℤ_[p] Z)) :=
    (continuous_gammaEnd γ).sub continuous_id
  have hdz : ∀ w : Z, ((gammaEnd (p := p) (Z := Z) γ - 1 : Module.End ℤ_[p] Z)) w = γ • w - w := fun w ↦ by simp
  have hpowX : ∀ n : ℕ, ∀ w : Z,
      σ ((X : ℤ_[p]⟦X⟧) ^ n) w = ((((gammaEnd (p := p) (Z := Z) γ - 1 : Module.End ℤ_[p] Z)) ^ n)) w := by
    intro n
    induction n with
    | zero => intro w; simpa using hone w
    | succ n ih =>
        intro w
        rw [pow_succ, hmul, hX, ← hdz, ih, pow_succ, Module.End.mul_apply]
  have hC : ∀ (a : ℤ_[p]) (w : Z), σ (PowerSeries.C a : ℤ_[p]⟦X⟧) w = a • w := by
    intro a w
    have h : (PowerSeries.C a : ℤ_[p]⟦X⟧) = a • (1 : ℤ_[p]⟦X⟧) := by
      rw [PowerSeries.smul_eq_C_mul, mul_one]
    rw [h, hzp, hone]
  have hpoly : ∀ (n : ℕ) (a : ℤ_[p]) (w : Z),
      σ ((Polynomial.monomial n a : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) w
        = a • (((((gammaEnd (p := p) (Z := Z) γ - 1 : Module.End ℤ_[p] Z)) ^ n)) w) := by
    intro n a w
    have hm : ((Polynomial.monomial n a : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧)
        = PowerSeries.C a * (PowerSeries.X : ℤ_[p]⟦X⟧) ^ n := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
        Polynomial.coe_pow, Polynomial.coe_X]
    rw [hm, hmul, hpowX, hC]
  rw [lambdaModule_smul hd hdc f z]
  exact eq_lsmul_of_continuous hd hadd hcont hpoly f z

/-- In `IwasawaAlgebra.gammaLambdaModule`, `T = X` acts as `z ↦ γ • z - z`. -/
theorem gammaLambdaModule_X_smul (γ : Γ)
    (hγ : Tendsto (fun n : ℕ ↦ γ ^ (p ^ n)) atTop (𝓝 1)) (z : Z) :
    letI := gammaLambdaModule (Z := Z) γ hγ
    (X : ℤ_[p]⟦X⟧) • z = γ • z - z :=
  lsmul_X (isUnifTopNilpotent_gammaEnd_sub_one γ hγ) z

/-- In `IwasawaAlgebra.gammaLambdaModule`, `ℤ_p ⊆ Λ` acts as before. -/
theorem gammaLambdaModule_C_smul (γ : Γ)
    (hγ : Tendsto (fun n : ℕ ↦ γ ^ (p ^ n)) atTop (𝓝 1)) (a : ℤ_[p]) (z : Z) :
    letI := gammaLambdaModule (Z := Z) γ hγ
    (PowerSeries.C a : ℤ_[p]⟦X⟧) • z = a • z :=
  lsmul_C (isUnifTopNilpotent_gammaEnd_sub_one γ hγ) a z

/-- `IwasawaAlgebra.gammaLambdaModule` is a continuous module structure. -/
theorem continuousSMul_gammaLambdaModule (γ : Γ)
    (hγ : Tendsto (fun n : ℕ ↦ γ ^ (p ^ n)) atTop (𝓝 1)) :
    letI := gammaLambdaModule (Z := Z) γ hγ
    ContinuousSMul ℤ_[p]⟦X⟧ Z :=
  continuousSMul_lambdaModule (isUnifTopNilpotent_gammaEnd_sub_one γ hγ)
    ((continuous_gammaEnd γ).sub continuous_id)

/-- `IwasawaAlgebra.gammaLambdaModule` extends the `ℤ_p`-module structure. -/
theorem isScalarTower_gammaLambdaModule (γ : Γ)
    (hγ : Tendsto (fun n : ℕ ↦ γ ^ (p ^ n)) atTop (𝓝 1)) :
    letI := gammaLambdaModule (Z := Z) γ hγ
    IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ Z :=
  isScalarTower_lambdaModule (isUnifTopNilpotent_gammaEnd_sub_one γ hγ)
    ((continuous_gammaEnd γ).sub continuous_id)

/-- **Blueprint node `Xn-isom-qout-of-totally-ramified`, Step 3 (module-theoretic core).**
Let a compact group act continuously and `ℤ_p`-linearly on a profinite `ℤ_p`-module `Z`, and
let `γ` satisfy `γ ^ (p ^ n) → 1`.  If the coinvariants `Z / (γ - 1) Z` are finite, then `Z`
is a finitely generated `Λ`-module for the structure `IwasawaAlgebra.gammaLambdaModule`. -/
theorem moduleFinite_gammaLambdaModule_of_finite_coinvariants (γ : Γ)
    (hγ : Tendsto (fun n : ℕ ↦ γ ^ (p ^ n)) atTop (𝓝 1))
    (hfin : Finite (Z ⧸ LinearMap.range (gammaEnd (p := p) (Z := Z) γ - 1))) :
    letI := gammaLambdaModule (Z := Z) γ hγ
    Module.Finite ℤ_[p]⟦X⟧ Z :=
  moduleFinite_of_finite_quotient_range (isUnifTopNilpotent_gammaEnd_sub_one γ hγ)
    ((continuous_gammaEnd γ).sub continuous_id) hfin

/-- **Blueprint node `Xn-isom-qout-of-totally-ramified`, Step 3 (module-theoretic core), in
the form Step 3 actually needs.**  If the coinvariants `Z / (γ - 1) Z` are a *finitely
generated* `ℤ_p`-module — not merely finite — then `Z` is a finitely generated `Λ`-module. -/
theorem moduleFinite_gammaLambdaModule_of_moduleFinite_coinvariants (γ : Γ)
    (hγ : Tendsto (fun n : ℕ ↦ γ ^ (p ^ n)) atTop (𝓝 1))
    (hfg : Module.Finite ℤ_[p]
      (Z ⧸ LinearMap.range (gammaEnd (p := p) (Z := Z) γ - 1))) :
    letI := gammaLambdaModule (Z := Z) γ hγ
    Module.Finite ℤ_[p]⟦X⟧ Z :=
  moduleFinite_of_moduleFinite_quotient_range (isUnifTopNilpotent_gammaEnd_sub_one γ hγ)
    ((continuous_gammaEnd γ).sub continuous_id) hfg

end Gamma

end IwasawaAlgebra
