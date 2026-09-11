/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.LambdaTopology
public import Iwasawalib.RingTheory.IwasawaAlgebra.ProfiniteModule
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.Topology.Algebra.InfiniteSum.Module

@[expose] public section

/-!
# Profinite `ℤ_p`-modules with a topologically nilpotent operator are `Λ`-modules

Let `Z` be a profinite `ℤ_p`-module (compact, Hausdorff, totally disconnected, continuous
scalar multiplication) and let `d : Z → Z` be a continuous `ℤ_p`-linear operator which is
*uniformly topologically nilpotent*: every neighbourhood of `0` contains `d ^ N (Z)` for some
`N`.  Then

`f • z := ∑' i, (coeff i f) • (d ^ i) z`

is a continuous `Λ = ℤ_p⟦X⟧`-module structure on `Z` in which `X` acts as `d`.

This is the analytic heart of blueprint node `profinite-Gamma-module-is-Lambda-module`: for a
pro-`p` abelian group with a continuous `Γ`-action, `d = γ - 1` is such an operator (see
`Iwasawalib.RingTheory.IwasawaAlgebra.GammaModule`), and the resulting `Λ`-structure is the
one the blueprint constructs as an inverse limit.  The proof here is by density of polynomials
in `Λ` rather than by the inverse limit; the two produce the same action because both are
continuous and agree on `ℤ_p[Γ]`.

## Main definitions and results

* `IwasawaAlgebra.IsUnifTopNilpotent`: uniform topological nilpotence.
* `IwasawaAlgebra.lsmul`: the action `f • z`.
* `IwasawaAlgebra.lambdaModule`: the `Λ`-module structure.
* `IwasawaAlgebra.continuousSMul_lambdaModule`: it is continuous.
* `IwasawaAlgebra.lsmul_X`, `IwasawaAlgebra.lsmul_C`: `X` acts as `d`, and `ℤ_p` acts as
  before.
-/

open Topology Filter PowerSeries
open scoped PowerSeries.WithPiTopology

/-- A profinite topological abelian group is nonarchimedean: the open subgroups form a
neighbourhood basis of `0`. -/
instance NonarchimedeanAddGroup.of_profinite {Z : Type*} [AddCommGroup Z] [UniformSpace Z]
    [IsUniformAddGroup Z] [CompactSpace Z] [T2Space Z] [TotallyDisconnectedSpace Z] :
    NonarchimedeanAddGroup Z where
  is_nonarchimedean U hU := by
    obtain ⟨O, hOU, hOopen, hO0⟩ := mem_nhds_iff.1 hU
    obtain ⟨W, hWclopen, hW0, hWO⟩ := compact_exists_isClopen_in_isOpen hOopen hO0
    obtain ⟨H, hH⟩ :=
      IsTopologicalAddGroup.exist_openAddSubgroup_sub_clopen_nhds_of_zero hWclopen hW0
    exact ⟨H, hH.trans (hWO.trans hOU)⟩

namespace IwasawaAlgebra

variable {p : ℕ} [Fact p.Prime] {Z : Type*} [AddCommGroup Z] [Module ℤ_[p] Z]
  [UniformSpace Z] [IsUniformAddGroup Z] [CompactSpace Z] [T2Space Z]
  [TotallyDisconnectedSpace Z] [ContinuousSMul ℤ_[p] Z]

section Basis

/-- The open `ℤ_p`-submodules of a profinite `ℤ_p`-module are a neighbourhood basis of `0`,
and they are closed. -/
theorem exists_isOpen_isClosed_submodule_subset {U : Set Z} (hU : U ∈ 𝓝 (0 : Z)) :
    ∃ V : Submodule ℤ_[p] Z, IsOpen (V : Set Z) ∧ IsClosed (V : Set Z) ∧ (V : Set Z) ⊆ U := by
  obtain ⟨H, hHU⟩ := NonarchimedeanAddGroup.is_nonarchimedean (G := Z) U hU
  refine ⟨H.toAddSubgroup.moduleCore ℤ_[p], H.toAddSubgroup.isOpen_moduleCore H.isOpen,
    AddSubgroup.isClosed_of_isOpen (H.toAddSubgroup.moduleCore ℤ_[p]).toAddSubgroup
      (H.toAddSubgroup.isOpen_moduleCore H.isOpen), ?_⟩
  exact (H.toAddSubgroup.moduleCore_le).trans hHU

/-- An infinite sum of elements of a closed submodule lies in that submodule. -/
theorem mem_of_hasSum_mem {ι : Type*} (V : Submodule ℤ_[p] Z) (hV : IsClosed (V : Set Z))
    {f : ι → Z} {a : Z} (hf : HasSum f a) (hmem : ∀ i, f i ∈ V) : a ∈ V :=
  hV.mem_of_tendsto hf (Filter.Eventually.of_forall fun s ↦ Submodule.sum_mem _ fun i _ ↦ hmem i)

end Basis

section Nilpotent

variable (d : Module.End ℤ_[p] Z)

/-- `d` is *uniformly topologically nilpotent*: every neighbourhood of `0` contains the image
of some power of `d`. -/
def IsUnifTopNilpotent : Prop := ∀ U ∈ 𝓝 (0 : Z), ∃ N : ℕ, ∀ z : Z, (d ^ N) z ∈ U

variable {d}

/-- All sufficiently large powers of a uniformly topologically nilpotent operator have image
inside a given neighbourhood of `0`. -/
theorem IsUnifTopNilpotent.exists_forall_le (hd : IsUnifTopNilpotent d) {U : Set Z}
    (hU : U ∈ 𝓝 (0 : Z)) : ∃ N : ℕ, ∀ i, N ≤ i → ∀ z : Z, (d ^ i) z ∈ U := by
  obtain ⟨N, hN⟩ := hd U hU
  refine ⟨N, fun i hi z ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [pow_add, Module.End.mul_apply]
  exact hN _

end Nilpotent

section Action

variable (d : Module.End ℤ_[p] Z)

/-- The action of `Λ = ℤ_p⟦X⟧` on `Z` in which `X` acts as `d`. -/
noncomputable def lsmul (f : ℤ_[p]⟦X⟧) (z : Z) : Z := ∑' i : ℕ, (coeff i f) • ((d ^ i) z)

variable {d}

theorem summable_lsmul (hd : IsUnifTopNilpotent d) (f : ℤ_[p]⟦X⟧) (z : Z) :
    Summable (fun i : ℕ ↦ (coeff i f) • ((d ^ i) z)) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop, tendsto_atTop']
  intro U hU
  obtain ⟨V, hVopen, -, hVU⟩ := exists_isOpen_isClosed_submodule_subset (p := p) hU
  obtain ⟨N, hN⟩ := hd.exists_forall_le (hVopen.mem_nhds V.zero_mem)
  exact ⟨N, fun i hi ↦ hVU (V.smul_mem _ (hN i hi z))⟩

theorem hasSum_lsmul (hd : IsUnifTopNilpotent d) (f : ℤ_[p]⟦X⟧) (z : Z) :
    HasSum (fun i : ℕ ↦ (coeff i f) • ((d ^ i) z)) (lsmul d f z) :=
  (summable_lsmul hd f z).hasSum

@[simp]
theorem lsmul_zero_right (f : ℤ_[p]⟦X⟧) : lsmul d f (0 : Z) = 0 := by
  simp [lsmul]

@[simp]
theorem lsmul_zero_left (z : Z) : lsmul d (0 : ℤ_[p]⟦X⟧) z = 0 := by
  simp [lsmul]

theorem lsmul_add_right (hd : IsUnifTopNilpotent d) (f : ℤ_[p]⟦X⟧) (z w : Z) :
    lsmul d f (z + w) = lsmul d f z + lsmul d f w := by
  have h : HasSum (fun i : ℕ ↦ (coeff i f) • ((d ^ i) (z + w)))
      (lsmul d f z + lsmul d f w) := by
    simpa [map_add, smul_add] using (hasSum_lsmul hd f z).add (hasSum_lsmul hd f w)
  exact h.tsum_eq

theorem lsmul_add_left (hd : IsUnifTopNilpotent d) (f g : ℤ_[p]⟦X⟧) (z : Z) :
    lsmul d (f + g) z = lsmul d f z + lsmul d g z := by
  have h : HasSum (fun i : ℕ ↦ (coeff i (f + g)) • ((d ^ i) z))
      (lsmul d f z + lsmul d g z) := by
    simpa [map_add, add_smul] using (hasSum_lsmul hd f z).add (hasSum_lsmul hd g z)
  exact h.tsum_eq

theorem lsmul_smul_right (hd : IsUnifTopNilpotent d) (f : ℤ_[p]⟦X⟧) (a : ℤ_[p]) (z : Z) :
    lsmul d f (a • z) = a • lsmul d f z := by
  have h : HasSum (fun i : ℕ ↦ (coeff i f) • ((d ^ i) (a • z))) (a • lsmul d f z) := by
    have := HasSum.const_smul (γ := ℤ_[p]) a (hasSum_lsmul hd f z)
    refine this.congr_fun fun i ↦ ?_
    rw [map_smul, smul_comm]
  exact h.tsum_eq

theorem lsmul_monomial (hd : IsUnifTopNilpotent d) (n : ℕ) (a : ℤ_[p]) (z : Z) :
    lsmul d ((Polynomial.monomial n a : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) z = a • ((d ^ n) z) := by
  have hfun : (fun i : ℕ ↦ (coeff i ((Polynomial.monomial n a : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧))
      • ((d ^ i) z)) = fun i : ℕ ↦ if i = n then a • ((d ^ n) z) else 0 := by
    funext i
    rw [Polynomial.coeff_coe, Polynomial.coeff_monomial]
    by_cases h : i = n
    · subst h; simp
    · simp [h, Ne.symm h]
  show (∑' i : ℕ, _) = _
  rw [hfun]
  exact (hasSum_ite_eq n (a • ((d ^ n) z))).tsum_eq

@[simp]
theorem lsmul_one (hd : IsUnifTopNilpotent d) (z : Z) : lsmul d (1 : ℤ_[p]⟦X⟧) z = z := by
  have h := lsmul_monomial hd 0 (1 : ℤ_[p]) z
  rw [Polynomial.monomial_zero_left, Polynomial.C_1, Polynomial.coe_one] at h
  simpa using h

@[simp]
theorem lsmul_C (hd : IsUnifTopNilpotent d) (a : ℤ_[p]) (z : Z) :
    lsmul d (PowerSeries.C a : ℤ_[p]⟦X⟧) z = a • z := by
  have h := lsmul_monomial hd 0 a z
  rw [Polynomial.monomial_zero_left, Polynomial.coe_C] at h
  simpa using h

@[simp]
theorem lsmul_X (hd : IsUnifTopNilpotent d) (z : Z) : lsmul d (X : ℤ_[p]⟦X⟧) z = d z := by
  have h := lsmul_monomial hd 1 (1 : ℤ_[p]) z
  rw [Polynomial.monomial_one_one_eq_X, Polynomial.coe_X] at h
  simpa using h

/-! ### Continuity -/

/-- For fixed `z`, the map `f ↦ f • z` is continuous on `Λ`. -/
theorem continuous_lsmul_left (hd : IsUnifTopNilpotent d) (z : Z) :
    Continuous (fun f : ℤ_[p]⟦X⟧ ↦ lsmul d f z) := by
  set F : ℤ_[p]⟦X⟧ →+ Z :=
    AddMonoidHom.mk' (fun f ↦ lsmul d f z) (fun f g ↦ lsmul_add_left hd f g z) with hF
  refine continuous_of_continuousAt_zero F ?_
  rw [ContinuousAt, show F 0 = 0 from lsmul_zero_left (d := d) z]
  intro U hU
  obtain ⟨V, hVopen, hVclosed, hVU⟩ := exists_isOpen_isClosed_submodule_subset (p := p) hU
  obtain ⟨N, hN⟩ := hd.exists_forall_le (hVopen.mem_nhds V.zero_mem)
  have hopen : ∀ i : ℕ, IsOpen {a : ℤ_[p] | a • ((d ^ i) z) ∈ V} :=
    fun i ↦ hVopen.preimage ((continuous_id.smul continuous_const))
  set W : Set ℤ_[p]⟦X⟧ :=
    ⋂ i ∈ Finset.range N, (fun f : ℤ_[p]⟦X⟧ ↦ coeff i f) ⁻¹' {a : ℤ_[p] | a • ((d ^ i) z) ∈ V}
    with hW
  have hWopen : IsOpen W :=
    (Finset.range N).finite_toSet.isOpen_biInter fun i _ ↦
      (hopen i).preimage (WithPiTopology.continuous_coeff ℤ_[p] i)
  have hW0 : (0 : ℤ_[p]⟦X⟧) ∈ W := by
    simp only [hW, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
    intro i _
    simpa using V.zero_mem
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (hWopen.mem_nhds hW0) fun f hf ↦ ?_
  show lsmul d f z ∈ U
  refine hVU (mem_of_hasSum_mem V hVclosed (hasSum_lsmul hd f z) fun i ↦ ?_)
  by_cases hi : i < N
  · simp only [hW, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq] at hf
    exact hf i (Finset.mem_range.2 hi)
  · exact V.smul_mem _ (hN i (not_lt.1 hi) z)

/-- For fixed `f`, the map `z ↦ f • z` is continuous on `Z`. -/
theorem continuous_lsmul_right (hd : IsUnifTopNilpotent d) (hdc : Continuous d)
    (f : ℤ_[p]⟦X⟧) : Continuous (fun z : Z ↦ lsmul d f z) := by
  set F : Z →+ Z := AddMonoidHom.mk' (fun z ↦ lsmul d f z) (fun z w ↦ lsmul_add_right hd f z w)
    with hF
  refine continuous_of_continuousAt_zero F ?_
  rw [ContinuousAt, show F 0 = 0 from lsmul_zero_right (d := d) f]
  intro U hU
  obtain ⟨V, hVopen, hVclosed, hVU⟩ := exists_isOpen_isClosed_submodule_subset (p := p) hU
  obtain ⟨N, hN⟩ := hd.exists_forall_le (hVopen.mem_nhds V.zero_mem)
  have hdpow : ∀ i : ℕ, Continuous (fun w : Z ↦ (d ^ i) w) := by
    intro i
    induction i with
    | zero => simp only [pow_zero]; exact continuous_id
    | succ i ih =>
      have he : (fun w : Z ↦ (d ^ (i + 1)) w) = ((fun w : Z ↦ (d ^ i) w) ∘ (fun w : Z ↦ d w)) := by
        funext w
        simp [pow_succ, Module.End.mul_apply]
      rw [he]
      exact ih.comp hdc
  set W : Set Z := ⋂ i ∈ Finset.range N, (fun w : Z ↦ (d ^ i) w) ⁻¹' (V : Set Z) with hW
  have hWopen : IsOpen W :=
    (Finset.range N).finite_toSet.isOpen_biInter fun i _ ↦ hVopen.preimage (hdpow i)
  have hW0 : (0 : Z) ∈ W := by
    simp only [hW, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    intro i _
    simpa using V.zero_mem
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (hWopen.mem_nhds hW0) fun w hw ↦ ?_
  show lsmul d f w ∈ U
  refine hVU (mem_of_hasSum_mem V hVclosed (hasSum_lsmul hd f w) fun i ↦ ?_)
  by_cases hi : i < N
  · simp only [hW, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] at hw
    exact V.smul_mem _ (hw i (Finset.mem_range.2 hi))
  · exact V.smul_mem _ (hN i (not_lt.1 hi) w)

/-! ### Multiplicativity -/

theorem lsmul_mul_X_pow (hd : IsUnifTopNilpotent d) (f : ℤ_[p]⟦X⟧) (n : ℕ) (z : Z) :
    lsmul d (f * X ^ n) z = lsmul d f ((d ^ n) z) := by
  have hinj : Function.Injective (fun j : ℕ ↦ j + n) := fun a b h ↦ by simpa using h
  have hzero : ∀ i : ℕ, i ∉ Set.range (fun j : ℕ ↦ j + n) →
      (coeff i (f * X ^ n)) • ((d ^ i) z) = 0 := by
    intro i hi
    have hin : i < n := by
      by_contra h
      exact hi ⟨i - n, by show i - n + n = i; omega⟩
    rw [PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
    simp
  have hcomp : (fun j : ℕ ↦ (coeff (j + n) (f * X ^ n)) • ((d ^ (j + n)) z))
      = fun j : ℕ ↦ (coeff j f) • ((d ^ j) ((d ^ n) z)) := by
    funext j
    rw [PowerSeries.coeff_mul_X_pow' , if_pos (by omega),
      show j + n - n = j by omega, pow_add, Module.End.mul_apply]
  have h : HasSum (fun i : ℕ ↦ (coeff i (f * X ^ n)) • ((d ^ i) z))
      (lsmul d f ((d ^ n) z)) := by
    refine (Function.Injective.hasSum_iff hinj hzero).1 ?_
    simpa only [Function.comp_def, hcomp] using hasSum_lsmul hd f ((d ^ n) z)
  exact h.tsum_eq

theorem lsmul_mul_C (hd : IsUnifTopNilpotent d) (f : ℤ_[p]⟦X⟧) (a : ℤ_[p]) (z : Z) :
    lsmul d (f * PowerSeries.C a) z = a • lsmul d f z := by
  have h : HasSum (fun i : ℕ ↦ (coeff i (f * PowerSeries.C a)) • ((d ^ i) z))
      (a • lsmul d f z) := by
    refine (HasSum.const_smul (γ := ℤ_[p]) a (hasSum_lsmul hd f z)).congr_fun fun i ↦ ?_
    rw [PowerSeries.coeff_mul_C, mul_comm, mul_smul]
  exact h.tsum_eq

theorem lsmul_mul_monomial (hd : IsUnifTopNilpotent d) (f : ℤ_[p]⟦X⟧) (n : ℕ) (a : ℤ_[p])
    (z : Z) :
    lsmul d (f * ((Polynomial.monomial n a : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧)) z
      = a • lsmul d f ((d ^ n) z) := by
  have hm : ((Polynomial.monomial n a : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧)
      = PowerSeries.C a * X ^ n := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X]
  rw [hm, ← mul_assoc, lsmul_mul_X_pow hd, lsmul_mul_C hd]

/-- Multiplicativity of the action against a *polynomial* second factor. -/
theorem lsmul_mul_polynomial (hd : IsUnifTopNilpotent d) (f : ℤ_[p]⟦X⟧)
    (Q : Polynomial ℤ_[p]) (z : Z) :
    lsmul d (f * (Q : ℤ_[p]⟦X⟧)) z = lsmul d f (lsmul d (Q : ℤ_[p]⟦X⟧) z) := by
  induction Q using Polynomial.induction_on' with
  | add Q₁ Q₂ h₁ h₂ =>
    rw [Polynomial.coe_add, mul_add, lsmul_add_left hd, h₁, h₂, lsmul_add_left hd,
      lsmul_add_right hd]
  | monomial n a =>
    rw [lsmul_mul_monomial hd, lsmul_monomial hd, lsmul_smul_right hd]

/-- **Multiplicativity of the `Λ`-action.** -/
theorem lsmul_mul (hd : IsUnifTopNilpotent d) (hdc : Continuous d) (f g : ℤ_[p]⟦X⟧) (z : Z) :
    lsmul d (f * g) z = lsmul d f (lsmul d g z) := by
  have hA : Continuous (fun g : ℤ_[p]⟦X⟧ ↦ lsmul d (f * g) z) :=
    (continuous_lsmul_left hd z).comp (continuous_const.mul continuous_id)
  have hB : Continuous (fun g : ℤ_[p]⟦X⟧ ↦ lsmul d f (lsmul d g z)) :=
    (continuous_lsmul_right hd hdc f).comp (continuous_lsmul_left hd z)
  have := (WithPiTopology.denseRange_toPowerSeries (R := ℤ_[p])).equalizer hA hB
    (funext fun Q ↦ lsmul_mul_polynomial hd f Q z)
  exact congrFun this g

/-- `d` commutes with the `Λ`-action, being multiplication by `X`. -/
theorem apply_lsmul (hd : IsUnifTopNilpotent d) (hdc : Continuous d) (f : ℤ_[p]⟦X⟧) (z : Z) :
    d (lsmul d f z) = lsmul d f (d z) := by
  have h1 : d (lsmul d f z) = lsmul d (X * f) z := by
    rw [lsmul_mul hd hdc, lsmul_X hd]
  have h2 : lsmul d (f * X) z = lsmul d f (d z) := by
    simpa using lsmul_mul_X_pow hd f 1 z
  rw [h1, mul_comm, h2]

/-! ### The module structure -/

/-- **Blueprint node `profinite-Gamma-module-is-Lambda-module`, analytic core.**  A profinite
`ℤ_p`-module `Z` with a continuous, uniformly topologically nilpotent `ℤ_p`-linear operator
`d` is a `Λ = ℤ_p⟦X⟧`-module, with `X` acting as `d`. -/
noncomputable def lambdaModule (hd : IsUnifTopNilpotent d) (hdc : Continuous d) :
    Module ℤ_[p]⟦X⟧ Z where
  smul := lsmul d
  one_smul := lsmul_one hd
  mul_smul f g z := lsmul_mul hd hdc f g z
  smul_zero f := lsmul_zero_right (d := d) f
  smul_add := lsmul_add_right hd
  add_smul f g z := lsmul_add_left hd f g z
  zero_smul z := lsmul_zero_left (d := d) z

theorem lambdaModule_smul (hd : IsUnifTopNilpotent d) (hdc : Continuous d)
    (f : ℤ_[p]⟦X⟧) (z : Z) :
    letI := lambdaModule hd hdc
    f • z = lsmul d f z := rfl

/-! ### Joint continuity of the action -/

/-- On a compact `ℤ_p`-module, high powers of `p` move everything into a given open
submodule.  (Tube lemma.) -/
theorem exists_pow_smul_mem (V : Submodule ℤ_[p] Z) (hV : IsOpen (V : Set Z)) :
    ∃ M : ℕ, ∀ a : ℤ_[p], a ∈ (Ideal.span {(p : ℤ_[p]) ^ M} : Ideal ℤ_[p]) →
      ∀ z : Z, a • z ∈ V := by
  have hpre : IsOpen {q : ℤ_[p] × Z | q.1 • q.2 ∈ V} :=
    hV.preimage (continuous_smul (M := ℤ_[p]) (X := Z))
  have hsub : ({0} : Set ℤ_[p]) ×ˢ (Set.univ : Set Z) ⊆ {q : ℤ_[p] × Z | q.1 • q.2 ∈ V} := by
    rintro ⟨a, z⟩ ⟨ha, -⟩
    simp only [Set.mem_singleton_iff] at ha
    simp [ha, V.zero_mem]
  obtain ⟨u, v, huo, -, hsu, hvu, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_univ (X := Z)) hpre hsub
  obtain ⟨M, hM⟩ := exists_span_p_pow_subset (p := p) (huo.mem_nhds (hsu rfl))
  exact ⟨M, fun a ha z ↦ huv (show ((a, z) : ℤ_[p] × Z) ∈ u ×ˢ v from
    ⟨hM ha, hvu (Set.mem_univ z)⟩)⟩

/-- **Uniform continuity of the action in the scalar.**  For every open closed submodule `V`
there is a neighbourhood `W` of `0` in `Λ` with `W • Z ⊆ V`. -/
theorem exists_nhds_zero_lsmul_mem (hd : IsUnifTopNilpotent d) (V : Submodule ℤ_[p] Z)
    (hVopen : IsOpen (V : Set Z)) (hVclosed : IsClosed (V : Set Z)) :
    ∃ W : Set ℤ_[p]⟦X⟧, W ∈ 𝓝 (0 : ℤ_[p]⟦X⟧) ∧ ∀ f ∈ W, ∀ z : Z, lsmul d f z ∈ V := by
  obtain ⟨N, hN⟩ := hd.exists_forall_le (hVopen.mem_nhds V.zero_mem)
  obtain ⟨M, hM⟩ := exists_pow_smul_mem V hVopen
  set W : Set ℤ_[p]⟦X⟧ := ⋂ i ∈ Finset.range N,
    (fun f : ℤ_[p]⟦X⟧ ↦ coeff i f) ⁻¹'
      ((Ideal.span {(p : ℤ_[p]) ^ M} : Ideal ℤ_[p]) : Set ℤ_[p]) with hWdef
  have hWopen : IsOpen W := (Finset.range N).finite_toSet.isOpen_biInter fun i _ ↦
    (isOpen_span_p_pow M).preimage (WithPiTopology.continuous_coeff ℤ_[p] i)
  have hW0 : (0 : ℤ_[p]⟦X⟧) ∈ W := by
    simp only [hWdef, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    intro i _
    simpa using Submodule.zero_mem _
  refine ⟨W, hWopen.mem_nhds hW0, fun f hf z ↦ ?_⟩
  refine mem_of_hasSum_mem V hVclosed (hasSum_lsmul hd f z) fun i ↦ ?_
  by_cases hi : i < N
  · simp only [hWdef, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] at hf
    exact hM _ (hf i (Finset.mem_range.2 hi)) _
  · exact V.smul_mem _ (hN i (not_lt.1 hi) z)

/-- **The `Λ`-action is jointly continuous.** -/
theorem continuous_lsmul_uncurry (hd : IsUnifTopNilpotent d) (hdc : Continuous d) :
    Continuous (fun q : ℤ_[p]⟦X⟧ × Z ↦ lsmul d q.1 q.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨f₀, w₀⟩
  rw [ContinuousAt, Filter.tendsto_def]
  intro U hU
  have hU0 : (fun v : Z ↦ lsmul d f₀ w₀ + v) ⁻¹' U ∈ 𝓝 (0 : Z) := by
    have hc : Continuous fun v : Z ↦ lsmul d f₀ w₀ + v := continuous_const.add continuous_id
    simpa using hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨V, hVopen, hVclosed, hVU⟩ := exists_isOpen_isClosed_submodule_subset (p := p) hU0
  obtain ⟨W, hW, hWmem⟩ := exists_nhds_zero_lsmul_mem hd V hVopen hVclosed
  have hS : (fun f : ℤ_[p]⟦X⟧ ↦ f - f₀) ⁻¹' W ∈ 𝓝 f₀ := by
    have hc : Continuous fun f : ℤ_[p]⟦X⟧ ↦ f - f₀ := continuous_id.sub continuous_const
    simpa using hc.continuousAt.preimage_mem_nhds (by simpa using hW)
  have hT : {w : Z | lsmul d f₀ w - lsmul d f₀ w₀ ∈ V} ∈ 𝓝 w₀ := by
    refine IsOpen.mem_nhds (hVopen.preimage ?_) (by simpa using V.zero_mem)
    exact (continuous_lsmul_right hd hdc f₀).sub continuous_const
  refine Filter.mem_of_superset (prod_mem_nhds hS hT) ?_
  rintro ⟨f, w⟩ ⟨hf, hw⟩
  simp only [Set.mem_preimage] at hf
  simp only [Set.mem_setOf_eq] at hw
  show lsmul d f w ∈ U
  have hsum : lsmul d f w = lsmul d f₀ w₀ +
      ((lsmul d f₀ w - lsmul d f₀ w₀) + lsmul d (f - f₀) w) := by
    have := lsmul_add_left hd (f - f₀) f₀ w
    rw [sub_add_cancel] at this
    rw [this]
    abel
  rw [hsum]
  exact hVU (V.add_mem hw (hWmem _ hf w))

/-- The `Λ`-module structure of `IwasawaAlgebra.lambdaModule` is continuous. -/
theorem continuousSMul_lambdaModule (hd : IsUnifTopNilpotent d) (hdc : Continuous d) :
    letI := lambdaModule hd hdc
    ContinuousSMul ℤ_[p]⟦X⟧ Z :=
  letI := lambdaModule hd hdc
  ⟨continuous_lsmul_uncurry hd hdc⟩

/-- The `Λ`-module structure of `IwasawaAlgebra.lambdaModule` restricts to the given
`ℤ_p`-module structure along `ℤ_p → Λ`. -/
theorem isScalarTower_lambdaModule (hd : IsUnifTopNilpotent d) (hdc : Continuous d) :
    letI := lambdaModule hd hdc
    IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ Z := by
  letI := lambdaModule hd hdc
  refine ⟨fun a f z ↦ ?_⟩
  show lsmul d (a • f) z = a • lsmul d f z
  rw [show a • f = f * PowerSeries.C a by
    rw [mul_comm]; exact (PowerSeries.smul_eq_C_mul f a)]
  exact lsmul_mul_C hd f a z

/-- **Uniqueness.**  A continuous `Λ`-module structure on `Z` extending the `ℤ_p`-structure and
sending `X` to `d` is unique: it must be `IwasawaAlgebra.lsmul`. -/
theorem eq_lsmul_of_continuous {σ : ℤ_[p]⟦X⟧ → Z → Z} (hd : IsUnifTopNilpotent d)
    (hadd : ∀ f g z, σ (f + g) z = σ f z + σ g z)
    (hcont : ∀ z, Continuous fun f ↦ σ f z)
    (hpoly : ∀ (n : ℕ) (a : ℤ_[p]) (z : Z),
      σ ((Polynomial.monomial n a : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) z = a • ((d ^ n) z))
    (f : ℤ_[p]⟦X⟧) (z : Z) : σ f z = lsmul d f z := by
  have hagree : ∀ Q : Polynomial ℤ_[p], σ (Q : ℤ_[p]⟦X⟧) z = lsmul d (Q : ℤ_[p]⟦X⟧) z := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add Q₁ Q₂ h₁ h₂ => rw [Polynomial.coe_add, hadd, h₁, h₂, lsmul_add_left hd]
    | monomial n a => rw [hpoly, lsmul_monomial hd]
  have := (WithPiTopology.denseRange_toPowerSeries (R := ℤ_[p])).equalizer (hcont z)
    (continuous_lsmul_left hd z) (funext hagree)
  exact congrFun this f

end Action

end IwasawaAlgebra
