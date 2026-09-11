/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.LocalGalois
public import Iwasawalib.NumberTheory.LocalCFT.DecompositionAction
public import Iwasawalib.GroupCohomology.InducedTate
public import Mathlib.FieldTheory.Galois.NormalBasis

@[expose] public section

/-!
# The normal basis of `L_w / K_v`, indexed by the decomposition group

`Iwasawalib/NumberTheory/CFT/LocalGalois.lean` proves that the completion `L_w` is a finite
Galois extension of `K_v` with group `D_w` (`NumberField.decompositionGroupEquivLocalGal`), so
Mathlib's normal basis theorem applies: `L_w` has a `K_v`-basis which is a single `D_w`-orbit.
Reindexing that basis by the decomposition group itself gives

`NumberField.decompositionNormalBasis : Module.Basis (decompositionGroup K L w) K_v L_w`

with `decompositionNormalBasis d = d • decompositionNormalBasis 1`
(`NumberField.decompositionNormalBasis_apply`).  In other words `L_w` is, as a `D_w`-module,
the regular module `K_v[D_w]`.

The cohomological consequence is immediate from
`CyclicTate.herbrand_eq_one_of_regularLattice`:

`NumberField.herbrand_adicCompletion_eq_one : h(D_w, L_w⁺) = 1`,

the **additive** local Herbrand quotient, *unconditionally at every finite place* — no
hypothesis on the ramification, in particular none on the residue characteristic.  This is the
first half of the classical computation `h(D_w, O_w^×) = 1`; the second half compares the
lattice `O_w` with the `O_v`-lattice spanned by a normal basis, and then the unit filtration
with the additive one.  See the scope discussion in
`Iwasawalib/NumberTheory/LocalCFT/LocalNormIndex.lean`.

## Main statements

* `NumberField.decompositionNormalBasis`, `NumberField.decompositionNormalBasis_apply`.
* `NumberField.smul_adicCompletion_smul`: the decomposition group acts `K_v`-linearly.
* `NumberField.herbrand_adicCompletion_eq_one`: `h(D_w, L_w⁺) = 1`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero

namespace NumberField

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] adicCompletionComapAlgebra

omit [IsGalois K L] in
/-- The action of the decomposition group on `L_w` is the local Galois action. -/
theorem toLocalGal_eq_smul (d : decompositionGroup K L w) (y : w.adicCompletion L) :
    toLocalGal v w d y = d • y := rfl

omit [IsGalois K L] in
/-- **The decomposition group acts `K_v`-linearly on `L_w`.** -/
theorem smul_adicCompletion_smul (d : decompositionGroup K L w) (c : v.adicCompletion K)
    (y : w.adicCompletion L) : d • (c • y) = c • (d • y) := by
  rw [Algebra.smul_def, Algebra.smul_def,
    ← toLocalGal_eq_smul v w d (algebraMap (v.adicCompletion K) (w.adicCompletion L) c * y),
    map_mul, AlgEquiv.commutes, toLocalGal_eq_smul]

/-- **A normal basis of `L_w / K_v`, indexed by the decomposition group.**  It is the orbit of
a single element under `D_w` (`NumberField.decompositionNormalBasis_apply`), so `L_w` is the
regular `K_v`-representation of `D_w`. -/
def decompositionNormalBasis :
    Module.Basis (decompositionGroup K L w) (v.adicCompletion K) (w.adicCompletion L) :=
  (IsGalois.normalBasis (v.adicCompletion K) (w.adicCompletion L)).reindex
    (decompositionGroupEquivLocalGal v w).toEquiv.symm

theorem decompositionNormalBasis_apply (d : decompositionGroup K L w) :
    decompositionNormalBasis v w d = d • decompositionNormalBasis v w 1 := by
  have key : ∀ g : decompositionGroup K L w,
      (decompositionGroupEquivLocalGal v w).toEquiv g = toLocalGal v w g := fun _ ↦ rfl
  have h1 : toLocalGal v w 1 = 1 := map_one (decompositionGroupEquivLocalGal v w)
  rw [decompositionNormalBasis, Module.Basis.reindex_apply, Module.Basis.reindex_apply]
  simp only [Equiv.symm_symm]
  rw [key, key, h1, IsGalois.normalBasis_apply, toLocalGal_eq_smul]

/-- Translating the index of the normal basis is the action. -/
theorem decompositionNormalBasis_mul (g d : decompositionGroup K L w) :
    decompositionNormalBasis v w (g * d) = g • decompositionNormalBasis v w d := by
  rw [decompositionNormalBasis_apply v w (g * d), decompositionNormalBasis_apply v w d,
    mul_smul]

variable [Fintype (decompositionGroup K L w)] {σ : decompositionGroup K L w}

include v

/-- **`h(D_w, L_w⁺) = 1` at every finite place.**

The additive group of the completion is the regular `K_v`-representation of the decomposition
group — this is the normal basis theorem for the local extension `L_w / K_v`
(`NumberField.decompositionNormalBasis`) — and an induced module has trivial Tate cohomology
(`CyclicTate.herbrand_eq_one_of_regularLattice`).

There is **no hypothesis on the ramification**: unlike `h(D_w, O_w^×)`, the additive Herbrand
quotient of the field is unconditional, including in the wildly ramified case. -/
theorem herbrand_adicCompletion_eq_one
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) :
    CyclicTate.herbrand (decompositionGroup K L w) (w.adicCompletion L) σ = 1 := by
  classical
  have hgen : ∀ d : decompositionGroup K L w, ∃ k : ℕ, σ ^ k = d := fun d ↦ by
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff d σ).1 (mem_powers_iff_mem_zpowers.2 (hσ d))
    exact ⟨k, hk⟩
  set b := decompositionNormalBasis v w with hb
  -- the coordinate map, as an additive homomorphism
  set f : (decompositionGroup K L w → v.adicCompletion K) →+ w.adicCompletion L :=
    (b.equivFun.symm : _ →ₗ[v.adicCompletion K] _).toAddMonoidHom with hf
  have hfapply : ∀ F : decompositionGroup K L w → v.adicCompletion K,
      f F = ∑ d : decompositionGroup K L w, F d • b d := fun F ↦ by
    rw [hf]
    exact b.equivFun_symm_apply F
  refine CyclicTate.herbrand_eq_one_of_regularLattice hgen f (fun g F ↦ ?_) ?_ ?_
  · rw [hfapply, hfapply, Finset.smul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun d ↦ ?_).symm
    rw [smul_adicCompletion_smul, ← decompositionNormalBasis_mul, ← hb]
    show F d • b (g * d) = F (g⁻¹ * (g * d)) • b (g * d)
    rw [inv_mul_cancel_left]
  · exact fun F F' h ↦ b.equivFun.symm.injective h
  · have htop : f.range = ⊤ := by
      rw [AddMonoidHom.range_eq_top]
      exact fun y ↦ ⟨b.equivFun y, b.equivFun.symm_apply_apply y⟩
    rw [htop]
    haveI : Subsingleton (w.adicCompletion L ⧸ (⊤ : AddSubgroup (w.adicCompletion L))) :=
      QuotientAddGroup.subsingleton_quotient_top
    infer_instance

end NumberField
