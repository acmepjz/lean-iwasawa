/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.LocalNormIndex
public import Iwasawalib.NumberTheory.LocalCFT.IntegralNormalBasis
public import Iwasawalib.NumberTheory.LocalCFT.UnitPowerIndex

@[expose] public section

/-!
# The local norm index in the wild case, and exactly what is still missing

At an arbitrary finite place the two halves of the local invariant map stand as follows.

* `Ĥ¹(D_w, L_w^×) = 0` is unconditional
  (`NumberField.subsingleton_tateH1_adicCompletionUnits`).
* `#Ĥ⁰(D_w, L_w^×) = #D_w` follows from `h(D_w, L_w^×) = #D_w`
  (`LocalCFT.card_tateH0_units_of_faithful_of_herbrand`), and the valuation sequence reduces
  that to `h(D_w, O_w^×) = 1` (`LocalCFT.herbrand_units_eq_mul`).

So the whole ramified local theory rests on `h(D_w, O_w^×) = 1`, and this file records the
reduction (`NumberField.card_tateH0_adicCompletionUnits_of_herbrand_integers_units`).

**What is now available and what is not.**  The *additive* statement `h(D_w, O_w⁺) = 1` is
proved unconditionally in `Iwasawalib/NumberTheory/LocalCFT/IntegralNormalBasis.lean`, at every
finite place including the wildly ramified ones: `L_w` is `K_v[D_w]` by the normal basis
theorem, an `O_v`-lattice inside it spanned by an orbit is `O_v[D_w]`-free and therefore
cohomologically trivial, and it has finite index in `O_w`.

What is missing is *only* the comparison of the multiplicative filtration with the additive one:
an isomorphism of `D_w`-modules `U^(m) ≅ 𝔪^m` for `m` large.  Both sides are commensurable with
their ambient groups (`LocalCFT.finite_quotient_unitFiltration` on the multiplicative side,
`LocalCFT.finite_quotient_of_valBall_le` on the additive side), so such an isomorphism would
give `h(O_w^×) = h(O_w⁺) = 1` and hence the local norm index at every finite place.  The
classical construction of that isomorphism is the `p`-adic logarithm, which Mathlib does not
have for a complete discretely valued field of mixed characteristic.  Note that the naive
substitute — multiplying by a uniformiser to move `𝔪^m` back to `O_w` — is *not* equivariant at
a ramified place, where no uniformiser is `D_w`-fixed; that is why the additive statement had to
be proved for `O_w` itself rather than for a single graded piece.

## Main statements

* `NumberField.herbrand_adicCompletion_units_eq_card_of_herbrand_integers_units`
* `NumberField.card_tateH0_adicCompletionUnits_of_herbrand_integers_units`
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero LocalCFT
open scoped WithZero

namespace NumberField

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] decompositionIntegersMulSemiringAction
  Units.mulDistribMulActionRight

variable [Fintype (decompositionGroup K L w)] {σ : decompositionGroup K L w}

omit [NumberField K] [IsGalois K L] in
/-- **`h(D_w, L_w^×) = #D_w` follows from `h(D_w, O_w^×) = 1`**, at every finite place.

This is the valuation sequence `0 → O_w^× → L_w^× → ℤ → 0` and nothing else; the hypothesis
`hunit` is the only thing that is still open in the wildly ramified case. -/
theorem herbrand_adicCompletion_units_eq_card_of_herbrand_integers_units
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ)
    [Finite (CyclicTate.TateH0 (decompositionGroup K L w)
      (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ)]
    [Finite (CyclicTate.TateH1 (decompositionGroup K L w)
      (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ)]
    (hunit : CyclicTate.herbrand (decompositionGroup K L w)
      (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ = 1) :
    CyclicTate.herbrand (decompositionGroup K L w) (Additive (w.adicCompletion L)ˣ) σ
      = (Nat.card (decompositionGroup K L w) : ℚ) := by
  have hgen : ∀ d : decompositionGroup K L w, ∃ k : ℕ, σ ^ k = d := fun d ↦ by
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff d σ).1 (mem_powers_iff_mem_zpowers.2 (hσ d))
    exact ⟨k, hk⟩
  have hπ : ∃ π : w.adicCompletion L, (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ) :=
    valuedAdicCompletion_surjective (K := L) w (exp (-1 : ℤ))
  rw [LocalCFT.herbrand_units_eq_mul (F := w.adicCompletion L)
      (G := decompositionGroup K L w) (valued_decomposition_smul w) (fun _ _ ↦ rfl) hgen hπ,
    hunit, one_mul]

omit [NumberField K] [IsGalois K L] in
/-- **The local norm index `#(K_v^× / N L_w^×) = [L_w : K_v]` follows from
`h(D_w, O_w^×) = 1`**, at every finite place, with no hypothesis on the ramification. -/
theorem card_tateH0_adicCompletionUnits_of_herbrand_integers_units
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ)
    [Finite (CyclicTate.TateH0 (decompositionGroup K L w)
      (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ)]
    [Finite (CyclicTate.TateH1 (decompositionGroup K L w)
      (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ)]
    (hunit : CyclicTate.herbrand (decompositionGroup K L w)
      (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ = 1) :
    Nat.card (CyclicTate.TateH0 (decompositionGroup K L w)
      (Additive (w.adicCompletion L)ˣ) σ) = Nat.card (decompositionGroup K L w) :=
  LocalCFT.card_tateH0_units_of_faithful_of_herbrand hσ
    (decompositionGroup_smul_injective w)
    (herbrand_adicCompletion_units_eq_card_of_herbrand_integers_units w hσ hunit)

include v in
/-- **`h(D_w, O_w^×) = 1` would follow from an equivariant comparison of `O_w^×` with `O_w⁺`
having finite kernel and cokernel**, because `h(D_w, O_w⁺) = 1` is now known unconditionally
(`NumberField.herbrand_adicCompletionIntegers_eq_one`).

The hypothesis is stated for a map out of the *additive* group because that is the side whose
Tate cohomology is known to be finite.  It is stronger than what the classical argument
produces — the logarithm compares the finite-index subgroups `𝔪^m` and `U^(m)`, not the whole
groups — so a caller who has only the filtered comparison should instead chain
`CyclicTate.herbrand_eq_of_finite_ker_coker` twice and use
`NumberField.herbrand_adicCompletionIntegers_eq_one` directly. -/
theorem herbrand_adicCompletionIntegers_units_eq_one_of_comparison
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ)
    (f : (LocalCFT.integers (F := w.adicCompletion L)) →+[decompositionGroup K L w]
      Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ)
    [Finite f.toAddMonoidHom.ker]
    [Finite (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ ⧸
      f.toAddMonoidHom.range)] :
    CyclicTate.herbrand (decompositionGroup K L w)
      (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ = 1 := by
  haveI := finite_tateH0_adicCompletionIntegers v w hσ
  haveI := finite_tateH1_adicCompletionIntegers v w hσ
  rw [← CyclicTate.herbrand_eq_of_finite_ker_coker f σ]
  exact herbrand_adicCompletionIntegers_eq_one v w hσ

/-! ## The additive side of the comparison, ready for the logarithm -/

omit [NumberField K] [IsGalois K L] in
/-- `𝔪^k` is a `D_w`-stable subgroup of `O_w`: the decomposition group preserves the
valuation. -/
instance isStableSubgroup_valBall (k : ℕ) :
    CyclicTate.IsStableSubgroup (decompositionGroup K L w)
      (LocalCFT.valBall (w.adicCompletion L) k) where
  smul_mem d {x} hx := by
    rw [LocalCFT.mem_valBall] at hx ⊢
    rw [coe_decomposition_smul_integers, valued_decomposition_smul w]
    exact hx

include v in
/-- The Tate cohomology of `𝔪^k` is finite. -/
theorem finite_tate_valBall
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) (k : ℕ) :
    Finite (CyclicTate.TateH0 (decompositionGroup K L w)
        (LocalCFT.valBall (w.adicCompletion L) k) σ) ∧
      Finite (CyclicTate.TateH1 (decompositionGroup K L w)
        (LocalCFT.valBall (w.adicCompletion L) k) σ) := by
  haveI : Finite (IsLocalRing.ResidueField
      (LocalCFT.integers (F := w.adicCompletion L))) :=
    HeightOneSpectrum.finite_residueField (F := L) w
  obtain ⟨π, hπ⟩ := valuedAdicCompletion_surjective (K := L) w (exp (-1 : ℤ))
  haveI : Finite (LocalCFT.integers (F := w.adicCompletion L) ⧸
      LocalCFT.valBall (w.adicCompletion L) k) :=
    LocalCFT.finite_quotient_of_valBall_le (π := π) hπ (le_refl _)
  haveI := finite_tateH0_adicCompletionIntegers v w hσ
  haveI := finite_tateH1_adicCompletionIntegers v w hσ
  have h₂ := CyclicTate.isShortExact_stableQuotient (decompositionGroup K L w)
    (LocalCFT.valBall (w.adicCompletion L) k)
  exact ⟨h₂.finite_tateH0_left σ, h₂.finite_tateH1_left σ⟩

include v in
/-- **`h(D_w, 𝔪^k) = 1` for every `k`**, at every finite place.

`𝔪^k` has finite index in `O_w` (`LocalCFT.finite_quotient_of_valBall_le`) and
`h(D_w, O_w⁺) = 1` (`NumberField.herbrand_adicCompletionIntegers_eq_one`), so the graded step of
the additive filtration is cohomologically trivial as well.  This is the additive half of the
comparison `U^(m) ≅ 𝔪^m`: a `D_w`-equivariant map between `U^(m)` and `𝔪^k` with finite kernel
and cokernel — what the `p`-adic logarithm provides — now immediately yields
`h(D_w, O_w^×) = 1` and therefore the local norm index in the wild case. -/
theorem herbrand_valBall_eq_one
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) (k : ℕ) :
    CyclicTate.herbrand (decompositionGroup K L w)
      (LocalCFT.valBall (w.adicCompletion L) k) σ = 1 := by
  haveI : Finite (IsLocalRing.ResidueField
      (LocalCFT.integers (F := w.adicCompletion L))) :=
    HeightOneSpectrum.finite_residueField (F := L) w
  obtain ⟨π, hπ⟩ := valuedAdicCompletion_surjective (K := L) w (exp (-1 : ℤ))
  haveI : Finite (LocalCFT.integers (F := w.adicCompletion L) ⧸
      LocalCFT.valBall (w.adicCompletion L) k) :=
    LocalCFT.finite_quotient_of_valBall_le (π := π) hπ (le_refl _)
  haveI := finite_tateH0_adicCompletionIntegers v w hσ
  haveI := finite_tateH1_adicCompletionIntegers v w hσ
  have h₂ := CyclicTate.isShortExact_stableQuotient (decompositionGroup K L w)
    (LocalCFT.valBall (w.adicCompletion L) k)
  haveI : Finite (CyclicTate.TateH0 (decompositionGroup K L w)
    (LocalCFT.integers (F := w.adicCompletion L) ⧸
      LocalCFT.valBall (w.adicCompletion L) k) σ) := inferInstance
  haveI : Finite (CyclicTate.TateH1 (decompositionGroup K L w)
    (LocalCFT.integers (F := w.adicCompletion L) ⧸
      LocalCFT.valBall (w.adicCompletion L) k) σ) := inferInstance
  haveI := h₂.finite_tateH0_left σ
  haveI := h₂.finite_tateH1_left σ
  have hmul := h₂.herbrand_eq_mul σ
  rw [herbrand_adicCompletionIntegers_eq_one v w hσ,
    CyclicTate.herbrand_eq_one_of_finite (M := LocalCFT.integers (F := w.adicCompletion L) ⧸
      LocalCFT.valBall (w.adicCompletion L) k) σ, mul_one] at hmul
  exact hmul.symm

/-! ## The reduction of the wild case to the logarithm, in its exact form -/

include v in
/-- **The local norm index at an arbitrary finite place, reduced to the logarithm.**

The hypothesis `f` is exactly what the `p`-adic exponential/logarithm supplies: a `D_w`-map
between a ball `𝔪^k` of the additive filtration and a step `U^(m)` of the unit filtration, with
finite kernel and cokernel (an isomorphism in the classical construction, for `k = m` large).
Everything else is now in place:

* `h(D_w, 𝔪^k) = 1` (`NumberField.herbrand_valBall_eq_one`), which rests on the integral normal
  basis lattice;
* `U^(m)` has finite index in `O_w^×` (`LocalCFT.finite_quotient_unitFiltration`);
* the valuation sequence turns `h(O_w^×) = 1` into `h(L_w^×) = #D_w`
  (`LocalCFT.herbrand_units_eq_mul`);
* `Ĥ¹(D_w, L_w^×) = 0` is Hilbert 90, unconditional.

So this is the whole of the ramified local norm index, modulo the one analytic input Mathlib
does not have. -/
theorem card_tateH0_adicCompletionUnits_of_expComparison
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) {k m : ℕ}
    (f : (LocalCFT.valBall (w.adicCompletion L) k) →+[decompositionGroup K L w]
      Additive (LocalCFT.unitFiltration (F := w.adicCompletion L) m))
    (hker : Finite f.toAddMonoidHom.ker)
    (hcoker : Finite (Additive (LocalCFT.unitFiltration (F := w.adicCompletion L) m) ⧸
      f.toAddMonoidHom.range)) :
    Nat.card (CyclicTate.TateH0 (decompositionGroup K L w)
      (Additive (w.adicCompletion L)ˣ) σ) = Nat.card (decompositionGroup K L w) := by
  haveI : Finite (IsLocalRing.ResidueField
      (LocalCFT.integers (F := w.adicCompletion L))) :=
    HeightOneSpectrum.finite_residueField (F := L) w
  haveI := LocalCFT.finite_quotient_unitFiltration_one (F := w.adicCompletion L)
  obtain ⟨π, hπ⟩ := valuedAdicCompletion_surjective (K := L) w (exp (-1 : ℤ))
  haveI : Finite ((LocalCFT.integers (F := w.adicCompletion L))ˣ ⧸
      LocalCFT.unitFiltration (F := w.adicCompletion L) m) :=
    LocalCFT.finite_quotient_unitFiltration (π := π) hπ m
  obtain ⟨hf0, hf1⟩ := finite_tate_valBall v w hσ k
  haveI := hf0
  haveI := hf1
  haveI := hker
  haveI := hcoker
  -- `h(U^(m)) = h(𝔪^k) = 1`
  have hU : CyclicTate.herbrand (decompositionGroup K L w)
      (Additive (LocalCFT.unitFiltration (F := w.adicCompletion L) m)) σ = 1 := by
    rw [← CyclicTate.herbrand_eq_of_finite_ker_coker f σ]
    exact herbrand_valBall_eq_one v w hσ k
  haveI := CyclicTate.finite_tateH0_of_finite_ker_coker f σ
  haveI := CyclicTate.finite_tateH1_of_finite_ker_coker f σ
  -- `h(O_w^×) = h(U^(m)) = 1`
  let incl : Additive (LocalCFT.unitFiltration (F := w.adicCompletion L) m)
      →+[decompositionGroup K L w] Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ :=
    { LocalCFT.unitFiltrationIncl (w.adicCompletion L) m with
      map_smul' := fun _ _ ↦ rfl }
  haveI : Finite incl.toAddMonoidHom.ker := by
    have h0 : incl.toAddMonoidHom.ker = ⊥ :=
      (AddMonoidHom.ker_eq_bot_iff _).2 (LocalCFT.unitFiltrationIncl_injective m)
    rw [h0]
    infer_instance
  haveI : Finite (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ ⧸
      incl.toAddMonoidHom.range) :=
    LocalCFT.finite_quotient_range_unitFiltrationIncl (F := w.adicCompletion L) (m := m)
  have hOx : CyclicTate.herbrand (decompositionGroup K L w)
      (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ = 1 := by
    rw [← CyclicTate.herbrand_eq_of_finite_ker_coker incl σ]
    exact hU
  haveI := CyclicTate.finite_tateH0_of_finite_ker_coker incl σ
  haveI := CyclicTate.finite_tateH1_of_finite_ker_coker incl σ
  exact card_tateH0_adicCompletionUnits_of_herbrand_integers_units w hσ hOx

end NumberField
