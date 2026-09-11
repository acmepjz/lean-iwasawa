/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.Unramified
public import Iwasawalib.NumberTheory.CFT.PermutationLattice

@[expose] public section

/-!
# The Herbrand quotient of the units of a local field

For a complete discretely valued field `F` with a finite cyclic group `G` acting by
valuation-preserving ring automorphisms, the valuation gives a short exact sequence of
`G`-modules

`0 → 𝒪ˣ → Fˣ → ℤ → 0`

with `ℤ` carrying the trivial action (presented as `PermLattice G Unit`).  Multiplicativity of
the Herbrand quotient therefore gives

`h(Fˣ) = h(𝒪ˣ) · #G`.

Combined with `h(𝒪ˣ) = 1`, which
`Iwasawalib/NumberTheory/LocalCFT/Unramified.lean` proves at an unramified place of a number
field, this is the local class field theory input `h(L_w^×) = #D_w = [L_w : K_v]`.

## Main statements

* `LocalCFT.valZ`: the valuation `Fˣ →* Multiplicative ℤ`.
* `LocalCFT.isShortExact_valHom`: the short exact sequence `0 → 𝒪ˣ → Fˣ → ℤ → 0`.
* `LocalCFT.herbrand_units_eq_mul`: `h(Fˣ) = h(𝒪ˣ) · #G`.
* `NumberField.herbrand_adicCompletion_units_eq_card`: `h(D_w, L_w^×) = #D_w` at an unramified
  place.
-/

noncomputable section

open WithZero CyclicTate

namespace LocalCFT

variable {F : Type*} [Field F] [Valued F ℤᵐ⁰]

/-! ## The valuation of a unit -/

/-- The valuation of a unit of `F`, as an element of `Multiplicative ℤ`. -/
def valZ : Fˣ →* Multiplicative ℤ :=
  (WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom.comp
    (Units.map (Valued.v : Valuation F ℤᵐ⁰).toMonoidWithZeroHom.toMonoidHom)

@[simp] theorem coe_valZ (u : Fˣ) :
    ((valZ u : Multiplicative ℤ) : ℤᵐ⁰) = Valued.v (u : F) := by
  rw [valZ]
  exact WithZero.coe_unitsWithZeroEquiv_eq_units_val _

theorem valZ_eq_one_iff (u : Fˣ) : valZ u = 1 ↔ (Valued.v (u : F) : ℤᵐ⁰) = 1 := by
  rw [← coe_valZ u]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    exact WithZero.coe_injective (by rw [h]; rfl)

attribute [local instance] Units.mulDistribMulActionRight

theorem valZ_smul {G : Type*} [Group G] [MulSemiringAction G F]
    (hG : ∀ (g : G) (x : F), (Valued.v (g • x) : ℤᵐ⁰) = Valued.v x) (g : G) (u : Fˣ) :
    valZ (g • u) = valZ u := by
  refine WithZero.coe_injective ?_
  rw [coe_valZ, coe_valZ]
  exact hG g (u : F)

/-! ## The short exact sequence `0 → 𝒪ˣ → Fˣ → ℤ → 0` -/

section ShortExact

variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G F]
  [MulSemiringAction G (integers (F := F))]
  (hG : ∀ (g : G) (x : F), (Valued.v (g • x) : ℤᵐ⁰) = Valued.v x)
  (hcompat : ∀ (g : G) (a : integers (F := F)),
    ((g • a : integers (F := F)) : F) = g • (a : F))

/-- The inclusion `𝒪ˣ → Fˣ`, as an equivariant map of additive `G`-modules. -/
def unitsInclusion :
    Additive (integers (F := F))ˣ →+[G] Additive Fˣ where
  toFun u := Additive.ofMul (Units.map (integers (F := F)).subtype.toMonoidHom u.toMul)
  map_smul' g u := congrArg Additive.ofMul
    (Units.ext (hcompat g (u.toMul : integers (F := F))))
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The valuation `Fˣ → ℤ`, as an equivariant map of additive `G`-modules, with `ℤ` presented
as the permutation lattice of a point so that it carries the trivial action. -/
def valHom : Additive Fˣ →+[G] PermLattice G Unit where
  toFun u := PermLattice.ofFun fun _ ↦ Multiplicative.toAdd (valZ u.toMul)
  map_smul' g u := PermLattice.ext fun _ ↦ by
    rw [PermLattice.eval_smul, PermLattice.eval_ofFun, PermLattice.eval_ofFun]
    exact congrArg Multiplicative.toAdd (valZ_smul hG g u.toMul)
  map_zero' := PermLattice.ext fun _ ↦ by
    rw [PermLattice.eval_ofFun]
    exact congrArg Multiplicative.toAdd (map_one valZ)
  map_add' u u' := PermLattice.ext fun _ ↦ by
    simp only [PermLattice.eval_ofFun, PermLattice.eval_add]
    exact congrArg Multiplicative.toAdd (map_mul valZ u.toMul u'.toMul)

/-- **The short exact sequence `0 → 𝒪ˣ → Fˣ → ℤ → 0`** given by the valuation. -/
theorem isShortExact_valHom (hπ : ∃ π : F, (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ)) :
    CyclicTate.IsShortExact (unitsInclusion hcompat) (valHom hG) where
  inj := by
    intro u u' huu
    have h' : (Units.map (integers (F := F)).subtype.toMonoidHom u.toMul : Fˣ)
        = Units.map (integers (F := F)).subtype.toMonoidHom u'.toMul := huu
    exact Units.ext (Subtype.ext (congrArg Units.val h'))
  surj := by
    intro f
    obtain ⟨π, hπv⟩ := hπ
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπv
      exact exp_ne_zero hπv.symm
    have hval : valZ (Units.mk0 π hπ0) = Multiplicative.ofAdd (-1 : ℤ) :=
      WithZero.coe_injective (by rw [coe_valZ]; exact hπv)
    refine ⟨Additive.ofMul ((Units.mk0 π hπ0) ^ (-(PermLattice.eval f ()))), ?_⟩
    refine PermLattice.ext fun x ↦ ?_
    obtain ⟨⟩ := x
    show Multiplicative.toAdd (valZ ((Units.mk0 π hπ0) ^ (-(PermLattice.eval f ()))))
      = PermLattice.eval f ()
    rw [map_zpow, hval]
    simp
  exact := by
    intro u
    constructor
    · intro hu
      have h0 : Multiplicative.toAdd (valZ u.toMul)
          = Multiplicative.toAdd (1 : Multiplicative ℤ) :=
        congrArg (fun z ↦ PermLattice.eval z ()) hu
      have h1 : (Valued.v ((u.toMul : Fˣ) : F) : ℤᵐ⁰) = 1 :=
        (valZ_eq_one_iff _).1 (Multiplicative.toAdd.injective h0)
      refine ⟨Additive.ofMul (unitOfValuedEqOne h1), ?_⟩
      exact congrArg Additive.ofMul (Units.ext rfl)
    · rintro ⟨a, rfl⟩
      refine PermLattice.ext fun x ↦ ?_
      obtain ⟨⟩ := x
      show Multiplicative.toAdd (valZ (Units.map (integers (F := F)).subtype.toMonoidHom a.toMul))
        = PermLattice.eval (0 : PermLattice G Unit) ()
      have : (Valued.v ((Units.map (integers (F := F)).subtype.toMonoidHom a.toMul : Fˣ) : F)
          : ℤᵐ⁰) = 1 := valued_coe_units a.toMul
      rw [show valZ (Units.map (integers (F := F)).subtype.toMonoidHom a.toMul) = 1 from
        (valZ_eq_one_iff _).2 this]
      rfl

include hG hcompat in
/-- **`h(Fˣ) = h(𝒪ˣ) · #G`.**  The valuation sequence `0 → 𝒪ˣ → Fˣ → ℤ → 0` and
multiplicativity of the Herbrand quotient. -/
theorem herbrand_units_eq_mul {σ : G} (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g)
    (hπ : ∃ π : F, (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ))
    [Finite (CyclicTate.TateH0 G (Additive (integers (F := F))ˣ) σ)]
    [Finite (CyclicTate.TateH1 G (Additive (integers (F := F))ˣ) σ)] :
    CyclicTate.herbrand G (Additive Fˣ) σ
      = CyclicTate.herbrand G (Additive (integers (F := F))ˣ) σ * (Nat.card G : ℚ) := by
  haveI := PermLattice.finite_tateH0_of_finite (G := G) (Ω := Unit) (σ := σ) hgen
  haveI := PermLattice.finite_tateH1_of_finite (G := G) (Ω := Unit) (σ := σ) hgen
  rw [(isShortExact_valHom hG hcompat hπ).herbrand_eq_mul' σ]
  congr 1
  rw [PermLattice.herbrand_eq hgen ()]
  congr 1
  rw [show MulAction.stabilizer G (() : Unit) = ⊤ by
    ext g; simp [MulAction.mem_stabilizer_iff], Subgroup.card_top]

end ShortExact

end LocalCFT

/-! ## The local field of a number field at an unramified place -/

namespace NumberField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum LocalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal] [IsGalois K L]

attribute [local instance] decompositionIntegersMulSemiringAction
  IsLocalRing.residueMulSemiringAction Units.mulDistribMulActionRight

variable [Fintype (decompositionGroup K L w)] {σ : decompositionGroup K L w}

/-- `Ĥ⁰(D_w, O_wˣ) = 0` at an unramified place, as a `Subsingleton` statement. -/
theorem subsingleton_tateH0_units (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) :
    Subsingleton (CyclicTate.TateH0 (decompositionGroup K L w)
      (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ) := by
  rw [CyclicTate.tateH0_subsingleton_iff]
  intro x hx
  obtain ⟨y, hy⟩ := exists_mulNorm_eq_of_smul_eq_adicCompletionIntegers v w h hσ hx
  exact ⟨Additive.ofMul y, by rw [LocalCFT.normHom_additive]; exact congrArg Additive.ofMul hy⟩

/-- `Ĥ¹(D_w, O_wˣ) = 0` at an unramified place, as a `Subsingleton` statement. -/
theorem subsingleton_tateH1_units (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) :
    Subsingleton (CyclicTate.TateH1 (decompositionGroup K L w)
      (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ) := by
  rw [CyclicTate.tateH1_subsingleton_iff]
  intro x hx
  rw [LocalCFT.normHom_additive] at hx
  obtain ⟨y, hy⟩ := exists_smul_div_of_mulNorm_eq_one_adicCompletionIntegers v w h hσ
    (x := x.toMul) (by simpa using hx)
  exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩

/-- **The Herbrand quotient of the local units at an unramified place:**
`h(D_w, L_w^×) = #D_w = [L_w : K_v]`.  This is the local class field theory input to the second
fundamental inequality, at the unramified places. -/
theorem herbrand_adicCompletion_units_eq_card
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hσ : ∀ d : decompositionGroup K L w, d ∈ Subgroup.zpowers σ) :
    CyclicTate.herbrand (decompositionGroup K L w) (Additive (w.adicCompletion L)ˣ) σ
      = (Nat.card (decompositionGroup K L w) : ℚ) := by
  haveI := subsingleton_tateH0_units v w h hσ
  haveI := subsingleton_tateH1_units v w h hσ
  have hgen : ∀ d : decompositionGroup K L w, ∃ k : ℕ, σ ^ k = d := by
    intro d
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff d σ).1
      (mem_powers_iff_mem_zpowers.2 (hσ d))
    exact ⟨k, hk⟩
  have hπ : ∃ π : w.adicCompletion L, (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ) :=
    valuedAdicCompletion_surjective (K := L) w (exp (-1 : ℤ))
  rw [LocalCFT.herbrand_units_eq_mul (F := w.adicCompletion L)
      (G := decompositionGroup K L w) (valued_decomposition_smul w)
      (fun d a ↦ rfl) hgen hπ,
    herbrand_adicCompletionIntegers_units_eq_one v w h hσ, one_mul]

end NumberField
