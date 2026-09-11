/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.ArchimedeanHerbrand
public import Iwasawalib.NumberTheory.CFT.InfiniteLocalGalois
public import Iwasawalib.NumberTheory.CFT.TateTransport
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# The local norm index at an archimedean place
-/

noncomputable section

open Complex NumberField NumberField.InfinitePlace
open scoped NumberField.LiesOver


namespace LocalCFT

section Transport

variable {G : Type*} [Group G] {σ : G}

attribute [local instance] Units.mulDistribMulActionRight

/-- **A continuous nontrivial involution of `ℂ` is complex conjugation.**  Let a two-element
group `G = {1, σ}` act faithfully by ring automorphisms on a topological field `F`, let
`e : F ≃+* ℂ` be a ring isomorphism which is a homeomorphism, and suppose `σ` acts
continuously.  Then `e` carries `σ` to complex conjugation.

This is the continuity route to `LocalCFT.eq_conj_of_ringEquiv_complex_of_faithful`.  It does
*not* need to know which elements of `F` are "real": the induced ring endomorphism
`e ∘ σ ∘ e⁻¹` of `ℂ` is continuous, hence is the identity or conjugation by
`Complex.ringHom_eq_id_or_conj_of_continuous`, and faithfulness rules out the identity. -/
theorem eq_conj_of_ringEquiv_complex_of_continuous {F : Type*} [Field F] [TopologicalSpace F]
    [MulSemiringAction G F] (h1 : σ ≠ 1)
    (hG : Function.Injective fun (g : G) ↦ (fun x : F ↦ g • x))
    (e : F ≃+* ℂ) (he : Continuous e) (hes : Continuous e.symm)
    (hcont : Continuous fun x : F ↦ σ • x) (z : F) :
    e (σ • z) = (starRingEnd ℂ) (e z) := by
  set τ : ℂ →+* ℂ :=
    (e : F →+* ℂ).comp ((MulSemiringAction.toRingHom G F σ).comp (e.symm : ℂ →+* F)) with hτ
  have hτapp : ∀ x : ℂ, τ x = e (σ • e.symm x) := fun _ ↦ rfl
  have hτcont : Continuous τ := he.comp (hcont.comp hes)
  rcases Complex.ringHom_eq_id_or_conj_of_continuous hτcont with h | h
  · exfalso
    refine h1 (hG (funext fun x ↦ ?_))
    have hx : τ (e x) = e x := by rw [h]; rfl
    rw [hτapp, e.symm_apply_apply] at hx
    show σ • x = (1 : G) • x
    rw [one_smul]
    exact e.injective hx
  · have hx : τ (e z) = (starRingEnd ℂ) (e z) := by rw [h]
    rw [hτapp, e.symm_apply_apply] at hx
    exact hx

/-- **`h(G, Fˣ) = 2` for a topological field isomorphic to `ℂ`.**  A two-element group acting
faithfully and continuously on a topological field `F`, together with a ring isomorphism
`e : F ≃+* ℂ` that is a homeomorphism, has `h(G, Fˣ) = 2`.

This is the form the archimedean local Herbrand quotient takes at an infinite place: no
compatibility between `ringEquivComplexOfIsComplex` and `ringEquivRealOfIsReal` is needed,
because the continuity of the `K_v`-automorphisms of `L_w`
(`NumberField.InfinitePlace.continuous_algEquiv`) already pins the action down. -/
theorem herbrand_units_eq_two_of_ringEquiv_complex_of_continuous {F : Type*} [Fintype G]
    [Field F] [TopologicalSpace F] [MulSemiringAction G F] (h1 : σ ≠ 1)
    (hσ : ∀ g : G, g = 1 ∨ g = σ)
    (hG : Function.Injective fun (g : G) ↦ (fun x : F ↦ g • x))
    (e : F ≃+* ℂ) (he : Continuous e) (hes : Continuous e.symm)
    (hcont : Continuous fun x : F ↦ σ • x) :
    CyclicTate.herbrand G (Additive Fˣ) σ = 2 :=
  herbrand_units_eq_two_of_ringEquiv_complex h1 hσ e
    (eq_conj_of_ringEquiv_complex_of_continuous h1 hG e he hes hcont)

end Transport

end LocalCFT

namespace NumberField.InfinitePlace

section Action

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (w : InfinitePlace L)

/-- **The decomposition group at an infinite place acts on `L_w` by ring automorphisms.**
The element `d` acts by `Completion.congr d`, which is `NumberField.InfinitePlace.toLocalGal`
forgetting the `K_v`-algebra structure; the definition does not mention the place `v` below
`w`, so it can be a genuine instance. -/
def stabilizerRingAut :
    MulAction.stabilizer (L ≃ₐ[K] L) w →* (w.Completion ≃+* w.Completion) :=
  MonoidHom.mk'
    (fun d ↦ Completion.congr ((d : L ≃ₐ[K] L) : L ≃+* L) w w
      ((mem_stabilizer_iff_apply_eq w).1 d.2))
    (fun a b ↦ RingEquiv.ext fun x ↦
      (Completion.congr_trans ((b : L ≃ₐ[K] L) : L ≃+* L) ((a : L ≃ₐ[K] L) : L ≃+* L)
        w w w ((mem_stabilizer_iff_apply_eq w).1 b.2) ((mem_stabilizer_iff_apply_eq w).1 a.2)
        ((mem_stabilizer_iff_apply_eq w).1 (a * b).2) x).symm)

@[simp] theorem stabilizerRingAut_apply (d : MulAction.stabilizer (L ≃ₐ[K] L) w)
    (x : w.Completion) :
    stabilizerRingAut w d x
      = Completion.congr ((d : L ≃ₐ[K] L) : L ≃+* L) w w
          ((mem_stabilizer_iff_apply_eq w).1 d.2) x := rfl

/-- The action of the decomposition group of an infinite place `w` on the completion `L_w`. -/
@[instance_reducible] def stabilizerCompletionMulSemiringAction :
    MulSemiringAction (MulAction.stabilizer (L ≃ₐ[K] L) w) w.Completion :=
  MulSemiringAction.compHom _ (stabilizerRingAut w)

attribute [local instance] stabilizerCompletionMulSemiringAction

theorem stabilizer_smul_def (d : MulAction.stabilizer (L ≃ₐ[K] L) w) (x : w.Completion) :
    d • x = Completion.congr ((d : L ≃ₐ[K] L) : L ≃+* L) w w
      ((mem_stabilizer_iff_apply_eq w).1 d.2) x := rfl

@[simp] theorem stabilizer_smul_algebraMap (d : MulAction.stabilizer (L ≃ₐ[K] L) w) (y : L) :
    d • algebraMap L w.Completion y = algebraMap L w.Completion ((d : L ≃ₐ[K] L) y) :=
  Completion.congr_algebraMap ((d : L ≃ₐ[K] L) : L ≃+* L) w w
    ((mem_stabilizer_iff_apply_eq w).1 d.2) y

/-- **The decomposition group of an infinite place acts faithfully on `L_w`.** -/
theorem stabilizer_smul_injective :
    Function.Injective fun (d : MulAction.stabilizer (L ≃ₐ[K] L) w) ↦
      (fun x : w.Completion ↦ d • x) := by
  intro a b hab
  refine Subtype.ext (AlgEquiv.ext fun y ↦ (algebraMap L w.Completion).injective ?_)
  have h := congrFun hab (algebraMap L w.Completion y)
  show algebraMap L w.Completion ((a : L ≃ₐ[K] L) y)
      = algebraMap L w.Completion ((b : L ≃ₐ[K] L) y)
  rw [← stabilizer_smul_algebraMap w a y, ← stabilizer_smul_algebraMap w b y]
  exact h

/-- The action of the decomposition group on `L_w` is by continuous maps. -/
theorem continuous_stabilizer_smul (d : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    Continuous fun x : w.Completion ↦ d • x :=
  Completion.continuous_congr ((d : L ≃ₐ[K] L) : L ≃+* L) w w
    ((mem_stabilizer_iff_apply_eq w).1 d.2)

end Action

section Card

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]

/-- **`#D_w = [L_w : K_v]` at an infinite place.** -/
theorem card_stabilizer_eq_finrank_completion :
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) = Module.finrank v.Completion w.Completion :=
  (Nat.card_congr (stabilizerEquivLocalGal v w).toEquiv).trans
    (IsGalois.card_aut_eq_finrank v.Completion w.Completion)

include v in
/-- **`#D_w = 2` at an infinite place of `L` ramified over `K`**, i.e. a complex place lying
over a real one. -/
theorem card_stabilizer_eq_two_of_isRamified (h : w.IsRamified K) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) = 2 :=
  (card_stabilizer_eq_finrank_completion v w).trans (h.finrank_eq_two v)

include v in
/-- **`#D_w = 1` at an infinite place of `L` unramified over `K`.** -/
theorem card_stabilizer_eq_one_of_isUnramified (h : w.IsUnramified K) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) = 1 :=
  (card_stabilizer_eq_finrank_completion v w).trans (h.finrank_eq_one v)

variable {v w}

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- A real place of `K` that becomes complex in `L` is ramified. -/
theorem isRamified_of_isReal_of_isComplex (hv : v.IsReal) (hw : w.IsComplex) :
    w.IsRamified K :=
  isRamified_iff.2 ⟨hw, by rwa [LiesOver.comap_eq w v]⟩

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- A place of `L` that is real is unramified over `K`. -/
theorem isUnramified_of_isReal (hw : w.IsReal) : w.IsUnramified K :=
  (w.isUnramified_or_isRamified K).resolve_right fun h ↦
    (not_isReal_iff_isComplex.2 h.isComplex) hw

end Card

section Herbrand

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]

attribute [local instance] stabilizerCompletionMulSemiringAction Units.mulDistribMulActionRight

omit [NumberField K] [IsGalois K L] [w.LiesOver v] in
/-- The identification `L_w ≃+* ℂ` at a complex place is an isometry. -/
theorem isometry_ringEquivComplexOfIsComplex (hw : w.IsComplex) :
    Isometry (Completion.ringEquivComplexOfIsComplex hw) :=
  Completion.isometry_extensionEmbedding w

omit [NumberField K] [IsGalois K L] [w.LiesOver v] in
/-- Its inverse is an isometry too, so `L_w ≃+* ℂ` is a homeomorphism. -/
theorem isometry_ringEquivComplexOfIsComplex_symm (hw : w.IsComplex) :
    Isometry (Completion.ringEquivComplexOfIsComplex hw).symm := by
  refine Isometry.of_dist_eq fun a b ↦ ?_
  rw [← (isometry_ringEquivComplexOfIsComplex w hw).dist_eq,
    RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/-! ### The ramified case: a real place of `K` that is complex in `L` -/

variable {v w}

/-- **`h(D_w, L_wˣ) = 2` at a real place of `K` that becomes complex in `L`.**

This is the archimedean local Herbrand quotient in the form the global identity
`h(C_L) = [L : K]` consumes it: `D_w` is the decomposition group of `w` in `Gal(L/K)`, acting
on `L_wˣ`, and its order is `2 = [L_w : K_v]`.  The proof identifies `L_w` with `ℂ` by
`NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex` and the nontrivial element
of `D_w` with complex conjugation — the latter because the action is faithful and continuous
(`NumberField.InfinitePlace.continuous_stabilizer_smul`), so that
`Complex.ringHom_eq_id_or_conj_of_continuous` applies. -/
theorem herbrand_completion_units_eq_two_of_isReal_of_isComplex
    [Fintype (MulAction.stabilizer (L ≃ₐ[K] L) w)] (hv : v.IsReal) (hw : w.IsComplex)
    {σ : MulAction.stabilizer (L ≃ₐ[K] L) w} (h1 : σ ≠ 1) :
    CyclicTate.herbrand (MulAction.stabilizer (L ≃ₐ[K] L) w)
      (Additive (w.Completion)ˣ) σ = 2 := by
  have hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) = 2 :=
    card_stabilizer_eq_two_of_isRamified v w (isRamified_of_isReal_of_isComplex hv hw)
  obtain ⟨τ, -, hτu⟩ :=
    (Nat.card_eq_two_iff' (1 : MulAction.stabilizer (L ≃ₐ[K] L) w)).1 hcard
  have hσ : ∀ g : MulAction.stabilizer (L ≃ₐ[K] L) w, g = 1 ∨ g = σ := by
    intro g
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr ((hτu g hg).trans (hτu σ h1).symm)
  exact LocalCFT.herbrand_units_eq_two_of_ringEquiv_complex_of_continuous h1 hσ
    (stabilizer_smul_injective w) (Completion.ringEquivComplexOfIsComplex hw)
    (isometry_ringEquivComplexOfIsComplex w hw).continuous
    (isometry_ringEquivComplexOfIsComplex_symm w hw).continuous
    (continuous_stabilizer_smul w σ)

/-! ### The unramified case: a place that stays real -/

include v in
/-- **`h(D_w, L_wˣ) = 1` at an infinite place unramified in `L`**, because the decomposition
group is trivial. -/
theorem herbrand_completion_units_eq_one_of_isUnramified
    [Fintype (MulAction.stabilizer (L ≃ₐ[K] L) w)] (h : w.IsUnramified K)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    CyclicTate.herbrand (MulAction.stabilizer (L ≃ₐ[K] L) w)
      (Additive (w.Completion)ˣ) σ = 1 := by
  haveI : Subsingleton (MulAction.stabilizer (L ≃ₐ[K] L) w) :=
    (Nat.card_eq_one_iff_unique.1 (card_stabilizer_eq_one_of_isUnramified v w h)).1
  exact CyclicTate.herbrand_eq_one_of_subsingleton_group

/-- **`h(D_w, L_wˣ) = 1` at a real place of `K` that stays real in `L`.** -/
theorem herbrand_completion_units_eq_one_of_isReal
    [Fintype (MulAction.stabilizer (L ≃ₐ[K] L) w)] (hv : v.IsReal) (hw : w.IsReal)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    CyclicTate.herbrand (MulAction.stabilizer (L ≃ₐ[K] L) w)
      (Additive (w.Completion)ˣ) σ = 1 :=
  herbrand_completion_units_eq_one_of_isUnramified (v := v) (isUnramified_of_isReal hw) σ

/-! ### The archimedean local norm index -/

omit [NumberField K] [IsGalois K L] [w.LiesOver v] in
/-- **`Ĥ¹(D_w, L_wˣ) = 0` at every infinite place**: Hilbert 90 for the faithful action of the
decomposition group on `L_w`.  No hypothesis on the ramification. -/
theorem subsingleton_tateH1_completion_units
    [Fintype (MulAction.stabilizer (L ≃ₐ[K] L) w)]
    {σ : MulAction.stabilizer (L ≃ₐ[K] L) w}
    (hσ : ∀ g : MulAction.stabilizer (L ≃ₐ[K] L) w, g ∈ Subgroup.zpowers σ) :
    Subsingleton (CyclicTate.TateH1 (MulAction.stabilizer (L ≃ₐ[K] L) w)
      (Additive (w.Completion)ˣ) σ) :=
  LocalCFT.subsingleton_tateH1_units_of_faithful hσ (stabilizer_smul_injective w)

omit [NumberField K] [IsGalois K L] [w.LiesOver v] in
/-- `#Ĥ¹(D_w, L_wˣ) = 1` at every infinite place. -/
theorem card_tateH1_completion_units
    [Fintype (MulAction.stabilizer (L ≃ₐ[K] L) w)]
    {σ : MulAction.stabilizer (L ≃ₐ[K] L) w}
    (hσ : ∀ g : MulAction.stabilizer (L ≃ₐ[K] L) w, g ∈ Subgroup.zpowers σ) :
    Nat.card (CyclicTate.TateH1 (MulAction.stabilizer (L ≃ₐ[K] L) w)
      (Additive (w.Completion)ˣ) σ) = 1 :=
  LocalCFT.card_tateH1_units_of_faithful hσ (stabilizer_smul_injective w)

/-- **The archimedean local norm index at a ramified place**:
`#(K_vˣ / N L_wˣ) = #Ĥ⁰(D_w, L_wˣ) = 2 = [L_w : K_v]` when `v` is real and `w` is complex. -/
theorem card_tateH0_completion_units_eq_two_of_isReal_of_isComplex
    [Fintype (MulAction.stabilizer (L ≃ₐ[K] L) w)] (hv : v.IsReal) (hw : w.IsComplex)
    {σ : MulAction.stabilizer (L ≃ₐ[K] L) w} (h1 : σ ≠ 1)
    (hσ : ∀ g : MulAction.stabilizer (L ≃ₐ[K] L) w, g ∈ Subgroup.zpowers σ) :
    Nat.card (CyclicTate.TateH0 (MulAction.stabilizer (L ≃ₐ[K] L) w)
      (Additive (w.Completion)ˣ) σ) = 2 :=
  LocalCFT.card_tateH0_units_of_faithful_of_herbrand hσ (stabilizer_smul_injective w)
    (n := 2) (by
      rw [herbrand_completion_units_eq_two_of_isReal_of_isComplex (v := v) hv hw h1]
      norm_num)

include v in
/-- **The archimedean local norm index at an unramified place**: `#Ĥ⁰(D_w, L_wˣ) = 1`, i.e.
every element of `K_vˣ` is a local norm. -/
theorem card_tateH0_completion_units_eq_one_of_isUnramified
    [Fintype (MulAction.stabilizer (L ≃ₐ[K] L) w)] (h : w.IsUnramified K)
    {σ : MulAction.stabilizer (L ≃ₐ[K] L) w}
    (hσ : ∀ g : MulAction.stabilizer (L ≃ₐ[K] L) w, g ∈ Subgroup.zpowers σ) :
    Nat.card (CyclicTate.TateH0 (MulAction.stabilizer (L ≃ₐ[K] L) w)
      (Additive (w.Completion)ˣ) σ) = 1 :=
  LocalCFT.card_tateH0_units_of_faithful_of_herbrand hσ (stabilizer_smul_injective w)
    (n := 1) (by
      rw [herbrand_completion_units_eq_one_of_isUnramified (v := v) h]
      norm_num)

end Herbrand

end NumberField.InfinitePlace
