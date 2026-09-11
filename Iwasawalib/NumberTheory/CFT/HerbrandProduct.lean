/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.Herbrand

@[expose] public section

/-!
# Transport and products for the Herbrand quotient

Two elementary but indispensable manipulations of the explicit Tate cohomology groups of
`Iwasawalib/GroupCohomology/CyclicTate.lean`:

* an equivariant additive equivalence `A ≃+ B` induces isomorphisms `Ĥ⁰(A) ≅ Ĥ⁰(B)` and
  `Ĥ¹(A) ≅ Ĥ¹(B)`, hence `h(A) = h(B)`;
* Tate cohomology commutes with arbitrary products: `Ĥ⁰(∏ i, M i) ≅ ∏ i, Ĥ⁰(M i)` and the
  same for `Ĥ¹`, hence `h(∏ i, M i) = ∏ i, h(M i)` over a finite index type.

The product statement needs no induction: the norm map and the map `x ↦ σ • x - x` are both
computed componentwise on a product, so their kernels and ranges are the products of the
componentwise kernels and ranges (the axiom of choice being used to split a family of
preimages).

## Main results

* `CyclicTate.tateH0Equiv`, `CyclicTate.tateH1Equiv`, `CyclicTate.herbrand_eq_of_addEquiv`
* `CyclicTate.tateH0PiEquiv`, `CyclicTate.tateH1PiEquiv`, `CyclicTate.herbrand_pi`
-/

noncomputable section

namespace CyclicTate

/-! ## Transport along an equivariant additive equivalence -/

section Transport

variable {G : Type*} [Group G] [Fintype G] {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  [DistribMulAction G A] [DistribMulAction G B] (e : A ≃+ B)
  (he : ∀ (g : G) (a : A), e (g • a) = g • e a)

include he

/-- An equivariant additive equivalence, read as an equivariant map. -/
def ofAddEquiv : A →+[G] B where
  toFun := e
  map_smul' := he
  map_zero' := map_zero e
  map_add' := map_add e

omit [Fintype G] in
@[simp] theorem ofAddEquiv_apply (a : A) : ofAddEquiv e he (a : A) = e a := rfl

omit [Fintype G] in
theorem symm_equivariant (g : G) (b : B) : e.symm (g • b) = g • e.symm b := by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

variable (σ : G)

/-- `Ĥ⁰` transported along an equivariant additive equivalence. -/
def tateH0Equiv : TateH0 G A σ ≃+ TateH0 G B σ where
  toFun := tateH0Map (ofAddEquiv e he) σ
  invFun := tateH0Map (ofAddEquiv e.symm (symm_equivariant e he)) σ
  left_inv t := by
    obtain ⟨x, hx, rfl⟩ := TateH0.mk_surjective t
    simp only [tateH0Map_mk, ofAddEquiv_apply]
    congr 1
    exact e.symm_apply_apply x
  right_inv t := by
    obtain ⟨x, hx, rfl⟩ := TateH0.mk_surjective t
    simp only [tateH0Map_mk, ofAddEquiv_apply]
    congr 1
    exact e.apply_symm_apply x
  map_add' _ _ := map_add _ _ _

/-- `Ĥ¹` transported along an equivariant additive equivalence. -/
def tateH1Equiv : TateH1 G A σ ≃+ TateH1 G B σ where
  toFun := tateH1Map (ofAddEquiv e he) σ
  invFun := tateH1Map (ofAddEquiv e.symm (symm_equivariant e he)) σ
  left_inv t := by
    obtain ⟨x, hx, rfl⟩ := TateH1.mk_surjective t
    simp only [tateH1Map_mk, ofAddEquiv_apply]
    congr 1
    exact e.symm_apply_apply x
  right_inv t := by
    obtain ⟨x, hx, rfl⟩ := TateH1.mk_surjective t
    simp only [tateH1Map_mk, ofAddEquiv_apply]
    congr 1
    exact e.apply_symm_apply x
  map_add' _ _ := map_add _ _ _

theorem finite_tateH0_of_addEquiv [Finite (TateH0 G A σ)] : Finite (TateH0 G B σ) :=
  Finite.of_equiv _ (tateH0Equiv e he σ).toEquiv

theorem finite_tateH1_of_addEquiv [Finite (TateH1 G A σ)] : Finite (TateH1 G B σ) :=
  Finite.of_equiv _ (tateH1Equiv e he σ).toEquiv

/-- **The Herbrand quotient is invariant under an equivariant additive equivalence.** -/
theorem herbrand_eq_of_addEquiv : herbrand G A σ = herbrand G B σ := by
  rw [herbrand_def, herbrand_def, Nat.card_congr (tateH0Equiv e he σ).toEquiv,
    Nat.card_congr (tateH1Equiv e he σ).toEquiv]

end Transport

/-! ## Tate cohomology of a product -/

section Pi

variable {G : Type*} [Group G] [Fintype G] {ι : Type*} {M : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, DistribMulAction G (M i)]

theorem normHom_pi_apply (x : ∀ i, M i) (i : ι) :
    normHom G (∀ i, M i) x i = normHom G (M i) (x i) := by
  simp only [normHom_apply]
  exact Finset.sum_apply i _ _

omit [Fintype G] in
theorem subHom_pi_apply (σ : G) (x : ∀ i, M i) (i : ι) :
    subHom (M := ∀ i, M i) σ x i = subHom (M := M i) σ (x i) := rfl

variable (σ : G)

/-- The componentwise class map `(M i)_{i}^σ → ∏ i, Ĥ⁰(M i)`. -/
def piTateH0Hom : kerSub G (∀ i, M i) σ →+ (∀ i, TateH0 G (M i) σ) where
  toFun x i := TateH0.mk σ (x := (x : ∀ i, M i) i)
    (congrFun (mem_kerSub.1 x.2) i)
  map_zero' := funext fun _ ↦ rfl
  map_add' _ _ := funext fun _ ↦ rfl

@[simp] theorem piTateH0Hom_apply (x : kerSub G (∀ i, M i) σ) (i : ι) :
    piTateH0Hom σ x i = TateH0.mk σ (x := (x : ∀ i, M i) i) (congrFun (mem_kerSub.1 x.2) i) :=
  rfl

theorem piTateH0Hom_surjective : Function.Surjective (piTateH0Hom (M := M) σ) := by
  intro t
  choose x hx hxt using fun i ↦ TateH0.mk_surjective (t i)
  refine ⟨⟨x, mem_kerSub.2 (funext fun i ↦ hx i)⟩, funext fun i ↦ ?_⟩
  exact hxt i

theorem ker_piTateH0Hom :
    (piTateH0Hom (M := M) σ).ker = (rangeNorm G (∀ i, M i)).addSubgroupOf (kerSub G (∀ i, M i) σ) := by
  ext x
  simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, mem_rangeNorm]
  constructor
  · intro h
    have h' : ∀ i, ∃ y : M i, normHom G (M i) y = (x : ∀ i, M i) i := fun i ↦
      (TateH0.mk_eq_zero_iff (σ := σ) (congrFun (mem_kerSub.1 x.2) i)).1 (congrFun h i)
    choose y hy using h'
    exact ⟨y, funext fun i ↦ (normHom_pi_apply y i).trans (hy i)⟩
  · rintro ⟨y, hy⟩
    refine funext fun i ↦ (TateH0.mk_eq_zero_iff (σ := σ)
      (congrFun (mem_kerSub.1 x.2) i)).2 ⟨y i, ?_⟩
    rw [← normHom_pi_apply, hy]

/-- **`Ĥ⁰` commutes with products.** -/
def tateH0PiEquiv : TateH0 G (∀ i, M i) σ ≃+ (∀ i, TateH0 G (M i) σ) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_piTateH0Hom (M := M) σ).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (piTateH0Hom_surjective (M := M) σ))

/-- The componentwise class map `ker N → ∏ i, Ĥ¹(M i)`. -/
def piTateH1Hom : kerNorm G (∀ i, M i) →+ (∀ i, TateH1 G (M i) σ) where
  toFun x i := TateH1.mk σ (x := (x : ∀ i, M i) i)
    ((normHom_pi_apply _ i).symm.trans (congrFun (mem_kerNorm.1 x.2) i))
  map_zero' := funext fun _ ↦ rfl
  map_add' _ _ := funext fun _ ↦ rfl

theorem piTateH1Hom_surjective : Function.Surjective (piTateH1Hom (M := M) σ) := by
  intro t
  choose x hx hxt using fun i ↦ TateH1.mk_surjective (t i)
  refine ⟨⟨x, mem_kerNorm.2 (funext fun i ↦ (normHom_pi_apply x i).trans (hx i))⟩,
    funext fun i ↦ ?_⟩
  exact hxt i

theorem ker_piTateH1Hom :
    (piTateH1Hom (M := M) σ).ker
      = (rangeSub G (∀ i, M i) σ).addSubgroupOf (kerNorm G (∀ i, M i)) := by
  ext x
  simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, mem_rangeSub]
  constructor
  · intro h
    have h' : ∀ i, ∃ y : M i, σ • y - y = (x : ∀ i, M i) i := fun i ↦
      (TateH1.mk_eq_zero_iff (σ := σ)
        ((normHom_pi_apply (M := M) _ i).symm.trans (congrFun (mem_kerNorm.1 x.2) i))).1
        (congrFun h i)
    choose y hy using h'
    exact ⟨y, funext fun i ↦ hy i⟩
  · rintro ⟨y, hy⟩
    exact funext fun i ↦ (TateH1.mk_eq_zero_iff (σ := σ)
      ((normHom_pi_apply (M := M) _ i).symm.trans (congrFun (mem_kerNorm.1 x.2) i))).2
      ⟨y i, congrFun hy i⟩

/-- **`Ĥ¹` commutes with products.** -/
def tateH1PiEquiv : TateH1 G (∀ i, M i) σ ≃+ (∀ i, TateH1 G (M i) σ) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_piTateH1Hom (M := M) σ).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (piTateH1Hom_surjective (M := M) σ))

variable [Fintype ι]

instance finite_tateH0_pi [∀ i, Finite (TateH0 G (M i) σ)] : Finite (TateH0 G (∀ i, M i) σ) :=
  Finite.of_equiv _ (tateH0PiEquiv (M := M) σ).toEquiv.symm

instance finite_tateH1_pi [∀ i, Finite (TateH1 G (M i) σ)] : Finite (TateH1 G (∀ i, M i) σ) :=
  Finite.of_equiv _ (tateH1PiEquiv (M := M) σ).toEquiv.symm

theorem card_tateH0_pi :
    Nat.card (TateH0 G (∀ i, M i) σ) = ∏ i, Nat.card (TateH0 G (M i) σ) :=
  (Nat.card_congr (tateH0PiEquiv (M := M) σ).toEquiv).trans Nat.card_pi

theorem card_tateH1_pi :
    Nat.card (TateH1 G (∀ i, M i) σ) = ∏ i, Nat.card (TateH1 G (M i) σ) :=
  (Nat.card_congr (tateH1PiEquiv (M := M) σ).toEquiv).trans Nat.card_pi

/-- **The Herbrand quotient of a finite product is the product of the Herbrand quotients.** -/
theorem herbrand_pi [∀ i, Finite (TateH0 G (M i) σ)] [∀ i, Finite (TateH1 G (M i) σ)] :
    herbrand G (∀ i, M i) σ = ∏ i, herbrand G (M i) σ := by
  simp only [herbrand_def]
  rw [card_tateH0_pi, card_tateH1_pi, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]

end Pi

/-! ## The binary product -/

section Prod

variable {G : Type*} [Group G] [Fintype G] {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  [DistribMulAction G A] [DistribMulAction G B]

/-- The inclusion of the first factor of a product of `G`-modules. -/
def prodInl : A →+[G] A × B where
  toFun a := (a, 0)
  map_smul' g a := by
    show ((g • a : A), (0 : B)) = g • (a, (0 : B))
    rw [Prod.smul_mk, smul_zero]
  map_zero' := rfl
  map_add' a a' := by rw [Prod.mk_add_mk, add_zero]

/-- The projection onto the second factor of a product of `G`-modules. -/
def prodSnd : A × B →+[G] B where
  toFun := Prod.snd
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Fintype G] in
/-- `0 → A → A × B → B → 0` is short exact. -/
theorem isShortExact_prod : IsShortExact (prodInl : A →+[G] A × B) prodSnd where
  inj _ _ h := congrArg Prod.fst h
  surj b := ⟨(0, b), rfl⟩
  exact x := by
    constructor
    · intro h
      exact ⟨x.1, Prod.ext rfl (show (0 : B) = x.2 from ((show x.2 = 0 from h)).symm)⟩
    · rintro ⟨a, rfl⟩
      rfl

variable (σ : G)

/-- **The Herbrand quotient of a product of two modules.** -/
theorem herbrand_prod [Finite (TateH0 G A σ)] [Finite (TateH1 G A σ)]
    [Finite (TateH0 G B σ)] [Finite (TateH1 G B σ)] :
    herbrand G (A × B) σ = herbrand G A σ * herbrand G B σ :=
  (isShortExact_prod (A := A) (B := B) (G := G)).herbrand_eq_mul' σ

theorem finite_tateH0_prod [Finite (TateH0 G A σ)] [Finite (TateH0 G B σ)] :
    Finite (TateH0 G (A × B) σ) :=
  (isShortExact_prod (A := A) (B := B) (G := G)).finite_tateH0_mid σ

theorem finite_tateH1_prod [Finite (TateH1 G A σ)] [Finite (TateH1 G B σ)] :
    Finite (TateH1 G (A × B) σ) :=
  (isShortExact_prod (A := A) (B := B) (G := G)).finite_tateH1_mid σ

end Prod

end CyclicTate
