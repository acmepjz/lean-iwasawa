/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.ExactCount
public import Iwasawalib.GroupCohomology.TateHexagon

@[expose] public section

/-!
# The Herbrand quotient

For a finite cyclic group `G = ⟨σ⟩` and a `G`-module `M` whose two Tate cohomology groups are
finite, the *Herbrand quotient* is

`h(M) = #Ĥ⁰(G, M) / #Ĥ¹(G, M) ∈ ℚ`.

Its three basic properties are proved here:

* `CyclicTate.herbrand_eq_one_of_finite`: `h(M) = 1` for a finite module `M`;
* `CyclicTate.IsShortExact.herbrand_eq_mul`: `h(B) = h(A) · h(C)` for a short exact sequence
  `0 → A → B → C → 0`;
* `CyclicTate.herbrand_eq_of_finite_ker_coker`: `h(A) = h(B)` for an equivariant map
  `f : A → B` with finite kernel and finite cokernel.

Multiplicativity is the counting identity `Nat.card_alternating_of_exact` applied to the Tate
hexagon of `Iwasawalib/GroupCohomology/TateHexagon.lean`, and the last statement follows from
the first two applied to `0 → ker f → A → im f → 0` and `0 → im f → B → coker f → 0`.

Finiteness is never assumed where it can be deduced: `CyclicTate.finite_of_exact` propagates
finiteness around the hexagon, so a short exact sequence with two finite Herbrand quotients has
a third.
-/

noncomputable section

namespace CyclicTate

/-! ## Finiteness from exactness -/

/-- If `A₁ → A₂ → A₃` is exact at `A₂` and the two ends are finite, so is `A₂`. -/
theorem finite_of_exact {A₁ A₂ A₃ : Type*} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]
    (f₁ : A₁ →+ A₂) (f₂ : A₂ →+ A₃) (e₂ : f₂.ker = f₁.range) [Finite A₁] [Finite A₃] :
    Finite A₂ := by
  have h₁ : Finite f₂.ker := by
    rw [e₂]
    exact Finite.of_surjective _ f₁.rangeRestrict_surjective
  have h₂ : Finite (A₂ ⧸ f₂.ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange f₂).toEquiv.symm
  exact Finite.of_addSubgroup_quotient f₂.ker

/-! ## The definition -/

section Def

variable (G : Type*) [Group G] [Fintype G] (M : Type*) [AddCommGroup M] [DistribMulAction G M]

/-- The **Herbrand quotient** `h(M) = #Ĥ⁰(G, M) / #Ĥ¹(G, M)` of a `G`-module for a finite cyclic
group `G = ⟨σ⟩`.  It is meaningful only when the two Tate groups are finite; `Nat.card` returns
`0` on an infinite type, so `herbrand` is `0` or ill-behaved otherwise. -/
def herbrand (σ : G) : ℚ :=
  (Nat.card (TateH0 G M σ) : ℚ) / (Nat.card (TateH1 G M σ) : ℚ)

variable {G M}

theorem herbrand_def (σ : G) :
    herbrand G M σ = (Nat.card (TateH0 G M σ) : ℚ) / (Nat.card (TateH1 G M σ) : ℚ) := rfl

theorem card_tateH0_pos (σ : G) [Finite (TateH0 G M σ)] : 0 < Nat.card (TateH0 G M σ) :=
  Nat.card_pos_iff.2 ⟨⟨0⟩, ‹_›⟩

theorem card_tateH1_pos (σ : G) [Finite (TateH1 G M σ)] : 0 < Nat.card (TateH1 G M σ) :=
  Nat.card_pos_iff.2 ⟨⟨0⟩, ‹_›⟩

theorem herbrand_pos (σ : G) [Finite (TateH0 G M σ)] [Finite (TateH1 G M σ)] :
    0 < herbrand G M σ :=
  div_pos (by exact_mod_cast card_tateH0_pos (M := M) σ)
    (by exact_mod_cast card_tateH1_pos (M := M) σ)

theorem herbrand_eq_one_iff (σ : G) [Finite (TateH0 G M σ)] [Finite (TateH1 G M σ)] :
    herbrand G M σ = 1 ↔ Nat.card (TateH0 G M σ) = Nat.card (TateH1 G M σ) := by
  rw [herbrand_def, div_eq_one_iff_eq (by exact_mod_cast (card_tateH1_pos (M := M) σ).ne')]
  exact_mod_cast Iff.rfl

/-- A module with vanishing Tate cohomology has Herbrand quotient `1`. -/
theorem herbrand_eq_one_of_subsingleton (σ : G) [Subsingleton (TateH0 G M σ)]
    [Subsingleton (TateH1 G M σ)] : herbrand G M σ = 1 := by
  have h0 : Nat.card (TateH0 G M σ) = 1 := Nat.card_eq_one_iff_unique.2 ⟨‹_›, ⟨0⟩⟩
  have h1 : Nat.card (TateH1 G M σ) = 1 := Nat.card_eq_one_iff_unique.2 ⟨‹_›, ⟨0⟩⟩
  rw [herbrand_def, h0, h1]
  norm_num

end Def

/-! ## The Herbrand quotient of a finite module is `1` -/

section Finite

variable {G : Type*} [Group G] [Fintype G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

/-- `#M^σ = #Ĥ⁰ · #(N M)`. -/
theorem card_kerSub_eq (σ : G) :
    Nat.card (kerSub G M σ) = Nat.card (TateH0 G M σ) * Nat.card (rangeNorm G M) := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    ((rangeNorm G M).addSubgroupOf (kerSub G M σ))]
  exact congrArg _
    (Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (rangeNorm_le_kerSub σ)).toEquiv)

/-- `#(ker N) = #Ĥ¹ · #((σ - 1) M)`. -/
theorem card_kerNorm_eq (σ : G) :
    Nat.card (kerNorm G M) = Nat.card (TateH1 G M σ) * Nat.card (rangeSub G M σ) := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    ((rangeSub G M σ).addSubgroupOf (kerNorm G M))]
  exact congrArg _
    (Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (rangeSub_le_kerNorm σ)).toEquiv)

variable [Finite M]

/-- For a finite module the two Tate groups have the same order. -/
theorem card_tateH0_eq_card_tateH1 (σ : G) :
    Nat.card (TateH0 G M σ) = Nat.card (TateH1 G M σ) := by
  have hN : Nat.card M = Nat.card (rangeNorm G M) * Nat.card (kerNorm G M) :=
    (normHom G M).card_eq_card_range_mul_card_ker
  have hD : Nat.card M = Nat.card (rangeSub G M σ) * Nat.card (kerSub G M σ) :=
    (subHom (M := M) σ).card_eq_card_range_mul_card_ker
  rw [card_kerNorm_eq σ] at hN
  rw [card_kerSub_eq σ] at hD
  have hb : 0 < Nat.card (rangeNorm G M) := Nat.card_pos_iff.2 ⟨⟨0⟩, inferInstance⟩
  have hd : 0 < Nat.card (rangeSub G M σ) := Nat.card_pos_iff.2 ⟨⟨0⟩, inferInstance⟩
  have := hN.symm.trans hD
  -- `b * (h¹ * d) = d * (h⁰ * b)`
  have key : Nat.card (rangeNorm G M) * Nat.card (rangeSub G M σ) * Nat.card (TateH1 G M σ) =
      Nat.card (rangeNorm G M) * Nat.card (rangeSub G M σ) * Nat.card (TateH0 G M σ) := by
    calc Nat.card (rangeNorm G M) * Nat.card (rangeSub G M σ) * Nat.card (TateH1 G M σ)
        = Nat.card (rangeNorm G M) * (Nat.card (TateH1 G M σ) * Nat.card (rangeSub G M σ)) := by
          ring
      _ = Nat.card (rangeSub G M σ) * (Nat.card (TateH0 G M σ) * Nat.card (rangeNorm G M)) := this
      _ = Nat.card (rangeNorm G M) * Nat.card (rangeSub G M σ) * Nat.card (TateH0 G M σ) := by
          ring
  exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hb hd) key).symm

/-- **The Herbrand quotient of a finite module is `1`.** -/
theorem herbrand_eq_one_of_finite (σ : G) : herbrand G M σ = 1 := by
  have h : Nat.card (TateH1 G M σ) ≠ 0 := (Nat.card_pos_iff.2 ⟨⟨0⟩, inferInstance⟩).ne'
  rw [herbrand_def, card_tateH0_eq_card_tateH1 σ, div_self (by exact_mod_cast h)]

end Finite


/-! ## Multiplicativity in a short exact sequence -/

namespace IsShortExact

variable {G : Type*} [Group G] [Fintype G] {A B C : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
  {i : A →+[G] B} {p : B →+[G] C} (h : IsShortExact i p) (σ : G)

include h

/-! ### Finiteness propagates around the hexagon -/

theorem finite_tateH0_mid [Finite (TateH0 G A σ)] [Finite (TateH0 G C σ)] :
    Finite (TateH0 G B σ) :=
  finite_of_exact (tateH0Map i σ) (tateH0Map p σ) (h.ker_tateH0Map_p σ)

theorem finite_tateH1_mid [Finite (TateH1 G A σ)] [Finite (TateH1 G C σ)] :
    Finite (TateH1 G B σ) :=
  finite_of_exact (tateH1Map i σ) (tateH1Map p σ) (h.ker_tateH1Map_p σ)

theorem finite_tateH0_right [Finite (TateH0 G B σ)] [Finite (TateH1 G A σ)] :
    Finite (TateH0 G C σ) :=
  finite_of_exact (tateH0Map p σ) (h.delta0 σ) (h.ker_delta0 σ)

theorem finite_tateH1_right [Finite (TateH1 G B σ)] [Finite (TateH0 G A σ)] :
    Finite (TateH1 G C σ) :=
  finite_of_exact (tateH1Map p σ) (h.delta1 σ) (h.ker_delta1 σ)

theorem finite_tateH1_left [Finite (TateH0 G C σ)] [Finite (TateH1 G B σ)] :
    Finite (TateH1 G A σ) :=
  finite_of_exact (h.delta0 σ) (tateH1Map i σ) (h.ker_tateH1Map_i σ)

theorem finite_tateH0_left [Finite (TateH1 G C σ)] [Finite (TateH0 G B σ)] :
    Finite (TateH0 G A σ) :=
  finite_of_exact (h.delta1 σ) (tateH0Map i σ) (h.ker_tateH0Map_i σ)

/-! ### The counting identity -/

/-- **The Tate hexagon, counted.**  `#Ĥ⁰(A) · #Ĥ⁰(C) · #Ĥ¹(B) = #Ĥ⁰(B) · #Ĥ¹(A) · #Ĥ¹(C)`. -/
theorem card_tate_alternating :
    Nat.card (TateH0 G A σ) * Nat.card (TateH0 G C σ) * Nat.card (TateH1 G B σ) =
      Nat.card (TateH0 G B σ) * Nat.card (TateH1 G A σ) * Nat.card (TateH1 G C σ) :=
  Nat.card_alternating_of_exact (tateH0Map i σ) (tateH0Map p σ) (h.delta0 σ)
    (tateH1Map i σ) (tateH1Map p σ) (h.delta1 σ)
    (h.ker_tateH0Map_i σ) (h.ker_tateH0Map_p σ) (h.ker_delta0 σ)
    (h.ker_tateH1Map_i σ) (h.ker_tateH1Map_p σ) (h.ker_delta1 σ)

/-- **Multiplicativity of the Herbrand quotient.**  For a short exact sequence
`0 → A → B → C → 0` of `G`-modules with finite Tate cohomology, `h(B) = h(A) · h(C)`. -/
theorem herbrand_eq_mul [Finite (TateH0 G A σ)] [Finite (TateH1 G A σ)]
    [Finite (TateH0 G B σ)] [Finite (TateH1 G B σ)]
    [Finite (TateH0 G C σ)] [Finite (TateH1 G C σ)] :
    herbrand G B σ = herbrand G A σ * herbrand G C σ := by
  have hA1 : (Nat.card (TateH1 G A σ) : ℚ) ≠ 0 := by
    exact_mod_cast (card_tateH1_pos (M := A) σ).ne'
  have hB1 : (Nat.card (TateH1 G B σ) : ℚ) ≠ 0 := by
    exact_mod_cast (card_tateH1_pos (M := B) σ).ne'
  have hC1 : (Nat.card (TateH1 G C σ) : ℚ) ≠ 0 := by
    exact_mod_cast (card_tateH1_pos (M := C) σ).ne'
  have key : (Nat.card (TateH0 G A σ) : ℚ) * Nat.card (TateH0 G C σ) * Nat.card (TateH1 G B σ) =
      (Nat.card (TateH0 G B σ) : ℚ) * Nat.card (TateH1 G A σ) * Nat.card (TateH1 G C σ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) (h.card_tate_alternating σ)
  rw [herbrand_def, herbrand_def, herbrand_def, div_mul_div_comm, div_eq_div_iff hB1
    (mul_ne_zero hA1 hC1)]
  linear_combination -key

/-- The version of multiplicativity in which the finiteness of the Tate cohomology of the
middle term is *deduced* from that of the two ends. -/
theorem herbrand_eq_mul' [Finite (TateH0 G A σ)] [Finite (TateH1 G A σ)]
    [Finite (TateH0 G C σ)] [Finite (TateH1 G C σ)] :
    herbrand G B σ = herbrand G A σ * herbrand G C σ := by
  haveI := h.finite_tateH0_mid σ
  haveI := h.finite_tateH1_mid σ
  exact h.herbrand_eq_mul σ

end IsShortExact


/-! ## Stable subgroups, quotients, and the induced short exact sequence -/

section Stable

variable (G : Type*) [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

/-- A subgroup of a `G`-module which is stable under the action. -/
class IsStableSubgroup (N : AddSubgroup M) : Prop where
  /-- the subgroup is stable under the action -/
  smul_mem : ∀ (g : G) {x : M}, x ∈ N → g • x ∈ N

variable {G}

theorem smul_mem_of_isStableSubgroup {N : AddSubgroup M} [IsStableSubgroup G N] (g : G) {x : M}
    (hx : x ∈ N) : g • x ∈ N := IsStableSubgroup.smul_mem g hx

variable (G)

/-- The action of `G` on a stable subgroup. -/
instance stableSubgroupDistribMulAction (N : AddSubgroup M) [IsStableSubgroup G N] :
    DistribMulAction G N where
  smul g x := ⟨g • (x : M), smul_mem_of_isStableSubgroup g x.2⟩
  one_smul x := Subtype.ext (one_smul G (x : M))
  mul_smul g g' x := Subtype.ext (mul_smul g g' (x : M))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g x y := Subtype.ext (smul_add g (x : M) (y : M))

variable {G}

@[simp] theorem coe_smul_stableSubgroup {N : AddSubgroup M} [IsStableSubgroup G N] (g : G)
    (x : N) : ((g • x : N) : M) = g • (x : M) := rfl

variable (G)

/-- The action of `G` on the quotient by a stable subgroup. -/
instance stableQuotientDistribMulAction (N : AddSubgroup M) [IsStableSubgroup G N] :
    DistribMulAction G (M ⧸ N) where
  smul g := QuotientAddGroup.map N N (DistribSMul.toAddMonoidHom M g)
    fun _ hx ↦ smul_mem_of_isStableSubgroup g hx
  one_smul x := by
    induction x using QuotientAddGroup.induction_on with | _ a =>
    exact congrArg QuotientAddGroup.mk (one_smul G a)
  mul_smul g g' x := by
    induction x using QuotientAddGroup.induction_on with | _ a =>
    exact congrArg QuotientAddGroup.mk (mul_smul g g' a)
  smul_zero g := congrArg QuotientAddGroup.mk (smul_zero g)
  smul_add g x y := by
    induction x using QuotientAddGroup.induction_on with | _ a =>
    induction y using QuotientAddGroup.induction_on with | _ b =>
    exact congrArg QuotientAddGroup.mk (smul_add g a b)

variable {G}

@[simp] theorem smul_mk_stableQuotient {N : AddSubgroup M} [IsStableSubgroup G N] (g : G)
    (a : M) : g • (QuotientAddGroup.mk a : M ⧸ N) = QuotientAddGroup.mk (g • a) := rfl

variable (G)

/-- The inclusion of a stable subgroup, as an equivariant map. -/
def stableSubgroupIncl (N : AddSubgroup M) [IsStableSubgroup G N] : N →+[G] M where
  toFun x := (x : M)
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The projection onto the quotient by a stable subgroup, as an equivariant map. -/
def stableQuotientMk (N : AddSubgroup M) [IsStableSubgroup G N] : M →+[G] M ⧸ N where
  toFun a := QuotientAddGroup.mk a
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `0 → N → M → M / N → 0` is short exact. -/
theorem isShortExact_stableQuotient (N : AddSubgroup M) [IsStableSubgroup G N] :
    IsShortExact (stableSubgroupIncl G N) (stableQuotientMk G N) where
  inj _ _ h := Subtype.ext h
  surj x := by
    induction x using QuotientAddGroup.induction_on with | _ a => exact ⟨a, rfl⟩
  exact b := by
    constructor
    · intro hb
      exact ⟨⟨b, (QuotientAddGroup.eq_zero_iff b).1 hb⟩, rfl⟩
    · rintro ⟨⟨a, ha⟩, rfl⟩
      exact (QuotientAddGroup.eq_zero_iff a).2 ha

end Stable

/-! ## Invariance under a map with finite kernel and cokernel -/

section Invariance

variable {G : Type*} [Group G] [Fintype G] {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  [DistribMulAction G A] [DistribMulAction G B] (f : A →+[G] B) (σ : G)

instance isStableSubgroup_ker : IsStableSubgroup G (f.toAddMonoidHom.ker) where
  smul_mem g {x} hx := by
    have hx' : f x = 0 := hx
    show f (g • x) = 0
    rw [map_smul, hx', smul_zero]

instance isStableSubgroup_range : IsStableSubgroup G (f.toAddMonoidHom.range) where
  smul_mem g {x} hx := by
    obtain ⟨a, rfl⟩ := hx
    exact ⟨g • a, map_smul f g a⟩

/-- The corestriction of `f` to its image, as an equivariant map. -/
def rangeRestrict : A →+[G] f.toAddMonoidHom.range where
  toFun a := ⟨f a, ⟨a, rfl⟩⟩
  map_smul' g a := Subtype.ext (map_smul f g a)
  map_zero' := Subtype.ext (map_zero f)
  map_add' a a' := Subtype.ext (map_add f a a')

omit [Fintype G] in
/-- `0 → ker f → A → im f → 0` is short exact. -/
theorem isShortExact_ker_range :
    IsShortExact (stableSubgroupIncl G (f.toAddMonoidHom.ker)) (rangeRestrict f) where
  inj _ _ h := Subtype.ext h
  surj := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  exact b := by
    constructor
    · intro hb
      exact ⟨⟨b, (congrArg Subtype.val hb : f b = 0)⟩, rfl⟩
    · rintro ⟨⟨a, ha⟩, rfl⟩
      exact Subtype.ext (show f a = 0 from ha)

/-- **The Herbrand quotient is invariant under an equivariant map with finite kernel and
finite cokernel.** -/
theorem herbrand_eq_of_finite_ker_coker [Finite (f.toAddMonoidHom.ker)]
    [Finite (B ⧸ f.toAddMonoidHom.range)]
    [Finite (TateH0 G A σ)] [Finite (TateH1 G A σ)] :
    herbrand G A σ = herbrand G B σ := by
  set N := f.toAddMonoidHom.ker
  set R := f.toAddMonoidHom.range
  have h₁ := isShortExact_ker_range f
  have h₂ := isShortExact_stableQuotient G R
  -- the Tate groups of the image are finite
  haveI : Finite (TateH0 G R σ) := h₁.finite_tateH0_right σ
  haveI : Finite (TateH1 G R σ) := h₁.finite_tateH1_right σ
  -- the Tate groups of `B` are finite
  haveI : Finite (TateH0 G B σ) := h₂.finite_tateH0_mid σ
  haveI : Finite (TateH1 G B σ) := h₂.finite_tateH1_mid σ
  have e₁ : herbrand G A σ = herbrand G N σ * herbrand G R σ := h₁.herbrand_eq_mul σ
  have e₂ : herbrand G B σ = herbrand G R σ * herbrand G (B ⧸ R) σ := h₂.herbrand_eq_mul σ
  rw [e₁, e₂, herbrand_eq_one_of_finite (M := N) σ, herbrand_eq_one_of_finite (M := B ⧸ R) σ,
    one_mul, mul_one]

end Invariance

end CyclicTate
