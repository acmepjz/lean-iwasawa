/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination

/-!

# Weierstrass preparation theorem for power series over a complete local ring

Consider using results in <https://github.com/leanprover-community/mathlib4/pull/21944> instead.

-/

open scoped Polynomial PowerSeries

/-- A typeclass asserting that a ring is a complete local ring, that is, it is a local ring,
and is adic complete with respect to the maximal ideal. By `isLocalRing_of_isAdicComplete_maximal`,
if a ring is adic complete with respect to some maximal ideal, then such ring has only one
maximal ideal, and hence such ring is a complete local ring. -/
class abbrev IsCompleteLocalRing (A : Type*) [CommRing A] : Prop :=
  IsLocalRing A, IsAdicComplete (IsLocalRing.maximalIdeal A) A

/-!

## Weierstrass division

-/

/-- A `Prop` which asserts that a power series `q` and a polynomial `r` of degree `< n` satisfy
`f = g * q + r`, where `n` is the order of the image of `g` in the residue field (defined to be
zero if such image is zero, in which case it's mathematically not considered). -/
def PowerSeries.IsWeierstrassDivision
    {A : Type*} [CommRing A] [IsLocalRing A]
    (f g q : A⟦X⟧) (r : A[X]) : Prop :=
  r.degree < (g.map (IsLocalRing.residue A)).order.toNat ∧ f = g * q + r

theorem PowerSeries.isWeierstrassDivision_zero
    {A : Type*} [CommRing A] [IsLocalRing A]
    (g : A⟦X⟧) : IsWeierstrassDivision 0 g 0 0 := by
  constructor
  · nontriviality A
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · simp

-- TODO: maybe `IsPrecomplete` is already enough?

/-- **Weierstrass division**: let `f`, `g` be power series over a complete local ring, such that
the image of `g` in the residue field is not zero. Let `n` be the order of the image of `g` in the
residue field. Then there exists a power series `q` and a polynomial `r` of degree `< n`, such that
`f = g * q + r`. -/
theorem PowerSeries.exists_isWeierstrassDivision
    {A : Type*} [CommRing A] [IsCompleteLocalRing A]
    (f g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    ∃ q r, f.IsWeierstrassDivision g q r := by
  sorry

-- Unfortunately there is no Unicode subscript `w`.

/-- The `q` in Werierstrass division, denoted by `f /ʷ g`. Note that when the image of `g` in the
residue field is zero, this is defined to be zero. -/
noncomputable def PowerSeries.weierstrassDiv
    {A : Type*} [CommRing A] [IsCompleteLocalRing A] (f g : A⟦X⟧) : A⟦X⟧ :=
  open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) ≠ 0 then
    (f.exists_isWeierstrassDivision g hg).choose
  else
    0

/-- The `r` in Werierstrass division, denoted by `f %ʷ g`. Note that when the image of `g` in the
residue field is zero, this is defined to be zero. -/
noncomputable def PowerSeries.weierstrassMod
    {A : Type*} [CommRing A] [IsCompleteLocalRing A] (f g : A⟦X⟧) : A[X] :=
  open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) ≠ 0 then
    (f.exists_isWeierstrassDivision g hg).choose_spec.choose
  else
    0

@[inherit_doc]
infixl:70 " /ʷ " => PowerSeries.weierstrassDiv

@[inherit_doc]
infixl:70 " %ʷ " => PowerSeries.weierstrassMod

@[simp]
theorem PowerSeries.weierstrassDiv_zero_right
    {A : Type*} [CommRing A] [IsCompleteLocalRing A] (f : A⟦X⟧) : f /ʷ 0 = 0 := by
  rw [weierstrassDiv, dif_neg (by simp)]

@[simp]
theorem PowerSeries.weierstrassMod_zero_right
    {A : Type*} [CommRing A] [IsCompleteLocalRing A] (f : A⟦X⟧) : f %ʷ 0 = 0 := by
  rw [weierstrassMod, dif_neg (by simp)]

theorem PowerSeries.degree_weierstrassMod_lt
    {A : Type*} [CommRing A] [IsCompleteLocalRing A] (f g : A⟦X⟧) :
    (f %ʷ g).degree < (g.map (IsLocalRing.residue A)).order.toNat := by
  rw [weierstrassMod]
  split_ifs with hg
  · exact (f.exists_isWeierstrassDivision g hg).choose_spec.choose_spec.1
  · nontriviality A
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _

theorem PowerSeries.isWeierstrassDivision_weierstrassDiv_weierstrassMod
    {A : Type*} [CommRing A] [IsCompleteLocalRing A]
    (f g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    f.IsWeierstrassDivision g (f /ʷ g) (f %ʷ g) := by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact (f.exists_isWeierstrassDivision g hg).choose_spec.choose_spec

theorem PowerSeries.eq_mul_weierstrassDiv_add_weierstrassMod
    {A : Type*} [CommRing A] [IsCompleteLocalRing A]
    (f g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    f = g * (f /ʷ g) + (f %ʷ g) := by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact (f.exists_isWeierstrassDivision g hg).choose_spec.choose_spec.2

/-- The `q` and `r` in the Weierstrass division for `0` is equal to `0`. -/
theorem PowerSeries.eq_zero_of_weierstrass_division
    {A : Type*} [CommRing A] [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0)
    {q : A⟦X⟧} {r : A[X]}
    (hr : r.degree < (g.map (IsLocalRing.residue A)).order.toNat)
    (heq : g * q = r) : q = 0 ∧ r = 0 := by
  sorry

/-- The `q` and `r` in the Weierstrass division is unique. -/
theorem PowerSeries.eq_of_weierstrass_division
    {A : Type*} [CommRing A] [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0)
    {q q' : A⟦X⟧} {r r' : A[X]}
    (hr : r.degree < (g.map (IsLocalRing.residue A)).order.toNat)
    (hr' : r'.degree < (g.map (IsLocalRing.residue A)).order.toNat)
    (heq : g * q + r = g * q' + r') : q = q' ∧ r = r' := by
  replace heq : g * (q - q') = ↑(r' - r) := by
    rw [Polynomial.coe_sub]
    linear_combination heq
  have h := g.eq_zero_of_weierstrass_division hg
    (lt_of_le_of_lt (r'.degree_sub_le r) (max_lt hr' hr)) heq
  simp_rw [sub_eq_zero] at h
  exact ⟨h.1, h.2.symm⟩

/-- The `q` and `r` in the Weierstrass division is unique. -/
theorem PowerSeries.IsWeierstrassDivision.elim
    {A : Type*} [CommRing A] [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {f g : A⟦X⟧} (hg : g.map (IsLocalRing.residue A) ≠ 0)
    {q q' : A⟦X⟧} {r r' : A[X]}
    (H1 : f.IsWeierstrassDivision g q r)
    (H2 : f.IsWeierstrassDivision g q' r') : q = q' ∧ r = r' :=
  g.eq_of_weierstrass_division hg H1.1 H2.1 (H1.2.symm.trans H2.2)

/-- The `q` and `r` in the Weierstrass division for `0` is equal to `0`. -/
theorem PowerSeries.IsWeierstrassDivision.eq_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {g : A⟦X⟧} (hg : g.map (IsLocalRing.residue A) ≠ 0)
    {q : A⟦X⟧} {r : A[X]}
    (H : IsWeierstrassDivision 0 g q r) : q = 0 ∧ r = 0 :=
  H.elim hg g.isWeierstrassDivision_zero

/-- The `q` and `r` in the Weierstrass division is equal to `f /ʷ g` and `f %ʷ g`. -/
theorem PowerSeries.IsWeierstrassDivision.eq_weierstrassDiv_weierstrassMod
    {A : Type*} [CommRing A] [IsCompleteLocalRing A]
    {f g : A⟦X⟧} (hg : g.map (IsLocalRing.residue A) ≠ 0)
    {q : A⟦X⟧} {r : A[X]}
    (H : f.IsWeierstrassDivision g q r) : q = f /ʷ g ∧ r = f %ʷ g :=
  H.elim hg (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod g hg)

@[simp]
theorem PowerSeries.weierstrassDiv_zero_left
    {A : Type*} [CommRing A] [IsCompleteLocalRing A] (g : A⟦X⟧) : 0 /ʷ g = 0 := by
  by_cases hg : g.map (IsLocalRing.residue A) ≠ 0
  · exact ((isWeierstrassDivision_weierstrassDiv_weierstrassMod 0 g hg).eq_zero hg).1
  rw [weierstrassDiv, dif_neg hg]

@[simp]
theorem PowerSeries.weierstrassMod_zero_left
    {A : Type*} [CommRing A] [IsCompleteLocalRing A] (g : A⟦X⟧) : 0 %ʷ g = 0 := by
  by_cases hg : g.map (IsLocalRing.residue A) ≠ 0
  · exact ((isWeierstrassDivision_weierstrassDiv_weierstrassMod 0 g hg).eq_zero hg).2
  rw [weierstrassMod, dif_neg hg]

/-!

## Weierstrass preparation theorem

-/

/-- A `Prop` which asserts that `f` is a distingushed polynomial,
`h` is a power series which is a unit, such that `g = f * h`. -/
@[mk_iff]
structure PowerSeries.IsWeierstrassFactorization
    {A : Type*} [CommRing A] [IsLocalRing A]
    (g : A⟦X⟧) (f : A[X]) (h : A⟦X⟧) : Prop where
  isDistinguishedAt : f.IsDistinguishedAt (IsLocalRing.maximalIdeal A)
  isUnit : IsUnit h
  eq_mul : g = f * h

theorem PowerSeries.IsWeierstrassFactorization.map_ne_zero
    {A : Type*} [CommRing A] [IsLocalRing A]
    {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧}
    (H : g.IsWeierstrassFactorization f h) :
    g.map (IsLocalRing.residue A) ≠ 0 := by
  rw [congr(map (IsLocalRing.residue A) $(H.eq_mul)), map_mul, mul_ne_zero_iff,
    ← Polynomial.polynomial_map_coe, ne_eq, Polynomial.coe_eq_zero_iff]
  exact ⟨f.map_monic_ne_zero H.isDistinguishedAt.monic, (H.isUnit.map _).ne_zero⟩

theorem PowerSeries.IsWeierstrassFactorization.degree_eq_order_map
    {A : Type*} [CommRing A] [IsLocalRing A]
    {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧}
    (H : g.IsWeierstrassFactorization f h) :
    f.degree = (g.map (IsLocalRing.residue A)).order := by
  refine IsDistinguishedAt.degree_eq_order_map g h f H.isDistinguishedAt ?_ H.eq_mul
  rw [IsLocalRing.not_mem_maximalIdeal, ← PowerSeries.isUnit_iff_constantCoeff]
  exact H.isUnit

/-- **Weierstrass preparation theorem**: let `g` be a power series over a complete local ring,
such that the image of `g` in the residue field is not zero. Then there exists a distinguished
polynomial `f` and a power series `h` which is a unit, such that `g = f * h`. -/
theorem PowerSeries.exists_isWeierstrassFactorization
    {A : Type*} [CommRing A] [IsCompleteLocalRing A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    ∃ f h, g.IsWeierstrassFactorization f h := by
  sorry

/-- The `f` in Werierstrass preparation theorem. -/
noncomputable def PowerSeries.weierstrassDistinguished
    {A : Type*} [CommRing A] [IsCompleteLocalRing A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) : A[X] :=
  (g.exists_isWeierstrassFactorization hg).choose

/-- The `h` in Werierstrass preparation theorem. -/
noncomputable def PowerSeries.weierstrassUnit
    {A : Type*} [CommRing A] [IsCompleteLocalRing A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) : A⟦X⟧ :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose

theorem PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    {A : Type*} [CommRing A] [IsCompleteLocalRing A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    g.IsWeierstrassFactorization (g.weierstrassDistinguished hg) (g.weierstrassUnit hg) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec

theorem PowerSeries.isDistinguishedAt_weierstrassDistinguished
    {A : Type*} [CommRing A] [IsCompleteLocalRing A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    (g.weierstrassDistinguished hg).IsDistinguishedAt (IsLocalRing.maximalIdeal A) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isDistinguishedAt

theorem PowerSeries.isUnit_weierstrassUnit
    {A : Type*} [CommRing A] [IsCompleteLocalRing A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    IsUnit (g.weierstrassUnit hg) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isUnit

theorem PowerSeries.eq_weierstrassDistinguished_mul_weierstrassUnit
    {A : Type*} [CommRing A] [IsCompleteLocalRing A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    g = g.weierstrassDistinguished hg * g.weierstrassUnit hg :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.eq_mul

/-- The `f` and `h` in Werierstrass preparation theorem is unique. -/
theorem PowerSeries.IsWeierstrassFactorization.elim
    {A : Type*} [CommRing A] [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {g : A⟦X⟧} {f f' : A[X]} {h h' : A⟦X⟧}
    (H1 : g.IsWeierstrassFactorization f h)
    (H2 : g.IsWeierstrassFactorization f' h') : f = f' ∧ h = h' := by
  sorry
