/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.Data.Nat.PrimaryComponent
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Int.Basic

@[expose] public section

/-!

# Complementary results to `p`-primary subgroups

-/

/-! ### Prime-to-`n` component of a group -/

variable (G : Type*)

/-- The prime-to-`n` component is the submonoid of elements with order prime to `n`. -/
@[to_additive (attr := simps)
      /-- The prime-to-`n` component is the submonoid of elements with additive
      order prime to `n`. -/]
def CommMonoid.primeToComponent [CommMonoid G] (n : ℕ) : Submonoid G where
  carrier := { g | (orderOf g).Coprime n }
  one_mem' := by simp
  mul_mem' {x} {y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    exact (hx.mul_left hy).coprime_dvd_left (Commute.all x y).orderOf_mul_dvd_mul_orderOf

/-- The prime-to-`n` component is the subgroup of elements with order prime to `n`. -/
@[to_additive (attr := simps!)
      /-- The prime-to-`n` component is the subgroup of elements with additive order
      prime to `n`. -/]
def CommGroup.primeToComponent [CommGroup G] (n : ℕ) : Subgroup G where
  toSubmonoid := CommMonoid.primeToComponent G n
  inv_mem' h := by
    change (orderOf _).Coprime n at h ⊢
    rwa [orderOf_inv]

@[to_additive]
theorem CommMonoid.mem_primeToComponent_iff_orderOf [CommMonoid G] (n : ℕ) (g : G) :
    g ∈ CommMonoid.primeToComponent G n ↔ (orderOf g).Coprime n := Iff.rfl

@[to_additive]
theorem CommGroup.mem_primeToComponent_iff_orderOf [CommGroup G] (n : ℕ) (g : G) :
    g ∈ CommGroup.primeToComponent G n ↔ (orderOf g).Coprime n := Iff.rfl

@[to_additive (attr := simp)]
theorem CommMonoid.primeToComponent_zero [CommMonoid G] : CommMonoid.primeToComponent G 0 = ⊥ := by
  ext1
  simp [mem_primeToComponent_iff_orderOf]

@[to_additive (attr := simp)]
theorem CommGroup.primeToComponent_zero [CommGroup G] : CommGroup.primeToComponent G 0 = ⊥ := by
  ext1
  simp [mem_primeToComponent_iff_orderOf]

-- TODO: go mathlib ???
@[to_additive (attr := simp)]
theorem CommMonoid.primaryComponent_zero [CommMonoid G] : CommMonoid.primaryComponent G 0 = ⊤ := by
  ext1
  simp only [mem_primaryComponent, Submonoid.mem_top, iff_true]
  use 1
  simp

-- TODO: go mathlib ???
@[to_additive (attr := simp)]
theorem CommGroup.primaryComponent_zero [CommGroup G] : CommGroup.primaryComponent G 0 = ⊤ := by
  ext1
  simp only [mem_primaryComponent, Subgroup.mem_top, iff_true]
  use 1
  simp

@[to_additive]
theorem CommGroup.card_primeToComponent_coprime [CommGroup G] [Finite G] (n : ℕ) :
    (Nat.card (primeToComponent G n)).Coprime n := by
  rw [Nat.Coprime]
  by_contra! H
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd H
  have := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p (hdvd.trans (Nat.gcd_dvd_left ..))
  replace hdvd := hdvd.trans (Nat.gcd_dvd_right ..)
  have h := g.2
  rw [mem_primeToComponent_iff_orderOf, show orderOf g.1 = _ from
    orderOf_injective (Subgroup.subtype _) Subtype.val_injective g, hg, hp.coprime_iff_not_dvd] at h
  contradiction

@[to_additive]
theorem CommGroup.primeFactors_card_primaryComponent_subset [CommGroup G] [Finite G]
    {n : ℕ} (hn : n ≠ 0) :
    (Nat.card (primaryComponent G n)).primeFactors ⊆ n.primeFactors := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  have := Fact.mk hp.1
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hp.2.1
  obtain ⟨k, hk⟩ := mem_primaryComponent.1 g.2
  norm_cast at hk
  rw [← orderOf_dvd_iff_pow_eq_one, hg] at hk
  exact hp.1.mem_primeFactors (hp.1.dvd_of_dvd_pow hk) hn

/-- TODO: go to mathlib -/
@[to_additive]
theorem orderOf_zpow_dvd {G} [Group G] {x : G} (n : ℤ) : orderOf (x ^ n) ∣ orderOf x := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simpa using orderOf_pow_dvd n

/-- TODO: go to mathlib -/
@[to_additive]
theorem orderOf_zpow_eq_orderOf_pow_natAbs {G} [Group G] {x : G} (n : ℤ) :
    orderOf (x ^ n) = orderOf (x ^ n.natAbs) := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simp

/-! ### A group is isomorphic to the product of its prime-to-`m` part and `m`-primary part -/

/-- A torsion abelian group is canonically isomorphic to the product of its prime-to-`m` component
and its `m`-primary component. -/
@[to_additive (attr := simps symm_apply) AddCommGroup.equivPrimeToComponentProdPrimaryComponent
      /-- A torsion additive abelian group is canonically isomorphic to the product of its
      prime-to-`m` component and its `m`-primary component. -/]
noncomputable def CommGroup.equivPrimeToComponentProdPrimaryComponent
    [CommGroup G] (m : ℕ) (ht : Monoid.IsTorsion G) :
    G ≃* CommGroup.primeToComponent G m × CommGroup.primaryComponent G m :=
  letI toFun (g : G) : CommGroup.primeToComponent G m × CommGroup.primaryComponent G m := by
    letI n : ℕ := orderOf g
    letI r : ℕ := n.primaryComponent m
    letI s : ℕ := n.primeToComponent m
    letI u : ℤ := r.gcdA s
    letI v : ℤ := r.gcdB s
    refine (⟨g ^ (r * u), ?_⟩, ⟨g ^ (s * v), ?_⟩)
    · rw [mem_primeToComponent_iff_orderOf]
      suffices (orderOf (g ^ r)).Coprime m by
        rw [zpow_mul, zpow_natCast]
        exact this.coprime_dvd_left (orderOf_zpow_dvd _)
      rw [Nat.coprime_comm, show orderOf (g ^ r) = s from orderOf_pow_of_dvd
        (Nat.primaryComponent_pos n m).ne' (Nat.primaryComponent_dvd_self n m)]
      exact (Nat.coprime_primeToComponent_right m (orderOf_ne_zero_iff.2 (ht g))).symm
    · rw [mem_primaryComponent]
      use n
      rw [← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one]
      suffices n ∣ s * m ^ n by
        zify at this
        convert Int.dvd_mul_of_dvd_left this (c := v) using 1
        push_cast
        ring
      have h1 : r ∣ m ^ n := gcd_dvd_right n (m ^ n)
      have h2 : n = s * r := (Nat.primeToComponent_mul_primaryComponent n m).symm
      nth_rw 1 [h2]
      exact Nat.mul_dvd_mul_left _ h1
  letI invFun (g : CommGroup.primeToComponent G m × CommGroup.primaryComponent G m) :=
    g.1.1 * g.2.1
  haveI left_inv : Function.LeftInverse invFun toFun := fun g ↦ by
    simp only [toFun, invFun, ← zpow_add, ← Nat.gcd_eq_gcd_ab]
    set n : ℕ := orderOf g
    simp [(n.coprime_primeToComponent_primaryComponent m).symm.gcd_eq_one]
  haveI map_mul_1 (x) (y) : invFun (x * y) = invFun x * invFun y := by
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, invFun, mul_assoc]
    congr 1
    simp_rw [← mul_assoc]
    congr 1
    rw [mul_comm]
  haveI hinj : Function.Injective invFun := by
    let invFun' : CommGroup.primeToComponent G m × CommGroup.primaryComponent G m →* G := {
      toFun := invFun
      map_one' := by simp [invFun]
      map_mul' := map_mul_1
    }
    refine (injective_iff_map_eq_one invFun').2 fun g hg ↦ ?_
    dsimp [invFun', invFun] at hg
    rw [← eq_inv_iff_mul_eq_one] at hg
    suffices g.2.1 = 1 by
      ext : 2
      · simp [hg, this]
      · simp [this]
    have h1 := g.1.2
    obtain ⟨n, h2⟩ := mem_primaryComponent.1 g.2.2
    rw [← orderOf_dvd_iff_pow_eq_one] at h2
    rw [mem_primeToComponent_iff_orderOf, hg, orderOf_inv] at h1
    simpa only [Nat.gcd_eq_left h2, orderOf_eq_one_iff] using (h1.pow_right n).gcd_eq_one
  haveI right_inv := left_inv.rightInverse_of_injective hinj
  haveI map_mul' (x) (y) : toFun (x * y) = toFun x * toFun y := by
    apply_fun _ using hinj
    simp [map_mul_1, left_inv.eq]
  { toFun := toFun, invFun := invFun,
    map_mul' := map_mul', left_inv := left_inv, right_inv := right_inv }

@[to_additive]
theorem CommGroup.card_primeToComponent_mul_card_primaryComponent
    [CommGroup G] (m : ℕ) (ht : Monoid.IsTorsion G) :
    Nat.card (primeToComponent G m) * Nat.card (primaryComponent G m) = Nat.card G := by
  simpa only [Nat.card_prod] using Nat.card_congr
    (equivPrimeToComponentProdPrimaryComponent G m ht).toEquiv.symm

@[to_additive]
theorem CommGroup.card_primeToComponent [CommGroup G] [Finite G] (m : ℕ) :
    Nat.card (primeToComponent G m) = (Nat.card G).primeToComponent m := by
  have h1 : Nat.card G ≠ 0 := Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  have h2 : Nat.card (primaryComponent G m) ≠ 0 :=
    Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [Nat.primeToComponent_zero_right h1]
  refine (Nat.dvd_primeToComponent_iff m h1).2
    ⟨Subgroup.card_subgroup_dvd_card _, card_primeToComponent_coprime G m⟩ |>.antisymm ?_
  rw [Nat.primeToComponent, Nat.eq_div_of_mul_eq_left h2
    (card_primeToComponent_mul_card_primaryComponent G m isTorsion_of_finite)]
  exact Nat.div_dvd_div_left (Nat.primaryComponent_dvd_self ..) <|
    (Nat.dvd_primaryComponent_iff h1 hm).2
      ⟨Subgroup.card_subgroup_dvd_card _, primeFactors_card_primaryComponent_subset G hm⟩

@[to_additive]
theorem CommGroup.card_primaryComponent [CommGroup G] [Finite G] (m : ℕ) :
    Nat.card (primaryComponent G m) = (Nat.card G).primaryComponent m := by
  have h1 : Nat.card G ≠ 0 := Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  have h2 : Nat.card (primeToComponent G m) ≠ 0 :=
    Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  rw [Nat.eq_div_of_mul_eq_right h2
    (card_primeToComponent_mul_card_primaryComponent G m isTorsion_of_finite),
    card_primeToComponent, Nat.primaryComponent_eq_div _ h1]
