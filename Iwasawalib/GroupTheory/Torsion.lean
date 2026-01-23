/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Int.Basic

@[expose] public section

/-!

# Complementary results to `p`-primary subgroups

-/

variable (G : Type*)

/-- TODO: go to mathlib -/
@[to_additive]
theorem CommMonoid.mem_primaryComponent [CommMonoid G] (p : ℕ) [Fact p.Prime] (g : G) :
    g ∈ CommMonoid.primaryComponent G p ↔ ∃ n, orderOf g = p ^ n := Iff.rfl

/-- TODO: go to mathlib -/
@[to_additive]
theorem CommGroup.mem_primaryComponent [CommGroup G] (p : ℕ) [Fact p.Prime] (g : G) :
    g ∈ CommGroup.primaryComponent G p ↔ ∃ n, orderOf g = p ^ n := Iff.rfl

/-- The prime-to-`n` component is the submonoid of elements with order prime to `n`. -/
@[to_additive (attr := simps)
      /-- The prime-to-`n` component is the submonoid of elements with additive
      order prime to `n`. -/]
def CommMonoid.primeToComponent [CommMonoid G] (n : ℕ) : Submonoid G where
  carrier := { g | (orderOf g).Coprime n }
  one_mem' := by simp
  mul_mem' {x} {y} hx hy := by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
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
theorem CommMonoid.mem_primeToComponent [CommMonoid G] (n : ℕ) (g : G) :
    g ∈ CommMonoid.primeToComponent G n ↔ (orderOf g).Coprime n := Iff.rfl

@[to_additive]
theorem CommGroup.mem_primeToComponent [CommGroup G] (n : ℕ) (g : G) :
    g ∈ CommGroup.primeToComponent G n ↔ (orderOf g).Coprime n := Iff.rfl

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
  rw [mem_primeToComponent, show orderOf g.1 = _ from
    orderOf_injective (Subgroup.subtype _) Subtype.val_injective g, hg, hp.coprime_iff_not_dvd] at h
  contradiction

/-- TODO: go to mathlib -/
@[to_additive]
theorem orderOf_zpow_dvd {G} [Group G] {x : G} (n : ℤ) : orderOf (x ^ n) ∣ orderOf x := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simpa using orderOf_pow_dvd n

/-- TODO: go to mathlib -/
@[to_additive]
theorem orderOf_zpow_eq_orderOf_pow_natAbs {G} [Group G] {x : G} (n : ℤ) :
    orderOf (x ^ n) = orderOf (x ^ n.natAbs) := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simp

/-- A torsion abelian group is canonically isomorphic to the product of its prime-to-`p` component
and its `p`-primary component. -/
@[to_additive (attr := simps symm_apply) AddCommGroup.equivPrimeToComponentProdPrimaryComponent
      /-- A torsion additive abelian group is canonically isomorphic to the product of its
      prime-to-`p` component and its `p`-primary component. -/]
noncomputable def CommGroup.equivPrimeToComponentProdPrimaryComponent
    [CommGroup G] (p : ℕ) [Fact p.Prime] (ht : Monoid.IsTorsion G) :
    G ≃* CommGroup.primeToComponent G p × CommGroup.primaryComponent G p :=
  letI toFun (g : G) : CommGroup.primeToComponent G p × CommGroup.primaryComponent G p := by
    letI n : ℕ := orderOf g
    letI r : ℕ := p ^ n.factorization p
    letI s : ℕ := n / r
    letI u : ℤ := r.gcdA s
    letI v : ℤ := r.gcdB s
    refine (⟨g ^ (r * u), ?_⟩, ⟨g ^ (s * v), ?_⟩)
    · rw [mem_primeToComponent]
      suffices (orderOf (g ^ r)).Coprime p by
        rw [zpow_mul, zpow_natCast]
        exact this.coprime_dvd_left (orderOf_zpow_dvd _)
      rw [Nat.coprime_comm, show orderOf (g ^ r) = s from orderOf_pow_of_dvd
        (by simp [r, ‹Fact p.Prime›.out.ne_zero]) (Nat.ordProj_dvd ..)]
      exact Nat.coprime_ordCompl Fact.out (orderOf_ne_zero_iff.2 (ht g))
    · use n.factorization p
      have h1 : orderOf (g ^ s) = r :=
        orderOf_pow_orderOf_div (orderOf_ne_zero_iff.2 (ht g)) (Nat.ordProj_dvd ..)
      have h2 : (orderOf (g ^ s)).Coprime v.natAbs := by
        rw [h1]
        have h := r.gcd_eq_gcd_ab s
        rw [eq_comm, mul_comm, show r.gcd s = 1 from
          (Nat.coprime_ordCompl Fact.out (orderOf_ne_zero_iff.2 (ht g))).pow_left _] at h
        replace h : IsCoprime (r : ℤ) v := ⟨_, _, h⟩
        rwa [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast] at h
      rwa [zpow_mul, zpow_natCast, orderOf_zpow_eq_orderOf_pow_natAbs, h2.orderOf_pow]
  letI invFun (g : CommGroup.primeToComponent G p × CommGroup.primaryComponent G p) :=
    g.1.1 * g.2.1
  haveI left_inv : Function.LeftInverse invFun toFun := fun g ↦ by
    simp only [toFun, invFun, ← zpow_add, ← Nat.gcd_eq_gcd_ab]
    set n : ℕ := orderOf g
    set r : ℕ := p ^ n.factorization p
    set s : ℕ := n / r
    simp [show r.gcd s = 1 from
      (Nat.coprime_ordCompl Fact.out (orderOf_ne_zero_iff.2 (ht g))).pow_left _]
  haveI map_mul_1 (x) (y) : invFun (x * y) = invFun x * invFun y := by
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, invFun, mul_assoc]
    congr 1
    simp_rw [← mul_assoc]
    congr 1
    rw [mul_comm]
  haveI hinj : Function.Injective invFun := by
    let invFun' : CommGroup.primeToComponent G p × CommGroup.primaryComponent G p →* G := {
      toFun := invFun
      map_one' := by simp [invFun]
      map_mul' := map_mul_1
    }
    refine (injective_iff_map_eq_one invFun').2 fun g hg ↦ ?_
    dsimp [invFun', invFun] at hg
    rw [← eq_inv_iff_mul_eq_one] at hg
    have h1 := g.1.2
    obtain ⟨n, h2⟩ := g.2.2
    rw [mem_primeToComponent, hg, orderOf_inv, h2] at h1
    rcases eq_or_ne n 0 with rfl | hn
    · rw [pow_zero, orderOf_eq_one_iff] at h2
      ext : 2 <;> simp [hg, h2]
    rw [Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hn), Nat.coprime_self] at h1
    exact False.elim (‹Fact p.Prime›.out.ne_one h1)
  haveI right_inv := left_inv.rightInverse_of_injective hinj
  haveI map_mul' (x) (y) : toFun (x * y) = toFun x * toFun y := by
    apply_fun _ using hinj
    simp [map_mul_1, left_inv.eq]
  { toFun := toFun, invFun := invFun,
    map_mul' := map_mul', left_inv := left_inv, right_inv := right_inv }

theorem CommGroup.card_primaryComponent [CommGroup G] [Finite G] (p : ℕ) [Fact p.Prime] :
    Nat.card (primaryComponent G p) = p ^ (Nat.card G).factorization p := by
  obtain ⟨n, hn⟩ := (CommGroup.primaryComponent.isPGroup (G := G) (p := p)).exists_card_eq
  rw [hn, eq_comm]
  congr 1
  have h1 := Nat.card_congr
    (equivPrimeToComponentProdPrimaryComponent G p isTorsion_of_finite).toEquiv
  rw [Nat.card_prod, hn] at h1
  have h2 := CommGroup.card_primeToComponent_coprime G p
  rw [Nat.coprime_comm, ‹Fact p.Prime›.out.coprime_iff_not_dvd] at h2
  apply_fun (Nat.factorization · p) at h1
  rw [Nat.factorization_mul Nat.card_pos.ne' (by simp [‹Fact p.Prime›.out.ne_zero])] at h1
  simpa [‹Fact p.Prime›.out.factorization_self, Nat.factorization_eq_zero_of_not_dvd h2] using h1

theorem CommGroup.card_primeToComponent [CommGroup G] [Finite G] (p : ℕ) [Fact p.Prime] :
    Nat.card (primeToComponent G p) = Nat.card G / p ^ (Nat.card G).factorization p := by
  have h1 := Nat.card_congr
    (equivPrimeToComponentProdPrimaryComponent G p isTorsion_of_finite).toEquiv
  rw [Nat.card_prod, card_primaryComponent] at h1
  rw [Nat.div_eq_of_eq_mul_left (by simp [‹Fact p.Prime›.out.pos]) h1]
