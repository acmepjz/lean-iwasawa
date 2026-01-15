/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.GroupTheory.Torsion

@[expose] public section

/-!

# Complementary results to `p`-primary subgroups

-/

variable (G : Type*)

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

/-- A torsion abelian group is canonically isomorphic to the product of its prime-to-`p` component
and its `p`-primary component. -/
noncomputable def CommGroup.equivPrimeToComponentProdPrimaryComponent
    [CommGroup G] (p : ℕ) [Fact p.Prime] (ht : Monoid.IsTorsion G) :
    G ≃* CommGroup.primeToComponent G p × CommGroup.primaryComponent G p where
  toFun g := by
    letI n : ℕ := orderOf g
    letI r : ℕ := p ^ n.factorization p
    letI s : ℕ := n / r
    letI u : ℤ := r.gcdA s
    letI v : ℤ := r.gcdB s
    refine (⟨g ^ (r * u), ?_⟩, ⟨g ^ (s * v), ?_⟩)
    · sorry
    · sorry
  invFun g := g.1.1 * g.2.1
  map_mul' x y := by
    sorry
  left_inv := by
    sorry
  right_inv := by
    sorry
