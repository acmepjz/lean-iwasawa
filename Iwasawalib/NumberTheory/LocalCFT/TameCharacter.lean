/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Ring.Aut

@[expose] public section

/-!
# The tame character, and `e ∣ q - 1` for an abelian extension

Let `B` be a discrete valuation ring with uniformizer `π`, residue field `k = B/𝔪`.  Every ring
automorphism `σ` of `B` sends `π` to another uniformizer, so there is a unique unit
`u_σ ∈ Bˣ` with `σ π = π · u_σ` (`LocalCFT.tameUnit`).  Reducing `u_σ` mod `𝔪` gives the **tame
character**

`θ(σ) = σ(π) / π  mod 𝔪  ∈  kˣ`   (`LocalCFT.tameChar`),

and this file proves the three classical facts about it, *unconditionally and with no class
field theory*:

* `LocalCFT.tameChar_mul`: `θ` is a homomorphism on the inertia group
  `LocalCFT.inertiaAut B = {σ | σ acts trivially on k}`.  (The cocycle identity
  `u_{στ} = u_σ · σ(u_τ)` holds for all `σ`; it becomes multiplicativity exactly when `σ` acts
  trivially on `k`.)
* `LocalCFT.tameChar_conj`: **Frobenius conjugation.**  If `τ` is any automorphism inducing
  `x ↦ x^q` on `k`, then `θ(τστ⁻¹) = θ(σ)^q` for `σ` in the inertia group.
* `LocalCFT.tameChar_pow_sub_one_eq_one`: hence if `τ` *commutes* with `σ` — which is what
  abelianness of the Galois group supplies — then `θ(σ)^{q-1} = 1`.

The payoff is `LocalCFT.orderOf_dvd_sub_one_of_tameChar_injective`:
in an abelian extension whose inertia injects under `θ`, the order of an inertia element
divides `q - 1`, i.e. `e ∣ q - 1` where `q = #k_v` is the residue cardinality of the base.

## What is a hypothesis here, and what is not

Nothing in this file uses local reciprocity, the Artin map, or any completion: the construction
of `θ` and both identities are elementary manipulations of the relation `σ π = π · u_σ` in a
discrete valuation ring.  The one input that is *not* supplied here is the **injectivity** of
`θ` on inertia, which is precisely tameness (`ker θ` is the first ramification group `G₁`, a
pro-`ℓ` group for `ℓ = char k`).  It appears as the explicit hypothesis `hinj` of
`LocalCFT.orderOf_dvd_sub_one_of_tameChar_injective` and is discharged, for automorphisms of
order invertible in `B`, in `Iwasawalib/NumberTheory/LocalCFT/TameInjective.lean`.

Note that the standard textbook form of the character, `σ ↦ σ(π^{1/e})/π^{1/e} ∈ μ_e`, is not
needed: on the inertia group of a *tamely* ramified extension the two agree, and `σ(π)/π`
avoids adjoining an `e`-th root.

## Main definitions

* `LocalCFT.tameUnit`: the unit `u_σ` with `σ π = π · u_σ`.
* `LocalCFT.tameChar`: its residue `θ(σ) ∈ k`, a unit of `k`.
* `LocalCFT.inertiaAut`: the subgroup of `RingAut B` acting trivially on the residue field.

## Main statements

* `LocalCFT.tameUnit_mul`: the cocycle identity `u_{στ} = u_σ · σ(u_τ)`.
* `LocalCFT.tameChar_mul`: `θ` is multiplicative along the inertia group.
* `LocalCFT.tameChar_conj`: `θ(τστ⁻¹) = θ(σ)^q`.
* `LocalCFT.tameChar_pow_sub_one_eq_one`: `θ(σ)^{q-1} = 1` when `τ` and `σ` commute.
* `LocalCFT.orderOf_dvd_sub_one_of_tameChar_injective`: `orderOf σ ∣ q - 1`.
-/

noncomputable section

open IsLocalRing

namespace LocalCFT



variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

def tameUnit {π : B} (hπ : Irreducible π) (σ : RingAut B) : Bˣ :=
  (IsDiscreteValuationRing.associated_of_irreducible (R := B) hπ (hπ.map σ)).choose

theorem mul_tameUnit {π : B} (hπ : Irreducible π) (σ : RingAut B) :
    π * (tameUnit hπ σ : B) = σ π :=
  (IsDiscreteValuationRing.associated_of_irreducible (R := B) hπ (hπ.map σ)).choose_spec

theorem tameUnit_unique {π : B} (hπ : Irreducible π) (σ : RingAut B) {u : Bˣ}
    (hu : π * (u : B) = σ π) : u = tameUnit hπ σ :=
  Units.ext (mul_left_cancel₀ hπ.ne_zero (hu.trans (mul_tameUnit hπ σ).symm))

theorem tameUnit_one {π : B} (hπ : Irreducible π) : tameUnit hπ 1 = 1 :=
  (tameUnit_unique hπ 1 (by simp)).symm

theorem tameUnit_mul {π : B} (hπ : Irreducible π) (σ τ : RingAut B) :
    tameUnit hπ (σ * τ) = tameUnit hπ σ * Units.map (σ : B →+* B).toMonoidHom (tameUnit hπ τ) := by
  refine (tameUnit_unique hπ (σ * τ) ?_).symm
  show π * ((tameUnit hπ σ : B) * σ (tameUnit hπ τ : B)) = σ (τ π)
  rw [← mul_assoc, mul_tameUnit hπ σ, ← map_mul, mul_tameUnit hπ τ]

theorem coe_tameUnit_mul {π : B} (hπ : Irreducible π) (σ τ : RingAut B) :
    ((tameUnit hπ (σ * τ) : B)) = (tameUnit hπ σ : B) * σ (tameUnit hπ τ : B) := by
  rw [tameUnit_mul]; rfl

def tameChar {π : B} (hπ : Irreducible π) (σ : RingAut B) : ResidueField B :=
  residue B (tameUnit hπ σ : B)

theorem isUnit_tameChar {π : B} (hπ : Irreducible π) (σ : RingAut B) :
    IsUnit (tameChar hπ σ) := (tameUnit hπ σ).isUnit.map (residue B)

theorem tameChar_ne_zero {π : B} (hπ : Irreducible π) (σ : RingAut B) :
    tameChar hπ σ ≠ 0 := (isUnit_tameChar hπ σ).ne_zero

theorem tameChar_one {π : B} (hπ : Irreducible π) : tameChar hπ 1 = 1 := by
  simp [tameChar, tameUnit_one]

/-- The cocycle identity at the level of the residue field. -/
theorem tameChar_mul' {π : B} (hπ : Irreducible π) (σ τ : RingAut B) :
    tameChar hπ (σ * τ) = tameChar hπ σ * residue B (σ (tameUnit hπ τ : B)) := by
  rw [tameChar, coe_tameUnit_mul, map_mul]; rfl

/-- If `σ` acts trivially on the residue field then `tameChar` is multiplicative in it. -/
theorem tameChar_mul {π : B} (hπ : Irreducible π) {σ : RingAut B}
    (hσ : ∀ b : B, residue B (σ b) = residue B b) (τ : RingAut B) :
    tameChar hπ (σ * τ) = tameChar hπ σ * tameChar hπ τ := by
  rw [tameChar_mul' hπ σ τ, hσ]; rfl

section Frobenius

variable {π : B} (hπ : Irreducible π) {σ τ : RingAut B} {q : ℕ}

/-- **Frobenius conjugation on the tame character.** -/
theorem tameChar_conj (hσ : ∀ b : B, residue B (σ b) = residue B b)
    (hτ : ∀ b : B, residue B (τ b) = residue B b ^ q) :
    tameChar hπ (τ * σ * τ⁻¹) = tameChar hπ σ ^ q := by
  have hinv : residue B (tameUnit hπ τ : B) * residue B (tameUnit hπ τ⁻¹ : B) ^ q = 1 := by
    have h1 : tameChar hπ (τ * τ⁻¹) = 1 := by rw [mul_inv_cancel, tameChar_one]
    rw [tameChar_mul' hπ τ τ⁻¹, hτ] at h1
    exact h1
  rw [mul_assoc, tameChar_mul' hπ τ (σ * τ⁻¹), coe_tameUnit_mul]
  simp only [map_mul, hτ, hσ, tameChar]
  linear_combination (residue B (tameUnit hπ σ : B)) ^ q * hinv

end Frobenius

/-- The automorphisms acting trivially on the residue field. -/
def inertiaAut (B : Type*) [CommRing B] [IsLocalRing B] : Subgroup (RingAut B) where
  carrier := {σ | ∀ b : B, residue B (σ b) = residue B b}
  mul_mem' {a b} ha hb x := (ha (b x)).trans (hb x)
  one_mem' _ := rfl
  inv_mem' {a} ha x := by
    conv_rhs => rw [show x = a (a⁻¹ x) from (RingEquiv.apply_symm_apply a x).symm]
    exact (ha (a⁻¹ x)).symm

theorem mem_inertiaAut {B : Type*} [CommRing B] [IsLocalRing B] {σ : RingAut B} :
    σ ∈ inertiaAut B ↔ ∀ b : B, residue B (σ b) = residue B b := Iff.rfl

theorem tameChar_pow {π : B} (hπ : Irreducible π) {σ : RingAut B} (hσ : σ ∈ inertiaAut B)
    (n : ℕ) : tameChar hπ (σ ^ n) = tameChar hπ σ ^ n := by
  induction n with
  | zero => simpa using tameChar_one hπ
  | succ n ih => rw [pow_succ', tameChar_mul hπ hσ, ih, ← pow_succ']

/-- **The tame character of an abelian tamely ramified extension is killed by `q - 1`.** -/
theorem tameChar_pow_sub_one_eq_one {π : B} (hπ : Irreducible π) {σ τ : RingAut B} {q : ℕ}
    (hq : 1 ≤ q) (hσ : σ ∈ inertiaAut B)
    (hτ : ∀ b : B, residue B (τ b) = residue B b ^ q) (hcomm : τ * σ = σ * τ) :
    tameChar hπ σ ^ (q - 1) = 1 := by
  have hconj : τ * σ * τ⁻¹ = σ := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have key : tameChar hπ σ = tameChar hπ σ ^ q := by
    conv_lhs => rw [← hconj]
    exact tameChar_conj hπ hσ hτ
  have hne : tameChar hπ σ ≠ 0 := tameChar_ne_zero hπ σ
  have hsplit : tameChar hπ σ ^ q = tameChar hπ σ * tameChar hπ σ ^ (q - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hsplit] at key
  exact (mul_eq_left₀ hne).1 key.symm

/-- **`e ∣ q - 1`, in the form `orderOf σ ∣ q - 1`.** -/
theorem orderOf_dvd_sub_one_of_tameChar_injective {π : B} (hπ : Irreducible π)
    {σ τ : RingAut B} {q : ℕ} (hq : 1 ≤ q) (hσ : σ ∈ inertiaAut B)
    (hτ : ∀ b : B, residue B (τ b) = residue B b ^ q) (hcomm : τ * σ = σ * τ)
    (hinj : ∀ g ∈ inertiaAut B, tameChar hπ g = 1 → g = 1) :
    orderOf σ ∣ q - 1 := by
  refine orderOf_dvd_of_pow_eq_one (hinj _ (Subgroup.pow_mem _ hσ _) ?_)
  rw [tameChar_pow hπ hσ]
  exact tameChar_pow_sub_one_eq_one hπ hq hσ hτ hcomm

end LocalCFT
