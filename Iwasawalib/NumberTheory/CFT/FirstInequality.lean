/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.IdeleClassHerbrandValue
public import Iwasawalib.NumberTheory.CFT.SecondInequality

@[expose] public section

/-!
# What the Herbrand quotient of `C_L` does and does not give

For a cyclic extension `L / K` of number fields,
`NumberField.herbrand_ideleClassGroup_eq_card_of_unramified` gives

`#Ĥ⁰(Gal(L/K), C_L) / #Ĥ¹(Gal(L/K), C_L) = [L : K]`,

i.e. `#Ĥ⁰(C_L) = [L : K] · #Ĥ¹(C_L)`.  This file records exactly what follows.

## What follows

* `#Ĥ⁰(C_L) = [L : K] · #Ĥ¹(C_L)` — `NumberField.card_tateH0_ideleClassGroup_eq_mul`;
* hence `[L : K] ∣ #Ĥ⁰(C_L)` and, since `#Ĥ¹ ≥ 1`, the **second fundamental inequality**
  `#Ĥ⁰(C_L) ≥ [L : K]` again, this time with no hypothesis at all beyond
  everything-unramified — `NumberField.card_tateH0_ideleClassGroup_ge_of_unramified`;
* and, most importantly, the **exact equivalence**

  `Ĥ¹(Gal(L/K), C_L) = 0  ↔  #Ĥ⁰(Gal(L/K), C_L) ≤ [L : K]`

  (`NumberField.subsingleton_tateH1_ideleClassGroup_iff`), each side being equivalent to
  `#Ĥ⁰(C_L) = [L : K]`.

## What does *not* follow, and why

The first fundamental inequality is the assertion `H¹(Gal(L/K), C_L) = 0`.  The equivalence
above says precisely that it is the **same statement** as the norm-index upper bound
`[C_K : N_{L/K} C_L] ≤ [L : K]`.  Neither is available here:

* the Herbrand quotient gives only the *ratio* of the two orders, so it cannot bound either of
  them on its own — the second inequality `#Ĥ⁰ ≥ [L : K]` is the half that comes for free, and
  the other half is exactly the missing input;
* `H¹(Gal(L/K), 𝕀_L) = 0` is now unconditional
  (`NumberField.isZero_H1_repIdele`), so the long exact sequence of
  `1 → L^× → 𝕀_L → C_L → 1` gives an **injection** `H¹(C_L) ↪ H²(Gal(L/K), L^×)`; but making
  that injection land in `0` is the injectivity of `H²(G, L^×) → H²(G, 𝕀_L)`, the Hasse
  principle for the Brauer group, which is a genuinely deeper statement and is not proved in
  this repository.

So: the second fundamental inequality is a theorem here, the first is *equivalent* to a
statement that is not, and the two together would pin down `#Ĥ⁰(C_L) = [L : K]` and
`Ĥ¹(C_L) = 0`.  That equivalence is the content of this file.

## Main statements

* `CyclicTate.card_tateH0_eq_mul_of_herbrand_eq_natCast`,
  `CyclicTate.card_tateH1_eq_one_iff_of_herbrand_eq_natCast`,
  `CyclicTate.subsingleton_tateH1_iff_of_herbrand_eq_natCast` : the elementary content.
* `NumberField.card_tateH0_ideleClassGroup_eq_mul`,
  `NumberField.card_tateH0_ideleClassGroup_ge_of_unramified`,
  `NumberField.subsingleton_tateH1_ideleClassGroup_iff` : for `C_L`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MulAction CyclicTate
open NumberField.InfiniteAdeleRing

namespace CyclicTate

variable {G M : Type*} [Group G] [Fintype G] [AddCommGroup M] [DistribMulAction G M]
  (σ : G) [Finite (TateH0 G M σ)] [Finite (TateH1 G M σ)]

/-- **`#Ĥ⁰ = n · #Ĥ¹` when the Herbrand quotient is the natural number `n`.** -/
theorem card_tateH0_eq_mul_of_herbrand_eq_natCast {n : ℕ} (h : herbrand G M σ = (n : ℚ)) :
    Nat.card (TateH0 G M σ) = n * Nat.card (TateH1 G M σ) := by
  rw [herbrand_def, div_eq_iff (by exact_mod_cast (card_tateH1_pos (M := M) σ).ne')] at h
  exact_mod_cast h

/-- **`Ĥ¹` has order `1` exactly when `#Ĥ⁰` attains the Herbrand quotient.** -/
theorem card_tateH1_eq_one_iff_of_herbrand_eq_natCast {n : ℕ} (hn : n ≠ 0)
    (h : herbrand G M σ = (n : ℚ)) :
    Nat.card (TateH1 G M σ) = 1 ↔ Nat.card (TateH0 G M σ) = n := by
  have hmul := card_tateH0_eq_mul_of_herbrand_eq_natCast σ h
  constructor
  · intro h1
    rw [hmul, h1, mul_one]
  · intro h0
    rw [h0] at hmul
    have h2 : n * 1 = n * Nat.card (TateH1 G M σ) := by rw [mul_one]; exact hmul
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) h2).symm

/-- **`Ĥ¹` has order `1` exactly when `#Ĥ⁰` is at most the Herbrand quotient.**  The reverse
inequality `#Ĥ⁰ ≥ n` always holds. -/
theorem card_tateH1_eq_one_iff_card_tateH0_le {n : ℕ} (hn : n ≠ 0)
    (h : herbrand G M σ = (n : ℚ)) :
    Nat.card (TateH1 G M σ) = 1 ↔ Nat.card (TateH0 G M σ) ≤ n := by
  have hmul := card_tateH0_eq_mul_of_herbrand_eq_natCast σ h
  rw [card_tateH1_eq_one_iff_of_herbrand_eq_natCast σ hn h]
  refine ⟨le_of_eq, fun hle ↦ le_antisymm hle ?_⟩
  rw [hmul]
  exact Nat.le_mul_of_pos_right n (Nat.card_pos (α := TateH1 G M σ))

/-- **The vanishing of `Ĥ¹`, as an equivalence with the upper bound on `#Ĥ⁰`.** -/
theorem subsingleton_tateH1_iff_of_herbrand_eq_natCast {n : ℕ} (hn : n ≠ 0)
    (h : herbrand G M σ = (n : ℚ)) :
    Subsingleton (TateH1 G M σ) ↔ Nat.card (TateH0 G M σ) ≤ n := by
  rw [← card_tateH1_eq_one_iff_card_tateH0_le σ hn h, Nat.card_eq_one_iff_unique]
  exact ⟨fun hs ↦ ⟨hs, ⟨0⟩⟩, fun hs ↦ hs.1⟩

/-- **The Herbrand quotient divides `#Ĥ⁰`.** -/
theorem dvd_card_tateH0_of_herbrand_eq_natCast {n : ℕ} (h : herbrand G M σ = (n : ℚ)) :
    n ∣ Nat.card (TateH0 G M σ) :=
  ⟨_, card_tateH0_eq_mul_of_herbrand_eq_natCast σ h⟩

end CyclicTate

/-! ## The idele class group -/

namespace NumberField

attribute [local instance] NumberField.galInfiniteAdeleMulSemiringAction
  NumberField.galIdeleMulDistribMulAction Units.mulDistribMulActionRight
  NumberField.galIdeleClassMulDistribMulAction

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {S : Set (HeightOneSpectrum (𝓞 K))} {σ : L ≃ₐ[K] L}
variable [IsGalois K L] [Fintype S] [Fintype (placesOverSet K L S)]

section

variable
  (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
  (hsup : IdeleGroup.principalSubgroup (𝓞 L) L
    ⊔ IdeleGroup.sIdeleSubgroup L (placesOverSet K L S) = ⊤)
  (w₁ : ∀ v : InfinitePlace K, Fibre L v)
  [∀ v : InfinitePlace K, Subsingleton (stabilizer (L ≃ₐ[K] L) (w₁ v))]
  (w₂ : ∀ v : HeightOneSpectrum (𝓞 K), placesOver K L v)
  [∀ v : HeightOneSpectrum (𝓞 K), Fintype (stabilizer (L ≃ₐ[K] L) (w₂ v))]
  [∀ v : HeightOneSpectrum (𝓞 K),
    Fintype (decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L)))]
  (τ₂ : ∀ v : HeightOneSpectrum (𝓞 K),
    decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L)))
  (hτ₂ : ∀ (v : HeightOneSpectrum (𝓞 K))
    (d : decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L))),
    d ∈ Subgroup.zpowers (τ₂ v))
  (hram : ∀ v : HeightOneSpectrum (𝓞 K),
    v.asIdeal.ramificationIdx' (w₂ v : HeightOneSpectrum (𝓞 L)).asIdeal = 1)
  [Finite (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)]
  [Finite (CyclicTate.TateH1 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)]

include hgen hsup w₁ w₂ τ₂ hτ₂ hram

/-- **`#Ĥ⁰(Gal(L/K), C_L) = [L : K] · #Ĥ¹(Gal(L/K), C_L)`** for a cyclic extension unramified
at every place.  This is `NumberField.herbrand_ideleClassGroup_eq_card_of_unramified` read as a
statement about orders. -/
theorem card_tateH0_ideleClassGroup_eq_mul :
    Nat.card (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      = Nat.card (L ≃ₐ[K] L)
        * Nat.card (CyclicTate.TateH1 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ) :=
  CyclicTate.card_tateH0_eq_mul_of_herbrand_eq_natCast σ
    (herbrand_ideleClassGroup_eq_card_of_unramified hgen hsup w₁ w₂ τ₂ hτ₂ hram)

/-- **The second fundamental inequality `#Ĥ⁰(Gal(L/K), C_L) ≥ [L : K]`**, for a cyclic
extension unramified at every place, with no further hypothesis: it is the divisibility
`[L : K] ∣ #Ĥ⁰(C_L)` together with `#Ĥ¹ ≥ 1`. -/
theorem card_tateH0_ideleClassGroup_ge_of_unramified :
    Nat.card (L ≃ₐ[K] L)
      ≤ Nat.card (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ) := by
  rw [card_tateH0_ideleClassGroup_eq_mul hgen hsup w₁ w₂ τ₂ hτ₂ hram]
  exact Nat.le_mul_of_pos_right _ (Nat.card_pos (α := CyclicTate.TateH1 (L ≃ₐ[K] L)
    (Additive (IdeleClassGroup (𝓞 L) L)) σ))

/-- **`[L : K]` divides `#Ĥ⁰(Gal(L/K), C_L)`.** -/
theorem card_dvd_card_tateH0_ideleClassGroup :
    Nat.card (L ≃ₐ[K] L)
      ∣ Nat.card (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ) :=
  ⟨_, card_tateH0_ideleClassGroup_eq_mul hgen hsup w₁ w₂ τ₂ hτ₂ hram⟩

/-- **The first fundamental inequality is equivalent to the norm-index upper bound.**

`Ĥ¹(Gal(L/K), C_L) = 0` holds exactly when `#Ĥ⁰(Gal(L/K), C_L) ≤ [L : K]`.  Since the reverse
inequality is `NumberField.card_tateH0_ideleClassGroup_ge_of_unramified`, either side is
equivalent to `#Ĥ⁰(Gal(L/K), C_L) = [L : K]`.

This is the strongest statement that the Herbrand quotient of `C_L` yields about `H¹(C_L)`: it
determines the *ratio* `#Ĥ⁰ / #Ĥ¹`, never either order alone. -/
theorem subsingleton_tateH1_ideleClassGroup_iff :
    Subsingleton (CyclicTate.TateH1 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      ↔ Nat.card (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
          ≤ Nat.card (L ≃ₐ[K] L) :=
  CyclicTate.subsingleton_tateH1_iff_of_herbrand_eq_natCast σ
    (Nat.card_pos (α := L ≃ₐ[K] L)).ne'
    (herbrand_ideleClassGroup_eq_card_of_unramified hgen hsup w₁ w₂ τ₂ hτ₂ hram)

/-- **The first fundamental inequality is equivalent to `#Ĥ⁰(C_L) = [L : K]`.** -/
theorem subsingleton_tateH1_ideleClassGroup_iff_card_eq :
    Subsingleton (CyclicTate.TateH1 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      ↔ Nat.card (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
          = Nat.card (L ≃ₐ[K] L) := by
  rw [subsingleton_tateH1_ideleClassGroup_iff hgen hsup w₁ w₂ τ₂ hτ₂ hram]
  exact ⟨fun h ↦ le_antisymm h
      (card_tateH0_ideleClassGroup_ge_of_unramified hgen hsup w₁ w₂ τ₂ hτ₂ hram),
    le_of_eq⟩

end

/-! ## The statements with no auxiliary set of places -/

section Everywhere

variable
  (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
  (w₁ : ∀ v : InfinitePlace K, Fibre L v)
  [∀ v : InfinitePlace K, Subsingleton (stabilizer (L ≃ₐ[K] L) (w₁ v))]
  (w₂ : ∀ v : HeightOneSpectrum (𝓞 K), placesOver K L v)
  (τ₂ : ∀ v : HeightOneSpectrum (𝓞 K),
    decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L)))
  (hτ₂ : ∀ (v : HeightOneSpectrum (𝓞 K))
    (d : decompositionGroup K L (w₂ v : HeightOneSpectrum (𝓞 L))),
    d ∈ Subgroup.zpowers (τ₂ v))
  (hram : ∀ v : HeightOneSpectrum (𝓞 K),
    v.asIdeal.ramificationIdx' (w₂ v : HeightOneSpectrum (𝓞 L)).asIdeal = 1)

include hgen w₁ w₂ τ₂ hτ₂ hram

/-- **`#Ĥ⁰(Gal(L/K), C_L) = [L : K] · #Ĥ¹(Gal(L/K), C_L)`**, with no auxiliary set of places. -/
theorem card_tateH0_ideleClassGroup_eq_mul_everywhere :
    Nat.card (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      = Nat.card (L ≃ₐ[K] L)
        * Nat.card (CyclicTate.TateH1 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ) := by
  haveI := finite_tateH0_ideleClassGroup_of_unramified_everywhere hgen w₁ w₂ τ₂ hτ₂ hram
  haveI := finite_tateH1_ideleClassGroup_of_unramified_everywhere hgen w₁ w₂ τ₂ hτ₂ hram
  exact CyclicTate.card_tateH0_eq_mul_of_herbrand_eq_natCast σ
    (herbrand_ideleClassGroup_eq_card_of_unramified_everywhere hgen w₁ w₂ τ₂ hτ₂ hram)

/-- **The second fundamental inequality `#Ĥ⁰(Gal(L/K), C_L) ≥ [L : K]`**, with no auxiliary set
of places and no hypothesis beyond everything-unramified. -/
theorem card_tateH0_ideleClassGroup_ge_everywhere :
    Nat.card (L ≃ₐ[K] L)
      ≤ Nat.card (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ) := by
  haveI := finite_tateH1_ideleClassGroup_of_unramified_everywhere hgen w₁ w₂ τ₂ hτ₂ hram
  rw [card_tateH0_ideleClassGroup_eq_mul_everywhere hgen w₁ w₂ τ₂ hτ₂ hram]
  exact Nat.le_mul_of_pos_right _ (Nat.card_pos (α := CyclicTate.TateH1 (L ≃ₐ[K] L)
    (Additive (IdeleClassGroup (𝓞 L) L)) σ))

/-- **The first fundamental inequality is equivalent to the norm-index upper bound**, with no
auxiliary set of places: for a cyclic extension unramified at every place,

`Ĥ¹(Gal(L/K), C_L) = 0  ↔  #Ĥ⁰(Gal(L/K), C_L) ≤ [L : K]  ↔  #Ĥ⁰(Gal(L/K), C_L) = [L : K]`. -/
theorem subsingleton_tateH1_ideleClassGroup_iff_everywhere :
    Subsingleton (CyclicTate.TateH1 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
      ↔ Nat.card (CyclicTate.TateH0 (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L)) σ)
          ≤ Nat.card (L ≃ₐ[K] L) := by
  haveI := finite_tateH0_ideleClassGroup_of_unramified_everywhere hgen w₁ w₂ τ₂ hτ₂ hram
  haveI := finite_tateH1_ideleClassGroup_of_unramified_everywhere hgen w₁ w₂ τ₂ hτ₂ hram
  exact CyclicTate.subsingleton_tateH1_iff_of_herbrand_eq_natCast σ
    (Nat.card_pos (α := L ≃ₐ[K] L)).ne'
    (herbrand_ideleClassGroup_eq_card_of_unramified_everywhere hgen w₁ w₂ τ₂ hτ₂ hram)

/-! ### The same, for Mathlib's `groupCohomology` -/

/-- **`#H²(Gal(L/K), C_L) = [L : K] · #H¹(Gal(L/K), C_L)`** for a cyclic extension unramified at
every place, in Mathlib's `groupCohomology`. -/
theorem card_groupCohomology_ideleClassGroup_eq_mul :
    letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
    Nat.card (groupCohomology
        (CyclicTate.rep (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L))) 2 : ModuleCat ℤ)
      = Nat.card (L ≃ₐ[K] L) * Nat.card (groupCohomology
          (CyclicTate.rep (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L))) 1 :
            ModuleCat ℤ) := by
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  rw [← CyclicTate.card_tateH0_eq (M := Additive (IdeleClassGroup (𝓞 L) L)) σ hσ 2 (by decide),
    ← CyclicTate.card_tateH1_eq (M := Additive (IdeleClassGroup (𝓞 L) L)) σ hσ 1 ⟨0, by ring⟩]
  exact card_tateH0_ideleClassGroup_eq_mul_everywhere hgen w₁ w₂ τ₂ hτ₂ hram

/-- **The first fundamental inequality, in Mathlib's `groupCohomology`:**

`H¹(Gal(L/K), C_L) = 0  ↔  #H²(Gal(L/K), C_L) ≤ [L : K]`

for a cyclic extension unramified at every place.  The right-hand side is the norm-index upper
bound; the reverse inequality `#H²(Gal(L/K), C_L) ≥ [L : K]` is the second fundamental
inequality, which *is* proved here
(`NumberField.card_groupCohomology_two_ideleClassGroup_ge` and
`NumberField.card_tateH0_ideleClassGroup_ge_everywhere`). -/
theorem subsingleton_groupCohomology_one_ideleClassGroup_iff :
    letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
    Subsingleton (groupCohomology
        (CyclicTate.rep (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L))) 1 : ModuleCat ℤ)
      ↔ Nat.card (groupCohomology
          (CyclicTate.rep (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L))) 2 : ModuleCat ℤ)
          ≤ Nat.card (L ≃ₐ[K] L) := by
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  rw [← CyclicTate.card_tateH0_eq (M := Additive (IdeleClassGroup (𝓞 L) L)) σ hσ 2 (by decide),
    ← subsingleton_tateH1_ideleClassGroup_iff_everywhere hgen w₁ w₂ τ₂ hτ₂ hram]
  exact (Equiv.subsingleton_congr (CyclicTate.tateH1EquivGroupCohomology
    (M := Additive (IdeleClassGroup (𝓞 L) L)) σ hσ 1 ⟨0, by ring⟩).toEquiv).symm

end Everywhere

end NumberField
