/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.SubgroupIdele
public import Iwasawalib.GroupCohomology.UnramifiedIdele
public import Iwasawalib.NumberTheory.CFT.FirstInequality

@[expose] public section

/-!
# The Hasse principle for the Brauer group is the first fundamental inequality

For a finite Galois extension `L / K` of number fields the injectivity of

`H²(Gal(L/K), Lˣ) ⟶ H²(Gal(L/K), 𝕀_L)`

-- the Hasse principle for the Brauer group of `L / K` -- is the one hypothesis under which
`Iwasawalib/GroupCohomology/IdeleShortExact.lean` and
`Iwasawalib/GroupCohomology/UnramifiedIdele.lean` deduce `H¹(Gal(L/K), C_L) = 0`, the first
axiom of a class formation.  This file names that hypothesis
(`NumberField.BrauerHassePrinciple`) and determines its exact logical strength.

## The result

The deduction is **reversible**.  Since `H¹(Gal(L/K), 𝕀_L) = 0` unconditionally
(`NumberField.isZero_H1_repIdele`), the long exact sequence of `1 ⟶ Lˣ ⟶ 𝕀_L ⟶ C_L ⟶ 1`
reads

`0 = H¹(𝕀_L) ⟶ H¹(C_L) --δ--> H²(Lˣ) ⟶ H²(𝕀_L)`

and is exact at both `H¹(C_L)` and `H²(Lˣ)`.  Exactness at `H¹(C_L)` makes `δ` injective, which
is the implication already in the library; exactness at `H²(Lˣ)` identifies the kernel of
`H²(Lˣ) ⟶ H²(𝕀_L)` with the image of `δ`, which gives the converse.  Hence

`NumberField.brauerHassePrinciple_iff_isZero_H1_repIdeleClass` :
  `BrauerHassePrinciple K L ↔ H¹(Gal(L/K), C_L) = 0`,

with no hypothesis at all beyond `L / K` finite Galois.

Combining this with `NumberField.subsingleton_groupCohomology_one_ideleClassGroup_iff` — which
says that for a cyclic extension unramified at every place `H¹(C_L) = 0` is equivalent to the
norm-index bound `#H²(Gal(L/K), C_L) ≤ [L : K]` — gives

`NumberField.brauerHassePrinciple_iff_card_le` :
  `BrauerHassePrinciple K L ↔ #H²(Gal(L/K), C_L) ≤ [L : K]`.

So for cyclic extensions the Hasse principle for the Brauer group is **not a route to** the
first fundamental inequality: it is *equivalent* to it, hence to the Hasse norm theorem
`Kˣ ∩ N 𝕀_L = N Lˣ`.  Proving it therefore requires an input of the same depth as the first
inequality itself — the analytic norm-index bound, or the local invariant maps of local class
field theory together with a reduction to the cyclotomic case.  It cannot be obtained from the
Herbrand quotient `h(C_L) = [L : K]`, which is what this library has: that computation fixes
only the *ratio* `#H² / #H¹`.

## Main definitions

* `NumberField.BrauerHassePrinciple` : injectivity of `H²(Gal(L/K), Lˣ) ⟶ H²(Gal(L/K), 𝕀_L)`.

## Main statements

* `groupCohomology.mono_of_isZero`, `groupCohomology.mono_iff_isZero` : the general converse in
  the long exact sequence.
* `NumberField.brauerHassePrinciple_iff_isZero_H1_repIdeleClass` : the equivalence with
  `H¹(Gal(L/K), C_L) = 0`, unconditionally.
* `NumberField.brauerHassePrinciple_fixedField_iff_isZero_H1_subgroup` : the same for every
  subgroup `H ≤ Gal(L/K)`, as the axioms of a class formation require.
* `NumberField.brauerHassePrinciple_iff_card_le`,
  `NumberField.brauerHassePrinciple_iff_card_eq` : the equivalence with the first fundamental
  inequality, for a cyclic extension unramified at every place.
* `NumberField.card_groupCohomology_two_ideleClassGroup_eq_of_brauerHassePrinciple` :
  `#H²(Gal(L/K), C_L) = [L : K]`, the second axiom of a class formation at the level of orders,
  granted the Hasse principle.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits IsDedekindDomain MulAction IntermediateField

/-! ## The converse implication in the long exact sequence -/

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep.{u} k G)}

/-- **The converse of `groupCohomology.isZero_of_isZero_of_mono`.**  If
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is a short exact sequence of representations and `Hⁿ(G, X₃) = 0`, then
`Hⁿ⁺¹(G, X₁) ⟶ Hⁿ⁺¹(G, X₂)` is injective.

Indeed the connecting map `δ : Hⁿ(G, X₃) ⟶ Hⁿ⁺¹(G, X₁)` is zero because its source is zero, and
the kernel of `Hⁿ⁺¹(G, X₁) ⟶ Hⁿ⁺¹(G, X₂)` is the image of `δ` by exactness. -/
theorem mono_of_isZero (hX : X.ShortExact) (n : ℕ)
    (h₃ : IsZero (groupCohomology X.X₃ n)) :
    Mono (map (MonoidHom.id G) X.f (n + 1)) :=
  (ShortComplex.exact_iff_mono _ (h₃.eq_zero_of_src _)).1
    (mapShortComplex₁_exact hX (i := n) (j := n + 1) rfl)

/-- **The vanishing of `Hⁿ(G, X₃)` and the injectivity of `Hⁿ⁺¹(G, X₁) ⟶ Hⁿ⁺¹(G, X₂)` are
equivalent**, for a short exact sequence of representations with `Hⁿ(G, X₂) = 0`. -/
theorem mono_iff_isZero (hX : X.ShortExact) (n : ℕ)
    (h₂ : IsZero (groupCohomology X.X₂ n)) :
    Mono (map (MonoidHom.id G) X.f (n + 1)) ↔ IsZero (groupCohomology X.X₃ n) :=
  ⟨fun h ↦ isZero_of_isZero_of_mono hX n h₂ h, fun h ↦ mono_of_isZero hX n h⟩

end groupCohomology

/-! ## The Hasse principle for the Brauer group -/

namespace NumberField

attribute [local instance] NumberField.galInfiniteAdeleMulSemiringAction
  NumberField.galIdeleMulDistribMulAction Units.mulDistribMulActionRight
  NumberField.galIdeleClassMulDistribMulAction

section Defn

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **The Hasse principle for the Brauer group of `L / K`**: the map
`H²(Gal(L/K), Lˣ) ⟶ H²(Gal(L/K), 𝕀_L)` induced by the inclusion of the principal ideles is
injective.

Classically this is the statement that a class in the Brauer group `H²(Gal(L/K), Lˣ)` which
becomes trivial in every completion is trivial.  It is *not* proved in this repository; see
`NumberField.brauerHassePrinciple_iff_card_le` for exactly how strong it is. -/
def BrauerHassePrinciple : Prop :=
  Mono ((groupCohomology.functor ℤ (L ≃ₐ[K] L) 2).map (ideleShortComplex K L).f)

/-- **The Hasse principle for the Brauer group is equivalent to `H¹(Gal(L/K), C_L) = 0`.**

This is the long exact sequence of `1 ⟶ Lˣ ⟶ 𝕀_L ⟶ C_L ⟶ 1` together with the unconditional
vanishing `NumberField.isZero_H1_repIdele` of `H¹(Gal(L/K), 𝕀_L)`.  No further hypothesis is
needed: in particular the implication that the library already had
(`NumberField.isZero_H1_repIdeleClass`) is reversible. -/
theorem brauerHassePrinciple_iff_isZero_H1_repIdeleClass :
    BrauerHassePrinciple K L ↔ IsZero (groupCohomology (repIdeleClass K L) 1) :=
  groupCohomology.mono_iff_isZero (ideleShortComplex_shortExact K L) 1 (isZero_H1_repIdele K L)

/-- The Hasse principle for the Brauer group gives `H¹(Gal(L/K), C_L) = 0`. -/
theorem isZero_H1_repIdeleClass_of_brauerHassePrinciple (h : BrauerHassePrinciple K L) :
    IsZero (groupCohomology (repIdeleClass K L) 1) :=
  (brauerHassePrinciple_iff_isZero_H1_repIdeleClass K L).1 h

/-- `H¹(Gal(L/K), C_L) = 0` gives the Hasse principle for the Brauer group. -/
theorem brauerHassePrinciple_of_isZero_H1_repIdeleClass
    (h : IsZero (groupCohomology (repIdeleClass K L) 1)) :
    BrauerHassePrinciple K L :=
  (brauerHassePrinciple_iff_isZero_H1_repIdeleClass K L).2 h

/-- **The Hasse principle holds when `L = K`.**  A satisfiability control for
`NumberField.BrauerHassePrinciple`: the definition is not vacuously false, and the equivalence
`NumberField.brauerHassePrinciple_iff_isZero_H1_repIdeleClass` is not an equivalence between two
unprovable statements.  For a trivial Galois group every higher cohomology group vanishes. -/
theorem brauerHassePrinciple_of_subsingleton [Subsingleton (L ≃ₐ[K] L)] :
    BrauerHassePrinciple K L :=
  brauerHassePrinciple_of_isZero_H1_repIdeleClass K L
    (isZero_groupCohomology_succ_of_subsingleton _ 0)

end Defn

/-! ## The same for every subgroup of the Galois group -/

section Subgroup

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L))

/-- **The Hasse principle over the fixed field `L^H` is equivalent to `H¹(H, C_L) = 0`**, for
every subgroup `H ≤ Gal(L/K)`.

The axioms of a class formation are quantified over all subgroups, so this is the form in which
the equivalence is needed; the transport is `NumberField.subgroupIdeleClassIso`. -/
theorem brauerHassePrinciple_fixedField_iff_isZero_H1_subgroup :
    BrauerHassePrinciple (fixedField H) L ↔
      IsZero (groupCohomology (Rep.ofMulDistribMulAction H (IdeleClassGroup (𝓞 L) L)) 1) := by
  rw [brauerHassePrinciple_iff_isZero_H1_repIdeleClass]
  exact ⟨fun h ↦ h.of_iso (subgroupIdeleClassIso H 1),
    fun h ↦ h.of_iso (subgroupIdeleClassIso H 1).symm⟩

/-- **The first axiom of a class formation for `C_L`, for every subgroup at once**, granted the
Hasse principle for the Brauer group over every fixed field. -/
theorem isZero_H1_subgroup_repIdeleClass_of_brauerHassePrinciple
    (h : ∀ H : Subgroup (L ≃ₐ[K] L), BrauerHassePrinciple (fixedField H) L)
    (H : Subgroup (L ≃ₐ[K] L)) :
    IsZero (groupCohomology (Rep.ofMulDistribMulAction H (IdeleClassGroup (𝓞 L) L)) 1) :=
  (brauerHassePrinciple_fixedField_iff_isZero_H1_subgroup H).1 (h H)

end Subgroup

/-! ## What the Hasse principle is worth, for a cyclic extension -/

section Cyclic

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {σ : L ≃ₐ[K] L}

variable
  (hgen : ∀ g : L ≃ₐ[K] L, ∃ m : ℕ, σ ^ m = g)
  (w₁ : ∀ v : InfinitePlace K, InfiniteAdeleRing.Fibre L v)
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

/-- **The Hasse principle for the Brauer group is the first fundamental inequality.**

For a cyclic extension `L / K` unramified at every place,

`H²(Gal(L/K), Lˣ) ⟶ H²(Gal(L/K), 𝕀_L)` is injective  ↔  `#H²(Gal(L/K), C_L) ≤ [L : K]`.

The right-hand side is the norm-index upper bound `[C_K : N C_L] ≤ [L : K]`, i.e. the first
fundamental inequality (see `NumberField.subsingleton_groupCohomology_one_ideleClassGroup_iff`).
So the Hasse principle is not a weaker input from which the first inequality could be derived:
the two are the same statement, and neither follows from the Herbrand quotient
`h(C_L) = [L : K]` proved in this library. -/
theorem brauerHassePrinciple_iff_card_le :
    letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
    BrauerHassePrinciple K L
      ↔ Nat.card (groupCohomology
          (CyclicTate.rep (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L))) 2 : ModuleCat ℤ)
          ≤ Nat.card (L ≃ₐ[K] L) := by
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  rw [← subsingleton_groupCohomology_one_ideleClassGroup_iff hgen w₁ w₂ τ₂ hτ₂ hram,
    brauerHassePrinciple_iff_isZero_H1_repIdeleClass]
  exact ModuleCat.isZero_iff_subsingleton

/-- **The Hasse principle for the Brauer group is equivalent to `#H²(C_L) = [L : K]`**, for a
cyclic extension unramified at every place: the reverse inequality `#H² ≥ [L : K]` is the
second fundamental inequality, which *is* a theorem here
(`NumberField.card_tateH0_ideleClassGroup_ge_everywhere`). -/
theorem brauerHassePrinciple_iff_card_eq :
    letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
    BrauerHassePrinciple K L
      ↔ Nat.card (groupCohomology
          (CyclicTate.rep (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L))) 2 : ModuleCat ℤ)
          = Nat.card (L ≃ₐ[K] L) := by
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  rw [brauerHassePrinciple_iff_card_le hgen w₁ w₂ τ₂ hτ₂ hram]
  refine ⟨fun h ↦ le_antisymm h ?_, le_of_eq⟩
  have hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ := fun g ↦ by
    obtain ⟨m, rfl⟩ := hgen g
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  haveI := finite_tateH0_ideleClassGroup_of_unramified_everywhere hgen w₁ w₂ τ₂ hτ₂ hram
  haveI := finite_tateH1_ideleClassGroup_of_unramified_everywhere hgen w₁ w₂ τ₂ hτ₂ hram
  rw [← CyclicTate.card_tateH0_eq (M := Additive (IdeleClassGroup (𝓞 L) L)) σ hσ 2 (by decide)]
  exact card_tateH0_ideleClassGroup_ge_everywhere hgen w₁ w₂ τ₂ hτ₂ hram

/-- **`#H²(Gal(L/K), C_L) = [L : K]`**, granted the Hasse principle for the Brauer group.  This
is the order statement behind the second axiom of a class formation. -/
theorem card_groupCohomology_two_ideleClassGroup_eq_of_brauerHassePrinciple
    (h : BrauerHassePrinciple K L) :
    letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
    Nat.card (groupCohomology
        (CyclicTate.rep (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L))) 2 : ModuleCat ℤ)
      = Nat.card (L ≃ₐ[K] L) :=
  (brauerHassePrinciple_iff_card_eq hgen w₁ w₂ τ₂ hτ₂ hram).1 h

/-- **`H¹(Gal(L/K), C_L) = 0`**, granted the Hasse principle for the Brauer group: the first
axiom of a class formation, in the cyclic unramified case. -/
theorem subsingleton_groupCohomology_one_ideleClassGroup_of_brauerHassePrinciple
    (h : BrauerHassePrinciple K L) :
    letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
    Subsingleton (groupCohomology
      (CyclicTate.rep (L ≃ₐ[K] L) (Additive (IdeleClassGroup (𝓞 L) L))) 1 : ModuleCat ℤ) := by
  letI : CommGroup (L ≃ₐ[K] L) := CyclicTate.commGroupOfGen hgen
  exact (subsingleton_groupCohomology_one_ideleClassGroup_iff hgen w₁ w₂ τ₂ hτ₂ hram).2
    ((brauerHassePrinciple_iff_card_le hgen w₁ w₂ τ₂ hτ₂ hram).1 h)

end Cyclic

end NumberField
