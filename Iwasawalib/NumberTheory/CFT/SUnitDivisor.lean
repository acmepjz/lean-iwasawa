/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.AdicOrd
public import Iwasawalib.NumberTheory.CFT.SIdeles
public import Iwasawalib.NumberTheory.CFT.SUnitLog
public import Mathlib.NumberTheory.NumberField.ClassNumber

@[expose] public section

/-!
# The divisor map on `S`-units, and Dirichlet's `S`-unit theorem

Let `L` be a number field and `T` a set of finite places of `L`.  This file studies the
**divisor map**
`O_{L,T}^\times \to \bigoplus_{w \in T} \mathbb{Z}, \quad x \mapsto (\operatorname{ord}_w x)_{w}`
and uses it to prove Dirichlet's `S`-unit theorem.

## Main definitions

* `NumberField.sDivisor L T` : the divisor map `Additive (T.unit L) →+ (T → ℤ)`.
* `NumberField.unitsToSUnit L T` : the inclusion of `(𝓞 L)ˣ` into the `T`-units.

## Main results

* `NumberField.sDivisor_eq_zero_iff` : the kernel of the divisor map is `(𝓞 L)ˣ`; this is the
  exactness of `1 → O_L^× → O_{L,T}^× → ⊕_{w ∈ T} ℤ`.
* `NumberField.exists_sDivisor_eq_classNumber_smul` : the image of the divisor map contains
  `h · ℤ^T`, where `h` is the class number of `L`.  This is the finiteness of the cokernel,
  and it is the ideal-theoretic input to the `S`-unit theorem.
* `NumberField.module_finite_sUnit` : the group of `T`-units is finitely generated.
* `NumberField.rank_sUnit`, `NumberField.finrank_sUnit` : **Dirichlet's `S`-unit theorem**,
  `rank O_{L,T}^× = rank O_L^× + #T = r₁ + r₂ - 1 + #T`.
* `NumberField.sDivisor_smul` : **the divisor map is `Gal(L/K)`-equivariant** when `T` is the
  set of places above a set `S` of places of the base field `K`.  Together with
  `NumberField.sLogEmbedding_smul` this exhibits the `S`-units as a `Gal(L/K)`-stable lattice
  mapping equivariantly to `∏_{w ∈ S} ℤ`, which is the shape required by the computation of
  the Herbrand quotient of the `S`-unit group.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- A unit of the ring of integers has valuation `1` at every finite place. -/
theorem valuation_unit_eq_one (u : (𝓞 L)ˣ) (v : HeightOneSpectrum (𝓞 L)) :
    v.valuation L (algebraMap (𝓞 L) L (u : 𝓞 L)) = 1 := by
  have h : v.valuation L (algebraMap (𝓞 L) L (u : 𝓞 L)) *
      v.valuation L (algebraMap (𝓞 L) L ((u⁻¹ : (𝓞 L)ˣ) : 𝓞 L)) = 1 := by
    rw [← map_mul, ← map_mul, u.mul_inv, map_one, map_one]
  exact eq_one_of_mul_eq_one_of_le_one h (v.valuation_le_one _) (v.valuation_le_one _)

/-- The order of vanishing of a unit of the ring of integers is `0` at every finite place. -/
theorem ord_unit_eq_zero (u : (𝓞 L)ˣ) (v : HeightOneSpectrum (𝓞 L)) :
    v.ord L (algebraMap (𝓞 L) L (u : 𝓞 L)) = 0 := by
  have hne : algebraMap (𝓞 L) L (u : 𝓞 L) ≠ 0 := by
    simp only [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 L) L)]
    exact u.ne_zero
  exact (ord_eq_zero_iff hne).2 (valuation_unit_eq_one u v)

theorem mem_unit_iff_ord {T : Set (HeightOneSpectrum (𝓞 L))} (x : Lˣ) :
    x ∈ T.unit L ↔ ∀ w : HeightOneSpectrum (𝓞 L), w ∉ T → w.ord L (x : L) = 0 := by
  constructor
  · exact fun hx w hw ↦ (ord_eq_zero_iff (x.ne_zero : (x : L) ≠ 0)).2 (hx w hw)
  · exact fun hx w hw ↦ (ord_eq_zero_iff (x.ne_zero : (x : L) ≠ 0)).1 (hx w hw)

variable (L) in
/-- **The divisor map on the `T`-units**, `x ↦ (ord_w x)_{w ∈ T}`. -/
def sDivisor (T : Set (HeightOneSpectrum (𝓞 L))) : Additive (T.unit L) →+ (T → ℤ) where
  toFun x w := (w : HeightOneSpectrum (𝓞 L)).ord L ((((Additive.toMul x : T.unit L) : Lˣ) : L))
  map_zero' := by
    funext w
    exact ord_one
  map_add' x y := by
    funext w
    exact ord_mul (Units.ne_zero _) (Units.ne_zero _)

@[simp]
theorem sDivisor_apply {T : Set (HeightOneSpectrum (𝓞 L))} (x : T.unit L)
    (w : T) :
    sDivisor L T (Additive.ofMul x) w
      = (w : HeightOneSpectrum (𝓞 L)).ord L ((x : Lˣ) : L) := rfl

/-- **The kernel of the divisor map on the `T`-units is the unit group of the ring of
integers.** -/
theorem sDivisor_eq_zero_iff {T : Set (HeightOneSpectrum (𝓞 L))} (x : T.unit L) :
    sDivisor L T (Additive.ofMul x) = 0 ↔
      ∃ u : (𝓞 L)ˣ, Units.map (algebraMap (𝓞 L) L : (𝓞 L) →* L) u = (x : Lˣ) := by
  constructor
  · intro h
    have hval : ∀ v : HeightOneSpectrum (𝓞 L), v.valuation L ((x : Lˣ) : L) = 1 := by
      intro v
      by_cases hv : v ∈ T
      · have := congrFun h ⟨v, hv⟩
        exact (ord_eq_zero_iff (Units.ne_zero _)).1 this
      · exact x.2 v hv
    obtain ⟨u, hu⟩ := exists_unit_ringOfIntegers_of_valuation_eq_one hval
    exact ⟨u, Units.ext hu⟩
  · rintro ⟨u, hu⟩
    funext w
    rw [sDivisor_apply, ← hu]
    exact ord_unit_eq_zero u _

/-- **The image of the divisor map on the `T`-units contains `h · ℤ^T`**, where `h` is the
class number of `L`.  This is the ideal-theoretic half of Dirichlet's `S`-unit theorem: the
divisor map from the `S`-units to `ℤ^S` has image of finite index. -/
theorem exists_sDivisor_eq_classNumber_smul {T : Set (HeightOneSpectrum (𝓞 L))}
    (hT : T.Finite) (n : T → ℤ) :
    ∃ x : T.unit L,
      sDivisor L T (Additive.ofMul x) = (NumberField.classNumber L : ℤ) • n := by
  classical
  set m : HeightOneSpectrum (𝓞 L) → ℤ := fun v ↦ if h : v ∈ T then n ⟨v, h⟩ else 0 with hm
  have hmsupp : ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite, m v = 0 := by
    rw [Filter.eventually_cofinite]
    refine hT.subset fun v hv ↦ ?_
    by_contra hvT
    exact hv (by simp [hm, hvT])
  obtain ⟨x, hx⟩ := IsDedekindDomain.HeightOneSpectrum.exists_ord_eq_card_classGroup_smul
    (R := 𝓞 L) L m hmsupp
  have hxT : x ∈ T.unit L := by
    rw [mem_unit_iff_ord]
    intro w hw
    rw [hx w, hm]
    simp [hw]
  refine ⟨⟨x, hxT⟩, ?_⟩
  funext w
  rw [sDivisor_apply, hx]
  simp [hm, w.2, NumberField.classNumber]

variable (L) in
/-- The unit group of the ring of integers, as a subgroup of the `T`-units. -/
def unitsToSUnit (T : Set (HeightOneSpectrum (𝓞 L))) :
    Additive (𝓞 L)ˣ →+ Additive (T.unit L) where
  toFun u := Additive.ofMul
    ⟨Units.map (algebraMap (𝓞 L) L : (𝓞 L) →* L) (Additive.toMul u),
      (mem_unit_iff_ord _).2 fun w _ ↦ ord_unit_eq_zero _ _⟩
  map_zero' := by
    refine congrArg Additive.ofMul (Subtype.ext ?_)
    exact map_one _
  map_add' u u' := by
    refine congrArg Additive.ofMul (Subtype.ext ?_)
    exact map_mul _ _ _

@[simp]
theorem coe_unitsToSUnit {T : Set (HeightOneSpectrum (𝓞 L))} (u : (𝓞 L)ˣ) :
    ((Additive.toMul (unitsToSUnit L T (Additive.ofMul u)) : T.unit L) : Lˣ)
      = Units.map (algebraMap (𝓞 L) L : (𝓞 L) →* L) u := rfl

theorem ker_sDivisor {T : Set (HeightOneSpectrum (𝓞 L))} :
    LinearMap.ker (sDivisor L T).toIntLinearMap
      = LinearMap.range (unitsToSUnit L T).toIntLinearMap := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu⟩ := (sDivisor_eq_zero_iff (Additive.toMul x)).1 hx
    exact ⟨Additive.ofMul u, by
      refine congrArg Additive.ofMul (Subtype.ext ?_)
      exact hu⟩
  · rintro ⟨u, rfl⟩
    refine (sDivisor_eq_zero_iff (T := T) _).2 ⟨Additive.toMul u, ?_⟩
    rfl

/-- **The group of `T`-units of a number field is finitely generated**, for any finite set `T`
of finite places. -/
theorem module_finite_sUnit {T : Set (HeightOneSpectrum (𝓞 L))} (hT : T.Finite) :
    Module.Finite ℤ (Additive (T.unit L)) := by
  have : Finite T := hT.to_subtype
  have : Fintype T := Fintype.ofFinite T
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (sDivisor L T).toIntLinearMap ?_ ?_⟩
  · exact IsNoetherian.noetherian _
  · rw [top_inf_eq, ker_sDivisor, ← Submodule.map_top]
    exact (Module.Finite.fg_top (R := ℤ) (M := Additive (𝓞 L)ˣ)).map _

/-! ## Galois equivariance -/

section Galois

variable {K : Type*} [Field K] [NumberField K] [Algebra K L]

omit [NumberField K] in
/-- **The order of vanishing is Galois equivariant**: `ord_{σw}(σx) = ord_w(x)`. -/
theorem ord_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    (σ • w).ord L (σ x) = w.ord L x := by
  simp only [IsDedekindDomain.HeightOneSpectrum.ord, valuation_smul_heightOneSpectrum]

omit [NumberField K] in
/-- **The divisor map on the `S`-units is a map of `Gal(L/K)`-modules.** -/
theorem sDivisor_smul (S : Set (HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L)
    (x : SUnitGroup K L S) (w : placesOverSet K L S) :
    sDivisor L (placesOverSet K L S) (Additive.ofMul (σ • x)) (σ • w)
      = sDivisor L (placesOverSet K L S) (Additive.ofMul x) w := by
  rw [sDivisor_apply, sDivisor_apply, coe_smul_SUnitGroup, coe_smul_units,
    coe_smul_placesOverSet, ord_smul]

end Galois

/-! ## Dirichlet's `S`-unit theorem: the rank -/

/-- A subgroup of `ℤ^T` containing `h ℤ^T` for some `h ≠ 0` has rank `#T`. -/
theorem rank_submodule_of_smul_mem {T : Type*} [Fintype T] {h : ℤ} (hh : h ≠ 0)
    (A : Submodule ℤ (T → ℤ)) (hA : ∀ n : T → ℤ, h • n ∈ A) :
    Module.rank ℤ A = Fintype.card T := by
  have hle : Module.rank ℤ A ≤ Module.rank ℤ (T → ℤ) := Submodule.rank_le A
  set φ : (T → ℤ) →ₗ[ℤ] (T → ℤ) := h • LinearMap.id with hφ
  have hinj : Function.Injective φ := fun a b hab ↦ smul_right_injective (T → ℤ) hh hab
  have hrange : LinearMap.range φ ≤ A := by
    rintro _ ⟨n, rfl⟩
    exact hA n
  have h1 : Module.rank ℤ (T → ℤ) = Module.rank ℤ (LinearMap.range φ) :=
    (LinearEquiv.ofInjective φ hinj).rank_eq
  have h2 : Module.rank ℤ (LinearMap.range φ) ≤ Module.rank ℤ A := Submodule.rank_mono hrange
  have h3 : Module.rank ℤ (T → ℤ) = Fintype.card T := by simp
  rw [← h3]
  exact le_antisymm hle (h1 ▸ h2)

theorem unitsToSUnit_injective {T : Set (HeightOneSpectrum (𝓞 L))} :
    Function.Injective (unitsToSUnit L T) := by
  intro u u' h
  have h' : Units.map (algebraMap (𝓞 L) L : (𝓞 L) →* L) (Additive.toMul u)
      = Units.map (algebraMap (𝓞 L) L : (𝓞 L) →* L) (Additive.toMul u') :=
    congrArg (fun y ↦ ((Additive.toMul y : T.unit L) : Lˣ)) h
  exact Additive.toMul.injective
    (Units.map_injective (FaithfulSMul.algebraMap_injective (𝓞 L) L) h')

/-- **Dirichlet's `S`-unit theorem** (rank form).  For a finite set `T` of finite places of a
number field `L`, the group of `T`-units is a finitely generated abelian group of rank
`rank (𝓞 L)ˣ + #T = r₁ + r₂ - 1 + #T`. -/
theorem rank_sUnit {T : Set (HeightOneSpectrum (𝓞 L))} (hT : T.Finite) :
    Module.rank ℤ (Additive (T.unit L))
      = Module.rank ℤ (Additive (𝓞 L)ˣ) + Nat.card T := by
  have : Finite T := hT.to_subtype
  have hfT : Fintype T := Fintype.ofFinite T
  set g := (sDivisor L T).toIntLinearMap with hg
  set f := (unitsToSUnit L T).toIntLinearMap with hf
  have hfinj : Function.Injective f := unitsToSUnit_injective
  have h1 : Module.rank ℤ (LinearMap.ker g) = Module.rank ℤ (Additive (𝓞 L)ˣ) := by
    rw [hg, ker_sDivisor, ← hf]
    exact ((LinearEquiv.ofInjective f hfinj).rank_eq).symm
  have hA : ∀ n : T → ℤ, (NumberField.classNumber L : ℤ) • n ∈ LinearMap.range g := by
    intro n
    obtain ⟨x, hx⟩ := exists_sDivisor_eq_classNumber_smul hT n
    exact ⟨Additive.ofMul x, hx⟩
  have hh : (NumberField.classNumber L : ℤ) ≠ 0 := by
    exact_mod_cast NumberField.classNumber_ne_zero L
  have h2 : Module.rank ℤ (Additive (T.unit L) ⧸ LinearMap.ker g) = Fintype.card T := by
    rw [(g.quotKerEquivRange).rank_eq]
    exact rank_submodule_of_smul_mem hh _ hA
  have hsum := rank_quotient_add_rank_of_isDomain (R := ℤ) (LinearMap.ker g)
  rw [h1, h2] at hsum
  rw [← hsum, Nat.card_eq_fintype_card, add_comm]

open Module in
/-- **Dirichlet's `S`-unit theorem.**  The group of `T`-units of `L` is a finitely generated
abelian group whose free rank is `rank (𝓞 L)ˣ + #T`, i.e. `r₁ + r₂ - 1 + #T`. -/
theorem finrank_sUnit {T : Set (HeightOneSpectrum (𝓞 L))} (hT : T.Finite) :
    finrank ℤ (Additive (T.unit L)) = NumberField.Units.rank L + Nat.card T := by
  have : Finite T := hT.to_subtype
  have hfT : Fintype T := Fintype.ofFinite T
  have hfin : Module.rank ℤ (Additive (𝓞 L)ˣ) < Cardinal.aleph0 := Module.rank_lt_aleph0 _ _
  have hnat : (Nat.card T : Cardinal.{_}) < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  show (Module.rank ℤ (Additive (T.unit L))).toNat = _
  rw [rank_sUnit hT, Cardinal.toNat_add hfin hnat, Cardinal.toNat_natCast]
  congr 1
  exact NumberField.Units.finrank_eq L
