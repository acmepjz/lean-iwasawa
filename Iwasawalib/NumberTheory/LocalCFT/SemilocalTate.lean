/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.CyclicCocycleNorm
public import Iwasawalib.NumberTheory.LocalCFT.Unramified
public import Iwasawalib.GroupCohomology.UnramifiedIdele
public import Iwasawalib.NumberTheory.CFT.SIdeleSemilocal

@[expose] public section

/-!
# The Tate cohomology of the semilocal integral units at an unramified place

`Iwasawalib/NumberTheory/CFT/SIdeleHerbrand.lean` computes the Herbrand quotient of the finite
`S`-ideles in terms of the semilocal factors, *provided* that

`Ĥ⁰(Gal(L/K), (∏_{w ∣ v} O_w)^×) = Ĥ¹(Gal(L/K), (∏_{w ∣ v} O_w)^×) = 0`

for every finite place `v ∉ S`.  This is strictly stronger than the vanishing of the Herbrand
quotient of the individual factors: `S` is infinite, and an infinite product of modules with
Herbrand quotient `1` need not have vanishing Tate cohomology, so
`CyclicTate.herbrand_pi` is of no use.  What `CyclicTate.subsingleton_tateH0_mulPi` needs is
the *vanishing* at each factor, which is what this file supplies.

## Main statements

* `NumberField.subsingleton_tateH1_localProductIntegerUnits_of_forall`: `Ĥ¹ = 0`, from the cocycle
  statement `NumberField.exists_integral_trivialisation` and
  `CyclicCocycle.exists_smul_div_of_forall_isMulCocycle₁`.
* `NumberField.subsingleton_tateH0_localProductIntegerUnits_of_forall`: `Ĥ⁰ = 0`, from the local
  statement `NumberField.exists_mulNorm_eq_of_smul_eq_adicCompletionIntegers` at `w₀ ∣ v` and
  the explicit norm computation `NumberField.prod_smul_pointFun_apply`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CyclicCocycle WithZero
open scoped WithZero

attribute [local instance] NumberField.decompositionIntegersMulSemiringAction
  Units.mulDistribMulActionRight

namespace NumberField

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

variable (v : HeightOneSpectrum (𝓞 K))

/-- The coercion of the norm of a semilocal integral unit. -/
theorem coe_mulNorm_localProductIntegerUnits (x : localProductIntegerUnits K L v) :
    ((mulNorm (G := L ≃ₐ[K] L) x : localProductIntegerUnits K L v)
        : (LocalProduct K L v)ˣ)
      = mulNorm (G := L ≃ₐ[K] L) (x : (LocalProduct K L v)ˣ) := by
  rw [mulNorm_def, mulNorm_def]
  exact map_prod (localProductIntegerUnits K L v).subtype _ _

/-- **`Ĥ¹(Gal(L/K), (∏_{w ∣ v} O_w)^×) = 0` at an unramified place.**  A semilocal integral
unit of norm one is `σ • y / y` for a semilocal integral unit `y`: the element of norm one is
the value at `σ` of a 1-cocycle with integral values
(`CyclicCocycle.cocycleOfMulNorm`), and such a cocycle is trivialised inside the integral units
by `NumberField.exists_integral_trivialisation`. -/
theorem subsingleton_tateH1_localProductIntegerUnits_of_forall
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), w ∈ placesOver K L v →
      v.asIdeal.ramificationIdx' w.asIdeal = 1)
    {σ : L ≃ₐ[K] L} (hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ) :
    Subsingleton (CyclicTate.TateH1 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L v)) σ) := by
  rw [CyclicTate.tateH1_subsingleton_iff]
  intro x hx
  rw [LocalCFT.normHom_additive] at hx
  have hx' : mulNorm (G := L ≃ₐ[K] L)
      ((x.toMul : localProductIntegerUnits K L v) : (LocalProduct K L v)ˣ) = 1 := by
    rw [← coe_mulNorm_localProductIntegerUnits]
    exact congrArg (fun z : localProductIntegerUnits K L v ↦
      (z : (LocalProduct K L v)ˣ)) (Additive.ofMul.injective hx)
  obtain ⟨y, hyN, hy⟩ := exists_smul_div_of_forall_isMulCocycle₁ hσ
    (fun g u hu ↦ smul_mem_localProductIntegerUnits g hu)
    (fun f hf hint ↦ exists_integral_trivialisation v hv f hf hint)
    (x.toMul : localProductIntegerUnits K L v).2 hx'
  refine ⟨Additive.ofMul (⟨y, hyN⟩ : localProductIntegerUnits K L v), ?_⟩
  exact congrArg Additive.ofMul (Subtype.ext hy)


/-! ## `Ĥ⁰` of the semilocal integral units -/

section TateH0

variable {v}
variable {w₀ : HeightOneSpectrum (𝓞 L)} [Fintype (decompositionGroup K L w₀)]

open scoped Classical in
/-- The element of `∏_{w ∣ v} L_w` which is `z` at `w₀` and `1` at every other place.  It is
the image of `z` under the inclusion of the factor at `w₀`, and its `Gal(L/K)`-norm is the
unique `Gal(L/K)`-invariant element whose component at `w₀` is the `D_{w₀}`-norm of `z`. -/
def pointFun (hw₀ : w₀ ∈ placesOver K L v) (z : w₀.adicCompletion L) : LocalProduct K L v :=
  Pi.mulSingle (⟨w₀, hw₀⟩ : placesOver K L v) z

theorem pointFun_same (hw₀ : w₀ ∈ placesOver K L v) (z : w₀.adicCompletion L) :
    pointFun hw₀ z ⟨w₀, hw₀⟩ = z := by
  classical exact Pi.mulSingle_eq_same _ _

theorem pointFun_ne (hw₀ : w₀ ∈ placesOver K L v) (z : w₀.adicCompletion L)
    {w : placesOver K L v} (hw : w ≠ ⟨w₀, hw₀⟩) : pointFun hw₀ z w = 1 := by
  classical exact Pi.mulSingle_eq_of_ne hw _

theorem invSmulPlace_eq_base {w : placesOver K L v} {g : L ≃ₐ[K] L}
    (hw₀ : w₀ ∈ placesOver K L v) (hg : g • w₀ = (w : HeightOneSpectrum (𝓞 L))) :
    invSmulPlace g w = (⟨w₀, hw₀⟩ : placesOver K L v) :=
  Subtype.ext (by rw [invSmulPlace_coe, ← hg, inv_smul_smul])

theorem invSmulPlace_ne_base {w : placesOver K L v} {g : L ≃ₐ[K] L}
    (hw₀ : w₀ ∈ placesOver K L v) (hg : ¬ g • w₀ = (w : HeightOneSpectrum (𝓞 L))) :
    invSmulPlace g w ≠ (⟨w₀, hw₀⟩ : placesOver K L v) := by
  intro h
  apply hg
  have hc : (invSmulPlace g w : HeightOneSpectrum (𝓞 L)) = w₀ := congrArg Subtype.val h
  rw [invSmulPlace_coe] at hc
  rw [← hc, smul_inv_smul]

/-- Off the fibre of `w₀` the translate of `pointFun` has trivial component. -/
theorem smul_pointFun_apply_eq_one (hw₀ : w₀ ∈ placesOver K L v) (z : w₀.adicCompletion L)
    {w : placesOver K L v} {g : L ≃ₐ[K] L} (hg : ¬ g • w₀ = (w : HeightOneSpectrum (𝓞 L))) :
    (g • pointFun hw₀ z) w = 1 := by
  rw [localProduct_smul_apply, pointFun_ne hw₀ z (invSmulPlace_ne_base hw₀ hg), map_one]


/-- **At the base place the decomposition group acts by the local action.** -/
theorem localProduct_smul_apply_base (hw₀ : w₀ ∈ placesOver K L v)
    (d : decompositionGroup K L w₀) (y : LocalProduct K L v) :
    ((d : L ≃ₐ[K] L) • y) (⟨w₀, hw₀⟩ : placesOver K L v) = d • (y ⟨w₀, hw₀⟩) := by
  rw [localProduct_smul_apply]
  refine (adicCompletionCongr_index_congr' Subtype.val
    (invSmulPlace_eq_base hw₀ (mem_decompositionGroup.1 d.2)) w₀
    (((d : L ≃ₐ[K] L) : L ≃+* L)) _ (valuation_of_mem_decompositionGroup d) y).trans ?_
  rw [decomposition_smul_def, decompositionRingAut_apply]

/-- **The component at `w` of `g₀ • y`, for `g₀` carrying `w₀` to `w`.** -/
theorem localProduct_smul_apply_of_smul_eq (hw₀ : w₀ ∈ placesOver K L v)
    (y : LocalProduct K L v) (w : placesOver K L v) {g₀ : L ≃ₐ[K] L}
    (hg₀ : g₀ • w₀ = (w : HeightOneSpectrum (𝓞 L)))
    (hval : ∀ t : L, (w : HeightOneSpectrum (𝓞 L)).valuation L (g₀ t) = w₀.valuation L t) :
    (g₀ • y) w = adicCompletionCongr ((g₀ : L ≃ₐ[K] L) : L ≃+* L) w₀
      (w : HeightOneSpectrum (𝓞 L)) hval (y (⟨w₀, hw₀⟩ : placesOver K L v)) := by
  rw [localProduct_smul_apply]
  exact adicCompletionCongr_index_congr' Subtype.val (invSmulPlace_eq_base hw₀ hg₀)
    (w : HeightOneSpectrum (𝓞 L)) (((g₀ : L ≃ₐ[K] L) : L ≃+* L)) _ hval y

/-- At the base place, the `D_{w₀}`-translate of `pointFun` is the local translate. -/
theorem smul_pointFun_apply_base (hw₀ : w₀ ∈ placesOver K L v) (z : w₀.adicCompletion L)
    (d : decompositionGroup K L w₀) :
    ((d : L ≃ₐ[K] L) • pointFun hw₀ z) (⟨w₀, hw₀⟩ : placesOver K L v) = d • z := by
  rw [localProduct_smul_apply_base hw₀ d (pointFun hw₀ z), pointFun_same]

/-- **The component at `w` of the `Gal(L/K)`-norm of `pointFun hw₀ z`** is the `D_{w₀}`-norm of
`z`, transported to `w` by any `g₀` carrying `w₀` to `w`.  Only the `#D_{w₀}` automorphisms
carrying `w₀` to `w` contribute to the product, and they are the coset `g₀ D_{w₀}`. -/
theorem prod_smul_pointFun_apply (hw₀ : w₀ ∈ placesOver K L v) (z : w₀.adicCompletion L)
    (w : placesOver K L v) {g₀ : L ≃ₐ[K] L} (hg₀ : g₀ • w₀ = (w : HeightOneSpectrum (𝓞 L)))
    (hval : ∀ y : L, (w : HeightOneSpectrum (𝓞 L)).valuation L (g₀ y) = w₀.valuation L y) :
    ∏ g : L ≃ₐ[K] L, (g • pointFun hw₀ z) w
      = adicCompletionCongr ((g₀ : L ≃ₐ[K] L) : L ≃+* L) w₀ (w : HeightOneSpectrum (𝓞 L)) hval
          (∏ d : decompositionGroup K L w₀, d • z) := by
  classical
  set T : Finset (L ≃ₐ[K] L) :=
    {g : L ≃ₐ[K] L | g • w₀ = (w : HeightOneSpectrum (𝓞 L))} with hT
  have hmemT : ∀ g : L ≃ₐ[K] L, g ∈ T ↔ g • w₀ = (w : HeightOneSpectrum (𝓞 L)) := by
    intro g; rw [hT]; simp
  have h1 : ∏ g : L ≃ₐ[K] L, (g • pointFun hw₀ z) w = ∏ g ∈ T, (g • pointFun hw₀ z) w := by
    refine (Finset.prod_subset (Finset.subset_univ T) ?_).symm
    intro g _ hgT
    exact smul_pointFun_apply_eq_one hw₀ z (fun h ↦ hgT ((hmemT g).2 h))
  have h2 : ∏ g ∈ T, (g • pointFun hw₀ z) w
      = ∏ d : decompositionGroup K L w₀, ((g₀ * (d : L ≃ₐ[K] L)) • pointFun hw₀ z) w := by
    refine (Finset.prod_bij (fun (d : decompositionGroup K L w₀) _ ↦ g₀ * (d : L ≃ₐ[K] L))
      ?_ ?_ ?_ ?_).symm
    · intro d _
      refine (hmemT _).2 ?_
      rw [mul_smul, mem_decompositionGroup.1 d.2, hg₀]
    · intro d _ d' _ h
      exact Subtype.ext (mul_left_cancel h)
    · intro g hg
      refine ⟨⟨g₀⁻¹ * g, ?_⟩, Finset.mem_univ _, by group⟩
      rw [mem_decompositionGroup, mul_smul, (hmemT g).1 hg, ← hg₀, inv_smul_smul]
    · intro d _; rfl
  have h3 : ∀ d : decompositionGroup K L w₀,
      ((g₀ * (d : L ≃ₐ[K] L)) • pointFun hw₀ z) w
        = adicCompletionCongr ((g₀ : L ≃ₐ[K] L) : L ≃+* L) w₀ (w : HeightOneSpectrum (𝓞 L))
            hval (d • z) := by
    intro d
    rw [mul_smul, localProduct_smul_apply_of_smul_eq hw₀ _ w hg₀ hval,
      smul_pointFun_apply_base hw₀ z d]
  rw [h1, h2, Finset.prod_congr rfl (fun d _ ↦ h3 d), ← map_prod]


/-! ### The integral unit supported at one place -/

theorem pointFun_mul (hw₀ : w₀ ∈ placesOver K L v) (a b : w₀.adicCompletion L) :
    pointFun hw₀ (a * b) = pointFun hw₀ a * pointFun hw₀ b := by
  classical exact Pi.mulSingle_mul _ _ _

theorem pointFun_one (hw₀ : w₀ ∈ placesOver K L v) :
    pointFun hw₀ (1 : w₀.adicCompletion L) = 1 := by
  classical exact Pi.mulSingle_one _

/-- The unit of `∏_{w ∣ v} L_w` which is `z` at `w₀` and `1` at every other place. -/
def pointUnit (hw₀ : w₀ ∈ placesOver K L v) (z : (w₀.adicCompletion L)ˣ) :
    (LocalProduct K L v)ˣ where
  val := pointFun hw₀ (z : w₀.adicCompletion L)
  inv := pointFun hw₀ ((z⁻¹ : (w₀.adicCompletion L)ˣ) : w₀.adicCompletion L)
  val_inv := by
    rw [← pointFun_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, pointFun_one]
  inv_val := by
    rw [← pointFun_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, pointFun_one]

@[simp] theorem coe_pointUnit (hw₀ : w₀ ∈ placesOver K L v) (z : (w₀.adicCompletion L)ˣ) :
    ((pointUnit hw₀ z : (LocalProduct K L v)ˣ) : LocalProduct K L v)
      = pointFun hw₀ (z : w₀.adicCompletion L) := rfl

/-- `pointUnit` of a unit of valuation one is a semilocal *integral* unit. -/
theorem pointUnit_mem_localProductIntegerUnits (hw₀ : w₀ ∈ placesOver K L v)
    (z : (w₀.adicCompletion L)ˣ) (hz : (Valued.v (z : w₀.adicCompletion L) : ℤᵐ⁰) = 1) :
    pointUnit hw₀ z ∈ localProductIntegerUnits K L v := by
  classical
  refine mem_localProductIntegerUnits_of_valued_eq_one fun w ↦ ?_
  rw [coe_pointUnit]
  by_cases h : w = (⟨w₀, hw₀⟩ : placesOver K L v)
  · subst h; rw [pointFun_same]; exact hz
  · rw [pointFun_ne hw₀ _ h, map_one]

/-- The coordinatewise form of the `Gal(L/K)`-norm of a semilocal unit. -/
theorem coe_mulNorm_apply (y : (LocalProduct K L v)ˣ) (w : placesOver K L v) :
    ((mulNorm (G := L ≃ₐ[K] L) y : (LocalProduct K L v)ˣ) : LocalProduct K L v) w
      = ∏ g : L ≃ₐ[K] L, (g • (y : LocalProduct K L v)) w := by
  rw [mulNorm_def, show ((∏ g : L ≃ₐ[K] L, g • y : (LocalProduct K L v)ˣ) : LocalProduct K L v)
      = ∏ g : L ≃ₐ[K] L, ((g • y : (LocalProduct K L v)ˣ) : LocalProduct K L v) from
    map_prod (Units.coeHom (LocalProduct K L v)) _ _]
  exact Finset.prod_apply w _ _


/-! ### `Ĥ⁰` vanishes -/

/-- **`Ĥ⁰(Gal(L/K), (∏_{w ∣ v} O_w)^×) = 0` at an unramified place.**

A `Gal(L/K)`-invariant semilocal integral unit `U` is the norm of the integral unit supported
at a single place `w₀ ∣ v` whose value there is a `D_{w₀}`-norm of the component `U_{w₀}` —
which exists by `NumberField.exists_mulNorm_eq_of_smul_eq_adicCompletionIntegers`, the
unramified local statement.  Only the coset `g₀ D_{w₀}` contributes to the component at `w`
of the global norm (`NumberField.prod_smul_pointFun_apply`), and an invariant element is
determined by its component at `w₀`. -/
theorem subsingleton_tateH0_localProductIntegerUnits_of_forall (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), w ∈ placesOver K L v →
      v.asIdeal.ramificationIdx' w.asIdeal = 1)
    {σ : L ≃ₐ[K] L} (hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ) :
    Subsingleton (CyclicTate.TateH0 (L ≃ₐ[K] L)
      (Additive (localProductIntegerUnits K L v)) σ) := by
  classical
  haveI : IsCyclic (L ≃ₐ[K] L) := ⟨⟨σ, hσ⟩⟩
  rw [CyclicTate.tateH0_subsingleton_iff]
  intro X hX
  have hX' : σ • (X.toMul : localProductIntegerUnits K L v) = X.toMul := hX
  set U : (LocalProduct K L v)ˣ :=
    ((X.toMul : localProductIntegerUnits K L v) : (LocalProduct K L v)ˣ) with hUdef
  have hUmem : U ∈ localProductIntegerUnits K L v :=
    (X.toMul : localProductIntegerUnits K L v).2
  have hσU : σ • U = U :=
    congrArg (fun t : localProductIntegerUnits K L v ↦ (t : (LocalProduct K L v)ˣ)) hX'
  have hfix : ∀ g : L ≃ₐ[K] L, g • U = U := by
    have hpow : ∀ k : ℕ, (σ ^ k) • U = U := by
      intro k
      induction k with
      | zero => rw [pow_zero, one_smul]
      | succ k ih => rw [pow_succ, mul_smul, hσU, ih]
    intro g
    obtain ⟨k, rfl⟩ := CyclicCocycle.exists_pow_eq hσ g
    exact hpow k
  obtain ⟨w₀, hw₀⟩ := nonempty_placesOver (K := K) (L := L) v
  haveI : Fintype (decompositionGroup K L w₀) := Fintype.ofFinite _
  haveI : w₀.asIdeal.LiesOver v.asIdeal := ⟨(mem_placesOver.1 hw₀).symm⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := decompositionGroup K L w₀)
  set X₀ : w₀.adicCompletion L := (U : LocalProduct K L v) ⟨w₀, hw₀⟩ with hX₀def
  have hX₀v : (Valued.v X₀ : ℤᵐ⁰) = 1 :=
    valued_eq_one_of_mem_localProductIntegerUnits hUmem ⟨w₀, hw₀⟩
  have hτX₀ : τ • X₀ = X₀ := by
    have h := congrArg (fun t : (LocalProduct K L v)ˣ ↦ (t : LocalProduct K L v))
      (hfix (τ : L ≃ₐ[K] L))
    have h' : ((τ : L ≃ₐ[K] L) • (U : LocalProduct K L v)) (⟨w₀, hw₀⟩ : placesOver K L v)
        = X₀ := congrFun h (⟨w₀, hw₀⟩ : placesOver K L v)
    rwa [localProduct_smul_apply_base hw₀ τ (U : LocalProduct K L v)] at h'
  set a : (LocalCFT.integers (F := w₀.adicCompletion L))ˣ :=
    LocalCFT.unitOfValuedEqOne hX₀v with hadef
  have hτa : τ • a = a := Units.ext (Subtype.ext hτX₀)
  obtain ⟨b, hb⟩ :=
    exists_mulNorm_eq_of_smul_eq_adicCompletionIntegers v w₀ (hv w₀ hw₀) hτ hτa
  set zU : (w₀.adicCompletion L)ˣ :=
    Units.map (LocalCFT.integers (F := w₀.adicCompletion L)).subtype.toMonoidHom b with hzUdef
  have hzUv : (Valued.v (zU : w₀.adicCompletion L) : ℤᵐ⁰) = 1 := LocalCFT.valued_coe_units b
  -- the `D_{w₀}`-norm of `zU` is the component of `U` at `w₀`
  have hprod : (∏ d : decompositionGroup K L w₀, d • (zU : w₀.adicCompletion L)) = X₀ := by
    have h := congrArg (fun t : (LocalCFT.integers (F := w₀.adicCompletion L))ˣ ↦
      ((t : LocalCFT.integers (F := w₀.adicCompletion L)) : w₀.adicCompletion L)) hb
    rw [mulNorm_def] at h
    refine Eq.trans ?_ h
    exact (map_prod ((LocalCFT.integers (F := w₀.adicCompletion L)).subtype.toMonoidHom.comp
      (Units.coeHom (LocalCFT.integers (F := w₀.adicCompletion L))))
      (fun d : decompositionGroup K L w₀ ↦ d • b) Finset.univ).symm
  refine ⟨Additive.ofMul (⟨pointUnit hw₀ zU,
    pointUnit_mem_localProductIntegerUnits hw₀ zU hzUv⟩ : localProductIntegerUnits K L v), ?_⟩
  rw [LocalCFT.normHom_additive]
  refine congrArg Additive.ofMul (Subtype.ext ?_)
  rw [coe_mulNorm_localProductIntegerUnits]
  refine Units.ext (funext fun w ↦ ?_)
  rw [coe_mulNorm_apply]
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq_of_mem_placesOver hw₀ w
  have hval : ∀ t : L, (w : HeightOneSpectrum (𝓞 L)).valuation L (g₀ t) = w₀.valuation L t := by
    intro t
    rw [← hg₀]
    exact valuation_smul_heightOneSpectrum g₀ w₀ t
  have hRHS : (U : LocalProduct K L v) w
      = adicCompletionCongr ((g₀ : L ≃ₐ[K] L) : L ≃+* L) w₀
          (w : HeightOneSpectrum (𝓞 L)) hval X₀ := by
    conv_lhs => rw [← hfix g₀]
    exact localProduct_smul_apply_of_smul_eq hw₀ (U : LocalProduct K L v) w hg₀ hval
  show ∏ g : L ≃ₐ[K] L, (g • pointFun hw₀ (zU : w₀.adicCompletion L)) w
      = (U : LocalProduct K L v) w
  rw [prod_smul_pointFun_apply hw₀ _ w hg₀ hval, hprod, hRHS]

end TateH0

end NumberField
