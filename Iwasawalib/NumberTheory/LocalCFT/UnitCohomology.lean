/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.UnitFiltration
public import Iwasawalib.GroupCohomology.CyclicTate

@[expose] public section

/-!
# The cohomology of the units of a complete valued field

Let `F` be a complete field with a valuation `v : F → ℤᵐ⁰`, let `𝒪 = {x | v x ≤ 1}` be its
valuation ring, and let a finite cyclic group `G = ⟨σ⟩` act on `𝒪` by valuation-preserving ring
automorphisms.  Suppose given

* a *`G`-fixed uniformizer* `π : 𝒪`, i.e. `v π = exp (-1)` and `g • π = π` for all `g`;
* a *residue map* `res : 𝒪 →+* k` onto a field `k`, surjective, `G`-equivariant, with kernel
  the maximal ideal `{x | v x < 1}`.

Then the Tate cohomology of `𝒪ˣ` vanishes as soon as it vanishes for the residue field, i.e.
as soon as `Ĥ*(G, kˣ) = 0` and `Ĥ*(G, k⁺) = 0`.  This is the classical computation
(Serre, *Corps Locaux*, ch. V): the graded pieces of the unit filtration
`𝒪ˣ ⊇ 1 + 𝔪 ⊇ 1 + 𝔪² ⊇ ⋯` are `kˣ` (at the bottom) and `k⁺` (higher up), and the
successive-approximation theorem of `Iwasawalib/GroupCohomology/CyclicLimit.lean` assembles
the graded vanishing into vanishing for `𝒪ˣ`.

Note where the hypothesis that `π` is `G`-fixed is used: it makes multiplication by `πⁿ` a
`G`-equivariant isomorphism `𝒪/𝔪 ≅ 𝔪ⁿ/𝔪ⁿ⁺¹`.  For the local extension `L_w / K_v` of a
number field this holds exactly when `w` is unramified over `v`, because then a uniformizer of
`K_v` is a uniformizer of `L_w`.

## Main definitions

* `LocalCFT.IsLocalData`: the bundle of hypotheses above.

## Main statements

* `LocalCFT.prod_one_add_sub_le`: `v (∏ (1 + xᵢ) - 1 - ∑ xᵢ) ≤ c²` when all `v xᵢ ≤ c ≤ 1`.
* `LocalCFT.IsLocalData.exists_smul_div_of_mulNorm_eq_one`: `Ĥ¹(G, 𝒪ˣ) = 0`.
* `LocalCFT.IsLocalData.exists_mulNorm_eq_of_smul_eq`: `Ĥ⁰(G, 𝒪ˣ) = 0`.
-/

noncomputable section

open Finset WithZero CyclicCocycle

namespace LocalCFT

variable {F : Type*} [Field F] [hv : Valued F ℤᵐ⁰]

/-! ## Two arithmetic lemmas about `ℤᵐ⁰` -/

theorem le_exp_neg_one_iff_lt_one {c : ℤᵐ⁰} : c ≤ exp (-1 : ℤ) ↔ c < 1 := by
  constructor
  · intro h
    refine lt_of_le_of_lt h ?_
    rw [show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm, exp_lt_exp]
    norm_num
  · intro h
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · obtain ⟨j, rfl⟩ : ∃ j : ℤ, c = exp j := ⟨log c, (exp_log hc).symm⟩
      rw [exp_le_exp]
      rw [show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm, exp_lt_exp] at h
      omega

theorem exp_neg_natCast_le_one (n : ℕ) : exp (-(n : ℤ)) ≤ (1 : ℤᵐ⁰) := by
  rw [show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm, exp_le_exp]
  omega

theorem exp_neg_mul_exp_neg_one (m : ℕ) :
    exp (-(m : ℤ)) * exp (-1 : ℤ) = exp (-((m + 1 : ℕ) : ℤ)) := by
  rw [← exp_add]
  congr 1
  push_cast
  ring

theorem exp_neg_sq_le {m : ℕ} (hm : 1 ≤ m) :
    exp (-(m : ℤ)) * exp (-(m : ℤ)) ≤ exp (-((m + 1 : ℕ) : ℤ)) := by
  rw [← exp_add, exp_le_exp]
  push_cast
  omega

/-! ## Expanding a product of principal units -/

/-- **The first-order expansion of a product.**  If all `v (x i) ≤ c ≤ 1`, then
`∏ (1 + x i) = 1 + ∑ x i` up to an error of valuation at most `c²`. -/
theorem prod_one_add_sub_le {ι : Type*} (s : Finset ι) (x : ι → F) {c : ℤᵐ⁰} (hc : c ≤ 1)
    (hx : ∀ i ∈ s, Valued.v (x i) ≤ c) :
    Valued.v ((∏ i ∈ s, (1 + x i)) - 1 - ∑ i ∈ s, x i) ≤ c * c := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    have hxj : Valued.v (x j) ≤ c := hx j (Finset.mem_insert_self j s)
    have hxs : ∀ i ∈ s, Valued.v (x i) ≤ c := fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)
    have hsum : Valued.v (∑ i ∈ s, x i) ≤ c := Valuation.map_sum_le _ hxs
    have hR := ih hxs
    set P : F := ∏ i ∈ s, (1 + x i) with hP
    set S : F := ∑ i ∈ s, x i with hS
    set R : F := P - 1 - S with hRdef
    have hPeq : P = 1 + S + R := by rw [hRdef]; ring
    have hnew : (∏ i ∈ insert j s, (1 + x i)) - 1 - ∑ i ∈ insert j s, x i
        = R + x j * (S + R) := by
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ← hP, ← hS, hPeq]
      ring
    rw [hnew]
    refine le_trans (Valuation.map_add _ _ _) (max_le hR ?_)
    rw [map_mul]
    refine mul_le_mul' hxj ?_
    exact le_trans (Valuation.map_add _ _ _)
      (max_le hsum (le_trans hR (mul_le_of_le_one_right' hc)))

/-! ## The local data -/

section Residue

variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G (integers (F := F))]
variable {k : Type*} [Field k] [MulSemiringAction G k]

attribute [local instance] Units.mulDistribMulActionRight

/-- **The local data of an unramified complete valued field.**  A `G`-fixed uniformizer `π`
together with a surjective `G`-equivariant residue map `res : 𝒪 → k` whose kernel is the
maximal ideal. -/
structure IsLocalData (res : integers (F := F) →+* k) (π : integers (F := F)) : Prop where
  /-- the action preserves the valuation -/
  valued_smul : ∀ (g : G) (a : integers (F := F)),
    Valued.v ((g • a : integers (F := F)) : F) = Valued.v ((a : integers (F := F)) : F)
  /-- the residue map is surjective -/
  res_surjective : Function.Surjective res
  /-- the kernel of the residue map is the maximal ideal -/
  res_eq_zero_iff : ∀ a : integers (F := F),
    res a = 0 ↔ Valued.v ((a : integers (F := F)) : F) < 1
  /-- the residue map is `G`-equivariant -/
  res_smul : ∀ (g : G) (a : integers (F := F)), res (g • a) = g • res a
  /-- `π` is a uniformizer -/
  valued_uniformizer : Valued.v ((π : integers (F := F)) : F) = exp (-1 : ℤ)
  /-- `π` is `G`-fixed -/
  smul_uniformizer : ∀ g : G, g • π = π

variable {res : integers (F := F) →+* k} {π : integers (F := F)}

namespace IsLocalData

variable (hd : IsLocalData (G := G) res π)

include hd

omit [Fintype G] in
theorem valued_eq_one_of_res_ne_zero {a : integers (F := F)} (ha : res a ≠ 0) :
    Valued.v ((a : integers (F := F)) : F) = 1 :=
  le_antisymm a.2 (not_lt.1 fun h ↦ ha ((hd.res_eq_zero_iff a).2 h))

omit [Fintype G] in
/-- Every unit of the residue field lifts to a unit of the valuation ring. -/
theorem exists_units_map_eq (y : kˣ) :
    ∃ z : (integers (F := F))ˣ, Units.map (res : integers (F := F) →* k) z = y := by
  obtain ⟨a, ha⟩ := hd.res_surjective (y : k)
  have hne : res a ≠ 0 := by rw [ha]; exact y.ne_zero
  have h1 : Valued.v ((a : integers (F := F)) : F) = 1 := hd.valued_eq_one_of_res_ne_zero hne
  refine ⟨unitOfValuedEqOne h1, Units.ext ?_⟩
  show res ((unitOfValuedEqOne h1 : integers (F := F))) = (y : k)
  rw [show (unitOfValuedEqOne h1 : integers (F := F)) = a from Subtype.ext rfl]
  exact ha

/-- The residue map intertwines the norms. -/
theorem map_mulNorm (u : (integers (F := F))ˣ) :
    Units.map (res : integers (F := F) →* k) (mulNorm (G := G) u)
      = mulNorm (G := G) (Units.map (res : integers (F := F) →* k) u) := by
  simp only [mulNorm_def, map_prod]
  exact Finset.prod_congr rfl fun g _ ↦ Units.ext (hd.res_smul g _)

omit [Fintype G] in
/-- **The first step of the filtration is the kernel of the residue map.** -/
theorem mem_unitFiltration_one_iff (u : (integers (F := F))ˣ) :
    u ∈ unitFiltration 1 ↔ Units.map (res : integers (F := F) →* k) u = 1 := by
  rw [mem_unitFiltration]
  have hcast : (((u : integers (F := F)) : F) - 1)
      = (((u : integers (F := F)) - 1 : integers (F := F)) : F) := by push_cast; ring
  rw [hcast, show (-((1 : ℕ) : ℤ)) = (-1 : ℤ) by norm_num, le_exp_neg_one_iff_lt_one,
    ← hd.res_eq_zero_iff, map_sub, map_one, sub_eq_zero]
  exact ⟨fun h ↦ Units.ext h, fun h ↦ congrArg Units.val h⟩


omit [Fintype G] in
theorem map_smul_units (g : G) (z : (integers (F := F))ˣ) :
    Units.map (res : integers (F := F) →* k) (g • z)
      = g • Units.map (res : integers (F := F) →* k) z :=
  Units.ext (hd.res_smul g _)

/-! ### Reductions to statements about differences -/

omit [Fintype G] hd in
theorem mem_unitFiltration_div (n : ℕ) (u z : (integers (F := F))ˣ)
    (h : Valued.v ((((u : integers (F := F)) - (z : integers (F := F))) : integers (F := F)) : F)
      ≤ exp (-(n : ℤ))) :
    u / z ∈ unitFiltration n := by
  rw [mem_unitFiltration, coe_units_div]
  have hz : ((z : integers (F := F)) : F) ≠ 0 := coe_units_ne_zero z
  have hsub : ((u : integers (F := F)) : F) / ((z : integers (F := F)) : F) - 1
      = (((u : integers (F := F)) : F) - ((z : integers (F := F)) : F))
        / ((z : integers (F := F)) : F) := by
    rw [sub_div, div_self hz]
  rw [hsub, map_div₀, valued_coe_units, div_one,
    show ((u : integers (F := F)) : F) - ((z : integers (F := F)) : F)
      = ((((u : integers (F := F)) - (z : integers (F := F))) : integers (F := F)) : F) from by
        push_cast; ring]
  exact h

omit [Fintype G] hd in
theorem mem_unitFiltration_mul_smul_div (n : ℕ) (u z : (integers (F := F))ˣ) (g : G)
    (h : Valued.v ((((u : integers (F := F)) * (g • (z : integers (F := F)))
        - (z : integers (F := F))) : integers (F := F)) : F) ≤ exp (-(n : ℤ))) :
    u * (g • z / z) ∈ unitFiltration n := by
  have hrw : u * (g • z / z) = (u * g • z) / z := by
    rw [mul_div_assoc]
  rw [hrw]
  exact mem_unitFiltration_div n (u * g • z) z h

/-! ### The coefficient of a principal unit -/

omit [Fintype G] in
theorem valued_pow_uniformizer (m : ℕ) :
    Valued.v (((π ^ m : integers (F := F)) : F)) = exp (-(m : ℤ)) := by
  push_cast
  rw [map_pow, hd.valued_uniformizer, ← exp_nsmul]
  congr 1
  simp

omit [Fintype G] in
theorem coe_pow_uniformizer_ne_zero (m : ℕ) : ((π ^ m : integers (F := F)) : F) ≠ 0 := by
  intro h
  have := hd.valued_pow_uniformizer (π := π) m
  rw [h, map_zero] at this
  exact exp_ne_zero this.symm

omit [Fintype G] in
/-- **An element of `U m` is `1 + πᵐ a`.** -/
theorem exists_coeff (m : ℕ) {u : (integers (F := F))ˣ} (hu : u ∈ unitFiltration m) :
    ∃ a : integers (F := F), (u : integers (F := F)) = 1 + π ^ m * a := by
  have hπ0 : ((π ^ m : integers (F := F)) : F) ≠ 0 := hd.coe_pow_uniformizer_ne_zero m
  rw [mem_unitFiltration] at hu
  have hcast : (((u : integers (F := F)) : F) - 1)
      = (((u : integers (F := F)) - 1 : integers (F := F)) : F) := by push_cast; ring
  rw [hcast] at hu
  set t : integers (F := F) := (u : integers (F := F)) - 1 with ht
  have hle : Valued.v ((t : F) / ((π ^ m : integers (F := F)) : F)) ≤ 1 := by
    rw [map_div₀, hd.valued_pow_uniformizer m]
    rw [div_le_one₀ (by simp)]
    simpa using hu
  refine ⟨⟨(t : F) / ((π ^ m : integers (F := F)) : F), hle⟩, ?_⟩
  refine Subtype.ext ?_
  have hπ0' : ((π : F)) ^ m ≠ 0 := by simpa using hπ0
  have htu : ((t : F)) = ((u : integers (F := F)) : F) - 1 := by rw [ht]; push_cast; ring
  push_cast
  rw [htu]
  field_simp
  ring

omit [Fintype G] in
/-- **`1 + πᵐ a` is a unit in `U m`** for `m ≥ 1`. -/
theorem exists_unit_one_add {m : ℕ} (hm : 1 ≤ m) (a : integers (F := F)) :
    ∃ z : (integers (F := F))ˣ, (z : integers (F := F)) = 1 + π ^ m * a ∧
      z ∈ unitFiltration m := by
  have hsplit : Valued.v (((π ^ m * a : integers (F := F)) : F))
      = exp (-(m : ℤ)) * Valued.v ((a : integers (F := F)) : F) := by
    rw [show ((π ^ m * a : integers (F := F)) : F)
        = ((π ^ m : integers (F := F)) : F) * ((a : integers (F := F)) : F) from by push_cast; ring,
      map_mul, hd.valued_pow_uniformizer m]
  have hle : Valued.v (((π ^ m * a : integers (F := F)) : F)) ≤ exp (-(m : ℤ)) := by
    rw [hsplit]
    exact mul_le_of_le_one_right' a.2
  have hlt : Valued.v (((π ^ m * a : integers (F := F)) : F)) < 1 := by
    refine lt_of_le_of_lt hle ?_
    rw [show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm, exp_lt_exp]
    omega
  have h1 : Valued.v (((1 + π ^ m * a : integers (F := F)) : F)) = 1 := by
    have hsub : (((1 + π ^ m * a : integers (F := F)) : F)) - 1
        = ((π ^ m * a : integers (F := F)) : F) := by push_cast; ring
    have := Valuation.map_eq_of_sub_lt (Valued.v (R := F)) (y := ((1 + π ^ m * a
      : integers (F := F)) : F)) (x := 1) (by rw [hsub, map_one]; exact hlt)
    rw [this, map_one]
  refine ⟨unitOfValuedEqOne h1, Subtype.ext rfl, ?_⟩
  rw [mem_unitFiltration]
  show Valued.v (((1 + π ^ m * a : integers (F := F)) : F) - 1) ≤ exp (-(m : ℤ))
  have hsub : (((1 + π ^ m * a : integers (F := F)) : F)) - 1
      = ((π ^ m * a : integers (F := F)) : F) := by push_cast; ring
  rw [hsub]
  exact hle

omit [Fintype G] in
theorem valued_le_of_res_eq_zero {a : integers (F := F)} (ha : res a = 0) :
    Valued.v ((a : integers (F := F)) : F) ≤ exp (-1 : ℤ) :=
  le_exp_neg_one_iff_lt_one.2 ((hd.res_eq_zero_iff a).1 ha)

theorem map_normHom (a : integers (F := F)) :
    res (CyclicTate.normHom G (integers (F := F)) a) = CyclicTate.normHom G k (res a) := by
  simp only [CyclicTate.normHom_apply, map_sum]
  exact Finset.sum_congr rfl fun g _ ↦ hd.res_smul g a

omit [Fintype G] in
theorem smul_one_add_pow_mul (g : G) (m : ℕ) (a : integers (F := F)) :
    g • (1 + π ^ m * a : integers (F := F)) = 1 + π ^ m * (g • a) := by
  rw [smul_add, smul_one, smul_mul', smul_pow', hd.smul_uniformizer]


omit [Fintype G] in
theorem valued_pow_mul (m : ℕ) (a : integers (F := F)) :
    Valued.v (((π ^ m * a : integers (F := F)) : F))
      = exp (-(m : ℤ)) * Valued.v ((a : integers (F := F)) : F) := by
  rw [show ((π ^ m * a : integers (F := F)) : F)
      = ((π ^ m : integers (F := F)) : F) * ((a : integers (F := F)) : F) from by push_cast; ring,
    map_mul, hd.valued_pow_uniformizer m]

/-! ### The graded vanishing at the bottom step -/

variable {σ : G}

/-- **`Ĥ¹` of the bottom graded piece `𝒪ˣ / (1 + 𝔪) ≅ kˣ`.** -/
theorem exists_smul_div_mem_one
    (hk : ∀ x : kˣ, mulNorm (G := G) x = 1 → ∃ y : kˣ, σ • y / y = x)
    (u : (integers (F := F))ˣ) (hnorm : mulNorm (G := G) u = 1) :
    ∃ z : (integers (F := F))ˣ, u * (σ • z / z) ∈ unitFiltration 1 := by
  have hn : mulNorm (G := G) (Units.map (res : integers (F := F) →* k) u)⁻¹ = 1 := by
    rw [CyclicLimit.mulNorm_inv, ← hd.map_mulNorm, hnorm, map_one, inv_one]
  obtain ⟨y, hy⟩ := hk _ hn
  obtain ⟨z, hz⟩ := hd.exists_units_map_eq y
  refine ⟨z, ?_⟩
  rw [hd.mem_unitFiltration_one_iff, map_mul, map_div, hd.map_smul_units, hz, hy]
  simp

/-- **`Ĥ⁰` of the bottom graded piece `𝒪ˣ / (1 + 𝔪) ≅ kˣ`.** -/
theorem exists_mulNorm_mem_one
    (hk : ∀ x : kˣ, σ • x = x → ∃ y : kˣ, mulNorm (G := G) y = x)
    (u : (integers (F := F))ˣ) (hu : σ • u = u) :
    ∃ z : (integers (F := F))ˣ, u / mulNorm (G := G) z ∈ unitFiltration 1 := by
  have hfix : σ • Units.map (res : integers (F := F) →* k) u
      = Units.map (res : integers (F := F) →* k) u := by
    rw [← hd.map_smul_units, hu]
  obtain ⟨y, hy⟩ := hk _ hfix
  obtain ⟨z, hz⟩ := hd.exists_units_map_eq y
  refine ⟨z, ?_⟩
  rw [hd.mem_unitFiltration_one_iff, map_div, hd.map_mulNorm, hz, hy]
  simp

/-! ### The graded vanishing at the higher steps -/

/-- **The norm of a principal unit to first order**: `N (1 + πᵐ a) = 1 + πᵐ Tr a` up to an
error of valuation at most `exp (-m)²`. -/
theorem valued_prod_sub (m : ℕ) (a : integers (F := F)) {z : (integers (F := F))ˣ}
    (hz : (z : integers (F := F)) = 1 + π ^ m * a) :
    Valued.v (((((mulNorm (G := G) z : (integers (F := F))ˣ) : integers (F := F))
      - 1 - π ^ m * CyclicTate.normHom G (integers (F := F)) a : integers (F := F))) : F)
      ≤ exp (-(m : ℤ)) * exp (-(m : ℤ)) := by
  classical
  have hcoe : ((mulNorm (G := G) z : (integers (F := F))ˣ) : integers (F := F))
      = ∏ g : G, (1 + π ^ m * (g • a)) := by
    rw [mulNorm_def, Units.coe_prod]
    refine Finset.prod_congr rfl fun g _ ↦ ?_
    rw [show ((g • z : (integers (F := F))ˣ) : integers (F := F))
      = g • (z : integers (F := F)) from rfl, hz, hd.smul_one_add_pow_mul g m a]
  have hxle : ∀ g : G,
      Valued.v (((π ^ m * (g • a) : integers (F := F)) : F)) ≤ exp (-(m : ℤ)) := by
    intro g
    rw [hd.valued_pow_mul]
    exact mul_le_of_le_one_right' (g • a).2
  have hval : ((((mulNorm (G := G) z : (integers (F := F))ˣ) : integers (F := F))
      - 1 - π ^ m * CyclicTate.normHom G (integers (F := F)) a : integers (F := F)) : F)
      = (∏ g : G, (1 + ((π ^ m * (g • a) : integers (F := F)) : F))) - 1
        - ∑ g : G, ((π ^ m * (g • a) : integers (F := F)) : F) := by
    rw [hcoe, CyclicTate.normHom_apply]
    push_cast
    rw [Finset.mul_sum]
  rw [hval]
  exact prod_one_add_sub_le _ _ (exp_neg_natCast_le_one m) fun g _ ↦ hxle g



/-- **`Ĥ¹` of the graded piece `(1 + 𝔪ᵐ)/(1 + 𝔪ᵐ⁺¹) ≅ k⁺`** for `m ≥ 1`. -/
theorem exists_smul_div_mem_succ
    (hk : ∀ x : k, CyclicTate.normHom G k x = 0 → ∃ y : k, σ • y - y = x)
    {m : ℕ} (hm : 1 ≤ m) {u : (integers (F := F))ˣ} (hu : u ∈ unitFiltration m)
    (hnorm : mulNorm (G := G) u = 1) :
    ∃ z ∈ unitFiltration m, u * (σ • z / z) ∈ unitFiltration (m + 1) := by
  obtain ⟨a, ha⟩ := hd.exists_coeff m hu
  -- the residue of the coefficient has trace zero
  have h1 : Valued.v (((π ^ m * CyclicTate.normHom G (integers (F := F)) a
      : integers (F := F))) : F) ≤ exp (-(m : ℤ)) * exp (-(m : ℤ)) := by
    have h := hd.valued_prod_sub m a ha
    rw [hnorm] at h
    rw [show (((1 : (integers (F := F))ˣ) : integers (F := F)) - 1
        - π ^ m * CyclicTate.normHom G (integers (F := F)) a : integers (F := F))
        = -(π ^ m * CyclicTate.normHom G (integers (F := F)) a) from by simp,
      show ((-(π ^ m * CyclicTate.normHom G (integers (F := F)) a) : integers (F := F)) : F)
        = -(((π ^ m * CyclicTate.normHom G (integers (F := F)) a : integers (F := F)) : F)) from by
          push_cast; ring, Valuation.map_neg] at h
    exact h
  have h2 : Valued.v ((CyclicTate.normHom G (integers (F := F)) a : integers (F := F)) : F)
      ≤ exp (-(m : ℤ)) := by
    rw [hd.valued_pow_mul] at h1
    exact le_of_mul_le_mul_left h1 (zero_lt_iff.2 exp_ne_zero)
  have h3 : res (CyclicTate.normHom G (integers (F := F)) a) = 0 := by
    rw [hd.res_eq_zero_iff]
    refine lt_of_le_of_lt h2 ?_
    rw [show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm, exp_lt_exp]
    omega
  have hnz : CyclicTate.normHom G k (res a) = 0 := by rw [← hd.map_normHom, h3]
  obtain ⟨bbar, hb⟩ := hk (-(res a)) (by rw [map_neg, hnz, neg_zero])
  obtain ⟨b, hbres⟩ := hd.res_surjective bbar
  obtain ⟨z, hzval, hzmem⟩ := hd.exists_unit_one_add hm b
  refine ⟨z, hzmem, mem_unitFiltration_mul_smul_div (m + 1) u z σ ?_⟩
  have hW : (u : integers (F := F)) * (σ • (z : integers (F := F))) - (z : integers (F := F))
      = π ^ m * (a + σ • b - b) + (π ^ m * a) * (π ^ m * (σ • b)) := by
    rw [ha, hzval, hd.smul_one_add_pow_mul σ m b]
    ring
  rw [hW, show ((π ^ m * (a + σ • b - b) + (π ^ m * a) * (π ^ m * (σ • b))
      : integers (F := F)) : F)
      = ((π ^ m * (a + σ • b - b) : integers (F := F)) : F)
        + (((π ^ m * a) * (π ^ m * (σ • b)) : integers (F := F)) : F) from by push_cast; ring]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
  · have hres0 : res (a + σ • b - b) = 0 := by
      rw [map_sub, map_add, hd.res_smul, hbres]
      linear_combination hb
    rw [hd.valued_pow_mul, ← exp_neg_mul_exp_neg_one m]
    exact mul_le_mul' le_rfl (hd.valued_le_of_res_eq_zero hres0)
  · rw [show (((π ^ m * a) * (π ^ m * (σ • b)) : integers (F := F)) : F)
        = ((π ^ m * a : integers (F := F)) : F) * ((π ^ m * (σ • b) : integers (F := F)) : F) from by
          push_cast; ring, map_mul]
    refine le_trans (mul_le_mul' ?_ ?_) (exp_neg_sq_le hm)
    · rw [hd.valued_pow_mul]; exact mul_le_of_le_one_right' a.2
    · rw [hd.valued_pow_mul]; exact mul_le_of_le_one_right' (σ • b).2

/-- **`Ĥ⁰` of the graded piece `(1 + 𝔪ᵐ)/(1 + 𝔪ᵐ⁺¹) ≅ k⁺`** for `m ≥ 1`. -/
theorem exists_mulNorm_mem_succ
    (hk : ∀ x : k, σ • x = x → ∃ y : k, CyclicTate.normHom G k y = x)
    {m : ℕ} (hm : 1 ≤ m) {u : (integers (F := F))ˣ} (hu : u ∈ unitFiltration m)
    (hfix : σ • u = u) :
    ∃ z ∈ unitFiltration m, u / mulNorm (G := G) z ∈ unitFiltration (m + 1) := by
  obtain ⟨a, ha⟩ := hd.exists_coeff m hu
  have hπ0 : (π : integers (F := F)) ^ m ≠ 0 := by
    intro h
    exact hd.coe_pow_uniformizer_ne_zero m (by rw [h]; simp)
  have hsa : σ • a = a := by
    have h1 : σ • (u : integers (F := F)) = (u : integers (F := F)) := by
      rw [show σ • (u : integers (F := F))
        = ((σ • u : (integers (F := F))ˣ) : integers (F := F)) from rfl, hfix]
    rw [ha, hd.smul_one_add_pow_mul σ m a] at h1
    exact mul_left_cancel₀ hπ0 (add_left_cancel h1)
  have hfixres : σ • res a = res a := by rw [← hd.res_smul, hsa]
  obtain ⟨bbar, hb⟩ := hk (res a) hfixres
  obtain ⟨b, hbres⟩ := hd.res_surjective bbar
  obtain ⟨z, hzval, hzmem⟩ := hd.exists_unit_one_add hm b
  refine ⟨z, hzmem, mem_unitFiltration_div (m + 1) u (mulNorm (G := G) z) ?_⟩
  have hsplit : (u : integers (F := F))
      - ((mulNorm (G := G) z : (integers (F := F))ˣ) : integers (F := F))
      = π ^ m * (a - CyclicTate.normHom G (integers (F := F)) b)
        - (((mulNorm (G := G) z : (integers (F := F))ˣ) : integers (F := F)) - 1
            - π ^ m * CyclicTate.normHom G (integers (F := F)) b) := by
    rw [ha]; ring
  rw [hsplit, show ((π ^ m * (a - CyclicTate.normHom G (integers (F := F)) b)
      - (((mulNorm (G := G) z : (integers (F := F))ˣ) : integers (F := F)) - 1
        - π ^ m * CyclicTate.normHom G (integers (F := F)) b) : integers (F := F)) : F)
      = ((π ^ m * (a - CyclicTate.normHom G (integers (F := F)) b) : integers (F := F)) : F)
        - (((((mulNorm (G := G) z : (integers (F := F))ˣ) : integers (F := F)) - 1
            - π ^ m * CyclicTate.normHom G (integers (F := F)) b : integers (F := F))) : F) from by
          push_cast; ring]
  refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
  · have hres0 : res (a - CyclicTate.normHom G (integers (F := F)) b) = 0 := by
      rw [map_sub, hd.map_normHom, hbres, hb, sub_self]
    rw [hd.valued_pow_mul, ← exp_neg_mul_exp_neg_one m]
    exact mul_le_mul' le_rfl (hd.valued_le_of_res_eq_zero hres0)
  · exact le_trans (hd.valued_prod_sub m b hzval) (exp_neg_sq_le hm)


/-! ### The vanishing theorems -/

section Vanishing

variable [CompleteSpace F]

/-- **`Ĥ¹(G, 𝒪ˣ) = 0`.**  If the residue field is cohomologically trivial, then so are the
units of the valuation ring of a complete valued field with a `G`-fixed uniformizer. -/
theorem exists_smul_div_of_mulNorm_eq_one
    (hk1 : ∀ x : kˣ, mulNorm (G := G) x = 1 → ∃ y : kˣ, σ • y / y = x)
    (hka : ∀ x : k, CyclicTate.normHom G k x = 0 → ∃ y : k, σ • y - y = x)
    {x : (integers (F := F))ˣ} (hx : mulNorm (G := G) x = 1) :
    ∃ y : (integers (F := F))ˣ, σ • y / y = x := by
  refine CyclicLimit.IsCompleteFiltration.exists_smul_div_of_mulNorm_eq_one
    (isCompleteFiltration_unitFiltration hd.valued_smul) (fun n u hu hun ↦ ?_) hx
  match n with
  | 0 =>
      obtain ⟨z, hz⟩ := hd.exists_smul_div_mem_one hk1 u hun
      exact ⟨z, by simp, hz⟩
  | (m + 1) => exact hd.exists_smul_div_mem_succ hka (Nat.le_add_left 1 m) hu hun

/-- **`Ĥ⁰(G, 𝒪ˣ) = 0`.**  Every `σ`-invariant unit of the valuation ring is a norm. -/
theorem exists_mulNorm_eq_of_smul_eq
    (hk1 : ∀ x : kˣ, σ • x = x → ∃ y : kˣ, mulNorm (G := G) y = x)
    (hka : ∀ x : k, σ • x = x → ∃ y : k, CyclicTate.normHom G k y = x)
    {x : (integers (F := F))ˣ} (hx : σ • x = x) :
    ∃ y : (integers (F := F))ˣ, mulNorm (G := G) y = x := by
  refine CyclicLimit.IsCompleteFiltration.exists_mulNorm_eq_of_smul_eq
    (isCompleteFiltration_unitFiltration hd.valued_smul) (fun n u hu hun ↦ ?_) hx
  match n with
  | 0 =>
      obtain ⟨z, hz⟩ := hd.exists_mulNorm_mem_one hk1 u hun
      exact ⟨z, by simp, hz⟩
  | (m + 1) => exact hd.exists_mulNorm_mem_succ hka (Nat.le_add_left 1 m) hu hun

/-- **Every multiplicative 1-cocycle with values in `𝒪ˣ` is a coboundary.** -/
theorem isMulCoboundary₁_of_isMulCocycle₁ (hg : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hk1 : ∀ x : kˣ, mulNorm (G := G) x = 1 → ∃ y : kˣ, σ • y / y = x)
    (hka : ∀ x : k, CyclicTate.normHom G k x = 0 → ∃ y : k, σ • y - y = x)
    {f : G → (integers (F := F))ˣ} (hf : groupCohomology.IsMulCocycle₁ f) :
    groupCohomology.IsMulCoboundary₁ f :=
  CyclicCocycle.isMulCoboundary₁_of_mulNorm hg
    (fun _ hx ↦ hd.exists_smul_div_of_mulNorm_eq_one hk1 hka hx) hf

end Vanishing

end IsLocalData

end Residue

end LocalCFT
