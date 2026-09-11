/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.Induced

@[expose] public section

/-!
# A transitive equivariant family of rings is an induced module

Let `G` be a group acting **transitively** on a type `Ω`, and let `M : Ω → Type` be a family of
rings on which `G` acts compatibly: for every `σ : G` and `w : Ω` an isomorphism
`M w ≃+* M (σ • w)`, functorially in `σ`.  Then for any `w₀ : Ω` with stabiliser
`H = Stab_G(w₀)`,

`∏_{w : Ω} M w  ≃  Ind_H^G (M w₀)`,

`G`-equivariantly.  This is the abstract form of "the local factor `∏_{w ∣ v} L_w` of the
adeles is an induced module for the decomposition group", and it is what makes Shapiro's lemma
applicable to the local factors at both the finite and the infinite places.

## Implementation notes

The compatible family is packaged as `EquivariantFamily G Ω M`, whose data is a map

`push σ (h : σ • w = w') : M w ≃+* M w'`

*indexed by a proof that `σ` carries `w` to `w'`* rather than as a map `M w ≃+* M (σ • w)`.
The two are equivalent (take `h := rfl`), but the present form is what avoids all transport of
elements along equalities of indices: every composite that occurs is again of the same shape,
with a different proof, and proofs are irrelevant.  The only two places where an equality of
indices is used are `EquivariantFamily.push_index_congr` and
`EquivariantFamily.push_group_congr`, both proved by `subst`.

The derived `G`-action on `∏ w, M w` and `H`-action on `M w₀` are *not* declared as instances,
since they depend on the data `F : EquivariantFamily G Ω M`; the results are stated for
arbitrary actions satisfying the two compatibility equations `hpi` and `hstab`, which in any
application hold by `rfl` for the actions constructed here.

## Main definitions

* `EquivariantFamily G Ω M`: the compatible family.
* `EquivariantFamily.piMulSemiringAction`: the `G`-action on `∏ w, M w`.
* `EquivariantFamily.stabilizerMulSemiringAction`: the `Stab_G(w₀)`-action on `M w₀`.
* `EquivariantFamily.equivRcoind`: the `G`-equivariant ring isomorphism
  `∏ w, M w ≃+* Ind_{Stab_G(w₀)}^G (M w₀)`.
-/

noncomputable section

open MulAction

/-- A family of rings `M : Ω → Type*` over a `G`-set `Ω`, together with compatible
isomorphisms `M w ≃+* M w'` for every `σ : G` carrying `w` to `w'`. -/
structure EquivariantFamily (G : Type*) [Group G] (Ω : Type*) [MulAction G Ω]
    (M : Ω → Type*) [∀ w, CommRing (M w)] where
  /-- The isomorphism `M w ≃+* M w'` attached to an element `σ` carrying `w` to `w'`. -/
  push {w w' : Ω} (σ : G) (h : σ • w = w') : M w ≃+* M w'
  /-- The identity acts as the identity. -/
  push_one {w : Ω} (h : (1 : G) • w = w) (z : M w) : push 1 h z = z
  /-- The maps compose. -/
  push_mul {w w' w'' : Ω} (σ τ : G) (h : τ • w = w') (h' : σ • w' = w'')
    (h'' : (σ * τ) • w = w'') (z : M w) : push σ h' (push τ h z) = push (σ * τ) h'' z

namespace EquivariantFamily

variable {G Ω : Type*} [Group G] [MulAction G Ω] {M : Ω → Type*} [∀ w, CommRing (M w)]
  (F : EquivariantFamily G Ω M)

/-- Transporting the source index of `push` along an equality of indices. -/
theorem push_index_congr {w₁ w₂ w' : Ω} (p : w₁ = w₂) (σ : G) (h₁ : σ • w₁ = w')
    (h₂ : σ • w₂ = w') (x : ∀ w, M w) : F.push σ h₁ (x w₁) = F.push σ h₂ (x w₂) := by
  subst p; rfl

/-- `push` depends only on the underlying group element, not on the proof. -/
theorem push_group_congr {w w' : Ω} {σ σ' : G} (p : σ = σ') (h : σ • w = w')
    (h' : σ' • w = w') (z : M w) : F.push σ h z = F.push σ' h' z := by
  subst p; rfl

/-! ## The action on the product -/

/-- The `G`-action on `∏ w, M w` permuting the factors: `(σ • x) w = push σ (x (σ⁻¹ • w))`. -/
@[instance_reducible]
def piMulSemiringAction : MulSemiringAction G (∀ w : Ω, M w) where
  smul σ x := fun w ↦ F.push σ (smul_inv_smul σ w) (x (σ⁻¹ • w))
  one_smul x := funext fun w ↦ by
    refine (F.push_index_congr (show (1 : G)⁻¹ • w = w by rw [inv_one, one_smul]) 1 _
      (one_smul G w) x).trans ?_
    exact F.push_one _ _
  mul_smul σ τ x := funext fun w ↦ by
    show F.push (σ * τ) (smul_inv_smul (σ * τ) w) (x ((σ * τ)⁻¹ • w))
      = F.push σ (smul_inv_smul σ w) (F.push τ (smul_inv_smul τ (σ⁻¹ • w)) (x (τ⁻¹ • σ⁻¹ • w)))
    rw [F.push_mul σ τ (smul_inv_smul τ (σ⁻¹ • w)) (smul_inv_smul σ w)
      (show (σ * τ) • (τ⁻¹ • σ⁻¹ • w) = w by rw [mul_smul, smul_inv_smul, smul_inv_smul])]
    exact F.push_index_congr (by rw [mul_inv_rev, mul_smul]) (σ * τ) _ _ x
  smul_zero σ := funext fun w ↦ map_zero _
  smul_add σ x y := funext fun w ↦ map_add _ _ _
  smul_one σ := funext fun w ↦ map_one _
  smul_mul σ x y := funext fun w ↦ map_mul _ _ _

/-! ## The action of the stabiliser on one factor -/

variable (w₀ : Ω)

/-- The action of the stabiliser of `w₀` on the factor `M w₀`. -/
@[instance_reducible]
def stabilizerMulSemiringAction : MulSemiringAction (stabilizer G w₀) (M w₀) where
  smul d z := F.push (d : G) (mem_stabilizer_iff.1 d.2) z
  one_smul z := F.push_one _ z
  mul_smul d d' z := by
    show F.push ((d * d' : stabilizer G w₀) : G) _ z
      = F.push (d : G) _ (F.push (d' : G) _ z)
    exact (F.push_mul (d : G) (d' : G) _ _ _ z).symm
  smul_zero d := map_zero _
  smul_add d z z' := map_add _ _ _
  smul_one d := map_one _
  smul_mul d z z' := map_mul _ _ _

/-! ## The product is the induced module -/

section Rcoind

variable {w₀}
variable [MulSemiringAction G (∀ w : Ω, M w)] [MulSemiringAction (stabilizer G w₀) (M w₀)]

/-- The compatibility of a given `G`-action on `∏ w, M w` with the family. -/
abbrev IsPiAction : Prop :=
  ∀ (σ : G) (x : ∀ w : Ω, M w) (w : Ω), (σ • x) w = F.push σ (smul_inv_smul σ w) (x (σ⁻¹ • w))

/-- The compatibility of a given action of the stabiliser on `M w₀` with the family. -/
abbrev IsStabilizerAction : Prop :=
  ∀ (d : stabilizer G w₀) (z : M w₀), d • z = F.push (d : G) (mem_stabilizer_iff.1 d.2) z

variable (hstab : F.IsStabilizerAction (w₀ := w₀))

theorem _root_.MulAction.smul_inv_stabilizer (d : stabilizer G w₀) : ((d : G))⁻¹ • w₀ = w₀ := by
  rw [inv_smul_eq_iff]
  exact (mem_stabilizer_iff.1 d.2).symm

/-- The underlying function of the map `∏ w, M w → Ind_{Stab(w₀)}^G (M w₀)`. -/
def toRcoindFun (x : ∀ w : Ω, M w) : G → M w₀ :=
  fun g ↦ F.push g⁻¹ (inv_smul_smul g w₀) (x (g • w₀))

omit [MulSemiringAction G (∀ w : Ω, M w)] [MulSemiringAction (stabilizer G w₀) (M w₀)] in
theorem toRcoindFun_apply (x : ∀ w : Ω, M w) (g : G) :
    F.toRcoindFun (w₀ := w₀) x g = F.push g⁻¹ (inv_smul_smul g w₀) (x (g • w₀)) := rfl

omit [MulSemiringAction G (∀ w : Ω, M w)] in
include hstab in
theorem toRcoindFun_mem (x : ∀ w : Ω, M w) :
    F.toRcoindFun (w₀ := w₀) x ∈ Subring.rcoind (stabilizer G w₀) (M w₀) := by
  intro g d
  have hd : (d : G) • w₀ = w₀ := mem_stabilizer_iff.1 d.2
  have hgd : (g * (d : G)) • w₀ = g • w₀ := by rw [mul_smul, hd]
  have hdinv : ((d : G))⁻¹ • w₀ = w₀ := MulAction.smul_inv_stabilizer d
  rw [toRcoindFun_apply, toRcoindFun_apply, hstab]
  refine (F.push_index_congr hgd (g * (d : G))⁻¹ _ (by rw [mul_inv_rev, mul_smul,
    inv_smul_smul, hdinv]) x).trans ?_
  refine ((F.push_mul ((d⁻¹ : stabilizer G w₀) : G) g⁻¹ (inv_smul_smul g w₀)
    (by rw [Subgroup.coe_inv]; exact hdinv) (by
      rw [mul_smul, inv_smul_smul, Subgroup.coe_inv, hdinv]) (x (g • w₀))).trans ?_).symm
  exact F.push_group_congr (by rw [Subgroup.coe_inv, ← mul_inv_rev]) _ _ _

include hstab in
/-- The ring homomorphism `∏ w, M w → Ind_{Stab(w₀)}^G (M w₀)`. -/
def toRcoind : (∀ w : Ω, M w) →+* Subring.rcoind (stabilizer G w₀) (M w₀) where
  toFun x := ⟨F.toRcoindFun x, F.toRcoindFun_mem hstab x⟩
  map_one' := Subtype.ext (funext fun _ ↦ map_one _)
  map_mul' _ _ := Subtype.ext (funext fun _ ↦ map_mul _ _ _)
  map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _)

omit [MulSemiringAction G (∀ w : Ω, M w)] in
@[simp]
theorem toRcoind_coe (x : ∀ w : Ω, M w) :
    ((F.toRcoind hstab x : Subring.rcoind (stabilizer G w₀) (M w₀)) : G → M w₀)
      = F.toRcoindFun x := rfl

/-- The map to the induced module is `G`-equivariant. -/
theorem toRcoind_smul (hpi : F.IsPiAction) (σ : G) (x : ∀ w : Ω, M w) :
    F.toRcoind hstab (σ • x) = σ • F.toRcoind hstab x := by
  refine Subtype.ext (funext fun g ↦ ?_)
  rw [toRcoind_coe, Subring.rcoind_smul_apply, toRcoind_coe, toRcoindFun_apply,
    toRcoindFun_apply, hpi]
  refine (F.push_mul g⁻¹ σ (smul_inv_smul σ (g • w₀)) (inv_smul_smul g w₀)
    (by rw [mul_smul, smul_inv_smul, inv_smul_smul]) _).trans ?_
  refine (F.push_group_congr (show g⁻¹ * σ = (σ⁻¹ * g)⁻¹ by rw [mul_inv_rev, inv_inv]) _
    (by rw [mul_inv_rev, inv_inv, mul_smul, smul_inv_smul, inv_smul_smul]) _).trans ?_
  exact F.push_index_congr (by rw [mul_smul]) _ _ _ x

/-! ### The inverse -/

variable [IsPretransitive G Ω]

variable (G w₀) in
/-- A choice of element of `G` carrying the base point `w₀` to a given point of a transitive
`G`-set. -/
def witness (w : Ω) : G := (exists_smul_eq G w₀ w).choose

variable (G w₀) in
theorem witness_spec (w : Ω) : witness G w₀ w • w₀ = w := (exists_smul_eq G w₀ w).choose_spec

omit [MulSemiringAction G (∀ w : Ω, M w)] [IsPretransitive G Ω] in
include hstab in
/-- The value `push g (Fn g)` does not depend on the choice of `g` carrying `w₀` to `w`. -/
theorem rcoind_apply_congr (Fn : Subring.rcoind (stabilizer G w₀) (M w₀)) {g g' : G} {w : Ω}
    (hg : g • w₀ = w) (hg' : g' • w₀ = w) :
    F.push g hg ((Fn : G → M w₀) g) = F.push g' hg' ((Fn : G → M w₀) g') := by
  have hd : (g⁻¹ * g') • w₀ = w₀ := by rw [mul_smul, hg', ← hg, inv_smul_smul]
  set d : stabilizer G w₀ := ⟨g⁻¹ * g', mem_stabilizer_iff.2 hd⟩ with hddef
  have hdinv : ((d : G))⁻¹ • w₀ = w₀ := MulAction.smul_inv_stabilizer d
  have hgd : g * (d : G) = g' := by
    show g * (g⁻¹ * g') = g'
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hFn : (Fn : G → M w₀) g' = F.push ((d : G))⁻¹ hdinv ((Fn : G → M w₀) g) := by
    conv_lhs => rw [← hgd]
    rw [Fn.2 g d, hstab]
    exact F.push_group_congr (by simp : ((d⁻¹ : stabilizer G w₀) : G) = ((d : G))⁻¹) _ _ _
  rw [hFn]
  refine ((F.push_mul g' ((d : G))⁻¹ hdinv hg' (by
    rw [mul_smul, hdinv, hg']) _).trans ?_).symm
  refine F.push_group_congr ?_ _ _ _
  show g' * (g⁻¹ * g')⁻¹ = g
  rw [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]

/-- The inverse of `toRcoind`, as a function. -/
def ofRcoindFun (Fn : Subring.rcoind (stabilizer G w₀) (M w₀)) : ∀ w : Ω, M w :=
  fun w ↦ F.push (witness G w₀ w) (witness_spec G w₀ w) ((Fn : G → M w₀) (witness G w₀ w))

omit [MulSemiringAction G (∀ w : Ω, M w)] in
include hstab in
theorem ofRcoindFun_apply (Fn : Subring.rcoind (stabilizer G w₀) (M w₀)) (w : Ω) {g : G}
    (hg : g • w₀ = w) :
    F.ofRcoindFun Fn w = F.push g hg ((Fn : G → M w₀) g) :=
  F.rcoind_apply_congr hstab Fn (witness_spec G w₀ w) hg

omit [MulSemiringAction G (∀ w : Ω, M w)] in
theorem ofRcoindFun_toRcoind (x : ∀ w : Ω, M w) :
    F.ofRcoindFun (F.toRcoind hstab x) = x := by
  funext w
  obtain ⟨g, rfl⟩ := exists_smul_eq G w₀ w
  rw [F.ofRcoindFun_apply hstab _ _ (rfl : g • w₀ = g • w₀), toRcoind_coe, toRcoindFun_apply]
  refine (F.push_mul g g⁻¹ (inv_smul_smul g w₀) (rfl : g • w₀ = g • w₀)
    (by rw [mul_inv_cancel, one_smul]) _).trans ?_
  refine (F.push_group_congr (mul_inv_cancel g) _ (by rw [one_smul]) _).trans ?_
  exact F.push_one _ _

omit [MulSemiringAction G (∀ w : Ω, M w)] in
theorem toRcoind_ofRcoindFun (Fn : Subring.rcoind (stabilizer G w₀) (M w₀)) :
    F.toRcoind hstab (F.ofRcoindFun Fn) = Fn := by
  refine Subtype.ext (funext fun g ↦ ?_)
  rw [toRcoind_coe, toRcoindFun_apply,
    F.ofRcoindFun_apply hstab _ _ (rfl : g • w₀ = g • w₀)]
  refine (F.push_mul g⁻¹ g (rfl : g • w₀ = g • w₀) (inv_smul_smul g w₀)
    (by rw [inv_mul_cancel, one_smul]) _).trans ?_
  refine (F.push_group_congr (inv_mul_cancel g) _ (by rw [one_smul]) _).trans ?_
  exact F.push_one _ _

include hstab in
/-- **A transitive equivariant family of rings is an induced module.**  The product
`∏ w : Ω, M w` over a transitive `G`-set `Ω` is `G`-equivariantly isomorphic to the module
`Ind_{Stab(w₀)}^G (M w₀)` coinduced from the stabiliser of any base point `w₀`.  The
equivariance is `EquivariantFamily.equivRcoind_smul`. -/
def equivRcoind : (∀ w : Ω, M w) ≃+* Subring.rcoind (stabilizer G w₀) (M w₀) :=
  RingEquiv.ofBijective (F.toRcoind hstab)
    (Function.bijective_iff_has_inverse.2
      ⟨F.ofRcoindFun, F.ofRcoindFun_toRcoind hstab, F.toRcoind_ofRcoindFun hstab⟩)

omit [MulSemiringAction G (∀ w : Ω, M w)] in
@[simp]
theorem equivRcoind_apply (x : ∀ w : Ω, M w) :
    F.equivRcoind hstab x = F.toRcoind hstab x := rfl

/-- The isomorphism with the induced module is `G`-equivariant. -/
theorem equivRcoind_smul (hpi : F.IsPiAction) (σ : G) (x : ∀ w : Ω, M w) :
    F.equivRcoind hstab (σ • x) = σ • F.equivRcoind hstab x :=
  F.toRcoind_smul hstab hpi σ x

end Rcoind

end EquivariantFamily
