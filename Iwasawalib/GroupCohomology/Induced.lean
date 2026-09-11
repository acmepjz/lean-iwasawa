/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.FiniteIndex

@[expose] public section

/-!
# Coinduced modules in "right-equivariant" form

Let `G` be a group, `H ≤ G` a subgroup and `M` an `H`-module.  Mathlib already provides the
coinduced representation `Representation.coind φ ρ` along a monoid homomorphism `φ : H →* G`
(see `Mathlib/RepresentationTheory/Coinduced.lean`), realised as the functions `f : G → M`
satisfying
`f (φ h * g) = ρ h (f g)`,
with `G` acting by `(g • f) g₁ = f (g₁ * g)`, as well as the induced representation
`Representation.ind` and, for a subgroup of finite index, the comparison `Rep.indCoindIso`
between the two.  **Shapiro's lemma is also already in Mathlib**, as
`groupCohomology.coindIso : Hⁿ(G, Coind_H^G A) ≅ Hⁿ(H, A)`.  We do not rebuild any of this.

What this file adds is the *other* standard normalisation of the same module, the one which
arises in number theory when one writes `∏_{w ∣ v} L_w` as an induced module for the
decomposition group: the functions `F : G → M` satisfying

`F (g * h) = h⁻¹ • F g`  for all `g : G`, `h : H`,

with `G` acting by `(σ • F) g = F (σ⁻¹ * g)`.  Here the subgroup translates on the *right*
and the `G`-action is on the left; the natural indexing of the factors `L_w` is then by the
coset `g D_w` with `g • w₀ = w`, which is why this shape is what the concrete constructions
produce.

## Design decision

We do **not** introduce a new definition of the induced module: `rcoind` is defined
independently (so that it is definitionally the concrete object one meets in practice, with no
coset machinery in the way) but it is immediately proved isomorphic to Mathlib's
`Representation.coind` along `H.subtype`, by the map

`F ↦ (g ↦ F g⁻¹)`,

and *all* homological content is then imported from Mathlib through that isomorphism.  So the
repository has one notion of induced module, Mathlib's; `rcoind` is a presentation of it.
The inversion is forced: `F (g * h) = h⁻¹ • F g` becomes `f (h * g) = h • f g` exactly under
`f g = F g⁻¹`, and the left translation action becomes the right translation action.

## Main definitions

* `Representation.rcoindV H ρ` : the submodule of right-`H`-equivariant functions `G → M`.
* `Representation.rcoind H ρ` : the `G`-representation on `rcoindV H ρ`.
* `Representation.rcoindEquivCoind H ρ` : the isomorphism with `Representation.coind`.
* `Rep.rcoind H A`, `Rep.rcoindFunctor k H`, `Rep.rcoindIsoCoind`,
  `Rep.rcoindFunctorIsoCoindFunctor`, `Rep.resRcoindAdjunction`.
* `Rep.rcoindCounit`, `Rep.rcoindUnit`.
* `Subring.rcoind H R` and `Subgroup.rcoindMul H N` : the same construction for a ring with a
  `MulSemiringAction` and for a group with a `MulDistribMulAction`, together with
  `Subring.rcoindUnitsEquiv : (Subring.rcoind H R)ˣ ≃* Subgroup.rcoindMul H Rˣ`.
-/

noncomputable section

universe u

/-- An additive equivalence between `ℤ`-modules is `ℤ`-linear.  Unlike
`AddEquiv.toIntLinearEquiv` this keeps whatever `Module ℤ` instances are in scope, which is
what one needs when the modules come from objects of `Rep ℤ G`. -/
def AddEquiv.toIntLinearEquivOfModule {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (e : M ≃+ N) : M ≃ₗ[ℤ] N :=
  { e with map_smul' := fun c x ↦ by simpa using map_intCast_smul e ℤ ℤ c x }

@[simp]
lemma AddEquiv.toIntLinearEquivOfModule_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (e : M ≃+ N) (x : M) : e.toIntLinearEquivOfModule x = e x := rfl

namespace Representation

variable {k G : Type*} [CommRing k] [Group G] (H : Subgroup G) {M N : Type*}
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  (ρ : Representation k H M) (τ : Representation k H N)

/-- The `k`-submodule of functions `F : G → M` which are equivariant for the *right* translation
action of `H`, i.e. `F (g * h) = ρ h⁻¹ (F g)`.  This is the underlying module of the coinduced
representation `Ind_H^G M` in the normalisation used in number theory. -/
@[simps]
def rcoindV : Submodule k (G → M) where
  carrier := {F : G → M | ∀ (g : G) (h : H), F (g * h) = ρ h⁻¹ (F g)}
  add_mem' hF hF' g h := by simp [hF g h, hF' g h]
  zero_mem' g h := by simp
  smul_mem' c F hF g h := by simp [hF g h]

@[simp]
lemma mem_rcoindV (F : G → M) :
    F ∈ rcoindV H ρ ↔ ∀ (g : G) (h : H), F (g * h) = ρ h⁻¹ (F g) := Iff.rfl

variable {H ρ} in
lemma rcoindV_apply_mul (F : rcoindV H ρ) (g : G) (h : H) :
    (F : G → M) (g * h) = ρ h⁻¹ ((F : G → M) g) := F.2 g h

/-- The `G`-representation coinduced from an `H`-representation `ρ`, in right-equivariant form:
`G` acts on `rcoindV H ρ` by `(σ • F) g = F (σ⁻¹ * g)`. -/
@[simps]
def rcoind : Representation k G (rcoindV H ρ) where
  toFun σ := (LinearMap.funLeft k M (fun g ↦ σ⁻¹ * g)).restrict fun F hF g h => by
    simpa [mul_assoc] using hF (σ⁻¹ * g) h
  map_one' := by ext F g; simp
  map_mul' σ σ' := by ext F g; simp [mul_assoc, mul_inv_rev]

variable {H ρ} in
@[simp]
lemma rcoind_apply_coe_apply (σ : G) (F : rcoindV H ρ) (g : G) :
    ((rcoind H ρ σ F : rcoindV H ρ) : G → M) g = (F : G → M) (σ⁻¹ * g) := rfl

/-- The comparison map with Mathlib's coinduced representation, `F ↦ (g ↦ F g⁻¹)`. -/
def rcoindEquivCoindₗ : rcoindV H ρ ≃ₗ[k] coindV H.subtype ρ where
  toFun F := ⟨fun g ↦ (F : G → M) g⁻¹, fun h g ↦ by
    have := rcoindV_apply_mul F g⁻¹ h⁻¹
    simpa [mul_inv_rev] using this⟩
  invFun f := ⟨fun g ↦ (f : G → M) g⁻¹, fun g h ↦ by
    have := f.2 h⁻¹ g⁻¹
    simpa [mul_inv_rev] using this⟩
  map_add' F F' := rfl
  map_smul' c F := rfl
  left_inv F := Subtype.ext (funext fun g ↦ by simp)
  right_inv f := Subtype.ext (funext fun g ↦ by simp)

variable {H ρ} in
@[simp]
lemma rcoindEquivCoindₗ_apply_val (F : rcoindV H ρ) (g : G) :
    (rcoindEquivCoindₗ H ρ F).1 g = F.1 g⁻¹ := rfl

variable {H ρ} in
@[simp]
lemma rcoindEquivCoindₗ_symm_apply_val (f : coindV H.subtype ρ) (g : G) :
    ((rcoindEquivCoindₗ H ρ).symm f).1 g = f.1 g⁻¹ := rfl

variable {H ρ} in
lemma rcoindEquivCoindₗ_equivariant (σ : G) (F : rcoindV H ρ) :
    rcoindEquivCoindₗ H ρ (rcoind H ρ σ F) = coind H.subtype ρ σ (rcoindEquivCoindₗ H ρ F) :=
  Subtype.ext (funext fun g ↦ by simp [mul_inv_rev])

/-- The right-equivariant model `rcoind H ρ` of the coinduced representation is isomorphic to
Mathlib's `coind H.subtype ρ`. -/
def rcoindEquivCoind : (rcoind H ρ).Equiv (coind H.subtype ρ) :=
  Equiv.mk (rcoindEquivCoindₗ H ρ) fun σ ↦
    LinearMap.ext fun F ↦ rcoindEquivCoindₗ_equivariant σ F

@[simp]
lemma rcoindEquivCoind_apply (F : rcoindV H ρ) :
    rcoindEquivCoind H ρ F = rcoindEquivCoindₗ H ρ F := rfl

end Representation

namespace Rep

open CategoryTheory Representation

universe v w

variable {k : Type u} {G : Type v} [CommRing k] [Group G] (H : Subgroup G)

/-!
The `Rep`-level API.  Since the underlying module of `rcoind H A` is a submodule of `G → A`,
it lives in the universe `max v w` where `G : Type v` and `A : Type w`; we therefore state the
whole section for representations on modules in `Type (max v w)`, which is no loss of
generality (and is automatic in the intended application, where everything is in `Type`).
-/

/-- The coinduced representation `Ind_H^G A` in right-equivariant form, as an object of
`Rep k G`: the `H`-equivariant functions `F : G → A` with `F (g * h) = ρ h⁻¹ (F g)`, with `G`
acting by `(σ • F) g = F (σ⁻¹ * g)`. -/
abbrev rcoind (A : Rep.{max v w} k H) : Rep.{max v w} k G :=
  Rep.of (Representation.rcoind H A.ρ)

/-- `rcoind H A` is isomorphic to Mathlib's coinduced representation `coind H.subtype A`. -/
def rcoindIsoCoind (A : Rep.{max v w} k H) : rcoind H A ≅ coind H.subtype A :=
  Rep.mkIso (Representation.rcoindEquivCoind H A.ρ)

@[simp]
lemma rcoindIsoCoind_hom_hom_apply (A : Rep.{max v w} k H) (F : rcoindV H A.ρ) (g : G) :
    ((rcoindIsoCoind H A).hom.hom F).1 g = F.1 g⁻¹ := rfl

variable {H}

/-- Functoriality of `rcoind` in the module, as a linear map. -/
def rcoindMapₗ {A B : Rep.{max v w} k H} (f : A ⟶ B) :
    rcoindV H A.ρ →ₗ[k] rcoindV H B.ρ :=
  (f.hom.toLinearMap.compLeft G).restrict fun F hF g h ↦ by
    show f.hom.toLinearMap (F (g * h)) = B.ρ h⁻¹ (f.hom.toLinearMap (F g))
    rw [hF g h]
    exact LinearMap.congr_fun (f.hom.isIntertwining' h⁻¹) (F g)

@[simp]
lemma rcoindMapₗ_apply_val {A B : Rep.{max v w} k H} (f : A ⟶ B) (F : rcoindV H A.ρ) (g : G) :
    (rcoindMapₗ f F).1 g = f.hom (F.1 g) := rfl

lemma rcoindMapₗ_equivariant {A B : Rep.{max v w} k H} (f : A ⟶ B) (σ : G)
    (F : rcoindV H A.ρ) :
    rcoindMapₗ f (Representation.rcoind H A.ρ σ F) =
      Representation.rcoind H B.ρ σ (rcoindMapₗ f F) := rfl

/-- Functoriality of `rcoind` in the module: a morphism `A ⟶ B` of `H`-representations induces
`rcoind H A ⟶ rcoind H B` by postcomposition. -/
def rcoindMap {A B : Rep.{max v w} k H} (f : A ⟶ B) : rcoind H A ⟶ rcoind H B :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (rcoindMapₗ f)
    fun σ F ↦ rcoindMapₗ_equivariant f σ F

@[simp]
lemma rcoindMap_hom_apply_val {A B : Rep.{max v w} k H} (f : A ⟶ B) (F : rcoindV H A.ρ)
    (g : G) : ((rcoindMap f).hom F).1 g = f.hom (F.1 g) := rfl

variable (k H)

/-- `rcoind` as a functor `Rep k H ⥤ Rep k G`. -/
def rcoindFunctor : Rep.{max v w} k H ⥤ Rep.{max v w} k G where
  obj A := rcoind H A
  map f := rcoindMap f
  map_id _ := Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    LinearMap.ext fun _ ↦ Subtype.ext (funext fun _ ↦ rfl)
  map_comp _ _ := Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    LinearMap.ext fun _ ↦ Subtype.ext (funext fun _ ↦ rfl)

@[simp]
lemma rcoindFunctor_obj (A : Rep.{max v w} k H) :
    (rcoindFunctor k H).obj A = rcoind H A := rfl

@[simp]
lemma rcoindFunctor_map {A B : Rep.{max v w} k H} (f : A ⟶ B) :
    (rcoindFunctor k H).map f = rcoindMap f := rfl

/-- The right-equivariant coinduction functor is naturally isomorphic to Mathlib's
coinduction functor along `H.subtype`. -/
def rcoindFunctorIsoCoindFunctor :
    rcoindFunctor.{u, v, w} k H ≅ coindFunctor.{max v w} k H.subtype :=
  NatIso.ofComponents (rcoindIsoCoind H) fun _ ↦ Rep.hom_ext <|
    Representation.IntertwiningMap.ext <| LinearMap.ext fun _ ↦ Subtype.ext (funext fun _ ↦ rfl)

/-- The counit of the (restriction, coinduction) adjunction, in right-equivariant form:
evaluation at `1 : G`, `F ↦ F 1`, is a map of `H`-representations `Res_H (rcoind H A) ⟶ A`. -/
def rcoindCounit (A : Rep.{max v w} k H) : Rep.res H.subtype (rcoind H A) ⟶ A :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ({ toFun F := F.1 1
       map_add' _ _ := rfl
       map_smul' _ _ := rfl } : rcoindV H A.ρ →ₗ[k] A.V)
    fun h F ↦ by
      show F.1 ((h : G)⁻¹ * 1) = A.ρ h (F.1 1)
      have := F.2 1 h⁻¹
      simp only [one_mul, Subgroup.coe_inv, inv_inv] at this
      rw [mul_one]
      exact this

@[simp]
lemma rcoindCounit_hom_apply (A : Rep.{max v w} k H) (F : rcoindV H A.ρ) :
    (rcoindCounit k H A).hom F = F.1 1 := rfl

/-- The unit of the (restriction, coinduction) adjunction, in right-equivariant form:
`b ↦ (g ↦ ρ g⁻¹ b)` is a map of `G`-representations `B ⟶ rcoind H (Res_H B)`. -/
def rcoindUnit (B : Rep.{max v w} k G) : B ⟶ rcoind H (Rep.res H.subtype B) :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ({ toFun b := ⟨fun g ↦ B.ρ g⁻¹ b, fun g h ↦ by
         show B.ρ (g * (h : G))⁻¹ b = B.ρ ((h⁻¹ : H) : G) (B.ρ g⁻¹ b)
         rw [mul_inv_rev, ← Module.End.mul_apply, ← map_mul]
         simp⟩
       map_add' _ _ := Subtype.ext (funext fun _ ↦ by simp)
       map_smul' _ _ := Subtype.ext (funext fun _ ↦ by simp) } :
        B.V →ₗ[k] rcoindV H (Rep.res H.subtype B).ρ)
    fun σ b ↦ Subtype.ext (funext fun g ↦ by
      show B.ρ g⁻¹ (B.ρ σ b) = B.ρ (σ⁻¹ * g)⁻¹ b
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_inv])

@[simp]
lemma rcoindUnit_hom_apply_val (B : Rep.{max v w} k G) (b : B) (g : G) :
    ((rcoindUnit k H B).hom b).1 g = B.ρ g⁻¹ b := rfl

/-- Restriction along `H ≤ G` is left adjoint to right-equivariant coinduction. -/
def resRcoindAdjunction :
    Rep.resFunctor.{max v w} H.subtype ⊣ rcoindFunctor.{u, v, w} k H :=
  (Rep.resCoindAdjunction k H.subtype).ofNatIsoRight
    (rcoindFunctorIsoCoindFunctor k H).symm

end Rep

/-!
## The ring and group versions

In the applications the module `M` is the additive group of a ring `R` (a local field `L_w`)
or the unit group of such a ring (the local units `L_w^×`), and the coinduced module is met as
a *subring* of `G → R`, resp. a *subgroup* of `G → R^×`.  We therefore record the same
construction in those categories, together with the comparison isomorphisms with
`Representation.rcoindV`.  The unit group of the coinduced ring is the coinduced group of the
unit groups, which is what turns the additive Shapiro isomorphism into the multiplicative one.
-/

attribute [local instance] Units.mulDistribMulActionRight

namespace Subring

variable {G : Type*} [Group G] (H : Subgroup G) (R : Type*) [Ring R] [MulSemiringAction H R]

/-- The coinduced ring `Ind_H^G R`: the subring of functions `F : G → R` satisfying
`F (g * h) = h⁻¹ • F g` for all `g : G`, `h : H`. -/
def rcoind : Subring (G → R) where
  carrier := {F : G → R | ∀ (g : G) (h : H), F (g * h) = h⁻¹ • F g}
  one_mem' g h := by simp
  mul_mem' hF hF' g h := by simp [hF g h, hF' g h, smul_mul']
  zero_mem' g h := by simp
  add_mem' hF hF' g h := by simp [hF g h, hF' g h, smul_add]
  neg_mem' hF g h := by simp [hF g h]

variable {H R}

@[simp]
lemma mem_rcoind {F : G → R} :
    F ∈ rcoind H R ↔ ∀ (g : G) (h : H), F (g * h) = h⁻¹ • F g := Iff.rfl

lemma rcoind_apply_mul (F : rcoind H R) (g : G) (h : H) :
    (F : G → R) (g * h) = h⁻¹ • (F : G → R) g := F.2 g h

variable (H R)

/-- Translation of an equivariant function by an element of `G`. -/
def rcoindSmul (σ : G) (F : rcoind H R) : rcoind H R :=
  ⟨fun g ↦ (F : G → R) (σ⁻¹ * g), fun g h ↦ by
    show (F : G → R) (σ⁻¹ * (g * (h : G))) = h⁻¹ • (F : G → R) (σ⁻¹ * g)
    rw [← mul_assoc]
    exact F.2 _ h⟩

/-- The translation action of `G` on the coinduced ring: `(σ • F) g = F (σ⁻¹ * g)`. -/
instance rcoindMulSemiringAction : MulSemiringAction G (rcoind H R) where
  smul := rcoindSmul H R
  one_smul F := Subtype.ext (funext fun g ↦ by
    show (F : G → R) ((1 : G)⁻¹ * g) = (F : G → R) g
    rw [inv_one, one_mul])
  mul_smul σ σ' F := Subtype.ext (funext fun g ↦ by
    show (F : G → R) ((σ * σ')⁻¹ * g) = (F : G → R) (σ'⁻¹ * (σ⁻¹ * g))
    rw [mul_inv_rev, mul_assoc])
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

variable {H R}

@[simp]
lemma rcoind_smul_apply (σ : G) (F : rcoind H R) (g : G) :
    ((σ • F : rcoind H R) : G → R) g = (F : G → R) (σ⁻¹ * g) := rfl

variable (H R)

/-- The coinduced ring is the coinduced module of the additive group of `R`: the underlying
sets agree, so this is the identity on underlying functions. -/
def rcoindAddEquivRcoindV :
    rcoind H R ≃+ Representation.rcoindV H (Representation.ofDistribMulAction ℤ H R) where
  toFun F := ⟨F.1, fun g h ↦ F.2 g h⟩
  invFun F := ⟨F.1, fun g h ↦ F.2 g h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable {H R}

@[simp]
lemma rcoindAddEquivRcoindV_apply_val (F : rcoind H R) (g : G) :
    (rcoindAddEquivRcoindV H R F).1 g = (F : G → R) g := rfl

lemma rcoindAddEquivRcoindV_equivariant (σ : G) (F : rcoind H R) :
    rcoindAddEquivRcoindV H R (σ • F) =
      Representation.rcoind H (Representation.ofDistribMulAction ℤ H R) σ
        (rcoindAddEquivRcoindV H R F) := rfl

end Subring

namespace Subgroup

variable {G : Type*} [Group G] (H : Subgroup G) (N : Type*) [CommGroup N]
  [MulDistribMulAction H N]

/-- The coinduced group `Ind_H^G N`: the subgroup of functions `F : G → N` satisfying
`F (g * h) = h⁻¹ • F g` for all `g : G`, `h : H`. -/
def rcoindMul : Subgroup (G → N) where
  carrier := {F : G → N | ∀ (g : G) (h : H), F (g * h) = h⁻¹ • F g}
  one_mem' g h := by simp
  mul_mem' hF hF' g h := by simp [hF g h, hF' g h, smul_mul']
  inv_mem' hF g h := by simp [hF g h]

variable {H N}

@[simp]
lemma mem_rcoindMul {F : G → N} :
    F ∈ rcoindMul H N ↔ ∀ (g : G) (h : H), F (g * h) = h⁻¹ • F g := Iff.rfl

variable (H N)

/-- Translation of an equivariant function by an element of `G`. -/
def rcoindMulSmul (σ : G) (F : rcoindMul H N) : rcoindMul H N :=
  ⟨fun g ↦ (F : G → N) (σ⁻¹ * g), fun g h ↦ by
    show (F : G → N) (σ⁻¹ * (g * (h : G))) = h⁻¹ • (F : G → N) (σ⁻¹ * g)
    rw [← mul_assoc]
    exact F.2 _ h⟩

/-- The translation action of `G` on the coinduced group: `(σ • F) g = F (σ⁻¹ * g)`. -/
instance rcoindMulDistribMulAction : MulDistribMulAction G (rcoindMul H N) where
  smul := rcoindMulSmul H N
  one_smul F := Subtype.ext (funext fun g ↦ by
    show (F : G → N) ((1 : G)⁻¹ * g) = (F : G → N) g
    rw [inv_one, one_mul])
  mul_smul σ σ' F := Subtype.ext (funext fun g ↦ by
    show (F : G → N) ((σ * σ')⁻¹ * g) = (F : G → N) (σ'⁻¹ * (σ⁻¹ * g))
    rw [mul_inv_rev, mul_assoc])
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

variable {H N}

@[simp]
lemma rcoindMul_smul_apply (σ : G) (F : rcoindMul H N) (g : G) :
    ((σ • F : rcoindMul H N) : G → N) g = (F : G → N) (σ⁻¹ * g) := rfl

variable (H N)

/-- The coinduced group, written additively, is the coinduced module of `Additive N`. -/
def rcoindMulAddEquivRcoindV :
    Additive (rcoindMul H N) ≃+
      Representation.rcoindV H (Representation.ofMulDistribMulAction H N) where
  toFun F := ⟨fun g ↦ Additive.ofMul ((F.toMul : G → N) g), fun g h ↦ F.toMul.2 g h⟩
  invFun F := Additive.ofMul ⟨fun g ↦ (F.1 g).toMul, fun g h ↦ F.2 g h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable {H N}

@[simp]
lemma rcoindMulAddEquivRcoindV_apply_val (F : Additive (rcoindMul H N)) (g : G) :
    (rcoindMulAddEquivRcoindV H N F).1 g = Additive.ofMul ((F.toMul : G → N) g) := rfl

lemma rcoindMulAddEquivRcoindV_equivariant (σ : G) (F : Additive (rcoindMul H N)) :
    rcoindMulAddEquivRcoindV H N (Additive.ofMul (σ • F.toMul)) =
      Representation.rcoind H (Representation.ofMulDistribMulAction H N) σ
        (rcoindMulAddEquivRcoindV H N F) := rfl

end Subgroup

namespace Subring

variable {G : Type*} [Group G] (H : Subgroup G) (R : Type*) [CommRing R]
  [MulSemiringAction H R]

/-- **The units of the coinduced ring are the coinduced group of the units.**  A function
`F : G → R` which is `H`-equivariant is a unit of `Ind_H^G R` exactly when it is pointwise a
unit, because the pointwise inverse of an equivariant function is again equivariant. -/
def rcoindUnitsEquiv : (rcoind H R)ˣ ≃* Subgroup.rcoindMul H Rˣ where
  toFun U := ⟨fun g ↦ ⟨(U.val : G → R) g, (U.inv : G → R) g,
      congrFun (congrArg Subtype.val U.val_inv) g,
      congrFun (congrArg Subtype.val U.inv_val) g⟩,
    fun g h ↦ Units.ext (U.val.2 g h)⟩
  invFun F :=
    { val := ⟨fun g ↦ ((F : G → Rˣ) g : R), fun g h ↦ by
        have := congrArg (Units.val) (F.2 g h)
        simpa using this⟩
      inv := ⟨fun g ↦ ((((F : G → Rˣ) g)⁻¹ : Rˣ) : R), fun g h ↦ by
        have := congrArg (fun u : Rˣ ↦ ((u⁻¹ : Rˣ) : R)) (F.2 g h)
        simpa using this⟩
      val_inv := Subtype.ext (funext fun g ↦ by simp)
      inv_val := Subtype.ext (funext fun g ↦ by simp) }
  left_inv U := Units.ext (Subtype.ext (funext fun g ↦ rfl))
  right_inv F := Subtype.ext (funext fun g ↦ Units.ext rfl)
  map_mul' U U' := Subtype.ext (funext fun g ↦ Units.ext rfl)

variable {H R}

@[simp]
lemma rcoindUnitsEquiv_apply_val_val (U : (rcoind H R)ˣ) (g : G) :
    (((rcoindUnitsEquiv H R U : Subgroup.rcoindMul H Rˣ) : G → Rˣ) g : R) =
      (U.val : G → R) g := rfl

lemma rcoindUnitsEquiv_equivariant (σ : G) (U : (rcoind H R)ˣ) :
    rcoindUnitsEquiv H R (σ • U) = σ • rcoindUnitsEquiv H R U :=
  Subtype.ext (funext fun _ ↦ Units.ext rfl)

end Subring
