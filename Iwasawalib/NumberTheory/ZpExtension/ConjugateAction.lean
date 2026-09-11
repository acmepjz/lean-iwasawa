/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Maps.Basic

@[expose] public section

/-!
# The conjugation action of `G ⧸ X` on an abelian normal subgroup `X`

Blueprint nodes `conjugate-action` and `conjugate-action-cont`.

Let `G` be a group and `X` an abelian normal subgroup.  Conjugation gives a homomorphism
`G →* MulAut X` (`MulAut.conjNormal`) which kills `X` precisely because `X` is abelian, hence
factors through `Γ := G ⧸ X`.  We package this as `Subgroup.conjQuotient` and show that when
`G` is a topological group the resulting action `Γ × X → X` is continuous.

The continuity proof is the one in the blueprint: the projection `G → G ⧸ X` is an open
continuous surjection, hence a quotient map, hence so is `G × X → (G ⧸ X) × X`, and the
conjugation map `G × X → X` is constant on its fibres.
-/

open Topology

namespace Subgroup

variable {G : Type*} [Group G] (X : Subgroup G) [X.Normal]
  (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)

include hX

theorem conjNormal_eq_one_of_mem {g : G} (hg : g ∈ X) :
    (MulAut.conjNormal g : MulAut X) = 1 := by
  ext a
  have := hX g hg a a.2
  simp only [MulAut.conjNormal_apply, MulAut.one_apply]
  rw [this, mul_assoc, mul_inv_cancel, mul_one]

/-- **Blueprint node `conjugate-action`.**  If `X` is an abelian normal subgroup of `G`, then
`Γ = G ⧸ X` acts on `X` by `σ • x = σ̃ x σ̃⁻¹` for any lift `σ̃` of `σ`. -/
noncomputable def conjQuotient : G ⧸ X →* MulAut X :=
  QuotientGroup.lift X MulAut.conjNormal fun _ hg ↦ conjNormal_eq_one_of_mem X hX hg

@[simp]
theorem conjQuotient_mk (g : G) :
    conjQuotient X hX (QuotientGroup.mk g) = MulAut.conjNormal g :=
  rfl

theorem conjQuotient_mk_apply (g : G) (x : X) :
    ((conjQuotient X hX (QuotientGroup.mk g) x : X) : G) = g * x * g⁻¹ :=
  MulAut.conjNormal_apply g x

/-- The conjugation action of `Γ = G ⧸ X` on `X`, as a plain function.  See
`Subgroup.conjQuotient` for the packaging as a homomorphism to `MulAut X`. -/
noncomputable def conjAct (σ : G ⧸ X) (x : X) : X := conjQuotient X hX σ x

@[simp]
theorem conjAct_one (x : X) : conjAct X hX 1 x = x := by
  simp [conjAct]

theorem conjAct_mul (σ τ : G ⧸ X) (x : X) :
    conjAct X hX (σ * τ) x = conjAct X hX σ (conjAct X hX τ x) := by
  simp [conjAct]

@[simp]
theorem conjAct_map_mul (σ : G ⧸ X) (x y : X) :
    conjAct X hX σ (x * y) = conjAct X hX σ x * conjAct X hX σ y :=
  map_mul _ x y

@[simp]
theorem conjAct_map_inv (σ : G ⧸ X) (x : X) :
    conjAct X hX σ x⁻¹ = (conjAct X hX σ x)⁻¹ :=
  map_inv _ x

@[simp]
theorem conjAct_map_one (σ : G ⧸ X) : conjAct X hX σ 1 = 1 := map_one _

theorem coe_conjAct_mk (g : G) (x : X) :
    ((conjAct X hX (QuotientGroup.mk g) x : X) : G) = g * x * g⁻¹ :=
  conjQuotient_mk_apply X hX g x

/-- `Γ` acts on `X` by group automorphisms, so `σ • ·` is a bijection. -/
theorem conjAct_leftInverse (σ : G ⧸ X) (x : X) :
    conjAct X hX σ⁻¹ (conjAct X hX σ x) = x := by
  rw [← conjAct_mul, inv_mul_cancel, conjAct_one]

omit [X.Normal] in
/-- The commutativity of `X`, packaged for `↥X`. -/
theorem mul_comm_of_abelian (x y : X) : x * y = y * x :=
  Subtype.ext (hX x x.2 y y.2)

end Subgroup

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Subgroup G) [X.Normal] (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)

include hX

omit hX in
/-- Conjugation `G × X → X` is continuous (`X` carries the subspace topology). -/
theorem continuous_conj_prod :
    Continuous fun gx : G × X ↦ (⟨gx.1 * gx.2 * gx.1⁻¹, Subgroup.Normal.conj_mem ‹X.Normal› _ gx.2.2 _⟩ : X) := by
  refine Continuous.subtype_mk ?_ _
  fun_prop

/-- **Blueprint node `conjugate-action-cont`.**  If `G` is a topological group and `X` is an
abelian normal subgroup, then the conjugation action `(G ⧸ X) × X → X` is continuous. -/
theorem continuous_conjQuotient :
    Continuous fun σx : (G ⧸ X) × X ↦ (conjQuotient X hX σx.1 σx.2 : X) := by
  have hq : IsQuotientMap (Prod.map (QuotientGroup.mk : G → G ⧸ X) (id : X → X)) := by
    refine IsOpenMap.isQuotientMap ?_ ?_ ?_
    · exact (QuotientGroup.isOpenMap_coe (N := X)).prodMap IsOpenMap.id
    · exact (continuous_quotient_mk' (s := QuotientGroup.leftRel X)).prodMap continuous_id
    · exact Function.Surjective.prodMap Quot.mk_surjective Function.surjective_id
  rw [hq.continuous_iff]
  convert continuous_conj_prod X using 1
  ext ⟨g, x⟩
  exact conjQuotient_mk_apply X hX g x

/-- For fixed `x`, the map `σ ↦ σ • x` is continuous. -/
theorem continuous_conjAct_right (x : X) :
    Continuous fun σ : G ⧸ X ↦ conjAct X hX σ x :=
  (continuous_conjQuotient X hX).comp (continuous_id.prodMk continuous_const)

end Subgroup
