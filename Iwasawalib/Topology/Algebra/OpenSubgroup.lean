/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Topology.Algebra.OpenSubgroup

/-!

# Supplementary results for open normal subgroups

-/

namespace OpenNormalSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] {U V : OpenNormalSubgroup G} {g : G}

@[to_additive (attr := simp)]
theorem coe_toOpenSubgroup : (U.toOpenSubgroup : Set G) = U := rfl

@[to_additive (attr := norm_cast)]
theorem coe_toSubgroup : ((U : Subgroup G) : Set G) = U := rfl

@[to_additive (attr := simp)]
theorem mem_toOpenSubgroup : g ∈ U.toOpenSubgroup ↔ g ∈ U := Iff.rfl

@[to_additive (attr := norm_cast)]
theorem mem_toSubgroup : g ∈ (U : Subgroup G) ↔ g ∈ U := Iff.rfl

@[to_additive]
instance instTop : Top (OpenNormalSubgroup G) := ⟨⟨⊤, inferInstanceAs (⊤ : Subgroup G).Normal⟩⟩

@[to_additive (attr := simp)]
theorem mem_top (x : G) : x ∈ (⊤ : OpenNormalSubgroup G) := trivial

@[to_additive (attr := simp, norm_cast)]
theorem coe_top : ((⊤ : OpenNormalSubgroup G) : Set G) = Set.univ := rfl

@[to_additive (attr := simp)]
theorem toOpenSubgroup_top : (⊤ : OpenNormalSubgroup G).toOpenSubgroup = ⊤ := rfl

@[to_additive (attr := norm_cast)]
theorem toSubgroup_top : ((⊤ : OpenNormalSubgroup G) : Subgroup G) = ⊤ := rfl

@[to_additive]
instance instInhabited : Inhabited (OpenNormalSubgroup G) := ⟨⊤⟩

section prod

variable {H : Type*} [Group H] [TopologicalSpace H]
  (U : OpenNormalSubgroup G) (V : OpenNormalSubgroup H)

/-- The product of two open normal subgroups as an open normal subgroup of the product group. -/
@[to_additive prod /-- The product of two open normal subgroups as an open normal subgroup
of the product group. -/]
def prod : OpenNormalSubgroup (G × H) :=
  ⟨U.toOpenSubgroup.prod V.toOpenSubgroup, U.toSubgroup.prod_normal V.toSubgroup⟩

@[to_additive (attr := simp, norm_cast) coe_prod]
theorem coe_prod : (U.prod V : Set (G × H)) = (U : Set G) ×ˢ (V : Set H) :=
  rfl

@[to_additive (attr := simp) toOpenAddSubgroup_prod]
theorem toOpenSubgroup_prod : (U.prod V).toOpenSubgroup = U.toOpenSubgroup.prod V.toOpenSubgroup :=
  rfl

@[to_additive (attr := norm_cast) toAddSubgroup_prod]
theorem toSubgroup_prod : (U.prod V : Subgroup (G × H)) = (U : Subgroup G).prod V :=
  rfl

end prod

@[to_additive]
instance instOrderTop : OrderTop (OpenNormalSubgroup G) where
  top := ⊤
  le_top _ := Set.subset_univ _

@[to_additive (attr := simp)]
theorem toOpenSubgroup_le : U.toOpenSubgroup ≤ V.toOpenSubgroup ↔ U ≤ V :=
  Iff.rfl

@[to_additive (attr := norm_cast)]
theorem toSubgroup_le : (U : Subgroup G) ≤ (V : Subgroup G) ↔ U ≤ V :=
  Iff.rfl

section comap

variable {N : Type*} [Group N] [TopologicalSpace N]

/-- The preimage of an `OpenNormalSubgroup` along a continuous `Monoid` homomorphism
  is an `OpenNormalSubgroup`. -/
@[to_additive /-- The preimage of an `OpenNormalAddSubgroup` along a continuous `AddMonoid`
homomorphism is an `OpenNormalAddSubgroup`. -/]
def comap (f : G →* N) (hf : Continuous f) (H : OpenNormalSubgroup N) : OpenNormalSubgroup G :=
  ⟨.comap f hf H.toOpenSubgroup, Subgroup.normal_comap f⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_comap (H : OpenNormalSubgroup N) (f : G →* N) (hf : Continuous f) :
    (H.comap f hf : Set G) = f ⁻¹' H :=
  rfl

@[to_additive (attr := simp)]
theorem toOpenSubgroup_comap (H : OpenNormalSubgroup N) (f : G →* N) (hf : Continuous f) :
    (H.comap f hf).toOpenSubgroup = H.toOpenSubgroup.comap f hf :=
  rfl

@[to_additive (attr := norm_cast)]
theorem toSubgroup_comap (H : OpenNormalSubgroup N) (f : G →* N) (hf : Continuous f) :
    (H.comap f hf : Subgroup G) = (H : Subgroup N).comap f :=
  rfl

@[to_additive (attr := simp)]
theorem mem_comap {H : OpenNormalSubgroup N} {f : G →* N} {hf : Continuous f} {x : G} :
    x ∈ H.comap f hf ↔ f x ∈ H :=
  Iff.rfl

@[to_additive]
theorem comap_comap {P : Type*} [Group P] [TopologicalSpace P] (K : OpenNormalSubgroup P)
    (f₂ : N →* P) (hf₂ : Continuous f₂) (f₁ : G →* N) (hf₁ : Continuous f₁) :
    (K.comap f₂ hf₂).comap f₁ hf₁ = K.comap (f₂.comp f₁) (hf₂.comp hf₁) :=
  rfl

end comap

end OpenNormalSubgroup
