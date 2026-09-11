/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.CyclicTate

@[expose] public section

/-!
# The Tate cohomology hexagon of a finite cyclic group

A short exact sequence `0 → A → B → C → 0` of `G`-modules for a finite cyclic group
`G = ⟨σ⟩` gives rise to the six-term exact sequence

`Ĥ⁰(A) → Ĥ⁰(B) → Ĥ⁰(C) → Ĥ¹(A) → Ĥ¹(B) → Ĥ¹(C) → Ĥ⁰(A)`

which closes up into a hexagon.  This is the whole of the long exact sequence of Tate
cohomology, because for a cyclic group Tate cohomology is two-periodic.

## Main definitions

* `CyclicTate.IsShortExact`: the short exactness of `A --i--> B --p--> C`.
* `CyclicTate.IsShortExact.delta0`: the connecting map `Ĥ⁰(C) → Ĥ¹(A)`.
* `CyclicTate.IsShortExact.delta1`: the connecting map `Ĥ¹(C) → Ĥ⁰(A)`.

## Main statements

* `CyclicTate.IsShortExact.ker_tateH0Map_p`, and its five companions: exactness at each of the
  six vertices of the hexagon.
-/

noncomputable section

namespace CyclicTate

variable {G : Type*} [Group G] [Fintype G] {A B C : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]

/-- `A --i--> B --p--> C` is a short exact sequence of `G`-modules. -/
structure IsShortExact (i : A →+[G] B) (p : B →+[G] C) : Prop where
  /-- `i` is injective. -/
  inj : Function.Injective i
  /-- `p` is surjective. -/
  surj : Function.Surjective p
  /-- the image of `i` is the kernel of `p`. -/
  exact : ∀ b : B, p b = 0 ↔ ∃ a : A, i a = b

namespace IsShortExact

variable {i : A →+[G] B} {p : B →+[G] C} (h : IsShortExact i p) {σ : G}

/-- A set-theoretic section of `p`. -/
def sec (c : C) : B := Function.surjInv h.surj c

omit [Fintype G] in
@[simp] theorem p_sec (c : C) : p (h.sec c) = c := Function.surjInv_eq h.surj c

/-- The preimage under `i` of an element killed by `p`. -/
def preim {b : B} (hb : p b = 0) : A := ((h.exact b).1 hb).choose

omit [Fintype G] in
@[simp] theorem i_preim {b : B} (hb : p b = 0) : i (h.preim hb) = b := ((h.exact b).1 hb).choose_spec

theorem preim_eq {b : B} (hb : p b = 0) {a : A} (ha : i a = b) : h.preim hb = a :=
  h.inj (by rw [i_preim, ha])

omit [Fintype G] in
include h in
theorem p_eq_zero_of_mem_range {a : A} : p (i a) = 0 := (h.exact _).2 ⟨a, rfl⟩

/-! ### The connecting map `Ĥ⁰(C) → Ĥ¹(A)` -/

theorem p_smul_sub_sec {c : C} (hc : σ • c = c) : p (σ • h.sec c - h.sec c) = 0 := by
  rw [map_sub, map_smul, h.p_sec, hc, sub_self]

theorem normHom_preim_smul_sub_sec {c : C} (hc : σ • c = c) :
    normHom G A (h.preim (h.p_smul_sub_sec hc)) = 0 := by
  refine h.inj ?_
  rw [map_normHom, h.i_preim, map_zero]
  exact normHom_subHom σ (h.sec c)

/-- The underlying function of the connecting map `Ĥ⁰(C) → Ĥ¹(A)`. -/
def delta0Fun (σ : G) (x : kerSub G C σ) : TateH1 G A σ :=
  TateH1.mk σ (h.normHom_preim_smul_sub_sec (mem_kerSub.1 x.2))

theorem delta0Fun_add (σ : G) (x y : kerSub G C σ) :
    h.delta0Fun σ (x + y) = h.delta0Fun σ x + h.delta0Fun σ y := by
  rw [delta0Fun, delta0Fun, delta0Fun, TateH1.mk_add, TateH1.mk_eq_mk_iff]
  have hu : p (h.sec ((x : C) + y) - h.sec x - h.sec y) = 0 := by
    simp [map_sub]
  refine ⟨h.preim hu, h.inj ?_⟩
  rw [map_sub, map_smul, h.i_preim, map_sub, map_add, h.i_preim, h.i_preim, h.i_preim]
  simp only [AddSubgroup.coe_add, smul_sub]
  abel

/-- The connecting map `Ĥ⁰(C) → Ĥ¹(A)`. -/
def delta0 (σ : G) : TateH0 G C σ →+ TateH1 G A σ :=
  QuotientAddGroup.lift _ (AddMonoidHom.mk' (h.delta0Fun σ) (h.delta0Fun_add σ)) (by
    rintro ⟨c, hc⟩ hmem
    obtain ⟨c', rfl⟩ := mem_rangeNorm.1 (show c ∈ rangeNorm G C from hmem)
    show h.delta0Fun σ _ = 0
    rw [delta0Fun, TateH1.mk_eq_zero_iff]
    have hb : p (h.sec (normHom G C c') - normHom G B (h.sec c')) = 0 := by
      rw [map_sub, h.p_sec, map_normHom, h.p_sec]
      exact sub_self _
    refine ⟨h.preim hb, h.inj ?_⟩
    rw [map_sub, map_smul, h.i_preim, h.i_preim]
    have h1 : σ • h.sec (normHom G C c') = σ • normHom G B (h.sec c') +
        σ • (h.sec (normHom G C c') - normHom G B (h.sec c')) := by
      rw [← smul_add]; congr 1; abel
    rw [h1, smul_normHom, smul_sub]
    abel)

@[simp] theorem delta0_mk {c : C} (hc : σ • c = c) :
    h.delta0 σ (TateH0.mk σ hc) =
      TateH1.mk σ (h.normHom_preim_smul_sub_sec hc) := rfl

/-! ### The connecting map `Ĥ¹(C) → Ĥ⁰(A)` -/

theorem p_normHom_sec {c : C} (hc : normHom G C c = 0) : p (normHom G B (h.sec c)) = 0 := by
  rw [map_normHom, h.p_sec, hc]

theorem smul_preim_normHom_sec (σ : G) {c : C} (hc : normHom G C c = 0) :
    σ • h.preim (h.p_normHom_sec hc) = h.preim (h.p_normHom_sec hc) := by
  refine h.inj ?_
  rw [map_smul, h.i_preim, smul_normHom]

/-- The underlying function of the connecting map `Ĥ¹(C) → Ĥ⁰(A)`. -/
def delta1Fun (σ : G) (x : kerNorm G C) : TateH0 G A σ :=
  TateH0.mk σ (h.smul_preim_normHom_sec σ (mem_kerNorm.1 x.2))

theorem delta1Fun_add (σ : G) (x y : kerNorm G C) :
    h.delta1Fun σ (x + y) = h.delta1Fun σ x + h.delta1Fun σ y := by
  rw [delta1Fun, delta1Fun, delta1Fun, TateH0.mk_add, TateH0.mk_eq_mk_iff]
  have hu : p (h.sec ((x : C) + y) - h.sec x - h.sec y) = 0 := by
    simp [map_sub]
  refine ⟨h.preim hu, h.inj ?_⟩
  simp only [map_sub, map_add, map_normHom, h.i_preim, AddSubgroup.coe_add]
  abel

/-- The connecting map `Ĥ¹(C) → Ĥ⁰(A)`. -/
def delta1 (σ : G) : TateH1 G C σ →+ TateH0 G A σ :=
  QuotientAddGroup.lift _ (AddMonoidHom.mk' (h.delta1Fun σ) (h.delta1Fun_add σ)) (by
    rintro ⟨c, hc⟩ hmem
    obtain ⟨c', rfl⟩ := mem_rangeSub.1 (show c ∈ rangeSub G C σ from hmem)
    show h.delta1Fun σ _ = 0
    rw [delta1Fun, TateH0.mk_eq_zero_iff]
    have hb : p (h.sec (σ • c' - c') - (σ • h.sec c' - h.sec c')) = 0 := by
      rw [map_sub, h.p_sec, map_sub, map_smul, h.p_sec]
      exact sub_self _
    refine ⟨h.preim hb, h.inj ?_⟩
    rw [map_normHom, h.i_preim, h.i_preim]
    have h1 : h.sec (σ • c' - c') = (σ • h.sec c' - h.sec c') +
        (h.sec (σ • c' - c') - (σ • h.sec c' - h.sec c')) := by abel
    rw [h1]
    simp only [map_add, map_sub]
    rw [show normHom G B (σ • h.sec c') = normHom G B (h.sec c') from normHom_smul G σ _]
    abel)

@[simp] theorem delta1_mk {c : C} (hc : normHom G C c = 0) :
    h.delta1 σ (TateH1.mk σ hc) = TateH0.mk σ (h.smul_preim_normHom_sec σ hc) := rfl

/-! ### Exactness of the hexagon -/

include h

/-- Exactness at `Ĥ⁰(B)`. -/
theorem ker_tateH0Map_p (σ : G) : (tateH0Map p σ).ker = (tateH0Map i σ).range := by
  ext t
  constructor
  · intro ht
    obtain ⟨b, hb, rfl⟩ := TateH0.mk_surjective t
    rw [AddMonoidHom.mem_ker, tateH0Map_mk, TateH0.mk_eq_zero_iff] at ht
    obtain ⟨c', hc'⟩ := ht
    have hx : p (b - normHom G B (h.sec c')) = 0 := by
      rw [map_sub, map_normHom, h.p_sec, hc', sub_self]
    have ha : σ • h.preim hx = h.preim hx :=
      h.inj (by rw [map_smul, h.i_preim, smul_sub, smul_normHom, hb])
    refine ⟨TateH0.mk σ ha, ?_⟩
    rw [tateH0Map_mk, TateH0.mk_eq_mk_iff]
    exact ⟨-h.sec c', by rw [map_neg, h.i_preim]; abel⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨a, ha, rfl⟩ := TateH0.mk_surjective s
    rw [AddMonoidHom.mem_ker, tateH0Map_mk, tateH0Map_mk, TateH0.mk_eq_zero_iff]
    exact ⟨0, by rw [map_zero, h.p_eq_zero_of_mem_range]⟩

/-- Exactness at `Ĥ⁰(C)`. -/
theorem ker_delta0 (σ : G) : (h.delta0 σ).ker = (tateH0Map p σ).range := by
  ext t
  constructor
  · intro ht
    obtain ⟨c, hc, rfl⟩ := TateH0.mk_surjective t
    rw [AddMonoidHom.mem_ker, delta0_mk, TateH1.mk_eq_zero_iff] at ht
    obtain ⟨a₁, ha₁⟩ := ht
    have hb : σ • (h.sec c - i a₁) = h.sec c - i a₁ := by
      rw [smul_sub, ← map_smul, ← sub_eq_zero]
      rw [show σ • h.sec c - i (σ • a₁) - (h.sec c - i a₁) =
        (σ • h.sec c - h.sec c) - i (σ • a₁ - a₁) by rw [map_sub]; abel]
      rw [ha₁, h.i_preim, sub_self]
    refine ⟨TateH0.mk σ hb, ?_⟩
    rw [tateH0Map_mk, TateH0.mk_eq_mk_iff]
    refine ⟨0, ?_⟩
    rw [map_zero, map_sub, h.p_sec, h.p_eq_zero_of_mem_range, sub_zero, sub_self]
  · rintro ⟨s, rfl⟩
    obtain ⟨b, hb, rfl⟩ := TateH0.mk_surjective s
    rw [AddMonoidHom.mem_ker, tateH0Map_mk, delta0_mk, TateH1.mk_eq_zero_iff]
    have hb₁ : p (h.sec (p b) - b) = 0 := by rw [map_sub, h.p_sec, sub_self]
    refine ⟨h.preim hb₁, ?_⟩
    refine (h.preim_eq _ ?_).symm
    rw [map_sub, map_smul, h.i_preim]
    rw [show h.sec (p b) = b + (h.sec (p b) - b) by abel]
    rw [smul_add, hb]
    abel

/-- Exactness at `Ĥ¹(A)`. -/
theorem ker_tateH1Map_i (σ : G) : (tateH1Map i σ).ker = (h.delta0 σ).range := by
  ext t
  constructor
  · intro ht
    obtain ⟨a, ha, rfl⟩ := TateH1.mk_surjective t
    rw [AddMonoidHom.mem_ker, tateH1Map_mk, TateH1.mk_eq_zero_iff] at ht
    obtain ⟨b, hbeq⟩ := ht
    have hc : σ • p b = p b := by
      rw [← map_smul, ← sub_eq_zero, ← map_sub, hbeq, h.p_eq_zero_of_mem_range]
    refine ⟨TateH0.mk σ hc, ?_⟩
    rw [delta0_mk, TateH1.mk_eq_mk_iff]
    have hb₁ : p (h.sec (p b) - b) = 0 := by rw [map_sub, h.p_sec, sub_self]
    refine ⟨h.preim hb₁, h.inj ?_⟩
    rw [map_sub, map_smul, h.i_preim, map_sub, h.i_preim]
    rw [show h.sec (p b) = b + (h.sec (p b) - b) by abel, smul_add]
    rw [show σ • b = i a + b by rw [← hbeq]; abel]
    abel
  · rintro ⟨s, rfl⟩
    obtain ⟨c, hc, rfl⟩ := TateH0.mk_surjective s
    rw [AddMonoidHom.mem_ker, delta0_mk, tateH1Map_mk, TateH1.mk_eq_zero_iff]
    exact ⟨h.sec c, by rw [h.i_preim]⟩

/-- Exactness at `Ĥ¹(B)`. -/
theorem ker_tateH1Map_p (σ : G) : (tateH1Map p σ).ker = (tateH1Map i σ).range := by
  ext t
  constructor
  · intro ht
    obtain ⟨b, hb, rfl⟩ := TateH1.mk_surjective t
    rw [AddMonoidHom.mem_ker, tateH1Map_mk, TateH1.mk_eq_zero_iff] at ht
    obtain ⟨c', hc'⟩ := ht
    have hx : p (b - (σ • h.sec c' - h.sec c')) = 0 := by
      rw [map_sub, map_sub, map_smul, h.p_sec, hc', sub_self]
    have ha : normHom G A (h.preim hx) = 0 := by
      refine h.inj ?_
      rw [map_normHom, h.i_preim, map_zero, map_sub, hb,
        show normHom G B (σ • h.sec c' - h.sec c') = 0 from normHom_subHom σ (h.sec c'),
        sub_zero]
    refine ⟨TateH1.mk σ ha, ?_⟩
    rw [tateH1Map_mk, TateH1.mk_eq_mk_iff]
    refine ⟨-h.sec c', ?_⟩
    rw [h.i_preim, smul_neg]
    abel
  · rintro ⟨s, rfl⟩
    obtain ⟨a, ha, rfl⟩ := TateH1.mk_surjective s
    rw [AddMonoidHom.mem_ker, tateH1Map_mk, tateH1Map_mk, TateH1.mk_eq_zero_iff]
    exact ⟨0, by rw [smul_zero, sub_zero, h.p_eq_zero_of_mem_range]⟩

/-- Exactness at `Ĥ¹(C)`. -/
theorem ker_delta1 (σ : G) : (h.delta1 σ).ker = (tateH1Map p σ).range := by
  ext t
  constructor
  · intro ht
    obtain ⟨c, hc, rfl⟩ := TateH1.mk_surjective t
    rw [AddMonoidHom.mem_ker, delta1_mk, TateH0.mk_eq_zero_iff] at ht
    obtain ⟨a', ha'⟩ := ht
    have hb : normHom G B (h.sec c - i a') = 0 := by
      rw [map_sub, ← map_normHom, ha', h.i_preim, sub_self]
    refine ⟨TateH1.mk σ hb, ?_⟩
    rw [tateH1Map_mk, TateH1.mk_eq_mk_iff]
    refine ⟨0, ?_⟩
    rw [smul_zero, sub_zero, map_sub, h.p_sec, h.p_eq_zero_of_mem_range, sub_zero, sub_self]
  · rintro ⟨s, rfl⟩
    obtain ⟨b, hb, rfl⟩ := TateH1.mk_surjective s
    rw [AddMonoidHom.mem_ker, tateH1Map_mk, delta1_mk, TateH0.mk_eq_zero_iff]
    have hb₁ : p (h.sec (p b) - b) = 0 := by rw [map_sub, h.p_sec, sub_self]
    refine ⟨h.preim hb₁, ?_⟩
    refine (h.preim_eq _ ?_).symm
    rw [map_normHom, h.i_preim, map_sub, hb, sub_zero]

/-- Exactness at `Ĥ⁰(A)`. -/
theorem ker_tateH0Map_i (σ : G) : (tateH0Map i σ).ker = (h.delta1 σ).range := by
  ext t
  constructor
  · intro ht
    obtain ⟨a, ha, rfl⟩ := TateH0.mk_surjective t
    rw [AddMonoidHom.mem_ker, tateH0Map_mk, TateH0.mk_eq_zero_iff] at ht
    obtain ⟨b, hbeq⟩ := ht
    have hc : normHom G C (p b) = 0 := by
      rw [← map_normHom, hbeq, h.p_eq_zero_of_mem_range]
    refine ⟨TateH1.mk σ hc, ?_⟩
    rw [delta1_mk, TateH0.mk_eq_mk_iff]
    have hb₁ : p (h.sec (p b) - b) = 0 := by rw [map_sub, h.p_sec, sub_self]
    refine ⟨h.preim hb₁, h.inj ?_⟩
    simp only [map_sub, map_normHom, h.i_preim]
    rw [← hbeq]
  · rintro ⟨s, rfl⟩
    obtain ⟨c, hc, rfl⟩ := TateH1.mk_surjective s
    rw [AddMonoidHom.mem_ker, delta1_mk, tateH0Map_mk, TateH0.mk_eq_zero_iff]
    exact ⟨h.sec c, by rw [h.i_preim]⟩

end IsShortExact

end CyclicTate
