/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.Padics.HasBasis
public import Iwasawalib.Topology.Algebra.Group.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section

open Topology

namespace CyclicTower

variable {G H : Type*} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
  [CompactSpace G] [CompactSpace H] [T2Space G] [T2Space H]
  {Q : ℕ → Type*} [∀ n, Group (Q n)] [∀ n, TopologicalSpace (Q n)]
  [∀ n, T2Space (Q n)]

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Compact groups with the same separating surjective system of finite quotients agree. -/
theorem nonempty_equiv_of_quotients
    (r : ∀ n, G →* Q n) (s : ∀ n, H →* Q n)
    (rc : ∀ n, Continuous (r n)) (sc : ∀ n, Continuous (s n))
    (rs : ∀ n, Function.Surjective (r n)) (ss : ∀ n, Function.Surjective (s n))
    (ri : ∀ x y, (∀ n, r n x = r n y) → x = y)
    (si : ∀ x y, (∀ n, s n x = s n y) → x = y)
    (t : ∀ n, Q (n + 1) →* Q n)
    (rt : ∀ n x, t n (r (n + 1) x) = r n x)
    (st : ∀ n x, t n (s (n + 1) x) = s n x) : Nonempty (G ≃ₜ* H) := by
  let R : Subgroup (G × H) := {
    carrier := {x | ∀ n, r n x.1 = s n x.2}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb n
      change r n (a.1 * b.1) = s n (a.2 * b.2)
      simp only [map_mul]
      rw [ha n, hb n]
    inv_mem' := by intro a ha n; change r n a.1⁻¹ = s n a.2⁻¹; simp only [map_inv]; rw [ha n] }
  have hclosed : IsClosed (R : Set (G × H)) := by
    change IsClosed {x : G × H | ∀ n, r n x.1 = s n x.2}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun n ↦ isClosed_eq ((rc n).comp continuous_fst)
      ((sc n).comp continuous_snd)
  let : CompactSpace R := isCompact_iff_compactSpace.mp hclosed.isCompact
  let a : R →* G := (MonoidHom.fst G H).comp R.subtype
  let b : R →* H := (MonoidHom.snd G H).comp R.subtype
  have ai : Function.Injective a := by
    intro x y h
    apply Subtype.ext
    exact Prod.ext h (si _ _ fun n ↦ (x.2 n).symm.trans ((congrArg (r n) h).trans (y.2 n)))
  have bi : Function.Injective b := by
    intro x y h
    apply Subtype.ext
    exact Prod.ext (ri _ _ fun n ↦ (x.2 n).trans ((congrArg (s n) h).trans (y.2 n).symm)) h
  have asurj : Function.Surjective a := by
    intro x
    let S (n : ℕ) : Set H := {y | r n x = s n y}
    have hc (n) : IsClosed (S n) := isClosed_eq continuous_const (sc n)
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
      (fun n y hy ↦ by change r n x = s n y; simpa only [rt, st] using congrArg (t n) hy)
      (fun n ↦ by obtain ⟨y, hy⟩ := ss n (r n x); exact ⟨y, hy.symm⟩)
      (hc 0).isCompact hc
    exact ⟨⟨(x, y), Set.mem_iInter.mp hy⟩, rfl⟩
  have bsurj : Function.Surjective b := by
    intro y
    let S (n : ℕ) : Set G := {x | r n x = s n y}
    have hc (n) : IsClosed (S n) := isClosed_eq (rc n) continuous_const
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
      (fun n x hx ↦ by change r n x = s n y; simpa only [rt, st] using congrArg (t n) hx)
      (fun n ↦ rs n (s n y)) (hc 0).isCompact hc
    exact ⟨⟨(x, y), Set.mem_iInter.mp hx⟩, rfl⟩
  let ea := MulEquiv.ofBijective a ⟨ai, asurj⟩
  let eb := MulEquiv.ofBijective b ⟨bi, bsurj⟩
  have ac : Continuous a := continuous_fst.comp continuous_subtype_val
  have bc : Continuous b := continuous_snd.comp continuous_subtype_val
  let ca : R ≃ₜ* G := { ea with
    continuous_toFun := ac
    continuous_invFun := (ac.homeoOfEquivCompactToT2 (f := ea.toEquiv)).continuous_invFun }
  let cb : R ≃ₜ* H := { eb with
    continuous_toFun := bc
    continuous_invFun := (bc.homeoOfEquivCompactToT2 (f := eb.toEquiv)).continuous_invFun }
  exact ⟨ca.symm.trans cb⟩

omit [IsTopologicalGroup G] in
/-- A compact group separated by cyclic quotients of order p^n is Z_p. -/
theorem nonempty_equiv_padic
    (p : ℕ) [Fact p.Prime]
    [∀ n, Finite (Q n)] [∀ n, DiscreteTopology (Q n)] [∀ n, IsCyclic (Q n)]
    (r : ∀ n, G →* Q n) (rc : ∀ n, Continuous (r n))
    (rs : ∀ n, Function.Surjective (r n))
    (ri : ∀ x y, (∀ n, r n x = r n y) → x = y)
    (t : ∀ n, Q (n + 1) →* Q n)
    (rt : ∀ n x, t n (r (n + 1) x) = r n x)
    (card : ∀ n, Nat.card (Q n) = p ^ n) :
    Nonempty (G ≃ₜ* Multiplicative ℤ_[p]) := by
  classical
  let S (n : ℕ) : Set G := {g | ∀ x, x ∈ Subgroup.zpowers (r n g)}
  have hc (n) : IsClosed (S n) :=
    (isClosed_discrete _ : IsClosed {q : Q n | ∀ x, x ∈ Subgroup.zpowers q}).preimage (rc n)
  have hs (n) : (S n).Nonempty := by
    obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := Q n)
    obtain ⟨g, hg⟩ := rs n q
    exact ⟨g, by simpa only [S, hg, Set.mem_ofPred_eq] using hq⟩
  have hd (n) : S (n + 1) ⊆ S n := by
    intro g hg q
    obtain ⟨x, hx⟩ := rs n q
    obtain ⟨k, hk⟩ := hg (r (n + 1) x)
    exact ⟨k, by simpa only [map_zpow, rt, hx] using congrArg (t n) hk⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hd hs (hc 0).isCompact hc
  have gen (n) : ∀ x, x ∈ Subgroup.zpowers (r n g) := Set.mem_iInter.mp hg n
  let e (n) : Multiplicative (ZMod (p ^ n)) ≃* Q n :=
    zmodMulEquivOfGenerator (gen n) (card n)
  let s (n) : Multiplicative ℤ_[p] →* Q n :=
    (e n).toMonoidHom.comp (AddMonoidHom.toMultiplicative (PadicInt.toZModPow n).toAddMonoidHom)
  let (n : ℕ) : TopologicalSpace (ZMod (p ^ n)) := ⊥
  let (n : ℕ) : DiscreteTopology (ZMod (p ^ n)) := ⟨rfl⟩
  have hcmod (n) : Continuous (PadicInt.toZModPow (p := p) n) := by
    apply (PadicInt.toZModPow n).toAddMonoidHom.continuous_iff.mpr
    intro U hU _
    refine ⟨Ideal.span {(p : ℤ_[p]) ^ n}, Ideal.zero_mem _, PadicInt.isOpen_span_p_pow p n, ?_⟩
    intro x hx
    have hz : PadicInt.toZModPow n x = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
      exact hx
    change PadicInt.toZModPow n x ∈ U
    rwa [hz]
  have sc (n) : Continuous (s n) :=
    (continuous_of_discreteTopology : Continuous (e n)).comp (hcmod n)
  have sint (n) (i : ℤ) : s n (Multiplicative.ofAdd (i : ℤ_[p])) = r n (g ^ i) := by
    simp [s, e]
  have ss (n) : Function.Surjective (s n) := by
    intro q
    let a := Multiplicative.toAdd ((e n).symm q)
    refine ⟨Multiplicative.ofAdd (a.val : ℤ_[p]), ?_⟩
    change e n (Multiplicative.ofAdd (PadicInt.toZModPow n (a.val : ℤ_[p]))) = q
    simp only [map_natCast, ZMod.natCast_zmod_val]
    exact (e n).apply_symm_apply q
  have si (x y : Multiplicative ℤ_[p]) (h : ∀ n, s n x = s n y) : x = y := by
    apply Multiplicative.toAdd.injective
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    exact congrArg Multiplicative.toAdd ((e n).injective (h n))
  have st (n) (x : Multiplicative ℤ_[p]) : t n (s (n + 1) x) = s n x := by
    have hcont : Continuous (fun z : ℤ_[p] ↦ t n (s (n + 1) (Multiplicative.ofAdd z))) :=
      (continuous_of_discreteTopology : Continuous (t n)).comp (sc (n + 1))
    have hsc : Continuous (fun z : ℤ_[p] ↦ s n (Multiplicative.ofAdd z)) := sc n
    have heq := hcont.ext_on PadicInt.denseRange_intCast hsc (by
      rintro z ⟨i, rfl⟩
      change t n (s (n + 1) (Multiplicative.ofAdd (i : ℤ_[p]))) =
        s n (Multiplicative.ofAdd (i : ℤ_[p]))
      rw [sint, sint, rt])
    exact congrFun heq x.toAdd
  exact nonempty_equiv_of_quotients r s rc sc rs ss ri si t rt st

end CyclicTower
