/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc

/-!

# Weierstrass preparation theorem for power series over a complete local ring

In this file we assume that a ring is adic complete with respect to some ideal.
If such ideal is a maximal ideal, then by `isLocalRing_of_isAdicComplete_maximal`,
such ring has only on maximal ideal, and hence such ring is a complete local ring.

Consider using results in <https://github.com/leanprover-community/mathlib4/pull/21944> instead.

-/

open scoped Polynomial PowerSeries

namespace PowerSeries

/-!

## Weierstrass division

-/

/-- A `Prop` which asserts that a power series `q` and a polynomial `r` of degree `< n` satisfy
`f = g * q + r`, where `n` is the order of the image of `g` in `(A / I)⟦X⟧` (defined to be
zero if such image is zero, in which case it's mathematically not considered). -/
def IsWeierstrassDivisionAt
    {A : Type*} [CommRing A]
    (f g q : A⟦X⟧) (r : A[X]) (I : Ideal A) : Prop :=
  r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat ∧ f = g * q + r

/-- Version of `IsWeierstrassDivisionAt` for local rings with respect to its maximal ideal. -/
abbrev IsWeierstrassDivision
    {A : Type*} [CommRing A] [IsLocalRing A]
    (f g q : A⟦X⟧) (r : A[X]) : Prop :=
  f.IsWeierstrassDivisionAt g q r (IsLocalRing.maximalIdeal A)

theorem isWeierstrassDivisionAt_zero
    {A : Type*} [CommRing A]
    (g : A⟦X⟧) (I : Ideal A) : IsWeierstrassDivisionAt 0 g 0 0 I := by
  constructor
  · rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · simp

section Private

variable {A : Type*} [CommRing A] (I : Ideal A)

theorem eq_shift_mul_X_pow_add_trunc (n : ℕ) (f : A⟦X⟧) :
    f = (mk fun i ↦ coeff A (i + n) f) * X ^ n + (f.trunc n : A⟦X⟧) := by
  ext j
  rw [map_add, Polynomial.coeff_coe, coeff_mul_X_pow', coeff_trunc]
  simp_rw [← not_le]
  split_ifs with h <;> simp [h]

theorem eq_X_pow_mul_shift_add_trunc (n : ℕ) (f : A⟦X⟧) :
    f = X ^ n * (mk fun i ↦ coeff A (i + n) f) + (f.trunc n : A⟦X⟧) := by
  rw [← (commute_X_pow _ n).eq, ← eq_shift_mul_X_pow_add_trunc]

theorem map_eq_zero_iff_coeff_mem_ker {B : Type*} [CommRing B] (f : A⟦X⟧)
    (g : A →+* B) : f.map g = 0 ↔ ∀ i, coeff A i f ∈ RingHom.ker g := by
  rw [PowerSeries.ext_iff]
  simp_rw [map_zero, coeff_map, RingHom.mem_ker]

variable {I} in
theorem coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal
    {J : Ideal A} (f g : A⟦X⟧) (n : ℕ) (hf : ∀ i ≤ n, coeff A i f ∈ I)
    (hg : ∀ i ≤ n, coeff A i g ∈ J) : ∀ i ≤ n, coeff A i (f * g) ∈ I * J := fun i hi ↦ by
  rw [coeff_mul]
  exact Ideal.sum_mem _ fun p hp ↦ Ideal.mul_mem_mul
    (hf _ ((Finset.antidiagonal.fst_le hp).trans hi))
    (hg _ ((Finset.antidiagonal.snd_le hp).trans hi))

variable {I} in
theorem coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'
    {J : Ideal A} (f g : A⟦X⟧) (hf : ∀ i, coeff A i f ∈ I)
    (hg : ∀ i, coeff A i g ∈ J) : ∀ i, coeff A i (f * g) ∈ I * J :=
  fun i ↦ f.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal g i
    (fun i _ ↦ hf i) (fun i _ ↦ hg i) i le_rfl

variable {I} in
theorem coeff_mul_mem_ideal_of_coeff_left_mem_ideal
    (f g : A⟦X⟧) (n : ℕ) (hf : ∀ i ≤ n, coeff A i f ∈ I) : ∀ i ≤ n, coeff A i (f * g) ∈ I := by
  simpa using f.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (J := ⊤) g n hf (by simp)

variable {I} in
theorem coeff_mul_mem_ideal_of_coeff_right_mem_ideal
    (f g : A⟦X⟧) (n : ℕ) (hg : ∀ i ≤ n, coeff A i g ∈ I) : ∀ i ≤ n, coeff A i (f * g) ∈ I := by
  simpa using f.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (I := ⊤) g n (by simp) hg

variable {I} in
theorem coeff_mul_mem_ideal_of_coeff_left_mem_ideal'
    (f g : A⟦X⟧) (hf : ∀ i, coeff A i f ∈ I) : ∀ i, coeff A i (f * g) ∈ I := by
  simpa using f.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (J := ⊤) g hf (by simp)

variable {I} in
theorem coeff_mul_mem_ideal_of_coeff_right_mem_ideal'
    (f g : A⟦X⟧) (hg : ∀ i, coeff A i g ∈ I) : ∀ i, coeff A i (f * g) ∈ I := by
  simpa using f.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (I := ⊤) g (by simp) hg

/-- The data used to construct Weierstrass division. -/
structure WeierstrassDivisionData where
  (n : ℕ) (g f : A⟦X⟧) (coeff_g_of_lt : ∀ i < n, coeff A i g ∈ I)
  (isUnit_coeff_g : IsUnit (coeff A n g))

/-- Construct a `WeierstrassDivisionData` from power series `f`, `g` over a local ring such that
the image of `g` in the residue field is not zero. -/
@[simps n g f]
noncomputable def WeierstrassDivisionData.ofMapResidueNeZero [IsLocalRing A]
    (f g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    WeierstrassDivisionData (IsLocalRing.maximalIdeal A) where
  n := (g.map (IsLocalRing.residue A)).order.toNat
  g := g
  f := f
  coeff_g_of_lt i hi := by
    simpa only [coeff_map, IsLocalRing.residue_eq_zero_iff] using coeff_of_lt_order_toNat _ hi
  isUnit_coeff_g := by
    rw [← IsLocalRing.not_mem_maximalIdeal]
    have h := coeff_order hg
    contrapose! h
    rwa [coeff_map, IsLocalRing.residue_eq_zero_iff]

variable {I}
variable (S : WeierstrassDivisionData I)

namespace WeierstrassDivisionData

/-- The `g₀` is `∑ i < n, coeff g i * X ^ i`. -/
noncomputable def g₀ := S.g.trunc S.n

/-- The `g₁` is `∑ i, coeff g (i + n) * X ^ i`. -/
noncomputable def g₁ := PowerSeries.mk fun i ↦ coeff A (i + S.n) S.g

theorem g_eq : S.g = (S.g₀ : A⟦X⟧) + X ^ S.n * S.g₁ := by
  rw [S.g.eq_X_pow_mul_shift_add_trunc S.n, g₀, g₁]; ring

theorem degree_g₀_lt : S.g₀.degree < S.n := S.g.degree_trunc_lt _

theorem coeff_g₀_mem : ∀ i, S.g₀.coeff i ∈ I := fun i ↦ by
  rw [g₀, coeff_trunc]
  split_ifs with h
  · exact S.coeff_g_of_lt i h
  · simp

theorem isUnit_g₁ : IsUnit S.g₁ := by
  simp_rw [g₁, isUnit_iff_constantCoeff, constantCoeff_mk, zero_add, S.isUnit_coeff_g]

/-- The `f₀` is `∑ i < n, coeff f i * X ^ i`. -/
noncomputable def f₀ := S.f.trunc S.n

/-- The `f₁` is `∑ i, coeff f (i + n) * X ^ i`. -/
noncomputable def f₁ := PowerSeries.mk fun i ↦ coeff A (i + S.n) S.f

theorem f_eq : S.f = (S.f₀ : A⟦X⟧) + X ^ S.n * S.f₁ := by
  rw [S.f.eq_X_pow_mul_shift_add_trunc S.n, f₀, f₁]; ring

theorem degree_f₀_lt : S.f₀.degree < S.n := S.f.degree_trunc_lt _

theorem order_eq (hI : I ≠ ⊤) : (S.g.map (Ideal.Quotient.mk I)).order = S.n := by
  simp_rw [order_eq_nat, coeff_map, S.g_eq, map_add, Polynomial.coeff_coe,
    Ideal.Quotient.eq_zero_iff_mem.2 (S.coeff_g₀_mem _), zero_add]
  refine ⟨?_, fun i hi ↦ ?_⟩
  · nth_rw 1 [← zero_add S.n]
    rw [coeff_X_pow_mul, coeff_zero_eq_constantCoeff]
    contrapose! hI
    ext x
    simp only [Submodule.mem_top, iff_true]
    suffices 1 ∈ I by simpa using I.mul_mem_left x this
    rw [Ideal.Quotient.eq_zero_iff_mem] at hI
    simpa using I.mul_mem_left (isUnit_constantCoeff _ S.isUnit_g₁).unit.inv hI
  · rw [Ideal.Quotient.eq_zero_iff_mem]
    refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal _ _ i (fun j hj ↦ ?_) i le_rfl
    simp_rw [coeff_X_pow, if_neg (lt_of_le_of_lt hj hi).ne, zero_mem]

theorem order_toNat_eq (hI : I ≠ ⊤) : (S.g.map (Ideal.Quotient.mk I)).order.toNat = S.n := by
  simpa using congr($(S.order_eq hI).toNat)

/-- The inductively constructed sequence `qₖ` in the proof of Weierstrass division. -/
noncomputable def seq (S : WeierstrassDivisionData I) : ℕ → A⟦X⟧
  | 0 => 0
  | k + 1 =>
    S.seq k + (PowerSeries.mk fun i ↦ coeff A (i + S.n) (S.f - S.g * S.seq k)) * S.isUnit_g₁.unit⁻¹

theorem coeff_seq_mem (k : ℕ) : ∀ i ≥ S.n, coeff A i (S.f - S.g * S.seq k) ∈ I ^ k := by
  induction k with
  | zero => simp
  | succ k hq =>
    rw [seq]
    set q := S.seq k
    set s := S.f - S.g * q
    have hs := s.eq_X_pow_mul_shift_add_trunc S.n
    set s₀ := s.trunc S.n
    set s₁ := PowerSeries.mk fun i ↦ coeff A (i + S.n) s
    set q' := q + s₁ * S.isUnit_g₁.unit⁻¹
    have key : S.f - S.g * q' = (s₀ : A⟦X⟧) - (S.g₀ : A⟦X⟧) * s₁ * S.isUnit_g₁.unit⁻¹ := by
      trans s + S.g * (q - q')
      · simp_rw [s]; ring
      simp_rw [q']
      rw [sub_add_cancel_left, mul_neg, ← mul_assoc, mul_right_comm, S.g_eq, add_mul, mul_assoc,
        IsUnit.mul_val_inv, hs]
      ring
    intro i hi
    rw [key, map_sub, Polynomial.coeff_coe, coeff_trunc, if_neg hi.not_lt, zero_sub, neg_mem_iff,
      pow_succ']
    refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' _ _ (fun i ↦ ?_) i
    refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' _ _
      (by simp [S.coeff_g₀_mem]) (fun i ↦ ?_) i
    rw [coeff_mk]
    exact hq (i + S.n) (by simp)

theorem coeff_seq_succ_sub_seq_mem (k : ℕ) : ∀ i, coeff A i (S.seq (k + 1) - S.seq k) ∈ I ^ k := by
  simp_rw [seq, add_sub_cancel_left]
  refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' _ _ fun i ↦ ?_
  rw [coeff_mk]
  exact S.coeff_seq_mem k (i + S.n) (by simp)

@[simp]
theorem seq_zero : S.seq 0 = 0 := rfl

theorem seq_one : S.seq 1 = S.f₁ * S.isUnit_g₁.unit⁻¹ := by
  simp_rw [seq, mul_zero, zero_add, sub_zero, f₁]

/-- The (bundled version of) coefficient of the limit `q` of the
inductively constructed sequence `qₖ` in the proof of Weierstrass division. -/
noncomputable def divCoeff [IsPrecomplete I A] (i : ℕ) :=
  Classical.indefiniteDescription _ <| IsPrecomplete.prec' (I := I)
    (fun k ↦ coeff A i (S.seq k)) fun {m} {n} hn ↦ by
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ n hn ih =>
        refine ih.trans (SModEq.symm ?_)
        simp_rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← map_sub]
        exact Ideal.pow_le_pow_right hn (S.coeff_seq_succ_sub_seq_mem n i)

/-- The limit `q` of the
inductively constructed sequence `qₖ` in the proof of Weierstrass division. -/
noncomputable def div [IsPrecomplete I A] : A⟦X⟧ :=
  PowerSeries.mk fun i ↦ (S.divCoeff i).1

theorem coeff_div [IsPrecomplete I A] : ∀ i, coeff A i S.div = (S.divCoeff i).1 := by
  simp [div]

theorem coeff_div_sub_seq_mem [IsPrecomplete I A] (k : ℕ) :
    ∀ i, coeff A i (S.div - (S.seq k)) ∈ I ^ k := fun i ↦ by
  rw [map_sub, coeff_div]
  simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using ((S.divCoeff i).2 k).symm

/-- The remainder `r` in the proof of Weierstrass division. -/
noncomputable def mod [IsPrecomplete I A] : A[X] :=
  (S.f - S.g * S.div).trunc S.n

theorem degree_mod_lt [IsPrecomplete I A] : S.mod.degree < S.n := degree_trunc_lt _ _

theorem coeff_f_sub_mod_mem [IsPrecomplete I A] :
    ∀ i < S.n, coeff A i (S.f - S.mod) ∈ I := fun i hi ↦ by
  rw [mod, map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hi, map_sub, sub_sub_cancel]
  refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal _ _ i (fun j hj ↦ ?_) i le_rfl
  exact S.coeff_g_of_lt _ (lt_of_le_of_lt hj hi)

theorem isWeierstrassDivisionAt_div_mod [IsAdicComplete I A] :
    S.f.IsWeierstrassDivisionAt S.g S.div S.mod I := by
  rcases eq_or_ne I ⊤ with rfl | hI
  · have := ‹IsAdicComplete ⊤ A›.toIsHausdorff.subsingleton
    rw [Subsingleton.elim S.f 0, Subsingleton.elim S.div 0, Subsingleton.elim S.mod 0]
    exact S.g.isWeierstrassDivisionAt_zero _
  constructor
  · rw [S.order_toNat_eq hI]
    exact degree_trunc_lt _ _
  · rw [mod, add_comm, ← sub_eq_iff_eq_add]
    ext i
    by_cases hi : i < S.n
    · simp [coeff_trunc, hi]
    rw [Polynomial.coeff_coe, coeff_trunc, if_neg hi]
    refine IsHausdorff.haus' (I := I) _ fun k ↦ ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, show S.f - S.g * S.div =
      S.f - S.g * (S.seq k) - S.g * (S.div - (S.seq k)) by ring, map_sub]
    exact Ideal.sub_mem _ (S.coeff_seq_mem k _ (not_lt.1 hi)) <|
      coeff_mul_mem_ideal_of_coeff_right_mem_ideal' _ _ (S.coeff_div_sub_seq_mem k) i

/-- If `g * q = r` for some power series `q` and some polynomial `r` whose degree is `< n`,
then `q` and `r` are all zero. This implies the uniqueness of Weierstrass division. -/
theorem eq_zero_of_mul_eq [IsHausdorff I A]
    {q : A⟦X⟧} {r : A[X]} (hdeg : r.degree < S.n) (heq : S.g * q = r) : q = 0 ∧ r = 0 := by
  suffices ∀ k i, coeff A i q ∈ I ^ k by
    have hq : q = 0 := by
      ext i
      refine IsHausdorff.haus' (I := I) _ fun k ↦ ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact this _ _
    rw [hq, mul_zero, Eq.comm, Polynomial.coe_eq_zero_iff] at heq
    exact ⟨hq, heq⟩
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [S.g_eq] at heq
    have h1 : ∀ i, coeff A i r ∈ I ^ (k + 1) := fun i ↦ by
      rcases lt_or_le i S.n with hi | hi
      · rw [← heq, pow_succ']
        refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal _ _ i (fun j hj ↦ ?_)
          (fun j _ ↦ ih j) i le_rfl
        rw [map_add, Polynomial.coeff_coe]
        refine Ideal.add_mem _ (S.coeff_g₀_mem _) ?_
        simp_rw [coeff_X_pow_mul', if_neg (lt_of_le_of_lt hj hi).not_le, zero_mem]
      simp_rw [Polynomial.coeff_coe,
        Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by simpa)), zero_mem]
    rw [add_mul, add_comm, ← eq_sub_iff_add_eq] at heq
    replace heq := congr($heq * S.isUnit_g₁.unit⁻¹)
    rw [mul_right_comm, mul_assoc _ S.g₁, IsUnit.mul_val_inv, mul_one] at heq
    intro i
    rw [← coeff_X_pow_mul _ S.n i, heq]
    refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' _ _ (fun i ↦ ?_) _
    rw [map_sub]
    refine Ideal.sub_mem _ (h1 _) ?_
    rw [pow_succ']
    refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' _ _ (fun i ↦ ?_) ih _
    simp_rw [Polynomial.coeff_coe, S.coeff_g₀_mem]

/-- If `g * q + r = g * q' + r'` for some power series `q`, `q'` and some polynomials `r`, `r'`
whose degrees are `< n`, then `q = q'` and `r = r'` are all zero.
This implies the uniqueness of Weierstrass division. -/
theorem eq_of_mul_add_eq_mul_add [IsHausdorff I A]
    {q q' : A⟦X⟧} {r r' : A[X]}
    (hr : r.degree < S.n) (hr' : r'.degree < S.n)
    (heq : S.g * q + r = S.g * q' + r') : q = q' ∧ r = r' := by
  replace heq : S.g * (q - q') = ↑(r' - r) := by
    rw [← eq_sub_iff_add_eq] at heq
    rw [Polynomial.coe_sub, mul_sub, heq]
    ring
  have h := S.eq_zero_of_mul_eq (lt_of_le_of_lt (r'.degree_sub_le r) (max_lt hr' hr)) heq
  simp_rw [sub_eq_zero] at h
  exact ⟨h.1, h.2.symm⟩

end WeierstrassDivisionData

end Private

/-- **Weierstrass division**: let `f`, `g` be power series over a complete local ring, such that
the image of `g` in the residue field is not zero. Let `n` be the order of the image of `g` in the
residue field. Then there exists a power series `q` and a polynomial `r` of degree `< n`, such that
`f = g * q + r`. -/
theorem exists_isWeierstrassDivision
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    ∃ q r, f.IsWeierstrassDivision g q r :=
  ⟨_, _, (WeierstrassDivisionData.ofMapResidueNeZero f g hg).isWeierstrassDivisionAt_div_mod⟩

-- Unfortunately there is no Unicode subscript `w`.

/-- The `q` in Werierstrass division, denoted by `f /ʷ g`. Note that when the image of `g` in the
residue field is zero, this is defined to be zero. -/
noncomputable def weierstrassDiv
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f g : A⟦X⟧) : A⟦X⟧ :=
  open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) ≠ 0 then
    (f.exists_isWeierstrassDivision g hg).choose
  else
    0

/-- The `r` in Werierstrass division, denoted by `f %ʷ g`. Note that when the image of `g` in the
residue field is zero, this is defined to be zero. -/
noncomputable def weierstrassMod
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f g : A⟦X⟧) : A[X] :=
  open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) ≠ 0 then
    (f.exists_isWeierstrassDivision g hg).choose_spec.choose
  else
    0

@[inherit_doc]
infixl:70 " /ʷ " => weierstrassDiv

@[inherit_doc]
infixl:70 " %ʷ " => weierstrassMod

@[simp]
theorem weierstrassDiv_zero_right
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f : A⟦X⟧) : f /ʷ 0 = 0 := by
  rw [weierstrassDiv, dif_neg (by simp)]

@[simp]
theorem weierstrassMod_zero_right
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f : A⟦X⟧) : f %ʷ 0 = 0 := by
  rw [weierstrassMod, dif_neg (by simp)]

theorem degree_weierstrassMod_lt
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f g : A⟦X⟧) : (f %ʷ g).degree < (g.map (IsLocalRing.residue A)).order.toNat := by
  rw [weierstrassMod]
  split_ifs with hg
  · exact (f.exists_isWeierstrassDivision g hg).choose_spec.choose_spec.1
  · nontriviality A
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _

theorem isWeierstrassDivision_weierstrassDiv_weierstrassMod
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    f.IsWeierstrassDivision g (f /ʷ g) (f %ʷ g) := by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact (f.exists_isWeierstrassDivision g hg).choose_spec.choose_spec

theorem eq_mul_weierstrassDiv_add_weierstrassMod
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    f = g * (f /ʷ g) + (f %ʷ g) := by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact (f.exists_isWeierstrassDivision g hg).choose_spec.choose_spec.2

/-- The `q` and `r` in the Weierstrass division for `0` is equal to `0`. -/
theorem eq_zero_of_weierstrass_division
    {A : Type*} [CommRing A] [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0)
    {q : A⟦X⟧} {r : A[X]}
    (hr : r.degree < (g.map (IsLocalRing.residue A)).order.toNat)
    (heq : g * q = r) : q = 0 ∧ r = 0 :=
  (WeierstrassDivisionData.ofMapResidueNeZero 0 g hg).eq_zero_of_mul_eq hr heq

/-- The `q` and `r` in the Weierstrass division is unique. -/
theorem eq_of_weierstrass_division
    {A : Type*} [CommRing A] [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0)
    {q q' : A⟦X⟧} {r r' : A[X]}
    (hr : r.degree < (g.map (IsLocalRing.residue A)).order.toNat)
    (hr' : r'.degree < (g.map (IsLocalRing.residue A)).order.toNat)
    (heq : g * q + r = g * q' + r') : q = q' ∧ r = r' :=
  (WeierstrassDivisionData.ofMapResidueNeZero 0 g hg).eq_of_mul_add_eq_mul_add hr hr' heq

/-- The `q` and `r` in the Weierstrass division is unique. -/
theorem IsWeierstrassDivision.elim
    {A : Type*} [CommRing A] [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {f g : A⟦X⟧} (hg : g.map (IsLocalRing.residue A) ≠ 0)
    {q q' : A⟦X⟧} {r r' : A[X]}
    (H1 : f.IsWeierstrassDivision g q r)
    (H2 : f.IsWeierstrassDivision g q' r') : q = q' ∧ r = r' :=
  g.eq_of_weierstrass_division hg H1.1 H2.1 (H1.2.symm.trans H2.2)

/-- The `q` and `r` in the Weierstrass division for `0` is equal to `0`. -/
theorem IsWeierstrassDivision.eq_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {g : A⟦X⟧} (hg : g.map (IsLocalRing.residue A) ≠ 0)
    {q : A⟦X⟧} {r : A[X]}
    (H : IsWeierstrassDivision 0 g q r) : q = 0 ∧ r = 0 :=
  H.elim hg (g.isWeierstrassDivisionAt_zero _)

/-- The `q` and `r` in the Weierstrass division is equal to `f /ʷ g` and `f %ʷ g`. -/
theorem IsWeierstrassDivision.eq_weierstrassDiv_weierstrassMod
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {f g : A⟦X⟧} (hg : g.map (IsLocalRing.residue A) ≠ 0)
    {q : A⟦X⟧} {r : A[X]}
    (H : f.IsWeierstrassDivision g q r) : q = f /ʷ g ∧ r = f %ʷ g :=
  H.elim hg (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod g hg)

@[simp]
theorem weierstrassDiv_zero_left
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) : 0 /ʷ g = 0 := by
  by_cases hg : g.map (IsLocalRing.residue A) ≠ 0
  · exact ((isWeierstrassDivision_weierstrassDiv_weierstrassMod 0 g hg).eq_zero hg).1
  rw [weierstrassDiv, dif_neg hg]

@[simp]
theorem weierstrassMod_zero_left
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) : 0 %ʷ g = 0 := by
  by_cases hg : g.map (IsLocalRing.residue A) ≠ 0
  · exact ((isWeierstrassDivision_weierstrassDiv_weierstrassMod 0 g hg).eq_zero hg).2
  rw [weierstrassMod, dif_neg hg]

/-!

## Weierstrass preparation theorem

-/

/-- A `Prop` which asserts that `f` is a distingushed polynomial,
`h` is a power series which is a unit, such that `g = f * h`. -/
@[mk_iff]
structure IsWeierstrassFactorization
    {A : Type*} [CommRing A] [IsLocalRing A]
    (g : A⟦X⟧) (f : A[X]) (h : A⟦X⟧) : Prop where
  isDistinguishedAt : f.IsDistinguishedAt (IsLocalRing.maximalIdeal A)
  isUnit : IsUnit h
  eq_mul : g = f * h

theorem IsWeierstrassFactorization.map_ne_zero
    {A : Type*} [CommRing A] [IsLocalRing A]
    {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧}
    (H : g.IsWeierstrassFactorization f h) :
    g.map (IsLocalRing.residue A) ≠ 0 := by
  rw [congr(map (IsLocalRing.residue A) $(H.eq_mul)), map_mul, mul_ne_zero_iff,
    ← Polynomial.polynomial_map_coe, ne_eq, Polynomial.coe_eq_zero_iff]
  exact ⟨f.map_monic_ne_zero H.isDistinguishedAt.monic, (H.isUnit.map _).ne_zero⟩

theorem IsWeierstrassFactorization.degree_eq_order_map
    {A : Type*} [CommRing A] [IsLocalRing A]
    {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧}
    (H : g.IsWeierstrassFactorization f h) :
    f.degree = (g.map (IsLocalRing.residue A)).order := by
  refine H.isDistinguishedAt.degree_eq_order_map g h ?_ H.eq_mul
  rw [IsLocalRing.not_mem_maximalIdeal, ← isUnit_iff_constantCoeff]
  exact H.isUnit

/-- **Weierstrass preparation theorem**: let `g` be a power series over a complete local ring,
such that the image of `g` in the residue field is not zero. Then there exists a distinguished
polynomial `f` and a power series `h` which is a unit, such that `g = f * h`. -/
theorem exists_isWeierstrassFactorization
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    ∃ f h, g.IsWeierstrassFactorization f h := by
  let n := (g.map (IsLocalRing.residue A)).order.toNat
  let S := WeierstrassDivisionData.ofMapResidueNeZero (X ^ n) g hg
  have hu : IsUnit S.div := by
    rw [isUnit_iff_constantCoeff, ← IsLocalRing.not_mem_maximalIdeal]
    have h1 := S.coeff_div_sub_seq_mem 1 0
    rw [pow_one, coeff_zero_eq_constantCoeff, S.seq_one, map_sub, map_mul] at h1
    by_contra h2
    replace h1 := Ideal.sub_mem _ h2 h1
    simp_rw [sub_sub_cancel, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, IsUnit.mul_iff,
      not_and, WeierstrassDivisionData.f₁, constantCoeff_mk, zero_add] at h1
    change IsUnit (coeff A n (X ^ n)) → _ at h1
    simp_rw [coeff_X_pow_self, isUnit_one, forall_const] at h1
    exact h1 (by simp_rw [← isUnit_iff_constantCoeff, Units.isUnit])
  let f := Polynomial.X ^ n - S.mod
  have hfdeg : f.natDegree = n := by
    suffices f.degree = n by rw [Polynomial.natDegree, this]; rfl
    rw [Polynomial.degree_sub_eq_left_of_degree_lt
      (S.degree_mod_lt.trans_eq (by rw [Polynomial.degree_X_pow]; rfl)), Polynomial.degree_X_pow]
  refine ⟨f, ↑hu.unit⁻¹, ⟨⟨fun {i} hi ↦ ?_⟩, .sub_of_left (Polynomial.monic_X_pow _)
    (S.degree_mod_lt.trans_eq (by rw [Polynomial.degree_X_pow]; rfl))⟩, Units.isUnit _, ?_⟩
  · rw [hfdeg] at hi
    simp_rw [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hi.ne, zero_sub, neg_mem_iff]
    have : coeff A i (X ^ n - _) ∈ _ := S.coeff_f_sub_mod_mem i hi
    rwa [map_sub, coeff_X_pow, if_neg hi.ne, zero_sub, neg_mem_iff, Polynomial.coeff_coe] at this
  · have hWD : (X ^ n).IsWeierstrassDivision g _ _ := S.isWeierstrassDivisionAt_div_mod
    have := congr($(hWD.2) * ↑hu.unit⁻¹)
    rw [add_mul, mul_assoc, IsUnit.mul_val_inv, mul_one, ← sub_eq_iff_eq_add] at this
    simp_rw [← this, f, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, sub_mul]

/-- The `f` in Werierstrass preparation theorem. -/
noncomputable def weierstrassDistinguished
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) : A[X] :=
  (g.exists_isWeierstrassFactorization hg).choose

/-- The `h` in Werierstrass preparation theorem. -/
noncomputable def weierstrassUnit
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) : A⟦X⟧ :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose

theorem isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    g.IsWeierstrassFactorization (g.weierstrassDistinguished hg) (g.weierstrassUnit hg) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec

theorem isDistinguishedAt_weierstrassDistinguished
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    (g.weierstrassDistinguished hg).IsDistinguishedAt (IsLocalRing.maximalIdeal A) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isDistinguishedAt

theorem isUnit_weierstrassUnit
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    IsUnit (g.weierstrassUnit hg) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isUnit

theorem eq_weierstrassDistinguished_mul_weierstrassUnit
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (g : A⟦X⟧) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    g = g.weierstrassDistinguished hg * g.weierstrassUnit hg :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.eq_mul

theorem _root_.PowerSeries.eq_of_X_pow_mul_eq_X_pow
    {A : Type*} [CommRing A] [Nontrivial A] (m n : ℕ) (u : A⟦X⟧) (hu : IsUnit u)
    (h : X ^ m * u = X ^ n) : m = n := by
  rw [isUnit_iff_constantCoeff] at hu
  replace h := congr(coeff A m $h)
  rw [coeff_mul, ← Finset.sum_subset (s₁ := {(m, 0)}) (by simp) (fun p hp hnmem ↦ by
    have hp1 : p.1 ≠ m := by
      contrapose! hnmem
      suffices p = (m, 0) by simp [this]
      rwa [Finset.antidiagonal_congr hp (by simp)]
    rw [coeff_X_pow, if_neg hp1, zero_mul]), Finset.sum_singleton, coeff_X_pow_self,
    coeff_zero_eq_constantCoeff, one_mul, coeff_X_pow] at h
  split_ifs at h with hmn
  · exact hmn
  · exact False.elim (hu.ne_zero h)

theorem _root_.Polynomial.IsDistinguishedAt.natDegree_eq_of_associated_powerSeries
    {A : Type*} [CommRing A] {I : Ideal A} {f g : A[X]}
    (hf : f.IsDistinguishedAt I) (hg : g.IsDistinguishedAt I) (hI : I ≠ ⊤)
    (hfg : Associated (f : A⟦X⟧) (g : A⟦X⟧)) : f.natDegree = g.natDegree := by
  rcases subsingleton_or_nontrivial (A ⧸ I) with h | _
  · apply (Submodule.Quotient.subsingleton_iff _).1 at h
    exact False.elim <| hI <| by ext; simp [h]
  obtain ⟨u, hu⟩ := hfg
  have hu' := congr(PowerSeries.map (Ideal.Quotient.mk I) $hu)
  simp_rw [map_mul, ← Polynomial.polynomial_map_coe, hf.map_eq_X_pow, hg.map_eq_X_pow,
    Polynomial.coe_pow, Polynomial.coe_X] at hu'
  change _ * (RingHom.toMonoidHom _) _ = _ at hu'
  rw [← Units.coe_map] at hu'
  exact PowerSeries.eq_of_X_pow_mul_eq_X_pow _ _ _ (Units.isUnit _) hu'

/-- The `f` and `h` in Werierstrass preparation theorem is unique. -/
theorem IsWeierstrassFactorization.elim
    {A : Type*} [CommRing A] [IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {g : A⟦X⟧} {f f' : A[X]} {h h' : A⟦X⟧}
    (H1 : g.IsWeierstrassFactorization f h)
    (H2 : g.IsWeierstrassFactorization f' h') : f = f' ∧ h = h' := by
  rcases eq_or_ne (IsLocalRing.maximalIdeal A) ⊤ with hI | hI
  · rw [hI] at ‹IsHausdorff _ A›
    have := ‹IsHausdorff _ A›.subsingleton
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have h1 := H1.eq_mul ▸ H2.eq_mul
  replace h1 := congr($h1 * H2.isUnit.unit⁻¹)
  rw [mul_assoc] at h1
  change _ * (H1.isUnit.unit.val * _) = _ at h1
  rw [← Units.val_mul] at h1
  set u := H1.isUnit.unit * H2.isUnit.unit⁻¹
  rw [mul_assoc, IsUnit.mul_val_inv, mul_one] at h1
  have hdeg := H1.isDistinguishedAt.natDegree_eq_of_associated_powerSeries
    H2.isDistinguishedAt hI ⟨u, h1⟩
  have hWD1 : (f' : A⟦X⟧).IsWeierstrassDivision f 1 (f' - f) := by
    refine ⟨?_, by simp⟩
    have hf := H1.isDistinguishedAt.monic.ne_zero
    rw [← Polynomial.polynomial_map_coe, H1.isDistinguishedAt.map_eq_X_pow, Polynomial.coe_pow,
      Polynomial.coe_X, order_X_pow, ENat.toNat_coe, ← Polynomial.degree_neg, neg_sub,
      ← Polynomial.degree_eq_natDegree hf]
    refine Polynomial.degree_sub_lt ?_ hf ?_
    · rw [Polynomial.degree_eq_natDegree hf,
        Polynomial.degree_eq_natDegree H2.isDistinguishedAt.monic.ne_zero, hdeg]
    · rw [H1.isDistinguishedAt.monic.leadingCoeff, H2.isDistinguishedAt.monic.leadingCoeff]
  have hWD2 : (f' : A⟦X⟧).IsWeierstrassDivision f u 0 := by
    refine ⟨?_, by simp [h1]⟩
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  have h2 := hWD1.elim (by
    change map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) _ ≠ _
    rw [← Polynomial.polynomial_map_coe, H1.isDistinguishedAt.map_eq_X_pow]
    simp) hWD2
  sorry

#check MvPowerSeries.X_mem_nonzeroDivisors

end PowerSeries
