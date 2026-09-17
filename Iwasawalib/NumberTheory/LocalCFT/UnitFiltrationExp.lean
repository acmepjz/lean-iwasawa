/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.AdditiveFiltration

@[expose] public section

/-!
# The exponential of a complete discretely valued field, without series

This file constructs the exponential isomorphism between a sufficiently deep additive
valuation ball and the corresponding unit-filtration subgroup.  The construction uses
compatible iterated `p`-power roots and completeness, without invoking power series.
-/

noncomputable section

open Filter Topology WithZero

namespace LocalCFT

variable {F : Type*} [Field F] [hv : Valued F ℤᵐ⁰]

/-! ## A sharper binomial estimate at a prime -/

/-- **`(1 + z)^p = 1 + p z + O(v z ^ 2)`.**  This is
`LocalCFT.valued_one_add_pow_sub_le_of_prime` with the crude bound `v p ≤ 1` on the middle
coefficients: every term of the expansion beyond the linear one is quadratic in `z`, which is
what makes the successive approximation below converge *geometrically in `a`* rather than one
step at a time. -/
theorem valued_one_add_pow_sub_two_mul {p : ℕ} (hp : p.Prime) {j : ℕ} {z : F}
    (hz : (Valued.v z : ℤᵐ⁰) ≤ exp (-(j : ℤ))) :
    (Valued.v ((1 + z) ^ p - 1 - (p : F) * z) : ℤᵐ⁰) ≤ exp (-(2 * j : ℤ)) := by
  refine valued_one_add_pow_sub_le_of_prime hp z (exp_neg_natCast_le_one j) hz
    (valued_natCast_le_one p) ?_ ?_
  · rw [one_mul, ← exp_add, exp_le_exp]
    omega
  · rw [← exp_nsmul, exp_le_exp, nsmul_eq_mul]
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    have hj : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    nlinarith

/-! ## Iterated `p`-power maps -/

section Iterate

variable {p m e : ℕ}

/-- **`u ↦ u ^ (p ^ a)` carries `U^(j)` into `U^(j + a e)`.** -/
theorem IsPowData.pow_pow_mem (hd : IsPowData F p m e) {j : ℕ} (hj : m ≤ j)
    {u : (integers (F := F))ˣ} (hu : u ∈ unitFiltration j) (a : ℕ) :
    u ^ p ^ a ∈ unitFiltration (F := F) (j + a * e) := by
  induction a with
  | zero => simpa using hu
  | succ a ih =>
      have heq : u ^ p ^ (a + 1) = (u ^ p ^ a) ^ p := by rw [← pow_mul, ← pow_succ]
      have heq2 : j + (a + 1) * e = j + a * e + e := by ring
      rw [heq, heq2]
      exact hd.pow_mem (by omega) ih

/-- **The iterated `p`-power map is exact on levels**: if `v (u - 1) = exp (-c)` exactly then
`v (u ^ (p ^ a) - 1) = exp (-(c + a e))` exactly. -/
theorem IsPowData.valued_pow_pow_sub_one (hd : IsPowData F p m e) {c : ℕ} (hc : m ≤ c)
    {u : (integers (F := F))ˣ}
    (hx : (Valued.v (((u : integers (F := F)) : F) - 1) : ℤᵐ⁰) = exp (-(c : ℤ))) (a : ℕ) :
    (Valued.v ((((u ^ p ^ a : (integers (F := F))ˣ) : integers (F := F)) : F) - 1) : ℤᵐ⁰)
      = exp (-((c : ℤ) + a * e)) := by
  induction a with
  | zero => simpa using hx
  | succ a ih =>
      have ih' : (Valued.v ((((u ^ p ^ a : (integers (F := F))ˣ) : integers (F := F)) : F) - 1)
          : ℤᵐ⁰) = exp (-((c + a * e : ℕ) : ℤ)) := by
        rw [ih]
        congr 1
      have h := hd.valued_pow_sub_one (k := c + a * e) (by omega) ih'
      have heq : (u ^ p ^ a) ^ p = u ^ p ^ (a + 1) := by rw [← pow_mul, ← pow_succ]
      rw [heq] at h
      rw [h]
      congr 1
      push_cast
      ring

/-- **Reflecting a level through the iterated power map**: if `u ∈ U^(m)` and `u ^ (p ^ a)` lies
`a e` steps further down than `N`, then `u` itself lies in `U^(N)`. -/
theorem IsPowData.mem_of_pow_pow_mem (hd : IsPowData F p m e)
    {u : (integers (F := F))ˣ} (hu : u ∈ unitFiltration m) {N a : ℕ}
    (h : u ^ p ^ a ∈ unitFiltration (F := F) (N + a * e)) :
    u ∈ unitFiltration (F := F) N := by
  by_cases h1 : u = 1
  · rw [h1]; exact one_mem _
  have hx0 : ((u : integers (F := F)) : F) - 1 ≠ 0 := by
    intro h0
    refine h1 (Units.ext (Subtype.ext ?_))
    have hh : ((u : integers (F := F)) : F) = 1 := by linear_combination h0
    exact hh
  have hne0 : (Valued.v (((u : integers (F := F)) : F) - 1) : ℤᵐ⁰) ≠ 0 := by simpa using hx0
  obtain ⟨jz, hjz⟩ : ∃ jz : ℤ, (Valued.v (((u : integers (F := F)) : F) - 1) : ℤᵐ⁰) = exp jz :=
    ⟨log _, (exp_log hne0).symm⟩
  have hle : (Valued.v (((u : integers (F := F)) : F) - 1) : ℤᵐ⁰) ≤ exp (-(m : ℤ)) := hu
  rw [hjz, exp_le_exp] at hle
  set c : ℕ := (-jz).toNat with hcdef
  have hcj : ((c : ℤ)) = -jz := Int.toNat_of_nonneg (by omega)
  have hmc : m ≤ c := by omega
  have hxc : (Valued.v (((u : integers (F := F)) : F) - 1) : ℤᵐ⁰) = exp (-(c : ℤ)) := by
    rw [hjz, hcj, neg_neg]
  have hpow := hd.valued_pow_pow_sub_one hmc hxc a
  have hmem : (Valued.v ((((u ^ p ^ a : (integers (F := F))ˣ) : integers (F := F)) : F) - 1)
      : ℤᵐ⁰) ≤ exp (-((N + a * e : ℕ) : ℤ)) := h
  rw [hpow, exp_le_exp] at hmem
  have hNc : N ≤ c := by
    push_cast at hmem
    omega
  rw [mem_unitFiltration, hxc, exp_le_exp]
  omega

/-- **The iterated `p`-power map is injective on `U^(m)`.** -/
theorem IsPowData.pow_pow_injective (hd : IsPowData F p m e)
    {u u' : (integers (F := F))ˣ} (hu : u ∈ unitFiltration m) (hu' : u' ∈ unitFiltration m)
    {a : ℕ} (h : u ^ p ^ a = u' ^ p ^ a) : u = u' := by
  have hs : u / u' ∈ unitFiltration (F := F) m := Subgroup.div_mem _ hu hu'
  have hpow : (u / u') ^ p ^ a = 1 := by rw [div_pow, h, div_self']
  have hall : ∀ N : ℕ, u / u' ∈ unitFiltration (F := F) N := by
    intro N
    have hmem : u / u' ∈ unitFiltration (F := F) (max m N) := by
      refine hd.mem_of_pow_pow_mem hs (a := a) ?_
      rw [hpow]
      exact one_mem _
    exact unitFiltration_mem_of_le (le_max_right m N) hmem
  have hone := unitFiltration_separated hall
  rwa [div_eq_one] at hone

/-- **The iterated `p`-power map carries `U^(j)` onto `U^(j + a e)`.** -/
theorem IsPowData.exists_pow_pow_eq [CompleteSpace F] (hd : IsPowData F p m e) {j : ℕ}
    (hj : m ≤ j) {a : ℕ} {t : (integers (F := F))ˣ}
    (ht : t ∈ unitFiltration (F := F) (j + a * e)) :
    ∃ u ∈ unitFiltration (F := F) j, u ^ p ^ a = t := by
  have himage := hd.image_pow_pow hj a
  have ht' : t ∈ ((unitFiltration (F := F) (j + a * e) : Subgroup _) : Set _) := ht
  rw [← himage] at ht'
  obtain ⟨u, hu, hut⟩ := ht'
  exact ⟨u, hu, hut⟩

end Iterate

/-! ## The exponential data -/

/-- **The hypotheses under which the `p`-adic exponential `𝔪^k → U^(k)` exists.** -/
structure IsExpData (F : Type*) [Field F] [Valued F ℤᵐ⁰] (p e k : ℕ) : Prop where
  /-- `p` is the residue characteristic -/
  prime : p.Prime
  /-- `v p = exp (-e)`: `e` is the absolute ramification index -/
  valued_natCast : (Valued.v ((p : F)) : ℤᵐ⁰) = exp (-(e : ℤ))
  /-- `p` lies in the maximal ideal -/
  one_le : 1 ≤ e
  /-- the exponential converges from level `k` on -/
  lt : e < k


/-! ## Two group identities -/

theorem div_mul_div_cancel_mid {G : Type*} [CommGroup G] (a b c : G) :
    a / b * (b / c) = a / c := by
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm]

theorem div_mul_cancel_mid {G : Type*} [CommGroup G] (a b : G) : a / b * b = a := by
  simp


/-! ## Additive completeness -/

/-- **A sequence whose consecutive differences go to zero converges.**  This is the additive
analogue of `LocalCFT.unitFiltration_complete`, with an offset `c` so that the limit is as close
to `g n` as the tail of the sequence is. -/
theorem exists_limit_of_valued_sub_le [CompleteSpace F] (g : ℕ → F) (c : ℕ)
    (hg : ∀ n : ℕ, (Valued.v (g n - g (n + 1)) : ℤᵐ⁰) ≤ exp (-((c + n : ℕ) : ℤ))) :
    ∃ y : F, ∀ n : ℕ, (Valued.v (y - g n) : ℤᵐ⁰) ≤ exp (-((c + n : ℕ) : ℤ)) := by
  have hdist : ∀ n m : ℕ, n ≤ m → (Valued.v (g n - g m) : ℤᵐ⁰) ≤ exp (-((c + n : ℕ) : ℤ)) := by
    intro n m hnm
    induction m with
    | zero => simp_all
    | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hnm) with h | h
      · have h1 := ih (Nat.lt_succ_iff.1 h)
        have h2 : (Valued.v (g m - g (m + 1)) : ℤᵐ⁰) ≤ exp (-((c + n : ℕ) : ℤ)) := by
          refine le_trans (hg m) ?_
          rw [exp_le_exp]
          have hnm' : n ≤ m := Nat.lt_succ_iff.1 h
          have : c + n ≤ c + m := by omega
          exact_mod_cast neg_le_neg (by exact_mod_cast this)
        have heq : g n - g (m + 1) = (g n - g m) + (g m - g (m + 1)) := by ring
        rw [heq]
        exact le_trans (Valuation.map_add _ _ _) (max_le h1 h2)
      · subst h
        simp
  have hweak : ∀ n m : ℕ, n ≤ m → (Valued.v (g n - g m) : ℤᵐ⁰) ≤ exp (-(n : ℤ)) := by
    intro n m hnm
    refine le_trans (hdist n m hnm) ?_
    rw [exp_le_exp]
    push_cast
    omega
  have hcauchy : Cauchy (Filter.map g Filter.atTop) := by
    rw [Valued.cauchy_iff]
    refine ⟨Filter.map_neBot, fun γ ↦ ?_⟩
    have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
      MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
    obtain ⟨j, hj⟩ : ∃ j : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = exp j :=
      ⟨log _, (exp_log hγ).symm⟩
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (-(N : ℤ)) < j := ⟨(1 - j).toNat, by omega⟩
    refine ⟨g '' (Set.Ici N), Filter.image_mem_map (Filter.Ici_mem_atTop N), ?_⟩
    rintro _ ⟨q, hq, rfl⟩ _ ⟨r, hr, rfl⟩
    rw [Valuation.restrict_lt_iff_lt_embedding, hj]
    have hpq : (Valued.v (g r - g q) : ℤᵐ⁰) ≤ exp (-(N : ℤ)) := by
      have heq : g r - g q = (g N - g q) - (g N - g r) := by ring
      rw [heq]
      exact le_trans (Valuation.map_sub _ _ _) (max_le (hweak N q hq) (hweak N r hr))
    exact lt_of_le_of_lt hpq (exp_lt_exp.2 hN)
  obtain ⟨y₀, hy₀⟩ := CompleteSpace.complete hcauchy
  have htendsto : Filter.Tendsto g Filter.atTop (nhds y₀) := hy₀
  refine ⟨y₀, fun n ↦ ?_⟩
  refine (isClosed_valued_sub_le (g n) (exp (-((c + n : ℕ) : ℤ)))).mem_of_tendsto htendsto ?_
  filter_upwards [Filter.Ici_mem_atTop n] with m hm
  show (Valued.v (g m - g n) : ℤᵐ⁰) ≤ exp (-((c + n : ℕ) : ℤ))
  rw [Valuation.map_sub_swap]
  exact hdist n m hm


theorem mul_div_swap {G : Type*} [CommGroup G] (a b c : G) : a * b / c = b * (a / c) := by
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm]

namespace IsExpData

variable {p e k : ℕ}

theorem one_le_k (hd : IsExpData F p e k) : 1 ≤ k := by
  have h1 := hd.one_le
  have h2 := hd.lt
  omega

theorem isPowData (hd : IsExpData F p e k) : IsPowData F p k e := by
  refine isPowData_prime hd.prime hd.one_le_k hd.valued_natCast ?_
  have hp := hd.prime.two_le
  have h1 : 1 ≤ p - 1 := by omega
  calc e < k := hd.lt
    _ = k * 1 := (mul_one k).symm
    _ ≤ k * (p - 1) := Nat.mul_le_mul_left k h1

theorem valued_pow_mul (hd : IsExpData F p e k) (x : F) (a : ℕ) :
    (Valued.v (((p : F) ^ a) * x) : ℤᵐ⁰) = exp (-((a * e : ℕ) : ℤ)) * Valued.v x := by
  rw [map_mul, map_pow, hd.valued_natCast, ← exp_nsmul, nsmul_eq_mul]
  congr 2
  push_cast
  ring

theorem valued_pow_mul_le (hd : IsExpData F p e k) {x : F} {j : ℕ}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(j : ℤ))) (a : ℕ) :
    (Valued.v (((p : F) ^ a) * x) : ℤᵐ⁰) ≤ exp (-((j + a * e : ℕ) : ℤ)) := by
  rw [hd.valued_pow_mul x a]
  refine le_trans (mul_le_mul' (le_refl (exp (-((a * e : ℕ) : ℤ)))) hx) ?_
  rw [← exp_add, exp_le_exp]
  push_cast
  omega

/-- `1 + p^a x` is a unit lying `a e` steps further down the filtration than `x`. -/
theorem exists_one_add (hd : IsExpData F p e k) {x : F} {j : ℕ} (hj : 1 ≤ j)
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(j : ℤ))) (a : ℕ) :
    ∃ t : (integers (F := F))ˣ, ((t : integers (F := F)) : F) = 1 + (p : F) ^ a * x ∧
      t ∈ unitFiltration (F := F) (j + a * e) := by
  have hle := hd.valued_pow_mul_le hx a
  have hlt : (Valued.v (((p : F) ^ a) * x) : ℤᵐ⁰) < 1 := by
    refine lt_of_le_of_lt hle ?_
    rw [show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm, exp_lt_exp]
    have h1 : 1 ≤ j + a * e := le_trans hj (Nat.le_add_right _ _)
    have h2 : (1 : ℤ) ≤ ((j + a * e : ℕ) : ℤ) := by exact_mod_cast h1
    omega
  exact ⟨oneAddUnit hlt, coe_oneAddUnit hlt, oneAddUnit_mem hlt hle⟩

/-! ## The `p^a`-th roots -/

/-- **There is exactly one `u ∈ U^(k)` with `u ^ (p ^ a) = 1 + p^a x`.** -/
theorem existsUnique_root [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) (a : ℕ) :
    ∃! u : (integers (F := F))ˣ, u ∈ unitFiltration (F := F) k ∧
      (((u ^ p ^ a : (integers (F := F))ˣ) : integers (F := F)) : F) = 1 + (p : F) ^ a * x := by
  obtain ⟨t, htc, htm⟩ := hd.exists_one_add hd.one_le_k hx a
  obtain ⟨u, hu, hut⟩ := hd.isPowData.exists_pow_pow_eq (le_refl k) htm
  refine ⟨u, ⟨hu, by rw [hut, htc]⟩, ?_⟩
  rintro u' ⟨hu', hu'c⟩
  refine hd.isPowData.pow_pow_injective hu' hu (a := a) (Units.ext (Subtype.ext ?_))
  rw [hu'c, hut, htc]

/-- **The `p^a`-th root of `1 + p^a x` inside `U^(k)`.** -/
def root [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) (a : ℕ) : (integers (F := F))ˣ :=
  (hd.existsUnique_root hx a).choose

theorem root_mem [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) (a : ℕ) :
    hd.root hx a ∈ unitFiltration (F := F) k :=
  (hd.existsUnique_root hx a).choose_spec.1.1

@[simp] theorem root_pow [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) (a : ℕ) :
    (((hd.root hx a ^ p ^ a : (integers (F := F))ˣ) : integers (F := F)) : F)
      = 1 + (p : F) ^ a * x :=
  (hd.existsUnique_root hx a).choose_spec.1.2

theorem root_unique [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) {a : ℕ} {u : (integers (F := F))ˣ}
    (hu : u ∈ unitFiltration (F := F) k)
    (hup : (((u ^ p ^ a : (integers (F := F))ˣ) : integers (F := F)) : F)
      = 1 + (p : F) ^ a * x) :
    u = hd.root hx a :=
  (hd.existsUnique_root hx a).choose_spec.2 u ⟨hu, hup⟩

/-- The root at `a = 0` is `1 + x` itself. -/
theorem coe_root_zero [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) :
    ((hd.root hx 0 : integers (F := F)) : F) = 1 + x := by
  have h := hd.root_pow hx 0
  simpa using h

/-- **The root inherits the level of `x`.** -/
theorem root_mem_of_le [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) {j : ℕ}
    (hxj : (Valued.v x : ℤᵐ⁰) ≤ exp (-(j : ℤ))) (a : ℕ) :
    hd.root hx a ∈ unitFiltration (F := F) j := by
  refine hd.isPowData.mem_of_pow_pow_mem (hd.root_mem hx a) (a := a) ?_
  rw [mem_unitFiltration, hd.root_pow hx a, add_sub_cancel_left]
  exact hd.valued_pow_mul_le hxj a

/-! ## Convergence of the roots -/

/-- **Consecutive roots agree to level `a e + (2 j - e)`.**  This is where the *quadratic*
binomial estimate `LocalCFT.valued_one_add_pow_sub_two_mul` is used: the agreement improves by
`e` at every step, so the sequence of roots is Cauchy for the unit filtration. -/
theorem root_div_root_succ [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) {j : ℕ}
    (hxj : (Valued.v x : ℤᵐ⁰) ≤ exp (-(j : ℤ))) (hej : e ≤ j) (a : ℕ) :
    hd.root hx a / hd.root hx (a + 1) ∈ unitFiltration (F := F) (a * e + (2 * j - e)) := by
  have hzv : (Valued.v ((p : F) ^ a * x) : ℤᵐ⁰) ≤ exp (-((j + a * e : ℕ) : ℤ)) :=
    hd.valued_pow_mul_le hxj a
  have hApow : (((hd.root hx a ^ p ^ (a + 1) : (integers (F := F))ˣ) : integers (F := F)) : F)
      = (1 + (p : F) ^ a * x) ^ p := by
    have h1 : hd.root hx a ^ p ^ (a + 1) = (hd.root hx a ^ p ^ a) ^ p := by
      rw [← pow_mul, ← pow_succ]
    rw [h1, coe_units_pow, hd.root_pow hx a]
  have hBpow : (((hd.root hx (a + 1) ^ p ^ (a + 1) : (integers (F := F))ˣ)
      : integers (F := F)) : F) = 1 + (p : F) * ((p : F) ^ a * x) := by
    rw [hd.root_pow hx (a + 1)]
    ring
  have hBval : (Valued.v (1 + (p : F) * ((p : F) ^ a * x)) : ℤᵐ⁰) = 1 := by
    rw [← hBpow]
    exact valued_coe_units _
  have hBne : (1 : F) + (p : F) * ((p : F) ^ a * x) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hBval
    exact zero_ne_one hBval
  have hquot : ((((hd.root hx a / hd.root hx (a + 1)) ^ p ^ (a + 1) : (integers (F := F))ˣ)
      : integers (F := F)) : F) - 1
      = ((1 + (p : F) ^ a * x) ^ p - 1 - (p : F) * ((p : F) ^ a * x))
        / (1 + (p : F) * ((p : F) ^ a * x)) := by
    rw [div_pow, coe_units_div, hApow, hBpow, div_sub_one hBne]
    congr 1
    ring
  have hRv : (Valued.v ((1 + (p : F) ^ a * x) ^ p - 1 - (p : F) * ((p : F) ^ a * x)) : ℤᵐ⁰)
      ≤ exp (-(2 * ((j + a * e : ℕ) : ℤ))) :=
    valued_one_add_pow_sub_two_mul hd.prime hzv
  have hmem : (hd.root hx a / hd.root hx (a + 1)) ^ p ^ (a + 1)
      ∈ unitFiltration (F := F) (2 * (j + a * e)) := by
    rw [mem_unitFiltration, hquot, map_div₀, hBval, div_one]
    refine le_trans hRv (le_of_eq ?_)
    congr 1
  refine hd.isPowData.mem_of_pow_pow_mem
    (Subgroup.div_mem _ (hd.root_mem hx a) (hd.root_mem hx (a + 1))) (a := a + 1) ?_
  refine unitFiltration_mem_of_le ?_ hmem
  have hsucc : (a + 1) * e = a * e + e := by ring
  omega

/-! ## The exponential -/

theorem exists_expUnit [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) :
    ∃ y : (integers (F := F))ˣ, ∀ a : ℕ, y / hd.root hx a ∈ unitFiltration (F := F) a := by
  refine unitFiltration_complete (hd.root hx) fun a ↦ ?_
  refine unitFiltration_mem_of_le ?_
    (hd.root_div_root_succ hx hx (le_of_lt hd.lt) a)
  have he := hd.one_le
  have hek := hd.lt
  have hae : a ≤ a * e := Nat.le_mul_of_pos_right a (by omega)
  omega

/-- **The exponential of `x`**: the limit of the `p^a`-th roots of `1 + p^a x`.

No series is summed.  The `p^a`-th root of `1 + p^a x` inside `U^(k)` exists and is unique by
`LocalCFT.IsExpData.existsUnique_root` — which is the successive-approximation theorem
`LocalCFT.IsPowData.exists_pow_eq` of `UnitFiltrationPow.lean` — and the roots converge because
the binomial error is quadratic. -/
def expUnit [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) : (integers (F := F))ˣ :=
  (hd.exists_expUnit hx).choose

theorem expUnit_div_root_mem [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) (a : ℕ) :
    hd.expUnit hx / hd.root hx a ∈ unitFiltration (F := F) a :=
  (hd.exists_expUnit hx).choose_spec a

/-- Later roots agree with the `a`-th root to level `a e + (2 j - e)`. -/
theorem root_div_root_le [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) {j : ℕ}
    (hxj : (Valued.v x : ℤᵐ⁰) ≤ exp (-(j : ℤ))) (hej : e ≤ j) (a b : ℕ) :
    hd.root hx (a + b) / hd.root hx a ∈ unitFiltration (F := F) (a * e + (2 * j - e)) := by
  induction b with
  | zero =>
      rw [Nat.add_zero, div_self']
      exact one_mem _
  | succ b ih =>
      have hstep : hd.root hx (a + b + 1) / hd.root hx (a + b)
          ∈ unitFiltration (F := F) (a * e + (2 * j - e)) := by
        have h := hd.root_div_root_succ hx hxj hej (a + b)
        have hinv := Subgroup.inv_mem _ h
        rw [inv_div] at hinv
        refine unitFiltration_mem_of_le ?_ hinv
        have hmul : a * e ≤ (a + b) * e := Nat.mul_le_mul_right e (Nat.le_add_right a b)
        omega
      rw [show a + (b + 1) = a + b + 1 from rfl,
        ← div_mul_div_cancel_mid (hd.root hx (a + b + 1)) (hd.root hx (a + b)) (hd.root hx a)]
      exact mul_mem hstep ih

/-- **The exponential agrees with the `a`-th root to level `a e + (2 j - e)`.** -/
theorem expUnit_div_root [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) {j : ℕ}
    (hxj : (Valued.v x : ℤᵐ⁰) ≤ exp (-(j : ℤ))) (hej : e ≤ j) (a : ℕ) :
    hd.expUnit hx / hd.root hx a ∈ unitFiltration (F := F) (a * e + (2 * j - e)) := by
  set N : ℕ := a * e + (2 * j - e) with hN
  have h1 : hd.expUnit hx / hd.root hx (a + N) ∈ unitFiltration (F := F) N :=
    unitFiltration_mem_of_le (Nat.le_add_left N a) (hd.expUnit_div_root_mem hx (a + N))
  have h2 : hd.root hx (a + N) / hd.root hx a ∈ unitFiltration (F := F) N :=
    hd.root_div_root_le hx hxj hej a N
  rw [← div_mul_div_cancel_mid (hd.expUnit hx) (hd.root hx (a + N)) (hd.root hx a)]
  exact mul_mem h1 h2

/-- **The exponential inherits the level of `x`**: `exp (𝔪^j) ⊆ U^(j)` for `j ≥ k`. -/
theorem expUnit_mem [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) {j : ℕ}
    (hxj : (Valued.v x : ℤᵐ⁰) ≤ exp (-(j : ℤ))) (hej : e ≤ j) :
    hd.expUnit hx ∈ unitFiltration (F := F) j := by
  have h1 := hd.expUnit_div_root hx hxj hej j
  have h2 := hd.root_mem_of_le hx hxj j
  rw [← div_mul_cancel_mid (hd.expUnit hx) (hd.root hx j)]
  refine mul_mem (unitFiltration_mem_of_le ?_ h1) h2
  have he := hd.one_le
  have hje : j ≤ j * e := Nat.le_mul_of_pos_right j (by omega)
  omega

/-- **First-order expansion of the exponential**: `exp x ≡ 1 + x` to level `2 j - e`. -/
theorem expUnit_div_one_add [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) {j : ℕ}
    (hxj : (Valued.v x : ℤᵐ⁰) ≤ exp (-(j : ℤ))) (hej : e ≤ j) :
    hd.expUnit hx / hd.root hx 0 ∈ unitFiltration (F := F) (2 * j - e) := by
  have h := hd.expUnit_div_root hx hxj hej 0
  rwa [Nat.zero_mul, Nat.zero_add] at h

/-! ## The exponential is a homomorphism -/

/-- The `a`-th roots are multiplicative up to level `2 k + a e`. -/
theorem root_add_div [CompleteSpace F] (hd : IsExpData F p e k) {x y : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) (hy : (Valued.v y : ℤᵐ⁰) ≤ exp (-(k : ℤ)))
    (hxy : (Valued.v (x + y) : ℤᵐ⁰) ≤ exp (-(k : ℤ))) (a : ℕ) :
    hd.root hxy a / (hd.root hx a * hd.root hy a)
      ∈ unitFiltration (F := F) (2 * k + a * e) := by
  have hBval : (Valued.v (1 + (p : F) ^ a * x) : ℤᵐ⁰) = 1 := by
    rw [← hd.root_pow hx a]
    exact valued_coe_units _
  have hCval : (Valued.v (1 + (p : F) ^ a * y) : ℤᵐ⁰) = 1 := by
    rw [← hd.root_pow hy a]
    exact valued_coe_units _
  have hBne : (1 : F) + (p : F) ^ a * x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hBval
    exact zero_ne_one hBval
  have hCne : (1 : F) + (p : F) ^ a * y ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hCval
    exact zero_ne_one hCval
  have hprodpow : ((((hd.root hx a * hd.root hy a) ^ p ^ a : (integers (F := F))ˣ)
      : integers (F := F)) : F) = (1 + (p : F) ^ a * x) * (1 + (p : F) ^ a * y) := by
    rw [mul_pow]
    push_cast
    rw [← coe_units_pow, ← coe_units_pow, hd.root_pow hx a, hd.root_pow hy a]
  have hquot : ((((hd.root hxy a / (hd.root hx a * hd.root hy a)) ^ p ^ a
      : (integers (F := F))ˣ) : integers (F := F)) : F) - 1
      = (-(((p : F) ^ a * x) * ((p : F) ^ a * y)))
        / ((1 + (p : F) ^ a * x) * (1 + (p : F) ^ a * y)) := by
    rw [div_pow, coe_units_div, hd.root_pow hxy a, hprodpow,
      div_sub_one (mul_ne_zero hBne hCne)]
    congr 1
    ring
  have hxv : (Valued.v ((p : F) ^ a * x) : ℤᵐ⁰) ≤ exp (-((k + a * e : ℕ) : ℤ)) :=
    hd.valued_pow_mul_le hx a
  have hyv : (Valued.v ((p : F) ^ a * y) : ℤᵐ⁰) ≤ exp (-((k + a * e : ℕ) : ℤ)) :=
    hd.valued_pow_mul_le hy a
  have hmem : (hd.root hxy a / (hd.root hx a * hd.root hy a)) ^ p ^ a
      ∈ unitFiltration (F := F) (2 * (k + a * e)) := by
    rw [mem_unitFiltration, hquot, map_div₀, map_mul, hBval, hCval, mul_one, div_one,
      Valuation.map_neg, map_mul]
    refine le_trans (mul_le_mul' hxv hyv) ?_
    rw [← exp_add, exp_le_exp]
    push_cast
    ring_nf
    omega
  refine hd.isPowData.mem_of_pow_pow_mem
    (Subgroup.div_mem _ (hd.root_mem hxy a) (mul_mem (hd.root_mem hx a) (hd.root_mem hy a)))
    (a := a) ?_
  refine unitFiltration_mem_of_le ?_ hmem
  omega

/-- **The exponential is additive.** -/
theorem expUnit_add [CompleteSpace F] (hd : IsExpData F p e k) {x y : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) (hy : (Valued.v y : ℤᵐ⁰) ≤ exp (-(k : ℤ)))
    (hxy : (Valued.v (x + y) : ℤᵐ⁰) ≤ exp (-(k : ℤ))) :
    hd.expUnit hxy = hd.expUnit hx * hd.expUnit hy := by
  have hlev : ∀ a : ℕ, a ≤ a * e + (2 * k - e) := by
    intro a
    have he := hd.one_le
    have hek := hd.lt
    have : a ≤ a * e := Nat.le_mul_of_pos_right a (by omega)
    omega
  have key : ∀ a : ℕ, hd.expUnit hxy / (hd.expUnit hx * hd.expUnit hy)
      ∈ unitFiltration (F := F) a := by
    intro a
    have h1 : hd.expUnit hxy / hd.root hxy a ∈ unitFiltration (F := F) a :=
      unitFiltration_mem_of_le (hlev a)
        (hd.expUnit_div_root hxy hxy (le_of_lt hd.lt) a)
    have h2 : hd.root hxy a / (hd.root hx a * hd.root hy a) ∈ unitFiltration (F := F) a := by
      refine unitFiltration_mem_of_le ?_ (hd.root_add_div hx hy hxy a)
      have : a ≤ a * e := Nat.le_mul_of_pos_right a (by have := hd.one_le; omega)
      omega
    have h3 : hd.root hx a / hd.expUnit hx ∈ unitFiltration (F := F) a := by
      have h := Subgroup.inv_mem _ (unitFiltration_mem_of_le (hlev a)
        (hd.expUnit_div_root hx hx (le_of_lt hd.lt) a))
      rwa [inv_div] at h
    have h4 : hd.root hy a / hd.expUnit hy ∈ unitFiltration (F := F) a := by
      have h := Subgroup.inv_mem _ (unitFiltration_mem_of_le (hlev a)
        (hd.expUnit_div_root hy hy (le_of_lt hd.lt) a))
      rwa [inv_div] at h
    have h5 : (hd.root hx a * hd.root hy a) / (hd.expUnit hx * hd.expUnit hy)
        ∈ unitFiltration (F := F) a := by
      rw [← div_mul_div_comm]
      exact mul_mem h3 h4
    have hchain : hd.expUnit hxy / (hd.expUnit hx * hd.expUnit hy)
        = (hd.expUnit hxy / hd.root hxy a)
          * ((hd.root hxy a / (hd.root hx a * hd.root hy a))
            * ((hd.root hx a * hd.root hy a) / (hd.expUnit hx * hd.expUnit hy))) := by
      rw [div_mul_div_cancel_mid, div_mul_div_cancel_mid]
    rw [hchain]
    exact mul_mem h1 (mul_mem h2 h5)
  have h := unitFiltration_separated key
  rwa [div_eq_one] at h

/-! ## The exponential is injective -/

/-- **The exponential has trivial kernel.** -/
theorem eq_zero_of_expUnit_eq_one [CompleteSpace F] (hd : IsExpData F p e k) {x : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) (h : hd.expUnit hx = 1) : x = 0 := by
  have key : ∀ i : ℕ, (Valued.v x : ℤᵐ⁰) ≤ exp (-((k + i : ℕ) : ℤ)) := by
    intro i
    induction i with
    | zero => simpa using hx
    | succ i ih =>
        have hej : e ≤ k + i := by
          have := hd.lt
          omega
        have h1 := hd.expUnit_div_one_add hx ih hej
        rw [h] at h1
        have h2 : hd.root hx 0 ∈ unitFiltration (F := F) (2 * (k + i) - e) := by
          have h3 := Subgroup.inv_mem _ h1
          rwa [one_div, inv_inv] at h3
        rw [mem_unitFiltration, hd.coe_root_zero hx, add_sub_cancel_left] at h2
        refine le_trans h2 ?_
        rw [exp_le_exp]
        have hlt := hd.lt
        have h4 : k + (i + 1) ≤ 2 * (k + i) - e := by omega
        exact_mod_cast neg_le_neg (by exact_mod_cast h4)
  by_contra hne
  have hv0 : (Valued.v x : ℤᵐ⁰) ≠ 0 := by simpa using hne
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (Valued.v x : ℤᵐ⁰) = exp c := ⟨log _, (exp_log hv0).symm⟩
  have hbig := key (c.natAbs + k + 1)
  rw [hc, exp_le_exp] at hbig
  push_cast at hbig
  have habs : -|c| ≤ c := neg_abs_le c
  omega


/-! ## The exponential at zero, and transport -/

theorem expUnit_congr [CompleteSpace F] (hd : IsExpData F p e k) {x x' : F}
    (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))) (hx' : (Valued.v x' : ℤᵐ⁰) ≤ exp (-(k : ℤ)))
    (h : x = x') : hd.expUnit hx = hd.expUnit hx' := by
  subst h
  rfl

/-- **`exp 0 = 1`.** -/
theorem expUnit_zero [CompleteSpace F] (hd : IsExpData F p e k)
    (h0 : (Valued.v (0 : F) : ℤᵐ⁰) ≤ exp (-(k : ℤ))) : hd.expUnit h0 = 1 := by
  have hroot : ∀ a : ℕ, hd.root h0 a = 1 := by
    intro a
    refine (hd.root_unique h0 (one_mem _) ?_).symm
    simp
  have key : ∀ a : ℕ, hd.expUnit h0 ∈ unitFiltration (F := F) a := by
    intro a
    have h := hd.expUnit_div_root_mem h0 a
    rwa [hroot a, div_one] at h
  exact unitFiltration_separated key


/-! ## Surjectivity -/

/-- **The exponential is onto `U^(k)`.**  Successive approximation: `exp x ≡ 1 + x` to level
`2 j - e`, which is strictly better than `j` because `j ≥ k > e`, so the error can be corrected
indefinitely and the corrections converge by `LocalCFT.exists_limit_of_valued_sub_le`. -/
theorem exists_expUnit_eq [CompleteSpace F] (hd : IsExpData F p e k)
    {t : (integers (F := F))ˣ} (ht : t ∈ unitFiltration (F := F) k) :
    ∃ (x : F) (hx : (Valued.v x : ℤᵐ⁰) ≤ exp (-(k : ℤ))), hd.expUnit hx = t := by
  classical
  have h0 : (Valued.v (0 : F) : ℤᵐ⁰) ≤ exp (-(k : ℤ)) := by simp
  set addB : {z : F // (Valued.v z : ℤᵐ⁰) ≤ exp (-(k : ℤ))} →
      {z : F // (Valued.v z : ℤᵐ⁰) ≤ exp (-(k : ℤ))} →
      {z : F // (Valued.v z : ℤᵐ⁰) ≤ exp (-(k : ℤ))} :=
    fun X z ↦ ⟨X.1 + z.1, le_trans (Valuation.map_add _ _ _) (max_le X.2 z.2)⟩ with haddB
  have step : ∀ (i : ℕ) (X : {z : F // (Valued.v z : ℤᵐ⁰) ≤ exp (-(k : ℤ))}),
      ∃ z : {z : F // (Valued.v z : ℤᵐ⁰) ≤ exp (-(k : ℤ))},
        (t / hd.expUnit X.2 ∈ unitFiltration (F := F) (k + i) →
          (Valued.v z.1 : ℤᵐ⁰) ≤ exp (-((k + i : ℕ) : ℤ)) ∧
            t / hd.expUnit (addB X z).2 ∈ unitFiltration (F := F) (k + i + 1)) := by
    intro i X
    by_cases hc : t / hd.expUnit X.2 ∈ unitFiltration (F := F) (k + i)
    · have hzv : (Valued.v ((((t / hd.expUnit X.2 : (integers (F := F))ˣ)
          : integers (F := F)) : F) - 1) : ℤᵐ⁰) ≤ exp (-((k + i : ℕ) : ℤ)) := hc
      have hzk : (Valued.v ((((t / hd.expUnit X.2 : (integers (F := F))ˣ)
          : integers (F := F)) : F) - 1) : ℤᵐ⁰) ≤ exp (-(k : ℤ)) := by
        refine le_trans hzv ?_
        rw [exp_le_exp]
        push_cast
        omega
      refine ⟨⟨_, hzk⟩, fun _ ↦ ⟨hzv, ?_⟩⟩
      rw [hd.expUnit_add X.2 hzk (addB X ⟨_, hzk⟩).2, div_mul_eq_div_div]
      have hroot0 : hd.root hzk 0 = t / hd.expUnit X.2 := by
        refine Units.ext (Subtype.ext ?_)
        rw [hd.coe_root_zero hzk]
        ring
      have hej : e ≤ k + i := by
        have := hd.lt
        omega
      have hfo := hd.expUnit_div_one_add hzk hzv hej
      rw [hroot0] at hfo
      have hinv := Subgroup.inv_mem _ hfo
      rw [inv_div] at hinv
      refine unitFiltration_mem_of_le ?_ hinv
      have hlt := hd.lt
      omega
    · exact ⟨⟨0, h0⟩, fun hcon ↦ absurd hcon hc⟩
  choose s hs using step
  set X : ℕ → {z : F // (Valued.v z : ℤᵐ⁰) ≤ exp (-(k : ℤ))} :=
    fun i ↦ Nat.rec (motive := fun _ ↦ {z : F // (Valued.v z : ℤᵐ⁰) ≤ exp (-(k : ℤ))})
      ⟨0, h0⟩ (fun i Xi ↦ addB Xi (s i Xi)) i with hXdef
  have hXsucc : ∀ i, X (i + 1) = addB (X i) (s i (X i)) := fun _ ↦ rfl
  have hinv : ∀ i, t / hd.expUnit (X i).2 ∈ unitFiltration (F := F) (k + i) := by
    intro i
    induction i with
    | zero =>
        have h1 : hd.expUnit (X 0).2 = 1 := hd.expUnit_zero h0
        rw [h1, div_one, Nat.add_zero]
        exact ht
    | succ i ih =>
        have h := (hs i (X i) ih).2
        rw [← hXsucc i] at h
        exact h
  have hdiff : ∀ i, (Valued.v ((X i).1 - (X (i + 1)).1) : ℤᵐ⁰) ≤ exp (-((k + i : ℕ) : ℤ)) := by
    intro i
    have h := (hs i (X i) (hinv i)).1
    have heq : (X i).1 - (X (i + 1)).1 = -((s i (X i)).1) := by
      rw [hXsucc i]
      show (X i).1 - ((X i).1 + (s i (X i)).1) = _
      ring
    rw [heq, Valuation.map_neg]
    exact h
  obtain ⟨y, hy⟩ := exists_limit_of_valued_sub_le (fun i ↦ (X i).1) k hdiff
  have hyk : (Valued.v y : ℤᵐ⁰) ≤ exp (-(k : ℤ)) := by
    have h := hy 0
    have hX0 : ((X 0 : {z : F // (Valued.v z : ℤᵐ⁰) ≤ exp (-(k : ℤ))}) : F) = 0 := rfl
    rw [hX0] at h
    simpa using h
  refine ⟨y, hyk, ?_⟩
  have key : ∀ n : ℕ, hd.expUnit hyk / t ∈ unitFiltration (F := F) n := by
    intro n
    have hd1 : (Valued.v (y - (X n).1) : ℤᵐ⁰) ≤ exp (-((k + n : ℕ) : ℤ)) := hy n
    have hd2 : (Valued.v (y - (X n).1) : ℤᵐ⁰) ≤ exp (-(k : ℤ)) := by
      refine le_trans hd1 ?_
      rw [exp_le_exp]
      push_cast
      omega
    have hsum : hd.expUnit hyk = hd.expUnit (X n).2 * hd.expUnit hd2 := by
      rw [← hd.expUnit_add (X n).2 hd2 (addB (X n) ⟨_, hd2⟩).2]
      exact hd.expUnit_congr hyk (addB (X n) ⟨_, hd2⟩).2 (by show y = (X n).1 + (y - (X n).1); ring)
    have h3 : hd.expUnit hd2 ∈ unitFiltration (F := F) (k + n) :=
      hd.expUnit_mem hd2 hd1 (by have := hd.lt; omega)
    have h5 : hd.expUnit (X n).2 / t ∈ unitFiltration (F := F) (k + n) := by
      have h := Subgroup.inv_mem _ (hinv n)
      rwa [inv_div] at h
    have hchain : hd.expUnit hyk / t = hd.expUnit hd2 * (hd.expUnit (X n).2 / t) := by
      rw [hsum, mul_div_swap]
    rw [hchain]
    exact unitFiltration_mem_of_le (Nat.le_add_left n k) (mul_mem h3 h5)
  have h := unitFiltration_separated key
  rwa [div_eq_one] at h


end IsExpData


end LocalCFT
