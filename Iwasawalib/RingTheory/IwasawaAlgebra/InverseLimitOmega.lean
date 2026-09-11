/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.Algebra.InverseLimit.Basic
public import Iwasawalib.RingTheory.IwasawaAlgebra.PowerSeriesAdic
public import Iwasawalib.RingTheory.IwasawaAlgebra.QuotientDistinguished
public import Iwasawalib.RingTheory.Polynomial.OneAddXPowSubOne

@[expose] public section

/-!
# `A⟦X⟧` as the inverse limit of `A⟦X⟧ ⧸ (ω_n)`
-/

open Polynomial PowerSeries

namespace PowerSeries

variable (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]

/-- The power series `ω_n = (1 + X) ^ (p ^ n) - 1`. -/
noncomputable abbrev omega (n : ℕ) : A⟦X⟧ := (Polynomial.oneAddXPowSubOne A (p ^ n) : A[X])

/-- The ideal `(ω_n)` of `A⟦X⟧`. -/
noncomputable abbrev omegaIdeal (n : ℕ) : Ideal A⟦X⟧ := Ideal.span {omega A p n}

variable {A p}

omit [Fact p.Prime] in
theorem omegaIdeal_antitone {n m : ℕ} (h : n ≤ m) : omegaIdeal A p m ≤ omegaIdeal A p n := by
  rw [omegaIdeal, omegaIdeal, Ideal.span_singleton_le_span_singleton]
  exact map_dvd Polynomial.coeToPowerSeries.ringHom
    (Polynomial.oneAddXPowSubOne_dvd_of_dvd A _ _ (pow_dvd_pow p h))

omit [Fact p.Prime] in
theorem coe_natCast_polynomial : ((p : A[X]) : A⟦X⟧) = C (p : A) := by
  rw [map_natCast, ← Polynomial.coeToPowerSeries.ringHom_apply, map_natCast]

omit [Fact p.Prime] in
theorem map_span_natCast_X :
    Ideal.map (Polynomial.coeToPowerSeries.ringHom (R := A))
      (Ideal.span {(p : A[X]), Polynomial.X}) = idealAX (p : A) := by
  rw [Ideal.map_span, idealAX]
  congr 1
  simp [Set.image_insert_eq, Polynomial.coeToPowerSeries.ringHom_apply,
    coe_natCast_polynomial (A := A) (p := p)]

omit [Fact p.Prime] in
theorem omega_mem_idealAX_pow (n : ℕ) : omega A p n ∈ idealAX (p : A) ^ (n + 1) := by
  rw [← map_span_natCast_X (A := A) (p := p), ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (Polynomial.oneAddXPowSubOne_mem_span_natCast_X_pow A p n)

omit [Fact p.Prime] in
theorem omegaIdeal_le_idealAX_pow (n : ℕ) : omegaIdeal A p n ≤ idealAX (p : A) ^ (n + 1) := by
  rw [omegaIdeal, Ideal.span_le, Set.singleton_subset_iff]
  exact omega_mem_idealAX_pow n

theorem idealAX_pow_le_span_pair (n m k : ℕ) (hm : m ≠ 0) (hk : k ≥ p ^ n * m) :
    idealAX (p : A) ^ k ≤ Ideal.span {(p : A⟦X⟧) ^ m, omega A p n} := by
  rw [← map_span_natCast_X (A := A) (p := p), ← Ideal.map_pow]
  refine (Ideal.map_mono
    (Polynomial.span_natCast_X_pow_le_span_natCast_pow_oneAddXPowSubOne A p n m k hm hk)).trans ?_
  rw [Ideal.map_span]
  refine Ideal.span_le.2 ?_
  rintro x hx
  simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · refine Ideal.subset_span ?_
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_pow,
      coe_natCast_polynomial (A := A) (p := p), Set.mem_insert_iff]
    left
    rw [map_natCast]
  · exact Ideal.subset_span (by simp [omega, Polynomial.coeToPowerSeries.ringHom_apply])

section Complete

variable [IsAdicComplete (Ideal.span {(p : A)}) A]

theorem ideal_smul_top (J : Ideal A) : J • (⊤ : Submodule A A) = J := by
  refine le_antisymm (Submodule.smul_le.2 fun r hr x _ ↦ ?_) fun x hx ↦ ?_
  · exact Ideal.mul_mem_right _ _ hr
  · simpa using Submodule.smul_mem_smul hx (Submodule.mem_top (x := (1 : A)))

omit [Fact p.Prime] in
theorem mem_span_pow_of_forall (c : A) (h : ∀ n : ℕ, c ∈ Ideal.span {(p : A) ^ n}) : c = 0 := by
  refine IsHausdorff.haus' (I := Ideal.span {(p : A)}) c fun n ↦ ?_
  rw [SModEq.zero, ideal_smul_top, Ideal.span_singleton_pow]
  exact h n

variable (A p) in
omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : A)}) A] in
theorem omegaIdeal_eq (n : ℕ) : omegaIdeal A p n =
    Ideal.span {((Polynomial.oneAddXPowSubOne A (p ^ n) : A[X]) : A⟦X⟧)} := rfl

omit [Fact p.Prime] in
theorem eq_zero_of_forall_mem_omegaIdeal {g : A⟦X⟧} (h : ∀ n, g ∈ omegaIdeal A p n) : g = 0 := by
  ext i
  rw [map_zero]
  refine mem_span_pow_of_forall (p := p) _ fun n ↦ ?_
  have := coeff_mem_of_mem_idealAX_pow (omegaIdeal_le_idealAX_pow (n + i) (h (n + i))) i
  rw [show n + i + 1 - i = n + 1 by omega] at this
  exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (by omega)) this

variable (A p)

/-- The transition maps of the inverse system `(A⟦X⟧ ⧸ (ω_n))_n`. -/
noncomputable def omegaFactor ⦃n m : ℕ⦄ (h : n ≤ m) :
    (A⟦X⟧ ⧸ omegaIdeal A p m) →ₐ[A] (A⟦X⟧ ⧸ omegaIdeal A p n) :=
  Ideal.Quotient.factorₐ A (omegaIdeal_antitone h)

/-- The natural map from `A⟦X⟧` to the inverse limit of `A⟦X⟧ ⧸ (ω_n)`. -/
noncomputable def toInverseLimitOmega :
    A⟦X⟧ →ₐ[A] Algebra.InverseLimit (omegaFactor A p) :=
  Algebra.InverseLimit.lift _ (fun n ↦ Ideal.Quotient.mkₐ A (omegaIdeal A p n))
    fun _ _ _ ↦ rfl

omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : A)}) A] in
@[simp]
theorem toInverseLimitOmega_apply_coe (g : A⟦X⟧) (n : ℕ) :
    (toInverseLimitOmega A p g).1 n = Ideal.Quotient.mk _ g := rfl

omit [Fact p.Prime] in
theorem toInverseLimitOmega_injective : Function.Injective (toInverseLimitOmega A p) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  refine eq_zero_of_forall_mem_omegaIdeal (p := p) fun n ↦ ?_
  have h0 := congr($(congr(($hg).1)) n)
  rw [toInverseLimitOmega_apply_coe] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0

theorem toInverseLimitOmega_surjective : Function.Surjective (toInverseLimitOmega A p) := by
  intro x
  choose r hr using fun n ↦ Ideal.Quotient.mk_surjective (x.1 n)
  have hcompat : ∀ {n m : ℕ}, n ≤ m → r m - r n ∈ omegaIdeal A p n := by
    intro n m h
    have hx := x.2 h
    rw [← hr m, ← hr n] at hx
    rw [← Ideal.Quotient.eq, ← hx]
    rfl
  have hcoeff : ∀ (i n m : ℕ), n ≤ m →
      coeff i (r m) - coeff i (r n) ∈ Ideal.span {(p : A) ^ (n + 1 - i)} := by
    intro i n m h
    have := coeff_mem_of_mem_idealAX_pow (omegaIdeal_le_idealAX_pow n (hcompat h)) i
    rwa [map_sub] at this
  have hL : ∀ i : ℕ, ∃ L : A, ∀ k : ℕ, coeff i (r (k + i)) - L ∈ Ideal.span {(p : A) ^ k} := by
    intro i
    have hcauchy : ∀ {k l : ℕ}, k ≤ l → coeff i (r (k + i)) ≡ coeff i (r (l + i))
        [SMOD (Ideal.span {(p : A)} ^ k • ⊤ : Submodule A A)] := by
      intro k l hkl
      rw [SModEq.sub_mem, ideal_smul_top, Ideal.span_singleton_pow]
      have := hcoeff i (k + i) (l + i) (by omega)
      rw [show k + i + 1 - i = k + 1 by omega] at this
      have h2 : Ideal.span {(p : A) ^ (k + 1)} ≤ Ideal.span {(p : A) ^ k} :=
        Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (by omega))
      exact (Ideal.neg_mem_iff _).1 (by simpa using h2 this)
    obtain ⟨L, hLspec⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : A)})
      (fun k ↦ coeff i (r (k + i))) hcauchy
    refine ⟨L, fun k ↦ ?_⟩
    have := hLspec k
    rw [SModEq.sub_mem, ideal_smul_top, Ideal.span_singleton_pow] at this
    exact this
  choose L hLspec using hL
  refine ⟨PowerSeries.mk L, ?_⟩
  have key : ∀ n : ℕ, PowerSeries.mk L - r n ∈ omegaIdeal A p n := by
    intro n
    have step1 : ∀ K : ℕ, PowerSeries.mk L - r n ∈ omegaIdeal A p n ⊔ idealAX (p : A) ^ K := by
      intro K
      set M := max n K with hM
      have h1 : PowerSeries.mk L - r M ∈ idealAX (p : A) ^ K := by
        refine mem_idealAX_pow_of_coeff_mem fun i hi ↦ ?_
        have hiM : i ≤ M := le_trans (le_of_lt hi) (le_max_right n K)
        have := hLspec i (M - i)
        rw [show M - i + i = M by omega] at this
        rw [map_sub, coeff_mk]
        have h3 : Ideal.span {(p : A) ^ (M - i)} ≤ Ideal.span {(p : A) ^ (K - i)} :=
          Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (by omega))
        exact (Ideal.neg_mem_iff _).1 (by simpa using h3 this)
      have h2 : r M - r n ∈ omegaIdeal A p n := hcompat (le_max_left n K)
      have h3 : PowerSeries.mk L - r n = (r M - r n) + (PowerSeries.mk L - r M) := by ring
      rw [h3]
      exact Submodule.add_mem _ (Submodule.mem_sup_left h2) (Submodule.mem_sup_right h1)
    -- Pass to the quotient by `(ω_n)`, which is a free `A`-module of finite rank.
    have hdist := Polynomial.isDistinguishedAt_oneAddXPowSubOne A p n
    have hzero := hdist.eq_zero_of_forall_mem_smul_pow (a := (p : A))
      (mem_span_pow_of_forall (p := p))
      (Ideal.Quotient.mk (omegaIdeal A p n) (PowerSeries.mk L - r n)) ?_
    · exact Ideal.Quotient.eq_zero_iff_mem.1 hzero
    · intro j
      have hK := step1 (p ^ n * (j + 1))
      have hle : idealAX (p : A) ^ (p ^ n * (j + 1)) ≤
          omegaIdeal A p n ⊔ Ideal.span {(p : A⟦X⟧) ^ (j + 1)} := by
        refine (idealAX_pow_le_span_pair n (j + 1) _ (by omega) le_rfl).trans ?_
        rw [Ideal.span_insert, omegaIdeal]
        exact sup_le le_sup_right le_sup_left
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (sup_le le_sup_left hle hK)
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      refine ⟨Ideal.Quotient.mk (omegaIdeal A p n) ((p : A⟦X⟧) * c), ?_⟩
      have hsmul : Ideal.Quotient.mk (omegaIdeal A p n) (((p : A) ^ j) • ((p : A⟦X⟧) * c))
          = ((p : A) ^ j) • Ideal.Quotient.mk (omegaIdeal A p n) ((p : A⟦X⟧) * c) :=
        map_smul (Ideal.Quotient.mkₐ A (omegaIdeal A p n)).toLinearMap _ _
      rw [← hsmul, ← hab, map_add, (Ideal.Quotient.eq_zero_iff_mem).2 ha, zero_add]
      congr 1
      rw [Algebra.smul_def]
      push_cast
      ring
  refine Subtype.ext (funext fun n ↦ ?_)
  rw [toInverseLimitOmega_apply_coe, ← hr n, Ideal.Quotient.eq]
  exact key n

/-- **The Iwasawa algebra isomorphism, power series side**: `A⟦X⟧` is the inverse limit of
`A⟦X⟧ ⧸ (ω_n)` where `ω_n = (1 + X) ^ (p ^ n) - 1`. -/
noncomputable def equivInverseLimitOmega :
    A⟦X⟧ ≃ₐ[A] Algebra.InverseLimit (omegaFactor A p) :=
  AlgEquiv.ofBijective (toInverseLimitOmega A p)
    ⟨toInverseLimitOmega_injective A p, toInverseLimitOmega_surjective A p⟩

@[simp]
theorem equivInverseLimitOmega_apply_coe (g : A⟦X⟧) (n : ℕ) :
    (equivInverseLimitOmega A p g).1 n = Ideal.Quotient.mk _ g := rfl

end Complete

end PowerSeries
