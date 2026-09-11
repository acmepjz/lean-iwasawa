/-
Copyright (c) 2025 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.Algebra.Module.EulerChar
public import Iwasawalib.RingTheory.IwasawaAlgebra.ModuleInvariants
public import Iwasawalib.RingTheory.IwasawaAlgebra.QuotientDistinguishedCard

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# Blueprint node `growth-general`
-/

open Function Module PowerSeries
open scoped Pointwise

section Aux

/-- A monotone bounded sequence of naturals is eventually constant. -/
theorem Nat.exists_eventually_const_of_monotone {f : ℕ → ℕ} (hf : Monotone f) {B : ℕ}
    (hB : ∀ n, f n ≤ B) : ∃ (N c : ℕ), ∀ n, N ≤ n → f n = c := by
  have hne : (Set.range f).Nonempty := ⟨f 0, 0, rfl⟩
  have hbdd : BddAbove (Set.range f) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  obtain ⟨N, hN⟩ := Nat.sSup_mem hne hbdd
  exact ⟨N, f N, fun n hn ↦ le_antisymm (hN ▸ le_csSup hbdd ⟨n, rfl⟩) (hf hn)⟩

variable {A : Type*} [CommRing A]

theorem Ideal.comap_mkQ_smul_top (I : Ideal A) (a : A) :
    Submodule.comap (Submodule.mkQ (I : Submodule A A)) (a • (⊤ : Submodule A (A ⧸ I))) =
      ((I ⊔ Ideal.span {a} : Ideal A) : Submodule A A) := by
  ext x
  simp only [Submodule.mem_comap, Submodule.mkQ_apply]
  constructor
  · intro hx
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ a ⊤).1 hx
    induction y using Submodule.Quotient.induction_on with
    | H z =>
      have heq : (Submodule.Quotient.mk x : A ⧸ I) = Submodule.Quotient.mk (a * z) := by
        rw [← hy, ← Submodule.Quotient.mk_smul]
        rfl
      have hmem : x - a * z ∈ I := (Submodule.Quotient.eq _).1 heq
      have : x = (x - a * z) + a * z := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hmem)
        (Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨z, mul_comm z a⟩))
  · intro hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hv
    refine (Submodule.mem_smul_pointwise_iff_exists _ a ⊤).2
      ⟨Submodule.Quotient.mk z, trivial, ?_⟩
    rw [← Submodule.Quotient.mk_smul]
    refine (Submodule.Quotient.eq _).2 ?_
    have h1 : a • z - (u + z * a) = -u := by simp only [smul_eq_mul]; ring
    rw [h1]
    exact neg_mem hu

/-- `(A ⧸ (b)) ⧸ a (A ⧸ (b)) = A ⧸ (b, a)`. -/
theorem Ideal.card_quotSMulTop_quotient_span_singleton (b a : A) :
    Nat.card (QuotSMulTop a (A ⧸ (Ideal.span {b} : Ideal A))) =
      Nat.card (A ⧸ (Ideal.span {b, a} : Ideal A)) := by
  set I : Ideal A := Ideal.span {b} with hI
  set π : A →ₗ[A] QuotSMulTop a (A ⧸ I) :=
    (Submodule.mkQ (a • (⊤ : Submodule A (A ⧸ I)))).comp (Submodule.mkQ (I : Submodule A A))
    with hπ
  have hsurj : Surjective π :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker π = ((Ideal.span {b, a} : Ideal A) : Submodule A A) := by
    rw [hπ, LinearMap.ker_comp, Submodule.ker_mkQ, Ideal.comap_mkQ_smul_top]
    rw [hI, Ideal.span_insert]
  rw [← Nat.card_congr (π.quotKerEquivOfSurjective hsurj).toEquiv, hker]

/-- A multiset of functions which are eventually `n + c_α` sums to `card • n + c`. -/
theorem Multiset.exists_sum_eq_card_mul_add {X : Type*} (s : Multiset X) (F : ℕ → X → ℝ)
    (h : ∀ α ∈ s, ∃ (c : ℝ) (N : ℕ), ∀ n, N ≤ n → F n α = n + c) :
    ∃ (c : ℝ) (N : ℕ), ∀ n, N ≤ n →
      (s.map (F n)).sum = (Multiset.card s : ℝ) * n + c := by
  induction s using Multiset.induction with
  | empty => exact ⟨0, 0, by simp⟩
  | cons a s ih =>
    obtain ⟨c₁, N₁, h₁⟩ := ih fun x hx ↦ h x (Multiset.mem_cons_of_mem hx)
    obtain ⟨c₂, N₂, h₂⟩ := h a (Multiset.mem_cons_self a s)
    refine ⟨c₁ + c₂, max N₁ N₂, fun n hn ↦ ?_⟩
    rw [Multiset.map_cons, Multiset.sum_cons, h₂ n (le_of_max_le_right hn),
      h₁ n (le_of_max_le_left hn), Multiset.card_cons]
    push_cast
    ring

theorem Ideal.finite_quotient_of_le {A : Type*} [CommRing A] {I J : Ideal A} (h : I ≤ J)
    [Finite (A ⧸ I)] : Finite (A ⧸ J) := by
  refine Finite.of_surjective (Ideal.Quotient.factor h) fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk I y, rfl⟩

/-- If `q` is prime and `q ∤ g`, then the `g`-torsion of `A ⧸ (q ^ e)` vanishes. -/
theorem Submodule.subsingleton_torsionBy_quotient_span_pow {A : Type*} [CommRing A] [IsDomain A]
    {q : A} (hq : Prime q) (e : ℕ) {g : A} (hqg : ¬ q ∣ g) :
    Subsingleton (Submodule.torsionBy A (A ⧸ (Ideal.span {q ^ e} : Ideal A)) g) := by
  have key : ∀ z : A ⧸ (Ideal.span {q ^ e} : Ideal A), g • z = 0 → z = 0 := by
    intro z hz
    induction z using Submodule.Quotient.induction_on with
    | H w =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Ideal.mem_span_singleton, smul_eq_mul] at hz
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      exact hq.pow_dvd_of_dvd_mul_left e hqg hz
  refine ⟨fun x y ↦ Subtype.ext ?_⟩
  rw [key x.1 ((Submodule.mem_torsionBy_iff g x.1).1 x.2),
    key y.1 ((Submodule.mem_torsionBy_iff g y.1).1 y.2)]

section Transfer

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- If `φ : M → N` has finite cokernel and `M ⧸ gM` is finite, then so is `N ⧸ gN`. -/
theorem Module.finite_quotSMulTop_of_finite_coker (φ : M →ₗ[R] N) (g : R)
    [Finite (N ⧸ LinearMap.range φ)] [Finite (QuotSMulTop g M)] :
    Finite (QuotSMulTop g N) := by
  haveI : Finite (QuotSMulTop g (LinearMap.range φ)) :=
    _root_.Finite.of_surjective _ (QuotSMulTop.map_surjective g φ.surjective_rangeRestrict)
  exact Module.finite_quotSMulTop_middle g (LinearMap.range φ).subtype (LinearMap.range φ).mkQ
    (LinearMap.exact_subtype_mkQ _) (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)

/-- If `N[g] = 0` then `M[g] = (ker φ)[g]`. -/
theorem Module.card_torsionBy_ker_eq (φ : M →ₗ[R] N) (g : R)
    [Subsingleton (Submodule.torsionBy R N g)] :
    Nat.card (Submodule.torsionBy R (LinearMap.ker φ) g) =
      Nat.card (Submodule.torsionBy R M g) := by
  refine Nat.card_congr (Equiv.ofBijective (Module.torsionByMap g (LinearMap.ker φ).subtype)
    ⟨Module.torsionByMap_injective g (Submodule.subtype_injective _), fun x ↦ ?_⟩)
  obtain ⟨x, hx⟩ := x
  have hgx : g • x = 0 := (Submodule.mem_torsionBy_iff g x).1 hx
  have hmem : φ x ∈ Submodule.torsionBy R N g := by
    rw [Submodule.mem_torsionBy_iff, ← map_smul, hgx, map_zero]
  have hzero : φ x = 0 :=
    congrArg Subtype.val (Subsingleton.elim (⟨φ x, hmem⟩ : Submodule.torsionBy R N g) 0)
  refine ⟨⟨⟨x, hzero⟩, ?_⟩, Subtype.ext rfl⟩
  rw [Submodule.mem_torsionBy_iff]
  exact Subtype.ext hgx

end Transfer

namespace IwasawaAlgebra

variable {p : ℕ} [Fact p.Prime]

/-- **Step 1 of `growth-general`**: if `Λ ⧸ (q, G)` is finite and `F` is a distinguished
polynomial of positive degree dividing `q`, then `F` does not divide `G`. -/
theorem not_dvd_of_finite_quotSMulTop {F : Polynomial ℤ_[p]}
    (hF : F.IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p])) (hd : 0 < F.natDegree)
    {q G : ℤ_[p]⟦X⟧} (hqF : (F : ℤ_[p]⟦X⟧) ∣ q)
    (hfin : Finite (QuotSMulTop G (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {q} : Ideal ℤ_[p]⟦X⟧)))) :
    ¬ (F : ℤ_[p]⟦X⟧) ∣ G := by
  intro hFG
  haveI := hfin
  have hcard : Nat.card (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {q, G} : Ideal ℤ_[p]⟦X⟧)) ≠ 0 := by
    rw [← Ideal.card_quotSMulTop_quotient_span_singleton q G]
    exact Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  haveI : Finite (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {q, G} : Ideal ℤ_[p]⟦X⟧)) := (Nat.card_ne_zero.1 hcard).2
  have hle : (Ideal.span {q, G} : Ideal ℤ_[p]⟦X⟧) ≤ Ideal.span {(F : ℤ_[p]⟦X⟧)} := by
    rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Ideal.mem_span_singleton.2 hqF, Ideal.mem_span_singleton.2 hFG⟩
  haveI : Finite (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {(F : ℤ_[p]⟦X⟧)} : Ideal ℤ_[p]⟦X⟧)) :=
    Ideal.finite_quotient_of_le hle
  have h0 := Module.finrank_eq_zero_of_finite ℤ_[p]
    (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {(F : ℤ_[p]⟦X⟧)} : Ideal ℤ_[p]⟦X⟧))
  rw [hF.finrank_quotient_powerSeries] at h0
  omega

/-- The `p`-summand: `ord_p #(Λ ⧸ (p ^ e, G)) = e * deg G`. -/
theorem factorization_card_quotSMulTop_p_pow {G : Polynomial ℤ_[p]}
    (hG : G.IsDistinguishedAt (Ideal.span {(p : ℤ_[p])})) (e : ℕ) :
    (Nat.card (QuotSMulTop ((G : ℤ_[p]⟦X⟧))
      (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {(p : ℤ_[p]⟦X⟧) ^ e} : Ideal ℤ_[p]⟦X⟧)))).factorization p
      = e * G.natDegree := by
  rw [Ideal.card_quotSMulTop_quotient_span_singleton,
    show ((p : ℤ_[p]⟦X⟧) ^ e) = algebraMap ℤ_[p] ℤ_[p]⟦X⟧ ((p : ℤ_[p]) ^ e) by
      rw [map_pow, map_natCast],
    hG.card_quotient_span_pair ((p : ℤ_[p]) ^ e), PadicInt.card_quotient_span_pow,
    ← pow_mul, Nat.factorization_pow_self (Fact.out : p.Prime)]

/-- The distinguished summand: `ord_p #(Λ ⧸ (f ^ e, G)) = ∑_α v(G(α))`. -/
theorem factorization_card_quotSMulTop_dist {f : Polynomial ℤ_[p]}
    (hf : f.IsDistinguishedAt (Ideal.span {(p : ℤ_[p])})) (hfp : Prime f) (e : ℕ)
    {G : Polynomial ℤ_[p]} (hfG : ¬ f ∣ G) :
    (((Nat.card (QuotSMulTop ((G : ℤ_[p]⟦X⟧))
        (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {(f : ℤ_[p]⟦X⟧) ^ e} : Ideal ℤ_[p]⟦X⟧)))).factorization p : ℝ))
      = ((((f ^ e).map (PadicInt.toPadicAlgCl p)).roots.map fun α ↦
          PadicAlgCl.val p (Polynomial.eval α (G.map (PadicInt.toPadicAlgCl p)))).sum) := by
  obtain ⟨k, h1, -, h3⟩ := exists_card_quotient_pow_pair hf hfp e hfG
  rw [Ideal.card_quotSMulTop_quotient_span_singleton, ← Polynomial.coe_pow, h1,
    Nat.factorization_pow_self (Fact.out : p.Prime), h3]

/-- If `f` is prime and does not divide `G`, then `G` does not vanish at any root of
`f ^ e`. -/
theorem eval_ne_zero_of_not_dvd {f : Polynomial ℤ_[p]}
    (hf : f.IsDistinguishedAt (Ideal.span {(p : ℤ_[p])})) (hfp : Prime f) (e : ℕ)
    {G : Polynomial ℤ_[p]} (hfG : ¬ f ∣ G) {α : PadicAlgCl p}
    (hα : α ∈ ((f ^ e).map (PadicInt.toPadicAlgCl p)).roots) :
    Polynomial.eval α (G.map (PadicInt.toPadicAlgCl p)) ≠ 0 := by
  set φ := PadicInt.toPadicAlgCl p with hφ
  have hF := hf.pow e
  have hdvd : ∀ h : Polynomial ℤ_[p], f ^ e ∣ G * h → f ^ e ∣ h :=
    fun _ hh ↦ hfp.pow_dvd_of_dvd_mul_left e hfG hh
  have hg := AdjoinRoot.norm_mk_ne_zero hF.monic hdvd
  intro hzero
  have hmap := AdjoinRoot.map_norm_mk φ hF.monic G
  have hprod := AdjoinRoot.norm_mk_eq_prod_roots (hF.monic.map φ) (G.map φ)
  rw [hprod] at hmap
  have hinj : Function.Injective φ :=
    (FaithfulSMul.algebraMap_injective ℚ_[p] (PadicAlgCl p)).comp Subtype.coe_injective
  refine hg (hinj ?_)
  rw [map_zero, hmap]
  refine Multiset.prod_eq_zero ?_
  rw [← hzero]
  exact Multiset.mem_map_of_mem _ hα


/-- For `F` distinguished, divisibility by `F` in `ℤ_p[X]` and in `Λ` agree. -/
theorem dvd_iff_coe_dvd {F h : Polynomial ℤ_[p]}
    (hF : F.IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p])) :
    F ∣ h ↔ (F : ℤ_[p]⟦X⟧) ∣ (h : ℤ_[p]⟦X⟧) := by
  rw [← Ideal.mem_span_singleton, ← Ideal.mem_span_singleton,
    ← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem,
    ← hF.algEquivQuotient_mk h]
  exact (map_eq_zero_iff _ hF.algEquivQuotient.injective).symm

/-- A distinguished polynomial which is prime in `Λ` is prime in `ℤ_p[X]`. -/
theorem prime_of_prime_coe {F : Polynomial ℤ_[p]}
    (hF : F.IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p]))
    (h : Prime (F : ℤ_[p]⟦X⟧)) : Prime F := by
  refine ⟨hF.monic.ne_zero, fun hu ↦ ?_, fun a c hac ↦ ?_⟩
  · have h1 : F ∣ 1 := isUnit_iff_dvd_one.1 hu
    rw [dvd_iff_coe_dvd hF, Polynomial.coe_one] at h1
    exact h.not_unit (isUnit_of_dvd_one h1)
  · rw [dvd_iff_coe_dvd hF, Polynomial.coe_mul] at hac
    rcases h.2.2 _ _ hac with h1 | h1
    · exact Or.inl ((dvd_iff_coe_dvd hF).2 h1)
    · exact Or.inr ((dvd_iff_coe_dvd hF).2 h1)

/-- **Step 3 of `growth-general`, one summand.** For a prime `q` of `Λ` which is either `p` or
an irreducible distinguished polynomial, the order of `Λ ⧸ (q ^ e, g_n)` is eventually
`e μ(q) p ^ n + e λ(q) n + c`. -/
theorem exists_eventually_factorization_summand
    {q : ℤ_[p]⟦X⟧} (e : ℕ)
    (hcase : q = (p : ℤ_[p]⟦X⟧) ∨ ∃ F : Polynomial ℤ_[p],
      F.IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p]) ∧ 0 < F.natDegree ∧
        q = (F : ℤ_[p]⟦X⟧))
    (hqp : Prime q)
    (g : ℕ → Polynomial ℤ_[p]) (n₀ : ℕ) (b : ℤ)
    (hdist : ∀ n, n₀ ≤ n → (g n).IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p]))
    (hdeg : ∀ n, n₀ ≤ n → ((g n).natDegree : ℤ) = (p : ℤ) ^ n + b)
    (hval : ∀ α : PadicAlgCl p, ‖α‖ < 1 →
      (∀ n, n₀ ≤ n → Polynomial.eval α ((g n).map (PadicInt.toPadicAlgCl p)) ≠ 0) →
      ∃ (c : ℝ) (N : ℕ), ∀ n, N ≤ n →
        PadicAlgCl.val p (Polynomial.eval α ((g n).map (PadicInt.toPadicAlgCl p))) = n + c)
    (hnd : ∀ n, n₀ ≤ n → ¬ q ∣ (g n : ℤ_[p]⟦X⟧)) :
    ∃ (c : ℝ) (N : ℕ), ∀ n, N ≤ n →
      ((Nat.card (QuotSMulTop ((g n : ℤ_[p]⟦X⟧))
        (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {q ^ e} : Ideal ℤ_[p]⟦X⟧)))).factorization p : ℝ)
        = ((e * mu q : ℕ) : ℝ) * (p : ℝ) ^ n + ((e * lambda q : ℕ) : ℝ) * n + c := by
  rcases hcase with rfl | ⟨F, hF, hFd, rfl⟩
  · refine ⟨(e : ℝ) * (b : ℝ), n₀, fun n hn ↦ ?_⟩
    have hGd : (g n).IsDistinguishedAt (Ideal.span {(p : ℤ_[p])}) :=
      PadicInt.maximalIdeal_eq_span_p (p := p) ▸ hdist n hn
    rw [factorization_card_quotSMulTop_p_pow hGd e, mu_p, lambda_p]
    have hd := hdeg n hn
    have : ((g n).natDegree : ℝ) = (p : ℝ) ^ n + (b : ℝ) := by exact_mod_cast hd
    push_cast
    rw [this]
    ring
  · have hF' : F.IsDistinguishedAt (Ideal.span {(p : ℤ_[p])}) :=
      PadicInt.maximalIdeal_eq_span_p (p := p) ▸ hF
    have hFprime : Prime F := prime_of_prime_coe hF hqp
    have hnd' : ∀ n, n₀ ≤ n → ¬ F ∣ g n := fun n hn hc ↦ hnd n hn ((dvd_iff_coe_dvd hF).1 hc)
    have hroots : ∀ α ∈ ((F ^ e).map (PadicInt.toPadicAlgCl p)).roots,
        ∃ (c : ℝ) (N : ℕ), ∀ n, N ≤ n →
          PadicAlgCl.val p (Polynomial.eval α ((g n).map (PadicInt.toPadicAlgCl p))) = n + c := by
      intro α hα
      refine hval α ((hF'.pow e).norm_lt_one_of_isRoot (Polynomial.isRoot_of_mem_roots hα))
        (fun n hn ↦ eval_ne_zero_of_not_dvd hF' hFprime e (hnd' n hn) hα)
    obtain ⟨c, N, hcN⟩ := Multiset.exists_sum_eq_card_mul_add
      (((F ^ e).map (PadicInt.toPadicAlgCl p)).roots)
      (fun n α ↦ PadicAlgCl.val p (Polynomial.eval α ((g n).map (PadicInt.toPadicAlgCl p))))
      hroots
    have hcard : (Multiset.card (((F ^ e).map (PadicInt.toPadicAlgCl p)).roots) : ℝ)
        = ((e * F.natDegree : ℕ) : ℝ) := by
      rw [AdjoinRoot.card_roots, ((hF.monic.pow e).natDegree_map _), hF.monic.natDegree_pow]
    refine ⟨c, max n₀ N, fun n hn ↦ ?_⟩
    rw [factorization_card_quotSMulTop_dist hF' hFprime e (hnd' n (le_of_max_le_left hn)),
      hcN n (le_of_max_le_right hn), hcard, mu_coe_distinguished hF, lambda_coe_distinguished hF]
    push_cast
    ring


/-- The final bookkeeping step: a quantity which is eventually `μ p ^ n + λ n + C` with `C`
real is eventually `μ p ^ n + λ n + ν` with `ν` an integer. -/
theorem exists_int_of_eventually_real {mu' lam' : ℤ} {P : ℕ} {ordf : ℕ → ℕ} {C : ℝ} {N : ℕ}
    (h : ∀ n, N ≤ n → (ordf n : ℝ) = (mu' : ℝ) * (P : ℝ) ^ n + (lam' : ℝ) * n + C) :
    ∃ ν : ℤ, ∀ n, N ≤ n → (ordf n : ℤ) = mu' * (P : ℤ) ^ n + lam' * n + ν := by
  refine ⟨(ordf N : ℤ) - mu' * (P : ℤ) ^ N - lam' * N, fun n hn ↦ ?_⟩
  have hN := h N le_rfl
  have hn' := h n hn
  have : ((ordf n : ℤ) : ℝ) =
      ((mu' * (P : ℤ) ^ n + lam' * n + ((ordf N : ℤ) - mu' * (P : ℤ) ^ N - lam' * N) : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

/-- The characteristic ideal read off a decomposition provided by the structure theorem. -/
theorem charIdeal_eq_span_prod {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M]
    {ι : Type*} [Fintype ι] (q : ι → ℤ_[p]⟦X⟧) (e : ι → ℕ) (hq : ∀ i, Prime (q i))
    (hpis : M ∼ₚᵢₛ[ℤ_[p]⟦X⟧] ((i : ι) → ℤ_[p]⟦X⟧ ⧸ Ideal.span {q i ^ e i})) :
    Module.charIdeal ℤ_[p]⟦X⟧ M = Ideal.span {∏ i, q i ^ e i} := by
  rw [hpis.charIdeal_eq, Module.IsTorsion.charIdeal_pi ℤ_[p]⟦X⟧ _
      (fun i ↦ Module.isTorsion_quotient_span_pow (hq i).ne_zero (e i)),
    Finset.prod_congr rfl (fun i _ ↦ Module.charIdeal_quotient_span_pow_of_prime (hq i) (e i)),
    Ideal.prod_span_singleton]

/-- **Blueprint node `growth-general`**: let `M` be a finitely generated torsion `Λ`-module and
let `(g n)` be a divisibility-increasing sequence of distinguished polynomials with
`deg g n = p ^ n + b`, satisfying hypothesis (c) on the valuations `v(g n (α))`, and such that
`M ⧸ g n M` is finite. Then there is an integer `ν` with
`ord_p #(M ⧸ g n M) = μ(M) p ^ n + λ(M) n + ν` for all sufficiently large `n`. -/
theorem exists_factorization_card_quotSMulTop_eq
    {M : Type*} [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M]
    (hM : Module.IsTorsion ℤ_[p]⟦X⟧ M)
    (g : ℕ → Polynomial ℤ_[p]) (n₀ : ℕ) (b : ℤ)
    (hdist : ∀ n, n₀ ≤ n → (g n).IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[p]))
    (hchain : ∀ n, n₀ ≤ n → g n ∣ g (n + 1))
    (hdeg : ∀ n, n₀ ≤ n → ((g n).natDegree : ℤ) = (p : ℤ) ^ n + b)
    (hval : ∀ α : PadicAlgCl p, ‖α‖ < 1 →
      (∀ n, n₀ ≤ n → Polynomial.eval α ((g n).map (PadicInt.toPadicAlgCl p)) ≠ 0) →
      ∃ (c : ℝ) (N : ℕ), ∀ n, N ≤ n →
        PadicAlgCl.val p (Polynomial.eval α ((g n).map (PadicInt.toPadicAlgCl p))) = n + c)
    (hfin : ∀ n, n₀ ≤ n → Finite (QuotSMulTop ((g n : ℤ_[p]⟦X⟧)) M)) :
    ∃ (ν : ℤ) (N : ℕ), ∀ n, N ≤ n →
      ((Nat.card (QuotSMulTop ((g n : ℤ_[p]⟦X⟧)) M)).factorization p : ℤ) =
        (muMod p M : ℤ) * (p : ℤ) ^ n + (lambdaMod p M : ℤ) * n + ν := by
  classical
  have hchain' : ∀ m n : ℕ, n₀ ≤ m → m ≤ n → g m ∣ g n := by
    intro m n hm hmn
    induction n, hmn using Nat.le_induction with
    | base => exact dvd_rfl
    | succ n hn ih => exact ih.trans (hchain n (hm.trans hn))
  obtain ⟨ι, hι, q, e, hqprime, hepos, hqcases, hpis⟩ := exists_isPseudoIsomorphic_pi hM
  obtain ⟨φ, hφ⟩ := hpis.exists_isPseudoIsomorphism
  haveI := hφ.isPseudoNull_ker
  haveI := hφ.isPseudoNull_coker
  haveI hfk : Finite (LinearMap.ker φ) :=
    finite_of_isPseudoNull (p := p) (LinearMap.ker φ)
  haveI hfc : Finite (((i : ι) → ℤ_[p]⟦X⟧ ⧸ Ideal.span {q i ^ e i}) ⧸ LinearMap.range φ) :=
    finite_of_isPseudoNull (p := p)
      (((i : ι) → ℤ_[p]⟦X⟧ ⧸ Ideal.span {q i ^ e i}) ⧸ LinearMap.range φ)
  obtain ⟨hmu, hlam⟩ := muMod_eq_sum_and_lambdaMod_eq_sum q e hqprime
    (charIdeal_eq_span_prod q e hqprime hpis)
  have hfinE : ∀ n, n₀ ≤ n →
      Finite (QuotSMulTop ((g n : ℤ_[p]⟦X⟧)) ((i : ι) → ℤ_[p]⟦X⟧ ⧸ Ideal.span {q i ^ e i})) := by
    intro n hn
    haveI := hfin n hn
    exact Module.finite_quotSMulTop_of_finite_coker φ _
  have hcardpi : ∀ G : ℤ_[p]⟦X⟧,
      Nat.card (QuotSMulTop G ((i : ι) → ℤ_[p]⟦X⟧ ⧸ Ideal.span {q i ^ e i})) =
        ∏ i, Nat.card (QuotSMulTop G (ℤ_[p]⟦X⟧ ⧸ Ideal.span {q i ^ e i})) := fun G ↦ by
    rw [Nat.card_congr (Module.quotSMulTopPiEquiv G
      (fun i ↦ ℤ_[p]⟦X⟧ ⧸ (Ideal.span {q i ^ e i} : Ideal ℤ_[p]⟦X⟧))).toEquiv, Nat.card_pi]
  have hfinfac : ∀ n, n₀ ≤ n → ∀ i,
      Finite (QuotSMulTop ((g n : ℤ_[p]⟦X⟧)) (ℤ_[p]⟦X⟧ ⧸ Ideal.span {q i ^ e i})) := by
    intro n hn i
    haveI := hfinE n hn
    have h1 : Nat.card (QuotSMulTop ((g n : ℤ_[p]⟦X⟧))
        ((i : ι) → ℤ_[p]⟦X⟧ ⧸ Ideal.span {q i ^ e i})) ≠ 0 :=
      Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
    rw [hcardpi] at h1
    exact (Nat.card_ne_zero.1 (Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ i))).2
  have hqnotdvd : ∀ n, n₀ ≤ n → ∀ i, ¬ q i ∣ (g n : ℤ_[p]⟦X⟧) := by
    intro n hn i
    rcases hqcases i with h | ⟨F, hF, hFd, h⟩
    · rw [h]
      exact not_p_dvd_of_isDistinguishedAt (hdist n hn)
    · rw [h]
      refine not_dvd_of_finite_quotSMulTop hF hFd (q := q i ^ e i) ?_ (hfinfac n hn i)
      rw [h]
      exact dvd_pow_self _ (hepos i).ne'
  have hsub : ∀ n, n₀ ≤ n →
      Subsingleton (Submodule.torsionBy ℤ_[p]⟦X⟧
        ((i : ι) → ℤ_[p]⟦X⟧ ⧸ Ideal.span {q i ^ e i}) ((g n : ℤ_[p]⟦X⟧))) := by
    intro n hn
    haveI : ∀ i, Subsingleton (Submodule.torsionBy ℤ_[p]⟦X⟧
        (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {q i ^ e i} : Ideal ℤ_[p]⟦X⟧)) ((g n : ℤ_[p]⟦X⟧))) := fun i ↦
      Submodule.subsingleton_torsionBy_quotient_span_pow (hqprime i) (e i) (hqnotdvd n hn i)
    exact (Module.torsionByPiEquiv ((g n : ℤ_[p]⟦X⟧))
      (fun i ↦ ℤ_[p]⟦X⟧ ⧸ (Ideal.span {q i ^ e i} : Ideal ℤ_[p]⟦X⟧))).toEquiv.subsingleton
  have hord : ∀ n, n₀ ≤ n →
      ((Nat.card (QuotSMulTop ((g n : ℤ_[p]⟦X⟧)) M)).factorization p : ℤ) =
        ((Nat.card (QuotSMulTop ((g n : ℤ_[p]⟦X⟧))
            ((i : ι) → ℤ_[p]⟦X⟧ ⧸ Ideal.span {q i ^ e i}))).factorization p : ℤ) +
        ((Nat.card (Submodule.torsionBy ℤ_[p]⟦X⟧ (LinearMap.ker φ)
            ((g n : ℤ_[p]⟦X⟧)))).factorization p : ℤ) := by
    intro n hn
    haveI := hfin n hn
    haveI := hfinE n hn
    haveI := hsub n hn
    haveI : Finite (Submodule.torsionBy ℤ_[p]⟦X⟧
        ((i : ι) → ℤ_[p]⟦X⟧ ⧸ Ideal.span {q i ^ e i}) ((g n : ℤ_[p]⟦X⟧))) :=
      Finite.of_subsingleton
    have hchi := Module.chi_eq_of_finite_ker_of_finite_coker p ((g n : ℤ_[p]⟦X⟧)) φ
    rw [Module.chi, Module.chi] at hchi
    have hE1 : Nat.card (Submodule.torsionBy ℤ_[p]⟦X⟧
        ((i : ι) → ℤ_[p]⟦X⟧ ⧸ Ideal.span {q i ^ e i}) ((g n : ℤ_[p]⟦X⟧))) = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩
    rw [hE1, Nat.factorization_one] at hchi
    rw [Module.card_torsionBy_ker_eq φ ((g n : ℤ_[p]⟦X⟧))]
    simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero] at hchi
    omega
  have hKmono : Monotone (fun n ↦ Nat.card (Submodule.torsionBy ℤ_[p]⟦X⟧ (LinearMap.ker φ)
      ((g (n₀ + n) : ℤ_[p]⟦X⟧)))) := by
    intro a c hac
    have hdd : (g (n₀ + a) : ℤ_[p]⟦X⟧) ∣ (g (n₀ + c) : ℤ_[p]⟦X⟧) := by
      obtain ⟨d, hd⟩ := hchain' (n₀ + a) (n₀ + c) (Nat.le_add_right _ _) (by omega)
      exact ⟨(d : ℤ_[p]⟦X⟧), by rw [hd]; exact Polynomial.coe_mul _ _⟩
    exact Nat.card_le_card_of_injective
      (Submodule.inclusion (Submodule.torsionBy_le_torsionBy_of_dvd _ _ hdd))
      (Submodule.inclusion_injective _)
  obtain ⟨N₁, c₁, hc₁⟩ := Nat.exists_eventually_const_of_monotone hKmono
    (B := Nat.card (LinearMap.ker φ))
    (fun n ↦ Nat.card_le_card_of_injective _ Subtype.val_injective)
  have hKconst : ∀ n, n₀ + N₁ ≤ n →
      Nat.card (Submodule.torsionBy ℤ_[p]⟦X⟧ (LinearMap.ker φ) ((g n : ℤ_[p]⟦X⟧))) = c₁ := by
    intro n hn
    have h := hc₁ (n - n₀) (by omega)
    rwa [show n₀ + (n - n₀) = n by omega] at h
  have hper : ∀ i : ι, ∃ (c : ℝ) (N : ℕ), ∀ n, N ≤ n →
      ((Nat.card (QuotSMulTop ((g n : ℤ_[p]⟦X⟧))
        (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {q i ^ e i} : Ideal ℤ_[p]⟦X⟧)))).factorization p : ℝ)
        = ((e i * mu (q i) : ℕ) : ℝ) * (p : ℝ) ^ n + ((e i * lambda (q i) : ℕ) : ℝ) * n + c :=
    fun i ↦ exists_eventually_factorization_summand (e i) (hqcases i) (hqprime i) g n₀ b
      hdist hdeg hval (fun n hn ↦ hqnotdvd n hn i)
  choose cc NN hNN using hper
  have hreal : ∀ n, max (n₀ + N₁) (Finset.univ.sup NN) ≤ n →
      ((Nat.card (QuotSMulTop ((g n : ℤ_[p]⟦X⟧)) M)).factorization p : ℝ)
        = ((muMod p M : ℤ) : ℝ) * (p : ℝ) ^ n + ((lambdaMod p M : ℤ) : ℝ) * n
          + ((∑ i, cc i) + ((c₁.factorization p : ℕ) : ℝ)) := by
    intro n hn
    have hn0 : n₀ ≤ n := le_trans (by omega) (le_trans (le_max_left _ _) hn)
    have hne : ∀ i ∈ (Finset.univ : Finset ι), Nat.card (QuotSMulTop ((g n : ℤ_[p]⟦X⟧))
        (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {q i ^ e i} : Ideal ℤ_[p]⟦X⟧))) ≠ 0 := by
      intro i _
      haveI := hfinfac n hn0 i
      exact Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
    have h3 := congrArg (fun F : ℕ →₀ ℕ ↦ F p) (Nat.factorization_prod hne)
    simp only [Finsupp.finsetSum_apply] at h3
    have hEsum : ((Nat.card (QuotSMulTop ((g n : ℤ_[p]⟦X⟧))
          ((i : ι) → ℤ_[p]⟦X⟧ ⧸ Ideal.span {q i ^ e i}))).factorization p : ℝ)
        = ∑ i, ((Nat.card (QuotSMulTop ((g n : ℤ_[p]⟦X⟧))
            (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {q i ^ e i} : Ideal ℤ_[p]⟦X⟧)))).factorization p : ℝ) := by
      rw [hcardpi, h3]
      push_cast
      ring
    have hsum : ∀ i : ι, ((Nat.card (QuotSMulTop ((g n : ℤ_[p]⟦X⟧))
        (ℤ_[p]⟦X⟧ ⧸ (Ideal.span {q i ^ e i} : Ideal ℤ_[p]⟦X⟧)))).factorization p : ℝ)
        = ((e i * mu (q i) : ℕ) : ℝ) * (p : ℝ) ^ n + ((e i * lambda (q i) : ℕ) : ℝ) * n
          + cc i := fun i ↦ hNN i n
      (le_trans (le_trans (Finset.le_sup (Finset.mem_univ i)) (le_max_right _ _)) hn)
    have h1 := hord n hn0
    rw [hKconst n (le_trans (le_max_left _ _) hn)] at h1
    have h1' : ((Nat.card (QuotSMulTop ((g n : ℤ_[p]⟦X⟧)) M)).factorization p : ℝ)
        = ((Nat.card (QuotSMulTop ((g n : ℤ_[p]⟦X⟧))
            ((i : ι) → ℤ_[p]⟦X⟧ ⧸ Ideal.span {q i ^ e i}))).factorization p : ℝ)
          + ((c₁.factorization p : ℕ) : ℝ) := by exact_mod_cast h1
    rw [h1', hEsum, Finset.sum_congr rfl (fun i _ ↦ hsum i), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, ← Nat.cast_sum,
      ← hmu, ← hlam]
    push_cast
    ring
  obtain ⟨ν, hν⟩ := exists_int_of_eventually_real (P := p) hreal
  exact ⟨ν, _, hν⟩

end IwasawaAlgebra
