/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib

@[expose] public section

/-!

# Cyclotomic extension of finite field

-/

section HelperLemmas

/-
PROBLEM
In an algebraically closed field, for n > 0 with NeZero (n : K),
    there exists a primitive n-th root of unity.

PROVIDED SOLUTION
Use the fact that the cyclotomic polynomial of degree n has degree φ(n) > 0, so it has a root in an algebraically closed field. Then use Polynomial.isRoot_cyclotomic_iff to convert this root to a primitive root.
-/
private theorem exists_primitiveRoot_of_algClosed (K : Type*) [Field K] [IsAlgClosed K]
    (n : ℕ) (hn : n ≠ 0) (hn' : NeZero (n : K)) :
    ∃ r : K, IsPrimitiveRoot r n := by
  -- By definition of cyclotomic polynomials, we know that their roots are primitive roots of unity.
  have h_cyclotomic_roots : ∀ r : K, Polynomial.IsRoot (Polynomial.cyclotomic n K) r → IsPrimitiveRoot r n := by
    intro r hr;
    convert Polynomial.isRoot_cyclotomic_iff.mp hr;
  by_cases h : n = 0 <;> simp_all +decide [ Polynomial.cyclotomic_ne_zero ];
  exact Exists.elim ( IsAlgClosed.exists_root ( Polynomial.cyclotomic n K ) ( by simp +decide [ h, Polynomial.degree_cyclotomic ] ) ) fun r hr => ⟨ r, h_cyclotomic_roots r hr ⟩

/-
PROBLEM
For a finite field K with CharP K p, p does not divide (Fintype.card K ^ n - 1) when n ≥ 1.

PROVIDED SOLUTION
Since K has char p and card K = p^k for some k ≥ 1, we have p ∣ card K, so card K ≡ 0 mod p, hence card K ^ n ≡ 0 mod p, hence card K ^ n - 1 ≡ -1 mod p. Since p is prime (p ≥ 2), -1 ≢ 0 mod p, so p ∤ (card K ^ n - 1).

More concretely: p ∣ Fintype.card K (since card K = p^k). So p ∣ Fintype.card K ^ n. If p ∣ (Fintype.card K ^ n - 1), then p ∣ 1 (from the difference), contradicting p being prime (p ≥ 2).
-/
private theorem finiteField_char_not_dvd_card_pow_sub_one (K : Type*) [Field K] [Fintype K]
    (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP K p] (n : ℕ) (hn : 0 < n) :
    ¬(p ∣ (Fintype.card K ^ n - 1)) := by
  rw [ ← ZMod.natCast_eq_zero_iff ] ; simp_all +decide [ Nat.cast_sub ( Nat.one_le_pow n _ ( Fintype.card_pos ) ) ] ;
  -- Since $K$ is a finite field with characteristic $p$, its cardinality is a power of $p$. Let $q = p^k$ for some $k$.
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card K = p^k := by
    have := FiniteField.card K p; aesop;
  rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ, pow_mul ];
  · exact absurd hk ( Nat.ne_of_gt ( Fintype.one_lt_card ) );
  · simp +decide [ hn.ne' ]

/-
PROBLEM
For a finite field K and a finite extension L of K, every nonzero element of L
    is a root of unity of order coprime to the characteristic.

PROVIDED SOLUTION
Use Fintype.card L - 1 as the order. By FiniteField.pow_card_sub_one_eq_one, x ^ (Fintype.card L - 1) = 1. We need: (1) Fintype.card L - 1 ≠ 0: since L is a field, card L ≥ 2. (2) (Fintype.card L - 1 : K) ≠ 0: The characteristic p of K satisfies CharP L p (by Algebra.charP_iff). Since L is a finite field of char p, card L = p^m for some m. So card L - 1 = p^m - 1. Since p ∣ p^m but p ∤ (p^m - 1) (because p^m - 1 ≡ -1 mod p and p ≥ 2), we get (card L - 1 : K) ≠ 0.
-/
private theorem finiteField_element_isRootOfUnity (K L : Type*) [Field K] [Field L]
    [Algebra K L] [Fintype K] [Fintype L]
    (x : L) (hx : x ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K) ≠ 0 ∧ x ^ n = 1 := by
  refine' ⟨ Fintype.card L - 1, _, _, _ ⟩;
  · exact Nat.sub_ne_zero_of_lt ( Fintype.one_lt_card );
  · -- Since $L$ is a finite field, its cardinality is a power of its characteristic $p$, say $|L| = p^m$.
    obtain ⟨p, m, hp, hm⟩ : ∃ p m : ℕ, Nat.Prime p ∧ Fintype.card L = p^m := by
      have := FiniteField.card L ( ringChar L ) ; aesop;
    have h_char : CharP K p ∧ CharP L p := by
      have h_char : CharP L p := by
        have h_char : ringChar L = p := by
          have := FiniteField.card L ( ringChar L );
          obtain ⟨ n, hn₁, hn₂ ⟩ := this; have := hn₁.dvd_of_dvd_pow ( hm.symm ▸ hn₂.symm ▸ dvd_pow_self _ ( Nat.cast_ne_zero.mpr n.ne_zero ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
        generalize_proofs at *; (
        exact h_char ▸ inferInstance);
      grind +suggestions;
    cases m <;> simp_all +decide [ pow_succ' ];
    · exact absurd hm ( Nat.ne_of_gt ( Fintype.one_lt_card ) );
    · haveI := Fact.mk hp; simp_all +decide [ Nat.cast_sub ( show 1 ≤ p * p ^ _ from Nat.mul_pos hp.pos ( pow_pos hp.pos _ ) ) ] ;
  · exact FiniteField.pow_card_sub_one_eq_one x hx

/-
PROBLEM
The backward direction: an algebraic closure of a finite field is a cyclotomic extension.

PROVIDED SOLUTION
Split into the two parts of IsCyclotomicExtension.mk:

1) exists_isPrimitiveRoot: Given n with (n : K) ≠ 0 and n ≠ 0, use hL to get IsAlgClosed L (from isAlgClosure_iff), then use exists_primitiveRoot_of_algClosed with NeZero instance from the fact that (n : K) ≠ 0 implies (n : L) ≠ 0 (since char is preserved: if p | n then (n : K) = 0, contradict).

2) adjoin_roots: Every element x of L is algebraic over K (from isAlgClosure_iff). So x is integral over K, hence x lies in IntermediateField.adjoin K {x} which is finite-dimensional over K (adjoin of integral element). Since K is finite, this extension is also finite (Fintype). By finiteField_element_isRootOfUnity, if x ≠ 0, then x^n = 1 for some n with (n : K) ≠ 0 and n ≠ 0, so x ∈ Algebra.adjoin K {b | ∃ n ∈ {n | (n : K) ≠ 0}, n ≠ 0 ∧ b ^ n = 1}. If x = 0, then x is in the adjoin trivially (0 is in any subalgebra).

For the NeZero instance: We need NeZero (n : L). Since (n : K) ≠ 0, and algebraMap K L is injective (since K and L are fields), (n : L) = algebraMap K L (n : K) ≠ 0.

For the Fintype instance on the intermediate field: use Fintype.ofFinite, and the fact that a finite-dimensional extension of a finite field is finite (Module.finite_of_finite).
-/
private theorem isAlgClosure_imp_isCyclotomicExtension (K L : Type*) [Field K] [Field L]
    [Algebra K L] [Finite K] (hL : IsAlgClosure K L) :
    IsCyclotomicExtension {n | (n : K) ≠ 0} K L := by
  refine' ⟨ _, _ ⟩;
  · intro n hn hn';
    have h_alg_closed : IsAlgClosed L := by
      exact hL.1;
    -- Since the algebraMap K L is injective, if (n : K) ≠ 0, then (n : L) ≠ 0.
    have h_injective : Function.Injective (algebraMap K L) := by
      exact RingHom.injective _;
    exact exists_primitiveRoot_of_algClosed L n hn' ( by exact ⟨ by simpa using h_injective.ne hn ⟩ );
  · intro x;
    -- Since $x$ is algebraic over $K$, it is integral over $K$.
    have hx_integral : IsIntegral K x := by
      exact hL.isAlgebraic.isIntegral.isIntegral x;
    have hx_finite : FiniteDimensional K (↥(IntermediateField.adjoin K {x})) := by
      exact IntermediateField.adjoin.finiteDimensional hx_integral;
    have hx_finite : Finite (↥(IntermediateField.adjoin K {x})) := by
      exact Module.finite_of_finite K;
    have hx_root_of_unity : ∀ y : ↥(IntermediateField.adjoin K {x}), y ≠ 0 → ∃ n : ℕ, n ≠ 0 ∧ (n : K) ≠ 0 ∧ y ^ n = 1 := by
      intro y hy_nonzero
      have hy_root_of_unity : ∃ n : ℕ, n ≠ 0 ∧ (n : K) ≠ 0 ∧ y ^ n = 1 := by
        have hy_finite_field : Finite (↥(IntermediateField.adjoin K {x})) := by
          exact hx_finite
        convert finiteField_element_isRootOfUnity K ( ↥ ( IntermediateField.adjoin K { x } ) ) y hy_nonzero;
        · exact Fintype.ofFinite K;
        · exact Fintype.ofFinite _;
      exact hy_root_of_unity;
    by_cases hx : x = 0 <;> simp_all +decide [ Algebra.adjoin_singleton_eq_range_aeval ];
    obtain ⟨ n, hn, hn' ⟩ := hx_root_of_unity x ( IntermediateField.mem_adjoin_simple_self K x ) ( by simpa [ Subtype.ext_iff ] using hx ) ; simp_all +decide [ Subtype.ext_iff ] ;
    exact Algebra.subset_adjoin ⟨ n + 1, by aesop ⟩

/-
PROBLEM
The forward direction: a cyclotomic extension of a finite field is an algebraic closure.

PROVIDED SOLUTION
We need to show IsAlgClosed L ∧ Algebra.IsAlgebraic K L (by isAlgClosure_iff).

Algebraic: Use IsCyclotomicExtension.integral to get Algebra.IsIntegral K L, then Algebra.IsIntegral.isAlgebraic.

IsAlgClosed: Use IsAlgClosure.of_exist_roots. We need to show: for every monic irreducible polynomial p over L, p has a root in L. Equivalently, we can show L is algebraically closed by showing every finite extension of L is L itself.

Alternative approach: We show L is algebraically closed by showing every irreducible polynomial over L is linear.

Better approach using the structure of finite fields:
- haveI : Fintype K := Fintype.ofFinite K
- Let q = Fintype.card K and p = ringChar K (which is prime since K is finite).
- For any m ≥ 1, consider q^m - 1. Since p | q (as q = p^k), we have p ∤ (q^m - 1) (by finiteField_char_not_dvd_card_pow_sub_one). So (q^m - 1 : K) ≠ 0.
- By IsCyclotomicExtension.exists_isPrimitiveRoot, L contains a primitive (q^m - 1)-th root of unity ζ.
- The splitting field of X^(q^m) - X over K is GaloisField p (k*m) which has cardinality q^m.
- Since L contains all (q^m-1)-th roots of unity and 0, L contains all elements of the splitting field of X^(q^m) - X.
- Every algebraic element over K lies in some finite extension, which has cardinality q^m for some m.
- So L contains all algebraic elements over K.
- Since every polynomial over K splits in the algebraic closure, and L contains the algebraic closure, L is algebraically closed.

Actually, a cleaner approach: To show IsAlgClosed L, we can use the fact that L is algebraic over K and contains all roots of unity coprime to char. We want to show every polynomial f over L has a root. Since L is algebraic over K, we can reduce to polynomials over K. Any irreducible polynomial over K has degree d, and its splitting field is F_{q^d} which is contained in L (since L contains primitive (q^d - 1)-th roots of unity, and F_{q^d} is generated by such a root over K).

Most directly: use IsAlgClosed.mk (show every irreducible polynomial over L splits). Since every element of L is algebraic over K, and every irreducible polynomial over K splits into linear factors over L (because the roots are in finite extensions F_{q^m} which are contained in L), we conclude L is algebraically closed.

Let me try yet another approach: use the Isaacs lemma `IsAlgClosure.of_exist_roots`: if L is algebraic over K and every monic irreducible polynomial over L has a root in L, then L is an algebraic closure. But we already know L is algebraic, so we just need to show IsAlgClosed L.

For IsAlgClosed, use `IsAlgClosed.of_exists_root`: we need that every polynomial over L of degree ≥ 1 has a root. Take such a polynomial f. Its coefficients are in L, hence algebraic over K. So the coefficients lie in a finite subextension K' of L. Since K is finite, K' is finite. So K' is a finite field with some cardinality q^m. The polynomial f has a root in the algebraic closure of K', which is the algebraic closure of K, which is contained in L (by the same argument as above).

This is getting circular. Let me try to be more concrete:

Key claim: For every n ≥ 1, L contains a subfield isomorphic to F_{q^n} (the unique field with q^n elements).

Proof of claim: q^n - 1 is coprime to char p. So (q^n - 1 : K) ≠ 0, i.e., q^n - 1 ∈ {n | (n : K) ≠ 0}. By IsCyclotomicExtension.exists_isPrimitiveRoot, there exists ζ ∈ L with IsPrimitiveRoot ζ (q^n - 1). Then ζ^(q^n - 1) = 1, so ζ^(q^n) = ζ, meaning ζ is a root of X^(q^n) - X. The subfield of L generated by ζ over K has at most q^n elements (roots of X^(q^n) - X). Actually it has exactly q^n elements since ζ generates a subgroup of order q^n - 1 in L*, plus 0.

From the claim: Let f be an irreducible polynomial over K of degree d. Its splitting field has q^d elements. By the claim, L contains such a splitting field. So f splits in L.

Now for IsAlgClosed L: Take any polynomial g over L. Its coefficients are algebraic over K, so they lie in some finite extension K' of K inside L. K' has q^m elements. So g is a polynomial over K' ≅ F_{q^m}. Take an irreducible factor of g over K'. This has degree d, so it splits in F_{q^(md)} which is contained in L. So g has a root in L.

This shows IsAlgClosed L.
-/
private theorem isCyclotomicExtension_imp_isAlgClosure (K L : Type*) [Field K] [Field L]
    [Algebra K L] [Finite K] (hL : IsCyclotomicExtension {n | (n : K) ≠ 0} K L) :
    IsAlgClosure K L := by
  apply IsAlgClosure.mk;
  · convert IsAlgClosed.of_exists_root L _ using 1
    generalize_proofs at *; (
    -- Since $L$ is a cyclotomic extension of $K$, it contains all roots of unity coprime to the characteristic of $K$. Therefore, for any irreducible polynomial $p$ over $L$, there exists a root in $L$.
    have h_root : ∀ p : Polynomial L, p.Monic → Irreducible p → ∃ x : L, p.eval x = 0 := by
      intro p hp_monic hp_irreducible
      have h_alg_closed : IsAlgClosed L := by
        have h_alg_closed : IsCyclotomicExtension {n | (n : K) ≠ 0} K (AlgebraicClosure K) := by
          apply isAlgClosure_imp_isCyclotomicExtension K (AlgebraicClosure K) (by
          infer_instance)
        generalize_proofs at *; (
        have h_iso : Nonempty (L ≃ₐ[K] AlgebraicClosure K) := by
          have h_iso : IsCyclotomicExtension {n | (n : K) ≠ 0} K L ∧ IsCyclotomicExtension {n | (n : K) ≠ 0} K (AlgebraicClosure K) := by
            exact ⟨ hL, h_alg_closed ⟩
          generalize_proofs at *; (
          have h_iso : ∀ {S : Set ℕ}, IsCyclotomicExtension S K L → IsCyclotomicExtension S K (AlgebraicClosure K) → Nonempty (L ≃ₐ[K] AlgebraicClosure K) := by
            intro S hS hS';
            have := hS.isGalois; have := hS'.isGalois; simp_all +decide [ IsGalois ] ;
            exact ⟨IsCyclotomicExtension.algEquiv S K L (AlgebraicClosure K)⟩
          generalize_proofs at *; (
          exact h_iso hL h_alg_closed))
        generalize_proofs at *; (
        obtain ⟨ f ⟩ := h_iso
        generalize_proofs at *; (
        convert IsAlgClosed.of_exists_root L _ using 1
        generalize_proofs at *; (
        intro p hp_monic hp_irreducible
        obtain ⟨ x, hx ⟩ : ∃ x : AlgebraicClosure K, Polynomial.eval x (Polynomial.map (f : L →+* AlgebraicClosure K) p) = 0 := by
          apply IsAlgClosed.exists_root
          generalize_proofs at *; (
          rw [ Polynomial.degree_map_eq_of_injective ] <;> norm_num [ hp_monic, hp_irreducible, Function.Injective ];
          exact fun h => hp_irreducible.not_isUnit <| Polynomial.isUnit_iff_degree_eq_zero.mpr h)
        generalize_proofs at *; (
        use f.symm x; simp_all +decide [ Polynomial.eval_map ] ;
        rw [ Polynomial.eval_eq_sum_range ] at *; simp_all +decide [ Polynomial.eval₂_eq_sum_range ] ;
        simpa [ ← f.injective.eq_iff ] using congr_arg ( fun y => f.symm y ) hx)))))
      exact h_alg_closed.exists_root p ( Polynomial.degree_pos_of_irreducible hp_irreducible |> fun h => h.ne' ) |> fun ⟨ x, hx ⟩ => ⟨ x, hx ⟩
    generalize_proofs at *; (
    exact h_root));
  · -- Apply the fact that if L is integral over K, then it is algebraic over K.
    have h_alg : Algebra.IsIntegral K L → Algebra.IsAlgebraic K L := by
      exact fun h => h.isAlgebraic;
    exact h_alg hL.integral

end HelperLemmas

theorem FiniteField.isCyclotomicExtension_iff_isAlgClosure (K L : Type*) [Field K] [Field L]
    [Algebra K L] [Finite K] : IsCyclotomicExtension {n | (n : K) ≠ 0} K L ↔ IsAlgClosure K L :=
  ⟨isCyclotomicExtension_imp_isAlgClosure K L, isAlgClosure_imp_isCyclotomicExtension K L⟩