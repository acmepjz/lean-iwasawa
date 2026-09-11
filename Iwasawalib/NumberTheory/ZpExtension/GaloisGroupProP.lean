/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.FieldTheory.IntermediateField.RestrictScalars
public import Iwasawalib.NumberTheory.ZpExtension.Linf
public import Iwasawalib.NumberTheory.ZpExtension.ProPGalois
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

/-!
# `G = Gal(L∞/K)` is pro-`p`

Let `K∞ / K` be a `ℤₚᵈ`-extension of number fields and `L∞` the union of the maximal
unramified abelian `p`-extensions `Lₙ / Kₙ` (`MvZpExtension.Linf`).  This file proves that
`G = Gal(L∞/K)` is a pro-`p` group, hence so are `X∞ = Gal(L∞/K∞)` and `Γ = G ⧸ X∞`.

The chain is: `K∞ / K` is a `{p}`-extension because every finite subextension sits inside some
`Kₙ`, of degree `p ^ (n · #ι)` (`MvZpExtension.finrank_eq_pow_of_finiteDimensional`); `L∞ / K∞`
is a `{p}`-extension (`MvZpExtension.isSExtension_Linf`); so `L∞ / K` is one, by
`IsSExtension.trans_of_isAlgebraic`.  Then `isProP_galoisGroup` applies.

Moving the conclusion from `↥L∞` (an intermediate field of `K∞`) to
`↥(L∞.restrictScalars K)` (the same field, viewed over `K`, which is what `MvZpExtension.GG`
is built from) is exactly what
`Iwasawalib.FieldTheory.IntermediateField.RestrictScalars` is for: doing it with `haveI` at
this concrete intermediate field makes the kernel reject the declaration.

## Main results

* `MvZpExtension.isSExtension_K_Kinf`, `MvZpExtension.isSExtension_K_Linf`.
* `MvZpExtension.isProP_GG`: `G = Gal(L∞/K)` is pro-`p`.
* `MvZpExtension.isProP_Xinf'` and `MvZpExtension.isProP_gammaQuotient`: so are `X∞` and
  `G ⧸ X∞`.
* `MvZpExtension.isClosed_Xinf`, `MvZpExtension.compactSpace_Xinf`: `X∞` is a closed, hence
  compact, subgroup of the profinite group `G`.
* `MvZpExtension.commGroup_Xinf`: `X∞` is commutative.
-/

open IntermediateField NumberField Topology

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-! ### `{p}`-extensions -/

omit [NumberField K] in
include H in
/-- `K∞ / K` is a `{p}`-extension: every finite subextension lies in some `Kₙ`, whose degree
over `K` is a power of `p`. -/
theorem isSExtension_K_Kinf : IsSExtension K Kinf {p} := by
  refine ⟨fun E _ ↦ ?_⟩
  obtain ⟨n, hn⟩ := H.finrank_eq_pow_of_finiteDimensional E
  rw [hn]
  intro q hq
  simp only [Finset.mem_coe, Nat.mem_primeFactors] at hq
  simpa using (Nat.prime_dvd_prime_iff_eq hq.1 Fact.out).1
    (Nat.Prime.dvd_of_dvd_pow hq.1 hq.2.1)

/-- `L∞ / K` is a `{p}`-extension. -/
instance isSExtension_K_Linf : IsSExtension K ↥H.Linf {p} :=
  haveI := H.isSExtension_K_Kinf
  IsSExtension.trans_of_isAlgebraic (F := K) (K := Kinf) (L := ↥H.Linf) {p}

/-- `L∞ / K` is a `{p}`-extension, for `L∞` viewed as an intermediate field of `K`. -/
instance isSExtension_K_restrictScalars_Linf :
    IsSExtension K ↥(H.Linf.restrictScalars K) {p} :=
  IntermediateField.isSExtension_restrictScalars K H.Linf {p}

/-! ### Pro-`p` -/

/-- **`G = Gal(L∞/K)` is pro-`p`.** -/
theorem isProP_GG : IsProP p H.GG :=
  isProP_galoisGroup p K ↥(H.Linf.restrictScalars K)

/-- `X∞`, as a subgroup of `G`, is pro-`p`. -/
theorem isProP_Xinf' : IsProP p ↥H.Xinf := H.isProP_GG.subgroup H.Xinf

/-- `Γ = G ⧸ X∞` is pro-`p`. -/
theorem isProP_gammaQuotient : IsProP p (H.GG ⧸ H.Xinf) :=
  H.isProP_GG.map (QuotientGroup.mk' H.Xinf) continuous_quot_mk
    (QuotientGroup.mk'_surjective H.Xinf)

/-- In `Γ = G ⧸ X∞`, `γ ^ (p ^ n) → 1`.  This is the hypothesis `hγ` of
`IwasawaAlgebra.gammaLambdaModule`. -/
theorem tendsto_pow_gammaQuotient (γ : H.GG ⧸ H.Xinf) :
    Filter.Tendsto (fun n : ℕ ↦ γ ^ p ^ n) Filter.atTop (𝓝 1) :=
  H.isProP_gammaQuotient.tendsto_pow γ

/-! ### `X∞` is a profinite group -/

/-- `X∞ = Gal(L∞/K∞)` is a closed subgroup of `G = Gal(L∞/K)`. -/
theorem isClosed_Xinf : IsClosed (H.Xinf : Set H.GG) :=
  InfiniteGalois.fixingSubgroup_isClosed H.KinfIn

/-- `X∞` is compact. -/
instance compactSpace_Xinf : CompactSpace ↥H.Xinf :=
  isCompact_iff_compactSpace.1 H.isClosed_Xinf.isCompact

/-- `X∞` is a commutative group (`MvZpExtension.mul_comm_Xinf`).  Note that the ambient group
`G` is *not* commutative, so this cannot be obtained from an instance on `G`; supplying it
directly also keeps typeclass synthesis from searching for `CommGroup G`, which times out. -/
noncomputable instance commGroup_Xinf : CommGroup ↥H.Xinf :=
  { (inferInstance : Group ↥H.Xinf) with
    mul_comm := fun a b ↦ Subtype.ext (H.mul_comm_Xinf a a.2 b b.2) }

end MvZpExtension
