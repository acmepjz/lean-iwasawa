/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.PowerIndex
public import Iwasawalib.NumberTheory.CFT.SUnitLattice

@[expose] public section

/-!
# The absolute index `[E_S : E_S^n]` of the `S`-units

Chevalley's algebraic proof of the first fundamental inequality needs the **absolute** index of
the `n`-th powers in the `S`-unit group, not just a Herbrand quotient.  Combining Dirichlet's
`S`-unit theorem in the structural form proved in
`Iwasawalib/NumberTheory/CFT/SUnitLattice.lean` — `O_{L,S}^×` modulo its (finite) torsion is
free of rank `#S - 1` — with the general index calculus of
`Iwasawalib/NumberTheory/CFT/PowerIndex.lean`, this file proves

`[O_{L,S}^× : (O_{L,S}^×)^n] = n ^ (#S - 1) · #{x ∈ O_{L,S}^× | x ^ n = 1}`

for every `n ≠ 0` (`NumberField.powIndex_sUnit`).  The second factor is stated exactly as it is
proved — the number of `n`-th roots of unity **among the `S`-units**.  (Mathematically it is
`#μ_n(L)`, because every root of unity of `L` is a unit of `𝓞_L` and hence an `S`-unit, but that
identification is *not* proved here and is not used.)  When `μ_n ⊆ L` this factor is `n`, and
the index is `n ^ #S`; that is the number that Chevalley's count of the Kummer extension
`K(a^{1/ℓ})` compares with the local indices.

## Main statements

* `NumberField.powIndex_sUnit` : the displayed formula.
* `NumberField.powIndex_sUnit_of_powKer_eq` : the specialisation `n ^ #S` when the group of
  `n`-th roots of unity inside `O_{L,S}^×` has order `n`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Module PowerIndex

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]
variable {T : Set (HeightOneSpectrum (𝓞 L))} [Fintype T]

/-- The logarithmic embedding of the `S`-units, corestricted to the `S`-unit lattice: a
surjection with finite kernel from `O_{L,S}^×` onto a free `ℤ`-module of rank `#S - 1`. -/
def sLogRange (L : Type*) [Field L] [NumberField L] (T : Set (HeightOneSpectrum (𝓞 L)))
    [Fintype T] : Additive (T.unit L) →+ sUnitLattice L T :=
  ((sLogHyp L T).toIntLinearMap.rangeRestrict : _ →ₗ[ℤ] _).toAddMonoidHom

theorem sLogRange_surjective : Function.Surjective (sLogRange L T) :=
  LinearMap.surjective_rangeRestrict _

theorem coe_sLogRange (x : Additive (T.unit L)) :
    ((sLogRange L T x : sUnitLattice L T) : sHyperplane L T) = sLogHyp L T x := rfl

instance finite_ker_sLogRange : Finite (sLogRange L T).ker := by
  refine Finite.of_injective
    (fun x : (sLogRange L T).ker ↦
      (⟨(x : Additive (T.unit L)), ?_⟩ : LinearMap.ker (sLogHyp L T).toIntLinearMap)) ?_
  · have hx : sLogRange L T (x : Additive (T.unit L)) = 0 := x.2
    exact Subtype.ext_iff.1 hx
  · intro a b h
    have h' : (a : Additive (T.unit L)) = (b : Additive (T.unit L)) := by
      simpa using congrArg
        (fun z : LinearMap.ker (sLogHyp L T).toIntLinearMap ↦ (z : Additive (T.unit L))) h
    exact Subtype.ext h'

/-- **The absolute index of the `n`-th powers in the `S`-unit group.**

`[O_{L,S}^× : (O_{L,S}^×)^n] = n ^ (#S - 1) · #{x ∈ O_{L,S}^× : x ^ n = 1}`.

Here `#S - 1 = r₁ + r₂ - 1 + #T` is `NumberField.sRank`, and `PowerIndex.powKer n` is the
number of `n`-th roots of unity lying in `O_{L,S}^×`.  This is Dirichlet's `S`-unit theorem
converted into a count, by the trivial-action Tate cohomology of
`Iwasawalib/NumberTheory/CFT/PowerIndex.lean`. -/
theorem powIndex_sUnit {n : ℕ} (hn : n ≠ 0) :
    powIndex n (Additive (T.unit L))
      = n ^ sRank L T * powKer n (Additive (T.unit L)) := by
  have h := powIndex_eq_pow_finrank_mul_powKer_of_surjective hn (sLogRange L T)
    sLogRange_surjective
  rwa [finrank_sUnitLattice] at h

/-- If `O_{L,S}^×` contains exactly `n` `n`-th roots of unity — the case `μ_n ⊆ L`, `n ≠ 0` —
then `[O_{L,S}^× : (O_{L,S}^×)^n] = n ^ #S`. -/
theorem powIndex_sUnit_of_powKer_eq {n : ℕ} (hn : n ≠ 0)
    (hmu : powKer n (Additive (T.unit L)) = n) :
    powIndex n (Additive (T.unit L)) = n ^ (sRank L T + 1) := by
  rw [powIndex_sUnit hn, hmu, pow_succ]

end NumberField
