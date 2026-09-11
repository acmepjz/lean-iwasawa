/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.GlobalCFT.IdeleFrobenius
public import Iwasawalib.NumberTheory.CFT.AdeleBaseChange
public import Iwasawalib.NumberTheory.CFT.AdicCompletionDecomposition

@[expose] public section

/-!
# The order of an idele under base change and under the Galois action

`Iwasawalib/NumberTheory/GlobalCFT/IdeleFrobenius.lean` attaches to an idele `a` its order
`ord_v(a)` at each finite place.  This file records how that order behaves under the two
operations that the reciprocity law involves.

* **Base change.**  `NumberField.IdeleGroup.ord_baseChange` : for `w` a place of `L` over `v`,
  `ord_w(a_L) = e(w|v) · ord_v(a)`, which is the completed ramification comparison
  `IsDedekindDomain.HeightOneSpectrum.valued_adicCompletionComap` read logarithmically.  At an
  unramified place this is an equality of orders,
  `NumberField.IdeleGroup.ord_baseChange_of_ramificationIdx_eq_one`.
* **Galois action.**  `NumberField.IdeleGroup.ord_smul` : `ord_{σ·w}(σ · b) = ord_w(b)`, because
  the Galois action moves the `w`-component isometrically to the `σ·w`-component
  (`NumberField.finiteAdele_smul_apply_smul` and
  `IsDedekindDomain.HeightOneSpectrum.valued_adicCompletionCongr`).

Together with `NumberField.IdeleGroup.ord_prod` these are what turns the norm of an idele into
a sum of local orders.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors

attribute [local instance] NumberField.galIdeleMulDistribMulAction

namespace NumberField.IdeleGroup

/-! ## Finite products -/

section Prod

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- **The order at `v` is additive on finite products of ideles.** -/
theorem ord_prod {ι : Type*} (s : Finset ι) (f : ι → IdeleGroup R K) (v : HeightOneSpectrum R) :
    ord (∏ i ∈ s, f i) v = ∑ i ∈ s, ord (f i) v := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ord_mul, ih]

end Prod

/-! ## Base change -/

section BaseChange

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]

/-- **Base change multiplies the order by the ramification index.** -/
theorem ord_baseChange (a : IdeleGroup (𝓞 K) K) (w : HeightOneSpectrum (𝓞 L)) :
    ord (baseChange K L a) w
      = ((w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal : ℤ) * ord a (w.under (𝓞 K)) := by
  show - WithZero.log (Valued.v (finiteAdeleBaseChange K L ((a : AdeleRing (𝓞 K) K).2) w)) = _
  rw [show finiteAdeleBaseChange K L ((a : AdeleRing (𝓞 K) K).2) w
      = adicCompletionComap K L (w.under (𝓞 K)) w ((a : AdeleRing (𝓞 K) K).2 (w.under (𝓞 K)))
    from rfl, valued_adicCompletionComap, WithZero.log_pow]
  show - ((w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal •
    WithZero.log (Valued.v ((a : AdeleRing (𝓞 K) K).2 (w.under (𝓞 K))))) = _
  rw [nsmul_eq_mul, ord, ordCompletion]
  ring

/-- **At an unramified place, base change preserves the order.** -/
theorem ord_baseChange_of_ramificationIdx_eq_one (a : IdeleGroup (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 L))
    (h : (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1) :
    ord (baseChange K L a) w = ord a (w.under (𝓞 K)) := by
  rw [ord_baseChange, h, Nat.cast_one, one_mul]

end BaseChange

/-! ## The Galois action -/

section Galois

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]

/-- **The Galois action on ideles moves the order along the action on places.** -/
theorem ord_smul (σ : L ≃ₐ[K] L) (b : IdeleGroup (𝓞 L) L) (w : HeightOneSpectrum (𝓞 L)) :
    ord (σ • b) (σ • w) = ord b w := by
  show - WithZero.log (Valued.v ((σ • ((b : AdeleRing (𝓞 L) L).2)) (σ • w))) = _
  rw [finiteAdele_smul_apply_smul, adicCompletionSmulEquiv, valued_adicCompletionCongr]
  rfl

/-- The same, with the place on the source. -/
theorem ord_smul' (σ : L ≃ₐ[K] L) (b : IdeleGroup (𝓞 L) L) (w : HeightOneSpectrum (𝓞 L)) :
    ord (σ • b) w = ord b (σ⁻¹ • w) := by
  conv_lhs => rw [← smul_inv_smul σ w]
  rw [ord_smul]

end Galois

end NumberField.IdeleGroup
