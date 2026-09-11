/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.AbsoluteValue.InfiniteInertia
public import Iwasawalib.NumberTheory.ZpExtension.TotallyRamified

@[expose] public section

/-!
# Washington's Lemma 13.3 in the language of places

Blueprint node `exists-totally-ramified`.  `Iwasawalib.NumberTheory.ZpExtension.TotallyRamified`
proves the group-theoretic core, `EquivMvZp.exists_Γpow_le_of_isClosed`; its docstring lists
three arithmetic inputs that were missing when it was written.  Two of them are supplied here:

* *the inertia subgroup of a place of `K∞` is a closed subgroup of `Γ`* is
  `AbsoluteValue.isClosed_inertiaSubgroup`, which holds in any (possibly infinite) algebraic
  extension for the Krull topology;
* *`K∞ / K_e` is totally ramified at the place* is turned into the membership statement
  `Γ^{p^e} ≤ I_v(K∞/K)` by `MvZpExtension.inertiaSubgroup_Kn_eq_top_iff`.

What is still genuinely missing is only the *identification of the ramified set*: that at least
one prime ramifies (needs finiteness of the Hilbert class field) and that only finitely many do
(only primes above `p` ramify, blueprint node `p:unr-outside-p`, local class field theory).
Accordingly `MvZpExtension.exists_totally_ramified` below takes the finite family of ramified
places as input.

## Main results

* `MvZpExtension.inertiaSubgroup_Kn_eq_top_iff`.
* `MvZpExtension.exists_totally_ramified`: **Washington, Lemma 13.3.**
-/

open IntermediateField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- `K∞ / Kₙ` is totally ramified at `v` exactly when `Γ^{p^n}` lies in the inertia subgroup of
`v` in `Γ = Gal(K∞/K)`. -/
theorem inertiaSubgroup_Kn_eq_top_iff (n : ℕ) (v : AbsoluteValue Kinf ℝ) :
    v.inertiaSubgroup ↥(H.Kn n) = ⊤ ↔ (H.Γpow n : Subgroup H.Γ) ≤ v.inertiaSubgroup K := by
  rw [AbsoluteValue.inertiaSubgroup_eq_top_iff K (H.Kn n) v, H.fixingSubgroup_Kn]

/-- **Washington, *Introduction to cyclotomic fields*, Lemma 13.3**, blueprint node
`exists-totally-ramified`.  Given finitely many places of `K∞` which ramify in `K∞ / K`
(i.e. have nontrivial inertia), there is a layer `K_e` such that `K∞ / K_n` is totally
ramified at all of them for every `n ≥ e`. -/
theorem exists_totally_ramified [Unique ι] {s : Type*} [Finite s] (v : s → AbsoluteValue Kinf ℝ)
    (hne : ∀ j, (v j).inertiaSubgroup K ≠ ⊥) :
    ∃ e : ℕ, ∀ n, e ≤ n → ∀ j, (v j).inertiaSubgroup ↥(H.Kn n) = ⊤ := by
  obtain ⟨e, he⟩ := H.exists_Γpow_le_of_isClosed (fun j ↦ (v j).inertiaSubgroup K)
    (fun j ↦ AbsoluteValue.isClosed_inertiaSubgroup K (v j)) hne
  exact ⟨e, fun n hn j ↦ (H.inertiaSubgroup_Kn_eq_top_iff n (v j)).2 (H.Γpow_le_of_le hn (he j))⟩

end MvZpExtension
