module

public import Iwasawalib.NumberTheory.ZpExtension.RamifiedFamily
public import Iwasawalib.NumberTheory.ZpExtension.Ln
public import Mathlib.FieldTheory.LinearDisjoint

@[expose] public section

open IntermediateField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/- The ramified-family API supplies the total-ramification half.  The
   linear-disjointness half remains an explicit arithmetic input. -/
theorem exists_eventually_totallyRamified_and_linearDisjoint
    [Unique ι] {s : Type*} [Finite s]
    (v : s → AbsoluteValue Kinf ℝ)
    (hne : ∀ j, (v j).inertiaSubgroup K ≠ ⊥)
    (e₀ : ℕ)
    (hld : ∀ n, e₀ ≤ n → (H.Ln n).LinearDisjoint Kinf) :
    ∃ e : ℕ, ∀ n, e ≤ n →
      (∀ j (w : AbsoluteValue ↥((H.shift n).Linf.restrictScalars ↥(H.Kn n)) ℝ),
        (H.shift n).placeBelow w = v j →
          ((H.shift n).placeBelow w).inertiaSubgroup ↥(H.Kn n) = ⊤) ∧
      (H.Ln n).LinearDisjoint Kinf := by
  obtain ⟨e₁, he₁⟩ := H.exists_shift_totally_ramified v hne
  refine ⟨max e₀ e₁, fun n hn ↦ ?_⟩
  have hn₀ : e₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn₁ : e₁ ≤ n := le_trans (le_max_right _ _) hn
  exact ⟨he₁ n hn₁, hld n hn₀⟩

/- The same composition using the finiteness-of-the-ramified-set interface. -/
theorem exists_eventually_totallyRamified_of_finiteRamified_and_linearDisjoint
    [Unique ι]
    (hfin : {w : AbsoluteValue Kinf ℝ | w.inertiaSubgroup K ≠ ⊥}.Finite)
    (e₀ : ℕ)
    (hld : ∀ n, e₀ ≤ n → (H.Ln n).LinearDisjoint Kinf) :
    ∃ e : ℕ, ∀ n, e ≤ n →
      (∀ w : AbsoluteValue Kinf ℝ, w.inertiaSubgroup K ≠ ⊥ →
        w.inertiaSubgroup ↥(H.Kn n) = ⊤) ∧
      (H.Ln n).LinearDisjoint Kinf := by
  obtain ⟨e₁, he₁⟩ := H.exists_totally_ramified_of_finite_ramified hfin
  refine ⟨max e₀ e₁, fun n hn ↦ ?_⟩
  have hn₀ : e₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn₁ : e₁ ≤ n := le_trans (le_max_right _ _) hn
  exact ⟨he₁ n hn₁, hld n hn₀⟩

end MvZpExtension
