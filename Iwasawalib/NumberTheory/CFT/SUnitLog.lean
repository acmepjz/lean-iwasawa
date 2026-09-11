/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.SUnits
public import Mathlib.NumberTheory.NumberField.ProductFormula

@[expose] public section

/-!
# The logarithmic embedding of the `S`-units

Let `L` be a number field and let `T` be a set of finite places of `L`.  The *`S`-places* of `L`
(relative to `T`) are the archimedean places together with the finite places in `T`; this is the
type `NumberField.SPlace L T`.  Each `S`-place `p` carries a normalised absolute value
`NumberField.sNorm p : L → ℝ`, namely `x ↦ (w x) ^ mult w` at an archimedean place `w` and the
`w`-adic absolute value at a finite place `w`.

The two facts proved here are the arithmetic input to the computation of the Herbrand quotient
of the `S`-unit group:

* the **product formula for `S`-units**: `∏_{p ∈ S} sNorm p x = 1` for an `S`-unit `x`
  (`NumberField.prod_sNorm_eq_one`), equivalently `∑_{p ∈ S} log ‖x‖_p = 0`
  (`NumberField.sum_sLog_eq_zero`), so that the logarithmic embedding lands in the trace-zero
  hyperplane of `∏_{p ∈ S} ℝ`;
* the **Galois equivariance** of the whole picture: `Gal(L/K)` permutes the `S`-places and
  `sNorm (σ • p) (σ x) = sNorm p x` (`NumberField.sNorm_smul`), so the logarithmic embedding is
  a map of `Gal(L/K)`-modules.

Finally, the kernel of the logarithmic embedding on the `S`-units is exactly the group of roots
of unity of `L` (`NumberField.sLog_eq_zero_iff`), which is finite.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField.InfinitePlace

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

/-! ## The `w`-adic absolute value and the `w`-adic valuation -/

theorem adicAbv_pos {v : HeightOneSpectrum (𝓞 L)} {x : L} (hx : x ≠ 0) :
    0 < NumberField.HeightOneSpectrum.adicAbv L v x :=
  (NumberField.HeightOneSpectrum.adicAbv L v).pos hx

theorem adicAbv_eq_one_iff (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    NumberField.HeightOneSpectrum.adicAbv L v x = 1 ↔ v.valuation L x = 1 := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, ← NNReal.coe_one, NNReal.coe_inj,
    WithZeroMulInt.toNNReal_eq_one_iff _ _
      (HeightOneSpectrum.one_lt_absNorm_nnreal v).ne']

/-! ## The `S`-places of a number field -/

variable (L) in
/-- The `S`-places of `L` relative to a set `T` of finite places: the archimedean places of `L`
together with the finite places belonging to `T`.  (The archimedean places are always in `S`.) -/
abbrev SPlace (T : Set (HeightOneSpectrum (𝓞 L))) : Type _ := InfinitePlace L ⊕ T

/-- The normalised absolute value attached to an `S`-place. -/
def sNorm {T : Set (HeightOneSpectrum (𝓞 L))} (p : SPlace L T) (x : L) : ℝ :=
  Sum.elim (fun w : InfinitePlace L ↦ w x ^ w.mult)
    (fun w : T ↦ NumberField.HeightOneSpectrum.adicAbv L (w : HeightOneSpectrum (𝓞 L)) x) p

@[simp]
theorem sNorm_inl {T : Set (HeightOneSpectrum (𝓞 L))} (w : InfinitePlace L) (x : L) :
    sNorm (T := T) (Sum.inl w) x = w x ^ w.mult := rfl

@[simp]
theorem sNorm_inr {T : Set (HeightOneSpectrum (𝓞 L))} (w : T) (x : L) :
    sNorm (Sum.inr w) x
      = NumberField.HeightOneSpectrum.adicAbv L (w : HeightOneSpectrum (𝓞 L)) x := rfl

theorem sNorm_pos {T : Set (HeightOneSpectrum (𝓞 L))} (p : SPlace L T) {x : L} (hx : x ≠ 0) :
    0 < sNorm p x := by
  cases p with
  | inl w => exact pow_pos (InfinitePlace.pos_iff.2 hx) _
  | inr w => exact adicAbv_pos hx

theorem sNorm_ne_zero {T : Set (HeightOneSpectrum (𝓞 L))} (p : SPlace L T) {x : L} (hx : x ≠ 0) :
    sNorm p x ≠ 0 := (sNorm_pos p hx).ne'

theorem sNorm_mul {T : Set (HeightOneSpectrum (𝓞 L))} (p : SPlace L T) (x y : L) :
    sNorm p (x * y) = sNorm p x * sNorm p y := by
  cases p with
  | inl w => simp [sNorm, mul_pow]
  | inr w => simp [sNorm]

theorem sNorm_one {T : Set (HeightOneSpectrum (𝓞 L))} (p : SPlace L T) : sNorm p 1 = 1 := by
  cases p with
  | inl w => simp [sNorm]
  | inr w => simp [sNorm]

theorem sNorm_pow {T : Set (HeightOneSpectrum (𝓞 L))} (p : SPlace L T) (x : L) (n : ℕ) :
    sNorm p (x ^ n) = sNorm p x ^ n := by
  induction n with
  | zero => simpa using sNorm_one p
  | succ k ih => rw [pow_succ, pow_succ, sNorm_mul, ih]

/-! ## The product formula for `S`-units -/

/-- Outside `T`, an `S`-unit has `w`-adic absolute value `1`. -/
theorem adicAbv_eq_one_of_mem_unit {T : Set (HeightOneSpectrum (𝓞 L))} {x : Lˣ}
    (hx : x ∈ T.unit L) {v : HeightOneSpectrum (𝓞 L)} (hv : v ∉ T) :
    NumberField.HeightOneSpectrum.adicAbv L v (x : L) = 1 :=
  (adicAbv_eq_one_iff v (x : L)).2 (hx v hv)

/-- For an `S`-unit, the product of the `v`-adic absolute values over all finite places reduces
to a finite product over `T`. -/
theorem finprod_adicAbv_eq_prod {T : Set (HeightOneSpectrum (𝓞 L))} [Fintype T] {x : Lˣ}
    (hx : x ∈ T.unit L) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 L), NumberField.HeightOneSpectrum.adicAbv L v (x : L)
      = ∏ w : T, NumberField.HeightOneSpectrum.adicAbv L (w : HeightOneSpectrum (𝓞 L)) (x : L) := by
  classical
  have hT : T.Finite := Set.toFinite T
  have hsub : Function.mulSupport
      (fun v : HeightOneSpectrum (𝓞 L) ↦
        NumberField.HeightOneSpectrum.adicAbv L v (x : L)) ⊆ (hT.toFinset : Set _) := by
    intro v hv
    rw [Set.Finite.coe_toFinset]
    by_contra hvT
    exact hv (adicAbv_eq_one_of_mem_unit hx hvT)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  exact Finset.prod_subtype hT.toFinset (fun v ↦ hT.mem_toFinset) _

/-- The product of the `v`-adic absolute values over all finite places, rewritten as a product
over the finite places in Mathlib's sense. -/
theorem finprod_finitePlace_eq_finprod_adicAbv (x : L) :
    ∏ᶠ w : FinitePlace L, w x
      = ∏ᶠ v : HeightOneSpectrum (𝓞 L), NumberField.HeightOneSpectrum.adicAbv L v x := by
  rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := L)).symm]
  exact finprod_congr fun v ↦ by
    rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]

/-- **The product formula for `S`-units.**  If `x` is an `S`-unit, then the product of its
normalised absolute values over the `S`-places is `1`.  In particular the logarithmic embedding
of the `S`-units lands in the trace-zero hyperplane. -/
theorem prod_sNorm_eq_one {T : Set (HeightOneSpectrum (𝓞 L))} [Fintype T] {x : Lˣ}
    (hx : x ∈ T.unit L) :
    ∏ p : SPlace L T, sNorm p (x : L) = 1 := by
  rw [Fintype.prod_sum_type]
  have h₁ : ∏ w : InfinitePlace L, sNorm (T := T) (Sum.inl w) (x : L)
      = ∏ w : InfinitePlace L, w (x : L) ^ w.mult := rfl
  have h₂ : ∏ w : T, sNorm (T := T) (Sum.inr w) (x : L)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 L), NumberField.HeightOneSpectrum.adicAbv L v (x : L) := by
    rw [finprod_adicAbv_eq_prod hx]
    rfl
  rw [h₁, h₂, ← finprod_finitePlace_eq_finprod_adicAbv]
  exact prod_abs_eq_one (x.ne_zero)

/-! ## The logarithmic embedding -/

variable {T : Set (HeightOneSpectrum (𝓞 L))}

/-- The logarithm of the normalised absolute value at an `S`-place. -/
def sLog (p : SPlace L T) (x : Lˣ) : ℝ := Real.log (sNorm p (x : L))

@[simp]
theorem sLog_inl (w : InfinitePlace L) (x : Lˣ) :
    sLog (T := T) (Sum.inl w) x = w.mult * Real.log (w (x : L)) := by
  rw [sLog, sNorm_inl, Real.log_pow]

@[simp]
theorem sLog_inr (w : T) (x : Lˣ) :
    sLog (Sum.inr w) x
      = Real.log (NumberField.HeightOneSpectrum.adicAbv L (w : HeightOneSpectrum (𝓞 L)) (x : L)) :=
  rfl

theorem sLog_mul (p : SPlace L T) (x y : Lˣ) : sLog p (x * y) = sLog p x + sLog p y := by
  rw [sLog, sLog, sLog, show ((x * y : Lˣ) : L) = (x : L) * (y : L) from rfl, sNorm_mul,
    Real.log_mul (sNorm_ne_zero p x.ne_zero) (sNorm_ne_zero p y.ne_zero)]

theorem sLog_one (p : SPlace L T) : sLog p 1 = 0 := by
  rw [sLog, show ((1 : Lˣ) : L) = 1 from rfl, sNorm_one, Real.log_one]

variable (L T) in
/-- **The logarithmic embedding of `Lˣ` attached to a finite set `S` of places.**  It is a
homomorphism from `Lˣ` to the real vector space `∏_{p ∈ S} ℝ`; restricted to the `S`-units it
lands in the trace-zero hyperplane (`NumberField.sum_sLog_eq_zero`). -/
def sLogEmbedding : Additive Lˣ →+ (SPlace L T → ℝ) where
  toFun x p := sLog p (Additive.toMul x)
  map_zero' := funext fun p ↦ sLog_one p
  map_add' _ _ := funext fun p ↦ sLog_mul p _ _

@[simp]
theorem sLogEmbedding_apply (x : Lˣ) (p : SPlace L T) :
    sLogEmbedding L T (Additive.ofMul x) p = sLog p x := rfl

/-- **The `S`-unit product formula in logarithmic form.**  The logarithmic embedding of an
`S`-unit lies in the trace-zero hyperplane `{y | ∑_p y p = 0}` of `∏_{p ∈ S} ℝ`. -/
theorem sum_sLog_eq_zero [Fintype T] {x : Lˣ} (hx : x ∈ T.unit L) :
    ∑ p : SPlace L T, sLog p x = 0 := by
  have h := prod_sNorm_eq_one (T := T) hx
  have h' := congrArg Real.log h
  rw [Real.log_one, Real.log_prod (fun p _ ↦ sNorm_ne_zero p x.ne_zero)] at h'
  exact h'

theorem sum_sLogEmbedding_eq_zero [Fintype T] {x : Lˣ} (hx : x ∈ T.unit L) :
    ∑ p : SPlace L T, sLogEmbedding L T (Additive.ofMul x) p = 0 :=
  sum_sLog_eq_zero hx

/-! ## The kernel of the logarithmic embedding -/

theorem infinitePlace_eq_one_of_sLog_eq_zero {x : Lˣ}
    (h : ∀ p : SPlace L T, sLog p x = 0) (w : InfinitePlace L) : w (x : L) = 1 := by
  have hw := h (Sum.inl w)
  rw [sLog_inl] at hw
  have hlog : Real.log (w (x : L)) = 0 := by
    rcases mul_eq_zero.1 hw with h' | h'
    · exact absurd (Nat.cast_eq_zero.1 h') InfinitePlace.mult_ne_zero
    · exact h'
  exact Real.eq_one_of_pos_of_log_eq_zero (InfinitePlace.pos_iff.2 x.ne_zero) hlog

theorem valuation_eq_one_of_sLog_eq_zero {x : Lˣ} (hx : x ∈ T.unit L)
    (h : ∀ p : SPlace L T, sLog p x = 0) (v : HeightOneSpectrum (𝓞 L)) :
    v.valuation L (x : L) = 1 := by
  by_cases hv : v ∈ T
  · have hw := h (Sum.inr ⟨v, hv⟩)
    rw [sLog_inr] at hw
    exact (adicAbv_eq_one_iff v (x : L)).1
      (Real.eq_one_of_pos_of_log_eq_zero (adicAbv_pos x.ne_zero) hw)
  · exact hx v hv

/-- An element of `Lˣ` all of whose finite valuations are `1` is a unit of the ring of
integers. -/
theorem exists_unit_ringOfIntegers_of_valuation_eq_one {x : Lˣ}
    (h : ∀ v : HeightOneSpectrum (𝓞 L), v.valuation L (x : L) = 1) :
    ∃ u : (𝓞 L)ˣ, algebraMap (𝓞 L) L (u : 𝓞 L) = (x : L) := by
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 L) L (x : L)
    fun v ↦ (h v).le
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 L) L
    ((x⁻¹ : Lˣ) : L) fun v ↦ by
      have : v.valuation L ((x⁻¹ : Lˣ) : L) * v.valuation L (x : L) = 1 := by
        rw [← map_mul]
        rw [show ((x⁻¹ : Lˣ) : L) * (x : L) = 1 from x.inv_mul]
        exact map_one _
      rw [h v, mul_one] at this
      exact this.le
  have hyz : algebraMap (𝓞 L) L (y * z) = 1 := by
    rw [map_mul, hy, hz]
    exact x.mul_inv
  have hzy : algebraMap (𝓞 L) L (z * y) = 1 := by rw [mul_comm]; exact hyz
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 L) L
  exact ⟨⟨y, z, hinj (by rw [hyz, map_one]), hinj (by rw [hzy, map_one])⟩, hy⟩

/-- **The kernel of the logarithmic embedding on the `S`-units is the group of roots of unity
of `L`.**  In particular it is finite. -/
theorem sLog_eq_zero_iff_isOfFinOrder {x : Lˣ} (hx : x ∈ T.unit L) :
    (∀ p : SPlace L T, sLog p x = 0) ↔ IsOfFinOrder x := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := exists_unit_ringOfIntegers_of_valuation_eq_one
      (valuation_eq_one_of_sLog_eq_zero hx h)
    have hutors : u ∈ Units.torsion L := by
      rw [Units.mem_torsion]
      intro w
      rw [hu]
      exact infinitePlace_eq_one_of_sLog_eq_zero h w
    have hfin : IsOfFinOrder u := (CommGroup.mem_torsion u).1 hutors
    have hmap : Units.map (algebraMap (𝓞 L) L : (𝓞 L) →* L) u = x := Units.ext hu
    exact hmap ▸ (Units.map (algebraMap (𝓞 L) L : (𝓞 L) →* L)).isOfFinOrder hfin
  · intro h p
    obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.1 h
    have hpow : sNorm p (x : L) ^ n = 1 := by
      rw [← sNorm_pow p (x : L) n,
        show ((x : L)) ^ n = ((x ^ n : Lˣ) : L) from (Units.val_pow_eq_pow_val x n).symm, hxn]
      exact sNorm_one p
    have hlog : (n : ℝ) * Real.log (sNorm p (x : L)) = 0 := by
      rw [← Real.log_pow, hpow, Real.log_one]
    rcases mul_eq_zero.1 hlog with h' | h'
    · exact absurd (Nat.cast_eq_zero.1 h') hn.ne'
    · exact h'

/-! ## Galois equivariance -/

section Galois

open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] [Algebra K L]

omit [NumberField K] in
/-- The absolute norm of an ideal is invariant under a ring automorphism. -/
theorem absNorm_smul (σ : L ≃ₐ[K] L) (I : Ideal (𝓞 L)) :
    Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  have hmap : σ • I = Ideal.map
      ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L) I := rfl
  rw [hmap, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I _
    (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ) rfl).toEquiv).symm

private theorem toNNReal_congr {e₁ e₂ : NNReal} (h₁ : e₁ ≠ 0) (h₂ : e₂ ≠ 0)
    (m : WithZero (Multiplicative ℤ)) (h : e₁ = e₂) :
    WithZeroMulInt.toNNReal h₁ m = WithZeroMulInt.toNNReal h₂ m := by
  subst h
  rfl

omit [NumberField K] in
/-- **The `w`-adic absolute value is Galois equivariant**: `|σ x|_{σ w} = |x|_w`. -/
theorem adicAbv_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    NumberField.HeightOneSpectrum.adicAbv L (σ • w) (σ x)
      = NumberField.HeightOneSpectrum.adicAbv L w x := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, NumberField.HeightOneSpectrum.adicAbv_def,
    valuation_smul_heightOneSpectrum]
  refine congrArg NNReal.toReal (toNNReal_congr _ _ _ ?_)
  rw [HeightOneSpectrum.smul_asIdeal, absNorm_smul]

omit [NumberField L] [NumberField K] in
/-- **An archimedean place is Galois equivariant**: `|σ x|_{σ w} = |x|_w`. -/
theorem infinitePlace_smul (σ : L ≃ₐ[K] L) (w : InfinitePlace L) (x : L) :
    (σ • w) (σ x) = w x := by
  rw [InfinitePlace.smul_apply]
  exact congrArg w (σ.symm_apply_apply x)

omit [NumberField L] [NumberField K] in
/-- The multiplicity of an archimedean place is Galois invariant. -/
theorem mult_smul (σ : L ≃ₐ[K] L) (w : InfinitePlace L) : (σ • w).mult = w.mult := by
  rw [InfinitePlace.smul_eq_comap]
  exact InfinitePlace.mult_comap (σ.symm : L ≃+* L) w

variable (K L)

/-- `Gal(L/K)` acts on the finite places above a set of places of `K`. -/
instance placesOverSetMulAction (S : Set (HeightOneSpectrum (𝓞 K))) :
    MulAction (L ≃ₐ[K] L) (placesOverSet K L S) where
  smul σ w := ⟨σ • (w : HeightOneSpectrum (𝓞 L)), (smul_mem_placesOverSet σ).2 w.2⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)

variable {K L}

omit [NumberField L] [NumberField K] in
@[simp]
theorem coe_smul_placesOverSet {S : Set (HeightOneSpectrum (𝓞 K))} (σ : L ≃ₐ[K] L)
    (w : placesOverSet K L S) :
    ((σ • w : placesOverSet K L S) : HeightOneSpectrum (𝓞 L))
      = σ • (w : HeightOneSpectrum (𝓞 L)) := rfl

variable (K L)

/-- **`Gal(L/K)` permutes the `S`-places of `L`.** -/
instance sPlaceMulAction (S : Set (HeightOneSpectrum (𝓞 K))) :
    MulAction (L ≃ₐ[K] L) (SPlace L (placesOverSet K L S)) where
  smul σ p := Sum.map (fun w : InfinitePlace L ↦ σ • w) (fun w ↦ σ • w) p
  one_smul p := by
    cases p with
    | inl w => exact congrArg Sum.inl (one_smul _ w)
    | inr w => exact congrArg Sum.inr (one_smul _ w)
  mul_smul σ τ p := by
    cases p with
    | inl w => exact congrArg Sum.inl (mul_smul σ τ w)
    | inr w => exact congrArg Sum.inr (mul_smul σ τ w)

variable {K L}

omit [NumberField L] [NumberField K] in
@[simp]
theorem smul_sPlace_inl {S : Set (HeightOneSpectrum (𝓞 K))} (σ : L ≃ₐ[K] L)
    (w : InfinitePlace L) :
    (σ • (Sum.inl w : SPlace L (placesOverSet K L S))) = Sum.inl (σ • w) := rfl

omit [NumberField L] [NumberField K] in
@[simp]
theorem smul_sPlace_inr {S : Set (HeightOneSpectrum (𝓞 K))} (σ : L ≃ₐ[K] L)
    (w : placesOverSet K L S) :
    (σ • (Sum.inr w : SPlace L (placesOverSet K L S))) = Sum.inr (σ • w) := rfl

/-- **The normalised absolute values are Galois equivariant.**  This is what makes the
logarithmic embedding a homomorphism of `Gal(L/K)`-modules. -/
theorem sNorm_smul {S : Set (HeightOneSpectrum (𝓞 K))} (σ : L ≃ₐ[K] L)
    (p : SPlace L (placesOverSet K L S)) (x : L) : sNorm (σ • p) (σ x) = sNorm p x := by
  cases p with
  | inl w => rw [smul_sPlace_inl, sNorm_inl, sNorm_inl, infinitePlace_smul, mult_smul]
  | inr w => rw [smul_sPlace_inr, sNorm_inr, sNorm_inr, coe_smul_placesOverSet, adicAbv_smul]

/-- **The logarithmic embedding is `Gal(L/K)`-equivariant.** -/
theorem sLog_smul {S : Set (HeightOneSpectrum (𝓞 K))} (σ : L ≃ₐ[K] L)
    (p : SPlace L (placesOverSet K L S)) (x : Lˣ) : sLog (σ • p) (σ • x) = sLog p x := by
  rw [sLog, sLog, coe_smul_units, sNorm_smul]

/-- **The logarithmic embedding is `Gal(L/K)`-equivariant.** -/
theorem sLogEmbedding_smul {S : Set (HeightOneSpectrum (𝓞 K))} (σ : L ≃ₐ[K] L)
    (p : SPlace L (placesOverSet K L S)) (x : Lˣ) :
    sLogEmbedding L (placesOverSet K L S) (Additive.ofMul (σ • x)) (σ • p)
      = sLogEmbedding L (placesOverSet K L S) (Additive.ofMul x) p :=
  sLog_smul σ p x

end Galois

end NumberField
