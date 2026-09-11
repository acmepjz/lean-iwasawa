/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.Herbrand

@[expose] public section

/-!
# The Tate cohomology of a regularly induced module vanishes

Let `G = ⟨σ⟩` be a finite cyclic group and let `M` be a `G`-module which, as an abelian group,
is identified with the functions `G → N` on the group itself in such a way that `G` acts by
translating the index:

`e (g • m) x = e m (g⁻¹ * x)`.

This is the module `Ind_1^G N = N[G]` induced from the trivial subgroup — in the number-theoretic
application, the `𝒪_v`-lattice spanned by a normal basis of `L_w / K_v`, on which the
decomposition group permutes the basis simply transitively.  Both Tate groups vanish:

* `CyclicTate.subsingleton_tateH0_of_regular`,
* `CyclicTate.subsingleton_tateH1_of_regular`,

and hence `h(G, M) = 1` (`CyclicTate.herbrand_eq_one_of_regular`).

Rather than introducing a new type for the induced module, the hypothesis is carried as an
additive equivalence `e : M ≃+ (G → N)` together with the translation law `he`.  A caller
therefore never has to transport its module along an isomorphism: it exhibits `e` and is done.

## Proof

`Ĥ⁰` is the easy half.  A `σ`-invariant `m` is `G`-invariant, so `e m` is a constant function
`c`, and `c` is the norm of the `δ`-function `Pi.single 1 c`, because the norm of `F` is the
constant function with value `∑ y : G, F y` (`CyclicTate.apply_normHom_of_regular`).

`Ĥ¹` is the half that genuinely uses the indexing by `G`: no `ℤ[G]`-linear formula in `F` can
solve `σ • H - H = F` (such a formula would have to divide by `#G`).  The solution is a
*partial sum along the orbit of `σ`*: `H (σ ^ i) = -∑_{j < i} F (σ ^ (j + 1))`.  This is
well defined precisely because `∑_{y : G} F y = 0`, which makes the partial sum periodic with
period `orderOf σ` (`CyclicTate.partialSum_add_orderOf`); the value at a group element is read
off from *any* exponent presenting it (`CyclicTate.partialSum_congr_pow`).
-/

noncomputable section

namespace CyclicTate

section Regular

variable {G : Type*} [Group G] [Fintype G] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [DistribMulAction G M] {σ : G}

omit [Fintype G] in
/-- A `σ`-invariant element of a cyclic module is invariant. -/
theorem smul_eq_self_of_pow (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) {m : M} (hm : σ • m = m)
    (g : G) : g • m = m := by
  obtain ⟨k, rfl⟩ := hgen g
  induction k with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, hm, ih]

variable (e : M ≃+ (G → N))
  (he : ∀ (g : G) (m : M) (x : G), e (g • m) x = e m (g⁻¹ * x))

include he

/-- **The norm of a regularly induced module is the total sum.**  `N(m)` corresponds to the
constant function with value `∑ y : G, (e m) y`. -/
theorem apply_normHom_of_regular (m : M) (x : G) :
    e (normHom G M m) x = ∑ y : G, e m y := by
  rw [normHom_apply, map_sum, Finset.sum_apply]
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x)) _ _ fun g ↦ ?_
  exact he g m x

/-- **`Ĥ⁰(G, Ind_1^G N) = 0`.** -/
theorem subsingleton_tateH0_of_regular (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) :
    Subsingleton (TateH0 G M σ) := by
  classical
  rw [tateH0_subsingleton_iff]
  intro m hm
  -- `e m` is a constant function
  have hconst : ∀ x : G, e m x = e m 1 := by
    intro x
    have := he x⁻¹ m 1
    rw [smul_eq_self_of_pow hgen hm x⁻¹, inv_inv, mul_one] at this
    exact this.symm
  refine ⟨e.symm (Pi.single 1 (e m 1)), ?_⟩
  refine e.injective (funext fun x ↦ ?_)
  rw [apply_normHom_of_regular e he, e.apply_symm_apply, hconst x]
  refine (Finset.sum_eq_single_of_mem (1 : G) (Finset.mem_univ _) ?_).trans ?_
  · exact fun b _ hb ↦ Pi.single_eq_of_ne hb _
  · exact Pi.single_eq_same _ _

/-! ### The partial sum along the orbit -/

variable (F : G → N)

/-- The partial sum `∑_{j < i} F (σ ^ (j + 1))` along the orbit of `σ`. -/
def partialSum (σ : G) (F : G → N) (i : ℕ) : N := ∑ j ∈ Finset.range i, F (σ ^ (j + 1))

omit he [Fintype G] in
theorem partialSum_succ (i : ℕ) :
    partialSum σ F (i + 1) = partialSum σ F i + F (σ ^ (i + 1)) :=
  Finset.sum_range_succ _ _

omit he in
/-- `orderOf σ = #G` for a generator. -/
theorem orderOf_eq_card_of_pow (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) :
    orderOf σ = Fintype.card G := by
  rw [← Nat.card_eq_fintype_card]
  refine orderOf_eq_card_of_forall_mem_zpowers fun x ↦ ?_
  obtain ⟨k, hk⟩ := hgen x
  exact Subgroup.mem_zpowers_iff.2 ⟨(k : ℤ), by rw [zpow_natCast]; exact hk⟩

omit he in
/-- **A full period of the orbit sums to the total sum.** -/
theorem sum_range_orderOf (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) (a : ℕ) :
    ∑ j ∈ Finset.range (orderOf σ), F (σ ^ (a + j)) = ∑ y : G, F y := by
  classical
  have hinj : ∀ j ∈ Finset.range (orderOf σ), ∀ j' ∈ Finset.range (orderOf σ),
      σ ^ (a + j) = σ ^ (a + j') → j = j' := by
    intro j hj j' hj' h
    rw [pow_add, pow_add] at h
    have h' : σ ^ j = σ ^ j' := mul_left_cancel h
    exact pow_injOn_Iio_orderOf (Finset.mem_range.1 hj) (Finset.mem_range.1 hj') h'
  have himg : (Finset.range (orderOf σ)).image (fun j ↦ σ ^ (a + j)) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_image_of_injOn (fun j hj j' hj' h ↦ hinj j hj j' hj' h), Finset.card_range,
      orderOf_eq_card_of_pow hgen]
  rw [← himg, Finset.sum_image (fun j hj j' hj' h ↦ hinj j hj j' hj' h)]

omit he in
/-- **The partial sum is periodic**, with period `orderOf σ`, as soon as the total sum vanishes. -/
theorem partialSum_add_orderOf (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) (hF : ∑ y : G, F y = 0)
    (i : ℕ) : partialSum σ F (i + orderOf σ) = partialSum σ F i := by
  have := sum_range_orderOf F hgen (i + 1)
  rw [hF] at this
  simp only [partialSum, Finset.sum_range_add]
  rw [show (∑ j ∈ Finset.range (orderOf σ), F (σ ^ (i + j + 1)))
      = ∑ j ∈ Finset.range (orderOf σ), F (σ ^ (i + 1 + j)) from
    Finset.sum_congr rfl fun j _ ↦ by rw [show i + j + 1 = i + 1 + j by omega], this, add_zero]

omit he in
theorem partialSum_add_mul_orderOf (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) (hF : ∑ y : G, F y = 0)
    (i k : ℕ) : partialSum σ F (i + orderOf σ * k) = partialSum σ F i := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [show i + orderOf σ * (n + 1) = (i + orderOf σ * n) + orderOf σ by ring,
        partialSum_add_orderOf F hgen hF, ih]

omit he in
theorem partialSum_mod (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) (hF : ∑ y : G, F y = 0) (a : ℕ) :
    partialSum σ F a = partialSum σ F (a % orderOf σ) := by
  conv_lhs => rw [← Nat.mod_add_div a (orderOf σ)]
  exact partialSum_add_mul_orderOf F hgen hF _ _

omit he in
/-- **The partial sum depends only on the group element `σ ^ a`.** -/
theorem partialSum_congr_pow (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) (hF : ∑ y : G, F y = 0)
    {a b : ℕ} (hab : σ ^ a = σ ^ b) : partialSum σ F a = partialSum σ F b := by
  rw [partialSum_mod F hgen hF a, partialSum_mod F hgen hF b]
  exact congrArg _ ((pow_eq_pow_iff_modEq (x := σ)).1 hab)

/-- **`Ĥ¹(G, Ind_1^G N) = 0`.** -/
theorem subsingleton_tateH1_of_regular (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) :
    Subsingleton (TateH1 G M σ) := by
  classical
  rw [tateH1_subsingleton_iff]
  intro m hm
  have hF : ∑ y : G, (e m) y = 0 := by
    have h1 := apply_normHom_of_regular e he m 1
    rw [hm, map_zero] at h1
    exact h1.symm
  have hidx : ∀ x : G, σ ^ (hgen x).choose = x := fun x ↦ (hgen x).choose_spec
  have hH : ∀ (k : ℕ) (x : G), σ ^ k = x →
      -partialSum σ (e m) (hgen x).choose = -partialSum σ (e m) k := fun k x hk ↦
    congrArg Neg.neg (partialSum_congr_pow (e m) hgen hF (by rw [hidx x, hk]))
  refine ⟨e.symm (fun y ↦ -partialSum σ (e m) (hgen y).choose), ?_⟩
  refine e.injective (funext fun x ↦ ?_)
  rw [map_sub, Pi.sub_apply, he σ _ x, e.apply_symm_apply]
  obtain ⟨k, hk⟩ := hgen x
  have hd : 0 < orderOf σ := orderOf_pos σ
  have hx : σ ^ (k + (orderOf σ - 1) + 1) = x := by
    rw [show k + (orderOf σ - 1) + 1 = k + orderOf σ by omega, pow_add, pow_orderOf_eq_one,
      mul_one, hk]
  have hx' : σ ^ (k + (orderOf σ - 1)) = σ⁻¹ * x := by
    rw [← hx, pow_succ', inv_mul_cancel_left]
  rw [hH _ x hx, hH _ _ hx', partialSum_succ, hx]
  abel

/-- **The Herbrand quotient of a regularly induced module is `1`.** -/
theorem herbrand_eq_one_of_regular (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) :
    herbrand G M σ = 1 := by
  haveI := subsingleton_tateH0_of_regular e he hgen
  haveI := subsingleton_tateH1_of_regular e he hgen
  exact herbrand_eq_one_of_subsingleton σ

/-- The Tate groups of a regularly induced module are finite (they vanish). -/
theorem finite_tateH0_of_regular (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) :
    Finite (TateH0 G M σ) :=
  haveI := subsingleton_tateH0_of_regular e he hgen
  Finite.of_subsingleton

theorem finite_tateH1_of_regular (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g) :
    Finite (TateH1 G M σ) :=
  haveI := subsingleton_tateH1_of_regular e he hgen
  Finite.of_subsingleton

end Regular

/-! ## The commensurability criterion -/

section Lattice

variable {G : Type*} [Group G] [Fintype G] {B N : Type*} [AddCommGroup B] [AddCommGroup N]
  [DistribMulAction G B] {σ : G}

/-- The translation action of `G` on `G → N`, which realises `G → N` as the regularly induced
module `Ind_1^G N`.  It is not a global instance: a caller enables it with
`attribute [local instance] CyclicTate.regularAction`. -/
@[reducible] def regularAction (G : Type*) [Group G] (N : Type*) [AddCommGroup N] :
    DistribMulAction G (G → N) where
  smul g F := fun x ↦ F (g⁻¹ * x)
  one_smul F := by
    funext x; show F (1⁻¹ * x) = F x; rw [inv_one, one_mul]
  mul_smul g h F := by
    funext x; show F ((g * h)⁻¹ * x) = F (h⁻¹ * (g⁻¹ * x)); rw [mul_inv_rev, mul_assoc]
  smul_zero g := rfl
  smul_add g F H := rfl

/-- **A module containing a regularly induced module with finite index has Herbrand quotient
`1`.**

`f` embeds `Ind_1^G N = N[G]` into the `G`-module `B` — in the application, `B` is the ring of
integers `O_w` of a local field, `N` the ring of integers `O_v` of the base, and `f` sends a
tuple of coefficients to the corresponding combination of a normal basis, scaled so as to land
in `O_w` — and the image has finite index.  Since the Herbrand quotient is a commensurability
invariant (`CyclicTate.herbrand_eq_of_finite_ker_coker`) and vanishes on induced modules
(`CyclicTate.herbrand_eq_one_of_regular`), `h(G, B) = 1`.

No instance on `G → N` appears in the statement: the translation action is introduced inside
the proof, and the hypothesis `hf` says in elementary terms that `f` intertwines translation
of the index with the action on `B`. -/
theorem herbrand_eq_one_of_regularLattice (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g)
    (f : (G → N) →+ B) (hf : ∀ (g : G) (F : G → N), f (fun x ↦ F (g⁻¹ * x)) = g • f F)
    (hinj : Function.Injective f) (hcoker : Finite (B ⧸ f.range)) :
    herbrand G B σ = 1 := by
  letI : DistribMulAction G (G → N) := regularAction G N
  have hsmul : ∀ (g : G) (F : G → N), g • F = fun x ↦ F (g⁻¹ * x) := fun _ _ ↦ rfl
  let f' : (G → N) →+[G] B :=
    { toFun := f
      map_smul' := fun g F ↦ by rw [hsmul]; exact hf g F
      map_zero' := f.map_zero
      map_add' := f.map_add }
  have hrange : f'.toAddMonoidHom.range = f.range := rfl
  haveI : Finite (TateH0 G (G → N) σ) :=
    finite_tateH0_of_regular (AddEquiv.refl (G → N)) (fun _ _ _ ↦ rfl) hgen
  haveI : Finite (TateH1 G (G → N) σ) :=
    finite_tateH1_of_regular (AddEquiv.refl (G → N)) (fun _ _ _ ↦ rfl) hgen
  haveI : Finite f'.toAddMonoidHom.ker := by
    have h0 : f'.toAddMonoidHom.ker = (⊥ : AddSubgroup (G → N)) :=
      (AddMonoidHom.ker_eq_bot_iff _).2 hinj
    rw [h0]
    infer_instance
  haveI : Finite (B ⧸ f'.toAddMonoidHom.range) := by rw [hrange]; exact hcoker
  rw [← herbrand_eq_of_finite_ker_coker f' σ]
  exact herbrand_eq_one_of_regular (AddEquiv.refl (G → N)) (fun _ _ _ ↦ rfl) hgen

/-- **Finiteness of `Ĥ⁰` transfers along a map with finite kernel and cokernel.**  This is the
finiteness that `CyclicTate.herbrand_eq_of_finite_ker_coker` establishes internally but does not
export. -/
theorem finite_tateH0_of_finite_ker_coker {A : Type*} [AddCommGroup A] [DistribMulAction G A]
    (f : A →+[G] B) (σ : G) [Finite f.toAddMonoidHom.ker] [Finite (B ⧸ f.toAddMonoidHom.range)]
    [Finite (TateH0 G A σ)] [Finite (TateH1 G A σ)] : Finite (TateH0 G B σ) := by
  have h₁ := isShortExact_ker_range f
  have h₂ := isShortExact_stableQuotient G f.toAddMonoidHom.range
  haveI : Finite (TateH0 G f.toAddMonoidHom.range σ) := h₁.finite_tateH0_right σ
  haveI : Finite (TateH1 G f.toAddMonoidHom.range σ) := h₁.finite_tateH1_right σ
  exact h₂.finite_tateH0_mid σ

/-- **Finiteness of `Ĥ¹` transfers along a map with finite kernel and cokernel.** -/
theorem finite_tateH1_of_finite_ker_coker {A : Type*} [AddCommGroup A] [DistribMulAction G A]
    (f : A →+[G] B) (σ : G) [Finite f.toAddMonoidHom.ker] [Finite (B ⧸ f.toAddMonoidHom.range)]
    [Finite (TateH0 G A σ)] [Finite (TateH1 G A σ)] : Finite (TateH1 G B σ) := by
  have h₁ := isShortExact_ker_range f
  have h₂ := isShortExact_stableQuotient G f.toAddMonoidHom.range
  haveI : Finite (TateH0 G f.toAddMonoidHom.range σ) := h₁.finite_tateH0_right σ
  haveI : Finite (TateH1 G f.toAddMonoidHom.range σ) := h₁.finite_tateH1_right σ
  exact h₂.finite_tateH1_mid σ

/-- The Tate cohomology of a module containing a regularly induced module with finite index is
finite. -/
theorem finite_tateH0_of_regularLattice (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g)
    (f : (G → N) →+ B) (hf : ∀ (g : G) (F : G → N), f (fun x ↦ F (g⁻¹ * x)) = g • f F)
    (hinj : Function.Injective f) (hcoker : Finite (B ⧸ f.range)) :
    Finite (TateH0 G B σ) := by
  letI : DistribMulAction G (G → N) := regularAction G N
  let f' : (G → N) →+[G] B :=
    { toFun := f
      map_smul' := fun g F ↦ hf g F
      map_zero' := f.map_zero
      map_add' := f.map_add }
  haveI : Finite (TateH0 G (G → N) σ) :=
    finite_tateH0_of_regular (AddEquiv.refl (G → N)) (fun _ _ _ ↦ rfl) hgen
  haveI : Finite (TateH1 G (G → N) σ) :=
    finite_tateH1_of_regular (AddEquiv.refl (G → N)) (fun _ _ _ ↦ rfl) hgen
  haveI : Finite f'.toAddMonoidHom.ker := by
    have h0 : f'.toAddMonoidHom.ker = (⊥ : AddSubgroup (G → N)) :=
      (AddMonoidHom.ker_eq_bot_iff _).2 hinj
    rw [h0]
    infer_instance
  haveI : Finite (B ⧸ f'.toAddMonoidHom.range) := hcoker
  exact finite_tateH0_of_finite_ker_coker f' σ

/-- The Tate cohomology of a module containing a regularly induced module with finite index is
finite. -/
theorem finite_tateH1_of_regularLattice (hgen : ∀ g : G, ∃ k : ℕ, σ ^ k = g)
    (f : (G → N) →+ B) (hf : ∀ (g : G) (F : G → N), f (fun x ↦ F (g⁻¹ * x)) = g • f F)
    (hinj : Function.Injective f) (hcoker : Finite (B ⧸ f.range)) :
    Finite (TateH1 G B σ) := by
  letI : DistribMulAction G (G → N) := regularAction G N
  let f' : (G → N) →+[G] B :=
    { toFun := f
      map_smul' := fun g F ↦ hf g F
      map_zero' := f.map_zero
      map_add' := f.map_add }
  haveI : Finite (TateH0 G (G → N) σ) :=
    finite_tateH0_of_regular (AddEquiv.refl (G → N)) (fun _ _ _ ↦ rfl) hgen
  haveI : Finite (TateH1 G (G → N) σ) :=
    finite_tateH1_of_regular (AddEquiv.refl (G → N)) (fun _ _ _ ↦ rfl) hgen
  haveI : Finite f'.toAddMonoidHom.ker := by
    have h0 : f'.toAddMonoidHom.ker = (⊥ : AddSubgroup (G → N)) :=
      (AddMonoidHom.ker_eq_bot_iff _).2 hinj
    rw [h0]
    infer_instance
  haveI : Finite (B ⧸ f'.toAddMonoidHom.range) := hcoker
  exact finite_tateH1_of_finite_ker_coker f' σ

end Lattice

end CyclicTate
