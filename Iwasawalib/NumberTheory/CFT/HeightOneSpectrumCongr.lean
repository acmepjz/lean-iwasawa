/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.AdicCompletionCongr

@[expose] public section

/-!
# Functoriality of the height one spectrum and of adic completions

`IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv` is functorial: it sends
`RingEquiv.refl` to `Equiv.refl`, a composite to a composite, and an inverse to an inverse.
The same is true of `IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr`, except that
there the statements carry a valuation-compatibility hypothesis, and composing two of them
changes the index at which the source completion is taken; the index bookkeeping is packaged
in `adicCompletionCongr_index_congr`.

These are the inputs needed to upgrade the induced map on finite adele rings from a ring
homomorphism to a ring isomorphism, and hence to a group action.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv_refl`,
  `..._trans`, `..._symm` : functoriality of `equivOfRingEquiv`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr_refl`,
  `..._comp`, `..._symm_apply` : functoriality of `adicCompletionCongr`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr_index_congr` : transporting the
  source index of `adicCompletionCongr` along an equality of places.
-/

noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

/-! ## Functoriality of `equivOfRingEquiv` -/

section Spectrum

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

@[simp]
theorem equivOfRingEquiv_refl : equivOfRingEquiv (RingEquiv.refl A) = Equiv.refl _ := by
  ext v x
  simp [equivOfRingEquiv]

theorem equivOfRingEquiv_trans (e : A ≃+* B) (e' : B ≃+* C) :
    equivOfRingEquiv (e.trans e') = (equivOfRingEquiv e).trans (equivOfRingEquiv e') := by
  ext v x
  simp only [equivOfRingEquiv, Equiv.trans_apply, Equiv.coe_fn_mk, comap_asIdeal,
    Ideal.mem_comap, RingHom.coe_coe, RingEquiv.symm_trans_apply]

theorem equivOfRingEquiv_symm (e : A ≃+* B) :
    equivOfRingEquiv e.symm = (equivOfRingEquiv e).symm := by
  ext v x
  simp [equivOfRingEquiv]

theorem equivOfRingEquiv_trans_apply (e : A ≃+* B) (e' : B ≃+* C) (v : HeightOneSpectrum A) :
    equivOfRingEquiv (e.trans e') v = equivOfRingEquiv e' (equivOfRingEquiv e v) := by
  rw [equivOfRingEquiv_trans]; rfl

theorem equivOfRingEquiv_trans_symm_apply (e : A ≃+* B) (e' : B ≃+* C)
    (u : HeightOneSpectrum C) :
    (equivOfRingEquiv (e.trans e')).symm u =
      (equivOfRingEquiv e).symm ((equivOfRingEquiv e').symm u) := by
  rw [equivOfRingEquiv_trans]; rfl

theorem equivOfRingEquiv_refl_symm_apply (v : HeightOneSpectrum A) :
    (equivOfRingEquiv (RingEquiv.refl A)).symm v = v := by
  rw [equivOfRingEquiv_refl]; rfl

end Spectrum

/-! ## Functoriality of `adicCompletionCongr` -/

section Completion

variable {A B C K L M : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B]
  [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L] [IsFractionRing B L]
  [Field M] [Algebra C M] [IsFractionRing C M]

/-- Transporting the source index of `adicCompletionCongr` along an equality of places. -/
theorem adicCompletionCongr_index_congr {v v' : HeightOneSpectrum A} (hv : v = v')
    (w : HeightOneSpectrum B) (f : K ≃+* L)
    (hfv : ∀ x : K, w.valuation L (f x) = v.valuation K x)
    (hfv' : ∀ x : K, w.valuation L (f x) = v'.valuation K x)
    (x : ∀ t : HeightOneSpectrum A, t.adicCompletion K) :
    adicCompletionCongr f v w hfv (x v) = adicCompletionCongr f v' w hfv' (x v') := by
  subst hv; rfl

/-- `adicCompletionCongr` only depends on the underlying function of the isomorphism. -/
theorem adicCompletionCongr_congr_equiv {f f' : K ≃+* L} (hff : ∀ x : K, f x = f' x)
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    (hfv : ∀ x : K, w.valuation L (f x) = v.valuation K x)
    (hfv' : ∀ x : K, w.valuation L (f' x) = v.valuation K x) (z : v.adicCompletion K) :
    adicCompletionCongr f v w hfv z = adicCompletionCongr f' v w hfv' z := by
  have h : f = f' := RingEquiv.ext hff
  subst h; rfl

/-- An automorphism of `K` acting as the identity induces the identity of the `v`-adic
completion. -/
theorem adicCompletionCongr_id (f : K ≃+* K) (v : HeightOneSpectrum A)
    (h : ∀ x : K, v.valuation K (f x) = v.valuation K x) (hid : ∀ x : K, f x = x)
    (z : v.adicCompletion K) : adicCompletionCongr f v v h z = z := by
  have hcont : Continuous (adicCompletionCongr f v v h) :=
    continuous_adicCompletionCongr f v v h
  have := Continuous.ext_on (denseRange_algebraMap (R := A) (K := K) (v := v))
    hcont continuous_id ?_
  · exact congrFun this z
  · rintro _ ⟨k, rfl⟩
    show adicCompletionCongr f v v h ((k : K) : v.adicCompletion K)
        = ((k : K) : v.adicCompletion K)
    rw [adicCompletionCongr_coe, hid]

/-- Transporting the source index of `adicCompletionCongr` along an equality of indices in an
arbitrary indexing family of places. -/
theorem adicCompletionCongr_index_congr' {ι : Type*} (p : ι → HeightOneSpectrum A)
    {i i' : ι} (hi : i = i') (w : HeightOneSpectrum B) (f : K ≃+* L)
    (hfv : ∀ x : K, w.valuation L (f x) = (p i).valuation K x)
    (hfv' : ∀ x : K, w.valuation L (f x) = (p i').valuation K x)
    (x : ∀ j : ι, (p j).adicCompletion K) :
    adicCompletionCongr f (p i) w hfv (x i) = adicCompletionCongr f (p i') w hfv' (x i') := by
  subst hi; rfl

/-- The identity of `K` induces the identity of the `v`-adic completion. -/
theorem adicCompletionCongr_refl (v : HeightOneSpectrum A)
    (h : ∀ x : K, v.valuation K (RingEquiv.refl K x) = v.valuation K x)
    (z : v.adicCompletion K) : adicCompletionCongr (RingEquiv.refl K) v v h z = z :=
  adicCompletionCongr_id _ v h (fun _ ↦ rfl) z

/-- Composing two `adicCompletionCongr`s. -/
theorem adicCompletionCongr_comp (f : K ≃+* L) (g : L ≃+* M)
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (u : HeightOneSpectrum C)
    (hfv : ∀ x : K, w.valuation L (f x) = v.valuation K x)
    (hgw : ∀ y : L, u.valuation M (g y) = w.valuation L y)
    (hfg : ∀ x : K, u.valuation M ((f.trans g) x) = v.valuation K x)
    (z : v.adicCompletion K) :
    adicCompletionCongr g w u hgw (adicCompletionCongr f v w hfv z)
      = adicCompletionCongr (f.trans g) v u hfg z := by
  have hcont₁ : Continuous fun z : v.adicCompletion K ↦
      adicCompletionCongr g w u hgw (adicCompletionCongr f v w hfv z) :=
    (continuous_adicCompletionCongr g w u hgw).comp (continuous_adicCompletionCongr f v w hfv)
  have hcont₂ : Continuous (adicCompletionCongr (f.trans g) v u hfg) :=
    continuous_adicCompletionCongr (f.trans g) v u hfg
  have := Continuous.ext_on (denseRange_algebraMap (R := A) (K := K) (v := v))
    hcont₁ hcont₂ ?_
  · exact congrFun this z
  · rintro _ ⟨k, rfl⟩
    show adicCompletionCongr g w u hgw (adicCompletionCongr f v w hfv
          ((k : K) : v.adicCompletion K))
        = adicCompletionCongr (f.trans g) v u hfg ((k : K) : v.adicCompletion K)
    rw [adicCompletionCongr_coe, adicCompletionCongr_coe, adicCompletionCongr_coe]
    rfl

/-- The inverse of `adicCompletionCongr f v w` is `adicCompletionCongr f.symm w v`. -/
theorem adicCompletionCongr_symm_apply (f : K ≃+* L)
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    (hfv : ∀ x : K, w.valuation L (f x) = v.valuation K x)
    (hfv' : ∀ y : L, v.valuation K (f.symm y) = w.valuation L y)
    (z : w.adicCompletion L) :
    (adicCompletionCongr f v w hfv).symm z = adicCompletionCongr f.symm w v hfv' z := by
  have h : ∀ y : w.adicCompletion L,
      adicCompletionCongr f v w hfv (adicCompletionCongr f.symm w v hfv' y) = y := by
    intro y
    refine (adicCompletionCongr_comp f.symm f w v w hfv' hfv (fun x ↦ by simp) y).trans ?_
    exact adicCompletionCongr_id (A := B) (K := L) _ w _ (fun y ↦ by simp) y
  exact ((adicCompletionCongr f v w hfv).symm_apply_eq).2 (h z).symm

end Completion

/-! ## The action of a group of ring automorphisms on the height one spectrum -/

section Action

open scoped Pointwise

variable {B G : Type*} [CommRing B] [IsDedekindDomain B] [Group G] [MulSemiringAction G B]

variable (B G) in
/-- A group acting on a Dedekind domain `B` by ring automorphisms permutes the height one
spectrum of `B`. -/
def spectrumPerm : G →* Equiv.Perm (HeightOneSpectrum B) where
  toFun σ := equivOfRingEquiv (MulSemiringAction.toRingAut G B σ)
  map_one' := by rw [map_one]; exact equivOfRingEquiv_refl
  map_mul' σ τ := by
    rw [map_mul]
    exact equivOfRingEquiv_trans _ _

/-- The action of a group of ring automorphisms of `B` on the height one spectrum of `B`. -/
instance instMulActionSpectrum : MulAction G (HeightOneSpectrum B) :=
  MulAction.compHom _ (spectrumPerm B G)

omit [IsDedekindDomain B] in
theorem smul_def (σ : G) (w : HeightOneSpectrum B) :
    σ • w = equivOfRingEquiv (MulSemiringAction.toRingAut G B σ) w := rfl

omit [IsDedekindDomain B] in
@[simp]
theorem smul_asIdeal (σ : G) (w : HeightOneSpectrum B) :
    (σ • w).asIdeal = σ • w.asIdeal := by
  rw [smul_def, asIdeal_equivOfRingEquiv, Ideal.pointwise_smul_def]
  rfl

omit [IsDedekindDomain B] in
theorem inv_smul_eq_symm (σ : G) (w : HeightOneSpectrum B) :
    σ⁻¹ • w = (equivOfRingEquiv (MulSemiringAction.toRingAut G B σ)).symm w := by
  have : (spectrumPerm B G) σ⁻¹ = ((spectrumPerm B G) σ)⁻¹ := map_inv _ _
  exact congrFun (congrArg (fun p : Equiv.Perm (HeightOneSpectrum B) ↦ ⇑p) this) w

omit [IsDedekindDomain B] in
@[simp]
theorem smul_inv_smul_spectrum (σ : G) (w : HeightOneSpectrum B) : σ • σ⁻¹ • w = w :=
  smul_inv_smul σ w

end Action

end IsDedekindDomain.HeightOneSpectrum
