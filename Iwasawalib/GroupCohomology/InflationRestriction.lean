module

public import Iwasawalib.GroupCohomology.Inflation
public import Iwasawalib.GroupCohomology.DimensionShift

@[expose] public noncomputable section

open
  Rep
  dimensionShift
  groupCohomology
  CategoryTheory
  Limits

variable {R : Type} [CommRing R]
variable {G : Type} [Group G]
variable {Q : Type} [Group Q] {φ : G →* Q} (surj : Function.Surjective φ)

namespace groupCohomology

lemma quotientToInvariantsFunctor'_shortExact_ofShortExact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) (hS' : IsZero (H1 (S.X₁ ↓ φ.ker.subtype))) :
    (S.map (quotientToInvariantsFunctor' surj)).ShortExact := by
  let K := φ.ker
  let e := QuotientGroup.quotientKerEquivOfSurjective φ surj
  let T := S.map (resFunctor K.subtype)
  have h0epi : Epi ((mapShortComplex₃
      ((shortExact_res K.subtype).2 hS) (i := 0) (j := 1) rfl).f) :=
    (mapShortComplex₃_exact ((shortExact_res K.subtype).2 hS) rfl).epi_f
      (hS'.eq_of_tgt _ _)
  have hinvEpi : Epi ((invariantsFunctor R K).map T.g) := by
    have hcomm := map_id_comp_H0Iso_hom T.g
    have hmapEpi : Epi ((functor R K 0).map T.g) := by
      change Epi ((mapShortComplex₃
        ((shortExact_res K.subtype).2 hS) (i := 0) (j := 1) rfl).f)
      exact h0epi
    rw [ModuleCat.epi_iff_surjective] at hmapEpi ⊢
    intro y
    obtain ⟨x, hx⟩ := hmapEpi ((H0Iso T.X₃).inv y)
    refine ⟨(H0Iso T.X₂).hom x, ?_⟩
    have hc := ConcreteCategory.congr_hom hcomm x
    change (H0Iso T.X₃).hom ((functor R K 0).map T.g x) =
      (invariantsFunctor R K).map T.g ((H0Iso T.X₂).hom x) at hc
    rw [← hc, hx]
    simp
  have hquotEpi : Epi ((S.map (quotientToInvariantsFunctor' surj)).g) := by
    have hcanonical : Epi ((quotientToInvariantsFunctor R K).map S.g) := by
      rw [Rep.epi_iff_surjective]
      rw [ModuleCat.epi_iff_surjective] at hinvEpi
      intro y
      obtain ⟨x, hx⟩ := hinvEpi y
      exact ⟨x, Subtype.ext (congr_arg Subtype.val hx)⟩
    change Epi ((resEquiv R e).inverse.map ((quotientToInvariantsFunctor R K).map S.g))
    exact Functor.map_epi _ _
  have hquotMono : Mono ((S.map (quotientToInvariantsFunctor' surj)).f) := by
    have hcanonical : Mono ((quotientToInvariantsFunctor R K).map S.f) := by
      rw [Rep.mono_iff_injective]
      exact fun x y hxy => Subtype.ext <| (Rep.mono_iff_injective S.f).1 hS.mono_f
        (congr_arg Subtype.val hxy)
    change Mono ((resEquiv R e).inverse.map
      ((quotientToInvariantsFunctor R K).map S.f))
    exact Functor.map_mono _ _
  have hquotExact : (S.map (quotientToInvariantsFunctor' surj)).Exact := by
    rw [ShortComplex.ShortExact.rep_exact_iff_function_exact]
    have hex := ShortComplex.ShortExact.rep_exact_iff_function_exact.mp hS.exact
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := (hex x.val).mp (congr_arg Subtype.val hx)
      refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
      intro k
      apply (Rep.mono_iff_injective S.f).1 hS.mono_f
      change S.f.hom (S.X₁.ρ k.1 a) = S.f.hom a
      rw [hom_comm_apply S.f, ha]
      exact x.property k
    · rintro ⟨a, rfl⟩
      apply Subtype.ext
      exact (hex _).mpr ⟨a.val, rfl⟩
  exact { exact := hquotExact, mono_f := hquotMono, epi_g := hquotEpi }

lemma infl_comp_rest_zero (n : ℕ) (M : Rep R G) :
    (infl surj (n + 1)).app M ≫ (rest φ.ker.subtype (n + 1)).app M = 0 := by
  let K := φ.ker
  let A := M ↑ surj
  let f : PUnit →* Q := 1
  let g : K →* PUnit := 1
  let B : Rep R PUnit := A ↓ f
  let ι : B →ₗ[R] M :=
    { toFun := fun v => v.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let β : B ↓ g ⟶ M ↓ K.subtype := Rep.ofHom ⟨ι, fun k => by
      ext v
      simp only [LinearMap.comp_apply, MonoidHom.comp_apply]
      rw [show g k = 1 by simp [g], map_one, Module.End.one_apply]
      change v.val = M.ρ k.1 v.val
      exact (v.property k).symm⟩
  simp only [infl, NatTrans.hcomp_app] at *
  change map φ (res_quotientToInvariantsFunctor'_ι surj M) (n + 1) ≫
    map K.subtype (𝟙 _) (n + 1) = 0
  rw [← map_comp]
  calc
    map (φ.comp K.subtype)
        ((resFunctor K.subtype).map (res_quotientToInvariantsFunctor'_ι surj M) ≫ 𝟙 _)
        (n + 1) =
      map (f.comp g) ((resFunctor g).map (𝟙 B) ≫ β) (n + 1) := by
        apply map_congr
        · ext x
          exact x.property
        · rfl
    _ = map f (𝟙 B) (n + 1) ≫ map g β (n + 1) := map_comp ..
    _ = 0 := by
      rw [IsZero.eq_zero_of_tgt
        (isZero_groupCohomology_succ_of_subsingleton B n) (map f (𝟙 B) (n + 1)), zero_comp]

lemma infl_one_mono (M : Rep R G) : Mono ((infl surj 1).app M) := by
  rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro z hz
  induction z using H1_induction_on with
  | @h x =>
      simp only [infl, NatTrans.hcomp_app] at hz
      change map φ (res_quotientToInvariantsFunctor'_ι surj M) 1 (H1π _ x) = 0 at hz
      rw [H1π_comp_map_apply] at hz
      rcases (H1π_eq_zero_iff _).1 hz with ⟨y, hy⟩
      have hyinv : y ∈ Representation.invariants (M.ρ.comp φ.ker.subtype) := by
        intro k
        have hk := congr_fun hy k.1
        have hzero : (mapCocycles₁ φ (res_quotientToInvariantsFunctor'_ι surj M) x) k.1 = 0 := by
          change (x (φ k.1)).val = 0
          rw [k.2]
          exact congr_arg Subtype.val (cocycles₁_map_one x)
        rw [hzero] at hk
        have hk' : M.ρ k.1 y - y = 0 := by simpa [d₀₁] using hk
        exact sub_eq_zero.mp hk'
      let yB : M ↑ surj := ⟨y, hyinv⟩
      refine (H1π_eq_zero_iff _).2 ⟨yB, ?_⟩
      ext q
      obtain ⟨g, rfl⟩ := surj q
      have hg := congr_fun hy g
      have hg' : M.ρ g y - y = (x (φ g)).val := by
        change M.ρ g y - y =
          (mapCocycles₁ φ (res_quotientToInvariantsFunctor'_ι surj M) x g)
        simpa [d₀₁] using hg
      apply Subtype.ext
      calc
        _ = (((M ↑ surj).ρ (φ g) yB - yB).val) := by
                rw [d₀₁_hom_apply]
        _ = M.ρ g y - y := by
          change (((M ↑ surj).ρ (φ g) yB).val - yB.val) = M.ρ g y - y
          rw [quotientToInvariantsFunctor'_obj_ρ_apply₂]
        _ = (x (φ g)).val := hg'

def inflationRestriction (n : ℕ) (M : Rep R G) : ShortComplex (ModuleCat R) where
  X₁ := groupCohomology (M ↑ surj) (n + 1)
  X₂ := groupCohomology M (n + 1)
  X₃ := groupCohomology (M ↓ φ.ker.subtype) (n + 1)
  f := (infl surj (n + 1)).app M
  g := (rest φ.ker.subtype (n + 1)).app M
  zero := infl_comp_rest_zero surj n M

set_option backward.isDefEq.respectTransparency false in
theorem inflation_restriction_mono (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ φ.ker.subtype) (i + 1))) :
    Mono (inflationRestriction surj n M).f := by
  induction n generalizing M with
  | zero =>
      exact infl_one_mono surj M
  | succ n ih =>
      have hU : (upSES M).ShortExact := shortExact_upSES M
      have hK1 : IsZero (H1 (M ↓ φ.ker.subtype)) := hM 0 (by omega)
      have hQ : ((upSES M).map (quotientToInvariantsFunctor' surj)).ShortExact :=
        quotientToInvariantsFunctor'_shortExact_ofShortExact surj hU (by simpa using hK1)
      have hUp (i : ℕ) (hi : i < n) :
          IsZero (groupCohomology (up.obj M ↓ φ.ker.subtype) (i + 1)) := by
        letI : NeZero (i + 1) := ⟨by omega⟩
        exact (hM (i + 1) (by omega)).of_iso
          (δUpResIso M φ.ker.subtype_injective (i + 1))
      haveI hmonoUp : Mono ((infl surj (n + 1)).app (up.obj M)) :=
        ih hUp
      haveI hmonoDelta : Mono (δ hU (n + 1) (n + 2) rfl) := by
        haveI : NeZero (n + 1) := ⟨by omega⟩
        haveI : IsIso (δ hU (n + 1) (n + 2) rfl) := inferInstance
        infer_instance
      have hcomm := infl_δ_naturality surj hU hQ (n + 1) (n + 2) rfl
      have hcompU : Mono (δ hQ (n + 1) (n + 2) rfl ≫
          (infl surj (n + 2)).app (upSES M).X₁) := by
        rw [hcomm]
        exact mono_comp' hmonoUp hmonoDelta
      have hcomp : Mono (δ hQ (n + 1) (n + 2) rfl ≫
          (infl surj (n + 2)).app M) := by simpa using hcompU
      have hmid : IsZero (groupCohomology ((coind₁'.obj M) ↑ surj) (n + 2)) :=
        isZero_of_trivialCohomology
      have hdEpi : Epi (δ hQ (n + 1) (n + 2) rfl) := by
        apply epi_δ_of_isZero hQ (n + 1)
        simpa using hmid
      change Mono ((infl surj (n + 2)).app M)
      rw [ModuleCat.mono_iff_injective]
      intro x y hxy
      rw [ModuleCat.epi_iff_surjective] at hdEpi
      obtain ⟨a, ha⟩ := hdEpi x
      obtain ⟨b, hb⟩ := hdEpi y
      change ((infl surj (n + 2)).app M).hom x = ((infl surj (n + 2)).app M).hom y at hxy
      have hc : (δ hQ (n + 1) (n + 2) rfl ≫ (infl surj (n + 2)).app M) a =
          (δ hQ (n + 1) (n + 2) rfl ≫ (infl surj (n + 2)).app M) b := by
        change ((infl surj (n + 2)).app M).hom ((δ hQ (n + 1) (n + 2) rfl).hom a) =
          ((infl surj (n + 2)).app M).hom ((δ hQ (n + 1) (n + 2) rfl).hom b)
        rw [ha, hb]
        exact hxy
      have hab := (ModuleCat.mono_iff_injective _).1 hcomp hc
      rw [← ha, ← hb, hab]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem inflation_restriction_exact (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ φ.ker.subtype) (i + 1))) :
    (inflationRestriction surj n M).Exact := by
  induction n generalizing M with
  | zero =>
      rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      have hcan :=
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (H1InfRes M φ.ker)).mp
          (H1InfRes_exact M φ.ker)
      intro x
      constructor
      · intro hx
        have hxcan : (H1InfRes M φ.ker).g x = 0 := by
          exact hx
        obtain ⟨z, hz⟩ := (hcan x).mp hxcan
        change groupCohomology (M.quotientToInvariants φ.ker) 1 at z
        let e := QuotientGroup.quotientKerEquivOfSurjective φ surj
        let τ := map (A := M.quotientToInvariants φ.ker) (B := M ↑ surj)
          e.symm (𝟙 (M ↑ surj)) 1
        refine ⟨τ z, ?_⟩
        have hfac : τ ≫ (infl surj 1).app M = (H1InfRes M φ.ker).f := by
          simp only [infl, NatTrans.hcomp_app]
          change τ ≫ map φ (res_quotientToInvariantsFunctor'_ι surj M) 1 =
            map (QuotientGroup.mk' φ.ker)
              (Rep.ofHom (M.ρ.quotientToInvariants_lift φ.ker)) 1
          dsimp only [τ]
          rw [← map_comp]
          apply map_congr
          · ext g
            exact QuotientGroup.quotientKerEquivOfSurjective_symm_apply φ surj g
          · rfl
        exact (ConcreteCategory.congr_hom hfac z).trans hz
      · rintro ⟨z, rfl⟩
        exact ConcreteCategory.congr_hom (inflationRestriction surj 0 M).zero z
  | succ n ih =>
      have hU : (upSES M).ShortExact := shortExact_upSES M
      have hK1 : IsZero (H1 (M ↓ φ.ker.subtype)) := hM 0 (by omega)
      have hQ : ((upSES M).map (quotientToInvariantsFunctor' surj)).ShortExact :=
        quotientToInvariantsFunctor'_shortExact_ofShortExact surj hU (by simpa using hK1)
      have hUp (i : ℕ) (hi : i < n) :
          IsZero (groupCohomology (up.obj M ↓ φ.ker.subtype) (i + 1)) := by
        letI : NeZero (i + 1) := ⟨by omega⟩
        exact (hM (i + 1) (by omega)).of_iso
          (δUpResIso M φ.ker.subtype_injective (i + 1))
      have hLower : (inflationRestriction surj n (up.obj M)).Exact := ih hUp
      haveI hδQ : IsIso (δ hQ (n + 1) (n + 2) rfl) := by
        apply isIso_δ_of_isZero hQ (n + 1)
        · simpa only [ShortComplex.map_X₂, upSES_X₂] using
            (isZero_of_trivialCohomology :
              IsZero (groupCohomology ((coind₁'.obj M) ↑ surj) (n + 1)))
        · simpa only [ShortComplex.map_X₂, upSES_X₂] using
            (isZero_of_trivialCohomology :
              IsZero (groupCohomology ((coind₁'.obj M) ↑ surj) (n + 2)))
      letI : NeZero (n + 1) := ⟨by omega⟩
      let e₁ := asIso (δ hQ (n + 1) (n + 2) rfl)
      let e₂ := δUpIso M n
      let e₃ := δUpResIso M φ.ker.subtype_injective (n + 1)
      let e : inflationRestriction surj n (up.obj M) ≅
          inflationRestriction surj (n + 1) M :=
        ShortComplex.isoMk e₁ e₂ e₃
          (by
            dsimp [e₁, e₂, inflationRestriction, δUpIso]
            exact infl_δ_naturality surj hU hQ (n + 1) (n + 2) rfl)
          (by
            dsimp [e₂, e₃, inflationRestriction, δUpIso, δUpResIso]
            exact rest_δ_naturality hU φ.ker.subtype (n + 1) (n + 2) rfl)
      exact ShortComplex.exact_of_iso e hLower

end groupCohomology

end
