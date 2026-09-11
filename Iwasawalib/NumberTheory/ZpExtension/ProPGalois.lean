/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.Topology.Algebra.ProP
public import Iwasawalib.FieldTheory.IntermediateField.MaximalGaloisSExtension
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.KrullTopology

@[expose] public section

/-!
# The Galois group of a `{p}`-extension is pro-`p`

If `L / F` is Galois and every finite subextension has `p`-power degree — that is,
`IsSExtension F L {p}` — then `Gal(L/F)` with its Krull topology is pro-`p` in the sense of
`IsProP`.

The proof is the usual one.  A neighbourhood of `1` contains `Gal(L/E)` for some finite
*normal* subextension `E / F` (`krullTopology_mem_nhds_one_iff_of_normal`).  Then `Gal(E/F)` is
a finite group of order `[E : F] = p ^ k`, so every `σ : Gal(L/F)` satisfies
`σ ^ (p ^ k) ∈ ker (restrictNormalHom E) = Gal(L/E)`.
-/

open Topology IntermediateField

/-- **The Galois group of a `{p}`-extension is pro-`p`.** -/
theorem isProP_galoisGroup (p : ℕ) [Fact p.Prime] (F L : Type*) [Field F] [Field L]
    [Algebra F L] [IsGalois F L] [IsSExtension F L {p}] : IsProP p Gal(L/F) := by
  intro s hs
  obtain ⟨E, hfin, hnorm, hE⟩ := (krullTopology_mem_nhds_one_iff_of_normal F L s).1 hs
  haveI : FiniteDimensional F E := hfin
  haveI : Normal F E := hnorm
  haveI : Algebra.IsSeparable F E :=
    Algebra.isSeparable_tower_bot_of_isSeparable F E L
  haveI : IsGalois F E := ⟨⟩
  haveI : IsSExtension F E {p} :=
    (isSExtension_iff_of_finiteDimensional F E {p}).2
      (IsSExtension.primeFactors_subset_of_intermediateField {p} E)
  obtain ⟨k, hk⟩ := (isSExtension_singleton_iff_of_finiteDimensional F E p).1 inferInstance
  refine ⟨k, fun σ ↦ hE ?_⟩
  rw [SetLike.mem_coe, ← E.restrictNormalHom_ker, MonoidHom.mem_ker, map_pow, ← hk,
    ← IsGalois.card_aut_eq_finrank F E, Nat.card_eq_fintype_card]
  exact pow_card_eq_one (G := Gal(↥E/F)) (x := AlgEquiv.restrictNormalHom (↥E) σ)
