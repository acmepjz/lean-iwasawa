# Formalization of Iwasawa Theory in LꓱꓯN (tentative)

https://acmepjz.github.io/lean-iwasawa

## Status of the main theorem

Iwasawa's theorem on the growth of class groups in a `ℤₚ`-extension is proved without any `sorry`.

* The library `Iwasawalib` contains no `sorry`. The class field theory needed is isolated in two
  statements, `NumberField.HilbertClassFieldUpperBound` and `NumberField.HilbertClassFieldExistence`
  (`Iwasawalib/NumberTheory/NumberField/HilbertClassField/Hypothesis.lean`), from which
  `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf`
  (`Iwasawalib/NumberTheory/ZpExtension/IwasawaTheoremOfHCF.lean`) proves the theorem.
* The nested package `IwasawalibCFT` (directory `IwasawalibCFT/`, not built by the root package
  or its CI) proves those two statements with the `sorry`-free class field theory library
  [n-yamaguchi-0729/ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory)
  (pinned at commit `2e6280f9`) and states the unconditional theorem
  `MvZpExtension.multiplicity_classNumber_Kn_eq₁` (`IwasawalibCFT/IwasawalibCFT/Iwasawa.lean`),
  whose axioms are `propext`, `Classical.choice`, `Quot.sound` only. Build it with
  `cd IwasawalibCFT && lake build` (this also compiles the external library).

Until September 2026 `Iwasawalib` also contained a version of the theorem proved from class field
theory `sorry`s; it has been removed.
