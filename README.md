# Formalization of Iwasawa Theory in LꓱꓯN (tentative)

https://acmepjz.github.io/lean-iwasawa

## Status of the main theorem

Iwasawa's theorem on the growth of class groups in a `ℤₚ`-extension is
`MvZpExtension.multiplicity_classNumber_Kn_eq₁` (`Iwasawalib/NumberTheory/ZpExtension/ClassGroup.lean`).

* In the library `Iwasawalib` it is proved modulo the class field theory `sorry`s of
  `Iwasawalib/NumberTheory/NumberField/HilbertClassField/ClassFieldTheory.lean`.
  The class field theory needed is isolated in two statements
  (`NumberField.HilbertClassFieldUpperBound`, `NumberField.HilbertClassFieldExistence`), from
  which `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf` proves the theorem without `sorry`.
* The leaf library `IwasawalibCFT` (not a default target) proves those two statements with the
  `sorry`-free class field theory library
  [n-yamaguchi-0729/ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory)
  (pinned at commit `2e6280f9`) and states
  `MvZpExtension.multiplicity_classNumber_Kn_eq₁_unconditional`, with exactly the same statement
  and axioms `propext`, `Classical.choice`, `Quot.sound` only. Build it with
  `lake build IwasawalibCFT` (the external library adds roughly half an hour of compilation).
