module
public import Iwasawalib.GroupCohomology.UnramifiedIdele
public import Iwasawalib.NumberTheory.CFT.FirstInequality
public import Iwasawalib.NumberTheory.CFT.IdeleClassHerbrand
public import Iwasawalib.NumberTheory.CFT.SecondInequality
public import Iwasawalib.NumberTheory.CFT.SIdeleHerbrand
public import Iwasawalib.NumberTheory.CFT.BrauerHassePrinciple
public import Iwasawalib.NumberTheory.ZpExtension.ClassGroup
@[expose] public section
-- FIRING CONTROL: a known-`sorry` declaration must show `sorryAx`.
-- If this line ever prints an axiom list WITHOUT `sorryAx`, the gate below is dead.
#print axioms MvZpExtension.multiplicity_classNumber_Kn_eq₁

-- ===== predecessor's declarations (S-unit lattice, S-unit Herbrand, idele class Herbrand) =====
#print axioms NumberField.finrank_sUnitLattice
#print axioms NumberField.sUnitBasis
#print axioms NumberField.span_sUnitBasisVec_int
#print axioms NumberField.finite_ker_sLogHyp
#print axioms NumberField.sUnitQuotEquivLattice
#print axioms NumberField.moduleFinite_sUnitQuot
#print axioms NumberField.moduleFree_sUnitQuot
#print axioms NumberField.finrank_sUnitQuot
#print axioms NumberField.span_coe_sUnitBasis_eq_sUnitLattice
#print axioms NumberField.discreteTopology_sUnitLattice
#print axioms NumberField.isZLattice_sUnitLattice
#print axioms NumberField.intBasis
#print axioms NumberField.intLattice_intBasis_eq_intHyper
#print axioms NumberField.sHyperplaneDistribMulAction
#print axioms NumberField.herbrand_sUnitLattice_eq_intHyper
#print axioms NumberField.herbrand_sUnitGroup_eq_lattice
#print axioms NumberField.herbrand_kerTotal_eq_intLattice
#print axioms NumberField.herbrand_sUnitGroup
#print axioms NumberField.herbrand_sUnitGroup_mul_card
#print axioms NumberField.galIdeleAut_principalEmbedding
#print axioms NumberField.sUnitToSIdele
#print axioms NumberField.sIdeleToIdeleClass
#print axioms NumberField.isShortExact_sUnit_sIdele
#print axioms NumberField.herbrand_sIdele_eq_mul
#print axioms NumberField.herbrand_ideleClassGroup_of_herbrand_sIdele

-- ===== RestrictedProductSplit =====
#print axioms RestrictedProduct.outsideSubgroup
#print axioms RestrictedProduct.mem_outsideSubgroup
#print axioms RestrictedProduct.outsideSplit
#print axioms RestrictedProduct.outsideMergeFun
#print axioms RestrictedProduct.outsideMergeFun_mem
#print axioms RestrictedProduct.outsideMerge
#print axioms RestrictedProduct.coe_outsideMerge
#print axioms RestrictedProduct.outsideSubgroupEquiv
#print axioms RestrictedProduct.outsideSubgroupEquiv_apply_fst
#print axioms RestrictedProduct.outsideSubgroupEquiv_apply_snd

-- ===== SecondInequality =====
#print axioms CyclicTate.commGroupOfGen
#print axioms CyclicTate.herbrand_le_card_tateH0
#print axioms CyclicTate.le_card_tateH0_of_le_herbrand
#print axioms CyclicTate.herbrand_eq_card_tateH0_of_subsingleton
#print axioms CyclicTate.le_card_groupCohomology_two_of_le_herbrand
#print axioms NumberField.finite_tateH1_ideleClassGroup
#print axioms NumberField.card_tateH0_ideleClassGroup_ge
#print axioms NumberField.card_groupCohomology_two_ideleClassGroup_ge
#print axioms NumberField.card_tateH0_ideleClassGroup_eq_of_subsingleton

-- ===== SIdeleSemilocal =====
#print axioms NumberField.coe_finiteIdeleEquivSemilocal
#print axioms NumberField.coe_inv_finiteIdeleEquivSemilocal
#print axioms NumberField.mem_localProductIntegerUnits
#print axioms NumberField.finiteIdeleEquivSemilocal_mem_outsideSubgroup
#print axioms NumberField.finiteIdeleEquivSemilocal_smul_apply
#print axioms NumberField.localProductIntegerUnitsMulDistribMulAction
#print axioms NumberField.coe_smul_localProductIntegerUnits
#print axioms NumberField.finiteSIdeleMulDistribMulAction
#print axioms NumberField.coe_smul_finiteSIdele
#print axioms NumberField.SIdeleSemilocal
#print axioms NumberField.outsideOfSIdele
#print axioms NumberField.sIdeleOfOutside
#print axioms NumberField.finiteSIdeleEquivOutside
#print axioms NumberField.finiteSIdeleSemilocalEquiv
#print axioms NumberField.finiteSIdeleSemilocalEquiv_fst
#print axioms NumberField.finiteSIdeleSemilocalEquiv_snd
#print axioms NumberField.finiteSIdeleSemilocalEquiv_smul

-- ===== SIdeleHerbrand =====
#print axioms CyclicTate.additiveProdEquiv
#print axioms CyclicTate.additivePiEquiv
#print axioms CyclicTate.herbrand_eq_of_mulEquiv
#print axioms CyclicTate.finite_tateH0_of_mulEquiv
#print axioms CyclicTate.finite_tateH1_of_mulEquiv
#print axioms CyclicTate.herbrand_mulProd
#print axioms CyclicTate.finite_tateH0_mulProd
#print axioms CyclicTate.finite_tateH1_mulProd
#print axioms CyclicTate.herbrand_mulPi
#print axioms CyclicTate.finite_tateH0_mulPi
#print axioms CyclicTate.finite_tateH1_mulPi
#print axioms CyclicTate.subsingleton_tateH0_mulPi
#print axioms CyclicTate.subsingleton_tateH1_mulPi
#print axioms NumberField.herbrand_finiteSIdele
#print axioms NumberField.herbrand_finiteSIdele_of_subsingleton
#print axioms NumberField.sIdeleProdEquiv
#print axioms NumberField.sIdeleProdEquiv_smul
#print axioms NumberField.herbrand_infiniteIdele
#print axioms NumberField.herbrand_sIdele
#print axioms NumberField.herbrand_localProductUnits
#print axioms NumberField.herbrand_infiniteLocalProductUnits
#print axioms NumberField.herbrand_sIdele_eq_prod_local


-- ===== PlaceFibreStabilizer (the bookkeeping join) =====
#print axioms NumberField.placesOverMulAction
#print axioms NumberField.coe_smul_placesOver
#print axioms NumberField.stabilizer_placesOver_eq
#print axioms NumberField.coe_finitePlaceFibre_mem_placesOver
#print axioms NumberField.coe_smul_finitePlaceFibre
#print axioms NumberField.stabilizer_finitePlaceFibre_eq
#print axioms NumberField.card_stabilizer_finitePlaceFibre_eq
#print axioms NumberField.placesOverToFibre
#print axioms NumberField.coe_placesOverToFibre
#print axioms NumberField.stabilizer_placesOverToFibre_eq

-- ===== TateTransport =====
#print axioms CyclicTate.normHom_eq_of_groupEquiv
#print axioms CyclicTate.subsingleton_tateH0_of_groupEquiv
#print axioms CyclicTate.subsingleton_tateH1_of_groupEquiv
#print axioms CyclicTate.rangeNorm_eq_of_groupEquiv
#print axioms CyclicTate.kerNorm_eq_of_groupEquiv
#print axioms CyclicTate.kerSub_eq_of_groupEquiv
#print axioms CyclicTate.rangeSub_eq_of_groupEquiv
#print axioms CyclicTate.subsingleton_tateH0_of_moduleEquiv
#print axioms CyclicTate.subsingleton_tateH1_of_moduleEquiv
#print axioms CyclicTate.normHom_eq_id_of_subsingleton_group
#print axioms CyclicTate.subsingleton_tateH0_of_subsingleton_group
#print axioms CyclicTate.subsingleton_tateH1_of_subsingleton_group
#print axioms CyclicTate.finite_tateH0_of_subsingleton_group
#print axioms CyclicTate.finite_tateH1_of_subsingleton_group
#print axioms CyclicTate.herbrand_eq_one_of_subsingleton_group
#print axioms EquivariantFamily.subsingleton_tateH0_piUnits
#print axioms EquivariantFamily.subsingleton_tateH1_piUnits
#print axioms EquivariantFamily.finite_tateH0_piUnits
#print axioms EquivariantFamily.finite_tateH1_piUnits

-- ===== SemilocalIntegerUnits =====
#print axioms NumberField.valuation_of_push_smul
#print axioms NumberField.pushAdicCompletion
#print axioms NumberField.valued_pushAdicCompletion
#print axioms NumberField.valued_pushAdicCompletion_symm
#print axioms NumberField.pushAdicIntegers
#print axioms NumberField.coe_pushAdicIntegers
#print axioms NumberField.localIntegerFamily
#print axioms NumberField.localProductIntegersEquivPi
#print axioms NumberField.localProductIntegerUnitsEquivPiUnits
#print axioms NumberField.coe_localProductIntegerUnitsEquivPiUnits
#print axioms NumberField.localIntegerPiAction
#print axioms NumberField.localIntegerStabilizerAction
#print axioms NumberField.localIntegerFamily_isPiAction
#print axioms NumberField.localIntegerFamily_isStabilizerAction
#print axioms NumberField.localProductIntegerUnitsEquivPiUnits_smul
#print axioms NumberField.adicIntegersDecompositionAction
#print axioms NumberField.subsingleton_tateH0_localProductIntegerUnits
#print axioms NumberField.subsingleton_tateH1_localProductIntegerUnits

-- ===== SemilocalFieldUnits =====
#print axioms NumberField.finite_tateH0_adicCompletion_units
#print axioms NumberField.finite_tateH1_adicCompletion_units
#print axioms NumberField.localFieldFamily
#print axioms NumberField.localFieldStabilizerAction
#print axioms NumberField.localFieldFamily_isPiAction
#print axioms NumberField.localFieldFamily_isStabilizerAction
#print axioms NumberField.finite_tateH0_localProductUnits
#print axioms NumberField.finite_tateH1_localProductUnits
#print axioms NumberField.InfiniteAdeleRing.subsingleton_tateH0_infiniteLocalProductUnits
#print axioms NumberField.InfiniteAdeleRing.subsingleton_tateH1_infiniteLocalProductUnits

-- ===== IdeleClassHerbrandValue =====
#print axioms NumberField.finite_tateH0_sIdele
#print axioms NumberField.finite_tateH1_sIdele
#print axioms NumberField.herbrand_ideleClassGroup_eq_card_of_unramified

-- ===== FirstInequality =====
#print axioms CyclicTate.card_tateH0_eq_mul_of_herbrand_eq_natCast
#print axioms CyclicTate.card_tateH1_eq_one_iff_of_herbrand_eq_natCast
#print axioms CyclicTate.card_tateH1_eq_one_iff_card_tateH0_le
#print axioms CyclicTate.subsingleton_tateH1_iff_of_herbrand_eq_natCast
#print axioms CyclicTate.dvd_card_tateH0_of_herbrand_eq_natCast
#print axioms NumberField.card_tateH0_ideleClassGroup_eq_mul
#print axioms NumberField.card_tateH0_ideleClassGroup_ge_of_unramified
#print axioms NumberField.card_dvd_card_tateH0_ideleClassGroup
#print axioms NumberField.subsingleton_tateH1_ideleClassGroup_iff
#print axioms NumberField.subsingleton_tateH1_ideleClassGroup_iff_card_eq

-- ===== new packaged results =====
#print axioms NumberField.localCFTIntegersStabilizerAction
#print axioms NumberField.finite_tateH0_ideleClassGroup
#print axioms NumberField.herbrand_ideleClassGroup_eq_card_of_unramified_everywhere
#print axioms NumberField.finite_tateH0_ideleClassGroup_of_unramified_everywhere
#print axioms NumberField.finite_tateH1_ideleClassGroup_of_unramified_everywhere
#print axioms NumberField.card_tateH0_ideleClassGroup_eq_mul_everywhere
#print axioms NumberField.card_tateH0_ideleClassGroup_ge_everywhere
#print axioms NumberField.subsingleton_tateH1_ideleClassGroup_iff_everywhere
#print axioms NumberField.card_groupCohomology_ideleClassGroup_eq_mul
#print axioms NumberField.subsingleton_groupCohomology_one_ideleClassGroup_iff

-- ===== every declaration named in a new docstring must exist =====
#check @CyclicTate.additivePiEquiv
#check @CyclicTate.additiveProdEquiv
#check @CyclicTate.commGroupOfGen
#check @CyclicTate.herbrand_eq_card_groupCohomology
#check @CyclicTate.herbrand_eq_of_mulEquiv
#check @CyclicTate.herbrand_le_card_tateH0
#check @CyclicTate.herbrand_mulPi
#check @CyclicTate.herbrand_mulProd
#check @CyclicTate.herbrand_pi
#check @CyclicTate.herbrand_piUnits
#check @CyclicTate.rep
#check @CyclicTate.subsingleton_tateH0_mulPi
#check @CyclicTate.subsingleton_tateH1_mulPi
#check @NumberField.InfiniteAdeleRing.infiniteFamily
#check @NumberField.InfiniteAdeleRing.infiniteLocalUnitsShapiro
#check @NumberField.SIdeleSemilocal
#check @NumberField.card_groupCohomology_two_ideleClassGroup_ge
#check @NumberField.card_tateH0_ideleClassGroup_eq_of_subsingleton
#check @NumberField.card_tateH0_ideleClassGroup_ge
#check @NumberField.finiteIdeleEquivSemilocal
#check @NumberField.finiteIdeleEquivSemilocal_mem_outsideSubgroup
#check @NumberField.finiteIdeleEquivSemilocal_smul
#check @NumberField.finiteSIdeleEquivOutside
#check @NumberField.finiteSIdeleSemilocalEquiv
#check @NumberField.finiteSIdeleSemilocalEquiv_smul
#check @NumberField.herbrand_finiteSIdele
#check @NumberField.herbrand_finiteSIdele_of_subsingleton
#check @NumberField.herbrand_ideleClassGroup_of_herbrand_sIdele
#check @NumberField.herbrand_infiniteIdele
#check @NumberField.herbrand_infiniteLocalProductUnits
#check @NumberField.herbrand_localProductUnits
#check @NumberField.herbrand_sIdele
#check @NumberField.herbrand_sIdele_eq_prod_local
#check @NumberField.infiniteIdeleEquivPi
#check @NumberField.isShortExact_sUnit_sIdele
#check @NumberField.localProductUnitsShapiro
#check @NumberField.module_finite_sUnit
#check @NumberField.outsideOfSIdele
#check @NumberField.sIdeleOfOutside
#check @NumberField.sIdeleProdEquiv
#check @NumberField.semilocalFiniteEquiv
#check @NumberField.smul_mem_localProductIntegerUnits
#check @NumberField.smul_mem_localProductIntegers
#check @RestrictedProduct.coe_outsideMerge
#check @RestrictedProduct.mem_outsideSubgroup
#check @RestrictedProduct.outsideMerge
#check @RestrictedProduct.outsideSubgroup
#check @RestrictedProduct.outsideSubgroupEquiv
#check @RestrictedProduct.outsideSubgroupEquiv_apply_fst
#check @RestrictedProduct.outsideSubgroupEquiv_apply_snd
#check @RestrictedProduct.unitsEquiv

-- ===== docstring references of this round =====
#check @CyclicTate.card_tateH0_eq_mul_of_herbrand_eq_natCast
#check @CyclicTate.card_tateH1_eq_one_iff_of_herbrand_eq_natCast
#check @CyclicTate.herbrand_eq_one_of_subsingleton_group
#check @CyclicTate.subsingleton_tateH0_mulPi
#check @CyclicTate.subsingleton_tateH0_of_groupEquiv
#check @CyclicTate.subsingleton_tateH0_of_moduleEquiv
#check @CyclicTate.subsingleton_tateH0_of_subsingleton_group
#check @CyclicTate.subsingleton_tateH1_iff_of_herbrand_eq_natCast
#check @CyclicTate.subsingleton_tateH1_of_groupEquiv
#check @CyclicTate.subsingleton_tateH1_of_moduleEquiv
#check @CyclicTate.subsingleton_tateH1_of_subsingleton_group
#check @EquivariantFamily.subsingleton_tateH0_piUnits
#check @EquivariantFamily.subsingleton_tateH1_piUnits
#check @LocalCFT.integers
#check @LocalCFT.isShortExact_valHom
#check @NumberField.InfiniteAdeleRing.subsingleton_tateH0_infiniteLocalProductUnits
#check @NumberField.InfiniteAdeleRing.subsingleton_tateH1_infiniteLocalProductUnits
#check @NumberField.card_groupCohomology_two_ideleClassGroup_ge
#check @NumberField.card_stabilizer_finitePlaceFibre_eq
#check @NumberField.card_tateH0_ideleClassGroup_eq_mul
#check @NumberField.card_tateH0_ideleClassGroup_ge_everywhere
#check @NumberField.card_tateH0_ideleClassGroup_ge_of_unramified
#check @NumberField.coe_finitePlaceFibre_mem_placesOver
#check @NumberField.decompositionGroup
#check @NumberField.exists_galois_stable_sIdeleSubgroup_sup
#check @NumberField.finite_tateH0_adicCompletion_units
#check @NumberField.finite_tateH0_ideleClassGroup
#check @NumberField.finite_tateH0_localProductUnits
#check @NumberField.finite_tateH0_sIdele
#check @NumberField.finite_tateH1_adicCompletion_units
#check @NumberField.finite_tateH1_ideleClassGroup
#check @NumberField.finite_tateH1_localProductUnits
#check @NumberField.finite_tateH1_sIdele
#check @NumberField.herbrand_adicCompletion_units_eq_card
#check @NumberField.herbrand_ideleClassGroup_eq_card_of_unramified
#check @NumberField.herbrand_ideleClassGroup_eq_card_of_unramified_everywhere
#check @NumberField.herbrand_ideleClassGroup_of_herbrand_sIdele
#check @NumberField.herbrand_localProductUnits
#check @NumberField.herbrand_sIdele
#check @NumberField.isZero_H1_repIdele
#check @NumberField.localFieldFamily
#check @NumberField.localFieldFamily_isPiAction
#check @NumberField.localIntegerFamily
#check @NumberField.localProductIntegersEquivPi
#check @NumberField.localProductMulSemiringAction
#check @NumberField.placesOverMulAction
#check @NumberField.pushAdicCompletion
#check @NumberField.pushAdicIntegers
#check @NumberField.stabilizer_finitePlaceFibre_eq
#check @NumberField.stabilizer_placesOver_eq
#check @NumberField.subsingleton_tateH0_localProductIntegerUnits
#check @NumberField.subsingleton_tateH0_units
#check @NumberField.subsingleton_tateH1_ideleClassGroup_iff
#check @NumberField.subsingleton_tateH1_localProductIntegerUnits
#check @NumberField.under_smul_heightOneSpectrum

-- ===== BrauerHassePrinciple (this round) =====
#print axioms groupCohomology.mono_of_isZero
#print axioms groupCohomology.mono_iff_isZero
#print axioms NumberField.BrauerHassePrinciple
#print axioms NumberField.brauerHassePrinciple_iff_isZero_H1_repIdeleClass
#print axioms NumberField.isZero_H1_repIdeleClass_of_brauerHassePrinciple
#print axioms NumberField.brauerHassePrinciple_of_isZero_H1_repIdeleClass
#print axioms NumberField.brauerHassePrinciple_of_subsingleton
#print axioms NumberField.brauerHassePrinciple_fixedField_iff_isZero_H1_subgroup
#print axioms NumberField.isZero_H1_subgroup_repIdeleClass_of_brauerHassePrinciple
#print axioms NumberField.brauerHassePrinciple_iff_card_le
#print axioms NumberField.brauerHassePrinciple_iff_card_eq
#print axioms NumberField.card_groupCohomology_two_ideleClassGroup_eq_of_brauerHassePrinciple
#print axioms NumberField.subsingleton_groupCohomology_one_ideleClassGroup_of_brauerHassePrinciple

-- ===== docstring forward references of this round =====
#check @groupCohomology.isZero_of_isZero_of_mono
#check @NumberField.card_tateH0_ideleClassGroup_ge_everywhere
#check @NumberField.isZero_H1_repIdele
#check @NumberField.isZero_H1_repIdeleClass
#check @NumberField.repIdeleClass
#check @NumberField.subgroupIdeleClassIso
#check @NumberField.subsingleton_groupCohomology_one_ideleClassGroup_iff
