

#ifndef SV_VPI_USER_H
#define SV_VPI_USER_H

#include "simulator/vpi.h"

#ifdef __cplusplus
extern "C" {
#endif

using PLI_INT32 = int32_t;
using PLI_BYTE8 = char;

#define vpiPackage 600
#define vpiInterface 601
#define vpiProgram 602
#define vpiInterfaceArray 603
#define vpiProgramArray 604
#define vpiTypespec 605
#define vpiModport 606
#define vpiInterfaceTfDecl 607
#define vpiRefObj 608
#define vpiTypeParameter 609

#define vpiLongIntVar 610
#define vpiShortIntVar 611
#define vpiIntVar 612
#define vpiShortRealVar 613
#define vpiByteVar 614
#define vpiClassVar 615
#define vpiStringVar 616
#define vpiEnumVar 617
#define vpiStructVar 618
#define vpiUnionVar 619
#define vpiBitVar 620
#define vpiClassObj 621
#define vpiChandleVar 622
#define vpiPackedArrayVar 623
#define vpiVirtualInterfaceVar 728

#define vpiLongIntTypespec 625
#define vpiShortIntTypespec 626
#define vpiIntTypespec 627
#define vpiShortRealTypespec 628
#define vpiByteTypespec 629
#define vpiClassTypespec 630
#define vpiStringTypespec 631
#define vpiEnumTypespec 632
#define vpiStructTypespec 633
#define vpiUnionTypespec 634
#define vpiBitTypespec 635
#define vpiLogicTypespec 636
#define vpiPackedArrayTypespec 637
#define vpiInterfaceTypespec 906

#define vpiAssert 686
#define vpiAssume 687
#define vpiCover 688
#define vpiRestrict 901
#define vpiPropertyDecl 655
#define vpiSequenceDecl 661
#define vpiImmediateAssert 665
#define vpiImmediateAssume 666
#define vpiImmediateCover 667

#define vpiConstraint 653
#define vpiConstraintOrdering 654

#define vpiDoWhile 670
#define vpiOrderedWait 671
#define vpiForeachStmt 675

#define vpiEnumNet 680
#define vpiIntegerNet 681
#define vpiTimeNet 682
#define vpiStructNet 683
#define vpiPackedArrayNet 693

#define vpiActual 700
#define vpiTypedefAlias 701
#define vpiBaseTypespec 703
#define vpiElemTypespec 704
#define vpiProperty 718

#define vpiTypedef 725
#define vpiImport 726
#define vpiDerivedClasses 727
#define vpiMethods 730

/* §37.32 class typespec relations/properties. 732-734 are free selector numbers
 * in this module (730 vpiMethods and 744 vpiAssertion bracket the gap).
 *   vpiClassType  - the class type of a class typespec
 *   vpiClassDefn  - the defining class (NULL for built-in classes)
 *   vpiExtends    - the base class typespec a typespec derives from */
#define vpiClassType 732
#define vpiClassDefn 733
#define vpiExtends 734

/* §37.10 instance relations. 735 and 736 are free selector numbers in this
 * module (734 vpiExtends and 744 vpiAssertion bracket the gap).
 *   vpiInstance    - the immediate instance (package/module/interface/program)
 *                    an object is instantiated in
 *   vpiNetTypedef  - iteration over the user-defined nettypes an instance
 *                    explicitly declares */
#define vpiInstance 735
#define vpiNetTypedef 736

/* §37.49 assertion model. The diagram introduces the clocking-block relation an
 * assertion traverses, two instance object kinds the assertion class groups
 * that had no constant yet, and the source-span location properties an
 * assertion exposes. 737-743 are the free selector numbers between
 * vpiNetTypedef (736) and vpiAssertion (744). vpiClockingBlock - the clocking
 * block governing a concurrent assertion vpiSequenceInst  - a sequence instance
 * grouped under the assertion class vpiPropertyInst  - a property instance
 * grouped under the assertion class
 *   vpiStartLine/vpiColumn/vpiEndLine/vpiEndColumn - the source span an
 * assertion occupies (its file component is read through vpiFile) */
#define vpiClockingBlock 737
#define vpiSequenceInst 738
#define vpiPropertyInst 739
#define vpiStartLine 740
#define vpiColumn 741
#define vpiEndLine 742
#define vpiEndColumn 743

#define vpiAssertion 744

/* §37.54 sequence expression. The diagram introduces a member object kind and a
 * traversal that had no constant yet. 745 and 746 are free selector numbers in
 * this module, between vpiAssertion (744) and vpiCoverageStart (750).
 *   vpiDistribution - a weighted distribution grouped under the sequence-expr
 *                     class alongside operations, sequence instances and bare
 *                     expressions
 *   vpiMatchItem    - the assignment/tf-call match items a bare boolean
 *                     expression carries within a sequence */
#define vpiDistribution 745
#define vpiMatchItem 746

/* §37.51 property declaration. The diagram introduces the property-formal
 * declaration object kind and the disable-condition relation a property
 * instance traverses. 778 and 779 are free selector numbers above vpiMatchItem
 * (746) and below the coverage block (vpiCoverageStart 750). vpiPropFormalDecl
 * - a formal of a property declaration; the kind the vpiPropFormalDecl
 * iteration yields in declaration order vpiDisableCondition - the
 * disable-condition relation, shared with §37.52's property specification */
#define vpiPropFormalDecl 778
#define vpiDisableCondition 779

/* §37.52 property specification. The diagram introduces the property-spec and
 * property-expr kinds, the clocked/case property member kinds and the case
 * property item kind, plus the clocking-event and property-expr relations and
 * the operator-strength property. 780-789 are free selector numbers in this
 * module. vpiPropertySpec           - a property specification vpiPropertyExpr
 * - the property-expr class selector / relation vpiMulticlockSequenceExpr - a
 * multiclock sequence expression member vpiClockedProperty        - a clocked
 * property member vpiCaseProperty           - a case property member
 *   vpiCasePropertyItem       - a case property item
 *   vpiClockingEvent          - the clocking-event relation
 *   vpiOpStrong               - the Boolean operator-strength property */
#define vpiPropertySpec 780
#define vpiPropertyExpr 781
#define vpiMulticlockSequenceExpr 782
#define vpiClockedProperty 783
#define vpiCaseProperty 784
#define vpiCasePropertyItem 785
#define vpiClockingEvent 786
#define vpiOpStrong 787

/* §37.50 concurrent assertion. The diagram introduces two Boolean properties a
 * concurrent assertion exposes that had no constant yet. 788 and 789 are the
 * remaining free selector numbers in the 780-789 block.
 *   vpiIsCoverSequence  - TRUE when a cover covers a sequence (rather than a
 *                         property)
 *   vpiIsClockInferred  - TRUE when the assertion's clocking event was inferred
 *                         from context rather than written explicitly */
#define vpiIsCoverSequence 788
#define vpiIsClockInferred 789

/* §37.56 multiclock sequence expression. The diagram introduces the clocked-seq
 * object kind a multiclock sequence expression is built from. The arrow into it
 * carries no tag, so the access type is the enclosure name with "vpi"
 * prepended. 790 is the first free selector number above the §37.50/§37.52
 * block (780-789). vpiClockedSeq - a single-clock sequence (a sequence
 * expression paired with a clocking event) grouped under a multiclock sequence
 *                   expression */
#define vpiClockedSeq 790

/* §37.53 sequence declaration. The diagram introduces the
 * seq-formal-declaration object kind a sequence declaration is built from - the
 * sequence analog of §37.51's property formal. 791 is the first free selector
 * number above vpiClockedSeq (790). vpiSeqFormalDecl - a formal of a sequence
 * declaration; the kind the vpiSeqFormalDecl iteration yields in declaration
 * order */
#define vpiSeqFormalDecl 791

#define vpiTop 600
#define vpiUnit 602

#define vpiJoinType 601
#define vpiJoin 0
#define vpiJoinNone 1
#define vpiJoinAny 2

#define vpiAccessType 606
#define vpiForkJoinAcc 1
#define vpiExternAcc 2
#define vpiDPIExportAcc 3
#define vpiDPIImportAcc 4

#define vpiArrayType 603
#define vpiStaticArray 1
#define vpiDynamicArray 2
#define vpiAssocArray 3
#define vpiQueueArray 4

#define vpiRandType 610
#define vpiNotRand 1
#define vpiRand 2
#define vpiRandC 3

#define vpiVisibility 620
#define vpiPublicVis 1
#define vpiProtectedVis 2
#define vpiLocalVis 3

#define vpiAlwaysType 624
#define vpiAlwaysComb 2
#define vpiAlwaysFF 3
#define vpiAlwaysLatch 4

#define vpiDPIPure 665
#define vpiDPIContext 666
#define vpiDPICStr 667
#define vpiDPI 1
#define vpiDPIC 2
#define vpiDPICIdentifier 668

#define vpiImplyOp 50
#define vpiNonOverlapImplyOp 51
#define vpiOverlapImplyOp 52
/* §37.54 detail 2: the composite sequence "and"/"or" operators complete the set
 * of operation kinds a sequence expression's vpiOpType may report. They had no
 * constant yet; 66 and 67 are the lowest free values in the operation-type
 * (vpiOpType return-value) namespace, between vpiPreDecOp (65) and vpiWildEqOp
 * (69). They are distinct from the logical/bitwise and/or operators above. */
#define vpiCompAndOp 66
#define vpiCompOrOp 67
#define vpiUnaryCycleDelayOp 53
#define vpiCycleDelayOp 54
#define vpiIntersectOp 55
#define vpiFirstMatchOp 56
#define vpiThroughoutOp 57
#define vpiWithinOp 58
#define vpiRepeatOp 59
#define vpiConsecutiveRepeatOp 60
#define vpiGotoRepeatOp 61
#define vpiPostIncOp 62
#define vpiPreIncOp 63
#define vpiPostDecOp 64
#define vpiPreDecOp 65
#define vpiWildEqOp 69
#define vpiWildNeqOp 70
#define vpiStreamLROp 71
#define vpiStreamRLOp 72
#define vpiInsideOp 95
#define vpiTypeOp 81
#define vpiAssignmentOp 82

#define vpiNexttimeOp 89
#define vpiAlwaysOp 90
#define vpiEventuallyOp 91
#define vpiUntilOp 92
#define vpiUntilWithOp 93

/* §37.52 detail 2: the property operators a property expr's operation may
 * report through vpi_get(vpiOpType) that had no constant yet. These live in the
 * vpiOpType return-value namespace; 73-84 are free values there (between
 * vpiStreamRLOp(72), vpiTypeOp(81)/vpiAssignmentOp(82) and vpiInsideOp(95)).
 * The remaining listed property operators already have constants:
 * vpiAlwaysOp(90), vpiEventuallyOp(91), vpiNexttimeOp(89), vpiUntilOp(92),
 * vpiUntilWithOp(93), vpiCompAndOp(66), vpiCompOrOp(67), vpiNotOp(3),
 * vpiNonOverlapImplyOp(51), vpiOverlapImplyOp(52). */
#define vpiAcceptOnOp 73
#define vpiRejectOnOp 74
#define vpiSyncAcceptOnOp 75
#define vpiSyncRejectOnOp 76
#define vpiIfOp 77
#define vpiIfElseOp 78
#define vpiIffOp 79
#define vpiImpliesOp 80
#define vpiNonOverlapFollowedByOp 83
#define vpiOverlapFollowedByOp 84

#define cbStartOfThread 600
#define cbEndOfThread 601
#define cbEnterThread 602
#define cbStartOfFrame 603
#define cbEndOfFrame 604
#define cbSizeChange 605

#define cbCreateObj 700
#define cbReclaimObj 701
#define cbEndOfObject 702

#define cbAssertionStart 606
#define cbAssertionSuccess 607
#define cbAssertionFailure 608
#define cbAssertionStepSuccess 609
#define cbAssertionStepFailure 610
#define cbAssertionDisable 611
#define cbAssertionEnable 612
#define cbAssertionReset 613
#define cbAssertionKill 614

#define cbAssertionSysInitialized 615
#define cbAssertionSysOn 616
#define cbAssertionSysOff 617
#define cbAssertionSysEnd 618
#define cbAssertionSysReset 619
#define cbAssertionSysKill 631

#define cbAssertionVacuousSuccess 657
#define cbAssertionDisabledEvaluation 658
#define cbAssertionSysLock 659
#define cbAssertionSysUnlock 660

/* §39.4.1 assertion-system action callback reasons */
#define cbAssertionSysEnablePassAction 705
#define cbAssertionSysEnableFailAction 706
#define cbAssertionSysDisablePassAction 707
#define cbAssertionSysDisableFailAction 708
#define cbAssertionSysEnableNonvacuousAction 709
#define cbAssertionSysDisableVacuousAction 710
#define cbAssertionLock 661
#define cbAssertionUnlock 662

/* §39.4.2 per-assertion action callback reasons */
#define cbAssertionDisablePassAction 663
#define cbAssertionEnablePassAction 664
#define cbAssertionDisableFailAction 665
#define cbAssertionEnableFailAction 666
#define cbAssertionDisableVacuousAction 667
#define cbAssertionEnableNonvacuousAction 668

#define vpiCoverageStart 750
#define vpiCoverageStop 751
#define vpiCoverageReset 752
#define vpiCoverageCheck 753
#define vpiCoverageMerge 754
#define vpiCoverageSave 755

#define vpiFsm 758
#define vpiFsmHandle 759

#define vpiAssertCoverage 760
#define vpiFsmStateCoverage 761
#define vpiStatementCoverage 762
#define vpiToggleCoverage 763

#define vpiCovered 765
#define vpiCoverMax 766
#define vpiCoveredCount 767

#define vpiAssertAttemptCovered 770
#define vpiAssertSuccessCovered 771
#define vpiAssertFailureCovered 772
#define vpiAssertVacuousSuccessCovered 773
#define vpiAssertDisableCovered 774
#define vpiFsmStates 775
#define vpiFsmStateExpression 776
#define vpiAssertKillCovered 777

#define vpiAssertionLock 645
#define vpiAssertionUnlock 646
#define vpiAssertionDisable 620
#define vpiAssertionEnable 621
#define vpiAssertionReset 622
#define vpiAssertionKill 623
#define vpiAssertionEnableStep 624
#define vpiAssertionDisableStep 625
#define vpiAssertionClockSteps 626

#define vpiAssertionSysLock 627
#define vpiAssertionSysUnlock 628
#define vpiAssertionSysOn 629
#define vpiAssertionSysOff 630
#define vpiAssertionSysKill 631
#define vpiAssertionSysEnd 632
#define vpiAssertionSysReset 633

/* §39.5.2 per-assertion action-control constants */
#define vpiAssertionDisablePassAction 647
#define vpiAssertionEnablePassAction 648
#define vpiAssertionDisableFailAction 649
#define vpiAssertionEnableFailAction 650
#define vpiAssertionDisableVacuousAction 651
#define vpiAssertionEnableNonvacuousAction 652

/* §39.5.1 assertion-system action-control constants */
#define vpiAssertionSysDisablePassAction 653
#define vpiAssertionSysEnablePassAction 654
#define vpiAssertionSysDisableFailAction 655
#define vpiAssertionSysEnableFailAction 656
#define vpiAssertionSysDisableVacuousAction 657
#define vpiAssertionSysEnableNonvacuousAction 658

/* Annex M source-listing completion. The constants below are entries of the
 * sv_vpi_user.h listing that no other VPI subclause had yet introduced into
 * this header. Annex M is the defining home of these numeric values, so they
 * are provided here with the values the listing assigns. Symbols already
 * supplied by another subclause (possibly with that subclause's own value) are
 * left to their owner and are not repeated. */

/* Variable object types aliased onto their IEEE 1364 register counterparts. */
#define vpiVarBit vpiRegBit
#define vpiLogicVar vpiReg
#define vpiArrayVar vpiRegArray

/* Typespec object types. */
#define vpiChandleTypespec 632
#define vpiEnumConst 634
#define vpiIntegerTypespec 635
#define vpiTimeTypespec 636
#define vpiRealTypespec 637
#define vpiArrayTypespec 642
#define vpiVoidTypespec 643
#define vpiTypespecMember 644
#define vpiSequenceTypespec 696
#define vpiPropertyTypespec 697
#define vpiEventTypespec 698

/* Clocking, statement, method-call, property and pattern object types. */
#define vpiClockingIODecl 651
#define vpiDistItem 645
#define vpiAliasStmt 646
#define vpiThread 647
#define vpiMethodFuncCall 648
#define vpiMethodTaskCall 649
#define vpiClockedProp 902
#define vpiReturn 666
#define vpiAnyPattern 667
#define vpiTaggedPattern 668
#define vpiStructPattern 669
#define vpiWaitFork 672
#define vpiDisableFork 673
#define vpiExpectStmt 674
#define vpiReturnStmt 691
#define vpiFinal 676

/* Net object types; the array/logic variants alias the IEEE 1364 nets. */
#define vpiArrayNet vpiNetArray
#define vpiLogicNet vpiNet
#define vpiUnionNet 525
#define vpiShortRealNet 526
#define vpiRealNet 527
#define vpiByteNet 528
#define vpiShortIntNet 529
#define vpiIntNet 530
#define vpiLongIntNet 531
#define vpiBitNet 532
#define vpiInterconnectNet 533
#define vpiInterconnectArray 534
#define vpiBreak 684
#define vpiContinue 685
#define vpiNettypeDecl 523

/* Constraint and let-construct object types. */
#define vpiConstraintExpr 747
#define vpiElseConst 748
#define vpiImplication 749
#define vpiConstrIf 738
#define vpiConstrIfElse 739
#define vpiConstrForEach 736
#define vpiSoftDisable 733
#define vpiLetDecl 903
#define vpiLetExpr 904

/* One-to-one traversal relations. */
#define vpiIndexTypespec 702
#define vpiNetTypedefAlias 705
#define vpiInputSkew 706
#define vpiOutputSkew 707
#define vpiGlobalClocking 708
#define vpiDefaultClocking 709
#define vpiDefaultDisableIff 710
#define vpiOrigin 713
#define vpiPrefix 714
#define vpiWith 715
#define vpiValueRange 720
#define vpiPattern 721
#define vpiWeight 722
#define vpiConstraintItem 746

/* One-to-many traversal relations; vpiInterfaceDecl is a deprecated spelling of
 * the virtual-interface variable kind. */
#define vpiInterfaceDecl vpiVirtualInterfaceVar
#define vpiSolveBefore 731
#define vpiSolveAfter 732
#define vpiWaitingProcesses 734
#define vpiMessages 735
#define vpiLoopVars 737
#define vpiConcurrentAssertion 740
#define vpiConcurrentAssertions vpiConcurrentAssertion
#define vpiMember 742
#define vpiElement 743

/* Generic object properties and their enumerated return values. */
#define vpiArrayMember 607
#define vpiIsRandomized 608
#define vpiLocalVarDecls 609
#define vpiPortType 611
#define vpiInterfacePort 1
#define vpiModportPort 2
#define vpiConstantVariable 612
#define vpiStructUnionMember 615

/* Return values for the vpiConstType property. */
#define vpiOneStepConst 9
#define vpiUnboundedConst 10
#define vpiNullConst 11

/* Distribution kind for constraints. */
#define vpiDistType 625
#define vpiEqualDist 1
#define vpiDivDist 2

#define vpiPacked 630
#define vpiTagged 632
/* Return value for the vpiDirection property denoting a ref port. */
#define vpiRef 6
#define vpiVirtual 635
#define vpiHasActual 636
#define vpiIsConstraintEnabled 638
#define vpiSoft 639

/* Class kind property and its return values. */
#define vpiMailboxClass 1
#define vpiSemaphoreClass 2
#define vpiUserDefinedClass 3
#define vpiProcessClass 4
#define vpiMethod 645
#define vpiIsDeferred 657
#define vpiIsFinal 670

/* Qualifier property carrying an OR of the qualifier bit flags. */
#define vpiQualifier 650
#define vpiNoQualifier 0
#define vpiUniqueQualifier 1
#define vpiPriorityQualifier 2
#define vpiTaggedQualifier 4
#define vpiRandQualifier 8
#define vpiInsideQualifier 16

/* Clocking-block skew edge properties and the generic object property. */
#define vpiInputEdge 651
#define vpiOutputEdge 652
#define vpiGeneric 653

/* Compatibility-mode property and its supported language-version values. */
#define vpiCompatibilityMode 654
#define vpiMode1364v1995 1
#define vpiMode1364v2001 2
#define vpiMode1364v2005 3
#define vpiMode1800v2005 4
#define vpiMode1800v2009 5

#define vpiPackedArrayMember 655
#define vpiObjId 660
#define vpiIsModPort 669

/* Sequence/property and assignment-pattern operation kinds (vpiOpType return
 * values). These occupy operation-type values distinct from the existing
 * operator constants in this header. */
#define vpiMatchOp 66
#define vpiCastOp 67
#define vpiMatchedOp 73
#define vpiTriggeredOp 74
#define vpiAssignmentPatternOp 75
#define vpiMultiAssignmentPatternOp 76

/* Function return-type value and the deprecated validity-unknown value. */
#define vpiOtherFunc 6
#define vpiValidUnknown 2

/* Coverage status property; vpiCoveredMax is the spelling retained alongside
 * the backward-compatible vpiCoverMax. */
#define vpiCoveredMax 766

typedef struct t_vpi_assertion_step_info {
  PLI_INT32 matched_expression_count;
  vpiHandle* matched_exprs;
  PLI_INT32 state_from;
  PLI_INT32 state_to;
} s_vpi_assertion_step_info, *p_vpi_assertion_step_info;

typedef struct t_vpi_attempt_info {
  union {
    vpiHandle fail_expr;
    p_vpi_assertion_step_info step;
  } detail;
  s_vpi_time attempt_start_time;
} s_vpi_attempt_info, *p_vpi_attempt_info;

typedef PLI_INT32 (*vpi_assertion_callback_func)(PLI_INT32 reason,
                                                 s_vpi_time* cb_time,
                                                 vpiHandle assertion,
                                                 p_vpi_attempt_info info,
                                                 PLI_BYTE8* user_data);

vpiHandle vpi_register_assertion_cb(vpiHandle assertion, PLI_INT32 reason,
                                    vpi_assertion_callback_func cb_rtn,
                                    PLI_BYTE8* user_data);

#ifdef __cplusplus
}
#endif

#endif
