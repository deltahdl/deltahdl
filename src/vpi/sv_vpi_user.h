// IEEE 1800-2023 Annex M — sv_vpi_user.h
// SystemVerilog-specific VPI extensions (normative).
//
// All constant names, type names, and function prototypes are MANDATED
// by the IEEE 1800-2023 standard.

#ifndef SV_VPI_USER_H
#define SV_VPI_USER_H

#include "simulation/vpi.h"

#ifdef __cplusplus
extern "C" {
#endif

// PLI type aliases used by IEEE-standard prototypes.
using PLI_INT32 = int32_t;
using PLI_BYTE8 = char;

// =============================================================================
// SV-specific object types (600-749)
// =============================================================================

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

// Variable types
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

// Typespec types
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

// Assertion types
#define vpiAssert 686
#define vpiAssume 687
#define vpiCover 688
#define vpiRestrict 901
#define vpiPropertyDecl 655
#define vpiSequenceDecl 661
#define vpiImmediateAssert 665
#define vpiImmediateAssume 666
#define vpiImmediateCover 667

// Constraint types
#define vpiConstraint 653
#define vpiConstraintOrdering 654

// Statement types
#define vpiDoWhile 670
#define vpiOrderedWait 671
#define vpiForeachStmt 675

// Net types
#define vpiEnumNet 680
#define vpiIntegerNet 681
#define vpiTimeNet 682
#define vpiStructNet 683
#define vpiPackedArrayNet 693

// =============================================================================
// Traversal method constants
// =============================================================================

#define vpiActual 700
#define vpiTypedefAlias 701
#define vpiBaseTypespec 703
#define vpiElemTypespec 704
#define vpiProperty 718

// 1-to-many
#define vpiTypedef 725
#define vpiImport 726
#define vpiDerivedClasses 727
#define vpiMethods 730
#define vpiAssertion 744

// =============================================================================
// Generic object properties
// =============================================================================

#define vpiTop 600
#define vpiUnit 602

// Join type
#define vpiJoinType 601
#define vpiJoin 0
#define vpiJoinNone 1
#define vpiJoinAny 2

// Access type
#define vpiAccessType 606
#define vpiForkJoinAcc 1
#define vpiExternAcc 2
#define vpiDPIExportAcc 3
#define vpiDPIImportAcc 4

// Array type
#define vpiArrayType 603
#define vpiStaticArray 1
#define vpiDynamicArray 2
#define vpiAssocArray 3
#define vpiQueueArray 4

// Rand type
#define vpiRandType 610
#define vpiNotRand 1
#define vpiRand 2
#define vpiRandC 3

// Visibility
#define vpiVisibility 620
#define vpiPublicVis 1
#define vpiProtectedVis 2
#define vpiLocalVis 3

// Always type
#define vpiAlwaysType 624
#define vpiAlwaysComb 2
#define vpiAlwaysFF 3
#define vpiAlwaysLatch 4

// DPI properties
#define vpiDPIPure 665
#define vpiDPIContext 666
#define vpiDPICStr 667
#define vpiDPI 1
#define vpiDPIC 2
#define vpiDPICIdentifier 668

// =============================================================================
// SV-specific operator constants
// =============================================================================

#define vpiImplyOp 50
#define vpiNonOverlapImplyOp 51
#define vpiOverlapImplyOp 52
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

// Temporal operators
#define vpiNexttimeOp 89
#define vpiAlwaysOp 90
#define vpiEventuallyOp 91
#define vpiUntilOp 92
#define vpiUntilWithOp 93

// =============================================================================
// Callback reason constants
// =============================================================================

// Thread/frame callbacks
#define cbStartOfThread 600
#define cbEndOfThread 601
#define cbEnterThread 602
#define cbStartOfFrame 603
#define cbEndOfFrame 604
#define cbSizeChange 605

// Object lifecycle
#define cbCreateObj 700
#define cbReclaimObj 701
#define cbEndOfObject 702

// Assertion callbacks (§39)
#define cbAssertionStart 606
#define cbAssertionSuccess 607
#define cbAssertionFailure 608
#define cbAssertionStepSuccess 609
#define cbAssertionStepFailure 610
#define cbAssertionDisable 611
#define cbAssertionEnable 612
#define cbAssertionReset 613
#define cbAssertionKill 614

// Assertion system callbacks
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
#define cbAssertionLock 661
#define cbAssertionUnlock 662

// =============================================================================
// Coverage VPI constants (750-779)
// =============================================================================

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

// =============================================================================
// Assertion control constants
// =============================================================================

#define vpiAssertionLock 645
#define vpiAssertionUnlock 646
#define vpiAssertionDisable 620
#define vpiAssertionEnable 621
#define vpiAssertionReset 622
#define vpiAssertionKill 623
#define vpiAssertionEnableStep 624
#define vpiAssertionDisableStep 625
#define vpiAssertionClockSteps 626

// System-level assertion control
#define vpiAssertionSysLock 627
#define vpiAssertionSysUnlock 628
#define vpiAssertionSysOn 629
#define vpiAssertionSysOff 630
#define vpiAssertionSysKill 631
#define vpiAssertionSysEnd 632
#define vpiAssertionSysReset 633

// =============================================================================
// Assertion API structures (§39)
// =============================================================================

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

// =============================================================================
// Assertion callback function typedef and registration
// =============================================================================

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

#endif  // SV_VPI_USER_H
