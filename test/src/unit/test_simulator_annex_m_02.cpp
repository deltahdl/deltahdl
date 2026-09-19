#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <type_traits>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace {

// §M.2 opens with the object types: the packages, interfaces, programs and
// modports from 600, the variable kinds from 610 with the register aliases, and
// the typespecs from 625, with vpiPackedArrayTypespec and the sequence,
// property and event typespecs above 690 and vpiInterfaceTypespec at 906.
TEST(SvVpiUserHeader, TheObjectTypesOfPackagesVariablesAndTypespecs) {
  EXPECT_EQ(vpiPackage, 600);
  EXPECT_EQ(vpiInterface, 601);
  EXPECT_EQ(vpiProgram, 602);
  EXPECT_EQ(vpiInterfaceArray, 603);
  EXPECT_EQ(vpiProgramArray, 604);
  EXPECT_EQ(vpiTypespec, 605);
  EXPECT_EQ(vpiModport, 606);
  EXPECT_EQ(vpiInterfaceTfDecl, 607);
  EXPECT_EQ(vpiRefObj, 608);
  EXPECT_EQ(vpiTypeParameter, 609);
  EXPECT_EQ(vpiVarBit, vpiRegBit);
  EXPECT_EQ(vpiLongIntVar, 610);
  EXPECT_EQ(vpiShortIntVar, 611);
  EXPECT_EQ(vpiIntVar, 612);
  EXPECT_EQ(vpiShortRealVar, 613);
  EXPECT_EQ(vpiByteVar, 614);
  EXPECT_EQ(vpiClassVar, 615);
  EXPECT_EQ(vpiStringVar, 616);
  EXPECT_EQ(vpiEnumVar, 617);
  EXPECT_EQ(vpiStructVar, 618);
  EXPECT_EQ(vpiUnionVar, 619);
  EXPECT_EQ(vpiBitVar, 620);
  EXPECT_EQ(vpiLogicVar, vpiReg);
  EXPECT_EQ(vpiArrayVar, vpiRegArray);
  EXPECT_EQ(vpiClassObj, 621);
  EXPECT_EQ(vpiChandleVar, 622);
  EXPECT_EQ(vpiPackedArrayVar, 623);
  EXPECT_EQ(vpiVirtualInterfaceVar, 728);
  EXPECT_EQ(vpiLongIntTypespec, 625);
  EXPECT_EQ(vpiShortRealTypespec, 626);
  EXPECT_EQ(vpiByteTypespec, 627);
  EXPECT_EQ(vpiShortIntTypespec, 628);
  EXPECT_EQ(vpiIntTypespec, 629);
  EXPECT_EQ(vpiClassTypespec, 630);
  EXPECT_EQ(vpiStringTypespec, 631);
  EXPECT_EQ(vpiChandleTypespec, 632);
  EXPECT_EQ(vpiEnumTypespec, 633);
  EXPECT_EQ(vpiEnumConst, 634);
  EXPECT_EQ(vpiIntegerTypespec, 635);
  EXPECT_EQ(vpiTimeTypespec, 636);
  EXPECT_EQ(vpiRealTypespec, 637);
  EXPECT_EQ(vpiStructTypespec, 638);
  EXPECT_EQ(vpiUnionTypespec, 639);
  EXPECT_EQ(vpiBitTypespec, 640);
  EXPECT_EQ(vpiLogicTypespec, 641);
  EXPECT_EQ(vpiArrayTypespec, 642);
  EXPECT_EQ(vpiVoidTypespec, 643);
  EXPECT_EQ(vpiTypespecMember, 644);
  EXPECT_EQ(vpiPackedArrayTypespec, 692);
  EXPECT_EQ(vpiSequenceTypespec, 696);
  EXPECT_EQ(vpiPropertyTypespec, 697);
  EXPECT_EQ(vpiEventTypespec, 698);
  EXPECT_EQ(vpiInterfaceTypespec, 906);
}

// §M.2 continues the object types with the clocking blocks, class definitions
// and constraints at 650, the statement and method-call kinds, the concurrent
// and immediate assertions, the property and sequence kinds, the patterns, the
// waits and disables, and the formals of sequences and properties.
TEST(SvVpiUserHeader, TheObjectTypesOfBlocksAssertionsAndStatements) {
  EXPECT_EQ(vpiClockingBlock, 650);
  EXPECT_EQ(vpiClockingIODecl, 651);
  EXPECT_EQ(vpiClassDefn, 652);
  EXPECT_EQ(vpiConstraint, 653);
  EXPECT_EQ(vpiConstraintOrdering, 654);
  EXPECT_EQ(vpiDistItem, 645);
  EXPECT_EQ(vpiAliasStmt, 646);
  EXPECT_EQ(vpiThread, 647);
  EXPECT_EQ(vpiMethodFuncCall, 648);
  EXPECT_EQ(vpiMethodTaskCall, 649);
  EXPECT_EQ(vpiAssert, 686);
  EXPECT_EQ(vpiAssume, 687);
  EXPECT_EQ(vpiCover, 688);
  EXPECT_EQ(vpiRestrict, 901);
  EXPECT_EQ(vpiDisableCondition, 689);
  EXPECT_EQ(vpiClockingEvent, 690);
  EXPECT_EQ(vpiPropertyDecl, 655);
  EXPECT_EQ(vpiPropertySpec, 656);
  EXPECT_EQ(vpiPropertyExpr, 657);
  EXPECT_EQ(vpiMulticlockSequenceExpr, 658);
  EXPECT_EQ(vpiClockedSeq, 659);
  EXPECT_EQ(vpiClockedProp, 902);
  EXPECT_EQ(vpiPropertyInst, 660);
  EXPECT_EQ(vpiSequenceDecl, 661);
  EXPECT_EQ(vpiCaseProperty, 662);
  EXPECT_EQ(vpiCasePropertyItem, 905);
  EXPECT_EQ(vpiSequenceInst, 664);
  EXPECT_EQ(vpiImmediateAssert, 665);
  EXPECT_EQ(vpiImmediateAssume, 694);
  EXPECT_EQ(vpiImmediateCover, 695);
  EXPECT_EQ(vpiReturn, 666);
  EXPECT_EQ(vpiAnyPattern, 667);
  EXPECT_EQ(vpiTaggedPattern, 668);
  EXPECT_EQ(vpiStructPattern, 669);
  EXPECT_EQ(vpiDoWhile, 670);
  EXPECT_EQ(vpiOrderedWait, 671);
  EXPECT_EQ(vpiWaitFork, 672);
  EXPECT_EQ(vpiDisableFork, 673);
  EXPECT_EQ(vpiExpectStmt, 674);
  EXPECT_EQ(vpiForeachStmt, 675);
  EXPECT_EQ(vpiReturnStmt, 691);
  EXPECT_EQ(vpiFinal, 676);
  EXPECT_EQ(vpiExtends, 677);
  EXPECT_EQ(vpiDistribution, 678);
  EXPECT_EQ(vpiSeqFormalDecl, 679);
  EXPECT_EQ(vpiPropFormalDecl, 699);
}

// §M.2 ends the object types with the nets, the array and logic nets aliasing
// the base file's, the typed nets from 525 and 680, the break and continue
// statements, the nettype declaration at 523, the constraint kinds and the let
// declaration and expression above 900.
TEST(SvVpiUserHeader, TheObjectTypesOfNetsConstraintsAndLets) {
  EXPECT_EQ(vpiArrayNet, vpiNetArray);
  EXPECT_EQ(vpiEnumNet, 680);
  EXPECT_EQ(vpiIntegerNet, 681);
  EXPECT_EQ(vpiLogicNet, vpiNet);
  EXPECT_EQ(vpiTimeNet, 682);
  EXPECT_EQ(vpiUnionNet, 525);
  EXPECT_EQ(vpiShortRealNet, 526);
  EXPECT_EQ(vpiRealNet, 527);
  EXPECT_EQ(vpiByteNet, 528);
  EXPECT_EQ(vpiShortIntNet, 529);
  EXPECT_EQ(vpiIntNet, 530);
  EXPECT_EQ(vpiLongIntNet, 531);
  EXPECT_EQ(vpiBitNet, 532);
  EXPECT_EQ(vpiInterconnectNet, 533);
  EXPECT_EQ(vpiInterconnectArray, 534);
  EXPECT_EQ(vpiStructNet, 683);
  EXPECT_EQ(vpiBreak, 684);
  EXPECT_EQ(vpiContinue, 685);
  EXPECT_EQ(vpiPackedArrayNet, 693);
  EXPECT_EQ(vpiNettypeDecl, 523);
  EXPECT_EQ(vpiConstraintExpr, 747);
  EXPECT_EQ(vpiElseConst, 748);
  EXPECT_EQ(vpiImplication, 749);
  EXPECT_EQ(vpiConstrIf, 738);
  EXPECT_EQ(vpiConstrIfElse, 739);
  EXPECT_EQ(vpiConstrForEach, 736);
  EXPECT_EQ(vpiSoftDisable, 733);
  EXPECT_EQ(vpiLetDecl, 903);
  EXPECT_EQ(vpiLetExpr, 904);
}

// §M.2 numbers the methods that traverse one-to-one relations from vpiActual at
// 700 through vpiConstraintItem at 746.
TEST(SvVpiUserHeader, TheMethodsTraversingOneToOneRelations) {
  EXPECT_EQ(vpiActual, 700);
  EXPECT_EQ(vpiTypedefAlias, 701);
  EXPECT_EQ(vpiIndexTypespec, 702);
  EXPECT_EQ(vpiBaseTypespec, 703);
  EXPECT_EQ(vpiElemTypespec, 704);
  EXPECT_EQ(vpiNetTypedefAlias, 705);
  EXPECT_EQ(vpiInputSkew, 706);
  EXPECT_EQ(vpiOutputSkew, 707);
  EXPECT_EQ(vpiGlobalClocking, 708);
  EXPECT_EQ(vpiDefaultClocking, 709);
  EXPECT_EQ(vpiDefaultDisableIff, 710);
  EXPECT_EQ(vpiOrigin, 713);
  EXPECT_EQ(vpiPrefix, 714);
  EXPECT_EQ(vpiWith, 715);
  EXPECT_EQ(vpiProperty, 718);
  EXPECT_EQ(vpiValueRange, 720);
  EXPECT_EQ(vpiPattern, 721);
  EXPECT_EQ(vpiWeight, 722);
  EXPECT_EQ(vpiConstraintItem, 746);
}

// §M.2 numbers the methods that traverse one-to-many relations from vpiTypedef
// at 725 through vpiElement at 743, vpiInterfaceDecl being a deprecated
// spelling of vpiVirtualInterfaceVar and vpiConcurrentAssertions of
// vpiConcurrentAssertion, then vpiAssertion at 744 and, traversing both kinds
// of relation, vpiInstance at 745.
TEST(SvVpiUserHeader, TheMethodsTraversingOneToManyRelations) {
  EXPECT_EQ(vpiTypedef, 725);
  EXPECT_EQ(vpiImport, 726);
  EXPECT_EQ(vpiDerivedClasses, 727);
  EXPECT_EQ(vpiInterfaceDecl, vpiVirtualInterfaceVar);
  EXPECT_EQ(vpiMethods, 730);
  EXPECT_EQ(vpiSolveBefore, 731);
  EXPECT_EQ(vpiSolveAfter, 732);
  EXPECT_EQ(vpiWaitingProcesses, 734);
  EXPECT_EQ(vpiMessages, 735);
  EXPECT_EQ(vpiLoopVars, 737);
  EXPECT_EQ(vpiConcurrentAssertion, 740);
  EXPECT_EQ(vpiConcurrentAssertions, vpiConcurrentAssertion);
  EXPECT_EQ(vpiMatchItem, 741);
  EXPECT_EQ(vpiMember, 742);
  EXPECT_EQ(vpiElement, 743);
  EXPECT_EQ(vpiAssertion, 744);
  EXPECT_EQ(vpiInstance, 745);
}

// §M.2 numbers the generic object properties from vpiTop at 600: the join,
// access, array and rand types with their return values, the port types beside
// the base file's vpiPort, and the constant-variable and struct-union-member
// Booleans.
TEST(SvVpiUserHeader,
     TheGenericObjectPropertiesOfScopesArraysAndRandomization) {
  EXPECT_EQ(vpiTop, 600);
  EXPECT_EQ(vpiUnit, 602);
  EXPECT_EQ(vpiJoinType, 603);
  EXPECT_EQ(vpiJoin, 0);
  EXPECT_EQ(vpiJoinNone, 1);
  EXPECT_EQ(vpiJoinAny, 2);
  EXPECT_EQ(vpiAccessType, 604);
  EXPECT_EQ(vpiForkJoinAcc, 1);
  EXPECT_EQ(vpiExternAcc, 2);
  EXPECT_EQ(vpiDPIExportAcc, 3);
  EXPECT_EQ(vpiDPIImportAcc, 4);
  EXPECT_EQ(vpiArrayType, 606);
  EXPECT_EQ(vpiStaticArray, 1);
  EXPECT_EQ(vpiDynamicArray, 2);
  EXPECT_EQ(vpiAssocArray, 3);
  EXPECT_EQ(vpiQueueArray, 4);
  EXPECT_EQ(vpiArrayMember, 607);
  EXPECT_EQ(vpiIsRandomized, 608);
  EXPECT_EQ(vpiLocalVarDecls, 609);
  EXPECT_EQ(vpiOpStrong, 656);
  EXPECT_EQ(vpiRandType, 610);
  EXPECT_EQ(vpiNotRand, 1);
  EXPECT_EQ(vpiRand, 2);
  EXPECT_EQ(vpiRandC, 3);
  EXPECT_EQ(vpiPortType, 611);
  EXPECT_EQ(vpiInterfacePort, 1);
  EXPECT_EQ(vpiModportPort, 2);
  EXPECT_EQ(vpiConstantVariable, 612);
  EXPECT_EQ(vpiStructUnionMember, 615);
}

// §M.2 continues the properties with the visibilities, the return values of
// vpiConstType, the always types, the distribution types, the packed, tagged,
// virtual and soft Booleans, vpiRef as a return value of vpiDirection, and the
// class types.
TEST(SvVpiUserHeader,
     TheGenericObjectPropertiesOfVisibilityConstantsAndClasses) {
  EXPECT_EQ(vpiVisibility, 620);
  EXPECT_EQ(vpiPublicVis, 1);
  EXPECT_EQ(vpiProtectedVis, 2);
  EXPECT_EQ(vpiLocalVis, 3);
  EXPECT_EQ(vpiOneStepConst, 9);
  EXPECT_EQ(vpiUnboundedConst, 10);
  EXPECT_EQ(vpiNullConst, 11);
  EXPECT_EQ(vpiAlwaysType, 624);
  EXPECT_EQ(vpiAlwaysComb, 2);
  EXPECT_EQ(vpiAlwaysFF, 3);
  EXPECT_EQ(vpiAlwaysLatch, 4);
  EXPECT_EQ(vpiDistType, 625);
  EXPECT_EQ(vpiEqualDist, 1);
  EXPECT_EQ(vpiDivDist, 2);
  EXPECT_EQ(vpiPacked, 630);
  EXPECT_EQ(vpiTagged, 632);
  EXPECT_EQ(vpiRef, 6);
  EXPECT_EQ(vpiVirtual, 635);
  EXPECT_EQ(vpiHasActual, 636);
  EXPECT_EQ(vpiIsConstraintEnabled, 638);
  EXPECT_EQ(vpiSoft, 639);
  EXPECT_EQ(vpiClassType, 640);
  EXPECT_EQ(vpiMailboxClass, 1);
  EXPECT_EQ(vpiSemaphoreClass, 2);
  EXPECT_EQ(vpiUserDefinedClass, 3);
  EXPECT_EQ(vpiProcessClass, 4);
}

// §M.2 continues the properties with the method, clock-inferred, deferred,
// final and cover-sequence Booleans, the qualifier bit flags, the skew edges,
// the generic Boolean and the compatibility modes.
TEST(SvVpiUserHeader, TheGenericObjectPropertiesOfMethodsQualifiersAndModes) {
  EXPECT_EQ(vpiMethod, 645);
  EXPECT_EQ(vpiIsClockInferred, 649);
  EXPECT_EQ(vpiIsDeferred, 657);
  EXPECT_EQ(vpiIsFinal, 670);
  EXPECT_EQ(vpiIsCoverSequence, 659);
  EXPECT_EQ(vpiQualifier, 650);
  EXPECT_EQ(vpiNoQualifier, 0);
  EXPECT_EQ(vpiUniqueQualifier, 1);
  EXPECT_EQ(vpiPriorityQualifier, 2);
  EXPECT_EQ(vpiTaggedQualifier, 4);
  EXPECT_EQ(vpiRandQualifier, 8);
  EXPECT_EQ(vpiInsideQualifier, 16);
  EXPECT_EQ(vpiInputEdge, 651);
  EXPECT_EQ(vpiOutputEdge, 652);
  EXPECT_EQ(vpiGeneric, 653);
  EXPECT_EQ(vpiCompatibilityMode, 654);
  EXPECT_EQ(vpiMode1364v1995, 1);
  EXPECT_EQ(vpiMode1364v2001, 2);
  EXPECT_EQ(vpiMode1364v2005, 3);
  EXPECT_EQ(vpiMode1800v2005, 4);
  EXPECT_EQ(vpiMode1800v2009, 5);
}

// §M.2 ends the properties with the packed-array-member Boolean, the source
// span from vpiStartLine at 661, the allocation scheme at 658 with its three
// values, the object identifier, the DPI properties and the modport Boolean.
TEST(SvVpiUserHeader, TheGenericObjectPropertiesOfLocationsAllocationAndDpi) {
  EXPECT_EQ(vpiPackedArrayMember, 655);
  EXPECT_EQ(vpiStartLine, 661);
  EXPECT_EQ(vpiColumn, 662);
  EXPECT_EQ(vpiEndLine, 663);
  EXPECT_EQ(vpiEndColumn, 664);
  EXPECT_EQ(vpiAllocScheme, 658);
  EXPECT_EQ(vpiAutomaticScheme, 1);
  EXPECT_EQ(vpiDynamicScheme, 2);
  EXPECT_EQ(vpiOtherScheme, 3);
  EXPECT_EQ(vpiObjId, 660);
  EXPECT_EQ(vpiDPIPure, 665);
  EXPECT_EQ(vpiDPIContext, 666);
  EXPECT_EQ(vpiDPICStr, 667);
  EXPECT_EQ(vpiDPI, 1);
  EXPECT_EQ(vpiDPIC, 2);
  EXPECT_EQ(vpiDPICIdentifier, 668);
  EXPECT_EQ(vpiIsModPort, 669);
}

// §M.2 numbers the operators from vpiImplyOp at 50 through vpiInsideOp at 95:
// the implications, the followed-by, accept-on and reject-on operators from 83,
// the temporal operators from 89, the cycle delays and sequence operators from
// 53, the increments and decrements from 62, and the match, cast, iff,
// wildcard, streaming, matched, triggered, pattern, if, composite, implies,
// type and assignment operators.
TEST(SvVpiUserHeader, TheOperators) {
  EXPECT_EQ(vpiImplyOp, 50);
  EXPECT_EQ(vpiNonOverlapImplyOp, 51);
  EXPECT_EQ(vpiOverlapImplyOp, 52);
  EXPECT_EQ(vpiAcceptOnOp, 83);
  EXPECT_EQ(vpiRejectOnOp, 84);
  EXPECT_EQ(vpiSyncAcceptOnOp, 85);
  EXPECT_EQ(vpiSyncRejectOnOp, 86);
  EXPECT_EQ(vpiOverlapFollowedByOp, 87);
  EXPECT_EQ(vpiNonOverlapFollowedByOp, 88);
  EXPECT_EQ(vpiNexttimeOp, 89);
  EXPECT_EQ(vpiAlwaysOp, 90);
  EXPECT_EQ(vpiEventuallyOp, 91);
  EXPECT_EQ(vpiUntilOp, 92);
  EXPECT_EQ(vpiUntilWithOp, 93);
  EXPECT_EQ(vpiUnaryCycleDelayOp, 53);
  EXPECT_EQ(vpiCycleDelayOp, 54);
  EXPECT_EQ(vpiIntersectOp, 55);
  EXPECT_EQ(vpiFirstMatchOp, 56);
  EXPECT_EQ(vpiThroughoutOp, 57);
  EXPECT_EQ(vpiWithinOp, 58);
  EXPECT_EQ(vpiRepeatOp, 59);
  EXPECT_EQ(vpiConsecutiveRepeatOp, 60);
  EXPECT_EQ(vpiGotoRepeatOp, 61);
  EXPECT_EQ(vpiPostIncOp, 62);
  EXPECT_EQ(vpiPreIncOp, 63);
  EXPECT_EQ(vpiPostDecOp, 64);
  EXPECT_EQ(vpiPreDecOp, 65);
  EXPECT_EQ(vpiMatchOp, 66);
  EXPECT_EQ(vpiCastOp, 67);
  EXPECT_EQ(vpiIffOp, 68);
  EXPECT_EQ(vpiWildEqOp, 69);
  EXPECT_EQ(vpiWildNeqOp, 70);
  EXPECT_EQ(vpiStreamLROp, 71);
  EXPECT_EQ(vpiStreamRLOp, 72);
  EXPECT_EQ(vpiMatchedOp, 73);
  EXPECT_EQ(vpiTriggeredOp, 74);
  EXPECT_EQ(vpiAssignmentPatternOp, 75);
  EXPECT_EQ(vpiMultiAssignmentPatternOp, 76);
  EXPECT_EQ(vpiIfOp, 77);
  EXPECT_EQ(vpiIfElseOp, 78);
  EXPECT_EQ(vpiCompAndOp, 79);
  EXPECT_EQ(vpiCompOrOp, 80);
  EXPECT_EQ(vpiImpliesOp, 94);
  EXPECT_EQ(vpiInsideOp, 95);
  EXPECT_EQ(vpiTypeOp, 81);
  EXPECT_EQ(vpiAssignmentOp, 82);
}

// §M.2 gives vpiOtherFunc as a return value of vpiFuncType and vpiValidUnknown
// as a return value of the deprecated vpiValid.
TEST(SvVpiUserHeader, TheTaskFunctionAndValidityProperties) {
  EXPECT_EQ(vpiOtherFunc, 6);
  EXPECT_EQ(vpiValidUnknown, 2);
}

// §M.2 numbers the callback reasons of threads, frames and size changes from
// 600 and of class and transient objects from 700.
TEST(SvVpiUserHeader, TheCallbackReasons) {
  EXPECT_EQ(cbStartOfThread, 600);
  EXPECT_EQ(cbEndOfThread, 601);
  EXPECT_EQ(cbEnterThread, 602);
  EXPECT_EQ(cbStartOfFrame, 603);
  EXPECT_EQ(cbEndOfFrame, 604);
  EXPECT_EQ(cbSizeChange, 605);
  EXPECT_EQ(cbCreateObj, 700);
  EXPECT_EQ(cbReclaimObj, 701);
  EXPECT_EQ(cbEndOfObject, 702);
}

// §M.2 numbers the coverage VPI within the 750 through 779 it reserves for it:
// the control operations from 750, the coverage types from 760, the status
// properties from 765 with vpiCoverMax kept beside vpiCoveredMax at 766, the
// assertion and FSM status properties from 770 and the FSM handle types at 758
// and 759.
TEST(SvVpiUserHeader, TheCoverageVpi) {
  EXPECT_EQ(vpiCoverageStart, 750);
  EXPECT_EQ(vpiCoverageStop, 751);
  EXPECT_EQ(vpiCoverageReset, 752);
  EXPECT_EQ(vpiCoverageCheck, 753);
  EXPECT_EQ(vpiCoverageMerge, 754);
  EXPECT_EQ(vpiCoverageSave, 755);
  EXPECT_EQ(vpiAssertCoverage, 760);
  EXPECT_EQ(vpiFsmStateCoverage, 761);
  EXPECT_EQ(vpiStatementCoverage, 762);
  EXPECT_EQ(vpiToggleCoverage, 763);
  EXPECT_EQ(vpiCovered, 765);
  EXPECT_EQ(vpiCoverMax, 766);
  EXPECT_EQ(vpiCoveredMax, 766);
  EXPECT_EQ(vpiCoveredCount, 767);
  EXPECT_EQ(vpiAssertAttemptCovered, 770);
  EXPECT_EQ(vpiAssertSuccessCovered, 771);
  EXPECT_EQ(vpiAssertFailureCovered, 772);
  EXPECT_EQ(vpiAssertVacuousSuccessCovered, 773);
  EXPECT_EQ(vpiAssertDisableCovered, 774);
  EXPECT_EQ(vpiAssertKillCovered, 777);
  EXPECT_EQ(vpiFsmStates, 775);
  EXPECT_EQ(vpiFsmStateExpression, 776);
  EXPECT_EQ(vpiFsm, 758);
  EXPECT_EQ(vpiFsmHandle, 759);
}

// §M.2 numbers the assertion callback reasons from cbAssertionStart at 606, the
// action reasons from 645, and the assertion system callback reasons from 615,
// 631 and 651.
TEST(SvVpiUserHeader, TheAssertionCallbackReasons) {
  EXPECT_EQ(cbAssertionStart, 606);
  EXPECT_EQ(cbAssertionSuccess, 607);
  EXPECT_EQ(cbAssertionFailure, 608);
  EXPECT_EQ(cbAssertionVacuousSuccess, 657);
  EXPECT_EQ(cbAssertionDisabledEvaluation, 658);
  EXPECT_EQ(cbAssertionStepSuccess, 609);
  EXPECT_EQ(cbAssertionStepFailure, 610);
  EXPECT_EQ(cbAssertionLock, 661);
  EXPECT_EQ(cbAssertionUnlock, 662);
  EXPECT_EQ(cbAssertionDisable, 611);
  EXPECT_EQ(cbAssertionEnable, 612);
  EXPECT_EQ(cbAssertionReset, 613);
  EXPECT_EQ(cbAssertionKill, 614);
  EXPECT_EQ(cbAssertionEnablePassAction, 645);
  EXPECT_EQ(cbAssertionEnableFailAction, 646);
  EXPECT_EQ(cbAssertionDisablePassAction, 647);
  EXPECT_EQ(cbAssertionDisableFailAction, 648);
  EXPECT_EQ(cbAssertionEnableNonvacuousAction, 649);
  EXPECT_EQ(cbAssertionDisableVacuousAction, 650);
  EXPECT_EQ(cbAssertionSysInitialized, 615);
  EXPECT_EQ(cbAssertionSysOn, 616);
  EXPECT_EQ(cbAssertionSysOff, 617);
  EXPECT_EQ(cbAssertionSysKill, 631);
  EXPECT_EQ(cbAssertionSysLock, 659);
  EXPECT_EQ(cbAssertionSysUnlock, 660);
  EXPECT_EQ(cbAssertionSysEnd, 618);
  EXPECT_EQ(cbAssertionSysReset, 619);
  EXPECT_EQ(cbAssertionSysEnablePassAction, 651);
  EXPECT_EQ(cbAssertionSysEnableFailAction, 652);
  EXPECT_EQ(cbAssertionSysDisablePassAction, 653);
  EXPECT_EQ(cbAssertionSysDisableFailAction, 654);
  EXPECT_EQ(cbAssertionSysEnableNonvacuousAction, 655);
  EXPECT_EQ(cbAssertionSysDisableVacuousAction, 656);
}

// §M.2 numbers the assertion control constants from vpiAssertionLock at 645 and
// vpiAssertionDisable at 620 through the per-assertion action controls from 633
// and the system action controls from 639.
TEST(SvVpiUserHeader, TheAssertionControlConstants) {
  EXPECT_EQ(vpiAssertionLock, 645);
  EXPECT_EQ(vpiAssertionUnlock, 646);
  EXPECT_EQ(vpiAssertionDisable, 620);
  EXPECT_EQ(vpiAssertionEnable, 621);
  EXPECT_EQ(vpiAssertionReset, 622);
  EXPECT_EQ(vpiAssertionKill, 623);
  EXPECT_EQ(vpiAssertionEnableStep, 624);
  EXPECT_EQ(vpiAssertionDisableStep, 625);
  EXPECT_EQ(vpiAssertionClockSteps, 626);
  EXPECT_EQ(vpiAssertionSysLock, 647);
  EXPECT_EQ(vpiAssertionSysUnlock, 648);
  EXPECT_EQ(vpiAssertionSysOn, 627);
  EXPECT_EQ(vpiAssertionSysOff, 628);
  EXPECT_EQ(vpiAssertionSysKill, 632);
  EXPECT_EQ(vpiAssertionSysEnd, 629);
  EXPECT_EQ(vpiAssertionSysReset, 630);
  EXPECT_EQ(vpiAssertionDisablePassAction, 633);
  EXPECT_EQ(vpiAssertionEnablePassAction, 634);
  EXPECT_EQ(vpiAssertionDisableFailAction, 635);
  EXPECT_EQ(vpiAssertionEnableFailAction, 636);
  EXPECT_EQ(vpiAssertionDisableVacuousAction, 637);
  EXPECT_EQ(vpiAssertionEnableNonvacuousAction, 638);
  EXPECT_EQ(vpiAssertionSysEnablePassAction, 639);
  EXPECT_EQ(vpiAssertionSysEnableFailAction, 640);
  EXPECT_EQ(vpiAssertionSysDisablePassAction, 641);
  EXPECT_EQ(vpiAssertionSysDisableFailAction, 642);
  EXPECT_EQ(vpiAssertionSysEnableNonvacuousAction, 643);
  EXPECT_EQ(vpiAssertionSysDisableVacuousAction, 644);
}

// §M.2 lays the step information out as a count of matched expressions, an
// array of handles to them and the two states of the transition, and gives
// the structure its pointer spelling.
TEST(SvVpiUserHeader, TheAssertionStepInfoStructureIsAsTheAnnexLaysItOut) {
  s_vpi_assertion_step_info step = {};
  static_assert(
      std::is_same_v<decltype(step.matched_expression_count), PLI_INT32>);
  static_assert(std::is_same_v<decltype(step.matched_exprs), vpiHandle*>);
  static_assert(std::is_same_v<decltype(step.stateFrom), PLI_INT32>);
  static_assert(std::is_same_v<decltype(step.stateTo), PLI_INT32>);
  static_assert(
      std::is_same_v<p_vpi_assertion_step_info, s_vpi_assertion_step_info*>);
  step.stateFrom = 2;
  step.stateTo = 3;
  EXPECT_EQ(step.stateFrom, 2);
  EXPECT_EQ(step.stateTo, 3);
  EXPECT_EQ(step.matched_expression_count, 0);
  EXPECT_EQ(step.matched_exprs, nullptr);
}

// §M.2 lays the attempt information out as a detail union of the failing
// expression's handle and a pointer to the step information, then the time
// the attempt was triggered, and gives the structure its pointer spelling.
TEST(SvVpiUserHeader, TheAttemptInfoStructureIsAsTheAnnexLaysItOut) {
  s_vpi_attempt_info info = {};
  static_assert(std::is_same_v<decltype(info.detail.failExpr), vpiHandle>);
  static_assert(
      std::is_same_v<decltype(info.detail.step), p_vpi_assertion_step_info>);
  static_assert(std::is_same_v<decltype(info.attemptStartTime), s_vpi_time>);
  static_assert(std::is_same_v<p_vpi_attempt_info, s_vpi_attempt_info*>);
  s_vpi_assertion_step_info step = {};
  info.detail.step = &step;
  info.attemptStartTime.type = vpiSimTime;
  info.attemptStartTime.low = 7;
  EXPECT_EQ(info.detail.step, &step);
  EXPECT_EQ(info.attemptStartTime.type, vpiSimTime);
  EXPECT_EQ(info.attemptStartTime.low, 7u);
}

// §M.2 names the callback routine's type as a function type, not a pointer
// type: a routine taking the reason, the callback time, the assertion, the
// attempt information and the user data, and returning PLI_INT32. The
// registration routine takes a pointer to that function type, the assertion,
// the reason and the user data, and returns a handle.
TEST(SvVpiUserHeader, TheCallbackTypeAndTheRegistrationRoutineAreAsDeclared) {
  static_assert(std::is_same_v<vpi_assertion_callback_func,
                               PLI_INT32(PLI_INT32, p_vpi_time, vpiHandle,
                                         p_vpi_attempt_info, PLI_BYTE8*)>);
  static_assert(std::is_function_v<vpi_assertion_callback_func>);
  static_assert(
      std::is_same_v<decltype(vpi_register_assertion_cb),
                     vpiHandle(vpiHandle, PLI_INT32,
                               vpi_assertion_callback_func*, PLI_BYTE8*)>);
  vpi_assertion_callback_func* routine = nullptr;
  EXPECT_EQ(routine, nullptr);
}

// The file the annex shows includes vpi_user.h, and its own guard is the
// SV_VPI_USER_H the annex tests, so both marks are defined once it is read.
TEST(SvVpiUserHeader, TheFileIncludesTheBaseFileUnderTheAnnexsGuard) {
#if defined(SV_VPI_USER_H) && defined(VPI_USER_H)
  SUCCEED();
#else
  FAIL() << "sv_vpi_user.h did not define its guard or include vpi_user.h";
#endif
}

// §37.10 tags the iteration from an instance to its nettype declarations
// vpiNetTypedef, a name Annex M does not list; the file keeps it at a number
// the annex leaves unused, so it collides with no object type or method the
// annex numbers, and the declarations it reaches are of the annex's type.
TEST(SvVpiUserHeader, TheNettypeIterationTagStandsApartFromTheAnnexsNumbers) {
  const int kAnnexObjectTypesAndMethodsNear711[] = {vpiActual,
                                                    vpiTypedefAlias,
                                                    vpiIndexTypespec,
                                                    vpiBaseTypespec,
                                                    vpiElemTypespec,
                                                    vpiNetTypedefAlias,
                                                    vpiInputSkew,
                                                    vpiOutputSkew,
                                                    vpiGlobalClocking,
                                                    vpiDefaultClocking,
                                                    vpiDefaultDisableIff,
                                                    vpiOrigin,
                                                    vpiPrefix,
                                                    vpiWith,
                                                    vpiProperty};
  for (int type : kAnnexObjectTypesAndMethodsNear711) {
    EXPECT_NE(vpiNetTypedef, type);
  }
  EXPECT_EQ(vpiNetTypedef, 711);
  EXPECT_NE(vpiNetTypedef, vpiNettypeDecl);
}

// Edge case: the listing documents vpiQualifier as carrying a bitwise OR of the
// qualifier flags, so each flag (other than the "none" sentinel) must be a
// single distinct bit and the flags must compose without overlapping.
TEST(SvVpiUserConstants, QualifierFlagsComposeAsDistinctBits) {
  EXPECT_EQ(vpiNoQualifier, 0);
  const int kFlags[] = {vpiUniqueQualifier, vpiPriorityQualifier,
                        vpiTaggedQualifier, vpiRandQualifier,
                        vpiInsideQualifier};
  int combined = 0;
  for (int flag : kFlags) {
    // Exactly one bit set (power of two).
    EXPECT_NE(flag, 0);
    EXPECT_EQ(flag & (flag - 1), 0);
    // No bit shared with any flag seen so far.
    EXPECT_EQ(combined & flag, 0);
    combined |= flag;
  }
  // All five flags OR-combine into a five-bit mask.
  EXPECT_EQ(combined, vpiUniqueQualifier | vpiPriorityQualifier |
                          vpiTaggedQualifier | vpiRandQualifier |
                          vpiInsideQualifier);
}

// Edge case: each enumerated property value-set the listing introduces must
// assign a distinct selector to every member so the values are unambiguous.
TEST(SvVpiUserConstants, EnumeratedPropertyValuesAreDistinct) {
  const int kClassKinds[] = {vpiMailboxClass, vpiSemaphoreClass,
                             vpiUserDefinedClass, vpiProcessClass};
  for (size_t i = 0; i < std::size(kClassKinds); ++i) {
    for (size_t j = i + 1; j < std::size(kClassKinds); ++j) {
      EXPECT_NE(kClassKinds[i], kClassKinds[j]);
    }
  }

  const int kCompatModes[] = {vpiMode1364v1995, vpiMode1364v2001,
                              vpiMode1364v2005, vpiMode1800v2005,
                              vpiMode1800v2009};
  for (size_t i = 0; i < std::size(kCompatModes); ++i) {
    for (size_t j = i + 1; j < std::size(kCompatModes); ++j) {
      EXPECT_NE(kCompatModes[i], kCompatModes[j]);
    }
  }

  // vpiConstType return values, distribution kinds, and port-type values.
  EXPECT_NE(vpiOneStepConst, vpiUnboundedConst);
  EXPECT_NE(vpiUnboundedConst, vpiNullConst);
  EXPECT_NE(vpiOneStepConst, vpiNullConst);
  EXPECT_NE(vpiEqualDist, vpiDivDist);
  EXPECT_NE(vpiInterfacePort, vpiModportPort);
}

// Edge case: the deprecated/alias spellings the listing defines must resolve to
// the very same selector as their canonical counterparts, so production code
// using either spelling is interchangeable.
TEST(SvVpiUserConstants, AliasSpellingsResolveToCanonicalSelectors) {
  EXPECT_EQ(vpiConcurrentAssertions, vpiConcurrentAssertion);
  EXPECT_EQ(vpiConcurrentAssertions, 740);
  EXPECT_EQ(vpiInterfaceDecl, vpiVirtualInterfaceVar);
  EXPECT_EQ(vpiVarBit, vpiRegBit);
  EXPECT_EQ(vpiLogicVar, vpiReg);
  EXPECT_EQ(vpiArrayVar, vpiRegArray);
  EXPECT_EQ(vpiArrayNet, vpiNetArray);
  EXPECT_EQ(vpiLogicNet, vpiNet);
}

}  // namespace
